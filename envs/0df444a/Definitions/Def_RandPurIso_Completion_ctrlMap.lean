-- Prove2me | Definitions.Def_RandPurIso_Completion_ctrlMap
-- name    : RandPurIso_Completion_ctrlMap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:26:15.154744+00:00
-- url     : https://prove2.me/theorems/d34d8de6-9aff-463e-860e-dc75bbb89b5d
-- title:
--   Controlled query $\mathrm{ctrl}_b[V]$ (Definition 3.9)
-- statement:
--   For a partial isometry $V:A\to A\otimes A_{\mathrm{pure}}$ and a control qubit $C$,
--   $$\mathrm{ctrl}_b[V]=|b\rangle\langle b|_C\otimes V+|b\oplus1\rangle\langle b\oplus1|_C\otimes(I_A\otimes|0\rangle_{A_{\mathrm{pure}}}),\qquad \mathrm{ctrl}[V]:=\mathrm{ctrl}_1[V].$$
--   `ctrlMap b V E` is $|b\rangle\langle b|\otimes V+|b\oplus1\rangle\langle b\oplus1|\otimes E$; Definition 3.9 is $E=I_A\otimes|0\rangle$ (`idleEmbed`), and when $A_{\mathrm{pure}}$ is trivial (as for $\mathrm{ctrl}[U]$, $\mathrm{ctrl}[PR]$ in Theorem 3.14) $E=I$. `ctrlSt` reassociates $C\otimes(Y\otimes\mathsf{St})$ as $(C\otimes Y)\otimes\mathsf{St}$.
-- source:
--   Goldin, On Random Purifications of Isometries and Channels, arXiv:2611.04573, Definition 3.9, p. 19

import Mathlib
open Matrix

namespace RandPurIso.Completion

/-- **Controlled query** (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, Definition 3.9, p. 19): for `V : A → A ⊗ A_pure`,
`ctrl_b[V] = |b⟩⟨b|_C ⊗ V + |b ⊕ 1⟩⟨b ⊕ 1|_C ⊗ (I_A ⊗ |0⟩_{A_pure})`, with `ctrl[V] := ctrl_1[V]`.

`ctrlMap b V E` is `|b⟩⟨b| ⊗ V + |b⊕1⟩⟨b⊕1| ⊗ E`; Definition 3.9 is `E = idleEmbed |0⟩`, and for a
square map (`A_pure` trivial, as for `ctrl[U]` and `ctrl[PR]` in Theorem 3.14) `E = I`.

**Formalization Note.** The control qubit `C` is `Bool`, `true = 1`. The idle branch is a parameter
so that the same definition covers `A_pure` nontrivial and trivial. -/
def ctrlMap {X Y : Type} (b : Bool) (V E : Matrix Y X ℂ) : Matrix (Bool × Y) (Bool × X) ℂ :=
  fun p q => if p.1 = q.1 then (if q.1 = b then V p.2 q.2 else E p.2 q.2) else 0

/-- `I_A ⊗ |z₀⟩_{A_pure}` (Definition 3.9's idle branch with `z₀ = |0⟩`). -/
def idleEmbed {X P : Type} [DecidableEq X] (z0 : P → ℂ) : Matrix (X × P) X ℂ :=
  fun p x => if p.1 = x then z0 p.2 else 0

/-- Reassociation `C ⊗ (Y ⊗ St) ≅ (C ⊗ Y) ⊗ St`, to view a controlled stateful map as a map
`(C ⊗ X) ⊗ St → (C ⊗ Y) ⊗ St` (the private register is the last factor, Definition 3.2). -/
def ctrlSt {X Y S : Type} (K : Matrix (Bool × (Y × S)) (Bool × (X × S)) ℂ) :
    Matrix ((Bool × Y) × S) ((Bool × X) × S) ℂ :=
  Matrix.reindex (Equiv.prodAssoc Bool Y S).symm (Equiv.prodAssoc Bool X S).symm K

end RandPurIso.Completion


