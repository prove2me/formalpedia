-- Prove2me | Definitions.Def_RandPurIso_Completion_randomCompletion
-- name    : RandPurIso_Completion_randomCompletion
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:26:26.328177+00:00
-- url     : https://prove2.me/theorems/6b063434-a0cf-458f-adb4-3ec124a994ce
-- title:
--   Random completion $D^V_{U_{M_1}}$ (Definition 5.2)
-- statement:
--   For a completion $D^V$ and $U_{M_1}\in U(\mathcal H(M_1))$,
--   $$D^V_{U_{M_1}}:=D^V\big(\Pi_{M_0}+(I_{\mathcal H(M_0)}\oplus U_{M_1})\Pi_{M_1}\big)=D^V(I_{\mathcal H(M_0)}\oplus U_{M_1}).$$
--   The **random completion ensemble** samples $U_{M_1}$ from the Haar measure on $U(\mathcal H(M_1))$.
--
--   **Formalization Note** $U(\mathcal H(M_1))$ is the unitary group of $\mathbb C^{M-N}$ through $x\mapsto x-N$.
-- source:
--   Goldin, On Random Purifications of Isometries and Channels, arXiv:2611.04573, Definition 5.2, p. 29

import Mathlib
open Matrix

namespace RandPurIso.Completion

/-- `I_{H(M0)} ⊕ U` on `H([M])` for `U` a unitary on `H(M1)`, `M1 = {N, …, M−1}` identified with
`[M − N]` by `x ↦ x − N`. -/
def blockIdU {N M : ℕ} (U : Matrix (Fin (M - N)) (Fin (M - N)) ℂ) : Matrix (Fin M) (Fin M) ℂ :=
  fun i j =>
    if h : N ≤ i.val ∧ N ≤ j.val then
      U ⟨i.val - N, by have := i.isLt; omega⟩ ⟨j.val - N, by have := j.isLt; omega⟩
    else if i = j then 1 else 0

/-- **Random completion** (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, Definition 5.2, p. 29):
`D^V_{U_{M1}} := D^V (Π_{M0} + (I_{H(M0)} ⊕ U_{M1}) Π_{M1}) = D^V (I_{H(M0)} ⊕ U_{M1})`; the random
completion ensemble samples `U_{M1}` from the Haar measure on `U(H(M1))`.

**Formalization Note.** `U(H(M1))` is `Matrix.unitaryGroup (Fin (M − N)) ℂ` through `x ↦ x − N`. -/
def randomCompletion {N M : ℕ} (D : Matrix.unitaryGroup (Fin M) ℂ)
    (U : Matrix.unitaryGroup (Fin (M - N)) ℂ) : Matrix (Fin M) (Fin M) ℂ :=
  (D : Matrix (Fin M) (Fin M) ℂ) * blockIdU (N := N) (U : Matrix (Fin (M - N)) (Fin (M - N)) ℂ)

end RandPurIso.Completion


