-- Prove2me | Definitions.Def_ShallowShadows_ShadowNorm_embedGate
-- name    : ShallowShadows_ShadowNorm_embedGate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:31:11.789465+00:00
-- url     : https://prove2.me/theorems/8eaf146c-4217-4ffc-bd38-bf438775b9f7
-- title:
--   An $r$-qubit gate acting on chosen qubits of an $n$-qubit register
-- statement:
--   Let $e(0), \dots, e(r-1)$ be distinct qubits of an $n$-qubit register and $G$ an $r$-qubit unitary. The **embedded gate** acts as $G$ on these qubits, in this order, and as the identity elsewhere:
--
--   $$
--   (G_e)_{a,b} = G_{(a_{e(0)},\dots,a_{e(r-1)}),\,(b_{e(0)},\dots,b_{e(r-1)})} \prod_{i\notin \{e(0),\dots,e(r-1)\}} \delta_{a_i b_i}.
--   $$
--
--   It is unitary. Single-qubit gates ($r = 1$) build the $0$th layer of the brickwork circuits, two-qubit gates ($r = 2$) the brickwork layers.
--
--   **Formalization Note** Built as $G \otimes \mathbb I$ after reindexing the qubits; the entry formula above is checked in a verification file.
-- source:
--   Bertoni, Haferkamp, Hinsche, Ioannou, Eisert, Pashayan, Shallow shadows: Expectation estimation using low-depth random Clifford circuits, arXiv:2209.12924v3, §V, p. 4, Fig. 1

import Mathlib
import Definitions.Def_ClassicalShadow_Linear_Setting

open ClassicalShadow.Linear
open scoped Kronecker

namespace ShallowShadows.ShadowNorm

/-- Bertoni, Haferkamp, Hinsche, Ioannou, Eisert, Pashayan, *Shallow shadows: Expectation
estimation using low-depth random Clifford circuits*, arXiv:2209.12924v3, §V, p. 4 and Fig. 1:
an `r`-qubit gate `G` acting on the qubits `e 0, …, e (r−1)` of an `n`-qubit register (in this
order) and as the identity on the other qubits. Its `(a, b)` entry is
`G_{(a ∘ e), (b ∘ e)} · ∏_{i ∉ range e} δ_{a_i b_i}`.

**Formalization Note.** The matrix is built as `G ⊗ 𝕀` after reindexing `{0,1}ⁿ` as
`{0,1}^{range e} × {0,1}^{(range e)ᶜ}` (`Equiv.piEquivPiSubtypeProd`) and `{0,1}^{range e}` as
`{0,1}^r` along `e`; unitarity follows from `Matrix.kronecker_mem_unitary` and invariance of
unitarity under reindexing. Single-qubit gates are the case `r = 1`, the two-qubit gates of the
brickwork the case `r = 2`. -/
noncomputable def embedGate {r n : ℕ} (e : Fin r ↪ Fin n) (G : Matrix.unitaryGroup (Bits r) ℂ) :
    Matrix.unitaryGroup (Bits n) ℂ := by
  classical
  let eBits : Bits n ≃ (({i // i ∈ Set.range e}) → Fin 2) × (({i // i ∉ Set.range e}) → Fin 2) :=
    Equiv.piEquivPiSubtypeProd (fun i => i ∈ Set.range e) (fun _ => Fin 2)
  let φ : Bits r ≃ (({i // i ∈ Set.range e}) → Fin 2) :=
    Equiv.arrowCongr (Equiv.ofInjective e e.injective) (Equiv.refl (Fin 2))
  have hsub : ∀ {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
      (f : α ≃ β) (A : Matrix β β ℂ), A ∈ Matrix.unitaryGroup β ℂ →
      A.submatrix f f ∈ Matrix.unitaryGroup α ℂ := by
    intro α β _ _ _ _ f A hA
    rw [Matrix.mem_unitaryGroup_iff] at hA ⊢
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
      ← Matrix.star_eq_conjTranspose, hA, Matrix.submatrix_one_equiv]
  exact ⟨((G : Op r).submatrix φ.symm φ.symm ⊗ₖ
      (1 : Matrix (({i // i ∉ Set.range e}) → Fin 2) (({i // i ∉ Set.range e}) → Fin 2) ℂ)).submatrix
      eBits eBits,
    hsub eBits _ (Matrix.kronecker_mem_unitary (hsub φ.symm _ G.2) (one_mem _))⟩

end ShallowShadows.ShadowNorm


