-- Prove2me | Definitions.Def_KnownFidelity_Rank_vecProj
-- name    : KnownFidelity_Rank_vecProj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:46:45.867141+00:00
-- url     : https://prove2.me/theorems/60bf3c8f-d1b5-41bb-86c4-304e1742565b
-- title:
--   The pure state $|\mathrm{vec}A\rangle\langle\mathrm{vec}A|$
-- statement:
--   For $A\in\mathbb C^{d\times s}$, the operator $|\mathrm{vec}A\rangle\langle\mathrm{vec}A|$ on $\mathbb C^d\otimes\mathbb C^s$. When $\|A\|_F=1$ it is a pure state (the module proves this), whose copies are the input of Lemma 3.1.
-- source:
--   Lee, Jo, Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank, arXiv:2608.01770, Lemma 3.1, p. 5 (PDF p. 7)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_KnownFidelity_Rank_vecOf

open scoped Matrix ComplexOrder

namespace KnownFidelity.Rank

/-- **The pure state `|vec A⟩⟨vec A|`.**
Lee, Jo, *Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank*,
arXiv:2608.01770, Lemma 3.1, printed p. 5 (PDF p. 7): "Let A ∈ C^{d×s} satisfy ∥A∥_F = 1, and let
|ψ⟩ = vec(A)", with the convention (7) of printed p. 4.

**Formalization Note.** The rank-one matrix `vecMulVec (vec A) (star (vec A))` on
`Fin d × Fin s`; it is a density matrix exactly when `‖A‖_F = 1` (`isDensityMatrix_vecProj`). -/
def vecProj {d s : ℕ} (A : Matrix (Fin d) (Fin s) ℂ) : Matrix (Fin d × Fin s) (Fin d × Fin s) ℂ :=
  Matrix.vecMulVec (vecOf A) (star (vecOf A))

/-- A Frobenius-normalized `A` gives a density matrix `|vec A⟩⟨vec A|` (structural lemma). -/
theorem isDensityMatrix_vecProj {d s : ℕ} {A : Matrix (Fin d) (Fin s) ℂ}
    (hA : ∑ i, ∑ j, ‖A i j‖ ^ 2 = 1) : QAlgorithms.IsDensityMatrix (vecProj A) := by
  refine ⟨Matrix.posSemidef_vecMulVec_self_star _, ?_⟩
  simp only [vecProj, Matrix.trace, Matrix.diag, Matrix.vecMulVec_apply, vecOf, Pi.star_apply,
    Complex.star_def, Complex.mul_conj, Fintype.sum_prod_type]
  have : (∑ i, ∑ j, (Complex.normSq (A i j) : ℂ)) = ((∑ i, ∑ j, ‖A i j‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    simp [Complex.normSq_eq_norm_sq]
  rw [this, hA]
  simp

end KnownFidelity.Rank


