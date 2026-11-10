-- Prove2me | Definitions.Def_KnownFidelity_Rank_copyLaw
-- name    : KnownFidelity_Rank_copyLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:45:41.630433+00:00
-- url     : https://prove2.me/theorems/c55b7b04-6df2-49a7-ba10-6b342ca9a0b7
-- title:
--   Outcome law $B\mapsto\mathrm{tr}(E(B)\,\rho^{\otimes n})$ of a collective measurement on $n$ copies
-- statement:
--   Let $E$ be a POVM on $(\mathbb C^{\iota})^{\otimes n}$ with outcomes in a measurable space $\mathcal O$: a normalized, countably additive map from measurable sets to positive semidefinite operators. For a density matrix $\rho$ on $\mathbb C^{\iota}$, the outcome of measuring $E$ on $n$ copies of $\rho$ has the law
--
--   $$\mathbb P_{E,\rho}(B)=\mathrm{tr}\big(E(B)\,\rho^{\otimes n}\big),\qquad B\subseteq\mathcal O\ \text{measurable}.$$
--
--   This is the measurement model of the paper: the estimator receives $n$ copies of the unknown state and may measure them collectively, with continuous outcomes and classical post-processing allowed.
--
--   The module also proves the structural fact that $\rho^{\otimes n}$ is a density matrix whenever $\rho$ is.
--
--   **Formalization Note** $(\mathbb C^\iota)^{\otimes n}$ is indexed by `Fin n → ι` and $\rho^{\otimes n}$ is the platform's `QAlgorithms.piKron n ρ`; the POVM and its Born law are the platform's `OperatorPOVM` and `bornLaw`.
-- source:
--   Lee, Jo, Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank, arXiv:2608.01770, §1 (unnumbered), p. 1 (PDF p. 3)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_GeneralPOVMs
import Definitions.Def_QAlgorithms_Defs_GradientMethods

open MeasureTheory
open scoped Matrix ComplexOrder MatrixOrder

namespace KnownFidelity.Rank

/-- **The `n`-fold tensor power of a state is a state** (structural lemma for `copyLaw`).
If `ρ` is a density matrix on `ℂ^ι` then `ρ^{⊗n} = QAlgorithms.piKron n ρ`, indexed by
`Fin n → ι`, is a density matrix. -/
theorem isDensityMatrix_piKron {ι : Type*} [Fintype ι] [DecidableEq ι] (n : ℕ) {ρ : Matrix ι ι ℂ}
    (hρ : QAlgorithms.IsDensityMatrix ρ) : QAlgorithms.IsDensityMatrix (QAlgorithms.piKron n ρ) := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hρ.1.nonneg
  refine ⟨?_, ?_⟩
  · have hk : QAlgorithms.piKron n ρ =
        (QAlgorithms.piKron n B)ᴴ * QAlgorithms.piKron n B := by
      ext x y
      simp only [QAlgorithms.piKron, hB, Matrix.star_eq_conjTranspose, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Matrix.of_apply]
      rw [Fintype.prod_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [star_prod, ← Finset.prod_mul_distrib]
    rw [hk]
    exact Matrix.posSemidef_conjTranspose_mul_self _
  · have h2 := hρ.2
    simp only [Matrix.trace, Matrix.diag, QAlgorithms.piKron, Matrix.of_apply] at h2 ⊢
    rw [show (∑ x : Fin n → ι, ∏ i, ρ (x i) (x i)) = ∏ _i : Fin n, ∑ j, ρ j j from
      (Fintype.prod_sum (fun (_ : Fin n) (j : ι) => ρ j j)).symm, h2,
      Finset.prod_const_one]

/-- **Outcome law of a collective measurement on `n` copies.**
Lee, Jo, *Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank*,
arXiv:2608.01770, §1 (unnumbered), printed p. 1 (PDF p. 3): "the estimator receives copies of ρ.
Measurements may act collectively on all copies."

For a POVM `E` on `(ℂ^ι)^{⊗n}` with outcomes in a measurable space `O` and a density matrix `ρ`
on `ℂ^ι`, `copyLaw n E ρ hρ` is the Born law `B ↦ tr(E(B) ρ^{⊗n})` of the outcome.

**Formalization Note.** `(ℂ^ι)^{⊗n}` is indexed by `Fin n → ι` (copy `i` is coordinate `i`) and
`ρ^{⊗n}` is the platform's `QAlgorithms.piKron n ρ`; the POVM is the platform's `OperatorPOVM`
(arbitrary measurable outcome space, countably additive), so continuous outcomes and classical
post-processing of the outcome are included. The proof that `ρ^{⊗n}` is a density matrix is
`isDensityMatrix_piKron`; it adds no hypothesis. -/
noncomputable def copyLaw {ι O : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace O] (n : ℕ)
    (E : QAlgorithms.Measurements.OperatorPOVM (Fin n → ι) O)
    (ρ : Matrix ι ι ℂ) (hρ : QAlgorithms.IsDensityMatrix ρ) : Measure O :=
  QAlgorithms.Measurements.bornLaw E (QAlgorithms.piKron n ρ) (isDensityMatrix_piKron n hρ)

end KnownFidelity.Rank


