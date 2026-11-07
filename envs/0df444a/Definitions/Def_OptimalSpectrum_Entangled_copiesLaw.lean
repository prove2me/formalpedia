-- Prove2me | Definitions.Def_OptimalSpectrum_Entangled_copiesLaw
-- name    : OptimalSpectrum_Entangled_copiesLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:18:23.400299+00:00
-- url     : https://prove2.me/theorems/b4505979-1db4-46be-bb55-ca5728c563b1
-- title:
--   Outcome law $B\mapsto\mathrm{tr}(E(B)\,\rho^{\otimes n})$ of a POVM on $n$ copies
-- statement:
--   Let $E$ be a POVM on $(\mathbb C^d)^{\otimes n}$ with outcomes in a measurable space $\mathcal O$: a normalized, countably additive map from measurable sets to positive semidefinite operators. For a density matrix $\rho$ on $\mathbb C^d$, the outcome of measuring $E$ on $n$ copies of $\rho$ has the law
--
--   $$\mathbb P_{E,\rho}(B)=\mathrm{tr}\big(E(B)\,\rho^{\otimes n}\big),\qquad B\subseteq\mathcal O\ \text{measurable}.$$
--
--   This is the entangled measurement model of Definition 4.1: an arbitrary POVM acting jointly on all copies, with continuous outcomes allowed.
--
--   **Formalization Note** The POVM is the platform's `OperatorPOVM` and the law is its `bornLaw` applied to the tensor power `piKron n ρ`; the definition carries the proof that $\rho^{\otimes n}$ is a density matrix.
-- source:
--   Bakshi, Singh, Tan, Optimal spectrum estimation, arXiv:2609.30171, Definition 4.1, p. 11 (PDF p. 13)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_GeneralPOVMs
import Definitions.Def_QAlgorithms_Defs_GradientMethods

open MeasureTheory
open scoped Matrix ComplexOrder MatrixOrder

namespace OptimalSpectrum.Entangled

/-- **Outcome law of a POVM measured on `n` copies of a state.**
Bakshi, Singh, Tan, *Optimal spectrum estimation*, arXiv:2609.30171, Definition 4.1, printed p. 11 (PDF p. 13): "In the entangled measurement model, we allow an
arbitrary POVM on (C^d)^⊗n. So each M_i ∈ C^(d^n×d^n) and outcome i occurs with probability
tr(M_i ρ^⊗n)" and "We also allow continuous outcomes".

For a POVM `E` on `(ℂ^d)^{⊗n}` with outcomes in a measurable space `O` and a density matrix `ρ` on
`ℂ^d`, `copiesLaw E ρ hρ` is the Born law `B ↦ tr(E(B) ρ^{⊗n})` of the outcome.

**Formalization Note.** `(ℂ^d)^{⊗n}` is indexed by `Fin n → Fin d` (copy `i` = coordinate `i`), and
`ρ^{⊗n}` is the platform's `QAlgorithms.piKron n ρ`. The proof inside the definition shows that
`ρ^{⊗n}` is a density matrix, which `bornLaw` requires; it adds no hypothesis. -/
noncomputable def copiesLaw {d n : ℕ} {O : Type*} [MeasurableSpace O]
    (E : QAlgorithms.Measurements.OperatorPOVM (Fin n → Fin d) O)
    (ρ : Matrix (Fin d) (Fin d) ℂ) (hρ : QAlgorithms.IsDensityMatrix ρ) : Measure O :=
  QAlgorithms.Measurements.bornLaw E (QAlgorithms.piKron n ρ) (by
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
      rw [show (∑ x : Fin n → Fin d, ∏ i, ρ (x i) (x i)) = ∏ _i : Fin n, ∑ j, ρ j j from
        (Fintype.prod_sum (fun (_ : Fin n) (j : Fin d) => ρ j j)).symm, h2,
        Finset.prod_const_one])

end OptimalSpectrum.Entangled


