-- Prove2me | Definitions.Def_RandomDimReduction_Channel_Supplement_Joint
-- name    : RandomDimReduction_Channel_Supplement_Joint
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:41:06.162906+00:00
-- url     : https://prove2.me/theorems/6c03f1e3-b185-47e4-9975-1a224da9a37d
-- title:
--   Two-state common-unitary mixtures and the two marginal conditions
-- statement:
--   For $n$ copies in each group, the data register is $(\mathbb C^d)^{\otimes n}\otimes(\mathbb C^d)^{\otimes n}$ and the purifying register is $(\mathbb C^k)^{\otimes n}\otimes(\mathbb C^k)^{\otimes n}$. For any Borel probability law $\nu$ on $U(k)$ define
--   $$J_\nu(\widetilde\rho,\widetilde\sigma)=\int (U\widetilde\rho U^\dagger)^{\otimes n}\otimes(U\widetilde\sigma U^\dagger)^{\otimes n}\,d\nu(U).$$
--   One unitary is shared by the two states and all copies. The marginal property of a complex-linear map $P$ says: for every four density operators $\rho,\sigma,\widetilde\rho,\widetilde\sigma$ and common isometry $W$ with $W\widetilde\rho W^\dagger=\rho$ and $W\widetilde\sigma W^\dagger=\sigma$, there exists a probability measure $\nu$ such that, for $X=\rho^{\otimes n}\otimes\sigma^{\otimes n}$,
--   $$\operatorname{tr}_{purify}P(X)=X,\qquad\operatorname{tr}_{data}P(X)=J_\nu(\widetilde\rho,\widetilde\sigma).$$
--   The law may depend on the entire compatible input tuple. This defines only the two equations, with neither CPTP validity nor impossibility built in, and with no rank-sum restriction.
-- source:
--   Angus Lowe, Xinyu Tan, Random dimension reduction and learning symmetric properties of quantum states, STOC 2027 submission #994 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/994.pdf, §3.3, pp.11–12, Eq. (9)

import Definitions.Def_RandomDimReduction_Channel_Tensor

set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped Kronecker Matrix ComplexConjugate Matrix.Norms.Elementwise

namespace RandomDimReduction.Channel.Supplement

abbrev Data (n d : ℕ) := Word n d × Word n d
abbrev Purify (n k : ℕ) := Word n k × Word n k

/-- The same sampled U acts in both tensor factors and in all copies. -/
def jointMixture {k : ℕ} (n : ℕ) (nu : Measure (Matrix.unitaryGroup (Fin k) ℂ))
    (rho sigma : Op (Fin k)) : Op (Purify n k) :=
  ∫ U : Matrix.unitaryGroup (Fin k) ℂ,
    (tensor n ((U : Op (Fin k)) * rho * (U : Op (Fin k))ᴴ) ⊗ₖ
      tensor n ((U : Op (Fin k)) * sigma * (U : Op (Fin k))ᴴ)) ∂nu

/-- Exactly the two desired marginal equations of Eq.(9).
The probability law may depend on every input and the common embedding. -/
def JointMarginals (n k d : ℕ)
    (P : Op (Data n d) →ₗ[ℂ] Op (Data n d × Purify n k)) : Prop :=
  ∀ (rho sigma : Op (Fin d)) (rho0 sigma0 : Op (Fin k)),
    MixedCloning.Optimal.IsState rho → MixedCloning.Optimal.IsState sigma →
    MixedCloning.Optimal.IsState rho0 → MixedCloning.Optimal.IsState sigma0 →
    ∀ W : Matrix (Fin d) (Fin k) ℂ, Wᴴ * W = 1 →
      W * rho0 * Wᴴ = rho → W * sigma0 * Wᴴ = sigma →
      ∃ nu : Measure (Matrix.unitaryGroup (Fin k) ℂ), IsProbabilityMeasure nu ∧
        WildeQIT.partialTraceRight (P (tensor n rho ⊗ₖ tensor n sigma)) =
          tensor n rho ⊗ₖ tensor n sigma ∧
        WildeQIT.partialTraceLeft (P (tensor n rho ⊗ₖ tensor n sigma)) =
          jointMixture n nu rho0 sigma0

end RandomDimReduction.Channel.Supplement


