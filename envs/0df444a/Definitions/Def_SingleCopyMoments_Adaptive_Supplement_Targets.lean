-- Prove2me | Definitions.Def_SingleCopyMoments_Adaptive_Supplement_Targets
-- name    : SingleCopyMoments_Adaptive_Supplement_Targets
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:36:54.94121+00:00
-- url     : https://prove2.me/theorems/ee76385a-e66a-4a8b-87de-7ce9ce7c4e5e
-- title:
--   Additive target success and partial transpose
-- statement:
--   Let $\rho$ be a positive semidefinite, trace-one matrix on $\mathbb C^d$. A real estimator of a functional $F$ succeeds when its normalized transcript law assigns probability at least $1-\delta$ to the measurable event
--   $$|\widehat F-F(\rho)|\le\epsilon.$$
--   For a known Hermitian observable $O$, the weighted target is $\operatorname{Re}\operatorname{Tr}(O\rho^t)$, equal to its real trace. On $\mathbb C^a\otimes\mathbb C^b$, partial transpose on the first subsystem has entries
--   $$ (\rho^{T_A})_{(i,j),(k,l)}=\rho_{(k,j),(i,l)}.$$
--   Its target is $\operatorname{Re}\operatorname{Tr}[(\rho^{T_A})^t]$. The matrix after partial transpose is not assumed positive. The nonadaptive exponent is $1-1/t$, with real division and $t\ge2$ in its theorem.
--
--   These definitions reuse the published density matrices, single-copy Born law and measurement schedules. They introduce the functionals and success predicates, without assuming any estimator exists.
-- source:
--   Zhenhuan Liu, STOC 2027 submission #41 (October 2026), §§5.4, 6.3, printed pp.19–20, 28–29 (PDF pp.21–22, 30–31); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/41.pdf

import Definitions.Def_SingleCopyMoments_Adaptive_Estimation

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal ComplexOrder Topology Matrix.Norms.L2Operator
set_option autoImplicit false
noncomputable section

namespace SingleCopyMoments.Adaptive.Supplement

/-- Additive success for a real functional, with normalization and a measurable event. -/
def RealSucceeds {d : ℕ} (P : Protocol d) (T : ℕ)
    (F : State d → ℝ) (ε δ : ℝ) : Prop :=
  ∀ ρ : State d, IsProbabilityMeasure (law P ρ T) ∧
    MeasurableSet {H | |P.output H - F ρ| ≤ ε} ∧
    ENNReal.ofReal (1 - δ) ≤ (law P ρ T) {H | |P.output H - F ρ| ≤ ε}

/-- The known observable need not commute with the state. -/
def weightedMoment {d : ℕ} (O : Op d) (t : ℕ) (ρ : State d) : ℝ :=
  (O * ρ.val ^ t).trace.re

/-- Partial transpose on the first factor in the fixed product basis, Eq. in §6.3.
The resulting matrix is Hermitian, but is not required to be positive. -/
def partialTranspose (a b : ℕ) (A : Op (a*b)) :
    Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ :=
  fun i j => A (finProdFinEquiv (j.1, i.2)) (finProdFinEquiv (i.1, j.2))

def partialTransposeMoment (a b t : ℕ) (ρ : State (a*b)) : ℝ :=
  ((partialTranspose a b ρ.val) ^ t).trace.re

/-- An ordinary real quotient; t is at least two wherever used. -/
def nonadaptiveExponent (t : ℕ) : ℝ := 1 - 1 / (t : ℝ)

end SingleCopyMoments.Adaptive.Supplement


