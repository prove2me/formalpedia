-- Prove2me | Definitions.Def_FiniteStateContract_Equivalence_Values
-- name    : FiniteStateContract_Equivalence_Values
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T14:15:21.487695+00:00
-- url     : https://prove2.me/theorems/38cdaaba-ac93-4793-a588-57520e9b1e9a
-- title:
--   The original contracting value and the forward McKean–Vlasov value
-- statement:
--   The original principal value is the two-level infimum
--   $$V(\kappa)=\inf_{K\in\mathcal C}\inf_{(\alpha,p)\in\mathcal N(K),\ J_K(\alpha,p)\le\kappa} J_0^{\alpha,p}(K).$$
--   For each candidate equilibrium, the best-response condition evaluates every competing control at that contract and flow. Each eligible principal cost must be defined. No equilibrium is selected arbitrarily: the inner infimum favors the principal.
--
--   The forward value is the two-level infimum in (34), over all $\mathcal F_0$-measurable random $Y_0$ with defined expectation at most $\kappa$, all predictable real $r$, and all adapted left-continuous $Z$ satisfying the printed first-moment condition. Each such input must have a solution of (30)–(33); every solution must give the same defined objective
--   $$E^Q\left[\int_0^T(c_0(t,p(t))+r_t)dt+C_0(p(T))+U^{-1}(-Y_T)\right].$$
--   The inverse requires a unique preimage almost surely. There is no assumption of global invertibility of $U$, no removal of inputs with undefined inverse, and no optimization over a chosen subset of solutions. Nonexistence or selection-dependent cost makes the value undefined. Both infima use extended reals, preserving empty and unbounded cases. The source's equality is represented as existence of a common defined value, rather than equality of two undefined objects.
-- source:
--   Carmona and Wang, Finite-State Contract Theory with a Principal and a Field of Agents, held PDF arXiv:1808.07942v1 (23 Aug 2018), §2.6, (11), PDF p. 5 = printed p. 5; §3.3, (30)–(34), PDF pp. 8–9 = printed pp. 8–9; catalog DOI 10.1287/mnsc.2020.3760 (metadata basis published).

import Definitions.Def_FiniteStateContract_Equivalence_BSDE

open MeasureTheory
open scoped ENNReal NNReal

namespace FiniteStateContract.Equivalence
noncomputable section

open ExtFSMFG.Existence (Omega filt)
variable {m l : ℕ} {T : ℝ≥0}

/-- Equation (11): the two actual infima, with partial costs checked at every
eligible index. Best responses evaluate all competing controls for that contract and flow. -/
def OriginalValue (D : Data m l T) (κ : ℝ) (v : EReal) : Prop :=
  InfimumValue (AdmissibleContract D)
    (fun K w => InfimumValue
      (fun x : Proc m T (Action l) × Flow m =>
        Nash D K x.1 x.2 ∧ ∃ c, AgentCost D K x.1 x.2 c ∧ c ≤ (κ : EReal))
      (fun x c => PrincipalCost D K x.1 x.2 c) w) v

/-- Terminal inverse in (34), required almost surely and unique at each value.
No integrability of the recovered payment is added to the forward control class. -/
def ForwardCost (D : Data m l T) (r : Proc m T ℝ) (Y : Proc m T ℝ)
    (p : Flow m) (Q : Measure (Omega m T)) (v : EReal) : Prop :=
  ∃ ξ : Omega m T → ℝ,
    (∀ᵐ ω ∂Q, InverseValue D.U (-Y T ω) (ξ ω)) ∧
    RunningCostValue Q (fun t ω => D.c₀ t (p t) + r t ω)
      (fun ω => D.C₀ (p T) + ξ ω) v

/-- The source's phrase 'its solution' means there is a solution and all solutions
give the same defined objective. It does not introduce an infimum over solutions. -/
def ForwardControlValue (D : Data m l T) (a : Feedback m l)
    (Z : Proc m T (Vec m)) (r : Proc m T ℝ) (Y₀ : Omega m T → ℝ) (v : EReal) : Prop :=
  (∃ Y α p Q, Forward D a Z r Y₀ Y α p Q) ∧
    ∀ Y α p Q, Forward D a Z r Y₀ Y α p Q → ForwardCost D r Y p Q v

/-- The expectation constraint for the random F₀-measurable initial value. -/
def InitialEligible (D : Data m l T) (κ : ℝ) (Y₀ : Omega m T → ℝ) : Prop :=
  StronglyMeasurable[filt m T 0] Y₀ ∧
    ∃ c, IntegralValue D.P (fun ω => (Y₀ ω : EReal)) c ∧ c ≤ (κ : EReal)

/-- Equation (34), with both infima and every printed forward control retained.
If any control lacks a solution or a defined, selection-independent cost, this
value relation fails, making the missing definedness an asserted theorem obligation. -/
def ForwardValue (D : Data m l T) (a : Feedback m l) (κ : ℝ) (v : EReal) : Prop :=
  InfimumValue (InitialEligible D κ)
    (fun Y₀ w => InfimumValue
      (fun x : Proc m T (Vec m) × Proc m T ℝ =>
        ForwardZ D x.1 ∧ IsStronglyPredictable (filt m T) x.2)
      (fun x c => ForwardControlValue D a x.1 x.2 Y₀ c) w) v

end
end FiniteStateContract.Equivalence


