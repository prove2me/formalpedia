-- Prove2me | Definitions.Def_FamilyGenTest_Rewards
-- name    : FamilyGenTest_Rewards
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:12:13.3542+00:00
-- url     : https://prove2.me/theorems/5ecfce42-bcba-45a1-9f0a-92ea150418d7
-- title:
--   Rewards, costs, the terminal reward and $r_i^\delta$
-- statement:
--   Each person $i$ carries five rewards, in net quality-adjusted life years, and two costs: $r_i^0(0)$ for a true non-carrier who changes nothing; $r_i^1(1)$ for a carrier with conclusive results and full treatment; $r_i^1(0)$ for a true carrier who changes nothing; $\bar r_i^0(1)$ and $\bar r_i^1(1)$, the censored rewards of a true non-carrier and of a true carrier at belief $1$; the screening cost $c_i^s$ and the follow-up cost $c_i^f$.
--
--   For a belief $p$,
--   $$
--   \bar r_i^0(p)=(1-p)r_i^0(0)+p\,\bar r_i^0(1),\qquad \bar r_i^1(p)=(1-p)r_i^1(0)+p\,\bar r_i^1(1),\qquad \bar r_i(p)=(1-p)\bar r_i^0(p)+p\,\bar r_i^1(p).
--   $$
--   Testing $i$ in $\mathbf s$ costs $c_i(\mathbf s)=c_i^s+\mathbb P_i(\mathbf s)c_i^f$ and pays $r_i^0(0)$ at result $0$ and $r_i^1(1)$ at results $1,2$. Stopping in $\mathbf s$ pays $\sum_{l\in\mathcal I\setminus\mathbf s}\bar r_l(\mathbb P_l(\mathbf s))$. Finally
--   $$
--   r_i^\delta=r_i^0(0)+\bar r_i^1(1)-\bar r_i^0(1)-r_i^1(0),\qquad d_i=r_i^1(1)-\bar r_i^1(1).
--   $$
--   The predicate `CensoredOrder` is the pair of weak inequalities of Assumption 4, $r_i^1(0)\le\bar r_i^1(1)$ and $\bar r_i^0(1)\le r_i^0(0)$.
--
--   These data define the objective (3) and the coefficients of the threshold rule.
--
--   **Formalization Note** All data are arbitrary reals. The quantity $r_i^0(1)$ of Assumption 4 occurs nowhere else in the paper's threshold argument and is not a field. Costs are per person.
-- source:
--   Adelman & Wang, Optimal Genetic Testing of Families, SSRN 4624694 (Jan 24 2023), §4.2–§4.3, pp.14–16: Assumptions 4, 5, (11); Definition 2, (8), p.13; (2), p.9

import Mathlib
import Definitions.Def_FamilyGenTest_risk

namespace FamilyGenTest

/-- The reward and cost data of a family, per individual, single gene (Adelman & Wang, Optimal
Genetic Testing of Families, SSRN 4624694 (Jan 24 2023), §4.2–§4.3, pp.14–15, and Definition 2,
p.13): `r0at0 i = rᵢ⁰(0)` true non-carrier with no behavior change; `r1at1 i = rᵢ¹(1)` tested carrier
with full treatment; `r1at0 i = rᵢ¹(0)` true carrier with no behavior change; `rbar0at1 i = r̄ᵢ⁰(1)`
and `rbar1at1 i = r̄ᵢ¹(1)` the censored rewards of a true non-carrier and a true carrier at belief 1;
`cs i = cᵢˢ` the screening cost; `cf i = cᵢᶠ` the follow-up cost.

**Formalization Note** All data are arbitrary reals; the only assumption the threshold theorem
keeps is `CensoredOrder`. `rᵢ⁰(1)` appears in the paper only in Assumption 4, in the part not kept. -/
structure Rewards (I : Type*) where
  r0at0 : I → ℝ
  r1at1 : I → ℝ
  r1at0 : I → ℝ
  rbar0at1 : I → ℝ
  rbar1at1 : I → ℝ
  cs : I → ℝ
  cf : I → ℝ

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The two weak inequalities of Assumption 4, (9) and (10) (Adelman & Wang, SSRN 4624694, p.15):
`rᵢ¹(0) ≤ r̄ᵢ¹(1)` and `r̄ᵢ⁰(1) ≤ rᵢ⁰(0)`.

**Formalization Note** The strict parts `r̄ᵢ¹(1) < rᵢ¹(1) − c_f − c_s` and `rᵢ⁰(1) < r̄ᵢ⁰(1)` are not
used by the threshold theorem and are not assumed. -/
def CensoredOrder (R : Rewards I) : Prop :=
  ∀ i, R.r1at0 i ≤ R.rbar1at1 i ∧ R.rbar0at1 i ≤ R.r0at0 i

/-- `r̄ᵢ⁰(p) = (1 − p) rᵢ⁰(0) + p r̄ᵢ⁰(1)` (Adelman & Wang, SSRN 4624694, Assumption 5, p.16). -/
def rbar0 (R : Rewards I) (i : I) (p : ℝ) : ℝ := (1 - p) * R.r0at0 i + p * R.rbar0at1 i

/-- `r̄ᵢ¹(p) = (1 − p) rᵢ¹(0) + p r̄ᵢ¹(1)` (Adelman & Wang, SSRN 4624694, Assumption 5, p.16). -/
def rbar1 (R : Rewards I) (i : I) (p : ℝ) : ℝ := (1 - p) * R.r1at0 i + p * R.rbar1at1 i

/-- The expected no-testing reward `r̄ᵢ(p) = (1 − p) r̄ᵢ⁰(p) + p r̄ᵢ¹(p)` (Adelman & Wang,
SSRN 4624694, (11), p.16). It is quadratic in `p`. -/
def rbar (R : Rewards I) (i : I) (p : ℝ) : ℝ := (1 - p) * rbar0 R i p + p * rbar1 R i p

/-- The reward of a tested individual at test result `γ`: `rᵢ⁰(0)` for `γ = 0`, and `rᵢ¹(1)` for
`γ ∈ {1,2}` (Adelman & Wang, SSRN 4624694, Definition 3 and Assumption 1, pp.14–15: after a test the
belief is the true carrier status). -/
def testedReward (R : Rewards I) (i : I) (γ : Fin 3) : ℝ :=
  if γ = 0 then R.r0at0 i else R.r1at1 i

/-- The expected cost `cᵢ(s) = cᵢˢ + ℙᵢ(s) cᵢᶠ` (Adelman & Wang, SSRN 4624694, §4.3, p.15; (8), p.13,
with one gene). -/
noncomputable def cost (R : Rewards I) (μ : Prior I) (s : State I) (i : I) : ℝ :=
  R.cs i + risk μ s i * R.cf i

/-- The terminal reward `∑_{l ∈ I \ s} r̄_l(ℙ_l(s))` of stopping in `s` (Adelman & Wang,
SSRN 4624694, (2), p.9, and the last term of (3), p.10). -/
noncomputable def stopValue (R : Rewards I) (μ : Prior I) (s : State I) : ℝ :=
  ∑ l ∈ untested s, rbar R l (risk μ s l)

/-- `rᵢ^δ = rᵢ⁰(0) + r̄ᵢ¹(1) − r̄ᵢ⁰(1) − rᵢ¹(0)` (Adelman & Wang, SSRN 4624694, p.15). -/
def rdelta (R : Rewards I) (i : I) : ℝ :=
  R.r0at0 i + R.rbar1at1 i - R.rbar0at1 i - R.r1at0 i

/-- The censoring effect `dᵢ = rᵢ¹(1) − r̄ᵢ¹(1)` (Adelman & Wang, SSRN 4624694, p.15). -/
def censoring (R : Rewards I) (i : I) : ℝ := R.r1at1 i - R.rbar1at1 i

end FamilyGenTest


