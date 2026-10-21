-- Prove2me | Definitions.Def_RetirePartialInfo_Duality_Primal
-- name    : RetirePartialInfo_Duality_Primal
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T05:50:48.259542+00:00
-- url     : https://prove2.me/theorems/2d21c71d-5f61-4aa3-b370-1f75dcf1a2c1
-- title:
--   (8), (10), (12), pp. 7–11 — retirement times, consumption, the budget constraint, ℬ(x), ℬ₁(x), the primal objectives and values
-- statement:
--   **The primal problem** (Definitions 2.2, 2.4, Proposition 2.3, (10) and (12) of Chen, Jeon and Wong), at time $0$.
--
--   *Choices.* A **retirement time** is an $\mathcal F^S$-stopping time $\tau$ with values in $[0,T_1]$; it encodes the voluntary retirement indicator $R_s=\mathbf 1\{s\ge\tau\}$ of Definition 2.4. A **consumption rate process** is a measurable, $\mathcal F^S$-adapted process $c$ on $[0,T]$ with $\int_0^Tc_s\,ds<\infty$ a.s. (Definition 2.2); here it is required to be strictly positive. A wealth process $H$ is $\mathcal F^S$-adapted.
--
--   *Budget constraint* (8). For all $0\le s<t\le T$,
--   $$\tilde{\mathbb E}\Bigl[\frac{H_t-b(t)(1-R_t)}{B_t}+\int_s^t\frac{c_u}{B_u}\,du-\int_s^t\frac{b(u)}{B_u}\,dR_u\Bigm|\mathcal F^S_s\Bigr]\le\frac{H_s-b(s)(1-R_s)}{B_s},$$
--   where $\int_s^t\frac{b(u)}{B_u}dR_u=\mathbf 1\{s<\tau\le t\}\,b(\tau)/B_\tau$.
--
--   *Feasible set.* $\mathcal B(x)$ is the set of triplets $(c,H,R)$ satisfying the assumptions in Proposition 2.3 ($R$ as in Definition 2.4; $H_t\ge(1-R_t)b(t)$ is $\mathcal F^S$-adapted with $H_0=x$; $c$ is a consumption rate process) and (8). $\mathcal B_1(x)$ is the set of pairs $(c,H)$ with $(c,H,\mathbf 1_{s\in[0,T]})\in\mathcal B(x)$, i.e. with $\tau\equiv0$.
--
--   *Objectives and values.*
--   $$J(c,H,R)=\mathbb E\Bigl[\int_0^Te^{-\beta t}\bigl(U_1(t,c_t)-\ell(1-R_t)\bigr)dt+e^{-\beta T}U_2(T,H_T)\Bigr]\qquad(10),$$
--   $V(0,x,0)=\sup\{J(c,H,R):(c,H,R)\in\mathcal B(x)\}$; and for the retired agent $J_1(c,H)=\mathbb E[\int_0^Te^{-\beta s}U_1(s,c_s)ds+e^{-\beta T}U_2(T,H_T)]$, $V(0,x,1)=\sup\{J_1(c,H):(c,H)\in\mathcal B_1(x)\}$ (12).
--
--   This is the static (budget) form of the agent's problem of Definition 2.6; Proposition 2.3 shows it is equivalent to the dynamic problem with investment, and the paper works with it from (10) on.
--
--   **Formalization Note.** A $\{0,1\}$-valued, $\mathcal F^S$-adapted, right-continuous, nondecreasing $R$ with $R_s=1$ for $s\ge T_1$ is exactly $\mathbf 1\{s\ge\tau\}$ for an $\mathcal F^S$-stopping time $\tau\in[0,T_1]$; $\tau=0$ (immediate retirement) is allowed. Added to $\mathcal B(x)$, because the utilities are only given on $(0,\infty)$ and the expectations must be genuine integrals: $c>0$ on $[0,T]$, $H_T>0$ a.s., the random variable inside (8) is $\tilde{\mathbb P}$-integrable, $e^{-\beta t}(U_1(t,c_t)-\ell(1-R_t))$ is $dt\otimes\mathbb P$-integrable on $[0,T]\times\Omega$, and $U_2(T,H_T)$ is $\mathbb P$-integrable. The paper's "max" is a supremum. $H_0=x$ and the floor $H_t\ge(1-R_t)b(t)$ hold almost surely; (8) holds $\tilde{\mathbb P}$-a.s.
-- source:
--   Chen, Jeon, Wong, Optimal retirement under partial information, SSRN 3683553 (version of June 8, 2021), pp. 7–11, Definitions 2.2, 2.4, Proposition 2.3 (8), (10), (12)

import Mathlib
import Definitions.Def_RetirePartialInfo_Duality_Market
import Definitions.Def_RetirePartialInfo_Duality_Utility

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace RetirePartialInfo.Duality

/-- A choice triplet `(c, H, R)` of the primal problem (10), p. 10 (SSRN 3683553, June 8, 2021):
a consumption rate `c`, a wealth process `H`, and the retirement time `τ` that encodes the
retirement indicator `R_s = 1{s ≥ τ}` (see `Rind`). -/
structure Plan (Ω : Type*) where
  c : ℝ≥0 → Ω → ℝ
  H : ℝ≥0 → Ω → ℝ
  τ : Ω → ℝ≥0

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Definition 2.4, p. 7 (SSRN 3683553, June 8, 2021), in stopping-time form: `τ` is an
`F^S`-stopping time with values in `[0, T1]`.

**Formalization Note.** A `{0, 1}`-valued, `F^S`-adapted, right-continuous, nondecreasing process
`R` with `R_s = 1` for `s ≥ T1` is exactly `R_s = 1{s ≥ τ}` for such a `τ`
(`τ = inf {s : R_s = 1}`; right-continuity gives `R_τ = 1`, and `{τ ≤ s} = {R_s = 1} ∈ F^S_s`).
`τ = 0` is allowed: the agent may retire at once. -/
def IsRetirementTime (p : Params) (st : Setting Ω) (τ : Ω → ℝ≥0) : Prop :=
  IsStoppingTime (FS p st) (fun ω => (τ ω : WithTop ℝ≥0)) ∧ ∀ ω, (τ ω : ℝ) ≤ p.T1

/-- The retirement indicator `R_s = 1{s ≥ τ}` of Definition 2.4, p. 7. -/
noncomputable def Rind (τ : Ω → ℝ≥0) (s : ℝ≥0) (ω : Ω) : ℝ := if τ ω ≤ s then 1 else 0

/-- Definition 2.2, p. 7 (SSRN 3683553, June 8, 2021): `c = (c_t)_{t∈[0,T]}` is a consumption rate
process — a measurable, `F^S`-adapted process on `[0, T]` with `∫_0^T c_s ds < ∞` a.s. — which is
moreover strictly positive on `[0, T]`.

**Formalization Note.** Processes are indexed by `ℝ≥0`; only times in `[0, T]` are constrained
(joint measurability is that of the process stopped at `T`). The page allows `c ≥ 0`; the utility
`U_1(t, ·)` is only given on `(0, ∞)` (Assumption 2.2), so the primal class uses `c > 0`. -/
def IsConsumption (p : Params) (st : Setting Ω) (c : ℝ≥0 → Ω → ℝ) : Prop :=
  Measurable (fun z : ℝ≥0 × Ω => c (min z.1 p.Tn) z.2) ∧
  (∀ t : ℝ≥0, (t : ℝ) ≤ p.T → Measurable[FS p st t] (c t)) ∧
  (∀ t : ℝ≥0, (t : ℝ) ≤ p.T → ∀ ω, 0 < c t ω) ∧
  ∀ᵐ ω ∂st.P, IntegrableOn (fun s : ℝ => c s.toNNReal ω) (Icc 0 p.T)

/-- The Stieltjes integral `∫_s^t b(u)/B_u dR_u` of (8), p. 8, for `R = 1{· ≥ τ}`: the measure
`dR` is the unit atom at `τ`, so the integral over `(s, t]` is `1{s < τ ≤ t} b(τ)/B_τ`. -/
noncomputable def dRatom (p : Params) (τ : Ω → ℝ≥0) (s t : ℝ≥0) (ω : Ω) : ℝ :=
  if s < τ ω ∧ τ ω ≤ t then b p (τ ω) / Bt p (τ ω) else 0

/-- The random variable inside the conditional expectation of (8), p. 8:
`(H_t − b(t)(1 − R_t))/B_t + ∫_s^t c_u/B_u du − ∫_s^t b(u)/B_u dR_u`. -/
noncomputable def budgetLHS (p : Params) (q : Plan Ω) (s t : ℝ≥0) (ω : Ω) : ℝ :=
  (q.H t ω - b p t * (1 - Rind q.τ t ω)) / Bt p t +
    (∫ u in Ioc (s : ℝ) t, q.c u.toNNReal ω / Bt p u) - dRatom p q.τ s t ω

/-- **The budget constraint** (8), p. 8 (SSRN 3683553, June 8, 2021): for all `0 ≤ s < t ≤ T`,
`Ẽ[(H_t − b(t)(1 − R_t))/B_t + ∫_s^t c_u/B_u du − ∫_s^t b(u)/B_u dR_u | F^S_s]
  ≤ (H_s − b(s)(1 − R_s))/B_s`,
a conditional inequality under `P̃`, holding `P̃`-almost surely.

**Formalization Note.** The random variable inside is required to be `P̃`-integrable, so that the
conditional expectation is not Lean's junk value `0`. -/
def BudgetConstraint (p : Params) (st : Setting Ω) (Iθ : ℝ≥0 → Ω → ℝ) (q : Plan Ω) : Prop :=
  ∀ s t : ℝ≥0, s < t → (t : ℝ) ≤ p.T →
    Integrable (budgetLHS p q s t) (Pt p st Iθ) ∧
    (Pt p st Iθ)[budgetLHS p q s t | FS p st s] ≤ᵐ[Pt p st Iθ]
      fun ω => (q.H s ω - b p s * (1 - Rind q.τ s ω)) / Bt p s

/-- The running reward of (10), p. 10: `e^{−βt}(U_1(t, c_t) − ℓ(1 − R_t))`. -/
noncomputable def runReward (p : Params) (U1 : ℝ → ℝ → ℝ) (c : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ≥0)
    (t : ℝ) (ω : Ω) : ℝ :=
  Real.exp (-p.β * t) * (U1 t (c t.toNNReal ω) - p.ℓ * (1 - Rind τ t.toNNReal ω))

/-- **The primal objective** (10), p. 10 (SSRN 3683553, June 8, 2021), at time `0`:
`E[∫_0^T e^{−βt}(U_1(t, c_t) − ℓ(1 − R_t)) dt + e^{−βT} U_2(T, H_T)]`, for a consumption rate `c`,
a terminal wealth `H_T` and a retirement time `τ` (`R = 1{· ≥ τ}`). -/
noncomputable def Jobj (p : Params) (st : Setting Ω) (U1 U2 : ℝ → ℝ → ℝ) (c : ℝ≥0 → Ω → ℝ)
    (HT : Ω → ℝ) (τ : Ω → ℝ≥0) : ℝ :=
  ∫ ω, (∫ t in Icc (0 : ℝ) p.T, runReward p U1 c τ t ω) +
    Real.exp (-p.β * p.T) * U2 p.T (HT ω) ∂st.P

/-- **The feasible set** `ℬ(x)` of the primal problem (10), p. 10 (SSRN 3683553, June 8, 2021):
"the set of triplets `(c, H, R)` satisfying the assumptions in Proposition 2.3 and the budget
constraint (8)". The assumptions of Proposition 2.3, p. 8, are: `R` satisfies Definition 2.4;
`H_t ≥ (1 − R_t) b(t)` is an `F^S`-adapted process with `H_0 = x`; `c ≥ 0` is a consumption rate
process. So `(c, H, τ) ∈ ℬ(x)` iff
1. `τ` is a retirement time (Definition 2.4) and `c` a consumption rate process (Definition 2.2);
2. `H` is `F^S`-adapted on `[0, T]`, `H_0 = x` a.s., and `H_t ≥ (1 − R_t) b(t)` a.s. for every `t ∈ [0, T]`;
3. the budget constraint (8) holds;
4. `H_T > 0` a.s., and the objective (10) is integrable: `(t, ω) ↦ e^{−βt}(U_1(t, c_t) − ℓ(1 − R_t))`
   is `dt ⊗ P`-integrable on `[0, T] × Ω` and `U_2(T, H_T)` is `P`-integrable.

**Formalization Note.** Item 4 and `c > 0` are added: the utilities are given on `(0, ∞)` only, and
the expectation in (10) must be a genuine (finite) integral rather than Lean's junk value. Since
the positive part of the objective is bounded by the dual for every budget-feasible plan, the
integrability requirement only drops plans with objective `−∞`. -/
def Bclass (p : Params) (st : Setting Ω) (Iθ : ℝ≥0 → Ω → ℝ) (U1 U2 : ℝ → ℝ → ℝ) (x : ℝ) :
    Set (Plan Ω) :=
  {q | IsRetirementTime p st q.τ ∧ IsConsumption p st q.c ∧
    (∀ t : ℝ≥0, (t : ℝ) ≤ p.T → Measurable[FS p st t] (q.H t)) ∧ (∀ᵐ ω ∂st.P, q.H 0 ω = x) ∧
    (∀ t : ℝ≥0, (t : ℝ) ≤ p.T → ∀ᵐ ω ∂st.P, (1 - Rind q.τ t ω) * b p t ≤ q.H t ω) ∧
    BudgetConstraint p st Iθ q ∧
    (∀ᵐ ω ∂st.P, 0 < q.H p.Tn ω) ∧
    Integrable (fun z : ℝ × Ω => runReward p U1 q.c q.τ z.1 z.2)
      ((volume.restrict (Icc (0 : ℝ) p.T)).prod st.P) ∧
    Integrable (fun ω => U2 p.T (q.H p.Tn ω)) st.P}

/-- The objective (10) of a plan. -/
noncomputable def J (p : Params) (st : Setting Ω) (U1 U2 : ℝ → ℝ → ℝ) (q : Plan Ω) : ℝ :=
  Jobj p st U1 U2 q.c (q.H p.Tn) q.τ

/-- **The value of the working agent** `V(0, x, 0)` ((10), p. 10, and p. 11): the supremum of the
objective over `ℬ(x)`.

**Formalization Note.** The paper writes "max"; it is a supremum, and its attainment is part of
Proposition 2.4. -/
noncomputable def V0 (p : Params) (st : Setting Ω) (Iθ : ℝ≥0 → Ω → ℝ) (U1 U2 : ℝ → ℝ → ℝ)
    (x : ℝ) : ℝ :=
  sSup (J p st U1 U2 '' Bclass p st Iθ U1 U2 x)

/-- `ℬ_1(x)`, p. 11 (SSRN 3683553, June 8, 2021): "the set of pairs `(c, H)` such that
`(c, H, 1_{s∈[t,T]}) ∈ ℬ(x_t)`", at `t = 0`, i.e. with retirement time `τ ≡ 0`. -/
def B1class (p : Params) (st : Setting Ω) (Iθ : ℝ≥0 → Ω → ℝ) (U1 U2 : ℝ → ℝ → ℝ) (x : ℝ) :
    Set ((ℝ≥0 → Ω → ℝ) × (ℝ≥0 → Ω → ℝ)) :=
  {q | (⟨q.1, q.2, fun _ => 0⟩ : Plan Ω) ∈ Bclass p st Iθ U1 U2 x}

/-- The objective of (12), p. 11, at `t = 0`:
`E[∫_0^T e^{−βs} U_1(s, c_s) ds + e^{−βT} U_2(T, H_T)]` (the objective (10) with `R ≡ 1`). -/
noncomputable def J1 (p : Params) (st : Setting Ω) (U1 U2 : ℝ → ℝ → ℝ)
    (q : (ℝ≥0 → Ω → ℝ) × (ℝ≥0 → Ω → ℝ)) : ℝ :=
  Jobj p st U1 U2 q.1 (q.2 p.Tn) (fun _ => 0)

/-- **The value of the retired agent** `V(0, x, 1)` ((12), p. 11): the supremum of (12) over
`ℬ_1(x)` ("max" in the paper). -/
noncomputable def V1 (p : Params) (st : Setting Ω) (Iθ : ℝ≥0 → Ω → ℝ) (U1 U2 : ℝ → ℝ → ℝ)
    (x : ℝ) : ℝ :=
  sSup (J1 p st U1 U2 '' B1class p st Iθ U1 U2 x)

end RetirePartialInfo.Duality


