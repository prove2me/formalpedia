-- Prove2me | Definitions.Def_InvRiskAlloc_Model
-- name    : InvRiskAlloc_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:18:30.233015+00:00
-- url     : https://prove2.me/theorems/75d25e79-920d-44ba-955c-040057026423
-- title:
--   The Hou–Lu supply chain: CVaR retailer, demand quantile, $S_\beta$, $\Delta S$, $\Delta\rho$, Problems P(1,2), P(1), P(2) (1)–(3), option choice, Problem C (4)–(5), $\eta(\beta_2)$
-- statement:
--   This module sets up the supply chain of Hou and Lu (§3 and §4, pp. 7–20): one risk-neutral manufacturer, one retailer who maximizes the CVaR of his profit, and two contracts that allocate the inventory risk differently.
--
--   **Data and standing assumptions** (pp. 8, 11). A probability space $(\Omega,\mathcal F,\mu)$ carries the random demand $D$ and the random profit $\Psi$ of the retailer's outside opportunity. The parameters are the selling price $s$, the unit cost $c$, the two possible risk attitudes $\beta_1$ (the less risk-averse type) and $\beta_2$, and the prior $\nu=\Pr(\beta=\beta_1)$. The assumptions are:
--
--   1. $0<c<s$, $0<\beta_2<\beta_1\le 1$ and $0<\nu<1$;
--   2. $D$ is measurable, $D\ge 0$ almost surely, and $F_D(x)=\mu\{D\le x\}$ is continuous and strictly increasing on $[0,\infty)$ (demand supported on all of $[0,\infty)$);
--   3. $\Psi$ is measurable, $\Psi\ge 0$ almost surely, and $\rho_{\beta_1}(\Psi)$ is finite ($\beta_1<1$ or $\Psi$ integrable).
--
--   **Derived quantities.** With $\rho_\beta(X)=\sup_\eta\{\eta+\mathbb E[\min\{X-\eta,0\}]/\beta\}$ the $\beta$-CVaR (the published definition `RiskPostpone.Threshold.cvar`):
--
--   1. the quantile $F_D^{-1}(p)=\inf\{x: p\le F_D(x)\}$;
--   2. the CVaR of sales $S_\beta(q)=\rho_\beta(\min\{q,D\})$, and the CVaR of the system-wide profit, defined by the paper as $\rho_\beta(\phi(q))=sS_\beta(q)-cq$;
--   3. the first-best quantity $q^{NW}_\beta=\hat q^*_\beta=F_D^{-1}(\beta(1-c/s))$;
--   4. $\Delta S(q)=S_{\beta_1}(q)-S_{\beta_2}(q)$ and $\Delta\rho(\Psi)=\rho_{\beta_1}(\Psi)-\rho_{\beta_2}(\Psi)$;
--   5. $q$ is $(\Delta S)^{-1}(x)$ when $q\ge 0$, $F_D(q)\le\beta_1$ and $\Delta S(q)=x$.
--
--   **Pre-order screening problems** (p. 12). Problem P(1,2), (1): maximize $\nu(sS_{\beta_1}(q_1)-cq_1-U_1)+(1-\nu)(sS_{\beta_2}(q_2)-cq_2-U_2)$ over $q_1,q_2\ge 0$ and $U_1,U_2\in\mathbb R$ subject to
--   $$U_1\ge\rho_{\beta_1}(\Psi),\quad U_2\ge\rho_{\beta_2}(\Psi),\quad U_1\ge U_2+s\Delta S(q_2),\quad U_2\ge U_1-s\Delta S(q_1).$$
--   Problem P(1), (2): maximize $\nu(sS_{\beta_1}(q_1)-cq_1-U_1)$ over $q_1\ge0$, $U_1$ subject to $U_1-s\Delta S(q_1)\le\rho_{\beta_2}(\Psi)$ and $U_1\ge\rho_{\beta_1}(\Psi)$. Problem P(2), (3): maximize $(1-\nu)(sS_{\beta_2}(q_2)-cq_2-U_2)$ over $q_2\ge0$, $U_2$ subject to $U_2+s\Delta S(q_2)\le\rho_{\beta_1}(\Psi)$ and $U_2\ge\rho_{\beta_2}(\Psi)$. Optimal solutions, and unique optimal solutions, are defined for each problem.
--
--   **Option choice and expected order quantity** (pp. 8, 14, 20). The option $P$ is the problem with the highest attained optimal value; an infeasible problem does not compete, ties with P(1,2) go to P(1,2), and a tie between P(1) and P(2) goes to P(1). The manufacturer trades iff the chosen value is $\ge0$. The expected order quantity of an optimal solution of the chosen problem is $\nu q_1+(1-\nu)q_2$ under P(1,2), $\nu q_1$ under P(1), $(1-\nu)q_2$ under P(2), and $0$ without trade.
--
--   **Consignment problem C** (4)–(5), p. 19: maximize $sS_1(q)-cq-t$ over $q\ge0$, $t\in\mathbb R$ subject to $t\ge\rho_{\beta_i}(\Psi)$, $i=1,2$.
--
--   **Thresholds.** $\hat\beta_2=(1/\beta_2+\tfrac{\nu}{1-\nu}(1/\beta_2-1/\beta_1))^{-1}$ and $\hat q_2^{P(1,2):L}=F_D^{-1}(\hat\beta_2(s-c)/s)$ (p. 13); $\hat\beta_1=(1/\beta_1-\tfrac{1-\nu}{\nu}(1/\max\{\beta_2,(1-\nu c/s)\beta_1\}-1/\beta_1))^{-1}$ and $\hat q_1^{P(1,2):H}=F_D^{-1}(\hat\beta_1(s-c)/s)$ (p. 16); and $\eta$ is $\eta(\beta_2)$ when $1\le\eta<s/(s-c)$ and $\nu F_D^{-1}(\eta(1-c/s))+(1-\nu)F_D^{-1}(\beta_2(1-c/s))=F_D^{-1}(1-c/s)$ (p. 20).
--
--   These objects carry every statement of the mission. Optimal menus, the option $P$ and the consignment contract are defined through the optimization problems, never by the closed forms of Tables 2–4.
--
--   **Formalization Note** One bundled module holds the tightly coupled model definitions. The paper's density of $D$ is replaced by continuity of $F_D$, and "supported on $[0,\infty)$" is read as full support. The quantile is only applied at levels in $(0,1)$ by the statements. The interval for $\eta$ is half-open because $F_D^{-1}(1)$ is not a real number. Problems (2)–(3) print no sign constraint on $q$; $q\ge0$ is added as in (1).
-- source:
--   Hou–Lu, Allocating Inventory Risk in Retail Supply Chains, SSRN 4297536 (accepted manuscript of MSOM 2024, doi:10.1287/msom.2022.0624), §3 pp. 7–8, §4 p. 11, eqs. (1)–(3) p. 12, Prop. 2 p. 13, p. 14, Prop. 4 p. 16, eqs. (4)–(5) p. 19, §4.3.1 p. 20

import Mathlib
import Definitions.Def_RiskPostpone_Threshold_CVaR

open MeasureTheory

namespace InvRiskAlloc

/-- The data of the supply chain of Hou–Lu, *Allocating Inventory Risk in Retail Supply Chains*,
SSRN 4297536 (accepted manuscript of MSOM 2024, doi:10.1287/msom.2022.0624), §3 (pp. 7–8) and
§4 (p. 11): a probability space `(Ω, μ)`, the random demand `D`, the random profit `Ψ` of the
retailer's outside opportunity, the selling price `s`, the unit production cost `c`, the two
possible risk attitudes `β₁` (the less risk-averse type, "type 1") and `β₂` (type 2), and the
manufacturer's prior `ν = Pr(β = β₁)`. The assumptions on these data are `Model.Standing`. -/
structure Model (Ω : Type*) [MeasurableSpace Ω] where
  /-- the probability measure -/
  μ : Measure Ω
  /-- the random demand `D` -/
  D : Ω → ℝ
  /-- the random profit `Ψ` of the retailer's outside opportunity -/
  Ψ : Ω → ℝ
  /-- the fixed selling price `s` -/
  s : ℝ
  /-- the unit production cost `c` -/
  c : ℝ
  /-- the risk attitude `β₁` of the less risk-averse retailer type -/
  β₁ : ℝ
  /-- the risk attitude `β₂` of the more risk-averse retailer type -/
  β₂ : ℝ
  /-- the prior probability `ν` that the retailer's risk attitude is `β₁` -/
  ν : ℝ

namespace Model

variable {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω)

/-- The distribution function of demand, `F_D(x) = μ{D ≤ x}` (p. 8). -/
noncomputable def F (x : ℝ) : ℝ := (M.μ {ω | M.D ω ≤ x}).toReal

/-- The quantile `F_D⁻¹(p) = inf {x | p ≤ F_D(x)}` (p. 8).

**Formalization Note** The statements apply it only at levels `p ∈ (0, 1)`; under the
standing assumptions `F_D` is a continuous strictly increasing bijection `[0, ∞) → [0, 1)`, so
`F_D⁻¹(p)` is the unique `x ≥ 0` with `F_D(x) = p` there. -/
noncomputable def Finv (p : ℝ) : ℝ := sInf {x : ℝ | p ≤ M.F x}

/-- The standing assumptions of §3 (p. 8) and §4 (p. 11).

1. `μ` is a probability measure.
2. `0 < c < s` (the paper states `c < s`; `c > 0` excludes the undefined case
   `F_D⁻¹(1)` of a zero cost).
3. `0 < β₂ < β₁ ≤ 1` and `ν ∈ (0, 1)` (p. 11).
4. Demand is supported on `[0, ∞)` (p. 8): `D` is measurable, `D ≥ 0` almost surely, and its
   distribution function is continuous and strictly increasing on `[0, ∞)` (read: the support
   is all of `[0, ∞)`; the paper also assumes a density, which implies continuity).
5. The outside profit `Ψ` is measurable with `Ψ ≥ 0` almost surely ("Without loss of
   generality, we assume Ψ ≥ 0", p. 8), and `ρ_{β₁}(Ψ)` is finite: `β₁ < 1` or `Ψ` integrable.
-/
structure Standing : Prop where
  isProb : IsProbabilityMeasure M.μ
  c_pos : 0 < M.c
  c_lt_s : M.c < M.s
  β₂_pos : 0 < M.β₂
  β₂_lt_β₁ : M.β₂ < M.β₁
  β₁_le_one : M.β₁ ≤ 1
  ν_pos : 0 < M.ν
  ν_lt_one : M.ν < 1
  D_meas : Measurable M.D
  D_nonneg : ∀ᵐ ω ∂M.μ, 0 ≤ M.D ω
  F_cont : Continuous M.F
  F_strictMonoOn : StrictMonoOn M.F (Set.Ici 0)
  Ψ_meas : Measurable M.Ψ
  Ψ_nonneg : ∀ᵐ ω ∂M.μ, 0 ≤ M.Ψ ω
  Ψ_cvar_finite : M.β₁ < 1 ∨ Integrable M.Ψ M.μ

/-- The CVaR of sales, `S_β(q) = ρ_β(min{q, D})` (§3.1, p. 8), with `ρ_β` the β-CVaR
`ρ_β(X) = sup_η {η + E[min{X − η, 0}/β]}` of p. 8 (the published
`RiskPostpone.Threshold.cvar`). -/
noncomputable def S (β q : ℝ) : ℝ :=
  RiskPostpone.Threshold.cvar M.μ β (fun ω => min q (M.D ω))

/-- The CVaR of the system-wide profit `ϕ(q) = s·min{q, D} − cq`, which the paper *defines* as
`ρ_β(ϕ(q)) = s·S_β(q) − cq` (§3.1, p. 8). -/
noncomputable def rhoPhi (β q : ℝ) : ℝ := M.s * M.S β q - M.c * q

/-- The first-best quantity `q^NW_β = F_D⁻¹(β(1 − c/s))` (§3.1, p. 8); also written `q̂*_β`
(§3.2.1, p. 8). This is the paper's closed-form value; that it maximizes `ρ_β(ϕ(·))` is a
theorem (`InvRiskAlloc.first_best_quantity`), not part of the definition. -/
noncomputable def qNW (β : ℝ) : ℝ := M.Finv (β * (1 - M.c / M.s))

/-- `ΔS(q) = S_{β₁}(q) − S_{β₂}(q)` (p. 12). -/
noncomputable def ΔS (q : ℝ) : ℝ := M.S M.β₁ q - M.S M.β₂ q

/-- `Δρ(Ψ) = ρ_{β₁}(Ψ) − ρ_{β₂}(Ψ)` (p. 12). -/
noncomputable def Δρ : ℝ :=
  RiskPostpone.Threshold.cvar M.μ M.β₁ M.Ψ - RiskPostpone.Threshold.cvar M.μ M.β₂ M.Ψ

/-- `q` is the value `(ΔS)⁻¹(x)` of pp. 13 and 16: a solution of `ΔS(q) = x` on the range
`0 ≤ q ≤ F_D⁻¹(β₁)`, written `F_D(q) ≤ β₁` (for `β₁ = 1` the range is all of `[0, ∞)`). -/
def IsDeltaSInv (q x : ℝ) : Prop := 0 ≤ q ∧ M.F q ≤ M.β₁ ∧ M.ΔS q = x

/-- A pre-order contract menu for option P(1,2) after the change of variables
`U_i = s S_{β_i}(q_i) − t_i` (p. 12): order quantities `q₁, q₂` and CVaR utilities `U₁, U₂`. -/
structure Menu where
  q₁ : ℝ
  U₁ : ℝ
  q₂ : ℝ
  U₂ : ℝ

/-- Feasible set of Problem P(1,2), (1) p. 12: `q₁ ≥ 0`, `q₂ ≥ 0`, (IR-1), (IR-2), (IC-1),
(IC-2). -/
def Feasible12 : Set Menu :=
  {x | 0 ≤ x.q₁ ∧ 0 ≤ x.q₂ ∧
    RiskPostpone.Threshold.cvar M.μ M.β₁ M.Ψ ≤ x.U₁ ∧
    RiskPostpone.Threshold.cvar M.μ M.β₂ M.Ψ ≤ x.U₂ ∧
    x.U₂ + M.s * M.ΔS x.q₂ ≤ x.U₁ ∧
    x.U₁ - M.s * M.ΔS x.q₁ ≤ x.U₂}

/-- Objective of Problem P(1,2), (1) p. 12:
`ν(sS_{β₁}(q₁) − cq₁ − U₁) + (1 − ν)(sS_{β₂}(q₂) − cq₂ − U₂)`. -/
noncomputable def obj12 (x : Menu) : ℝ :=
  M.ν * (M.s * M.S M.β₁ x.q₁ - M.c * x.q₁ - x.U₁) +
    (1 - M.ν) * (M.s * M.S M.β₂ x.q₂ - M.c * x.q₂ - x.U₂)

/-- Feasible set of Problem P(1), (2) p. 12, for a contract `(q₁, U₁)`: `q₁ ≥ 0`, (EX-2)
`U₁ − sΔS(q₁) ≤ ρ_{β₂}(Ψ)` and (IR-1) `U₁ ≥ ρ_{β₁}(Ψ)`. -/
def Feasible1 : Set (ℝ × ℝ) :=
  {y | 0 ≤ y.1 ∧ y.2 - M.s * M.ΔS y.1 ≤ RiskPostpone.Threshold.cvar M.μ M.β₂ M.Ψ ∧
    RiskPostpone.Threshold.cvar M.μ M.β₁ M.Ψ ≤ y.2}

/-- Objective of Problem P(1), (2) p. 12: `ν(sS_{β₁}(q₁) − cq₁ − U₁)`. -/
noncomputable def obj1 (y : ℝ × ℝ) : ℝ := M.ν * (M.s * M.S M.β₁ y.1 - M.c * y.1 - y.2)

/-- Feasible set of Problem P(2), (3) p. 12, for a contract `(q₂, U₂)`: `q₂ ≥ 0`, (EX-1)
`U₂ + sΔS(q₂) ≤ ρ_{β₁}(Ψ)` and (IR-2) `U₂ ≥ ρ_{β₂}(Ψ)`. -/
def Feasible2 : Set (ℝ × ℝ) :=
  {y | 0 ≤ y.1 ∧ y.2 + M.s * M.ΔS y.1 ≤ RiskPostpone.Threshold.cvar M.μ M.β₁ M.Ψ ∧
    RiskPostpone.Threshold.cvar M.μ M.β₂ M.Ψ ≤ y.2}

/-- Objective of Problem P(2), (3) p. 12: `(1 − ν)(sS_{β₂}(q₂) − cq₂ − U₂)`. -/
noncomputable def obj2 (y : ℝ × ℝ) : ℝ := (1 - M.ν) * (M.s * M.S M.β₂ y.1 - M.c * y.1 - y.2)

/-- `x` is an optimal solution of Problem P(1,2). -/
def IsOpt12 (x : Menu) : Prop := x ∈ M.Feasible12 ∧ ∀ y ∈ M.Feasible12, M.obj12 y ≤ M.obj12 x

/-- `y` is an optimal solution of Problem P(1). -/
def IsOpt1 (y : ℝ × ℝ) : Prop := y ∈ M.Feasible1 ∧ ∀ z ∈ M.Feasible1, M.obj1 z ≤ M.obj1 y

/-- `y` is an optimal solution of Problem P(2). -/
def IsOpt2 (y : ℝ × ℝ) : Prop := y ∈ M.Feasible2 ∧ ∀ z ∈ M.Feasible2, M.obj2 z ≤ M.obj2 y

/-- `x` is the unique optimal solution of Problem P(1,2) (the reading of "the optimal
pre-order contract menu is given in Table k", pp. 13–16). -/
def IsUniqueOpt12 (x : Menu) : Prop := M.IsOpt12 x ∧ ∀ y, M.IsOpt12 y → y = x

/-- `y` is the unique optimal solution of Problem P(1). -/
def IsUniqueOpt1 (y : ℝ × ℝ) : Prop := M.IsOpt1 y ∧ ∀ z, M.IsOpt1 z → z = y

/-- `y` is the unique optimal solution of Problem P(2). -/
def IsUniqueOpt2 (y : ℝ × ℝ) : Prop := M.IsOpt2 y ∧ ∀ z, M.IsOpt2 z → z = y

/-- The three trading options under the pre-order contract (p. 11): trading with both types
P(1,2), only with the less risk-averse type P(1), only with the more risk-averse type P(2). -/
inductive PreOrderOption
  | P12
  | P1
  | P2
  deriving DecidableEq

/-- `M.Chooses o v`: the option `P` of p. 14 ("the option among P(1,2), P(1), and P(2) that
generates the highest profit") is `o`, and `v` is its optimal value (a maximum, attained).

**Formalization Note** An option whose feasible set is empty (P(1) can be infeasible, p. 16)
competes with no value. Ties go to P(1,2) (as in Propositions 3 and 6, pp. 15 and 17), and a
tie between P(1) and P(2) goes to P(1). -/
def Chooses : PreOrderOption → ℝ → Prop
  | .P12, v => IsGreatest (M.obj12 '' M.Feasible12) v ∧
      (∀ y ∈ M.Feasible1, M.obj1 y ≤ v) ∧ (∀ y ∈ M.Feasible2, M.obj2 y ≤ v)
  | .P1, v => IsGreatest (M.obj1 '' M.Feasible1) v ∧
      (∀ x ∈ M.Feasible12, M.obj12 x < v) ∧ (∀ y ∈ M.Feasible2, M.obj2 y ≤ v)
  | .P2, v => IsGreatest (M.obj2 '' M.Feasible2) v ∧
      (∀ x ∈ M.Feasible12, M.obj12 x < v) ∧ (∀ y ∈ M.Feasible1, M.obj1 y < v)

/-- `Q` is the expected order quantity under the pre-order contract (§4.3.1, p. 20) of an
optimal solution of the problem of the chosen option `P`: `νq₁ + (1 − ν)q₂` under P(1,2),
`νq₁` under P(1), `(1 − ν)q₂` under P(2), and `0` if the manufacturer does not trade, which
happens iff the optimal value is negative (§3.2.1, p. 8: "She will offer a contract if and only
if … ≥ 0"). -/
def IsPreOrderExpectedQty (Q : ℝ) : Prop :=
  (∃ v x, M.Chooses .P12 v ∧ x ∈ M.Feasible12 ∧ M.obj12 x = v ∧
      Q = if 0 ≤ v then M.ν * x.q₁ + (1 - M.ν) * x.q₂ else 0) ∨
  (∃ v y, M.Chooses .P1 v ∧ y ∈ M.Feasible1 ∧ M.obj1 y = v ∧
      Q = if 0 ≤ v then M.ν * y.1 else 0) ∨
  (∃ v y, M.Chooses .P2 v ∧ y ∈ M.Feasible2 ∧ M.obj2 y = v ∧
      Q = if 0 ≤ v then (1 - M.ν) * y.1 else 0)

/-- Feasible set of the consignment Problem C, (4)–(5) p. 19, for a contract `(q, t)`:
`q ≥ 0` and `t ≥ ρ_{β_i}(Ψ)` for `i = 1, 2`. -/
def FeasibleC : Set (ℝ × ℝ) :=
  {y | 0 ≤ y.1 ∧ RiskPostpone.Threshold.cvar M.μ M.β₁ M.Ψ ≤ y.2 ∧
    RiskPostpone.Threshold.cvar M.μ M.β₂ M.Ψ ≤ y.2}

/-- Objective of Problem C, (4) p. 19: `sS₁(q) − cq − t`. -/
noncomputable def objC (y : ℝ × ℝ) : ℝ := M.s * M.S 1 y.1 - M.c * y.1 - y.2

/-- `y = (q̃, t̃)` is an optimal solution of Problem C. -/
def IsOptC (y : ℝ × ℝ) : Prop := y ∈ M.FeasibleC ∧ ∀ z ∈ M.FeasibleC, M.objC z ≤ M.objC y

/-- `β̂₂ = (1/β₂ + ν/(1 − ν)·(1/β₂ − 1/β₁))⁻¹` (Proposition 2, p. 13). -/
noncomputable def betaHat2 : ℝ :=
  (1 / M.β₂ + M.ν / (1 - M.ν) * (1 / M.β₂ - 1 / M.β₁))⁻¹

/-- `q̂₂^{P(1,2):L} = F_D⁻¹(β̂₂(s − c)/s)` (Proposition 2, p. 13). -/
noncomputable def qL2 : ℝ := M.Finv (M.betaHat2 * (M.s - M.c) / M.s)

/-- `β̂₁ = (1/β₁ − (1 − ν)/ν·(1/max{β₂, (1 − νc/s)β₁} − 1/β₁))⁻¹` (Proposition 4, p. 16). -/
noncomputable def betaHat1 : ℝ :=
  (1 / M.β₁ - (1 - M.ν) / M.ν *
    (1 / max M.β₂ ((1 - M.ν * M.c / M.s) * M.β₁) - 1 / M.β₁))⁻¹

/-- `q̂₁^{P(1,2):H} = F_D⁻¹(β̂₁(s − c)/s)` (Proposition 4, p. 16). -/
noncomputable def qH1 : ℝ := M.Finv (M.betaHat1 * (M.s - M.c) / M.s)

/-- `η` is the value `η(β₂)` of §4.3.1 (p. 20): `η ∈ [1, s/(s − c))` and
`νF_D⁻¹(η(1 − c/s)) + (1 − ν)F_D⁻¹(β₂(1 − c/s)) = F_D⁻¹(1 − c/s)`.

**Formalization Note** The paper writes the closed interval `[1, s/(s − c)]`; at the right
endpoint `F_D⁻¹(1)` is not a real number, so it is excluded. -/
def IsEta (η : ℝ) : Prop :=
  1 ≤ η ∧ η < M.s / (M.s - M.c) ∧
    M.ν * M.Finv (η * (1 - M.c / M.s)) + (1 - M.ν) * M.Finv (M.β₂ * (1 - M.c / M.s)) =
      M.Finv (1 - M.c / M.s)

end Model

end InvRiskAlloc


