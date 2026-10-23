-- Prove2me | Definitions.Def_ProjectOutsourcing_SingleTask_Setting
-- name    : ProjectOutsourcing_SingleTask_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T23:07:29.579732+00:00
-- url     : https://prove2.me/theorems/820ffe91-5f04-4f5e-a0c6-a2f31f3f0918
-- title:
--   §3, pp. 7–12 — scale-family duration, Assumptions 1–2, contract forms (Table 3), profits, best response, Problem B (3), coordination, Φ^m, δ^TB_S (4)
-- statement:
--   This file sets up the single-task project model of Section 3.
--
--   **Primitives.** A client receives a one-time reward $Q>0$ when the project is completed. A subcontractor chooses a constant work rate $r\ge 0$. Let $Z\ge 0$ be a random variable with a density, cdf $F(z)=\mathbb P(Z\le z)$ and mean $\mathbb E[Z]=1$; at work rate $r>0$ the task duration is $T=Z/r$. Both firms discount at rate $\alpha>0$. The subcontractor incurs a realized total discounted cost $C(r,T)$, with expectation $c(r)=\mathbb E[C(r,Z/r)]$. The standing assumptions are
--
--   1. Assumption 1: $F$ is strictly concave on $[0,\infty)$;
--   2. Assumption 2: $c$ is differentiable, increasing and strictly convex on $[0,\infty)$, with $c(0)=0$ and $c'(0)=0$.
--
--   **Discounting.** For $s$ and $r>0$ write $\mathbb E_Z[e^{-sZ/r}]$ and $\mathbb E_Z[Ze^{-sZ/r}]$; both are set to $0$ at $r=0$, where the task never completes.
--
--   **Contracts (Table 3).** A contract term is a pair $(p,\beta)$, and the payment valued at completion is
--   $$\rho^{FP}=p,\quad \rho^{TF+}=\rho^{TF}=p+\beta e^{\alpha T},\quad \rho^{TB}=pe^{-\beta T},\quad \rho^{CS}=p+\beta Ce^{\alpha T},\quad \rho^{C+}=p+Ce^{\alpha T},$$
--   with $p\in\mathbb R$, $\beta\ge 0$ for TF+ and TB, $\beta\in\mathbb R$ for TF and $\beta\in[0,1]$ for CS. For FP and C+ the second coordinate is a dummy fixed at $0$ and $1$.
--
--   **Profits.** The subcontractor's and the client's profits are
--   $$\Pi^m_S(\Psi,r)=\mathbb E_Z\big[\rho^m(\Psi,Z/r,C(r,Z/r))e^{-\alpha Z/r}\big]-c(r),\qquad \Pi^m_C(\Psi,r)=\mathbb E_Z\big[(Q-\rho^m(\Psi,Z/r,C(r,Z/r)))e^{-\alpha Z/r}\big],$$
--   and the system profit is $\Pi(r)=Q\,\mathbb E_Z[e^{-\alpha Z/r}]-c(r)$, eq. (1). A rate $r^*$ is system optimal if it maximizes $\Pi$ on $[0,\infty)$.
--
--   **Bargaining.** The subcontractor's chosen rate $\hat r$ under $\Psi$ maximizes $\Pi^m_S(\Psi,\cdot)$ on $[0,\infty)$. Following footnote 1, if a system-optimal rate is among his maximizers, he chooses a system-optimal rate. A feasible outcome of Problem B (3) is an admissible term together with the chosen rate, with both profits nonnegative (disagreement points normalized to $0$). An outcome solves Problem B for bargaining power $\theta$ if it maximizes the Nash product $\Omega=(\Pi_S)^\theta(\Pi_C)^{1-\theta}$ over all feasible outcomes. Form $m$ **coordinates** the system at $\theta$ if Problem B has a solution and every solution induces a system-optimal rate, and
--   $$\Phi^m=\{\theta\in[0,1]: m \text{ coordinates the system at } \theta\}.$$
--   Finally, eq. (4) defines
--   $$\delta^{TB}_S(\beta)=\frac{\alpha Q\,\mathbb E_Z[Ze^{-\alpha Z/r^*}]\,\mathbb E_Z[e^{-(\alpha+\beta)Z/r^*}]}{(\alpha+\beta)\,\mathbb E_Z[Ze^{-(\alpha+\beta)Z/r^*}]}-c(r^*).$$
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** The law of $Z$ is a measure on $\mathbb R$ with no mass on $(-\infty,0)$ and absolutely continuous with respect to Lebesgue measure. Support $[0,\infty)$ is not written separately: a nondecreasing, bounded, strictly concave cdf is strictly increasing on $[0,\infty)$. Two hypotheses are added to the page: $\alpha>0$, which the page leaves implicit in "discount rate", and integrability of the realized cost $C(r,Z/r)$, so that $c(r)=\mathbb E[C]$ and $\mathbb E[\beta C]=\beta c(r)$ have meaning. At $r=0$ every discounted quantity is $0$, except that the TF and TF+ down payment $\beta$, paid at the start, is still received. This is the limit as $r\downarrow 0$, and it avoids Lean's $z/0=0$, which would read as instant completion. The best response is a relation, not a function: a term without a best response (for example C+ with $p>0$) has no feasible outcome. The Nash product uses `Real.rpow` and is only compared on feasible outcomes, where both factors are nonnegative. There $0^0=1$, so $\Omega=\Pi_S$ at $\theta=1$ and $\Omega=\Pi_C$ at $\theta=0$. The system-optimal rate is never defined by a supremum or a choice; statements take it as a variable satisfying the optimality predicate.
-- source:
--   Hou, Lu, Deng, Shen, Coordinating Project Outsourcing through Bilateral Contract Negotiations, author manuscript (SSRN 3443865; MSOM, doi:10.1287/msom.2020.0911), pp. 7–12, §3, Assumptions 1–2, (1), Table 3, §3.2, (3), (4), footnote 1

import Mathlib

namespace ProjectOutsourcing.SingleTask

open MeasureTheory

/-- The six contract forms of Table 3 (p. 9): fixed-price (FP), two-part fixed-price with nonnegative
down payment (TF+), two-part fixed-price (TF), time-based incentive (TB), cost-sharing (CS) and
cost-plus (C+). -/
inductive Form
  | FP
  | TFplus
  | TF
  | TB
  | CS
  | Cplus

/-- Primitive data of the single-task model of §3 (pp. 7–8): the client's reward `Q`, the discount
rate `alpha`, the law `μ` of the standardized duration `Z` (the duration at work rate `r` is `Z / r`),
the realized total discounted cost `C r t` at work rate `r` and duration `t`, and the expected total
discounted cost `c r`. -/
structure Model where
  Q : ℝ
  alpha : ℝ
  μ : Measure ℝ
  C : ℝ → ℝ → ℝ
  c : ℝ → ℝ

/-- The cdf `F(z) = P(Z ≤ z)` of `Z`. -/
noncomputable def Model.F (M : Model) (z : ℝ) : ℝ := (M.μ (Set.Iic z)).toReal

/-- The standing assumptions of §3 (pp. 7–8): `Q > 0`; `Z ≥ 0` has a density and mean `E[Z] = 1`;
Assumption 1 (the cdf `F` is strictly concave); `c(r) = E[C(r, Z/r)]`; Assumption 2 (`c` is
differentiable, increasing and strictly convex, `c(0) = 0`, `c'(0) = 0`). Added: `alpha > 0` and the
integrability of the realized cost. -/
structure Model.Valid (M : Model) : Prop where
  Q_pos : 0 < M.Q
  alpha_pos : 0 < M.alpha
  isProb : IsProbabilityMeasure M.μ
  nonneg : M.μ (Set.Iio 0) = 0
  hasPdf : M.μ ≪ volume
  integrable_id : Integrable id M.μ
  mean_one : ∫ z, z ∂M.μ = 1
  assumption1 : StrictConcaveOn ℝ (Set.Ici 0) M.F
  cost_integrable : ∀ r, 0 < r → Integrable (fun z => M.C r (z / r)) M.μ
  cost_mean : ∀ r, 0 < r → ∫ z, M.C r (z / r) ∂M.μ = M.c r
  c_diff : DifferentiableOn ℝ M.c (Set.Ici 0)
  c_mono : MonotoneOn M.c (Set.Ici 0)
  c_strictConvex : StrictConvexOn ℝ (Set.Ici 0) M.c
  c_zero : M.c 0 = 0
  c_deriv_zero : HasDerivWithinAt M.c 0 (Set.Ici 0) 0

/-- `E_Z[e^{-s Z / r}]` at work rate `r > 0`; `0` at `r ≤ 0` (the task never completes). -/
noncomputable def disc (M : Model) (s r : ℝ) : ℝ :=
  if 0 < r then ∫ z, Real.exp (-(s * z / r)) ∂M.μ else 0

/-- `E_Z[Z e^{-s Z / r}]` at work rate `r > 0`; `0` at `r ≤ 0`. -/
noncomputable def discZ (M : Model) (s r : ℝ) : ℝ :=
  if 0 < r then ∫ z, z * Real.exp (-(s * z / r)) ∂M.μ else 0

/-- Payment `ρ^m(Ψ^m, T, C)` of Table 3, valued at the task completion time `T`, for the contract term
`(p, β)` and realized discounted cost `Cv`. For FP and C+, `β` is a dummy coordinate. -/
noncomputable def pay (M : Model) : Form → ℝ → ℝ → ℝ → ℝ → ℝ
  | .FP, p, _, _, _ => p
  | .TFplus, p, β, T, _ => p + β * Real.exp (M.alpha * T)
  | .TF, p, β, T, _ => p + β * Real.exp (M.alpha * T)
  | .TB, p, β, T, _ => p * Real.exp (-(β * T))
  | .CS, p, β, T, Cv => p + β * Cv * Real.exp (M.alpha * T)
  | .Cplus, p, _, T, Cv => p + Cv * Real.exp (M.alpha * T)

/-- Admissible contract terms `(p, β)` of Table 3: `p ∈ ℝ` always; `β ≥ 0` for TF+ and TB, `β ∈ ℝ` for
TF, `β ∈ [0, 1]` for CS; the dummy `β` is pinned to `0` for FP and to `1` for C+. -/
def params : Form → Set (ℝ × ℝ)
  | .FP => {x | x.2 = 0}
  | .TFplus => {x | 0 ≤ x.2}
  | .TF => Set.univ
  | .TB => {x | 0 ≤ x.2}
  | .CS => {x | x.2 ∈ Set.Icc 0 1}
  | .Cplus => {x | x.2 = 1}

/-- The part of the payment made at the start of the task: the down payment `β` of TF+ and TF. -/
def upfront : Form → ℝ → ℝ
  | .TFplus, β => β
  | .TF, β => β
  | .FP, _ => 0
  | .TB, _ => 0
  | .CS, _ => 0
  | .Cplus, _ => 0

/-- Expected discounted payment `E_Z[ρ^m(Ψ, Z/r, C(r, Z/r)) e^{-α Z / r}]` at work rate `r > 0`; at
`r ≤ 0` the task never completes and only the down payment is received. -/
noncomputable def discPay (M : Model) (m : Form) (Ψ : ℝ × ℝ) (r : ℝ) : ℝ :=
  if 0 < r then
    ∫ z, pay M m Ψ.1 Ψ.2 (z / r) (M.C r (z / r)) * Real.exp (-(M.alpha * z / r)) ∂M.μ
  else upfront m Ψ.2

/-- The subcontractor's profit `Π^m_S(Ψ, r)` (p. 10). -/
noncomputable def subProfit (M : Model) (m : Form) (Ψ : ℝ × ℝ) (r : ℝ) : ℝ :=
  discPay M m Ψ r - M.c r

/-- The client's profit `Π^m_C(Ψ, r)` (p. 10). -/
noncomputable def clientProfit (M : Model) (m : Form) (Ψ : ℝ × ℝ) (r : ℝ) : ℝ :=
  M.Q * disc M M.alpha r - discPay M m Ψ r

/-- The system profit `Π(r) = Q E_Z[e^{-α Z / r}] - c(r)` of (1), p. 8. -/
noncomputable def sysProfit (M : Model) (r : ℝ) : ℝ :=
  M.Q * disc M M.alpha r - M.c r

/-- `r` is a system-optimal work rate: it maximizes `Π` over `[0, ∞)`. -/
def IsSystemOpt (M : Model) (r : ℝ) : Prop :=
  0 ≤ r ∧ IsMaxOn (sysProfit M) (Set.Ici 0) r

/-- `r` is the subcontractor's chosen work rate `r̂^m(Ψ)`: it maximizes `Π^m_S(Ψ, ·)` over `[0, ∞)`, and,
per footnote 1 (p. 12), when a system-optimal rate is among his best responses he chooses a
system-optimal rate. -/
def IsChosenRate (M : Model) (m : Form) (Ψ : ℝ × ℝ) (r : ℝ) : Prop :=
  0 ≤ r ∧ IsMaxOn (subProfit M m Ψ) (Set.Ici 0) r ∧
    ((∃ r', IsSystemOpt M r' ∧ IsMaxOn (subProfit M m Ψ) (Set.Ici 0) r') → IsSystemOpt M r)

/-- A feasible outcome of Problem B (3) with disagreement points `0`: an admissible term `x.1`, the
work rate `x.2` the subcontractor chooses under it, and both profits nonnegative. -/
def Feasible (M : Model) (m : Form) (x : (ℝ × ℝ) × ℝ) : Prop :=
  x.1 ∈ params m ∧ IsChosenRate M m x.1 x.2 ∧
    0 ≤ subProfit M m x.1 x.2 ∧ 0 ≤ clientProfit M m x.1 x.2

/-- The Nash product `S^θ C^{1-θ}` (`Real.rpow`; used only for `S, C ≥ 0`). -/
noncomputable def nashProd (θ S C : ℝ) : ℝ := S ^ θ * C ^ (1 - θ)

/-- `x` solves Problem B (3) for bargaining power `θ`: it is feasible and its Nash product is at least
that of every feasible outcome. -/
def IsNashSol (M : Model) (m : Form) (θ : ℝ) (x : (ℝ × ℝ) × ℝ) : Prop :=
  Feasible M m x ∧ ∀ y, Feasible M m y →
    nashProd θ (subProfit M m y.1 y.2) (clientProfit M m y.1 y.2) ≤
      nashProd θ (subProfit M m x.1 x.2) (clientProfit M m x.1 x.2)

/-- System coordination through bargaining (p. 11): Problem B has a solution, and every solution
induces a system-optimal work rate. -/
def Coordinates (M : Model) (m : Form) (θ : ℝ) : Prop :=
  (∃ x, IsNashSol M m θ x) ∧ ∀ x, IsNashSol M m θ x → IsSystemOpt M x.2

/-- `Φ^m`: the bargaining powers `θ ∈ [0, 1]` at which form `m` coordinates the system. -/
def Phi (M : Model) (m : Form) : Set ℝ :=
  {θ | θ ∈ Set.Icc 0 1 ∧ Coordinates M m θ}

/-- `δ^TB_S(β)` of (4), p. 11, at the system-optimal rate `rStar`. -/
noncomputable def deltaTB (M : Model) (rStar β : ℝ) : ℝ :=
  M.alpha * M.Q * discZ M M.alpha rStar * disc M (M.alpha + β) rStar /
      ((M.alpha + β) * discZ M (M.alpha + β) rStar) - M.c rStar

end ProjectOutsourcing.SingleTask


