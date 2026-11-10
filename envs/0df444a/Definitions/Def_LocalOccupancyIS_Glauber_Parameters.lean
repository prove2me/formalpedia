-- Prove2me | Definitions.Def_LocalOccupancyIS_Glauber_Parameters
-- name    : LocalOccupancyIS_Glauber_Parameters
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T10:58:14.16762+00:00
-- url     : https://prove2.me/theorems/cbe86820-7568-4584-9894-6b14fcd7089a
-- title:
--   Explicit local occupancy parameters and admissible families
-- statement:
--   For positive integer $t$, nonnegative $b$ and degree parameter $\Delta$, define $s=(b+1)^{1/(2t-1)}$, $\rho=\Delta/s$ and $D=\log\rho$. The source parameters are
--
--   $$\lambda=\frac1{sD^{2t-1}},\quad M=4esD^{2t},\quad c=\exp\!\left(-\frac{4t(4e)^{1-1/t}}D\right),\quad z=W(p\Delta/c),$$
--   $$\beta_w=\frac{e^w}{p(1+w)},\quad\gamma_w=\frac1{c(1+w)},\quad\Gamma=\beta_z+\gamma_z\Delta.$$
--
--   The principal Lambert function is the published nonnegative inverse. Transfer constants are $C=\beta+\kappa\max\{\beta p,\gamma\Delta\}$ and $C_3$ uses $\kappa=3\Delta$. The relative-error scale is $t\log D/D$. A family indexed by natural numbers is admissible precisely when each $\Delta,t\ge1$, $b\ge0$, and
--
--   $$D\longrightarrow\infty,\qquad t\log D/D\longrightarrow0.$$
--
--   These are computed parameters and explicit limiting conditions, not success assumptions. The finite parameter theorem additionally requires $D\ge8et$.
-- source:
--   Ewan Davies, Brian Tan, STOC 2027 submission #982 (October 2026), Proposition 6 and Remark 1, p. 6–12; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/982.pdf#page=6

import Definitions.Def_LocalOccupancyIS_Glauber_Dynamics
import Definitions.Def_RiskBalancingMNL_lambertW

namespace LocalOccupancyIS.Glauber
noncomputable section

/-- The source's finite parameters, with t positive in all assertions. -/
def scale (t : ℕ) (b : ℝ) : ℝ := (b + 1) ^ (1 / (2 * (t : ℝ) - 1))
def rho (Δ : ℝ) (t : ℕ) (b : ℝ) : ℝ := Δ / scale t b
def D (Δ : ℝ) (t : ℕ) (b : ℝ) : ℝ := Real.log (rho Δ t b)
def fugacity (Δ : ℝ) (t : ℕ) (b : ℝ) : ℝ := 1 / (scale t b * D Δ t b ^ (2*t-1))
def cutoff (Δ : ℝ) (t : ℕ) (b : ℝ) : ℝ := 4 * Real.exp 1 * scale t b * D Δ t b ^ (2*t)
def correction (Δ : ℝ) (t : ℕ) (b : ℝ) : ℝ :=
  Real.exp (-(4 * (t : ℝ) * (4 * Real.exp 1) ^ (1 - 1 / (t : ℝ)) / D Δ t b))
def beta (lam z : ℝ) : ℝ := Real.exp z / (p lam * (1 + z))
def gamma (c z : ℝ) : ℝ := 1 / (c * (1 + z))
def optimizer (Δ : ℝ) (lam c : ℝ) : ℝ := RiskBalancingMNL.lambertW (p lam * Δ / c)
def Gamma (Δ : ℝ) (lam c : ℝ) : ℝ :=
  beta lam (optimizer Δ lam c) + gamma c (optimizer Δ lam c) * Δ

def transferConstant (Δ κ : ℕ) (lam β γ : ℝ) : ℝ :=
  β + κ * max (β * p lam) (γ * Δ)

def cThree (Δ : ℕ) (lam c : ℝ) : ℝ :=
  transferConstant Δ (3*Δ) lam (beta lam (optimizer Δ lam c)) (gamma c (optimizer Δ lam c))

/-- Error term with the absolute uniformity required in Remark 1. -/
def relativeError (Δ : ℝ) (t : ℕ) (b : ℝ) : ℝ := t * Real.log (D Δ t b) / D Δ t b

/-- Real upper-degree-bound families used by Proposition 6. -/
def AdmissibleReal (Δ : ℕ → ℝ) (t : ℕ → ℕ) (b : ℕ → ℝ) : Prop :=
  (∀ i, 1 ≤ Δ i ∧ 1 ≤ t i ∧ 0 ≤ b i) ∧
  Filter.Tendsto (fun i => D (Δ i) (t i) (b i)) Filter.atTop Filter.atTop ∧
  Filter.Tendsto (fun i => relativeError (Δ i) (t i) (b i)) Filter.atTop (nhds 0)

/-- Explicit sequence convention: both limits are hypotheses on the input family. -/
def Admissible (Δ t : ℕ → ℕ) (b : ℕ → ℝ) : Prop :=
  (∀ i, 1 ≤ Δ i ∧ 1 ≤ t i ∧ 0 ≤ b i) ∧
  Filter.Tendsto (fun i => D (Δ i) (t i) (b i)) Filter.atTop Filter.atTop ∧
  Filter.Tendsto (fun i => relativeError (Δ i) (t i) (b i)) Filter.atTop (nhds 0)

end
end LocalOccupancyIS.Glauber


