-- Prove2me | Definitions.Def_CachonCoord_CapacityForecast_Model
-- name    : CachonCoord_CapacityForecast_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T04:44:54.229334+00:00
-- url     : https://prove2.me/theorems/a7cf042b-6166-46c7-9f34-b423be89e802
-- title:
--   §6.10.1–6.10.2, pp. 97–98 — the capacity procurement game: two demand types, costs c_k, c_p, revenue r, expected sales S_θ and chain profit Ω_θ
-- statement:
--   The capacity procurement game of Cachon's §6.10 (after Cachon and Lariviere 2001). A manufacturer $M$ buys a critical component from a single supplier $S$. Demand $D_\theta$ has one of two types $\theta \in \{h, l\}$ (high, low), with distribution function $F(x\mid\theta) = F_\theta(x)$. The standing assumptions of p. 97–98 are:
--
--   1. $F(x\mid\theta) = 0$ for all $x < 0$ and $F(x\mid\theta) > 0$ for all $x \ge 0$, so demand is nonnegative and has an atom at $0$;
--   2. $F(x\mid\theta)$ is differentiable (on $(0,\infty)$; it jumps at $0$);
--   3. $D_h$ stochastically dominates $D_l$: $F(x\mid h) < F(x\mid l)$ for all $x \ge 0$;
--   4. capacity costs $c_k > 0$ per unit, production costs $c_p > 0$ per unit, and $M$ earns $r > c_p + c_k$ per unit of demand satisfied; unused capacity has salvage value $0$.
--
--   With $x$ units of capacity the expected sales are
--   $$S_\theta(x) = x - \mathbb E\big[(x - D_\theta)^+\big],$$
--   and the supply chain's expected profit with $k$ units of capacity is
--   $$\Omega_\theta(k) = (r - c_p)\,S_\theta(k) - c_k k.$$
--
--   These are the primitives of every statement of the mission: the supply chain builds capacity $k$ before demand is known and produces $\min\{k, D_\theta\}$ afterwards.
--
--   **Formalization Note** Each demand law is a probability measure $\mu_\theta$ on $\mathbb R$ and $F_\theta$ is Mathlib's `cdf`, which is automatically nondecreasing and right-continuous ("increasing" on the page). Because $F_\theta(0) > 0 = F_\theta(0^-)$, differentiability is required only on $(0, \infty)$. $S_\theta$ is defined by the expectation; its integral form is a separate theorem of the mission. The prior $\rho = \Pr(\theta = h)$ of p. 97 plays no role in the statements of this mission and is not part of the structure.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.10.1, p. 97 (demand) and p. 98 (stages, costs); §6.10.2, p. 98, the displays defining S_θ and Ω_θ

import Mathlib

open MeasureTheory ProbabilityTheory

namespace CachonCoord.CapacityForecast

/-- The two demand types `θ ∈ {h, l}` of Cachon (2003), 3rd draft, §6.10.1, p. 97. -/
inductive DemandType where
  /-- High demand. -/
  | h
  /-- Low demand. -/
  | l
  deriving DecidableEq

/-- The capacity procurement game of Cachon (2003), 3rd draft, §6.10.1, pp. 97–98 (after Cachon and
Lariviere 2001). `μ θ` is the law of demand `D_θ` for type `θ`, with distribution function
`F(x|θ) = cdf (μ θ) x`. The fields are the page's assumptions:
* `F(x|θ) = 0` for all `x < 0` and `F(x|θ) > 0` for all `x ≥ 0` (so `D_θ` has an atom at `0`);
* `F(x|θ)` is differentiable; because of the atom at `0` this can only hold on `(0, ∞)`
  (monotonicity is automatic for a distribution function);
* `D_h` stochastically dominates `D_l`: `F(x|h) < F(x|l)` for all `x ≥ 0`;
* capacity costs `c_k > 0` per unit (`ck`), production costs `c_p > 0` per unit (`cp`), and the
  manufacturer earns `r > c_p + c_k` per unit of demand satisfied (`r`).
The salvage value of unused capacity is normalized to zero. -/
structure Model where
  /-- The demand law of each type. -/
  μ : DemandType → Measure ℝ
  /-- Each demand law is a probability measure. -/
  isProb : ∀ θ, IsProbabilityMeasure (μ θ)
  /-- `F(x|θ) = 0` for all `x < 0`. -/
  cdf_neg : ∀ θ (x : ℝ), x < 0 → cdf (μ θ) x = 0
  /-- `F(x|θ) > 0` for all `x ≥ 0`. -/
  cdf_pos : ∀ θ (x : ℝ), 0 ≤ x → 0 < cdf (μ θ) x
  /-- `F(x|θ)` is differentiable (on `(0, ∞)`, see the docstring). -/
  differentiable : ∀ θ (x : ℝ), 0 < x → DifferentiableAt ℝ (cdf (μ θ)) x
  /-- Stochastic dominance: `F(x|h) < F(x|l)` for all `x ≥ 0`. -/
  dominance : ∀ x : ℝ, 0 ≤ x → cdf (μ DemandType.h) x < cdf (μ DemandType.l) x
  /-- Revenue `r` per unit of demand satisfied. -/
  r : ℝ
  /-- Production cost `c_p` per unit. -/
  cp : ℝ
  /-- Capacity cost `c_k` per unit. -/
  ck : ℝ
  /-- `c_p > 0`. -/
  cp_pos : 0 < cp
  /-- `c_k > 0`. -/
  ck_pos : 0 < ck
  /-- `r > c_p + c_k`. -/
  margin : cp + ck < r

namespace Model

variable (M : Model)

instance (θ : DemandType) : IsProbabilityMeasure (M.μ θ) := M.isProb θ

/-- Expected sales with `x` units of capacity, `S_θ(x) = x − E[(x − D_θ)⁺]` (§6.10.2, p. 98). -/
noncomputable def S (θ : DemandType) (x : ℝ) : ℝ :=
  x - ∫ d, max (x - d) 0 ∂(M.μ θ)

/-- The supply chain's expected profit with `k` units of capacity,
`Ω_θ(k) = (r − c_p) S_θ(k) − c_k k` (§6.10.2, p. 98). -/
noncomputable def Omega (θ : DemandType) (k : ℝ) : ℝ :=
  (M.r - M.cp) * M.S θ k - M.ck * k

end Model

end CachonCoord.CapacityForecast


