-- Prove2me | Definitions.Def_GallegoOzerADI_ZeroSetup_Model
-- name    : GallegoOzerADI_ZeroSetup_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T13:53:07.843821+00:00
-- url     : https://prove2.me/theorems/c3959967-577f-4af8-b7eb-a197a056f15b
-- title:
--   Inventory model with advance demand information and zero set-up cost: state transition (5)-(6) and functional equation (8)-(9) with $K_t = 0$
-- statement:
--   This file sets up the finite-horizon inventory model of Gallego and Özer with **advance demand information** and **zero set-up cost**.
--
--   **Data.** Let $L \ge 0$ be the supply lead time and $M \ge 1$ an integer; the information horizon is $N = L + M + 1$, so the paper's standing assumption $N > L + 1$ is $M \ge 1$. In period $t$ customers place orders $D_t = (D_{t,t}, D_{t,t+1}, \dots, D_{t,t+N})$ for delivery in periods $t, \dots, t+N$. A model consists of a horizon $T$, single-period cost functions $G_t : \mathbb{R} \to \mathbb{R}$, discount factors $\alpha_{t+1}$, and the law $\mu_t$ of the demand vector $D_t \in \mathbb{R}^{N+1}$.
--
--   **State and transition.** The state at the start of period $t$ is $(x_t, o_t)$, where $x_t$ is the modified inventory position and $o_t = (o_{t,t+L+1}, \dots, o_{t,t+N-1}) \in \mathbb{R}^M$ collects the demands already observed for periods beyond the protection period. If the position is raised to $y = x_t + z_t$ and $D_t$ is realised, then (Eqs. (5)–(6))
--
--   $$x_{t+1} = y - \sum_{k=0}^{L+1} D_{t,t+k} - o_{t,t+L+1}, \qquad o_{t+1,s} = o_{t,s} + D_{t,s} \quad (s = t+L+2, \dots, t+N),$$
--
--   with the convention $o_{t,t+N} = 0$, since nothing is observed beyond the information horizon.
--
--   **Functional equation.** With zero set-up cost, Eqs. (8)–(9) become, for $t = 1, \dots, T$,
--
--   $$J_t(x, o) = \inf_{y \ge x} V_t(y, o), \qquad V_t(y, o) = G_t(y) + \alpha_{t+1}\, \mathbb{E}\, J_{t+1}(x_{t+1}, o_{t+1}),$$
--
--   with terminal condition $J_{T+1} \equiv 0$ and the expectation taken over $D_t \sim \mu_t$. The file also defines the **smallest minimizer** of a function $f : \mathbb{R} \to \mathbb{R}$, namely the least $y$ with $f(y) = \min_x f(x)$, used for the base-stock level $y_t(o_t)$ of Eq. (11) and for the myopic level $y^m_t$.
--
--   **Standing hypotheses** (bundled as `Model.Assumptions`, required only for periods $1 \le t \le T$):
--   1. $M \ge 1$, i.e. $N > L + 1$ (p. 1349);
--   2. each $G_t$ is convex, and $G_t(y) \to \infty$ as $|y| \to \infty$;
--   3. each $G_t$ has at most linear growth, $|G_t(y)| \le a + b|y|$, and each component of $D_t$ is integrable;
--   4. $\alpha_{t+1} > 0$;
--   5. $\mu_t$ is a probability measure under which every component of $D_t$ is nonnegative almost surely.
--
--   Every theorem of the mission is a statement about this recursion.
--
--   **Formalization Note.** $G_t$ is taken as a primitive convex function rather than built from $c_t$, $g_t$ and the lead-time demand as on p. 1350; the paper's cost has this form, so the theorems generalise the paper's setting. The paper states coercivity for $\tilde G_t$ only, and uses without stating it: coercivity of $G_t$, nonnegative demands, $\alpha_{t+1} > 0$, and finiteness of the expectation in (9). Linear growth of $G_t$ together with finite first moments of demand is the guard chosen for that finiteness: it covers the usual holding/backorder costs with any demand law of finite mean (including the paper's Poisson example), but excludes, for example, quadratic $g_t$. Components are indexed from $0$: $D$ is a function on $\{0, \dots, N\}$ with $D(k) = D_{t,t+k}$, and $o$ a function on $\{0, \dots, M-1\}$ with $o(j) = o_{t,t+L+1+j}$. The infimum over $y \ge x$ is a real `iInf`, and the expectation a Bochner integral; under the standing hypotheses both are the genuine infimum and expectation. Attainment of the infimum is part of the theorems, not of the definitions.
-- source:
--   Gallego, Özer, Integrating Replenishment Decisions with Advance Demand Information, Management Science 47(10):1344–1360 (2001), pp. 1346–1351, Section 2 Eqs. (1)-(6), Section 4 Eqs. (8)-(9) and p. 1350, Section 5 (K_t = 0, Eq. (11)), p. 1352 (y^m_t)

import Mathlib

open MeasureTheory Filter Topology

namespace GallegoOzerADI.ZeroSetup

/-- The demand vector `D_t = (D_{t,t}, D_{t,t+1}, …, D_{t,t+N})` placed in period `t`, with
information horizon `N = L + M + 1`: component `k` is `D_{t,t+k}`. The index type is written
`Fin (L + 2 + M)` so that the protection-period part (`k ≤ L + 1`) and the part beyond it
(`k = L + 2 + j`, `j < M`) are `Fin.castAdd M` and `Fin.natAdd (L + 2)`. -/
abbrev DemandVec (L M : ℕ) : Type := Fin (L + 2 + M) → ℝ

/-- Inventory model with advance demand information and zero set-up cost (Section 2 and
Eqs. (8)–(9) with `K_t = 0`). `L` is the lead time and `M = N − L − 1` the number of observed
demands beyond the protection period, so the information horizon is `N = L + M + 1`.
Periods are `t = 1, …, T`; `G t` is the single-period cost `G_t`, `α (t + 1)` is the discount
factor `α_{t+1}` of Eq. (9), and `μ t` is the law of the demand vector `D_t`. -/
structure Model (L M : ℕ) where
  /-- The planning horizon `T`. -/
  T : ℕ
  /-- The single-period cost function `G_t : ℝ → ℝ`. -/
  G : ℕ → ℝ → ℝ
  /-- The discount factors; `α (t + 1)` multiplies the expected cost-to-go in period `t`. -/
  α : ℕ → ℝ
  /-- The law of the demand vector `D_t` on `ℝ^{N+1}`. -/
  μ : ℕ → Measure (DemandVec L M)

/-- Eq. (5): the modified inventory position at the start of period `t + 1`, given the order-up-to
level `y = x_t + z_t`, the observed demands `o = o_t = (o_{t,t+L+1}, …, o_{t,t+N−1})` beyond the
protection period (component `j` is `o_{t,t+L+1+j}`) and the demand vector `D = D_t`:
`x_{t+1} = y − D_{t,t} − ∑_{s=t+1}^{t+L+1} D_{t,s} − o_{t,t+L+1}`. -/
noncomputable def nextInv {L M : ℕ} (y : ℝ) (o : Fin M → ℝ) (D : DemandVec L M) : ℝ :=
  y - ∑ k : Fin (L + 2), D (Fin.castAdd M k) - (if h : 0 < M then o ⟨0, h⟩ else 0)

/-- Eq. (6): the observed demands beyond the protection period at the start of period `t + 1`,
`O_{t+1,s} = O_{t,s} + D_{t,s}` for `s = t+L+2, …, t+N`, with `O_{t,t+N} = 0` (nothing is observed
beyond the information horizon). Component `j` is `O_{t+1,t+L+2+j}`. -/
noncomputable def nextObs {L M : ℕ} (o : Fin M → ℝ) (D : DemandVec L M) : Fin M → ℝ :=
  fun j => (if h : j.val + 1 < M then o ⟨j.val + 1, h⟩ else 0) + D (Fin.natAdd (L + 2) j)

/-- The optimal cost-to-go `J_t(x, o)` of Eq. (8) with `K_t = 0`, by backward recursion:
`J_t(x, o) = inf_{y ≥ x} V_t(y, o)` for `t ≤ T`, and `J_t ≡ 0` for `t > T` (so `J_{T+1} ≡ 0`),
where `V_t(y, o) = G_t(y) + α_{t+1} E J_{t+1}(x_{t+1}, O_{t+1})` (Eq. (9)), the expectation being
over `D_t ∼ μ_t`. -/
noncomputable def Model.J {L M : ℕ} (P : Model L M) (t : ℕ) (x : ℝ) (o : Fin M → ℝ) : ℝ :=
  if _h : P.T < t then 0 else
    ⨅ y : {y : ℝ // x ≤ y},
      (P.G t y + P.α (t + 1) *
        ∫ D, P.J (t + 1) (nextInv (y : ℝ) o D) (nextObs o D) ∂(P.μ t))
termination_by P.T + 1 - t
decreasing_by omega

/-- Eq. (9): `V_t(y, o) = G_t(y) + α_{t+1} E J_{t+1}(x_{t+1}, O_{t+1})`, the expected cost when the
modified inventory position is raised to `y` in period `t` with observed demands `o`. -/
noncomputable def Model.V {L M : ℕ} (P : Model L M) (t : ℕ) (y : ℝ) (o : Fin M → ℝ) : ℝ :=
  P.G t y + P.α (t + 1) * ∫ D, P.J (t + 1) (nextInv y o D) (nextObs o D) ∂(P.μ t)

/-- Eq. (8) with `K_t = 0`: `J_t(x, o) = inf_{y ≥ x} V_t(y, o)` for `t ≤ T`. -/
theorem Model.J_of_le {L M : ℕ} (P : Model L M) {t : ℕ} (ht : t ≤ P.T) (x : ℝ)
    (o : Fin M → ℝ) : P.J t x o = ⨅ y : {y : ℝ // x ≤ y}, P.V t y o := by
  rw [Model.J, dif_neg (not_lt.mpr ht)]
  rfl

/-- The terminal condition: `J_t ≡ 0` for `t > T`, in particular `J_{T+1} ≡ 0`. -/
theorem Model.J_of_lt {L M : ℕ} (P : Model L M) {t : ℕ} (ht : P.T < t) (x : ℝ)
    (o : Fin M → ℝ) : P.J t x o = 0 := by
  rw [Model.J, dif_pos ht]

/-- `y` is the smallest minimizer of `f : ℝ → ℝ`, i.e. `y = min {y : f(y) = min_x f(x)}`. Used for
the base-stock level `y_t(o_t)` of Eq. (11) and for the myopic level `y^m_t` of p. 1352. -/
def IsLeastMinimizer (f : ℝ → ℝ) (y : ℝ) : Prop :=
  IsLeast {z : ℝ | ∀ x, f z ≤ f x} y

/-- The standing hypotheses on the primitives for periods `t = 1, …, T`:
`N > L + 1` (p. 1349), i.e. `M ≥ 1`; each `G_t` convex (p. 1348) and coercive,
`G_t(y) → ∞` as `|y| → ∞`; each `G_t` of at most linear growth and each `D_t` with a finite
first moment, so that the expectation in Eq. (9) is finite; discount factors `α_{t+1} > 0`;
`μ_t` a probability measure; demands nonnegative almost surely. -/
structure Model.Assumptions {L M : ℕ} (P : Model L M) : Prop where
  obs_pos : 0 < M
  convex : ∀ t, 1 ≤ t → t ≤ P.T → ConvexOn ℝ Set.univ (P.G t)
  coercive : ∀ t, 1 ≤ t → t ≤ P.T → Tendsto (P.G t) (cocompact ℝ) atTop
  linear_growth : ∀ t, 1 ≤ t → t ≤ P.T → ∃ a b : ℝ, ∀ y, |P.G t y| ≤ a + b * |y|
  discount_pos : ∀ t, 1 ≤ t → t ≤ P.T → 0 < P.α (t + 1)
  prob : ∀ t, 1 ≤ t → t ≤ P.T → IsProbabilityMeasure (P.μ t)
  demand_nonneg : ∀ t, 1 ≤ t → t ≤ P.T → ∀ᵐ D ∂(P.μ t), ∀ k, 0 ≤ D k
  demand_integrable : ∀ t, 1 ≤ t → t ≤ P.T → ∀ k,
    Integrable (fun D : DemandVec L M => D k) (P.μ t)

end GallegoOzerADI.ZeroSetup


