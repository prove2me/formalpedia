-- Prove2me | Definitions.Def_GallegoOzerADI_PositiveSetup_Model
-- name    : GallegoOzerADI_PositiveSetup_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T13:45:35.558321+00:00
-- url     : https://prove2.me/theorems/f2e69ba9-0a33-4d9b-bc58-a49a2613524e
-- title:
--   Finite-horizon inventory model with advance demand information and set-up costs: the functional equation (8)–(9)
-- statement:
--   **Demand and state.** Let $L \ge 0$ be the supply lead time and $N = L + M + 1$ the information horizon, with $M \ge 1$ (the paper's standing assumption $N > L + 1$ of Section 4). In period $t$ customers place orders $D_t = (D_{t,t}, D_{t,t+1}, \dots, D_{t,t+N})$ for periods $t, \dots, t+N$; $D_t$ has law $\mu_t$ on $\mathbb{R}^{N+1}$. The state at the start of period $t$ is $(x_t, o_t)$, where $x_t$ is the modified inventory position and
--   $$
--   o_t = (o_{t,t+L+1}, \dots, o_{t,t+N-1}) \in \mathbb{R}^{M}
--   $$
--   holds the observed demands for the periods beyond the protection period.
--
--   **Transition** (Eqs. (5)–(6)). After ordering up to $y \ge x_t$ and observing $D_t$,
--   $$
--   x_{t+1} = y - D_{t,t} - \sum_{s=t+1}^{t+L+1} D_{t,s} - o_{t,t+L+1},\qquad
--   o_{t+1,s} = o_{t,s} + D_{t,s}\quad (s = t+L+2, \dots, t+N),
--   $$
--   with $o_{t,t+N} = 0$ (nothing is observed beyond the information horizon).
--
--   **Costs.** $G_t : \mathbb{R} \to \mathbb{R}$ is the single-period cost, $K_t > 0$ the set-up cost and $\alpha_t > 0$ the discount factor. The model assumes: $G_t$ convex with $G_t(y) \to \infty$ as $|y| \to \infty$; $\alpha_{t+1}K_{t+1} \le K_t$ for all $t$; demands nonnegative almost surely; every demand component has a finite mean; and $|G_t(y)| \le a_t + b_t|y|$ for some constants.
--
--   **Functional equation** (Eqs. (8)–(9)). With $J_{T+1} \equiv 0$ and $\delta(z) = \mathbf{1}\{z > 0\}$, for $t = T, T-1, \dots, 1$,
--   $$
--   J_t(x, o) = \min_{y \ge x}\bigl\{K_t\delta(y - x) + V_t(y, o)\bigr\},\qquad
--   V_t(y, o) = G_t(y) + \alpha_{t+1}\,\mathbb{E}\,J_{t+1}(x_{t+1}, o_{t+1}),
--   $$
--   the expectation being over $D_t \sim \mu_t$. Finally $H_t(x, o) = K_t + \min_{y \ge x} V_t(y, o) - V_t(x, o)$. Two structural facts are proved in the definition file: $J_{T+1} \equiv 0$, and the recursion above holds for $1 \le t \le T$.
--
--   This is the object of every theorem of the mission: the $(s,S)$ structure of Theorem 1, the bounds of Lemma 3, and the horizon result of Theorem 2.
--
--   **Formalization Note** The demand vector is a function `Fin (L + M + 2) → ℝ` with component $k$ equal to $D_{t,t+k}$; $o$ is a function `Fin M → ℝ` with component $j$ equal to $o_{t,t+L+1+j}$. $J$ is defined by recursion on the number of remaining periods. Minima over $y \ge x$ are infima over $\{y : x \le y\}$, and the expectation is a Bochner integral. The paper builds $G_t(y) = (c_t - \gamma_t c_{t+1})y + \widetilde G_t(y)$ from holding–penalty costs; here $G_t$ is an abstract primitive, which covers the paper's setting. The paper states $K_t \ge 0$ in Section 2 and restricts to positive set-up costs in Section 4 (at $K_t = 0$ the reorder gap is never positive and $\max\{x : H_t \le 0\}$ does not exist). The paper uses without stating: positive discount factors; nonnegative demands (customers place orders); and finiteness of the expectation in (9), which it assumes through "$\widetilde G_t$ exists". Finite first moments with at most linear growth of $G_t$ make that expectation finite without any assumption on the derived $J_{t+1}$; the paper assumes coercivity for $\widetilde G_t$ and uses it for $G_t$ (p. 1350).
-- source:
--   Gallego, Özer, Integrating Replenishment Decisions with Advance Demand Information, Management Science 47(10):1344–1360 (2001), pp. 1347–1350, Section 2 Eqs. (1), (4)–(6) and Section 4 Eqs. (8)–(9), definition of H_t

import Mathlib
import Definitions.Def_GallegoOzerADI_PositiveSetup_SetupCost

open MeasureTheory Filter Topology

namespace GallegoOzerADI.PositiveSetup

/-- The finite-horizon inventory model with advance demand information and set-up costs of
Gallego–Özer (2001), §2 and §4, reduced to the functional equation (8)–(9).

Indices: the lead time is `L`, the information horizon is `N = L + M + 1`, so `N > L + 1`
is `M ≥ 1` (imposed as `[NeZero M]` by the theorems). Periods are `t = 1, …, T`.

* `G t : ℝ → ℝ` — the single-period cost `G_t(y)` of p. 1350, taken as a primitive;
* `K t` — the set-up cost `K_t` (positive: §4 treats positive set-up costs);
* `α t` — the discount factor `α_t`; in (9) period `t` uses `α (t + 1)`;
* `μ t` — the law of the demand vector `D_t = (D_{t,t}, …, D_{t,t+N})`, a measure on
  `Fin (N + 1) → ℝ = Fin (L + M + 2) → ℝ` with component `k` equal to `D_{t,t+k}`.

The hypotheses are those the paper states (`K_t ≥ 0`, here `> 0` by §4; `α_{t+1} K_{t+1} ≤ K_t`;
convex `G_t` with `G_t(y) → ∞` as `|y| → ∞`) and those it uses without stating: positive
discount factors, nonnegative demands, finite first moments of the demands and at most linear
growth of `G_t` (so that the expectation in (9) is finite). -/
structure Model (L M : ℕ) where
  /-- The planning horizon `T`. -/
  T : ℕ
  /-- Single-period cost `G_t`. -/
  G : ℕ → ℝ → ℝ
  /-- Set-up cost `K_t`. -/
  K : ℕ → ℝ
  /-- Discount factor `α_t`. -/
  α : ℕ → ℝ
  /-- Law of the demand vector `D_t`. -/
  μ : ℕ → Measure (Fin (L + M + 2) → ℝ)
  G_convex : ∀ t, ConvexOn ℝ Set.univ (G t)
  G_coercive : ∀ t, Tendsto (G t) (cocompact ℝ) atTop
  G_linearGrowth : ∀ t, ∃ a b : ℝ, ∀ y, |G t y| ≤ a + b * |y|
  K_pos : ∀ t, 0 < K t
  α_pos : ∀ t, 0 < α t
  discount_setup : ∀ t, α (t + 1) * K (t + 1) ≤ K t
  μ_prob : ∀ t, IsProbabilityMeasure (μ t)
  μ_nonneg : ∀ t, ∀ᵐ D ∂(μ t), ∀ k, 0 ≤ D k
  μ_integrable : ∀ t, ∀ k, Integrable (fun D : Fin (L + M + 2) → ℝ => D k) (μ t)

variable {L M : ℕ}

/-- The observed demand `o_{t,t+L+1+j}` for `j < M`, extended by `0` for `j ≥ M`
(the paper sets `O_{t,s} ≡ 0` for `s ≥ t + N`, p. 1347). -/
def obsComp (o : Fin M → ℝ) (j : ℕ) : ℝ :=
  if h : j < M then o ⟨j, h⟩ else 0

/-- Transition (5) of the modified inventory position: after ordering up to `y` and observing
`D = D_t`, `x_{t+1} = y - D_{t,t} - ∑_{s=t+1}^{t+L+1} D_{t,s} - o_{t,t+L+1}`, i.e.
`y - ∑_{k=0}^{L+1} D k - o 0`. -/
def nextX (y : ℝ) (o : Fin M → ℝ) (D : Fin (L + M + 2) → ℝ) : ℝ :=
  y - ∑ k : Fin (L + 2), D (Fin.castLE (by omega) k) - obsComp o 0

/-- Transition (6) of the observed demand beyond the protection period:
`O_{t+1,s} = O_{t,s} + D_{t,s}` for `s = t+L+2, …, t+N`, i.e. component `j` of the new vector is
`o (j + 1) + D (L + 2 + j)`, with `o M = O_{t,t+N} = 0`. -/
def nextO (o : Fin M → ℝ) (D : Fin (L + M + 2) → ℝ) : Fin M → ℝ :=
  fun j => obsComp o (j.val + 1) + D ⟨L + 2 + j.val, by have := j.isLt; omega⟩

/-- Backward recursion on the number of remaining periods: `P.Jgo n` is `J_{T+1-n}`.
`Jgo 0 = J_{T+1} ≡ 0`, and with `n + 1` periods remaining the current period is `t = T - n`,
where `J_t(x, o) = min_{y ≥ x} {K_t δ(y - x) + V_t(y, o)}` (8) and
`V_t(y, o) = G_t(y) + α_{t+1} E J_{t+1}(x_{t+1}, O_{t+1})` (9), the expectation being over
`D_t ∼ μ_t`. -/
noncomputable def Model.Jgo (P : Model L M) : ℕ → ℝ → (Fin M → ℝ) → ℝ
  | 0 => fun _ _ => 0
  | n + 1 => fun x o =>
      orderCost (P.K (P.T - n))
        (fun y => P.G (P.T - n) y + P.α (P.T - n + 1) *
          ∫ D, P.Jgo n (nextX y o D) (nextO o D) ∂(P.μ (P.T - n))) x

/-- The optimal cost `J_t(x, o)` of (8), for periods `1 ≤ t ≤ T`; `J_{T+1} ≡ 0`. -/
noncomputable def Model.J (P : Model L M) (t : ℕ) : ℝ → (Fin M → ℝ) → ℝ :=
  P.Jgo (P.T + 1 - t)

/-- The cost-to-go `V_t(y, o) = G_t(y) + α_{t+1} E J_{t+1}(x_{t+1}, O_{t+1})` of (9). -/
noncomputable def Model.V (P : Model L M) (t : ℕ) (y : ℝ) (o : Fin M → ℝ) : ℝ :=
  P.G t y + P.α (t + 1) * ∫ D, P.J (t + 1) (nextX y o D) (nextO o D) ∂(P.μ t)

/-- `H_t(x, o) = K_t + min_{y ≥ x} V_t(y, o) - V_t(x, o)` (p. 1350). -/
noncomputable def Model.H (P : Model L M) (t : ℕ) (x : ℝ) (o : Fin M → ℝ) : ℝ :=
  reorderGap (P.K t) (fun y => P.V t y o) x

/-- `J_{T+1} ≡ 0`. -/
theorem Model.J_terminal (P : Model L M) (x : ℝ) (o : Fin M → ℝ) : P.J (P.T + 1) x o = 0 := by
  simp [Model.J, Model.Jgo]

/-- The functional equation (8): for `1 ≤ t ≤ T`,
`J_t(x, o) = min_{y ≥ x} {K_t δ(y - x) + V_t(y, o)}`. -/
theorem Model.J_eq (P : Model L M) (t : ℕ) (ht : 1 ≤ t) (htT : t ≤ P.T) (x : ℝ)
    (o : Fin M → ℝ) : P.J t x o = orderCost (P.K t) (fun y => P.V t y o) x := by
  have h1 : P.T + 1 - t = (P.T - t) + 1 := by omega
  have h2 : P.T - (P.T - t) = t := by omega
  have h3 : P.T + 1 - (t + 1) = P.T - t := by omega
  simp only [Model.J, Model.V, h1, Model.Jgo, h2, h3]

end GallegoOzerADI.PositiveSetup


