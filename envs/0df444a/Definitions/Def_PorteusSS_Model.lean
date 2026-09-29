-- Prove2me | Definitions.Def_PorteusSS_Model
-- name    : PorteusSS_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T17:52:59.263261+00:00
-- url     : https://prove2.me/theorems/a6d37c2b-15c4-4ce0-b1fd-b49dc26bec6e
-- title:
--   The finite-horizon inventory model: recursion (2)–(4), $Y_n(x)$, $G_{cn}$, standing assumptions and A1–A5
-- statement:
--   The model of §III: orders are delivered immediately, shortages are backlogged, periods are indexed by the number $n$ of periods remaining, demands are i.i.d. with density $\varphi$, costs $n$ periods ahead are discounted by $\alpha^n$, $m$ is the holding-and-shortage cost charged on ending inventory, $f_0$ is the terminal cost of leftover (or backlogged) inventory, and $c$ is the ordering cost.
--
--   With $L = m * \varphi$, the value functions are $f_0$ and, for $n \ge 1$,
--   $$ h_n = L + \alpha\, f_{n-1} * \varphi, \qquad f_n(x) = \inf_{y \ge x} \{ c(y - x) + h_n(y) \} \qquad \text{(3), (4)} .$$
--   The set of optimal post-order levels at pre-order level $x$ in period $n$ is
--   $$ Y_n(x) = \{ S : S \ge x \text{ and } c(S - x) + h_n(S) \le c(y - x) + h_n(y) \text{ for all } y \ge x \}, $$
--   and for a slope $\kappa \in C$, $G_{\kappa n}(y) = \kappa y + h_n(y)$ (eq. (7)).
--
--   The **standing assumptions** (§§II–III) bundled as the model hypothesis are: $c$ satisfies the assumptions of §II; $0 \le \alpha \le 1$; $\varphi$ is a one-sided Pólya density; $m$ is PF-integrable and bounded below. The assumptions of §VI are:
--
--   1. **A1.** $(c_0 - \alpha c_\infty)\cdot + m$ is nonincreasing on $R^- = (-\infty,0)$.
--   2. **A2.** $(c_0 - \alpha c_\infty) x + m(x) \to \infty$ as $x \to -\infty$.
--   3. **A3.** $(1-\alpha)\kappa\cdot + m$ is non-$(1-\alpha)K_\kappa$-decreasing on $[0,\infty)$ for $\kappa \in C$.
--   4. **A4.** $(1-\alpha) c_\infty x + m(x) \to \infty$ as $x \to \infty$.
--   5. **A5.** $f_0$ is piecewise continuous and PF-integrable, $c_\infty\cdot + f_0$ is nonincreasing on $R^-$, and $\kappa\cdot + f_0$ is non-$K_\kappa$-decreasing on $\mathbb R$ for $\kappa \in C$.
--
--   These objects are what the main theorem is about: it asserts that, under A1–A5, $Y_n(x)$ is always nonempty and can be selected as a generalized $(s,S)$ policy.
--
--   **Formalization Note.** Since $\varphi$ vanishes on $R^-$, the paper's $L(y) = \int_0^\infty m(y-\xi)\varphi(\xi)\,d\xi$ equals the full-line convolution used here. The infimum in (4) is Lean's `⨅` over $\{y \ge x\}$, which returns $0$ on a set unbounded below, and the convolutions return $0$ on non-integrable integrands; the main theorem concludes rather than assumes that these values are genuine. $h_n$ is only meaningful for $n \ge 1$ (at $n = 0$ the Lean definition reuses $f_0$). $Y_n(x)$ is defined by its inequality, not through the infimum. The paper's primary definition of $G_{cn}$ is $g_{cn} * \varphi$ with $g_{cn}(x) = cx + m(x) + \alpha f_{n-1}(x) + c\mu$, $\mu = \int_0^\infty \xi \varphi(\xi)\,d\xi$ ((5)–(6)); eq. (7) is its stated identity, valid whenever the integrals exist, and is used as the definition here.
-- source:
--   Porteus, On the Optimality of Generalized (s, S) Policies, Management Science 17(7):411–426 (1971), p. 413, §III and eqs. (2)–(7); p. 414, Y_n(x); p. 417, §VI assumptions A1–A5

import Mathlib
import Definitions.Def_PorteusSS_Functions
import Definitions.Def_PorteusSS_OrderingCost

open MeasureTheory Filter Topology Set

namespace PorteusSS

/-! The finite-horizon inventory model of §III with data `c` (ordering cost), `m` (holding and
shortage cost on ending inventory), `φ` (demand density), `f0` (terminal cost) and `α`
(discount factor). Periods are counted backwards: `n` is the number of periods remaining. -/

/-- `h_n` from its predecessor: given `f_{n-1}`, `h_n(y) = L(y) + α (f_{n-1} * φ)(y)` with
`L = m * φ`  (eq. (3)). -/
noncomputable def hStep (m φ : ℝ → ℝ) (α : ℝ) (fPrev : ℝ → ℝ) (y : ℝ) : ℝ :=
  conv m φ y + α * conv fPrev φ y

/-- The value functions of eqs. (2)/(4): `f_0 = f0` and
`f_n(x) = inf_{y ≥ x} {c(y - x) + h_n(y)}` for `n ≥ 1`. -/
noncomputable def valueFn (c m φ f0 : ℝ → ℝ) (α : ℝ) : ℕ → ℝ → ℝ
  | 0 => f0
  | n + 1 => fun x => ⨅ y : Ici x, c ((y : ℝ) - x) + hStep m φ α (valueFn c m φ f0 α n) y

/-- `h_n = L + α f_{n-1} * φ` (eq. (3)), meaningful for `n ≥ 1`. -/
noncomputable def hFn (c m φ f0 : ℝ → ℝ) (α : ℝ) (n : ℕ) (y : ℝ) : ℝ :=
  hStep m φ α (valueFn c m φ f0 α (n - 1)) y

/-- `Y_n(x)`, the set of optimal post-order inventory levels when the pre-order level is `x`
(p. 414): `S ≥ x` and `c(S - x) + h_n(S) ≤ c(y - x) + h_n(y)` for all `y ≥ x`. -/
def Yset (c m φ f0 : ℝ → ℝ) (α : ℝ) (n : ℕ) (x : ℝ) : Set ℝ :=
  {S | x ≤ S ∧ ∀ y : ℝ, x ≤ y →
    c (S - x) + hFn c m φ f0 α n S ≤ c (y - x) + hFn c m φ f0 α n y}

/-- `G_{κ n} = κ· + h_n` (eq. (7)), for a slope `κ ∈ C`. -/
noncomputable def Gfn (c m φ f0 : ℝ → ℝ) (α κ : ℝ) (n : ℕ) (y : ℝ) : ℝ :=
  κ * y + hFn c m φ f0 α n y

/-- The standing assumptions of §§II–III: the ordering cost satisfies §II, `0 ≤ α ≤ 1`,
the demand density `φ` is a one-sided Pólya density, and `m` is PF-integrable and bounded below. -/
structure IsModel (c m φ : ℝ → ℝ) (α c0 K0 cInf KInf : ℝ) : Prop where
  cost : IsOrderingCost c c0 K0 cInf KInf
  alpha_nonneg : 0 ≤ α
  alpha_le_one : α ≤ 1
  density : IsOneSidedPolyaDensity φ
  m_pfIntegrable : PFIntegrable m
  m_bddBelow : BddBelow (range m)

/-- A1: `(c₀ - α c_∞)· + m` is nonincreasing on `R⁻ = (-∞, 0)`. -/
def AssumptionA1 (m : ℝ → ℝ) (α c0 cInf : ℝ) : Prop :=
  AntitoneOn (fun x => (c0 - α * cInf) * x + m x) (Iio 0)

/-- A2: `(c₀ - α c_∞) x + m(x) → ∞` as `x → -∞`. -/
def AssumptionA2 (m : ℝ → ℝ) (α c0 cInf : ℝ) : Prop :=
  Tendsto (fun x => (c0 - α * cInf) * x + m x) atBot atTop

/-- A3: `(1 - α) κ· + m` is non-`(1 - α) K_κ`-decreasing on `[0, ∞)` for `κ ∈ C`. -/
def AssumptionA3 (c m : ℝ → ℝ) (α : ℝ) : Prop :=
  ∀ κ ∈ slopeSet c,
    NonKDecreasingOn (fun x => (1 - α) * κ * x + m x) ((1 - α) * Kc c κ) (Ici 0)

/-- A4: `(1 - α) c_∞ x + m(x) → ∞` as `x → ∞`. -/
def AssumptionA4 (m : ℝ → ℝ) (α cInf : ℝ) : Prop :=
  Tendsto (fun x => (1 - α) * cInf * x + m x) atTop atTop

/-- A5: `f0` is piecewise continuous and PF-integrable, `c_∞· + f0` is nonincreasing on `R⁻`, and
`κ· + f0` is non-`K_κ`-decreasing on `ℝ` for `κ ∈ C`. -/
def AssumptionA5 (c f0 : ℝ → ℝ) (cInf : ℝ) : Prop :=
  PiecewiseContinuousOn f0 univ ∧ PFIntegrable f0 ∧
    AntitoneOn (fun x => cInf * x + f0 x) (Iio 0) ∧
    ∀ κ ∈ slopeSet c, NonKDecreasingOn (fun x => κ * x + f0 x) (Kc c κ) univ

end PorteusSS


