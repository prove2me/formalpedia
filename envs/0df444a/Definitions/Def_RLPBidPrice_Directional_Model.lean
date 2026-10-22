-- Prove2me | Definitions.Def_RLPBidPrice_Directional_Model
-- name    : RLPBidPrice_Directional_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T13:00:07.203195+00:00
-- url     : https://prove2.me/theorems/313f7183-10a2-432f-830d-64ff670cf5fc
-- title:
--   Network LP model: PI LP value v(x, Y), J^PI, Lagrangian L(x, μ), optimal dual prices, superdifferential ∂v(x, Y), and u(x, Y; d) of Eq. (22) (corrected: duals of y ≤ Y included)
-- statement:
--   A network has $m$ legs and $n$ itineraries. The **incidence matrix** $A = [a_{ij}] \in \mathbb{R}^{m \times n}$ has $a_{ij} = 1$ if itinerary $j$ uses leg $i$ and $a_{ij} = 0$ otherwise, and every column $A^j$ is nonzero (every itinerary uses at least one leg) — `IsIncidence A`. Fares are $r = (r^1, \dots, r^n)$, capacities $x \in \mathbb{R}^m$, and $y_0 = Y \in \mathbb{R}^n$ is a vector of demands to come.
--
--   - `piValue A r x y₀` is the **perfect-information LP value**
--   $$v(x, Y) = \max\{ r^\top y : Ay \le x,\ 0 \le y \le Y \},$$
--   written as the real supremum of the objective values of feasible $y$.
--   - `JPI P A r Y x` is the **perfect-information approximation** $J^{PI}(x) = \mathbb{E}\, v(x, Y) = \int v(x, Y(\omega))\, dP(\omega)$ for a random demand vector $Y$ on a probability space $(\Omega, P)$.
--   - `lagr A r x y₀ μ` is the **Lagrangian dual function** $L(x, \mu) = \sum_{j=1}^n Y^j (r^j - \mu^\top A^j)^+ + \mu^\top x$, where $(t)^+ = \max\{0, t\}$.
--   - `IsDualOpt A r x y₀ μ` says that $\mu \ge 0$ minimizes $L(x, \cdot)$ over $\mu \ge 0$: $\mu$ is an **optimal vector of dual prices** for the capacity constraints $Ay \le x$.
--   - `superdiff A r x y₀` is the **superdifferential** $\partial v(x, Y)$ of the concave function $z \mapsto v(z, Y)$ at $x$: the set of $\mu \in \mathbb{R}^m$ with $v(z, Y) \le v(x, Y) + \mu^\top (z - x)$ for every capacity vector $z \ge 0$. The paper calls its elements "subgradients"; since $v(\cdot, Y)$ is concave they are supergradients.
--   - `u A r x y₀ d` is, for a direction $d \in \mathbb{R}^m$,
--   $$u(x, Y; d) = \inf\{ d^\top \mu : \mu \text{ an optimal vector of dual prices, i.e. } \mu \ge 0 \text{ minimizes } L(x, \cdot) \}.$$
--   Equivalently, $u(x, Y; d)$ is the optimal value of the linear program $\min d^\top \mu$ subject to $\mu^\top x + \theta^\top Y = v(x, Y)$, $\mu^\top A^j + \theta^j \ge r^j$ for all $j$, $\mu \ge 0$, $\theta \ge 0$.
--
--   These are the objects of §1.2, §2 and §3 of the paper; every theorem of the mission is stated with them.
--
--   **Formalization Note.** Capacities are real vectors (the paper differentiates in $x$, p. 208, "if we imagine x is a real vector"). The paper's remaining-time index $k$ in $v_k$ and $J_k^{PI}$ is notation only (p. 208) and is dropped. $v$ is a real `sSup`: when $x \ge 0$ and $Y \ge 0$ the feasible set contains $y = 0$ and is bounded, so the supremum is the LP maximum; with a negative entry in $x$ or $Y$ the set is empty and the Lean value is $0$, which is why every theorem assumes $x \ge 0$ and $Y \ge 0$, and why the superdifferential quantifies over $z \ge 0$ only (the feasible capacities). Optimal dual prices are defined through the Lagrangian (13)–(14); by LP duality they are exactly the $\mu$-parts of the optimal solutions $(\mu, \theta)$ of the LP dual of (6)–(8), with $\theta^j = (r^j - \mu^\top A^j)^+$. $u$ is a real `sInf`, which is $0$ on an empty or unbounded-below set; for $x > 0$ (componentwise) and $Y \ge 0$ the set of optimal dual prices is nonempty and contained in the box $0 \le \mu \le \max_j r^j$, so $u$ is the attained minimum.
--
--   **Correction.** The printed Eq. (22) (p. 212) is $u(x, Y; d) = \min d^\top\mu$ subject to $\mu^\top x = v_k(x, Y)$, $\mu^\top A \le r$, $\mu \ge 0$: it omits the dual variables $\theta$ of the constraints $y \le Y$, and so describes the dual optimal set of the LP without the demand bounds. With one leg, one itinerary, $r = 1$, $x = 1$ and $Y$ uniform on $[0, 2]$, the directional derivative of $\mathbb{E}\, v$ at $x$ in the direction $d = 1$ is $P(Y > 1) = 1/2$, while the printed (22) gives $\mu = \min(Y, 1)$ and $\mathbb{E}\, u = 3/4$. The definition above uses the dual optimal set of (14) instead.
-- source:
--   Talluri, van Ryzin, A Randomized Linear Programming Method for Computing Network Bid Prices, Transp. Sci. 33(2), 1999, p. 207 (network data), p. 209, Eqs. (6)-(9), p. 210, Eqs. (13)-(14), p. 212, §3.1 and Eq. (22)

import Mathlib

namespace RLPBidPrice.Directional

open MeasureTheory Matrix

/-- The network data of Talluri–van Ryzin (1999), p. 207: `A` is the leg–itinerary incidence
matrix (`A i j = 1` if itinerary `j` uses leg `i`, `0` otherwise) and every itinerary uses at
least one leg (every column of `A` is nonzero). -/
def IsIncidence {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  (∀ i j, A i j = 0 ∨ A i j = 1) ∧ ∀ j, ∃ i, A i j ≠ 0

/-- The perfect-information LP value, Eqs. (6)–(8), p. 209:
`v(x, y₀) = max { r ⬝ᵥ y : A y ≤ x, 0 ≤ y ≤ y₀ }`, as a real `sSup`. The feasible set is
nonempty and bounded when `0 ≤ x` and `0 ≤ y₀`; otherwise it is empty and the value is `0`. -/
noncomputable def piValue {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin n → ℝ)
    (x : Fin m → ℝ) (y₀ : Fin n → ℝ) : ℝ :=
  sSup {v : ℝ | ∃ y : Fin n → ℝ, A *ᵥ y ≤ x ∧ 0 ≤ y ∧ y ≤ y₀ ∧ v = r ⬝ᵥ y}

/-- The perfect-information approximation `J^PI(x) = E v(x, Y)`, Eq. (9), p. 209. -/
noncomputable def JPI {m n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin n → ℝ) (Y : Ω → Fin n → ℝ)
    (x : Fin m → ℝ) : ℝ :=
  ∫ ω, piValue A r x (Y ω) ∂P

/-- The Lagrangian dual function, Eq. (13), second line, p. 210:
`L(x, μ) = ∑ⱼ y₀ʲ (rʲ − μᵀAʲ)⁺ + μᵀx`. -/
noncomputable def lagr {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin n → ℝ)
    (x : Fin m → ℝ) (y₀ : Fin n → ℝ) (μ : Fin m → ℝ) : ℝ :=
  ∑ j, y₀ j * max 0 (r j - ∑ i, μ i * A i j) + μ ⬝ᵥ x

/-- `μ` is an optimal vector of dual prices for the capacity constraints `A y ≤ x`:
a solution of `min_{μ ≥ 0} L(x, μ)`, Eq. (14), p. 210. -/
def IsDualOpt {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin n → ℝ)
    (x : Fin m → ℝ) (y₀ : Fin n → ℝ) (μ : Fin m → ℝ) : Prop :=
  0 ≤ μ ∧ ∀ μ' : Fin m → ℝ, 0 ≤ μ' → lagr A r x y₀ μ ≤ lagr A r x y₀ μ'

/-- The superdifferential `∂v(x, y₀)` of the concave map `z ↦ v(z, y₀)` at `x`, on its domain
`z ≥ 0` (p. 212, "the set of subgradients"): the vectors `μ` with
`v(z, y₀) ≤ v(x, y₀) + μᵀ(z − x)` for every capacity vector `z ≥ 0`. -/
def superdiff {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin n → ℝ)
    (x : Fin m → ℝ) (y₀ : Fin n → ℝ) : Set (Fin m → ℝ) :=
  {μ | ∀ z : Fin m → ℝ, 0 ≤ z → piValue A r z y₀ ≤ piValue A r x y₀ + μ ⬝ᵥ (z - x)}

/-- `u(x, y₀; d)`, Eq. (22), p. 212, corrected: the least value of `dᵀμ` over the optimal dual
price vectors `μ` of (14) (equivalently over the `μ`-parts of the optimal solutions of the full LP
dual of (6)–(8), which includes the duals of `y ≤ y₀`). -/
noncomputable def u {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin n → ℝ)
    (x : Fin m → ℝ) (y₀ : Fin n → ℝ) (d : Fin m → ℝ) : ℝ :=
  sInf ((fun μ : Fin m → ℝ => d ⬝ᵥ μ) '' {μ | IsDualOpt A r x y₀ μ})

end RLPBidPrice.Directional


