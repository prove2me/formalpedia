-- Prove2me | Definitions.Def_RLPBidPrice_Unbiased_Model
-- name    : RLPBidPrice_Unbiased_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T12:36:09.090217+00:00
-- url     : https://prove2.me/theorems/9c839f5a-a08a-470e-bb78-3376f2c12322
-- title:
--   Network LP model: incidence matrix, PI LP value v(x, Y), J^PI, Lagrangian L(x, μ), optimal dual prices, Conditions C1′ and C2
-- statement:
--   A network has $m$ legs and $n$ itineraries. The **incidence matrix** $A = [a_{ij}] \in \mathbb{R}^{m \times n}$ has $a_{ij} = 1$ if itinerary $j$ uses leg $i$ and $a_{ij} = 0$ otherwise, and every column $A^j$ is nonzero (every itinerary uses at least one leg) — `IsIncidence A`. Fares are $r = (r^1, \dots, r^n)$, capacities $x \in \mathbb{R}^m$, demands to come $y_0 = Y \in \mathbb{R}^n$.
--
--   - `piValue A r x y₀` is the **perfect-information LP value**
--   $$v(x, Y) = \max\{ r^\top y : Ay \le x,\ 0 \le y \le Y \},$$
--   written as the real supremum of the objective values of feasible $y$.
--   - `JPI P A r Y x` is the **perfect-information approximation** $J^{PI}(x) = \mathbb{E}\, v(x, Y) = \int v(x, Y(\omega))\, dP(\omega)$ for a random demand vector $Y$ on a probability space $(\Omega, P)$.
--   - `lagr A r x y₀ μ` is the **Lagrangian dual function** $L(x, \mu) = \sum_{j=1}^n Y^j (r^j - \mu^\top A^j)^+ + \mu^\top x$, where $(t)^+ = \max\{0, t\}$.
--   - `IsDualOpt A r x y₀ μ` says $\mu \ge 0$ minimizes $L(x, \cdot)$ over $\mu \ge 0$: $\mu$ is an optimal vector of dual prices for the capacity constraints $Ay \le x$.
--   - `colSet A S T` is the set of columns $\{A^j : j \in S\} \cup \{e^i : i \in T\}$ of the matrix $[A\ I]$, with $e^i$ the $i$-th unit vector.
--   - `ConditionOnePrime A x` (**Condition C1′**): for all $S \subseteq \{1,\dots,n\}$ and $T \subseteq \{1,\dots,m\}$, if $x$ lies in the linear span of `colSet A S T`, that set spans $\mathbb{R}^m$ (has rank $m$). Equivalently, $x$ lies in no subspace spanned by fewer than $m$ columns of $[A\ I]$.
--   - `ConditionTwo P Y` (**Condition 2**): for every $j$, the map $t \mapsto P(Y^j \le t)$ is continuous.
--   - `gradCLM g` is the linear functional $h \mapsto \sum_i g^i h^i$; a function has gradient $g$ at $x$ when its Fréchet derivative at $x$ is `gradCLM g`.
--
--   These are the objects of §1.2 and §2 of the paper; every theorem of the mission is stated with them.
--
--   **Formalization Note.** Capacities are real vectors (the paper differentiates in $x$, p. 208, "if we imagine x is a real vector"). The paper's remaining-time index $k$ in $v_k$ and $J_k^{PI}$ is notation only (p. 208) and is dropped. $v$ is a real `sSup`: when $x \ge 0$ and $Y \ge 0$ the feasible set contains $y = 0$ and is bounded (by $0 \le y \le Y$), so the supremum is the LP maximum; with a negative entry in $x$ or $Y$ the set is empty and the Lean value is $0$, which is why every theorem assumes $x \ge 0$ and $Y \ge 0$. Optimal dual prices are defined through the Lagrangian (13)–(14); by LP duality they coincide with the $\mu$-parts of the optimal solutions of the LP dual of (6)–(8). Condition C1′ replaces the printed Condition 1, which quantifies only over columns of $A$.
--
--   **Correction.** The printed Condition 1 (p. 210: "If $x = \sum_{j\in S}\alpha^j A^j$, then $\{A^j : j \in S\}$ must have rank $m$") ignores the slack columns of $Ay \le x$ and is too weak for Theorem 1: with $A$ having rows $(0,1,1), (1,1,0), (1,0,1)$, $r = (100,1,1)$, $x = (1,1,1)$ and $Y^j$ i.i.d. uniform on $[0,2]$, Condition 1 and Condition 2 hold but $\mathbb{E}\, v(\cdot, Y)$ is not differentiable at $x$; this $x = e^1 + A^1$ violates C1′.
-- source:
--   Talluri, van Ryzin, A Randomized Linear Programming Method for Computing Network Bid Prices, Transp. Sci. 33(2), 1999, p. 207 (network data), p. 209, Eqs. (6)-(9), p. 210, Eqs. (13)-(14) and Conditions 1-2

import Mathlib

open MeasureTheory Matrix

namespace RLPBidPrice.Unbiased

/-- The network data of Talluri–van Ryzin (1999), p. 207: `A` is the leg–itinerary incidence
matrix (`A i j = 1` if itinerary `j` uses leg `i`, `0` otherwise) and every itinerary uses at
least one leg (every column of `A` is nonzero). -/
def IsIncidence {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  (∀ i j, A i j = 0 ∨ A i j = 1) ∧ ∀ j, ∃ i, A i j ≠ 0

/-- The perfect-information LP value, Eqs. (6)–(8), p. 209:
`v(x, y₀) = max { r ⬝ᵥ y : A y ≤ x, 0 ≤ y ≤ y₀ }`, taken as a real `sSup`
(the feasible set is nonempty and bounded when `0 ≤ x` and `0 ≤ y₀`). -/
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

/-- `μ` is an optimal vector of dual prices for the capacity constraints (7):
a solution of `min_{μ ≥ 0} L(x, μ)`, Eq. (14), p. 210. -/
def IsDualOpt {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin n → ℝ)
    (x : Fin m → ℝ) (y₀ : Fin n → ℝ) (μ : Fin m → ℝ) : Prop :=
  0 ≤ μ ∧ ∀ μ' : Fin m → ℝ, 0 ≤ μ' → lagr A r x y₀ μ ≤ lagr A r x y₀ μ'

/-- The columns `{Aʲ : j ∈ S}` of `A` together with the unit vectors `{eⁱ : i ∈ T}`,
i.e. a set of columns of `[A I]`. -/
def colSet {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (S : Finset (Fin n))
    (T : Finset (Fin m)) : Set (Fin m → ℝ) :=
  ((fun j => fun i => A i j) '' (S : Set (Fin n))) ∪
    ((fun i => (Pi.single i 1 : Fin m → ℝ)) '' (T : Set (Fin m)))

/-- Condition C1′ (Condition 1 of p. 210 applied to the columns of `[A I]`): whenever `x` is a
linear combination of a set of columns of `[A I]`, that set has rank `m` (spans `ℝᵐ`). -/
def ConditionOnePrime {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin m → ℝ) : Prop :=
  ∀ (S : Finset (Fin n)) (T : Finset (Fin m)),
    x ∈ Submodule.span ℝ (colSet A S T) → Submodule.span ℝ (colSet A S T) = ⊤

/-- Condition 2, p. 210: `P(Yʲ ≤ y)` is continuous in `y`, for every itinerary `j`. -/
def ConditionTwo {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : Ω → Fin n → ℝ) : Prop :=
  ∀ j : Fin n, Continuous (fun t : ℝ => P.real {ω | Y ω j ≤ t})

/-- The continuous linear functional `h ↦ ∑ᵢ gⁱ hⁱ` whose gradient is the vector `g`. -/
noncomputable def gradCLM {m : ℕ} (g : Fin m → ℝ) : (Fin m → ℝ) →L[ℝ] ℝ :=
  ∑ i, g i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) i

end RLPBidPrice.Unbiased


