-- Prove2me | Definitions.Def_FuzzyGames_Walras_Basic
-- name    : FuzzyGames_Walras_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:05:42.843575+00:00
-- url     : https://prove2.me/theorems/4c2d158d-92c8-447d-aa93-4c30786e725b
-- title:
--   Exchange economy with fuzzy coalitions: allocations X(τ), fuzzy core, income functions, budget sets, Walras equilibria
-- statement:
--   This file fixes the exchange economy of §4 of Aubin's *Cooperative Fuzzy Games* and the two solution concepts compared in Theorem 4.1.
--
--   **Economy.** There are $n$ consumers $i \in N = \{1,\dots,n\}$ and $l$ commodities. Every consumer has the consumption set $\mathbb{R}^l_+$, a preference relation $\succcurlyeq_i$ (we write $x \succcurlyeq_i y$ for "consumer $i$ weakly prefers $x$ to $y$"), and a set $Y(i) \subset \mathbb{R}^l$ of initial endowments. The strict preference is $x \succ_i y$ iff $x \succcurlyeq_i y$ and not $y \succcurlyeq_i x$. The inner product is $p\cdot y = \sum_{k=1}^l p_k y_k$.
--
--   **Assumptions.** The economy satisfies the standing assumptions of §4 and assumption §4 (1):
--
--   1. each $Y(i)$ is closed, convex and comprehensive: $y \in Y(i)$ and $z \in \mathbb{R}^l_+$ imply $y - z \in Y(i)$;
--   2. each $\succcurlyeq_i$ is a complete preorder on $\mathbb{R}^l_+$ (reflexive, transitive, any two bundles comparable);
--   3. continuity: for every $x \in \mathbb{R}^l_+$ the sets $\{y \in \mathbb{R}^l_+ : y \succcurlyeq_i x\}$ and $\{y \in \mathbb{R}^l_+ : x \succcurlyeq_i y\}$ are closed;
--   4. convexity: the sets $\{y \in \mathbb{R}^l_+ : y \succcurlyeq_i x\}$ are convex, and $x \succ_i y$ implies $\alpha x + (1-\alpha) y \succ_i y$ for every $\alpha \in\, ]0,1[$;
--   5. no consumer is satiated: for every $x \in \mathbb{R}^l_+$ there is $y \in \mathbb{R}^l_+$ with $y \succ_i x$;
--   6. each consumer is positively endowed: $Y(i)$ contains a vector with all coordinates strictly positive.
--
--   **Allocations of a fuzzy coalition.** A fuzzy coalition is $\tau \in [0,1]^n$, with support $A_\tau = \{i : \tau_i > 0\}$. It disposes of the endowments
--   $$Y(\tau) = \sum_{i \in N} \tau_i\, Y(i)$$
--   (a Minkowski sum of scaled sets), and its allocations are
--   $$X(\tau) = \Big\{ x_\tau = (x_\tau^i)_{i \in A_\tau},\ x_\tau^i \in \mathbb{R}^l_+ \ :\ \sum_{i=1}^n \tau_i x_\tau^i \in Y(\tau) \Big\}.$$
--   The allocations of the economy are $X(N) = X(\tau^N)$ with $\tau^N = (1,\dots,1)$.
--
--   **Fuzzy core.** An allocation $x \in X(N)$ is in the fuzzy core if no nonzero fuzzy coalition $\tau \in [0,1]^n$ has an allocation $x_\tau \in X(\tau)$ with $x_\tau^i \succ_i x^i$ for every $i \in A_\tau$.
--
--   **Walras equilibria.** The income function of consumer $i$ is $r_i(p) = \sup_{y \in Y(i)} p \cdot y \in \mathbb{R} \cup \{+\infty\}$ and the budget set is $B_i(p) = \{x \in \mathbb{R}^l_+ : p\cdot x \le r_i(p)\}$. An allocation $\bar x \in X(N)$ is a Walras equilibrium if there is a price $\bar p \in \mathbb{R}^l$ with, for every consumer $i$,
--   $$\text{(i)}\ \ \bar p \cdot \bar x^i = r_i(\bar p), \qquad \text{(ii)}\ \ \bar x^i \succcurlyeq_i x \ \text{ for every } x \in B_i(\bar p).$$
--
--   **Auxiliary sets.** For an allocation $\bar x$, the proof of Theorem 4.1 uses $Q(i) = Y(i) - \{x \in \mathbb{R}^l_+ : x \succ_i \bar x^i\}$ (a Minkowski difference).
--
--   These objects are the vocabulary of the mission: Theorem 4.1 states that the fuzzy core and the set of Walras equilibria are equal.
--
--   **Formalization Note.** Consumers are `Fin n` and commodities `Fin l`; an allocation is a function `Fin n → Fin l → ℝ`, and a fuzzy coalition a function `Fin n → ℝ` in the cube `Set.Icc 0 1`. Bundles $x_\tau^i$ with $\tau_i = 0$ are kept as dummy coordinates: they are multiplied by $0$ in $\sum_i \tau_i x_\tau^i$, are unconstrained, and are never compared. $Y(\tau)$ uses Mathlib's pointwise scalar multiplication and sum of sets, so $0 \cdot Y(i) = \{0\}$ for nonempty $Y(i)$. The paper writes "preference preordering"; following Debreu's usage we read it as a *complete* preorder, and "continuous" as closed upper and lower contour sets in $\mathbb{R}^l_+$. The paper prints (1)(i) as "$x \succcurlyeq y \Rightarrow \alpha x + (1-\alpha) y \succ y$", which fails at $x = y$ and would make every economy violate the assumptions; we state it with $x \succ y$ in the premise. The paper's fuzzy-core definition prints "$x_\tau^i \succcurlyeq x^i$"; the proof of Theorem 4.1 uses the strict $x_\tau^i \succ \bar x^i$, and the weak version would let $x_\tau = x$ block every allocation, so we use the strict relation. The paper says "for any fuzzy coalition $\tau$"; we require $\tau \neq 0$, since at $\tau = 0$ the condition over $A_\tau = \emptyset$ is vacuous and would empty the core. In (2) the product is printed over $\mathbb{R}^\tau_+$; we read $\mathbb{R}^l_+$, the consumption set. The income $r_i(p)$ is valued in `EReal` (it can be $+\infty$), and the budget inequality and (i) are compared in `EReal`. The preference relation is a predicate on all of $\mathbb{R}^l$, but every assumption and every use is restricted to $\mathbb{R}^l_+$.
-- source:
--   Aubin, Cooperative Fuzzy Games, Math. Oper. Res. 6(1) (1981), §1, p. 2; §4, (1)–(4), pp. 5–6; proof of Theorem 4.1, p. 6

import Mathlib
import Definitions.Def_FuzzyGames_NTUCore_Basic

namespace FuzzyGames.Walras

open Set Pointwise

/-- The inner product `p · y = ∑ₖ pₖ yₖ` on `ℝ^l` (§4 (3)). -/
def dot {l : ℕ} (p y : Fin l → ℝ) : ℝ := ∑ k, p k * y k

/-- An exchange economy with `n` consumers and `l` commodities (§4, p. 5).
`pref i x y` reads `x ≽_i y` (consumer `i` weakly prefers `x` to `y`); `Y i` is the set
`Y(i) ⊂ ℝ^l` of initial endowments of consumer `i`. Every consumption set is `ℝ^l_+`. -/
structure Economy (n l : ℕ) where
  pref : Fin n → (Fin l → ℝ) → (Fin l → ℝ) → Prop
  Y : Fin n → Set (Fin l → ℝ)

variable {n l : ℕ}

/-- The strict preference `x ≻_i y`: `x ≽_i y` and not `y ≽_i x`. -/
def Economy.spref (E : Economy n l) (i : Fin n) (x y : Fin l → ℝ) : Prop :=
  E.pref i x y ∧ ¬ E.pref i y x

/-- The paper's standing assumptions of §4 together with assumption §4 (1).
* `Y(i)` is closed, convex and comprehensive (`Y(i) = Y(i) − ℝ^l_+`);
* `≽_i` is a preference preordering on `ℝ^l_+`: reflexive, transitive and complete;
* continuity: the upper and lower contour sets of `≽_i` in `ℝ^l_+` are closed;
* convexity: the upper contour sets of `≽_i` in `ℝ^l_+` are convex, and
  `x ≻_i y ⇒ αx + (1 − α)y ≻_i y` for `α ∈ ]0,1[` (the printed (1)(i) has `x ≽ y` in the
  premise, which is unsatisfiable at `x = y`; we read it with `x ≻ y`);
* (1)(ii) no consumer is satiated;
* (1)(iii) `Y(i)` meets the open positive orthant. -/
structure Economy.Assumptions (E : Economy n l) : Prop where
  closed_Y : ∀ i, IsClosed (E.Y i)
  convex_Y : ∀ i, Convex ℝ (E.Y i)
  comprehensive_Y : ∀ i, ∀ y ∈ E.Y i, ∀ z : Fin l → ℝ, 0 ≤ z → y - z ∈ E.Y i
  refl : ∀ i, ∀ x : Fin l → ℝ, 0 ≤ x → E.pref i x x
  trans : ∀ i, ∀ x y z : Fin l → ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ z →
    E.pref i x y → E.pref i y z → E.pref i x z
  total : ∀ i, ∀ x y : Fin l → ℝ, 0 ≤ x → 0 ≤ y → E.pref i x y ∨ E.pref i y x
  closed_upper : ∀ i, ∀ x : Fin l → ℝ, 0 ≤ x → IsClosed {y : Fin l → ℝ | 0 ≤ y ∧ E.pref i y x}
  closed_lower : ∀ i, ∀ x : Fin l → ℝ, 0 ≤ x → IsClosed {y : Fin l → ℝ | 0 ≤ y ∧ E.pref i x y}
  convex_upper : ∀ i, ∀ x : Fin l → ℝ, 0 ≤ x → Convex ℝ {y : Fin l → ℝ | 0 ≤ y ∧ E.pref i y x}
  strict_convex : ∀ i, ∀ x y : Fin l → ℝ, 0 ≤ x → 0 ≤ y → E.spref i x y →
    ∀ α : ℝ, 0 < α → α < 1 → E.spref i (α • x + (1 - α) • y) y
  nonsatiation : ∀ i, ∀ x : Fin l → ℝ, 0 ≤ x → ∃ y : Fin l → ℝ, 0 ≤ y ∧ E.spref i y x
  pos_endowed : ∀ i, ∃ y ∈ E.Y i, ∀ k, 0 < y k

/-- `Y(τ) = ∑ᵢ τᵢ Y(i)`, the endowments a fuzzy coalition `τ` puts at its disposal
(§4, p. 6); pointwise Minkowski sum of scaled sets. -/
def Economy.Ytau (E : Economy n l) (τ : Fin n → ℝ) : Set (Fin l → ℝ) :=
  ∑ i, τ i • E.Y i

/-- `X(τ)`, the allocations of the fuzzy coalition `τ` (§4 (2)): bundles `x_τ^i ∈ ℝ^l_+` for
the members `i ∈ A_τ = {i | τᵢ > 0}` with `∑ᵢ τᵢ x_τ^i ∈ Y(τ)`. The coordinates `x_τ^i` with
`τᵢ = 0` are dummies: they are multiplied by `0` and never compared. -/
def Economy.X (E : Economy n l) (τ : Fin n → ℝ) : Set (Fin n → Fin l → ℝ) :=
  {x | (∀ i, 0 < τ i → 0 ≤ x i) ∧ ∑ i, τ i • x i ∈ E.Ytau τ}

/-- The fuzzy core of the economy (§4, p. 6): allocations `x ∈ X(τ^N)` that no nonzero fuzzy
coalition `τ ∈ [0,1]^n` can improve upon, i.e. there is no `x_τ ∈ X(τ)` with
`x_τ^i ≻_i x^i` for every `i ∈ A_τ`. -/
def Economy.fuzzyCore (E : Economy n l) : Set (Fin n → Fin l → ℝ) :=
  {x | x ∈ E.X 1 ∧ ∀ τ ∈ FuzzyGames.NTUCore.cube n, τ ≠ 0 →
    ¬ ∃ xτ ∈ E.X τ, ∀ i, 0 < τ i → E.spref i (xτ i) (x i)}

/-- The income function `r_i(p) = sup_{y ∈ Y(i)} p · y` (§4 (3)), valued in `EReal`
(it is `+∞` when `p · y` is unbounded above on `Y(i)`). -/
noncomputable def Economy.income (E : Economy n l) (i : Fin n) (p : Fin l → ℝ) : EReal :=
  ⨆ y ∈ E.Y i, ((dot p y : ℝ) : EReal)

/-- The budget set `B_i(p) = {x ∈ ℝ^l_+ | p · x ≤ r_i(p)}` (§4, p. 6). -/
def Economy.budget (E : Economy n l) (i : Fin n) (p : Fin l → ℝ) : Set (Fin l → ℝ) :=
  {x | 0 ≤ x ∧ ((dot p x : ℝ) : EReal) ≤ E.income i p}

/-- The set of Walras equilibria (§4 (4)): allocations `x̄ ∈ X(τ^N)` for which some price
`p̄ ∈ ℝ^l` satisfies (i) `p̄ · x̄^i = r_i(p̄)` and (ii) `x̄^i ≽_i x` for every `x ∈ B_i(p̄)`,
for every consumer `i`. -/
def Economy.walras (E : Economy n l) : Set (Fin n → Fin l → ℝ) :=
  {x | x ∈ E.X 1 ∧ ∃ p : Fin l → ℝ,
    (∀ i, ((dot p (x i) : ℝ) : EReal) = E.income i p) ∧
    ∀ i, ∀ z ∈ E.budget i p, E.pref i (x i) z}

/-- The set `Q(i) = Y(i) − {x ∈ ℝ^l_+ | x ≻_i x̄^i}` of the proof of Theorem 4.1 (§4, p. 6). -/
def Economy.Q (E : Economy n l) (xbar : Fin n → Fin l → ℝ) (i : Fin n) :
    Set (Fin l → ℝ) :=
  E.Y i - {x | 0 ≤ x ∧ E.spref i x (xbar i)}

end FuzzyGames.Walras


