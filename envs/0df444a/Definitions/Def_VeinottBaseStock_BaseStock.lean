-- Prove2me | Definitions.Def_VeinottBaseStock_BaseStock
-- name    : VeinottBaseStock_BaseStock
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T19:38:22.406065+00:00
-- url     : https://prove2.me/theorems/6072f339-8c03-49c1-a06b-168bc93b76d5
-- title:
--   Hypotheses (3a)–(3d), the minimal feasible order $w_i(x)$ and the base stock ordering policy (§3)
-- statement:
--   This file states the hypotheses of §3 of Veinott (1965) and constructs the base stock ordering policy of Theorem 3.2. Fix vectors $\bar y_1, \bar y_2, \dots \in \mathbb{R}^n$.
--
--   1. **(3a)** For each $i$, $\bar y_i \in Y_i$ minimizes $G_i(y)$ over $Y_i$.
--   2. **(3b)** $q_{i+1}(s_i(\bar y_i, t)) \le \bar y_{i+1}$ for all $t \in \mathfrak{D}_i$ and all $i$.
--   3. **(3c)** For each $i$, $Y_i$ is closed and linearly ordered by $\le$ (any two elements are comparable).
--   4. **(3d)** For each $i$, $G_i(y)$ and $s_i(y, t)$ ($t \in \mathfrak{D}_i$) are nondecreasing in $y$ on $\{y \in Y_i : y \ge \bar y_i\}$, and $q_i$ is nondecreasing in the one-sided sense: if $x \le x'$ in $X_i$ and $q_i(x) \not\le \bar y_i$, then $q_i(x) \le q_i(x')$.
--   5. **Order feasibility**: for every $x \in X_i$ there is $y \in Y_i$ with $y \ge q_i(x)$.
--
--   For $x \in X_i$ let $w_i(x)$ be the minimal element (the element below all others) of
--   $$Y_i \cap \{ y : y \ge q_i(x),\ y \ge \bar y_i \}.$$
--   The **base stock ordering rule** orders up to
--   $$\bar Y_i^*(x) = \begin{cases} \bar y_i, & q_i(x) \le \bar y_i, \\ w_i(x), & q_i(x) \not\le \bar y_i, \end{cases}$$
--   and the **base stock policy** applies this rule in every period to the current inventory vector $x_i^*$, starting from $x_1^* = x_1$ and updating $x_{i+1}^* = s_i(\bar Y_i^*(x_i^*), D_i)$. In words: if it is possible to order so as to attain $\bar y_i$, do so; otherwise order the minimal feasible amount.
--
--   These are the objects about which the main theorem of the paper is stated.
--
--   **Formalization Note.** Periods are 0-based (Lean $k$ = paper period $k+1$), and `ybar` stands for $\bar y$. "$\not\le$" is `¬ (· ≤ ·)` in `Fin n → EReal`, which is not the same as $>$. Three points differ from the page and are deliberate. (i) The paper states (3d)'s $q$-clause as "$q_i(x)$ is non-decreasing in $x$ for $x \in X_i$ for which $q_i(x) \not\le \bar y_i$"; read as monotonicity on that region only, Theorem 3.2 fails (see the moderation notes for a one-product counterexample), and the proof of Theorem 3.2 (p. 214) uses exactly the one-sided form stated here. (ii) Order feasibility (`OrderFeasible`) is used by the paper without being stated: p. 212 asserts that the set above "has a minimal element" for every $x \in X_i$, which requires it to be nonempty. (iii) When that set has no minimal element, `w` returns $\bar y_i$ by convention; under the hypotheses this case does not arise for $x \in X_i$. The policy is a function of the past demands: its state recursion is `baseStockState`, and `extendHist` pads a finite demand history into a path (only the first $k$ demands are read in period $k$).
-- source:
--   Veinott, Optimal Policy for a Multi-Product, Dynamic, Nonstationary Inventory Problem, Management Science 12(3):206–222 (1965), p. 210 ((3a), (3b)), p. 212 ((3c), (3d), linearly ordered sets, minimal element, w_i(x)), p. 213 (Theorem 3.2, base stock ordering policy)

import Mathlib
import Definitions.Def_VeinottBaseStock_Model

open MeasureTheory

namespace VeinottBaseStock

variable {n m : ℕ}

/-- Hypothesis (3a) (p. 210): for each period, `ȳ_i` minimizes `G_i(y)` over the set `Y_i`. -/
def Model.H3a (M : Model n m) (ybar : ℕ → Fin n → ℝ) : Prop :=
  ∀ k, ybar k ∈ M.Y k ∧ ∀ y ∈ M.Y k, M.G k (ybar k) ≤ M.G k y

/-- Hypothesis (3b) (p. 210): `q_{i+1}(s_i(ȳ_i, t)) ≤ ȳ_{i+1}` for all `t ∈ 𝔇_i`. -/
def Model.H3b (M : Model n m) (ybar : ℕ → Fin n → ℝ) : Prop :=
  ∀ k, ∀ t ∈ M.Dset k, M.q (k + 1) (M.s k (ybar k) t) ≤ coeVec (ybar (k + 1))

/-- Hypothesis (3c) (p. 212): each `Y_i` is closed and linearly ordered by `≤`. -/
def Model.H3c (M : Model n m) : Prop :=
  ∀ k, IsClosed (M.Y k) ∧ IsChain (· ≤ ·) (M.Y k)

/-- Hypothesis (3d) (p. 212), with its `q`-clause in the one-sided form used by the proof of
Theorem 3.2: `G_i` and `s_i(·, t)` (`t ∈ 𝔇_i`) are nondecreasing on `{y ∈ Y_i | y ≥ ȳ_i}`, and
for `x ≤ x'` in `X_i` with `q_i(x) ≰ ȳ_i` one has `q_i(x) ≤ q_i(x')`. -/
def Model.H3d (M : Model n m) (ybar : ℕ → Fin n → ℝ) : Prop :=
  (∀ k, MonotoneOn (M.G k) {y | y ∈ M.Y k ∧ ybar k ≤ y}) ∧
  (∀ k, ∀ t ∈ M.Dset k, MonotoneOn (fun y => M.s k y t) {y | y ∈ M.Y k ∧ ybar k ≤ y}) ∧
  (∀ k, ∀ x ∈ M.X k, ∀ x' ∈ M.X k, x ≤ x' → ¬ M.q k x ≤ coeVec (ybar k) → M.q k x ≤ M.q k x')

/-- Every admissible initial inventory vector admits an admissible order:
for `x ∈ X_i` there is `y ∈ Y_i` with `y ≥ q_i(x)`. The paper uses this without stating it (p. 212,
nonemptiness of the set whose minimal element is `w_i(x)`). -/
def Model.OrderFeasible (M : Model n m) : Prop :=
  ∀ k, ∀ x ∈ M.X k, ∃ y ∈ M.Y k, M.q k x ≤ coeVec y

/-- The set `Y_i ∩ {y | y ≥ q_i(x), y ≥ ȳ_i}` (p. 212). -/
def Model.orderSet (M : Model n m) (ybar : ℕ → Fin n → ℝ) (k : ℕ) (x : Fin n → ℝ) :
    Set (Fin n → ℝ) :=
  M.Y k ∩ {y | M.q k x ≤ coeVec y ∧ ybar k ≤ y}

open Classical in
/-- `w_i(x)`: the minimal (least) element of `Y_i ∩ {y | y ≥ q_i(x), y ≥ ȳ_i}` (p. 212); when that
set has no least element the value is `ȳ_i` (a convention; it keeps `w_i` inside `Y_i` under (3a)). -/
noncomputable def Model.w (M : Model n m) (ybar : ℕ → Fin n → ℝ) (k : ℕ) (x : Fin n → ℝ) :
    Fin n → ℝ :=
  if h : ∃ a, IsLeast (M.orderSet ybar k x) a then h.choose else ybar k

open Classical in
/-- The base stock ordering rule of Theorem 3.2 (p. 213): order up to `ȳ_i` if `q_i(x) ≤ ȳ_i`,
otherwise up to `w_i(x)`. -/
noncomputable def Model.baseStockRule (M : Model n m) (ybar : ℕ → Fin n → ℝ) (k : ℕ)
    (x : Fin n → ℝ) : Fin n → ℝ :=
  if M.q k x ≤ coeVec (ybar k) then ybar k else M.w ybar k x

/-- The initial inventory vector `x*_{k+1}` when the base stock rule is followed from `x₁` along the
demand path `d`. -/
noncomputable def Model.baseStockState (M : Model n m) (ybar : ℕ → Fin n → ℝ) (x₁ : Fin n → ℝ)
    (d : ℕ → Fin m → ℝ) : ℕ → Fin n → ℝ
  | 0 => x₁
  | k + 1 => M.s k (M.baseStockRule ybar k (M.baseStockState ybar x₁ d k)) (d k)

/-- Extends a finite demand history `(d_1, …, d_k)` to a demand path (by `0` afterwards; the
base stock state in period `k` only reads the first `k` demands). -/
def extendHist {k : ℕ} (z : Fin k → Fin m → ℝ) : ℕ → Fin m → ℝ :=
  fun j => if h : j < k then z ⟨j, h⟩ else 0

/-- The base stock ordering policy `Ȳ*` of Theorem 3.2 (p. 213), as a policy on demand
histories: in period `k` it applies the base stock rule to the current inventory vector `x*_{k+1}`
obtained by following the rule from `x₁`. -/
noncomputable def Model.baseStock (M : Model n m) (ybar : ℕ → Fin n → ℝ) (x₁ : Fin n → ℝ) :
    Pol n m :=
  fun k z => M.baseStockRule ybar k (M.baseStockState ybar x₁ (extendHist z) k)

end VeinottBaseStock


