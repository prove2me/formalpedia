-- Prove2me | Definitions.Def_PrivSeqLearn_QueryComplexity_Setting
-- name    : PrivSeqLearn_QueryComplexity_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T20:13:39.806896+00:00
-- url     : https://prove2.me/theorems/206b1a22-b587-454c-a9c0-a8d771bf3625
-- title:
--   §2–§4, pp. 6–11 — learner strategies Φ_N, Q(x), the information set I(q), δ-cover number C_δ, (ϵ,δ,L)-private strategies, N*(ϵ,δ,L)
-- statement:
--   The model of private sequential learning of Tsitsiklis, Xu and Xu.
--
--   A learner wants to locate an unknown **true value** $v^* \in [0,1)$. She submits queries $q_1, \dots, q_N$ one at a time; the response to query $q_k$ is the bit $r_k = \mathbb I(v^* \ge q_k)$. She may randomize through a **random seed** $Y$, uniform on $\{1, \dots, \bar Y\}$ for some integer $\bar Y \ge 1$.
--
--   1. **Learner strategies** (§2.1, pp. 7–8). A learner strategy $\phi$ of length $N$ consists of query maps $\phi_k : \{0,1\}^{k-1} \times \{1,\dots,\bar Y\} \to [0,1)$, $k = 1, \dots, N$, with $q_k = \phi_k(r_1, \dots, r_{k-1}, Y)$, and an estimation map $\phi^E : \{0,1\}^N \times \{1,\dots,\bar Y\} \to [0,1)$ with $\hat x = \phi^E(r_1, \dots, r_N, Y)$. The set $\Phi_N$ consists of those strategies that, in addition, submit pairwise distinct queries. For a true value $x$ and a seed $y$, write $\bar q(x,y) = (q_1, \dots, q_N)$ for the realized queries and $\hat x(x,y)$ for the estimate.
--
--   2. **Information set** (eq. (1) and Definition 3.1, p. 9). The query sequences that have positive probability when $v^* = x$ form
--   $$\mathcal Q(x) = \{\bar q(x,y) : y \in \{1, \dots, \bar Y\}\},$$
--   and the adversary, who sees the queries but not the responses, has the information set
--   $$\mathcal I(\bar q) = \{x \in [0,1) : \bar q \in \mathcal Q(x)\}.$$
--
--   3. **Cover number** (Definition 3.2, p. 10). A set $E \subset \mathbb R$ is $(\delta, L)$-coverable if it is contained in a union of $L$ closed intervals $[a_j, b_j]$ with $b_j - a_j \le \delta$, and its $\delta$-cover number is
--   $$C_\delta(E) = \min\{L \in \mathbb N : E \text{ is } (\delta,L)\text{-coverable}\}.$$
--
--   4. **Private strategies** (Definition 3.3, p. 10). A strategy $\phi$ is $(\epsilon, \delta, L)$-private if it is accurate, $|\hat x(x,y) - x| \le \epsilon/2$ for every $x \in [0,1)$ and every seed $y$, and private: $C_\delta(\mathcal I(\bar q)) \ge L$ for every $x \in [0,1)$ and every $\bar q \in \mathcal Q(x)$.
--
--   5. **Query complexity** (eq. (5), p. 11).
--   $$N^*(\epsilon, \delta, L) = \min\{N \in \mathbb N : \Phi_N \text{ contains an } (\epsilon,\delta,L)\text{-private strategy}\}.$$
--
--   These objects are shared by every statement of the mission; the main theorem bounds $N^*$.
--
--   **Formalization Note** The seed space is `Fin Ybar` with `0 < Ybar` (an empty seed space would make every "for all seeds" condition vacuous). Since the seed is uniform on a finite set, "positive probability" is read as "for some seed" and "probability one" as "for every seed". Response histories are `List Bool` (`true` = 1), the response to $q$ at true value $x$ is `decide (q ≤ x)`, and queries are 0-indexed (`Fin N`). The query and estimation maps are total functions on all histories; the range $[0,1)$ is required on histories of length $< N$ (queries) and $= N$ (estimate), and distinctness for every $x \in [0,1)$ and seed. The cover uses exactly $L$ intervals indexed by `Fin L` (a degenerate interval may be repeated, which is equivalent to "at most $L$"); $C_\delta$ and $N^*$ are `sInf` over $\mathbb N$, which equals the minimum whenever the set is nonempty.
-- source:
--   Tsitsiklis, Xu, Xu, Private Sequential Learning, arXiv:1805.02136v3, pp. 6–11, §2.1 (pp. 7–8), eq. (1) and Definition 3.1 (p. 9), Definitions 3.2–3.3 (p. 10), eq. (5) (p. 11)

import Mathlib

namespace PrivSeqLearn.QueryComplexity

/-- A learner strategy of length `N` (Tsitsiklis, Xu, Xu, Private Sequential Learning,
arXiv:1805.02136v3, §2.1, pp. 7–8, the "simpler definition" adopted on p. 8).

The random seed `Y` is uniform on `{1, …, Ybar}`, encoded as `Fin Ybar` with `0 < Ybar`.
`query h y` is the paper's `φ_k(r_1, …, r_{k-1}, y)` on a response history `h` of length `k - 1`;
`est h y` is `φ^E(r_1, …, r_N, y)` on a history of length `N`. Values on histories of other lengths
are never used. The range condition `[0, 1)` and distinctness are imposed separately by `InPhi`.

**Formalization Note** `0 < Ybar` is mandatory: with an empty seed space every "for all seeds"
statement would hold vacuously. Responses are `true` for `1` and `false` for `0`. -/
structure Strategy (N : ℕ) where
  /-- The number `Ybar` of seed values. -/
  Ybar : ℕ
  /-- The seed space is nonempty. -/
  Ybar_pos : 0 < Ybar
  /-- The query maps `φ_k`, `k = 1, …, N`, on response histories of length `k - 1`. -/
  query : List Bool → Fin Ybar → ℝ
  /-- The estimation map `φ^E`, on response histories of length `N`. -/
  est : List Bool → Fin Ybar → ℝ

variable {N : ℕ}

/-- The response history after `k` queries, when the true value is `x` and the seed is `y`:
`hist 0 = []` and `hist (k+1) = hist k ++ [r_{k+1}]`, where `r_{k+1} = I(x ≥ q_{k+1})` (p. 6) and
`q_{k+1} = φ_{k+1}(hist k, y)`. -/
noncomputable def hist (φ : Strategy N) (x : ℝ) (y : Fin φ.Ybar) : ℕ → List Bool
  | 0 => []
  | k + 1 => hist φ x y k ++ [decide (φ.query (hist φ x y k) y ≤ x)]

/-- The realized query sequence `q(x, y) = (q_1, …, q_N)` (p. 8), 0-indexed: `queries φ x y k` is the
paper's `q_{k+1}`. -/
noncomputable def queries (φ : Strategy N) (x : ℝ) (y : Fin φ.Ybar) : Fin N → ℝ :=
  fun k => φ.query (hist φ x y k) y

/-- The learner's estimate `x̂(x, y) = φ^E(r_1, …, r_N, y)` (p. 8). -/
noncomputable def estimate (φ : Strategy N) (x : ℝ) (y : Fin φ.Ybar) : ℝ :=
  φ.est (hist φ x y N) y

/-- Every query map takes values in `[0, 1)`: `φ_k : {0,1}^{k-1} × {1, …, Ybar} → [0, 1)` (p. 8). -/
def QueriesInUnit (φ : Strategy N) : Prop :=
  ∀ h : List Bool, h.length < N → ∀ y : Fin φ.Ybar, φ.query h y ∈ Set.Ico (0 : ℝ) 1

/-- The estimation map takes values in `[0, 1)`: `φ^E : {0,1}^N × {1, …, Ybar} → [0, 1)` (p. 8). -/
def EstInUnit (φ : Strategy N) : Prop :=
  ∀ h : List Bool, h.length = N → ∀ y : Fin φ.Ybar, φ.est h y ∈ Set.Ico (0 : ℝ) 1

/-- The strategy submits distinct queries (p. 8): for every true value `x ∈ [0, 1)` and every seed
`y`, the queries `q_1, …, q_N` are pairwise distinct. -/
def SubmitsDistinct (φ : Strategy N) : Prop :=
  ∀ x ∈ Set.Ico (0 : ℝ) 1, ∀ y : Fin φ.Ybar, Function.Injective (queries φ x y)

/-- Membership in `Φ_N` (p. 8): values in `[0, 1)` and distinct queries. -/
def InPhi (φ : Strategy N) : Prop :=
  QueriesInUnit φ ∧ EstInUnit φ ∧ SubmitsDistinct φ

/-- `Q(x)`, eq. (1), p. 9: the query sequences with positive probability when `v* = x`. With a
uniform seed, positive probability means "realized by some seed". -/
def Qset (φ : Strategy N) (x : ℝ) : Set (Fin N → ℝ) :=
  Set.range (queries φ x)

/-- The information set `I(q) = {x ∈ [0, 1) : q ∈ Q(x)}` of the adversary, Definition 3.1, p. 9. -/
def infoSet (φ : Strategy N) (q : Fin N → ℝ) : Set ℝ :=
  {x | x ∈ Set.Ico (0 : ℝ) 1 ∧ q ∈ Qset φ x}

/-- `E` is `(δ, L)`-coverable (Definition 3.2, p. 10): there are `L` closed intervals
`[a_j, b_j]` with `b_j - a_j ≤ δ` whose union contains `E`. -/
def Coverable (δ : ℝ) (L : ℕ) (E : Set ℝ) : Prop :=
  ∃ a b : Fin L → ℝ, E ⊆ ⋃ j, Set.Icc (a j) (b j) ∧ ∀ j, b j - a j ≤ δ

/-- The `δ`-cover number `C_δ(E) = min {L ∈ ℕ : E is (δ, L)-coverable}`, eq. (3), p. 10.
It is `sInf` over `ℕ`; for a bounded `E` and `δ > 0` the set is nonempty, so this is the minimum. -/
noncomputable def coverNumber (δ : ℝ) (E : Set ℝ) : ℕ :=
  sInf {L : ℕ | Coverable δ L E}

/-- The accuracy constraint of Definition 3.3, p. 10: `P(|x̂(x, Y) - x| ≤ ϵ/2) = 1` for every
`x ∈ [0, 1)`; with a uniform seed, probability one means "for every seed". -/
def IsAccurate (ϵ : ℝ) (φ : Strategy N) : Prop :=
  ∀ x ∈ Set.Ico (0 : ℝ) 1, ∀ y : Fin φ.Ybar, |estimate φ x y - x| ≤ ϵ / 2

/-- `(ϵ, δ, L)`-private learner strategy, Definition 3.3, p. 10: accurate, and
`C_δ(I(q)) ≥ L` for every `x ∈ [0, 1)` and every `q ∈ Q(x)` (eq. (4)). -/
def IsPrivate (ϵ δ : ℝ) (L : ℕ) (φ : Strategy N) : Prop :=
  IsAccurate ϵ φ ∧
    ∀ x ∈ Set.Ico (0 : ℝ) 1, ∀ q ∈ Qset φ x, L ≤ coverNumber δ (infoSet φ q)

/-- The query complexity `N*(ϵ, δ, L) = min {N ∈ ℕ : Φ_N contains an (ϵ, δ, L)-private strategy}`,
eq. (5), p. 11. -/
noncomputable def Nstar (ϵ δ : ℝ) (L : ℕ) : ℕ :=
  sInf {N : ℕ | ∃ φ : Strategy N, InPhi φ ∧ IsPrivate ϵ δ L φ}

end PrivSeqLearn.QueryComplexity


