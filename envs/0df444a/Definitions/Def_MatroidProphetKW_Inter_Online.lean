-- Prove2me | Definitions.Def_MatroidProphetKW_Inter_Online
-- name    : MatroidProphetKW_Inter_Online
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T13:23:20.231479+00:00
-- url     : https://prove2.me/theorems/da671cf4-7258-439a-9fa3-53b06c0c9b3e
-- title:
--   §2, §4.1–4.2 — threshold algorithms, online weight-adaptive adversaries, $\alpha$-balanced thresholds (Definition 3), and the summed-threshold algorithm
-- statement:
--   This definition fixes the online model of §2 for the feasibility constraint $\mathcal I = \bigcap_{j=1}^p \mathcal I_j$.
--
--   1. **Input sequence.** An input sequence $\sigma = (x_1, w(x_1)), \dots, (x_n, w(x_n))$ lists every element of $\mathcal U$ exactly once with its weight.
--   2. **Threshold algorithm.** A deterministic monotone online algorithm is given by thresholds: at step $i$, with $A_{i-1}$ the set selected so far, it offers $x_i$ a threshold $T_i(\sigma) \in \mathbb R$ that depends only on $x_1,\dots,x_{i-1}$, their weights, $A_{i-1}$ and $x_i$, and selects $x_i$ if and only if $A_{i-1} \cup \{x_i\} \in \mathcal I$ and $w(x_i) \ge T_i(\sigma)$. (The paper's threshold $T_i = \infty$ on infeasible steps is this feasibility test.) The selected set is $A = A(\sigma) = A_n$.
--   3. **$\alpha$-balanced thresholds (Definition 3).** The algorithm has $\alpha$-balanced thresholds if for every input sequence $\sigma$ with non-negative weights, with $A = A(\sigma)$, and every $V$ disjoint from $A$ with $A \cup V \in \mathcal I$,
--   $$\sum_{x_i \in A} T_i(\sigma) \ge \frac1\alpha\, \mathbb E\Big[\sum_j w'(C_j(A))\Big] \quad (13), \qquad \sum_{x_i \in V} T_i(\sigma) \le \frac1\alpha\, \mathbb E\Big[\sum_j w'(R_j(A))\Big] \quad (14),$$
--   the expectations being over the ghost sample $w'$.
--   4. **The algorithm of §4.2.** Its threshold is $T_i = T(A_{i-1}, i) = \sum_j T(A_{i-1}, i, j)$ (and $\infty$ when $A_{i-1} \cup \{x_i\} \notin \mathcal I$).
--   5. **Online weight-adaptive adversary.** After revealing $x_1,\dots,x_{i-1}$ and learning their weights, the adversary chooses the next element $x_i$, which has not been revealed yet, without knowing $w(x_i)$ or any other unrevealed weight. The selected set against the adversary, as a function of the weights $w$, is $A(w)$.
--
--   These notions are used in Proposition 3 and in the main theorem of the mission.
--
--   **Formalization Note** A threshold rule is a function `thr A xs w x` of the current selected set, the list of revealed elements, the weights and the current element; it may read `w` only on the revealed elements and must be measurable in `w`. An adversary is a function `next xs w` with the same two restrictions, which never repeats an element while unrevealed ones remain; the reveal order is obtained by iterating it $|\mathcal U|$ times. The only infinite threshold is the one on infeasible steps (the feasibility test); a monotone algorithm that offers $T_i = \infty$ on a step where $A_{i-1} \cup \{x_i\} \in \mathcal I$ is outside this class, so Proposition 3 is posed for algorithms whose thresholds are finite on feasible steps, which includes the §4.2 algorithm. Measurability is the standard convention that makes $\mathbb E[w(A)]$ meaningful. Randomized adversaries are mixtures of deterministic ones, so it suffices to consider deterministic adversaries. Sums $\sum_{x_i \in S}$ are over positions of the input order whose element lies in $S$.
-- source:
--   Kleinberg & Weinberg, Matroid Prophet Inequalities, arXiv:1201.4764v1, pp. 3–4 (§2, input sequences, threshold algorithms, online weight-adaptive adversaries), p. 9 (Definition 3, (13)–(14)), p. 10 (§4.2, T_i = T(A_{i−1}, i))

import Mathlib
import Definitions.Def_MatroidProphetKW_Inter_Setting

open MeasureTheory

namespace MatroidProphetKW.Inter

/-!
Kleinberg & Weinberg, *Matroid Prophet Inequalities*, arXiv:1201.4764v1,
§2 (pp. 3–4: threshold algorithms, online weight-adaptive adversaries),
§4.1 (p. 9: Definition 3) and §4.2 (p. 10: the summed thresholds `T(A, i)`).
-/

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A deterministic monotone online selection algorithm, given by its thresholds (§2, p. 4).
`thr A xs w x` is the threshold `T_i` offered to the element `x = x_i` when the elements
`xs = [x_1, …, x_{i-1}]` have been revealed (with their weights read from `w`) and the set
`A = A_{i-1}` has been selected. The threshold may depend on the revealed weights only
(`online`) and is measurable in them (`meas`). The threshold `∞` on infeasible steps is
modelled by the feasibility test in `sel`. -/
structure ThresholdRule (α : Type*) where
  thr : Finset α → List α → (α → ℝ) → α → ℝ
  online : ∀ (A : Finset α) (xs : List α) (w w' : α → ℝ) (x : α),
    (∀ y ∈ xs, w y = w' y) → thr A xs w x = thr A xs w' x
  meas : ∀ (A : Finset α) (xs : List α) (x : α), Measurable fun w : α → ℝ => thr A xs w x

open Classical in
/-- `sel rule M xs w i = A_i`: the set selected among the first `i` elements of the input
sequence `σ = (x_1, w(x_1)), …, (x_n, w(x_n))`, where `xs = [x_1, …, x_n]`. Step `i + 1`
selects `x_{i+1}` iff `A_i ∪ {x_{i+1}} ∈ ℐ` and `w(x_{i+1}) ≥ T_{i+1}` (§2, p. 4). -/
noncomputable def sel {p : ℕ} (rule : ThresholdRule α) (M : Fin p → Matroid α)
    (xs : List α) (w : α → ℝ) : ℕ → Finset α
  | 0 => ∅
  | i + 1 =>
    if h : i < xs.length then
      if IsIndep M (insert xs[i] (sel rule M xs w i)) ∧
          rule.thr (sel rule M xs w i) (xs.take i) w xs[i] ≤ w xs[i]
      then insert xs[i] (sel rule M xs w i) else sel rule M xs w i
    else sel rule M xs w i

/-- `A(σ)`, the set selected on the whole input sequence. -/
noncomputable def selected {p : ℕ} (rule : ThresholdRule α) (M : Fin p → Matroid α)
    (xs : List α) (w : α → ℝ) : Finset α :=
  sel rule M xs w xs.length

/-- `T_i(σ)` for the element in position `i` (0-based) of `xs`: the rule's threshold given the
prefix `xs.take i` and the set `A_{i-1} = sel rule M xs w i` selected so far. -/
noncomputable def thrAt {p : ℕ} (rule : ThresholdRule α) (M : Fin p → Matroid α)
    (xs : List α) (w : α → ℝ) (i : Fin xs.length) : ℝ :=
  rule.thr (sel rule M xs w i) (xs.take i) w xs[i]

open Classical in
/-- `∑_{x_i ∈ S} g_i`, a sum over the positions `i` of `xs` whose element lies in `S`. -/
noncomputable def sumOn (xs : List α) (S : Finset α) (g : Fin xs.length → ℝ) : ℝ :=
  ∑ i : Fin xs.length, if xs[i] ∈ S then g i else 0

/-- Property (13) of Definition 3 (p. 9): for every input sequence `σ` (every ordering `xs`
of `α` and every non-negative weight vector `w`), with `A = A(σ)`,
`∑_{x_i ∈ A} T_i(σ) ≥ (1/α) E[∑_j w′(C_j(A))]`. -/
def Balanced13 {p : ℕ} (M : Fin p → Matroid α) (F : α → Measure ℝ)
    [∀ x, IsProbabilityMeasure (F x)] (a : ℝ) (rule : ThresholdRule α) : Prop :=
  ∀ xs : List α, xs.Nodup → (∀ x, x ∈ xs) → ∀ w : α → ℝ, (∀ x, 0 ≤ w x) →
    (1 / a) * ∫ w', ∑ j, MatroidProphetKW.Single.wt w' (Cj M j (selected rule M xs w) w') ∂(law F) ≤
      sumOn xs (selected rule M xs w) (thrAt rule M xs w)

/-- Property (14) of Definition 3 (p. 9): for every input sequence `σ`, with `A = A(σ)`, and
every `V` disjoint from `A` with `A ∪ V ∈ ℐ`,
`∑_{x_i ∈ V} T_i(σ) ≤ (1/α) E[∑_j w′(R_j(A))]`. -/
def Balanced14 {p : ℕ} (M : Fin p → Matroid α) (F : α → Measure ℝ)
    [∀ x, IsProbabilityMeasure (F x)] (a : ℝ) (rule : ThresholdRule α) : Prop :=
  ∀ xs : List α, xs.Nodup → (∀ x, x ∈ xs) → ∀ w : α → ℝ, (∀ x, 0 ≤ w x) →
    ∀ V : Finset α, Disjoint (selected rule M xs w) V →
      IsIndep M (selected rule M xs w ∪ V) →
      sumOn xs V (thrAt rule M xs w) ≤
        (1 / a) * ∫ w', ∑ j, MatroidProphetKW.Single.wt w' (Rj M j (selected rule M xs w) w') ∂(law F)

/-- Definition 3 (p. 9): the rule has `α`-balanced thresholds, i.e. (13) and (14). -/
def IsBalanced {p : ℕ} (M : Fin p → Matroid α) (F : α → Measure ℝ)
    [∀ x, IsProbabilityMeasure (F x)] (a : ℝ) (rule : ThresholdRule α) : Prop :=
  Balanced13 M F a rule ∧ Balanced14 M F a rule

/-- The algorithm of §4.2 (p. 10): `T_i = T(A_{i-1}, i) = ∑_j T(A_{i-1}, i, j)` when
`A_{i-1} ∪ {x_i} ∈ ℐ` (and `∞` otherwise, via the feasibility test of `sel`), with
parameter `a = α`. The threshold depends only on `A_{i-1}` and `x_i`. -/
noncomputable def sumRule {p : ℕ} (M : Fin p → Matroid α) (F : α → Measure ℝ)
    [∀ x, IsProbabilityMeasure (F x)] (a : ℝ) : ThresholdRule α where
  thr A _ _ x := Tsum M F a A x
  online _ _ _ _ _ _ := rfl
  meas _ _ _ := measurable_const

/-- A deterministic online weight-adaptive adversary (§2, p. 4). Having revealed
`xs = [x_1, …, x_{i-1}]` and learned their weights, it chooses the next element
`next xs w`; it may not look at any other weight (`online`), it never repeats an element
while unrevealed ones remain (`fresh`), and its choice is a measurable function of the
weights (`meas`). -/
structure Adversary (α : Type*) where
  next : List α → (α → ℝ) → α
  online : ∀ (xs : List α) (w w' : α → ℝ), (∀ y ∈ xs, w y = w' y) → next xs w = next xs w'
  fresh : ∀ (xs : List α) (w : α → ℝ), (∃ y, y ∉ xs) → next xs w ∉ xs
  meas : ∀ (xs : List α) (x : α), MeasurableSet {w : α → ℝ | next xs w = x}

/-- The order `[x_1, …, x_n]` (`n = |𝒰|`) in which the adversary reveals the elements when
the weights are `w`. -/
def revealOrder (adv : Adversary α) (w : α → ℝ) : List α :=
  (fun xs => xs ++ [adv.next xs w])^[Fintype.card α] []

/-- `A`, the set the rule selects against the adversary when the weights are `w`. -/
noncomputable def adaptiveSelected {p : ℕ} (rule : ThresholdRule α) (M : Fin p → Matroid α)
    (adv : Adversary α) (w : α → ℝ) : Finset α :=
  selected rule M (revealOrder adv w) w

end MatroidProphetKW.Inter


