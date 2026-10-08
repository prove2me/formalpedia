-- Prove2me | Definitions.Def_MatroidProphetKW_Single_Online
-- name    : MatroidProphetKW_Single_Online
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T12:22:45.302415+00:00
-- url     : https://prove2.me/theorems/b24b5df4-e158-4219-aa83-86bbf5e1c3c2
-- title:
--   §2 — input orders, threshold rules, the online run $A(\sigma)$, and online weight-adaptive adversaries
-- statement:
--   An **input sequence** is a sequence $\sigma = (x_1, w_1), \dots, (x_n, w_n)$ in which every element of the ground set $\mathcal U$ occurs exactly once among $x_1, \dots, x_n$ and $w_i = w(x_i)$. The list $l = [x_1, \dots, x_n]$ is called an **input order**.
--
--   A **threshold rule** assigns to the arriving element $x_i$ a threshold $T_i = \mathrm{Thr}(A_{i-1}, (x_1,\dots,x_{i-1}), w, x_i) \ge 0$, where $A_{i-1}$ is the set selected so far; it is admissible if it is non-negative and depends on the weight vector $w$ only through the already revealed weights $w(x_1), \dots, w(x_{i-1})$, measurably. On an input sequence the rule produces sets $A_0 = \emptyset$ and
--   $$A_i = \begin{cases} A_{i-1} \cup \{x_i\} & \text{if } A_{i-1} \cup \{x_i\} \in \mathcal I \text{ and } w_i \ge T_i,\\ A_{i-1} & \text{otherwise,}\end{cases}$$
--   i.e. the effective threshold is $\infty$ exactly when $A_{i-1} \cup \{x_i\} \notin \mathcal I$. The selected set is $A(\sigma) = A_n$, and $T_i(\sigma)$ denotes the threshold faced by $x_i$.
--
--   An **online weight-adaptive adversary** chooses the next element to reveal one at a time: after choosing $x_1, \dots, x_{i-1}$ and learning $w(x_1), \dots, w(x_{i-1})$, it chooses $x_i$ without knowing $w(x_i)$ or any other unrevealed weight. Formally it is a map $\mathrm{adv}$ from the revealed list and the weight vector to the next element that (1) never repeats an element while some element is unrevealed, (2) depends on $w$ only through the weights of the revealed elements, and (3) is measurable in $w$. Running it for $n = |\mathcal U|$ steps produces the input order $x_1, \dots, x_n$, which depends on $w$.
--
--   These definitions describe the online model against which Proposition 1 and the main theorem are stated.
--
--   **Formalization Note** "Monotone deterministic online selection algorithm" is taken in the threshold form that §2 shows equivalent: the algorithm is given by its thresholds, and the characterization itself is not formalized. The threshold is real valued and the value $\infty$ for infeasible steps is implemented by the independence guard in the acceptance test. The threshold may depend on the current selection $A_{i-1}$ as well as on the revealed prefix; since $A_{i-1}$ is itself a function of the prefix, this is no extra generality. A randomized adversary is a mixture of deterministic ones, so quantifying over deterministic adversaries loses nothing; the measurability requirement is what makes $\mathbb E[w(A)]$ a genuine expectation.
-- source:
--   Kleinberg & Weinberg, Matroid Prophet Inequalities, arXiv:1201.4764v1, pp. 3–4 (§2, input sequences, deterministic online selection algorithms, thresholds T_i(σ), online weight-adaptive adversary)

import Mathlib
import Definitions.Def_MatroidProphetKW_Single_Setting

namespace MatroidProphetKW.Single

open MeasureTheory

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- An input order: a list in which every element of the ground set occurs exactly once
(Kleinberg–Weinberg, arXiv:1201.4764v1, §2, p. 3, "every element of 𝒰 occurs exactly once"). -/
def IsOrder (l : List α) : Prop := l.Nodup ∧ ∀ x, x ∈ l

/-- A deterministic threshold rule (§2, pp. 3–4). `Thr A l w x` is the threshold offered to the
element `x` when the elements of the list `l` have already been revealed (in this order), `A` is the
set selected so far, and `w` is the weight vector. It is admissible if it is non-negative and it
depends on `w` only through the weights of the revealed elements, measurably. -/
def IsThresholdRule (Thr : Finset α → List α → (α → ℝ) → α → ℝ) : Prop :=
  (∀ A l w x, 0 ≤ Thr A l w x) ∧
  (∀ A l w w' x, (∀ y ∈ l, w y = w' y) → Thr A l w x = Thr A l w' x) ∧
  (∀ A l x, Measurable (fun w => Thr A l w x))

/-- One step of the online run: the element `x` is revealed after the list `st.1`, with `st.2`
selected so far. It is selected iff `A ∪ {x}` is independent and `w(x) ≥ Thr`; that is, the
threshold is `∞` exactly when `A ∪ {x} ∉ ℐ` (§2, p. 4). -/
noncomputable def step (M : Matroid α) (Thr : Finset α → List α → (α → ℝ) → α → ℝ)
    (w : α → ℝ) (st : List α × Finset α) (x : α) : List α × Finset α := by
  classical
  exact (st.1 ++ [x],
    if M.Indep (↑(insert x st.2) : Set α) ∧ Thr st.2 st.1 w x ≤ w x then insert x st.2 else st.2)

/-- The set `A(σ)` selected by the threshold rule on the input sequence
`σ = (x_1, w(x_1)), …, (x_n, w(x_n))` with `l = [x_1, …, x_n]`. On a prefix of the order it is the
partial selection `A_i`. -/
noncomputable def run (M : Matroid α) (Thr : Finset α → List α → (α → ℝ) → α → ℝ)
    (l : List α) (w : α → ℝ) : Finset α :=
  (l.foldl (step M Thr w) ([], ∅)).2

/-- The threshold `T_i(σ)` faced by `x = x_i` on the input order `l`: the rule evaluated at the
prefix `x_1, …, x_{i−1}` and the selection `A_{i−1}` made on it. -/
noncomputable def thrAt (M : Matroid α) (Thr : Finset α → List α → (α → ℝ) → α → ℝ)
    (l : List α) (w : α → ℝ) (x : α) : ℝ :=
  Thr (run M Thr (l.take (l.idxOf x)) w) (l.take (l.idxOf x)) w x

/-- A deterministic online weight-adaptive adversary (§2, p. 4): `adv l w` is the next element to
reveal after the elements of `l` were revealed in this order. It never repeats an element while some
element is unrevealed, and it depends on `w` only through the weights of the revealed elements
(it does not see `w(x_i)` before choosing `x_i`), measurably. -/
def IsAdversary (adv : List α → (α → ℝ) → α) : Prop :=
  (∀ l w, (∃ y, y ∉ l) → adv l w ∉ l) ∧
  (∀ l w w', (∀ y ∈ l, w y = w' y) → adv l w = adv l w') ∧
  (∀ l y, MeasurableSet {w : α → ℝ | adv l w = y})

/-- The first `k` elements revealed by the adversary `adv` when the weights are `w`. -/
def advPrefix (adv : List α → (α → ℝ) → α) (w : α → ℝ) : ℕ → List α
  | 0 => []
  | k + 1 => advPrefix adv w k ++ [adv (advPrefix adv w k) w]

/-- The whole order `x_1, …, x_n` (`n = |𝒰|`) in which the adversary reveals the elements. -/
def advOrder (adv : List α → (α → ℝ) → α) (w : α → ℝ) : List α :=
  advPrefix adv w (Fintype.card α)

end MatroidProphetKW.Single


