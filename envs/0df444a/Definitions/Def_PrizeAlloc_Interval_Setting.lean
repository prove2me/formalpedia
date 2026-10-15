-- Prove2me | Definitions.Def_PrizeAlloc_Interval_Setting
-- name    : PrizeAlloc_Interval_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T02:28:59.145464+00:00
-- url     : https://prove2.me/theorems/f7ae2a37-af52-440f-9b3f-61e82c9fd35a
-- title:
--   pp. 8–12 — competitions, subrankings, prize allocation rules, the axioms of §2, and interval rules
-- statement:
--   This file sets up the variable-population model of prize allocation in rank-order competitions of Dietzenbacher and Kondratev.
--
--   **Competitions.** Let $U$ be a set of potential competitors. A competition is a triple $(N, \mathcal R, E)$: a nonempty finite set $N \subseteq U$ of competitors, a ranking $\mathcal R : N \to \{1, \dots, |N|\}$ (a bijection; competitor $i$ is ranked higher than $j$ if $\mathcal R(i) < \mathcal R(j)$), and a prize endowment $E \ge 0$. For a nonempty $S \subseteq N$, the subranking $\mathcal R_S : S \to \{1, \dots, |S|\}$ lists the members of $S$ in the order of $\mathcal R$.
--
--   **Prize allocation rules.** A rule $\varphi$ assigns to every competition an allocation $\varphi(N, \mathcal R, E) \in \mathbb R^N_+$ with
--   $$\sum_{i \in N} \varphi_i(N, \mathcal R, E) = E.$$
--
--   **Axioms.** For every competition $(N, \mathcal R, E)$ and competitors $i, j \in N$:
--
--   1. *Anonymity*: if $|N| = |N'|$ and $\mathcal R(i) = \mathcal R'(j)$, then $\varphi_i(N, \mathcal R, E) = \varphi_j(N', \mathcal R', E)$.
--   2. *Order preservation*: if $\mathcal R(i) < \mathcal R(j)$, then $\varphi_i(N, \mathcal R, E) \ge \varphi_j(N, \mathcal R, E)$.
--   3. *Endowment monotonicity*: if $E < E'$, then $\varphi_i(N, \mathcal R, E) \le \varphi_i(N, \mathcal R, E')$.
--   4. *Endowment continuity*: $E \mapsto \varphi_i(N, \mathcal R, E)$ is continuous on $\mathbb R_+$.
--   5. *Consistency*: for every nonempty $S \subseteq N$ and $i \in S$,
--   $$\varphi_i(N, \mathcal R, E) = \varphi_i\Big(S, \mathcal R_S, \sum_{j \in S} \varphi_j(N, \mathcal R, E)\Big).$$
--
--   **Interval rules.** $\varphi$ is an interval rule if there are pairwise disjoint open intervals $(a_k, b_k)$, $k = 1, 2, \dots$, with $a_k \in \mathbb R_+$, $b_k \in \mathbb R_+ \cup \{+\infty\}$ and $a_k \le b_k$, such that for every competition and every $i \in N$, writing $n = |N|$ and $r = \mathcal R(i)$,
--   $$\varphi_i(N, \mathcal R, E) = \begin{cases} a_k & \text{if } n a_k \le E \le (n - r + 1) a_k + (r - 1) b_k; \\ E - (n - r) a_k - (r - 1) b_k & \text{if } (n - r + 1) a_k + (r - 1) b_k \le E \le (n - r) a_k + r b_k; \\ b_k & \text{if } (n - r) a_k + r b_k \le E \le n b_k; \\ E / n & \text{otherwise.} \end{cases}$$
--   In words: at endowment $n a_k$ every competitor gets $a_k$; as the endowment grows, the prizes are raised to $b_k$ one competitor at a time, from the top of the ranking down; if $E/n$ lies in none of the closed intervals $[a_k, b_k]$, the endowment is divided equally. The equal division rule is the interval rule with $a_k = b_k = 0$, the winner-takes-all rule has $a_1 = 0$, $b_1 = +\infty$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** A pair $(N, \mathcal R)$ is a duplicate-free nonempty list `l` of competitors, best first: $N$ is the set of entries, $|N|$ the length and $\mathcal R(i)$ = `pos l i` = (index of $i$ in `l`) + 1. Nonempty because $\sum_{i\in N}\varphi_i = E > 0$ is impossible for $N = \emptyset$. The subranking $\mathcal R_S$ is the sublist of the members of $S$. A rule is a function `φ : List U → ℝ → U → ℝ`; its values on non-rankings, negative endowments and non-competitors are irrelevant, and every axiom quantifies only over rankings, $E \ge 0$ and $i \in N$. Endowment continuity is continuity of each coordinate on $[0, \infty)$, which is convergence in $\mathbb R^N$. In interval rules the endpoints $b_k$ live in the extended reals (`EReal`), where $0 \cdot (+\infty) = 0$, so the term $(r-1) b_k$ vanishes for the winner and every case whose bound is $+\infty$ cannot fire, as on the page; the intervals are indexed by $\mathbb N$ (finitely many is the case of padding with $a_k = b_k = 0$, as for ED); $a_k \le b_k$ is implicit in "intervals $(a_k, b_k)$"; disjointness is of the open intervals, so degenerate intervals are allowed. Each case is an implication, so overlapping endpoints (where the case values agree) need no choice of $k$, and "otherwise" is the case that $E \notin [n a_k, n b_k]$ for every $k$.
-- source:
--   Dietzenbacher and Kondratev, Fair and Consistent Prize Allocation in Competitions, arXiv:2008.08985v2, pp. 8–12, §2.1 (model, prize allocation rules, anonymity, order preservation, endowment monotonicity, endowment continuity), §2.2 (subranking, consistency, interval rules)

import Mathlib

namespace PrizeAlloc.Interval

variable {U : Type*} [DecidableEq U]

/-- A ranking (p. 8) of a nonempty finite set `N ⊆ U` of competitors, written as the list of the
competitors from the highest position to the lowest: `N = l.toFinset`, `|N| = l.length`. -/
def IsRanking (l : List U) : Prop := l.Nodup ∧ l ≠ []

/-- The position `R(i) ∈ {1, …, |N|}` of competitor `i` in the ranking `l` (1-based, as on p. 8). -/
def pos (l : List U) (i : U) : ℕ := l.idxOf i + 1

/-- The subranking `R_S` (p. 10): the members of `S` in the order of `l`. -/
def sub (l : List U) (S : Finset U) : List U := l.filter (· ∈ S)

/-- A prize allocation rule (p. 9): for each competition `(N, R, E)` with `E ≥ 0`, the prizes are
nonnegative and sum to `E`. Values off this domain are irrelevant. -/
def IsPrizeRule (φ : List U → ℝ → U → ℝ) : Prop :=
  ∀ l E, IsRanking l → 0 ≤ E →
    (∀ i ∈ l, 0 ≤ φ l E i) ∧ ∑ i ∈ l.toFinset, φ l E i = E

/-- Anonymity (p. 9). -/
def Anonymous (φ : List U → ℝ → U → ℝ) : Prop :=
  ∀ l l' E, IsRanking l → IsRanking l' → 0 ≤ E → l.length = l'.length →
    ∀ i ∈ l, ∀ j ∈ l', pos l i = pos l' j → φ l E i = φ l' E j

/-- Order preservation (pp. 9–10). -/
def OrderPreserving (φ : List U → ℝ → U → ℝ) : Prop :=
  ∀ l E, IsRanking l → 0 ≤ E → ∀ i ∈ l, ∀ j ∈ l, pos l i < pos l j → φ l E j ≤ φ l E i

/-- Endowment monotonicity (p. 10). -/
def EndowmentMonotone (φ : List U → ℝ → U → ℝ) : Prop :=
  ∀ l E E', IsRanking l → 0 ≤ E → E < E' → ∀ i ∈ l, φ l E i ≤ φ l E' i

/-- Endowment continuity (p. 10): each prize is continuous in the endowment on `ℝ₊`. -/
def EndowmentContinuous (φ : List U → ℝ → U → ℝ) : Prop :=
  ∀ l, IsRanking l → ∀ i ∈ l, ContinuousOn (fun E => φ l E i) (Set.Ici 0)

/-- Consistency (p. 10). -/
def Consistent (φ : List U → ℝ → U → ℝ) : Prop :=
  ∀ l E, IsRanking l → 0 ≤ E → ∀ S : Finset U, S ⊆ l.toFinset → S.Nonempty →
    ∀ i ∈ S, φ l E i = φ (sub l S) (∑ j ∈ S, φ l E j) i

/-- Interval rules (p. 12): there are disjoint open intervals `(a k, b k)`, `k ∈ ℕ`, with
`a k ∈ ℝ₊` and `b k ∈ ℝ₊ ∪ {+∞}` (encoded in `EReal`), such that for each competition and each
competitor the four cases of the page hold. Each case is an implication, so overlapping endpoints
(where the values agree) need no choice of `k`; "otherwise" means that `E` lies in no
`[|N| a k, |N| b k]`. -/
def IsIntervalRule (φ : List U → ℝ → U → ℝ) : Prop :=
  ∃ (a : ℕ → ℝ) (b : ℕ → EReal),
    (∀ k, 0 ≤ a k ∧ (a k : EReal) ≤ b k) ∧
    Pairwise (fun k k' => Disjoint (Set.Ioo (a k : EReal) (b k)) (Set.Ioo (a k' : EReal) (b k'))) ∧
    ∀ (l : List U) (E : ℝ), IsRanking l → 0 ≤ E → ∀ i ∈ l,
      (∀ k, ((l.length * a k : ℝ) : EReal) ≤ E ∧
          (E : EReal) ≤ (((l.length - pos l i + 1 : ℕ) * a k : ℝ) : EReal)
            + ((pos l i - 1 : ℕ) : EReal) * b k →
        φ l E i = a k) ∧
      (∀ k, (((l.length - pos l i + 1 : ℕ) * a k : ℝ) : EReal)
            + ((pos l i - 1 : ℕ) : EReal) * b k ≤ E ∧
          (E : EReal) ≤ (((l.length - pos l i : ℕ) * a k : ℝ) : EReal)
            + ((pos l i : ℕ) : EReal) * b k →
        (φ l E i : EReal) = (E : EReal) - (((l.length - pos l i : ℕ) * a k : ℝ) : EReal)
            - ((pos l i - 1 : ℕ) : EReal) * b k) ∧
      (∀ k, (((l.length - pos l i : ℕ) * a k : ℝ) : EReal)
            + ((pos l i : ℕ) : EReal) * b k ≤ E ∧
          (E : EReal) ≤ ((l.length : ℕ) : EReal) * b k →
        (φ l E i : EReal) = b k) ∧
      ((∀ k, ¬ (((l.length * a k : ℝ) : EReal) ≤ E ∧ (E : EReal) ≤ ((l.length : ℕ) : EReal) * b k)) →
        φ l E i = E / l.length)

end PrizeAlloc.Interval


