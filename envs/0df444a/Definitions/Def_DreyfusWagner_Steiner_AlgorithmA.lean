-- Prove2me | Definitions.Def_DreyfusWagner_Steiner_AlgorithmA
-- name    : DreyfusWagner_Steiner_AlgorithmA
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T12:04:04.224835+00:00
-- url     : https://prove2.me/theorems/3c3ac931-9e87-49f0-9d96-53d2c8771b68
-- title:
--   Algorithm A of Dreyfus and Wagner: the dynamic-programming table $S[D,I]$ and the returned value $v$
-- statement:
--   Let the node set $N$ be finite and linearly ordered, so that every nonempty node set $D$ has a first element $D[1]$. For a node set $D$ let
--   $$\operatorname{splits}(D) = \{\, E : D[1] \in E,\ E \subsetneq D \,\},$$
--   the subsets enumerated in lines (10) and (18) of Algorithm A (empty when $D$ is empty). Each unordered splitting $\{E, D - E\}$ of $D$ into two nonempty parts appears exactly once.
--
--   Given a distance table $d(i,j)$ with values in $\mathbb{R} \cup \{+\infty\}$, the table $S[D, I]$ of Algorithm A is defined by recursion on $\|D\|$:
--
--   1. $S[\{t\}, I] = d(t, I)$ (lines (1)–(3));
--   2. for $\|D\| \ge 2$ (lines (5)–(14)),
--   $$S[D, I] = \min_{J \in N}\Big( d(I, J) + \min_{E \in \operatorname{splits}(D)} \big(S[E, J] + S[D - E, J]\big) \Big);$$
--   3. $S[\emptyset, I] = +\infty$ (never used by the algorithm).
--
--   Given a graph $G$ with arc lengths, a node set $Y$ and a node $q$, Algorithm A sets $C = Y - \{q\}$, uses the shortest-path lengths $D(i,j)$ of $G$ as the distance table, and returns (lines (15)–(20))
--   $$v = \min_{J \in N}\Big( D(q, J) + \min_{E \in \operatorname{splits}(C)} \big(S[E, J] + S[C - E, J]\big) \Big).$$
--   A minimum over an empty index set is $+\infty$, as in lines (7), (9), (15) and (17), and $+\infty$ plus anything is $+\infty$.
--
--   The algorithm fills the table by increasing $\|D\|$ for $2 \le \|D\| \le \|C\| - 1$; the paper remarks (p. 203) that the order in which the subsets are processed is immaterial, which is what licenses the recursive formulation. The algorithm is built from $D(i,j)$, addition and minima only; it never refers to Steiner lengths.
--
--   **Formalization Note** Values live in `WithTop ℝ`, where `⊤` is $+\infty$, `⊤ + x = ⊤`, and `Finset.inf` over an empty set is `⊤`. The order on nodes is a `LinearOrder V` and $D[1]$ is `Finset.min'`. The table `tableA d D I` is defined by well-founded recursion on the cardinality of `D`; the file also contains the structural lemmas `mem_splits`, `card_lt_of_mem_splits` and `card_sdiff_lt_of_mem_splits` that justify the recursion.
-- source:
--   Dreyfus, Wagner, The Steiner Problem in Graphs, Networks 1 (1971), p. 202, §4 (D(i,j), C = Y − {q}, A[1], ⊊) and p. 203, Algorithm A, lines (1)–(20)

import Mathlib
import Definitions.Def_DreyfusWagner_Steiner_SteinerProblem

namespace DreyfusWagner.Steiner

variable {V : Type*}

/-- The subsets `E` enumerated in lines (10) and (18) of Algorithm A for a node set `D`:
`D[1] ∈ E ∧ E ⊊ D`, where `D[1]` is the first (least) element of `D` in the fixed order of the
nodes (Dreyfus–Wagner 1971, §4, pp. 202–203). Empty when `D` is empty. -/
def splits [LinearOrder V] (D : Finset V) : Finset (Finset V) :=
  if h : D.Nonempty then D.powerset.filter (fun E => D.min' h ∈ E ∧ E ≠ D) else ∅

theorem mem_splits [LinearOrder V] {D E : Finset V} :
    E ∈ splits D ↔ ∃ h : D.Nonempty, E ⊆ D ∧ D.min' h ∈ E ∧ E ≠ D := by
  unfold splits
  split_ifs with h
  · simp [h]
  · simp [h]

theorem card_lt_of_mem_splits [LinearOrder V] {D E : Finset V} (hE : E ∈ splits D) :
    E.card < D.card := by
  obtain ⟨_, hsub, _, hne⟩ := mem_splits.1 hE
  exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hsub, hne⟩)

theorem card_sdiff_lt_of_mem_splits [LinearOrder V] {D E : Finset V} (hE : E ∈ splits D) :
    (D \ E).card < D.card := by
  obtain ⟨h, _, hmin, _⟩ := mem_splits.1 hE
  refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨Finset.sdiff_subset, ?_⟩)
  intro heq
  rw [Finset.sdiff_eq_self_iff_disjoint] at heq
  exact Finset.disjoint_left.1 heq (D.min'_mem h) hmin

/-- The table `S[D, I]` of Algorithm A (Dreyfus–Wagner 1971, §4, p. 203), computed from a
distance table `d` (the paper's `D(i,j)`), by recursion on `‖D‖`:
* `‖D‖ = 1`, `D = {t}`: `S[{t}, I] = d(t, I)` (lines (1)–(3));
* `‖D‖ ≥ 2`: `S[D, I] = min_J ( d(I, J) + min_{E : D[1] ∈ E ⊊ D} (S[E, J] + S[D − E, J]) )`
  (lines (5)–(14));
* `D = ∅`: `∞` (never used by the algorithm).
Minima over empty index sets are `⊤ = ∞`, as in lines (7) and (9). -/
noncomputable def tableA [Fintype V] [LinearOrder V] (d : V → V → WithTop ℝ) (D : Finset V)
    (I : V) : WithTop ℝ :=
  if _h : D.card ≤ 1 then
    if hne : D.Nonempty then d (D.min' hne) I else ⊤
  else
    Finset.univ.inf fun J => d I J +
      (splits D).attach.inf fun E => tableA d E.1 J + tableA d (D \ E.1) J
termination_by D.card
decreasing_by
  · exact card_lt_of_mem_splits E.2
  · exact card_sdiff_lt_of_mem_splits E.2

/-- Algorithm A of Dreyfus–Wagner (1971, §4, p. 203): with `C = Y − {q}` and `D(i,j)` the
shortest-path length `pathDist G ℓ i j`, the returned value is
`v = min_J ( D(q, J) + min_{E : C[1] ∈ E ⊊ C} (S[E, J] + S[C − E, J]) )` (lines (15)–(20)),
where `S` is the table `tableA` built from `D`. -/
noncomputable def algorithmA [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (ℓ : Sym2 V → ℝ) (Y : Finset V) (q : V) : WithTop ℝ :=
  Finset.univ.inf fun J => pathDist G ℓ q J +
    (splits (Y.erase q)).inf fun E =>
      tableA (pathDist G ℓ) E J + tableA (pathDist G ℓ) (Y.erase q \ E) J

end DreyfusWagner.Steiner


