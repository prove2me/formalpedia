-- Prove2me | Definitions.Def_SortingCounterexamples_Optimal_Supplement_Geometric
-- name    : SortingCounterexamples_Optimal_Supplement_Geometric
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:36:38.796292+00:00
-- url     : https://prove2.me/theorems/dfdd84d4-abd5-406b-ab9a-645777176085
-- title:
--   §5 — geometric ranking classes, weighted-majority weights, pair probabilities and the strong-majority graph
-- statement:
--   This file adds the objects of §5 (*Geometric Rankings*) on top of the published interaction model (rankings of the items $0,\dots,n-1$, counterexample pairs, transcripts, lie counts).
--
--   1. **Scores and induced rankings.** A representation assigns to each item $i$ a vector $v_i\in\mathbb R^d$. For a direction $w\in\mathbb R^d$ the score of $i$ is $\langle v_i,w\rangle=\sum_{l=1}^d v_{i,l}w_l$. The direction $w$ **induces** the ranking $\pi$ when, for all items $i,j$,
--   $$i\prec_\pi j\iff\langle v_i,w\rangle<\langle v_j,w\rangle .$$
--   Such a direction gives pairwise distinct scores, so only directions inducing strict linear orders occur.
--   2. **Geometric classes.** A finite class $H$ of rankings is **$d$-dimensional geometric** with representation $v$ when every $\pi\in H$ is induced by some direction $w\in\mathbb R^d$. $H$ may be any such class; it need not contain all rankings induced by $v$.
--   3. **Weights.** After a transcript $h$ (the chronological list of queries $\hat\pi_t$ with the returned pairs $\{i,j\}$), the weight of a ranking $\pi$ is obtained from $q_0(\pi)=1$ by halving it on every round in which $\pi$ orders the returned pair as the query did, and leaving it unchanged otherwise (eq. (10)). These are exactly the rounds whose counterexample is untruthful for $\pi$, so $q_h(\pi)=2^{-\ell(\pi,h)}$ with $\ell(\pi,h)$ the published lie count.
--   4. **Pair probabilities.** $Q_h=\sum_{\pi\in H}q_h(\pi)$, $P_h(\pi)=q_h(\pi)/Q_h$, and
--   $$p_h(i,j)=\sum_{\pi\in H,\ i\prec_\pi j}P_h(\pi),$$
--   the probability that a ranking drawn from $P_h$ places $i$ before $j$.
--   5. **Strong-majority graph.** $G_h$ has an edge $i\to j$ between distinct items exactly when $p_h(i,j)>1-\frac1{d+1}$ (eq. (8)). A ranking is a **linear extension** of a relation when it places $i$ before $j$ for every edge $i\to j$.
--   6. **Rates.** $d^2\log n+dk$ (Theorem 5.1) and $d\log n+dk$ (Theorem 5.4), with the natural logarithm.
--
--   These objects are used by Lemmas 5.2 and 5.3 and Theorems 5.1 and 5.4.
--
--   **Formalization Note** Vectors of $\mathbb R^d$ are functions `Fin d → ℝ` with the standard dot product. The weights depend only on the transcript, and are defined for every transcript, not only for those produced by a particular learner. When $H$ is empty, $Q_h=0$ and Lean's division gives $p_h\equiv0$; the lemmas that normalize assume $H$ nonempty.
-- source:
--   Noga Alon, Shay Moran, Shlomo Moran, STOC 2027 submission #549 (October 2026), printed p. 22 / PDF p. 23, §5 (geometric classes, directions inducing strict linear orders) and proof of Theorem 5.1 (weights q_t, Q_t, P_t, p_t); printed p. 23 / PDF p. 24, eq. (8); printed p. 24 / PDF p. 25, eq. (10); printed p. 3–4 / PDF p. 4–5 (geometric rankings, Figure 2)

import Mathlib
import Definitions.Def_SortingCounterexamples_Optimal_Protocol

open scoped BigOperators

namespace SortingCounterexamples.Optimal.Supplement

open SortingCounterexamples.Optimal

/-- The score `⟨v i, w⟩` of item `i` in direction `w`, for a representation `v` of the items
by vectors of `ℝ^d` (standard inner product). -/
def score {n d : ℕ} (v : Fin n → Fin d → ℝ) (w : Fin d → ℝ) (i : Fin n) : ℝ :=
  ∑ l : Fin d, v i l * w l

/-- The direction `w` induces the ranking `π` in the representation `v`: for all items,
`i` comes before `j` in `π` exactly when `⟨v i, w⟩ < ⟨v j, w⟩`. Such a `w` gives pairwise
distinct scores, so only directions inducing strict linear orders are used. -/
def InducedBy {n d : ℕ} (v : Fin n → Fin d → ℝ) (w : Fin d → ℝ) (π : Ranking n) : Prop :=
  ∀ i j : Fin n, π.Before i j ↔ score v w i < score v w j

/-- `H` is a `d`-dimensional geometric class of rankings with representation `v`: every
ranking of `H` is induced by some direction `w ∈ ℝ^d`. `H` may be any such class, not
necessarily all rankings induced by `v`. -/
def IsGeometricClass {n d : ℕ} (v : Fin n → Fin d → ℝ) (H : Finset (Ranking n)) : Prop :=
  ∀ π ∈ H, ∃ w : Fin d → ℝ, InducedBy v w π

/-- The weight `q_t(π)` after the transcript `h`: starting from `1`, it is halved on every
round whose returned pair `{i, j}` is ordered by `π` as by that round's query (eq. (10)).
Those are exactly the rounds whose counterexample is untruthful for `π`, so
`q_h(π) = (1/2)^(lieCount π h)`. -/
noncomputable def weight {n : ℕ} (h : Transcript n) (π : Ranking n) : ℝ :=
  (1 / 2 : ℝ) ^ lieCount π h

/-- The total weight `Q_t = ∑_{π ∈ H} q_t(π)`. -/
noncomputable def totalWeight {n : ℕ} (H : Finset (Ranking n)) (h : Transcript n) : ℝ :=
  ∑ π ∈ H, weight h π

/-- `p_t(i, j)`: the probability that a ranking drawn from `H` with the normalized weights
`P_t(π) = q_t(π) / Q_t` places `i` before `j`. -/
noncomputable def pairProb {n : ℕ} (H : Finset (Ranking n)) (h : Transcript n) (i j : Fin n) :
    ℝ :=
  (∑ π ∈ H.filter (fun π => π.Before i j), weight h π) / totalWeight H h

/-- The strong-majority graph `G_t` (eq. (8)): an edge `i → j` between distinct items
whenever `p_t(i, j) > 1 - 1/(d+1)`. -/
def MajorityEdge {n : ℕ} (d : ℕ) (H : Finset (Ranking n)) (h : Transcript n) (i j : Fin n) :
    Prop :=
  i ≠ j ∧ 1 - 1 / ((d : ℝ) + 1) < pairProb H h i j

/-- `π` is a linear extension of the relation `E`: every edge `i → j` of `E` is respected,
`i` before `j` in `π`. -/
def IsLinearExtension {n : ℕ} (π : Ranking n) (E : Fin n → Fin n → Prop) : Prop :=
  ∀ i j : Fin n, E i j → π.Before i j

/-- The upper rate `d² log n + d k` of Theorem 5.1 (natural logarithm). -/
noncomputable def upperRate (n d k : ℕ) : ℝ := (d : ℝ) ^ 2 * Real.log n + d * k

/-- The lower rate `d log n + d k` of Theorem 5.4 (natural logarithm). -/
noncomputable def lowerRate (n d k : ℕ) : ℝ := (d : ℝ) * Real.log n + d * k

end SortingCounterexamples.Optimal.Supplement


