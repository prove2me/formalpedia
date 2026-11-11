-- Prove2me | Definitions.Def_GraphSimOT_Gaps_LocalEdit
-- name    : GraphSimOT_Gaps_LocalEdit
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T18:06:55.277549+00:00
-- url     : https://prove2.me/theorems/5f3f80a2-9913-40a7-adf9-d7b0f33a1035
-- title:
--   ρ_H, bipartite matchings, the bipartite matching polytope, random matchings and Φ_v (App. D.2)
-- statement:
--   Objects of the rounding argument for the local edit distance (App. D.2).
--
--   For a graph $H$ on $[n]$, $\rho_H(w,w') = |N_H(w)\,\triangle\,N_H(w')|$ (`rhoH`) counts the vertices adjacent to exactly one of $w, w'$; it is a pseudometric.
--
--   For finite sets $V, W$ and an edge set $E \subseteq V\times W$ of a bipartite graph, a **matching** (`IsBipMatching E M`) is a set $M\subseteq E$ in which no two distinct pairs share an endpoint on either side. Its indicator vector is $1_M\in\mathbb R^{V\times W}$ (`indic`). The **bipartite matching polytope** of $E$ (`matchingPolytope`) is the convex hull of the indicator vectors of the matchings of $E$.
--
--   A **random matching** of $E$ is given by its law $p$ (`IsRandomMatching E p`): a probability distribution on the finitely many subsets $M\subseteq V\times W$ that gives positive mass only to matchings of $E$. Expectations and probabilities are the finite sums
--   $$\mathbb E[f(M)] = \sum_M p(M)\,f(M),\qquad \Pr(S(M)) = \sum_{M:\,S(M)} p(M)$$
--   (`expect`, `prob`). A **linear statistic** with coefficients $\alpha$ is $Z(M) = \sum_e \alpha_e 1[e\in M] = \sum_{e\in M}\alpha_e$ (`linStat`).
--
--   For graphs $G, H$ on $[n]$, a bijection $\sigma$ and a matching $M\subseteq [n]\times[n]$,
--   $$\Phi_v(M) = \sum_{(v',w')\in M}|A_G(v,v') - A_H(\sigma(v),w')|$$
--   (`Phi`) is the local cost of $v$ under $\sigma$ relative to $M$.
--
--   **Formalization Note.** A random matching is represented by its law on the finite set `Finset (V × W)`; every statement about it (marginals, tail probabilities) depends only on the law. $\rho_H$ is a natural number (`Set.ncard` of the symmetric difference of neighbour sets).
-- source:
--   Breitung, Gervens, Grohe, Graph Similarity Meets Optimal Transport, arXiv:2611.05048 (held version, sha256 1cd10e91…), App. D.2, pp. 28–29

import Mathlib
import Definitions.Def_GraphSimOT_Gaps_Distances

namespace GraphSimOT.Gaps

/-!
# Objects of the local edit rounding (App. D.2)

Breitung, Gervens, Grohe, *Graph Similarity Meets Optimal Transport*, arXiv:2611.05048
(held version, sha256 1cd10e91…), App. D.2, pp. 28–29.

* `rhoH H w w' = |N_H(w) △ N_H(w')|`, the pseudometric `ρ_H` on the vertices of `H`.
* Matchings of a bipartite graph with sides `V`, `W` and edge set `E ⊆ V × W`, the bipartite
  matching polytope (the convex hull of the indicator vectors of matchings), and random
  matchings, given by their law: a probability distribution on the finite set of subsets of
  `V × W`, supported on matchings of `E`.
* `Phi G H σ M v = Φ_v(M)`, the local cost of `v` under `σ` relative to a matching `M`.
-/

/-- `ρ_H(w, w') = |N_H(w) △ N_H(w')|` (App. D.2, p. 28), the number of vertices adjacent to
exactly one of `w`, `w'`. -/
noncomputable def rhoH {n : ℕ} (H : SimpleGraph (Fin n)) (w w' : Fin n) : ℕ :=
  (symmDiff (H.neighborSet w) (H.neighborSet w')).ncard

/-- `M ⊆ V × W` is a matching of the bipartite graph with edge set `E ⊆ V × W`: every pair of
`M` is an edge, and two distinct pairs of `M` share neither their `V`-end nor their `W`-end. -/
def IsBipMatching {V W : Type*} (E M : Finset (V × W)) : Prop :=
  M ⊆ E ∧ ∀ e ∈ M, ∀ e' ∈ M, e ≠ e' → e.1 ≠ e'.1 ∧ e.2 ≠ e'.2

/-- The indicator vector `1_M ∈ ℝ^{V×W}` of a set of pairs `M`. -/
def indic {V W : Type*} [DecidableEq V] [DecidableEq W] (M : Finset (V × W)) : V × W → ℝ :=
  fun e => if e ∈ M then 1 else 0

/-- The bipartite matching polytope of the bipartite graph with edge set `E ⊆ V × W`: the
convex hull of the indicator vectors of its matchings (vectors indexed by `V × W`, vanishing
off `E`). -/
def matchingPolytope {V W : Type*} [DecidableEq V] [DecidableEq W] (E : Finset (V × W)) :
    Set (V × W → ℝ) :=
  convexHull ℝ {x | ∃ M : Finset (V × W), IsBipMatching E M ∧ x = indic M}

/-- `p` is (the law of) a random matching of the bipartite graph with edge set `E`: a
probability distribution on the finite set of all `M ⊆ V × W` that gives positive mass only
to matchings of `E`. -/
def IsRandomMatching {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (E : Finset (V × W)) (p : Finset (V × W) → ℝ) : Prop :=
  (∀ M, 0 ≤ p M) ∧ ∑ M, p M = 1 ∧ ∀ M, p M ≠ 0 → IsBipMatching E M

/-- The expectation `E[f(M)] = ∑_M p(M) f(M)` of a function of a random matching with law `p`. -/
def expect {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (p : Finset (V × W) → ℝ) (f : Finset (V × W) → ℝ) : ℝ :=
  ∑ M, p M * f M

open Classical in
/-- The probability `Pr(S(M)) = ∑_{M : S(M)} p(M)` of an event of a random matching with
law `p`. -/
noncomputable def prob {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (p : Finset (V × W) → ℝ) (S : Finset (V × W) → Prop) : ℝ :=
  ∑ M with S M, p M

/-- The linear statistic `Z(M) = ∑_e α_e 1[e ∈ M] = ∑_{e ∈ M} α_e` with coefficients `α`. -/
def linStat {V W : Type*} (α : V × W → ℝ) (M : Finset (V × W)) : ℝ :=
  ∑ e ∈ M, α e

/-- `Φ_v(M) = ∑_{(v', w') ∈ M} |A_G(v, v') − A_H(σ(v), w')|`, the local cost of `v` under `σ`
relative to the matching `M` (App. D.2, p. 29). -/
noncomputable def Phi {n : ℕ} (G H : SimpleGraph (Fin n)) (σ : Equiv.Perm (Fin n))
    (M : Finset (Fin n × Fin n)) (v : Fin n) : ℝ :=
  ∑ e ∈ M, |adj G v e.1 - adj H (σ v) e.2|

end GraphSimOT.Gaps


