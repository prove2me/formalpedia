-- Prove2me | Definitions.Def_LocalOccupancyIS_Glauber_Supplement_Correspondence
-- name    : LocalOccupancyIS_Glauber_Supplement_Correspondence
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T22:00:41.724207+00:00
-- url     : https://prove2.me/theorems/9d77eb36-ea9e-4602-b6f6-9feef4876aa0
-- title:
--   Correspondence coloring, quantiles and chromatic local occupancy
-- statement:
--   A correspondence assignment gives each vertex a list of $k$ colors and each graph edge an arbitrary partial matching of forbidden color pairs. Lists are encoded by independently relabeled copies of $\{0,\ldots,k-1\}$. A coloring chooses one color at each vertex avoiding every forbidden pair. Write $\chi_c(G)$ for the least $k$ for which every assignment is colorable. The infimum is taken in $\mathbb N\cup\{\infty\}$, so an empty defining set cannot produce a false finite bound; for a finite graph the usual greedy argument establishes finiteness, and the empty graph has value zero. A bound $\chi_c(G)\le x$ is expressed by an actual colorable integer list size $k\le x$, together with the corresponding infimum bound.
--
--   For a finite graph $F$, $\lambda>0$ and $0<q<1$, define
--
--   $$Q_{F,q}(\lambda)=\max\{a\in\mathbb N:\mathbb P_{\mu_{F,\lambda}}(|I|\ge a)\ge q\}.$$
--
--   The maximum is over $0\le a\le|V(F)|$, which includes all feasible values and has $0$ feasible, including when $F$ is empty. Chromatic local occupancy requires positive parameters and, for every vertex and every subgraph $F$ of its neighborhood,
--
--   $$\frac{\beta p}{Z_F(\lambda)}\ge1\quad\text{or}\quad\gamma qQ_{F,q}(\lambda)\ge1.$$
--
--   Each subgraph has its own vertex set and may delete arbitrary edges. Matchings need not be perfect or consistent around cycles. This bundle defines the general correspondence object separately from the occupancy condition; it imposes no chromatic bound as an axiom.
-- source:
--   Ewan Davies, Brian Tan, STOC 2027 submission #982 (October 2026), Appendix A p.22, equation (26) and correspondence-coloring definitions

import Definitions.Def_LocalOccupancyIS_Glauber_Supplement_AppendixParameters

namespace LocalOccupancyIS.Glauber.Supplement
noncomputable section

/-- Fin k lists at each vertex, independently relabeled. Matchings may be partial
and have no cycle-consistency requirement. Symmetry gives uniqueness on both sides. -/
structure Correspondence {V : Type} (G : SimpleGraph V) (k : ℕ) where
  forbidden : V → Fin k → V → Fin k → Prop
  on_edge : ∀ u c v d, forbidden u c v d → G.Adj u v
  symm : ∀ u c v d, forbidden u c v d → forbidden v d u c
  matching : ∀ u c v d e, forbidden u c v d → forbidden u c v e → d = e

def CorrColorable {V : Type} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ C : Correspondence G k, ∃ f : V → Fin k, ∀ u v, ¬ C.forbidden u (f u) v (f v)

/-- Infimum in ENat: no colorable list size would give infinity, never junk zero.
For finite graphs greedy coloring establishes finiteness; the empty graph has value 0. -/
def corrChromatic {V : Type} (G : SimpleGraph V) : ℕ∞ :=
  sInf ((fun k : ℕ => (k : ℕ∞)) '' {k | CorrColorable G k})

/-- Explicit feasible list size is an upper bound on the least such size.
This also asserts attainment of a finite upper bound instead of converting infinity to 0. -/
def ColoringBound {V : Type} (G : SimpleGraph V) (x : ℝ) : Prop :=
  ∃ k : ℕ, CorrColorable G k ∧ corrChromatic G ≤ (k : ℕ∞) ∧ (k : ℝ) ≤ x

/-- Finite maximum of the quantile candidates; 0 is feasible whenever λ>0 and 0<q<1.
The explicit upper bound card V includes every possible quantile. -/
def quantile {V : Type} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) [DecidableRel F.Adj] (lam q : ℝ) : ℕ :=
  ((Finset.range (Fintype.card V + 1)).filter (fun a => q ≤ sizeGE F lam a)).sup id

/-- Every subgraph on its own vertex set A, with arbitrary edge deletions. -/
def ChromaticOccupancy {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (lam q β γ : ℝ) : Prop :=
  0 < lam ∧ 0 < q ∧ q < 1 ∧ 0 < β ∧ 0 < γ ∧
  ∀ u : V, ∀ A : Finset V, A ⊆ G.neighborFinset u →
    ∀ (F : SimpleGraph ↥A) [DecidableRel F.Adj],
      (∀ v w : A, F.Adj v w → G.Adj v.val w.val) →
        β * p lam / partition F lam ≥ 1 ∨ γ * q * quantile F lam q ≥ 1

end
end LocalOccupancyIS.Glauber.Supplement


