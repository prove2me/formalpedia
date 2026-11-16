-- Prove2me | Definitions.Def_DistancePreserver934_Exact_Supplement_Spanners
-- name    : DistancePreserver934_Exact_Supplement_Spanners
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:20:46.666199+00:00
-- url     : https://prove2.me/theorems/3d6a9180-48f3-405d-9e24-6826dbdae7e1
-- title:
--   Definition 26 — pairwise additive spanners
-- statement:
--   For a finite ordered demand set $P\subseteq V\times V$ and an integer $\beta\ge0$, a spanning subgraph $J\subseteq G$ is an additive $+\beta$ spanner when
--
--   $$\operatorname{dist}_G(s,t)\le\operatorname{dist}_J(s,t)\le\operatorname{dist}_G(s,t)+\beta\qquad((s,t)\in P).$$
--
--   Distances lie in $\mathbb N\cup\{\infty\}$. Thus unreachable original pairs remain at infinity; diagonal pairs are allowed. The technical unordered version quantifies over both orientations of each unordered pair. The satisfied-pair set consists precisely of pairs meeting the two inequalities; half-satisfaction means its cardinality is at least $|P|/2$. These predicates contain no edge-cost bound.
-- source:
--   Yanyu Chen, Yu Chen, Zihan Tan, Mingyang Yang, Improved Bounds on Distance Preservers, STOC 2027 submission #934 (October 2026); canonical source.pdf SHA-256 79b3d23a6e7b7fc6148c7a627181474a0129fb2f4c1d04ccd94c1da7987ed76b; Definition 26, printed p. 25 (PDF p. 26); half-satisfaction, Lemmas 34–35, printed pp. 30–32 (PDF pp. 31–33)

import Definitions.Def_DistancePreserver934_Exact_Preservers

set_option autoImplicit false

namespace DistancePreserver934.Exact.Supplement

open Classical

/-- The two distance inequalities for one ordered pair, with unreachable distance = infinity. -/
def GoodPair {V : Type} (G J : SimpleGraph V) (β : ℕ) (s t : V) : Prop :=
  G.edist s t ≤ J.edist s t ∧ J.edist s t ≤ G.edist s t + (β : ℕ∞)

/-- Definition 26: a spanning additive spanner for arbitrary ordered demands. -/
def IsAdditive {V : Type} (G J : SimpleGraph V) (P : Finset (V × V)) (β : ℕ) : Prop :=
  J ≤ G ∧ ∀ q ∈ P, GoodPair G J β q.1 q.2

/-- The equivalent technical unordered-demand guarantee. -/
def IsAdditiveUnordered {V : Type} (G J : SimpleGraph V) (Q : Finset (Sym2 V)) (β : ℕ) : Prop :=
  J ≤ G ∧ ∀ s t : V, s(s, t) ∈ Q → GoodPair G J β s t

/-- The demands satisfied by J, measured against original G-distances. -/
noncomputable def satisfiedPairs {V : Type} (G J : SimpleGraph V)
    (P : Finset (V × V)) (β : ℕ) : Finset (V × V) :=
  P.filter (fun q => GoodPair G J β q.1 q.2)

/-- Satisfaction of at least half of the original demands, with containment. -/
def HalfSatisfied {V : Type} (G J : SimpleGraph V) (P : Finset (V × V)) (β : ℕ) : Prop :=
  J ≤ G ∧ P.card ≤ 2 * (satisfiedPairs G J P β).card

end DistancePreserver934.Exact.Supplement


