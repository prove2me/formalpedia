-- Prove2me | Definitions.Def_DistancePreserver934_Exact_Supplement_Sourcewise
-- name    : DistancePreserver934_Exact_Supplement_Sourcewise
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:21:15.944196+00:00
-- url     : https://prove2.me/theorems/ff2562ef-4f1e-420b-ac99-a5e999fb2e34
-- title:
--   Definition 33 — source-sensitive and complete sourcewise spanners
-- statement:
--   A source set $S\subseteq V$ restricts an ordered demand set by $P\subseteq S\times V$. Source-sensitive preservation is the pairwise additive guarantee on this selected $P$. Complete sourcewise preservation requires
--
--   $$\operatorname{dist}_G(s,t)\le\operatorname{dist}_J(s,t)\le\operatorname{dist}_G(s,t)+\beta\quad(s\in S,\ t\in V,\ t\text{ reachable from }s).$$
--
--   Both notions require $J\subseteq G$. The auxiliary set of reachable pairs between $S$ and $T$ is the reachable part of $S\times T$. These definitions preserve the distinction between partial demands and every reachable source pair; empty sources need no edges.
-- source:
--   Yanyu Chen, Yu Chen, Zihan Tan, Mingyang Yang, Improved Bounds on Distance Preservers, STOC 2027 submission #934 (October 2026); canonical source.pdf SHA-256 79b3d23a6e7b7fc6148c7a627181474a0129fb2f4c1d04ccd94c1da7987ed76b; Definition 33, printed p. 30 (PDF p. 31)

import Definitions.Def_DistancePreserver934_Exact_Supplement_Spanners

set_option autoImplicit false

namespace DistancePreserver934.Exact.Supplement

open Classical

/-- P has its first endpoints in the source set; no reachability restriction. -/
def SourceDemands {V : Type} (S : Finset V) (P : Finset (V × V)) : Prop :=
  ∀ q ∈ P, q.1 ∈ S

/-- Definition 33, partial source-sensitive preservation. -/
def IsSourceSensitive {V : Type} (G J : SimpleGraph V) (S : Finset V)
    (P : Finset (V × V)) (β : ℕ) : Prop :=
  SourceDemands S P ∧ IsAdditive G J P β

/-- All reachable ordered pairs between two vertex sets, including diagonal pairs. -/
noncomputable def reachablePairs {V : Type} (G : SimpleGraph V)
    (S T : Finset V) : Finset (V × V) :=
  (S.product T).filter (fun q => G.Reachable q.1 q.2)

/-- Definition 33: complete sourcewise preservation, not just a selected demand set. -/
def IsCompleteSourcewise {V : Type} (G J : SimpleGraph V) (S : Finset V) (β : ℕ) : Prop :=
  J ≤ G ∧ ∀ s ∈ S, ∀ t : V, G.Reachable s t → GoodPair G J β s t

end DistancePreserver934.Exact.Supplement


