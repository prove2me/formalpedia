-- Prove2me | Definitions.Def_PivotADO_OneHop_Charging
-- name    : PivotADO_OneHop_Charging
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:14:09.015034+00:00
-- url     : https://prove2.me/theorems/58a794ee-e1db-4a39-bde5-9eec4cbb1acd
-- title:
--   Alignment, non-aligned unordered pairs, middle segment and charges
-- statement:
--   Fix an oracle $(H,\mathcal P)$, a shortest-path system $P$, and integers $c,t$. A pivot $p_u$ is aligned with $v$ when $u,p_u$ and $u,v$ are reachable, both fixed paths have at least $t$ edges, and their first $t$ edges agree. A non-aligned pair is a distinct unordered pair $\{u,v\}$ with $\delta_G(u,v)=c$ such that no pivot is aligned at either endpoint.
--
--   $$Q=\text{the edge segment of }P(u,v)\text{ after its first }t\text{ edges and before its last }t\text{ edges}.$$
--
--   The concrete middle-edge list drops $t$ edges and takes $c-2t$. In applications $c\ge2t+1$, so this segment is nonempty and has the printed endpoints $q_u,q_v$. Sets of unordered pairs use $\mathrm{Sym}^2(V)$ with diagonal pairs excluded. A non-aligned pair charges an unordered hop $e$ if some realizing pivot pair has $e=\{p_u,p_v\}$. This relation permits all realizing choices, so its cardinality bound generalizes and bounds any one-choice charging scheme in the paper. Lists and sets retain the fixed path system throughout.
-- source:
--   Avi Kadria, Liam Roditty, STOC 2027 submission #584 (October 2026), §5.1, Claims 1.1–1.3, p.18–19; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/584.pdf

import Definitions.Def_PivotADO_OneHop_Oracle
import Definitions.Def_PivotADO_OneHop_PathSystem

set_option autoImplicit false
open scoped Classical
noncomputable section

namespace PivotADO.OneHop

/-- Alignment is agreement of the first t edges of the fixed paths, not existence
of some favorable shortest paths. §5.1, p.18. -/
def Aligned {V : Type*} {G : SimpleGraph V} (P : PathSystem G)
    (t : ℕ) (u v pu : V) : Prop :=
  ∃ (hp : G.Reachable u pu) (hv : G.Reachable u v),
    t ≤ (P.path u pu hp).length ∧ t ≤ (P.path u v hv).length ∧
      (P.path u pu hp).support.take (t + 1) = (P.path u v hv).support.take (t + 1)

def NonAligned {V : Type*} {G : SimpleGraph V} {r : ℕ} {k : ℝ}
    (O : Oracle G r k) (P : PathSystem G) (c t : ℕ) (u v : V) : Prop :=
  u ≠ v ∧ G.edist u v = (c : ℕ∞) ∧
    (∀ pu ∈ O.pivots u, ¬ Aligned P t u v pu) ∧
    (∀ pv ∈ O.pivots v, ¬ Aligned P t v u pv)

/-- Count each unordered pair once, regardless of orientation. -/
def nonAlignedPairs {V : Type*} {G : SimpleGraph V} {r : ℕ} {k : ℝ}
    (O : Oracle G r k) (P : PathSystem G) (c t : ℕ) : Set (Sym2 V) :=
  {e | ∃ u v, e = s(u, v) ∧ NonAligned O P c t u v}

/-- Q is constructed by deleting the first and last t edges of P(u,v).
At distance c its edge list has length c-2t. §5.1, p.19. -/
def middleEdges {V : Type*} {G : SimpleGraph V} (P : PathSystem G)
    (c t : ℕ) (u v : V) (h : G.Reachable u v) : List (Sym2 V) :=
  ((P.path u v h).edges.drop t).take (c - 2 * t)

/-- All realizing choices are permitted. This relation bounds every single-choice
charging scheme used in the printed proof. §5.1, Claim 1.3, p.19. -/
def chargedPairs {V : Type*} {G : SimpleGraph V} {r : ℕ} {k : ℝ}
    (O : Oracle G r k) (P : PathSystem G) (c t : ℕ) (e : Sym2 V) : Set (Sym2 V) :=
  {q | ∃ u v pu pv, q = s(u, v) ∧ NonAligned O P c t u v ∧
    Realizes O u v pu pv ∧ e = s(pu, pv)}

end PivotADO.OneHop


