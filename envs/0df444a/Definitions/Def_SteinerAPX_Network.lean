-- Prove2me | Definitions.Def_SteinerAPX_Network
-- name    : SteinerAPX_Network
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:33:13.931541+00:00
-- url     : https://prove2.me/theorems/ed342e98-3e6d-4819-9e63-728d202eddeb
-- title:
--   Segment networks, their length, and the Euclidean Steiner optimum $\mathrm{OPT}(P)$
-- statement:
--   Let $V$ be a real inner product space (in this mission always $\mathbb R^D$). A **network** $N$ is a finite set of closed line segments $[a,b]\subseteq V$, each given by its pair of endpoints. Its **carrier** is the union $|N|=\bigcup_{[a,b]\in N}[a,b]$ and its **length** is
--   $$
--   \operatorname{len}(N)=\sum_{[a,b]\in N}\|a-b\|.
--   $$
--   A network **spans** a point set $P\subseteq V$ if $P\subseteq |N|$ and $|N|$ is connected. The **Euclidean Steiner optimum** of $P$ is
--   $$
--   \mathrm{OPT}(P)=\inf\{\operatorname{len}(N) : N \text{ spans } P\}.
--   $$
--   Endpoints of segments are arbitrary points of the space, so **Steiner points** may be placed anywhere, as in the Euclidean Steiner Tree problem: connect $n$ given terminals by a shortest network. For a set $Z\subseteq V$, the **length of $N$ inside $Z$** is the one-dimensional Hausdorff measure $\mathcal H^1(|N|\cap Z)$.
--
--   This is the objective of the Euclidean Steiner Tree problem; every hardness statement of the mission is phrased through $\mathrm{OPT}$.
--
--   **Formalization Note** Crossing segments meet at the crossing, which acts as a free Steiner point. A degenerate segment $[a,a]$ is allowed, so a single point has $\mathrm{OPT}=0$. Overlapping segments only overcount $\operatorname{len}$ and do not change the infimum. $\mathrm{OPT}$ is an infimum (`sInf`); on a finite set the spanning family is nonempty (a star) and bounded below by $0$, and every statement applies it to finite sets. The Hausdorff length is finite for every network and is converted to $\mathbb R$.
-- source:
--   S. Bartlmae, Inapproximability of Euclidean Steiner Tree, STOC 2027 submission (manuscript sha256 6f78a9ea…), §1, p.1 (PDF p.3); Definition 5, §4.1, p.13 (PDF p.15)

import Mathlib

namespace SteinerAPX

open MeasureTheory

/-- **Networks of line segments, their length, and the Euclidean Steiner optimum.**
S. Bartlmae, *Inapproximability of Euclidean Steiner Tree*, STOC 2027 submission (manuscript
sha256 6f78a9ea…), §1, p.1 (PDF p.3), and Definition 5, §4.1, p.13 (PDF p.15): "We consider the
Euclidean Steiner Tree problem of connecting n given points in Rd by a shortest network. These
points are called terminals and additional Steiner points may be placed anywhere in the space. The
length of a network is the sum of its Euclidean edge lengths."

A network is a finite set of closed line segments `[a, b]`, each given by its endpoint pair
`(a, b)`. Its `carrier` is the union of the segments, its length `len` the sum of the segment
lengths. A network `N` spans a point set `P` when `P` lies in the carrier and the carrier is
connected; `opt P` is the infimum of `len N` over spanning networks.

**Formalization Note** Endpoints are arbitrary points of the space, so Steiner points are free.
Two segments that cross meet at the crossing point, which then acts as a Steiner point at no cost.
A degenerate segment `(a, a)` is allowed, so a one-point set has `opt = 0`. Overlapping segments
only overcount `len`, which does not change the infimum. `opt P` is an infimum and need not be
attained by a given network; for a finite `P` the spanning family is nonempty (a star), and when
it is empty (`P` not coverable by finitely many segments) `sInf ∅ = 0`; every statement of the
mission applies `opt` to finite sets. `lengthIn N Z` is the one-dimensional Hausdorff measure of
the part of the carrier inside `Z` ("the length of T inside Z", Lemma 11, p.15); it is finite for
every network, so the conversion to `ℝ` loses nothing. -/
abbrev Network (V : Type*) := Finset (V × V)

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The union of the segments of a network. -/
def carrier (N : Network V) : Set V := ⋃ e ∈ N, segment ℝ e.1 e.2

/-- The length of a network: the sum of its Euclidean segment lengths. -/
def len (N : Network V) : ℝ := ∑ e ∈ N, dist e.1 e.2

/-- `N` spans `P`: `P` lies on the network and the network is connected. -/
def Spans (P : Set V) (N : Network V) : Prop := P ⊆ carrier N ∧ IsConnected (carrier N)

/-- `OPT(P)`: the length of a shortest network spanning `P`, as an infimum. -/
noncomputable def opt (P : Set V) : ℝ := sInf (len '' {N : Network V | Spans P N})

/-- The length of the part of a network inside a set `Z` (one-dimensional Hausdorff measure). -/
noncomputable def lengthIn [MeasurableSpace V] [BorelSpace V] (N : Network V) (Z : Set V) : ℝ :=
  (μH[1] (carrier N ∩ Z)).toReal

end SteinerAPX


