-- Prove2me | Definitions.Def_RandOnlineSetCoverSqrt_LowerBound_Canonical
-- name    : RandOnlineSetCoverSqrt_LowerBound_Canonical
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T19:32:29.956039+00:00
-- url     : https://prove2.me/theorems/e409e24e-1f70-458c-a06e-4738a7fe3026
-- title:
--   Canonical known set system and batch coverage
-- statement:
--   For a nonnegative integer $m$, label the available unit-cost sets by $[m]$. The complete known universe has one element $u_A$ for every nonempty subset $A\subseteq[m]$. Define
--
--   $$U_m=\{u_A:\varnothing\ne A\subseteq[m]\},\qquad S_i=\{u_A:i\in A\}.$$
--
--   An element's identity is its nonempty incidence label $A$. A finite batch is an ordered list of these elements, allowing repetitions. Its incidence list forgets only the subtype certificate of nonemptiness. A purchased label set $X$ covers the batch when it intersects every incidence in the list, using the published coverage predicate. The singleton elements distinguish the available sets, so there are exactly $m$ distinct sets. The empty universe at $m=0$ is harmless; the lower bound concerns sufficiently large $m$.
--
--   This interface identifies the fixed fully known system on which the lower bound holds. It does not hide element identities or future contents of available sets. Labels use zero-based finite indices, a relabeling of the source's $[m]$.
-- source:
--   Ilan Doron-Arad, Joseph (Seffi) Naor, STOC 2027 submission #1160 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1160.pdf, Definition 2.1, printed p. 6 / PDF p. 7; §3 equation (1), printed p. 7 / PDF p. 8

import Definitions.Def_RandOnlineSetCover_InfoLB_Model

namespace RandOnlineSetCoverSqrt.LowerBound

/-- §3, equation (1), printed p. 7 / PDF p. 8: the complete known universe. -/
abbrev Element (m : ℕ) := {A : Finset (Fin m) // A.Nonempty}

/-- The i-th unit-cost available set consists of exactly the elements whose label contains i. -/
def availableSet {m : ℕ} (i : Fin m) : Set (Element m) := {u | i ∈ u.val}

/-- Requests are identified with their complete, publicly known incidence labels. -/
def incidences {m : ℕ} (B : List (Element m)) : List (Finset (Fin m)) := B.map Subtype.val

/-- Equation (1), extended to a finite request batch; uses the published coverage predicate. -/
def CoversBatch {m : ℕ} (X : Finset (Fin m)) (B : List (Element m)) : Prop :=
  RandOnlineSetCover.InfoLB.Covers (incidences B) X

end RandOnlineSetCoverSqrt.LowerBound


