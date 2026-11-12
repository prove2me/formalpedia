-- Prove2me | Definitions.Def_DSDensity1246_Main_oneInclusion
-- name    : DSDensity1246_Main_oneInclusion
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T16:10:29.194698+00:00
-- url     : https://prove2.me/theorems/aa5ccdc5-9035-4b42-bea9-9b5954ef5a86
-- title:
--   Direction-indexed one-inclusion hypergraph and finite fibers
-- statement:
--   For an arbitrary set of words $W\subseteq Y^n$, a direction $i$, and an assignment $a$ on all coordinates except $i$, define
--
--   $$e_{i,a}=\{w\in W:w|_{[n]\setminus\{i\}}=a\}.$$
--
--   The one-inclusion hypergraph has vertex set $W$ and edges indexed by the pairs $(i,a)$ for which $e_{i,a}$ is nonempty. Incidence is membership in this fiber. Different directions remain different edges even when their vertex sets coincide.
--
--   For finite $W$, the realized assignments are the finite image of $W$ under deletion of coordinate $i$, and the finite fiber is obtained by filtering $W$ for that assignment. These definitions permit finite graph sums without enumerating an infinite ambient label space.
--
--   **Formalization Note** Coordinate complements are subtypes of $\mathrm{Fin}\,n$. The dependent edge index retains the direction and its nonempty fiber. A singleton word therefore has exactly $n$ indexed incident edges.
-- source:
--   Chirag Pabbaraju, STOC 2027 submission #1246 (October 2026), p. 13, Definition 4, Eq. (8); realized behaviors also §4, p. 15

import Mathlib

namespace DSDensity1246.Main

/-- A word's behavior on all coordinates other than `i` (§4, p. 15). -/
def away {Y : Type*} {n : ℕ} (i : Fin n) (w : Fin n → Y) :
    ({j : Fin n // j ≠ i} → Y) :=
  fun j => w j.val

/-- Definition 4, p. 13, (8): the fiber indexed by direction and behavior. -/
def edge {Y : Type*} {n : ℕ} (W : Set (Fin n → Y))
    (i : Fin n) (a : {j : Fin n // j ≠ i} → Y) : Set (Fin n → Y) :=
  {w ∈ W | away i w = a}

/-- The direction is retained in the edge index, even for coincident vertex sets.
Together with vertex set `W` and incidence `w ∈ edge W i a`, this is G(W). -/
def OneInclusionEdge {Y : Type*} {n : ℕ} (W : Set (Fin n → Y)) :=
  (i : Fin n) × {a : ({j : Fin n // j ≠ i} → Y) // (edge W i a).Nonempty}

/-- Only realized behaviors are enumerated in the finite graph. -/
noncomputable def finiteBehaviors {Y : Type*} {n : ℕ}
    (W : Finset (Fin n → Y)) (i : Fin n) :
    Finset ({j : Fin n // j ≠ i} → Y) := by
  classical
  exact W.image (away i)

/-- Finite version of the same fiber, with no assumption on the ambient label type. -/
noncomputable def finiteFiber {Y : Type*} {n : ℕ}
    (W : Finset (Fin n → Y)) (i : Fin n)
    (a : {j : Fin n // j ≠ i} → Y) : Finset (Fin n → Y) := by
  classical
  exact W.filter (fun w => away i w = a)

end DSDensity1246.Main


