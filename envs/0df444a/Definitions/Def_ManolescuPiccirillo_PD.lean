-- Prove2me | Definitions.Def_ManolescuPiccirillo_PD
-- name    : ManolescuPiccirillo_PD
-- status  : Definition
-- author  : @LG
-- created : 2026-11-16T18:49:23.749578+00:00
-- url     : https://prove2.me/theorems/19b862d4-6e4e-45e5-a51e-42f83d40c8c9
-- title:
--   Manolescu–Piccirillo: PD layer
-- statement:
--   Planar diagram (PD) codes for knot and link diagrams: validity, components, mirror, and the pairing graph.
-- source:
--   Epoch AI FrontierMath, smooth 4D Poincaré conjecture, https://epoch.ai/frontiermath/open-problems/smooth-poincare-4d

import Mathlib

open Classical
noncomputable section

namespace ManolescuPiccirillo

/-- A planar diagram (PD) code: a list of crossings, each given by four strand labels
listed counter-clockwise around the crossing, starting from the incoming under-strand.
The under-strand connects entries `0` and `2`; the over-strand connects entries `1` and `3`. -/
structure PD where
  crossings : List (Fin 4 → ℕ)

namespace PD

def entries (D : PD) : List ℕ := D.crossings.flatMap (fun c => [c 0, c 1, c 2, c 3])

def labels (D : PD) : Finset ℕ := D.entries.toFinset

/-- Every strand label occurs exactly twice. -/
def Valid (D : PD) : Prop := ∀ l ∈ D.labels, D.entries.count l = 2

def numCrossings (D : PD) : ℕ := D.crossings.length

/-- The pairing relation on labels: two labels are paired when they are the two ends of
one of the two strands passing through a crossing (under pair `{0,2}`, over pair `{1,3}`). -/
def Paired (D : PD) (x y : ℕ) : Prop :=
  ∃ c ∈ D.crossings, (c 0 = x ∧ c 2 = y) ∨ (c 2 = x ∧ c 0 = y)
    ∨ (c 1 = x ∧ c 3 = y) ∨ (c 3 = x ∧ c 1 = y)

def graph (D : PD) : SimpleGraph D.labels :=
  SimpleGraph.fromRel (fun x y => D.Paired x.val y.val ∧ x ≠ y)

/-- Number of link components of the diagram (the empty diagram is the unknot). -/
def numComponents (D : PD) : ℕ :=
  if D.crossings = [] then 1 else Fintype.card (D.graph.ConnectedComponent)

/-- A PD code is a knot diagram when it is valid and has a single component. -/
def IsKnot (D : PD) : Prop := D.Valid ∧ D.numComponents = 1

/-- The mirror diagram: reverse the cyclic order at every crossing. -/
def mirror (D : PD) : PD :=
  ⟨D.crossings.map (fun c => ![c 0, c 3, c 2, c 1])⟩

end PD
end ManolescuPiccirillo


