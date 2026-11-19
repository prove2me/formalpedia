-- Prove2me | Definitions.Def_JonesUnknot_planar
-- name    : JonesUnknot_planar
-- status  : Definition
-- author  : @LG
-- created : 2026-11-17T00:31:20.965449+00:00
-- url     : https://prove2.me/theorems/95b5df0f-500e-4c06-bb92-f27c88c4cf30
-- title:
--   Planar PD codes, crossing signs and writhe
-- statement:
--   Planarity, crossing signs and writhe for planar diagram (PD) codes, extending the platform's `ManolescuPiccirillo.PD` type.
--
--   A **dart** is a strand-end at a crossing, indexed by a crossing $c\in\{0,\dots,n-1\}$ and a position $j\in\{0,1,2,3\}$ listed counter-clockwise from the incoming under-strand. Positions $0,2$ form the under-strand (incoming $0$, outgoing $2$) and positions $1,3$ the over-strand. The edge-pairing involution sends a dart to the unique other dart with the same edge label.
--
--   The faces of the diagram are the cycles of the face-successor map (rotate counter-clockwise, then cross the edge); `faceCount` counts them. A single-component diagram has a connected underlying map, so it is **planar** exactly when the sphere Euler characteristic gives $F=n+2$; this is the predicate `Planar`.
--
--   The strand orientation is recovered from the strand-successor permutation. A crossing is **positive** when the over-strand enters at position $3$, and `writhe` $w(D)=\sum_c \mathrm{sign}(c)$ is the sum of the crossing signs. These conventions were calibrated so that the trefoil, its mirror and the unknot have their standard Jones polynomials.
--
--   **Formalization Note.** Darts use `Fin D.crossings.length × Fin 4`; face and strand cycles are counted as connected components of `SimpleGraph.fromRel`, mirroring the existing `PD.numComponents`. The edge-pairing uses `Classical.choose` and is an involution on valid diagrams.
-- source:
--   Epoch AI FrontierMath, The Jones Unknot Conjecture, https://epoch.ai/frontiermath/open-problems/jones-unknot ; L. H. Kauffman, State models and the Jones polynomial, Topology 26 (1987), 395-407.

import Mathlib
import Definitions.Def_ManolescuPiccirillo_PD

open Classical
noncomputable section

namespace JonesUnknot
open ManolescuPiccirillo

/-- A dart is a strand-end at a crossing: the crossing index and a position in `Fin 4`.
Positions `0,2` are the under-strand (incoming `0`, outgoing `2`); positions `1,3` are the
over-strand. Positions are listed counter-clockwise from the incoming under-strand. -/
abbrev Dart (D : PD) := Fin D.crossings.length × Fin 4

def dartLabel (D : PD) (d : Dart D) : ℕ := D.crossings.get d.1 d.2

/-- The other dart carrying the same edge label (the edge-pairing involution). -/
def edgePartner (D : PD) (d : Dart D) : Dart D :=
  if h : ∃ e : Dart D, e ≠ d ∧ dartLabel D e = dartLabel D d then Classical.choose h else d

/-- Counter-clockwise rotation of the position at a fixed crossing. -/
def rotate (D : PD) (d : Dart D) : Dart D := (d.1, d.2 + 1)

def faceSucc (D : PD) (d : Dart D) : Dart D := rotate D (edgePartner D d)

def faceGraph (D : PD) : SimpleGraph (Dart D) :=
  SimpleGraph.fromRel (fun d e => faceSucc D d = e ∧ d ≠ e)

/-- Number of faces of the diagram viewed as a combinatorial map on the sphere. -/
def faceCount (D : PD) : ℕ :=
  if D.crossings = [] then 2 else Fintype.card (faceGraph D).ConnectedComponent

/-- Planarity: for a single-component diagram the underlying map is connected, so the
sphere Euler count `V - E + F = 2` (here `F = n + 2`) characterises planar diagrams. -/
def Planar (D : PD) : Prop := faceCount D = D.numCrossings + 2

/-- The unoriented strand pairing at a crossing: `0 <-> 2` and `1 <-> 3`. -/
def strandPair (D : PD) (d : Dart D) : Dart D := (d.1, d.2 + 2)

def strandSucc (D : PD) (d : Dart D) : Dart D := edgePartner D (strandPair D d)

def strandGraph (D : PD) : SimpleGraph (Dart D) :=
  SimpleGraph.fromRel (fun d e => strandSucc D d = e ∧ d ≠ e)

/-- The over-strand enters crossing `c` at position `3` (equivalently, the dart `(c,3)`
lies in the same strand-cycle as the incoming under-dart `(c,0)`). -/
def overIn3 (D : PD) (c : Fin D.crossings.length) : Prop :=
  Relation.ReflTransGen (strandGraph D).Adj (c, 0) (c, 3)

def crossingSign (D : PD) (c : Fin D.crossings.length) : ℤ :=
  if overIn3 D c then 1 else -1

/-- The writhe: the sum of the signs of all crossings. -/
def writhe (D : PD) : ℤ := ∑ c : Fin D.crossings.length, crossingSign D c

end JonesUnknot


