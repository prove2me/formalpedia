-- Prove2me | Definitions.Def_JonesUnknot_genus
-- name    : JonesUnknot_genus
-- status  : Definition
-- author  : @Lucas
-- created : 2026-11-17T00:32:23.880204+00:00
-- url     : https://prove2.me/theorems/ac26c8c6-819e-4061-92c4-84340d177432
-- title:
--   Seifert genus, reduced and alternating diagrams
-- statement:
--   Seifert circles, the Seifert genus of a knot, and the reduced and alternating predicates for PD codes.
--
--   **Seifert's algorithm** smooths each crossing respecting orientation, connecting the incoming under-strand to the outgoing over-strand; the resulting circles are the **Seifert circles**, counted by `seifertCircles` $s$. The canonical Seifert surface has $s$ disks and $n$ bands, so its genus is
--   $$g_{\mathrm{alg}}(D)=\frac{n-s+1}{2}.$$
--
--   The **Seifert genus of the knot** is the minimum of $g_{\mathrm{alg}}$ over all diagrams Reidemeister-equivalent to $D$:
--   $$g(D)=\min\{\,g_{\mathrm{alg}}(D') : D'\sim D\,\}.$$
--   This is a knot invariant; $g(D)=0$ exactly for the unknot. It is this invariant — not the canonical genus of the exhibited diagram, which can be positive for an unknot diagram — that certifies knottedness in the goal. The equivalence relation reuses the platform's `PD.ReidemeisterEquiv`.
--
--   A diagram is **reduced** when no simplifying Reidemeister I or II move lowers its crossing number. It is **alternating** when, travelling along the strand, over- and under-passages alternate.
--
--   **Formalization Note.** `seifertGenus` is an `sInf` over a nonempty set of naturals (the diagram itself is a witness). `Reduced` and `Alternating` reuse `PD.R1`/`PD.R2` and the dart orientation from the planar layer.
-- source:
--   Epoch AI FrontierMath, The Jones Unknot Conjecture, https://epoch.ai/frontiermath/open-problems/jones-unknot ; L. H. Kauffman, State models and the Jones polynomial, Topology 26 (1987), 395-407. ; P. Ozsváth, Z. Szabó, Holomorphic disks and genus bounds, Geom. Topol. 8 (2004), 311-334.

import Mathlib
import Definitions.Def_ManolescuPiccirillo_PD
import Definitions.Def_ManolescuPiccirillo_Kirby
import Definitions.Def_JonesUnknot_planar

open Classical
noncomputable section

namespace JonesUnknot
open ManolescuPiccirillo

/-- The oriented (Seifert) smoothing pairs at each crossing, determined by the strand
orientation: connect the incoming under-strand to the outgoing over-strand. -/
def seifertPairs (D : PD) : List (ℕ × ℕ) :=
  (List.ofFn (fun i : Fin D.crossings.length =>
    let c := D.crossings.get i
    if overIn3 D i then [(c 0, c 1), (c 2, c 3)] else [(c 0, c 3), (c 1, c 2)])).flatMap id

def seifertPaired (D : PD) (x y : ℕ) : Prop :=
  (x, y) ∈ seifertPairs D ∨ (y, x) ∈ seifertPairs D

def seifertGraph (D : PD) : SimpleGraph D.labels :=
  SimpleGraph.fromRel (fun x y => seifertPaired D x.val y.val ∧ x ≠ y)

/-- The number of Seifert circles of the diagram. -/
def seifertCircles (D : PD) : ℕ :=
  if D.crossings = [] then 1 else Fintype.card (seifertGraph D).ConnectedComponent

/-- The genus of the canonical Seifert surface produced by Seifert's algorithm:
`g = (n - s + 1) / 2`. -/
def seifertAlgGenus (D : PD) : ℕ := (D.numCrossings - seifertCircles D + 1) / 2

/-- The Seifert genus of the knot: the minimum canonical genus over all diagrams
Reidemeister-equivalent to `D`. -/
def seifertGenus (D : PD) : ℕ :=
  sInf {g : ℕ | ∃ D', D.ReidemeisterEquiv D' ∧ seifertAlgGenus D' = g}

/-- A diagram is reduced when it admits no simplifying Reidemeister I or II move. -/
def Reduced (D : PD) : Prop :=
  ¬ ∃ D', (D.R1 D' ∨ D.R2 D') ∧ D'.numCrossings < D.numCrossings

def IsInDart (D : PD) (d : Dart D) : Prop :=
  d.2 = 0 ∨ (d.2 = 1 ∧ ¬ overIn3 D d.1) ∨ (d.2 = 3 ∧ overIn3 D d.1)

/-- Along the strand, over- and under-passages alternate. -/
def Alternating (D : PD) : Prop :=
  ∀ d : Dart D, IsInDart D d → ((d.2 = 0) ≠ ((strandSucc D d).2 = 0))

end JonesUnknot


