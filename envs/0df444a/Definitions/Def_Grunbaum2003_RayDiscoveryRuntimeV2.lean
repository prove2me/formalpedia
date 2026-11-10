-- Prove2me | Definitions.Def_Grunbaum2003_RayDiscoveryRuntimeV2
-- name    : Grunbaum2003_RayDiscoveryRuntimeV2
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-09T08:38:06.911193+00:00
-- url     : https://prove2.me/theorems/0f4c9f3d-3d09-4497-84d5-2167033c08a2
-- title:
--   Tape layouts and actual query events for ray discovery
-- statement:
--   These definitions specify the runtime data and query events used by a versioned ray-oracle reconstruction target. The underlying program, instruction set, real tape, step function, and run function are the existing canonical ones; no new oracle operation or machine capability is introduced.
--
--   For normalized facet forms and a finite set of discovered indices, the outer approximation is
--
--   $$
--   Q_S=\{x:L_i(x)\leq1\text{ for every }i\in S\}.
--   $$
--
--   A discovery table stores the number of known facets, the number of certified vertices, and the two array addresses in four fixed control cells beginning at the current head. Its first array contains the coordinate coefficients of the known normalized facet forms; its second contains the certified vertex coordinates. Bijections with the corresponding finite sets specify the row ordering, and the arrays are disjoint from each other and the control cells.
--
--   A query event between two times is witnessed by an actual run from the blank input to a configuration whose next instruction is an oracle query and whose query cells contain the designated vector. Thus a geometric expression involving an oracle response is accompanied by a real query event, rather than by an independently chosen numerical budget.
--
--   A face/vertex table stores its face count, vertex count, and array address in three fixed control cells. The array contains the Boolean incidence matrix for the supplied face and exposed-vertex enumerations:
--
--   $$
--   A_{a,k}=\begin{cases}1&v_k\in F_a,\\0&v_k\notin F_a.\end{cases}
--   $$
--
--   The blank configuration has program counter, tape head, and query counter zero and an everywhere-zero tape. These are literal representation and event definitions. They do not assume the existence or correctness of a reconstruction program and contain no unproved theorem.
--
--   **Formalization Note.** These tape layouts are a supplied implementation interface, not a transcription of a layout specified by Gritzmann–Klee–Westwater. They support the runtime repair of the disproved fixed-program leaf while preserving the original canonical machine semantics.
-- source:
--   P. Gritzmann, V. Klee, J. Westwater, Polytope Containment and Determination by Linear Probes, Proc. London Math. Soc. (3) 70 (1995), 691–720, DOI https://doi.org/10.1112/plms/s3-70.3.691, §5.3–5.5, pp. 714–715. The runtime tape layouts and execution-coupled phase specification are a supplied versioned repair, not verbatim source declarations. Original reconstruction root: https://prove2.me/theorems/60ec78e9-77c6-458e-8d47-5b17e861648a. Disproved predecessor: https://prove2.me/theorems/ff61873e-edc0-4145-acb9-a5e057125207.

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_IsPolytopeRayOracle
import Definitions.Def_Grunbaum2003_rayMachineRun
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_IsRayFaceLatticeOutput
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Data.Finset.Card

set_option autoImplicit false
open scoped Classical BigOperators

namespace Grunbaum2003.RayV2

/-- The canonical blank input, with no polytope-dependent data on the tape. -/
def blank : RayConfiguration := ⟨0, 0, fun _ => 0, 0⟩

/-- The outer approximation determined by the facets actually discovered so far. -/
def outerApproximation {d m : ℕ}
    (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ) (S : Finset (Fin m)) : Set (Fin d → ℝ) :=
  {x | ∀ i ∈ S, L i x ≤ 1}

/-- A memory representation of the discovered normalized facet rows and certified
vertices. Dimensions and array addresses are data on tape, not code parameters.
The four control cells are followed by two disjoint finite arrays. -/
def DiscoveryTable {d m : ℕ} (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    (S : Finset (Fin m)) (C : Finset (Fin d → ℝ)) (c : RayConfiguration) : Prop :=
  ∃ (rowBase vertexBase : ℤ) (row : Fin S.card ≃ ↥S) (vertex : Fin C.card ≃ ↥C),
    c.tape c.head = (S.card : ℝ) ∧
    c.tape (c.head + 1) = (C.card : ℝ) ∧
    c.tape (c.head + 2) = (rowBase : ℝ) ∧
    c.tape (c.head + 3) = (vertexBase : ℝ) ∧
    c.head + 4 ≤ rowBase ∧ rowBase + (S.card * d : ℕ) ≤ vertexBase ∧
    (∀ (i : Fin S.card) (k : Fin d),
      c.tape (rowBase + (i.val * d + k.val : ℕ)) =
        L (row i).val (Pi.single k (1 : ℝ))) ∧
    (∀ (i : Fin C.card) (k : Fin d),
      c.tape (vertexBase + (i.val * d + k.val : ℕ)) = (vertex i).val k)

/-- The queried vector occurs at a query instruction of the actual execution
between two phase times. It is not supplied as an uncharged abstract oracle call. -/
def QueriedBetween {d : ℕ} (program : List RayInstruction)
    (oracle : (Fin d → ℝ) → Fin d → ℝ) (lo hi : ℕ) (v : Fin d → ℝ) : Prop :=
  ∃ (t next : ℕ) (c : RayConfiguration),
    lo ≤ t ∧ t < hi ∧
    rayMachineRun program oracle t blank = some c ∧
    program[c.pc]? = some (.query next) ∧
    ∀ i : Fin d, c.tape (c.head + (i.val : ℤ)) = v i

/-- Literal face/vertex incidence data at a runtime-discovered table location. -/
def FaceVertexTable {d n V : ℕ} {P : Set (Fin d → ℝ)}
    (e : Fin n ≃ PolytopeFace P)
    (vEnum : Fin V ≃ {x : Fin d → ℝ | IsExposed ℝ P {x}})
    (c : RayConfiguration) (base : ℤ) : Prop :=
  c.tape c.head = (n : ℝ) ∧ c.tape (c.head + 1) = (V : ℝ) ∧
    c.tape (c.head + 2) = (base : ℝ) ∧ c.head + 3 ≤ base ∧
    ∀ (a : Fin n) (k : Fin V),
      c.tape (base + (a.val * V + k.val : ℕ)) =
        if (vEnum k).val ∈ (e a).val then (1 : ℝ) else 0

end Grunbaum2003.RayV2


