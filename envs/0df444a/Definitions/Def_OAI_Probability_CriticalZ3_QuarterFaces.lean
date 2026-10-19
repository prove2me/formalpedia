-- Prove2me | Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces
-- name    : OAI_Probability_CriticalZ3_QuarterFaces
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T17:53:49.203578+00:00
-- url     : https://prove2.me/theorems/823b57cf-4f34-4a74-a4a5-496fd0a23683
-- title:
--   The 24 quarter-faces of a cube
-- statement:
--   Quarter-faces of the boundary of the cube $\Lambda_n(c)$ in $\mathbb Z^3$ and the symmetries relating them.
--
--   1. **Indices.** A face index is a pair $(k,s)$ of a coordinate $k\in\{0,1,2\}$ and signs $s\in\{\pm\}^3$; only the sign pattern matters up to the $3\cdot8=24$ choices used.
--   2. **Quarter-faces.** The quarter-face $(k,s)$ consists of the vertices $x$ with $x_k=c_k\pm n$ (sign $s_k$) and, for every other coordinate $i$, $x_i$ between $c_i$ and $c_i\pm n$ according to $s_i$:
--   $$
--   x_k=c_k+s_kn,\qquad x_i\in[c_i,c_i+n]\ \text{or}\ [c_i-n,c_i]\ \ (i\ne k).
--   $$
--   3. **Symmetry.** The canonical face is $(0,+\!+\!+)$, and the signed symmetry swapping coordinates $k$ and $0$ with signs $s$ and shift $c$ maps $0$ to $c$ and the canonical quarter-face to the quarter-face $(k,s)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/QuarterFaces.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/QuarterFaces.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the CriticalZ3 mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry

-- Lean 4.33 compatibility: Measurable.of_eval is the renamed measurable_pi_lambda
-- (Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean at d13f23b records the alias).
section Lean433MeasurableOfEval
end Lean433MeasurableOfEval

namespace OAI

universe uE uI uV uW

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical

/-! The 24 signed-coordinate quarter-faces, symmetry and the Harris root bound.
The probability statements here are for the actual infinite lattice laws. -/
namespace CriticalZ3
open Classical

abbrev FaceIndex := Fin 3 × (Fin 3 → Bool)

def QuarterFace (c : Vertex) (n : ℕ) (f : FaceIndex) : Set Vertex :=
  {x | x f.1 = c f.1 + (if f.2 f.1 then (n : ℤ) else -(n : ℤ)) ∧
    ∀ i, i ≠ f.1 → if f.2 i then c i ≤ x i ∧ x i ≤ c i + (n : ℤ)
      else c i - (n : ℤ) ≤ x i ∧ x i ≤ c i}

def canonicalFace : FaceIndex := (0, fun _ => true)

namespace SignedSymmetry

end SignedSymmetry

def faceSymmetry (c : Vertex) (f : FaceIndex) : SignedSymmetry :=
  ⟨Equiv.swap f.1 0, f.2, c⟩

@[simp] theorem faceSymmetry_zero (c : Vertex) (f : FaceIndex) :
    (faceSymmetry c f).vertex 0 = c := by
  funext i
  simp [faceSymmetry,SignedSymmetry.vertex]

end CriticalZ3

namespace ProductCylinder

end ProductCylinder

namespace CriticalZ3
open Classical

end CriticalZ3

namespace CriticalZ3
open Filter Topology Classical

end CriticalZ3

end OAI


