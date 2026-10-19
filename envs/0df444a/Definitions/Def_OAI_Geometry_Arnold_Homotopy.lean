-- Prove2me | Definitions.Def_OAI_Geometry_Arnold_Homotopy
-- name    : OAI_Geometry_Arnold_Homotopy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T08:39:15.476045+00:00
-- url     : https://prove2.me/theorems/df72bedb-883b-4568-aee8-bd63e35a1a85
-- title:
--   Contraction of forms on a cylinder $\mathbb{R}\times E$ with the time direction
-- statement:
--   Let $E$ be a real normed vector space and consider the cylinder $\mathbb{R}\times E$.
--
--   1. **Spatial inclusion.** $v\mapsto(0,v)$ from $E$ to $\mathbb{R}\times E$.
--   2. **Cylinder contraction.** For a continuous alternating $(n+1)$-form $\theta$ on $\mathbb{R}\times E$, the $n$-form on $E$
--   $$
--   (\iota_{\partial_t}\theta)(v_1,\dots,v_n)=\theta\bigl((1,0),(0,v_1),\dots,(0,v_n)\bigr).
--   $$
--   This is a continuous linear operation in $\theta$.
--   3. **Slice contraction.** For a family $\Theta(t,z)$ of $(n+1)$-forms on the cylinder, the family $z\mapsto\iota_{\partial_t}\Theta(t,z)$ of $n$-forms on $E$ at a fixed time $t$.
--   4. **Finite dimensionality.** If $E$ is finite-dimensional, the space of continuous $n$-multilinear forms on $E$ is finite-dimensional.
--
--   These operations implement the homotopy formula for differential forms, where a form on a cylinder is integrated along the time direction. That formula shows that pullbacks along homotopic maps differ by an exact form.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/Arnold/Homotopy.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/Arnold/Homotopy.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ArnoldCounterexample mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ArnoldCounterexample
import Definitions.Def_OAI_Geometry_Arnold_Involution
import Definitions.Def_OAI_Geometry_Arnold_Projective
import Definitions.Def_OAI_Geometry_Arnold_Rotation
import Definitions.Def_OAI_Geometry_Arnold_Tangent
import Definitions.Def_OAI_Geometry_Arnold_Haar
import Definitions.Def_OAI_Geometry_Arnold_Differentiation
import Definitions.Def_OAI_Geometry_Arnold_Orbit
import Definitions.Def_OAI_Geometry_Arnold_Symplectic
import Definitions.Def_OAI_Geometry_Arnold_Coordinates
import Definitions.Def_OAI_Geometry_Arnold_Extension
import Definitions.Def_OAI_Geometry_Arnold_Deformation
import Definitions.Def_OAI_Geometry_Arnold_Exterior

namespace OAI

universe uE uD uF

noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator
open scoped Topology
open Function
open ContinuousAlternatingMap

open scoped BigOperators ContDiff
open ContinuousAlternatingMap

namespace ArnoldCounterexample.Forms
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Spatial inclusion in the cylinder. -/
def spatial : E →L[ℝ] ℝ × E := (0 : E →L[ℝ] ℝ).prod (.id ℝ E)

@[simp] lemma spatial_apply (v : E) : spatial v = (0, v) := rfl

/-- Fixed-direction contraction and slice restriction, bundled in norm topology. -/
def cylinderContraction (n : ℕ) :
    ((ℝ × E) [⋀^Fin (n + 1)]→L[ℝ] ℝ) →L[ℝ] (E [⋀^Fin n]→L[ℝ] ℝ) :=
  let P : ((ℝ × E) [⋀^Fin n]→L[ℝ] ℝ) →L[ℝ] (E [⋀^Fin n]→L[ℝ] ℝ) :=
    (compContinuousLinearMapₗ (ι := Fin n) (N := ℝ) spatial).mkContinuous
      (‖(spatial : E →L[ℝ] ℝ × E)‖ ^ n) (by
        intro θ
        simpa only [compContinuousLinearMapₗ, LinearMap.coe_mk, AddHom.coe_mk,
          Fintype.card_fin, mul_comm] using θ.norm_compContinuousLinearMap_le spatial)
  P.comp ((ContinuousLinearMap.apply ℝ
    ((ℝ × E) [⋀^Fin n]→L[ℝ] ℝ) (1, 0)).comp (curryLeftLI.toContinuousLinearMap))

@[simp] lemma cylinderContraction_apply (n : ℕ)
    (θ : (ℝ × E) [⋀^Fin (n + 1)]→L[ℝ] ℝ) (v : Fin n → E) :
    cylinderContraction n θ v = θ (Matrix.vecCons (1, 0) (fun i ↦ (0, v i))) := rfl

def sliceContraction {n : ℕ}
    (Θ : ℝ × E → (ℝ × E) [⋀^Fin (n + 1)]→L[ℝ] ℝ) (t : ℝ) :
    E → E [⋀^Fin n]→L[ℝ] ℝ := fun z ↦ cylinderContraction n (Θ (t, z))

instance finiteDimensional_multilinear_fin [FiniteDimensional ℝ E] (n : ℕ) :
    FiniteDimensional ℝ (E [×n]→L[ℝ] ℝ) := by
  induction n with
  | zero =>
    exact (continuousMultilinearCurryFin0 ℝ E ℝ).symm.toLinearEquiv.finiteDimensional
  | succ n ih =>
    let := ih
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) ↦ E) ℝ).symm.toLinearEquiv.finiteDimensional

end ArnoldCounterexample.Forms

end

end OAI


