-- Prove2me | Definitions.Def_OAI_Geometry_Arnold_Symplectic
-- name    : OAI_Geometry_Arnold_Symplectic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T08:30:45.25719+00:00
-- url     : https://prove2.me/theorems/8e3aae46-e05c-47d7-a388-0612a7e5d14f
-- title:
--   The standard symplectic form and squared norm on $\mathbb{C}^n$
-- statement:
--   For $n\in\mathbb{N}$, consider $\mathbb{C}^n$ as a real vector space with coordinates $x_i=\operatorname{Re}z_i$ and $y_i=\operatorname{Im}z_i$.
--
--   1. **Symplectic form.**
--   $$
--   \omega_n(u,v)=2\sum_{i<n}\bigl(\operatorname{Re}u_i\operatorname{Im}v_i-\operatorname{Im}u_i\operatorname{Re}v_i\bigr)=2\operatorname{Im}\sum_i\bar u_iv_i ,
--   $$
--   the normalization $d\bigl(\sum_ix_i\,dy_i-y_i\,dx_i\bigr)$.
--   2. **Squared norm.** $|z|^2=\sum_i|z_i|^2$, the Euclidean squared norm, not the max norm of the ambient product space.
--
--   These are the flat models whose restrictions to spheres and quadrics produce the symplectic and volume forms of the obstruction argument.
--
--   **Formalization Note** `symplectic n` is a continuous real-bilinear form on `Fin n → ℂ`, assembled from the coordinate functionals `reCoord n i` and `imCoord n i`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/Arnold/Symplectic.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/Arnold/Symplectic.lean by skeleton subtraction
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

namespace OAI

noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator

open scoped BigOperators ContDiff

namespace ArnoldCounterexample.Forms

abbrev CSpace (n : ℕ) := Fin n → ℂ

def reCoord (n : ℕ) (i : Fin n) : CSpace n →L[ℝ] ℝ :=
  Complex.reCLM.comp (ContinuousLinearMap.proj i)

def imCoord (n : ℕ) (i : Fin n) : CSpace n →L[ℝ] ℝ :=
  Complex.imCLM.comp (ContinuousLinearMap.proj i)

@[simp] lemma reCoord_apply (n : ℕ) (i : Fin n) (z : CSpace n) : reCoord n i z = (z i).re := rfl
@[simp] lemma imCoord_apply (n : ℕ) (i : Fin n) (z : CSpace n) : imCoord n i z = (z i).im := rfl

/-- Exactly the normalization d(sum x dy-y dx). -/
def symplectic (n : ℕ) : CSpace n →L[ℝ] CSpace n →L[ℝ] ℝ :=
  2 • ∑ i : Fin n, ((ContinuousLinearMap.mul ℝ ℝ).bilinearComp (reCoord n i) (imCoord n i) -
    (ContinuousLinearMap.mul ℝ ℝ).bilinearComp (imCoord n i) (reCoord n i))

/-- Euclidean squared norm, not the sup norm of the Pi ambient Banach space. -/
def normSq (n : ℕ) (z : CSpace n) : ℝ := ∑ i, Complex.normSq (z i)

end ArnoldCounterexample.Forms

end

end OAI


