-- Prove2me | Definitions.Def_NoHair_kerrNewman
-- name    : NoHair_kerrNewman
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-04T21:19:04.765612+00:00
-- url     : https://prove2.me/theorems/f8c3d6a0-7b2a-491b-bc20-023abe056cae
-- title:
--   No-hair: the Kerr–Newman spacetime as a manifold
-- statement:
--   The Kerr–Newman spacetime as a manifold.
--
--   For a rotation parameter $a$, the **Kerr–Newman spacetime** is the open subset $\{y\in\mathbb R^4: r(y)>0\}$ of Kerr–Schild coordinate space (the region where the Kerr–Schild radial function $r$ of the coordinate definitions is positive; the disc/ring where $r=0$ is removed), regarded as a 4-manifold. On it, the Kerr–Newman metric and field are the bilinear fields
--   $$g_y(v,w)=\sum_{\mu,\nu}g^{KN}_{\mu\nu}(y)\,v^\mu w^\nu,\qquad F_y(v,w)=\sum_{\mu,\nu}F^{KN}_{\mu\nu}(y)\,v^\mu w^\nu .$$
--
--   This is the concrete model used to check that the standing hypotheses of the mission are satisfiable.
--
--   **Formalization Note** The region is a `TopologicalSpace.Opens` of `EuclideanSpace ℝ (Fin 4)`; its openness is proved from the continuity of $r$.
-- source:
--   Wikipedia, "No-hair theorem" (revision oldid=1353599195), https://en.wikipedia.org/w/index.php?title=No-hair_theorem&oldid=1353599195

import Mathlib
import Definitions.Def_NoHair_spacetime

/-!
# No-hair mission: the Kerr–Newman spacetime as a manifold

The region `{r > 0}` of Kerr–Schild coordinate space, with the Kerr–Newman metric and field,
viewed as a spacetime (an open submanifold of `ℝ⁴`).
-/

noncomputable section

open scoped ContDiff Manifold BigOperators
open Set

namespace NoHair

/-- The continuous bilinear form `(v, w) ↦ ∑_{μν} A_{μν} v^μ w^ν` on `ℝ⁴` with matrix `A`. -/
def matrixBilin (A : Matrix (Fin 4) (Fin 4) ℝ) : E4 →L[ℝ] E4 →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (E4 →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (E4 →L[ℝ] ℝ)).toLinearMap ∘ₗ
      ((Matrix.toLinearMap₂' ℝ A).compl₁₂
        (WithLp.linearEquiv 2 ℝ (Fin 4 → ℝ)).toLinearMap
        (WithLp.linearEquiv 2 ℝ (Fin 4 → ℝ)).toLinearMap))

lemma continuous_ksRadius (a : ℝ) : Continuous (ksRadius a) := by
  unfold ksRadius
  fun_prop

/-- The Kerr–Newman spacetime region `{r > 0}` of Kerr–Schild coordinate space (the ring
singularity and the disc `r = 0` removed). -/
def kerrNewmanSpacetime (a : ℝ) : TopologicalSpace.Opens E4 :=
  ⟨{y | 0 < ksRadius a y}, isOpen_lt continuous_const (continuous_ksRadius a)⟩

/-- The Kerr–Newman metric as a bilinear field on `kerrNewmanSpacetime a`. -/
def kerrNewmanMetricField (m a e : ℝ) : BilinField (kerrNewmanSpacetime a) :=
  fun x => matrixBilin (kerrNewmanMetric m a e x)

/-- The Kerr–Newman electromagnetic field as a bilinear field on `kerrNewmanSpacetime a`. -/
def kerrNewmanFieldField (a e : ℝ) : BilinField (kerrNewmanSpacetime a) :=
  fun x => matrixBilin (kerrNewmanField a e x)

end NoHair


