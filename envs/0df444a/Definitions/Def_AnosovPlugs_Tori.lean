-- Prove2me | Definitions.Def_AnosovPlugs_Tori
-- name    : AnosovPlugs_Tori
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-01T02:28:58.106355+00:00
-- url     : https://prove2.me/theorems/99383fbc-cf12-4dd7-a8e6-89cbaff8b1a5
-- title:
--   Anosov plugs VII: embedded tori transverse to a flow, isotopy of tori
-- statement:
--   Let $\mathbb T^2=S^1\times S^1$ with its standard smooth structure and $M$ a 3-manifold.
--
--   1. **Embedded torus**: an injective C¹ immersion $f:\mathbb T^2\to M$ (a C¹ embedding, $\mathbb T^2$ being compact).
--   2. **Transverse torus**: an embedded torus such that the vector field $X$ is nowhere tangent to it: $X(f(p))\notin \operatorname{im} Df_p$.
--   3. **Isotopic tori**: $f_1,f_2$ are isotopic if there is a C¹ family $(F_t)_{t\in[0,1]}$ of embedded tori with $F_0=f_1$ and $F_1(\mathbb T^2)=f_2(\mathbb T^2)$.
--
--   **Formalization Note** Isotopy is between embedded surfaces (images), in the C¹ category.
-- source:
--   F. Béguin, C. Bonatti, B. Yu, *Building Anosov flows on 3-manifolds*, Geom. Topol. 21 (2017) 1837–1930, https://doi.org/10.2140/gt.2017.21.1837, §1.4.5, Theorem 1.15 (p. 1847)

import Mathlib
import Definitions.Def_AnosovPlugs_Flows

/-!
Béguin–Bonatti–Yu, *Building Anosov flows on 3-manifolds*, Geom. Topol. 21 (2017).
Embedded tori transverse to a vector field, and isotopy of embedded tori (§1.4.5).
The torus is `𝕋² = S¹ × S¹` with its standard smooth structure.
-/

open scoped Manifold ContDiff Topology
open Set Function

namespace AnosovPlugs

/-- The model of the torus `S¹ × S¹`. -/
noncomputable abbrev ITorus := (𝓡 1).prod (𝓡 1)

variable {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold I3 ∞ M]

/-- `f : S¹ × S¹ → M` is an embedded torus: an injective C¹ immersion (hence, the torus being
compact, a C¹ embedding). -/
def IsEmbeddedTorus (f : Circle × Circle → M) : Prop :=
  ContMDiff ITorus I3 1 f ∧ Injective f ∧ ∀ p, Injective (mfderiv ITorus I3 f p)

/-- The embedded torus `f` is transverse to the vector field `X`: at every point of the torus,
`X` is not tangent to the torus. -/
def IsTransverseTorus (X : (x : M) → TangentSpace I3 x) (f : Circle × Circle → M) : Prop :=
  IsEmbeddedTorus f ∧ ∀ p, X (f p) ∉ LinearMap.range (mfderiv ITorus I3 f p).toLinearMap

/-- The embedded tori `f₁` and `f₂` are isotopic: there is a C¹ family `(F_t)_{t ∈ [0,1]}` of
embedded tori with `F₀ = f₁` and `F₁` having the same image as `f₂`. -/
def ToriIsotopic (f₁ f₂ : Circle × Circle → M) : Prop :=
  ∃ F : ℝ × (Circle × Circle) → M, ContMDiff (𝓘(ℝ, ℝ).prod ITorus) I3 1 F ∧
    (∀ t ∈ Icc (0 : ℝ) 1, IsEmbeddedTorus fun p => F (t, p)) ∧
    (∀ p, F (0, p) = f₁ p) ∧ range (fun p => F (1, p)) = range f₂

end AnosovPlugs


