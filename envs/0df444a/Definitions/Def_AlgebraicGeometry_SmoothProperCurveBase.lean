-- Prove2me | Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
-- name    : AlgebraicGeometry_SmoothProperCurveBase
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/94b3d398-e0d0-5a77-a5de-ebfc2b03a98a
-- title:
--   Base change and fibre instances for smooth proper curves
-- statement:
--   This module collects infrastructure for a scheme $C$ over an affine base, given by a structure morphism $c : C \to \operatorname{Spec} R$ with $R$ a commutative ring, under the standing Mathlib classes `IsProper`, `SmoothOfRelativeDimension 1` and `GeometricallyIntegral`. No new predicate is introduced. First, instances are registered which let Lean propagate `SmoothOfRelativeDimension n` automatically: a morphism smooth of relative dimension $1$ is smooth; smoothness of relative dimension $n$ is inherited by both pullback projections `pullback.snd f g` and `pullback.fst f g` from the corresponding factor (via stability of the property under base change); and it is inherited by the fibre morphism `f.fiberToSpecResidueField s` over a point $s$ of the base, which is a base change of $f$ along the inclusion of the residue field. The analogous instance for `IsProper` of `f.fiberToSpecResidueField s` is also supplied.
--
--   Second, a fixed spelling for base change along a ring map is provided: for an $R$-algebra $T$, `specMap R T` is $\operatorname{Spec}$ of the structure map $R \to T$, and `baseChange R c T` is the second projection $C \times_{\operatorname{Spec} R} \operatorname{Spec} T \to \operatorname{Spec} T$; properness, smoothness of relative dimension $1$ and geometric integrality transfer to it by instance resolution. A section of $c$ is recorded as an element of `SchemeHomOver (𝟙 _) c`, i.e. a morphism $\varepsilon : \operatorname{Spec} R \to C$ together with a proof that $\varepsilon$ followed by $c$ is the identity; `sectionBaseChange T ε` is the induced section of `baseChange R c T`, characterised by the two stated equations for its composites with the two pullback projections. Finally, for any morphism $\xi : \operatorname{Spec} K \to \operatorname{Spec} R$ with $K$ a field, geometric integrality of $c$ yields the instance `IsIntegral (pullback c ξ)`: every field-valued fibre is an integral scheme, hence an integral smooth proper curve over that field.
--
--   **Relation to Mathlib.** All notions used here (`SmoothOfRelativeDimension`, `IsProper`, `GeometricallyIntegral`, `Scheme.fiberToSpecResidueField`) are Mathlib's; the module only registers instances and abbreviations for base change along $R \to T$, together with the base change of a section, where `SchemeHomOver` is the project's subtype of morphisms over a fixed morphism.
--
--   **Where it is used.** This infrastructure supports the treatment of modular curves and elliptic curves as smooth proper curves over an affine base, where fibres over field-valued points and base change along ring maps are constantly needed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_SmoothProperCurveBase.lean

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Fiber
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits NeronModelInfra

universe u

namespace AlgebraicGeometry

instance SmoothOfRelativeDimension.smooth_one {X S : Scheme.{u}} (f : X ⟶ S)
    [SmoothOfRelativeDimension 1 f] : Smooth f :=
  SmoothOfRelativeDimension.smooth 1 f

instance SmoothOfRelativeDimension.pullback_snd (n : ℕ) {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [SmoothOfRelativeDimension n f] : SmoothOfRelativeDimension n (pullback.snd f g) :=
  have := smoothOfRelativeDimension_isStableUnderBaseChange n
  MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension n) f g inferInstance

instance SmoothOfRelativeDimension.pullback_fst (n : ℕ) {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [SmoothOfRelativeDimension n g] : SmoothOfRelativeDimension n (pullback.fst f g) :=
  have := smoothOfRelativeDimension_isStableUnderBaseChange n
  MorphismProperty.pullback_fst (P := @SmoothOfRelativeDimension n) f g inferInstance

instance SmoothOfRelativeDimension.fiberToSpecResidueField (n : ℕ) {X S : Scheme.{u}} (f : X ⟶ S)
    [SmoothOfRelativeDimension n f] (s : S) : SmoothOfRelativeDimension n (f.fiberToSpecResidueField s) :=
  have := smoothOfRelativeDimension_isStableUnderBaseChange n
  MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension n) _ _ inferInstance

instance IsProper.fiberToSpecResidueField {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] (s : S) :
    IsProper (f.fiberToSpecResidueField s) :=
  MorphismProperty.pullback_snd (P := @IsProper) _ _ inferInstance

namespace SmoothProperCurve

variable (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R))

section BaseChange

variable (T : Type u) [CommRing T] [Algebra R T]

abbrev specMap : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R T))

abbrev baseChange : pullback c (specMap R T) ⟶ Spec (CommRingCat.of T) :=
  pullback.snd c (specMap R T)

example [SmoothOfRelativeDimension 1 c] : SmoothOfRelativeDimension 1 (baseChange R c T) :=
  inferInstance
example [IsProper c] : IsProper (baseChange R c T) := inferInstance
example [GeometricallyIntegral c] : GeometricallyIntegral (baseChange R c T) := inferInstance

variable {R c}

def sectionBaseChange (ε : SchemeHomOver (𝟙 _) c) : SchemeHomOver (𝟙 _) (baseChange R c T) :=
  ⟨pullback.lift (specMap R T ≫ ε.1) (𝟙 _) (by rw [Category.assoc, ε.2]; simp),
    pullback.lift_snd _ _ _⟩

@[simp]
theorem sectionBaseChange_coe_fst (ε : SchemeHomOver (𝟙 _) c) :
    (sectionBaseChange T ε).1 ≫ pullback.fst c (specMap R T) = specMap R T ≫ ε.1 :=
  pullback.lift_fst _ _ _

@[simp]
theorem sectionBaseChange_coe_snd (ε : SchemeHomOver (𝟙 _) c) :
    (sectionBaseChange T ε).1 ≫ pullback.snd c (specMap R T) = 𝟙 _ :=
  pullback.lift_snd _ _ _

end BaseChange

instance isIntegral_pullback_Spec_field [GeometricallyIntegral c] {K : Type u} [Field K]
    (ξ : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)) : IsIntegral (pullback c ξ) :=
  GeometricallyIntegral.geometrically_isIntegral _ _ _ (.of_hasPullback c ξ)

example [GeometricallyIntegral c] (K : Type u) [Field K] [Algebra R K] :
    IsIntegral (pullback c (specMap R K)) := inferInstance

end SmoothProperCurve

end AlgebraicGeometry

end


