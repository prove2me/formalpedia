-- Prove2me | Definitions.Def_MazurTransfer_OriginalDivisorPresentationTransportDataExplicitSectionSpaces20261017
-- name    : MazurTransfer_OriginalDivisorPresentationTransportDataExplicitSectionSpaces20261017
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T13:52:37.706354+00:00
-- url     : https://prove2.me/theorems/4d33748c-8207-4b87-84e1-83f65c834545
-- title:
--   The original divisor-presentation predicate and its transport along line-bundle isomorphisms
-- statement:
--   For an integral scheme $X$ over a field $K$, a divisor presentation of a line bundle consists of its additive section maps into $K(X)$, their restriction and scalar compatibilities, injectivity, and the exact range prescribed by the divisor on every nonempty affine open. The original presentation predicate and its four fields are retained. An isomorphism of line bundles transports a presentation by composition on sections. This library supplies the interface for arithmetic Picard pullback naturality.
-- source:
--   Original complete IsPresentation structure, constructor, four projections, app_map_of_hom and IsPresentation.of_iso from official Anthropic FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0. The original mathematical declaration texts and transport proof bodies are unchanged. All eight full original closed types are kernel-compared; there are no data-valued definitions among these selected declarations. Original public definition imports replace the broader proof-module imports. Named downstream consumer: CurveIsoDivisorPresentationFieldAction.presentation_pullback and then actual arithmetic Picard curve-pullback naturality. The original native proof provider remains immutable and its duplicate declaration boundary must be reconciled explicitly for later native consumers.

/-
Original full Anthropic FLT declarations, Apache-2.0, pin
6e837e75355538c7f80bab5b956861e86c4eacc2.
Design boundary: the original divisor presentation predicate, its four fields,
and transport along a line-bundle isomorphism. No divisor existence is assumed.
Named downstream consumer: CurveIsoDivisorPresentationFieldAction.presentation_pullback,
then the actual arithmetic Picard curve-pullback naturality theorem.
Original complete selected declaration texts and proof bodies are retained.
-/
import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_PlacesOf
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_SheafOfModules_Monoidal
noncomputable section
universe u v
namespace P2MW.S_AlgebraicCurve_CurveModel_exists_divisorClassMap.DivisorClassMapGlue
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicCurve
section Presentation

variable {K : Type u} [Field K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K)) [IsIntegral X]

structure IsPresentation (L : X.Modules)
    (D : letI := (baseToFunctionField x).toAlgebra
      Divisor K X.functionField)
    (φ : ∀ U : X.Opens, Γ(L, U) →+ (X.functionField : Type u)) : Prop where
  nat : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
    ∀ m : Γ(L, U), φ V (L.presheaf.map (homOfLE h).op m) = φ U m
  smul : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(L, U)),
    φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m
  inj : ∀ U : X.Opens, Nonempty U → Function.Injective (φ U)
  range : letI := (baseToFunctionField x).toAlgebra
    ∀ U : X.Opens, IsAffineOpen U → Nonempty U →
      Set.range (φ U) = (lSpaceOn (placesOf x U) D : Set X.functionField)

variable {x}

omit [IsIntegral X] in

theorem app_map_of_hom {L L' : X.Modules} (f : L ⟶ L') {U V : X.Opens} (i : V ≤ U) (m : Γ(L, U)) :
    (Scheme.Modules.Hom.app f V) (L.presheaf.map (homOfLE i).op m) =
      L'.presheaf.map (homOfLE i).op ((Scheme.Modules.Hom.app f U) m) := by
  have hn := (Scheme.Modules.Hom.mapPresheaf f).naturality (homOfLE i).op
  have hm := ConcreteCategory.congr_hom hn m
  simpa only [Scheme.Modules.mapPresheaf_app, ConcreteCategory.comp_apply] using hm


theorem IsPresentation.of_iso {L L' : X.Modules} (e : L ≅ L')
    {D : letI := (baseToFunctionField x).toAlgebra
      Divisor K X.functionField}
    {φ' : ∀ U : X.Opens, Γ(L', U) →+ (X.functionField : Type u)} (h : IsPresentation x L' D φ') :
    IsPresentation x L D (fun U => (φ' U).comp (Scheme.Modules.Hom.app e.hom U).hom) := by
  refine ⟨fun U V hVU hV m => ?_, fun U _ a m => ?_, fun U hU => ?_, fun U hU hne => ?_⟩
  · show φ' V ((Scheme.Modules.Hom.app e.hom V) (L.presheaf.map (homOfLE hVU).op m)) =
      φ' U ((Scheme.Modules.Hom.app e.hom U) m)
    rw [app_map_of_hom e.hom hVU m]
    exact h.nat U V hVU hV _
  · show φ' U ((Scheme.Modules.Hom.app e.hom U) (a • m)) =
      algebraMap Γ(X, U) X.functionField a * φ' U ((Scheme.Modules.Hom.app e.hom U) m)
    rw [Scheme.Modules.Hom.app_smul]
    exact h.smul U a _
  · exact (h.inj U hU).comp (ConcreteCategory.bijective_of_isIso (Scheme.Modules.Hom.app e.hom U)).1
  · letI := (baseToFunctionField x).toAlgebra
    have hs : Function.Surjective (Scheme.Modules.Hom.app e.hom U) :=
      (ConcreteCategory.bijective_of_isIso (Scheme.Modules.Hom.app e.hom U)).2
    show Set.range (φ' U ∘ (Scheme.Modules.Hom.app e.hom U)) = _
    rw [hs.range_comp]
    exact h.range U hU hne

end Presentation
end P2MW.S_AlgebraicCurve_CurveModel_exists_divisorClassMap.DivisorClassMapGlue
#print axioms P2MW.S_AlgebraicCurve_CurveModel_exists_divisorClassMap.DivisorClassMapGlue.IsPresentation
#print axioms P2MW.S_AlgebraicCurve_CurveModel_exists_divisorClassMap.DivisorClassMapGlue.IsPresentation.of_iso


