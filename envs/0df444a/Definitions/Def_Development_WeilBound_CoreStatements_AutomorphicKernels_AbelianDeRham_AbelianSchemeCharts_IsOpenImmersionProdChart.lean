-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_AbelianDeRham_AbelianSchemeCharts_IsOpenImmersionProdChart
-- name    : Development_WeilBound_CoreStatements_AutomorphicKernels_AbelianDeRham_AbelianSchemeCharts_IsOpenImmersionProdChart
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T22:12:38.431951+00:00
-- url     : https://prove2.me/theorems/3d135662-9e3a-4cfa-bdf5-074edc7cfb17
-- title:
--   Is Open Immersion Prod Chart
-- statement:
--   Definitions and structural lemmas for Is Open Immersion Prod Chart, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/AbelianDeRham/AbelianSchemeCharts/IsOpenImmersionProdChart.lean

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR
attribute [local instance] Over.cartesianMonoidalCategory
namespace MainStatements.Hodge.Sh
variable {R : Type} [CommRing R]
def secMapLE {X Y : Scheme.{0}} {s : X ⟶ Sp R} {t : Y ⟶ Sp R} (f : Y ⟶ X) (hf : f ≫ s = t) {U : X.Opens}
    {W : Y.Opens} (hW : W ≤ f ⁻¹ᵁ U) : Sec s U →ₐ[R] Sec t W :=
  { (f.appLE U W hW).hom with
    commutes' := fun r ↦ by
      subst hf
      exact congrArg (fun q ↦ (CommRingCat.Hom.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ q)) r)
        (Scheme.Hom.appLE_comp_appLE f s ⊤ U W _ hW) }
section SecMap
variable {X Y Z : Scheme.{0}} {s : X ⟶ Sp R} {t : Y ⟶ Sp R} {u : Z ⟶ Sp R}
end SecMap
section Flat
end Flat
section Prod
variable (X Y : Over (Sp R))
abbrev prodW (U : X.left.Opens) (V : Y.left.Opens) : (X ⊗ Y).left.Opens :=
  (fst X Y).left ⁻¹ᵁ U ⊓ (snd X Y).left ⁻¹ᵁ V
section Chart
variable (U : X.left.affineOpens) (V : Y.left.affineOpens)
def prodChart : Spec (CommRingCat.of (Sec X.hom U.1 ⊗[R] Sec Y.hom V.1)) ⟶ (X ⊗ Y).left :=
  (pullbackSpecIso R (Sec X.hom U.1) (Sec Y.hom V.1)).inv ≫
    Limits.pullback.map (spMap (algebraMap R (Sec X.hom U.1))) (spMap (algebraMap R (Sec Y.hom V.1))) X.hom Y.hom
      (affPt X.hom U) (affPt Y.hom V) (𝟙 _) (by rw [Category.comp_id, affPt_w])
      (by rw [Category.comp_id, affPt_w])
instance isOpenImmersion_prodChart : IsOpenImmersion (prodChart X Y U V) := by
  have : IsOpenImmersion (affPt X.hom U) := U.2.isOpenImmersion_fromSpec
  have : IsOpenImmersion (affPt Y.hom V) := V.2.isOpenImmersion_fromSpec
  unfold prodChart
  infer_instance
theorem opensRange_prodChart : (prodChart X Y U V).opensRange = prodW X Y U.1 V.1 := by
  have : IsOpenImmersion (affPt X.hom U) := U.2.isOpenImmersion_fromSpec
  have : IsOpenImmersion (affPt Y.hom V) := V.2.isOpenImmersion_fromSpec
  unfold prodChart
  rw [Scheme.Hom.opensRange_comp_of_isIso]
  refine TopologicalSpace.Opens.ext ((Scheme.Pullback.range_map _ _ _ _ _ _ _ _ _).trans ?_)
  rw [show Set.range (affPt X.hom U) = U.1 from U.2.range_fromSpec,
    show Set.range (affPt Y.hom V) = V.1 from V.2.range_fromSpec]
  rfl
theorem prodChart_preimage : prodChart X Y U V ⁻¹ᵁ prodW X Y U.1 V.1 = ⊤ := by
  rw [← opensRange_prodChart, Scheme.Hom.preimage_opensRange]
def prodInv : Sec (X ⊗ Y).hom (prodW X Y U.1 V.1) →+* Sec X.hom U.1 ⊗[R] Sec Y.hom V.1 :=
  ((prodChart X Y U V).appLE (prodW X Y U.1 V.1) ⊤ (prodChart_preimage X Y U V).ge ≫
    (Scheme.ΓSpecIso _).hom).hom
end Chart
theorem isAffineOpen_prodW (U : X.left.affineOpens) (V : Y.left.affineOpens) : IsAffineOpen (prodW X Y U.1 V.1) := by
  rw [← opensRange_prodChart]
  exact isAffineOpen_opensRange _
def prodAff (U : X.left.affineOpens) (V : Y.left.affineOpens) : (X ⊗ Y).left.affineOpens :=
  ⟨prodW X Y U.1 V.1, isAffineOpen_prodW X Y U V⟩
def prodSecMap (U : X.left.Opens) (V : Y.left.Opens) :
    Sec X.hom U ⊗[R] Sec Y.hom V →ₐ[R] Sec (X ⊗ Y).hom (prodW X Y U V) :=
  Algebra.TensorProduct.lift (secMapLE (fst X Y).left (Over.w _) inf_le_left)
    (secMapLE (snd X Y).left (Over.w _) inf_le_right) fun _ _ ↦ Commute.all _ _
section Inv
variable (U : X.left.affineOpens) (V : Y.left.affineOpens)
end Inv
end Prod
end MainStatements.Hodge.Sh


