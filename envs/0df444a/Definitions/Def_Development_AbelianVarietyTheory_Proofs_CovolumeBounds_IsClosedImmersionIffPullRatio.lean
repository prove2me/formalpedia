-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IsClosedImmersionIffPullRatio
-- name    : Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IsClosedImmersionIffPullRatio
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T21:15:38.459807+00:00
-- url     : https://prove2.me/theorems/14fd33b4-c616-43b0-8a6a-845c00ae6a22
-- title:
--   Is Closed Immersion Iff Pull Ratio
-- statement:
--   Definitions and structural lemmas for Is Closed Immersion Iff Pull Ratio, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/IsClosedImmersionIffPullRatio.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TwistingSheafOneChartEqPreimageStandardChart
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Theorems.Thm_GlobalTheory_Cartier_IsRegularFn_mul
import Theorems.Thm_GlobalTheory_ProjSpace_aeval_ratio_surjective
import Theorems.Thm_GlobalTheory_ProjSpace_gradedMap_apply
import Theorems.Thm_GlobalTheory_ProjSpace_isAffineOpen_chart
import Theorems.Thm_GlobalTheory_QCoh_Qcqs_appLinearBase_apply
import Theorems.Thm_GlobalTheory_QCoh_Qcqs_baseRingHom_top
import Theorems.Thm_GlobalTheory_QCoh_germLinear_apply
import Theorems.Thm_GlobalTheory_QCoh_resBasicOpen_apply
import Theorems.Thm_GlobalTheory_QCoh_resLinear_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.ProjSpace.gradedMap_apply
attribute [local simp] GlobalTheory.QCoh.Qcqs.appLinearBase_apply
attribute [local simp] GlobalTheory.QCoh.germLinear_apply
attribute [local simp] GlobalTheory.QCoh.resBasicOpen_apply
attribute [local simp] GlobalTheory.QCoh.resLinear_apply


set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace resG)
open GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier
attribute [local instance] MvPolynomial.gradedAlgebra
namespace GlobalTheory.ProjSpace
variable {R : Type} [CommRing R] {N : ℕ} {Y Z : Scheme.{0}}
theorem appLE_of_eq {φ ψ : Z ⟶ Y} (h : φ = ψ) (U : Y.Opens) (V : Z.Opens) (h₁ : V ≤ φ ⁻¹ᵁ U)
    (h₂ : V ≤ ψ ⁻¹ᵁ U) : φ.appLE U V h₁ = ψ.appLE U V h₂ := by
  subst h
  rfl
theorem appLE_resG (g : Z ⟶ Y) {U U' : Y.Opens} {V : Z.Opens} (h' : U' ≤ U) (h : V ≤ g ⁻¹ᵁ U')
    (a : Γ(Y, U)) :
    (g.appLE U' V h).hom (resG Y h' a) = (g.appLE U V (h.trans (g.preimage_mono h'))).hom a :=
  congrArg (fun φ => φ.hom a) (g.map_appLE h (homOfLE h').op)
theorem appLE_appLE {X : Scheme.{0}} (g : Z ⟶ Y) (φ : Y ⟶ X) {U : X.Opens} {V : Y.Opens} {W : Z.Opens}
    (h : V ≤ φ ⁻¹ᵁ U) (h' : W ≤ g ⁻¹ᵁ V) (a : Γ(X, U)) :
    (g.appLE V W h').hom ((φ.appLE U V h).hom a) =
      ((g ≫ φ).appLE U W (h'.trans (g.preimage_mono h))).hom a :=
  congrArg (fun ψ => ψ.hom a) (Scheme.Hom.appLE_comp_appLE g φ U V W h h')
theorem baseRingHom_appLE {B : CommRingCat.{0}} (p : Y ⟶ Spec B) (g : Z ⟶ Y) (U : Y.Opens) (V : Z.Opens)
    (h : V ≤ g ⁻¹ᵁ U) : baseRingHom p U ≫ g.appLE U V h = baseRingHom (g ≫ p) V :=
  (Category.assoc _ _ _).trans
    (congrArg (_ ≫ ·) (Scheme.Hom.appLE_comp_appLE g p ⊤ U V le_top h))
theorem eq_of_baseRingHom_top {B : CommRingCat.{0}} {p q : Y ⟶ Spec B}
    (h : baseRingHom p ⊤ = baseRingHom q ⊤) : p = q := by
  rw [baseRingHom_top, baseRingHom_top, cancel_epi] at h
  exact ext_of_isAffine h
instance isIso_ι_appLE_top (U : Y.Opens) (h : ⊤ ≤ U.ι ⁻¹ᵁ U) : IsIso (U.ι.appLE U ⊤ h) := by
  rw [Scheme.Opens.ι_appLE]
  have e : U.ι ''ᵁ ⊤ = U := by simp
  have : ∀ i : U.ι ''ᵁ ⊤ ⟶ U, IsIso (Y.presheaf.map i.op) := fun i =>
    (Subsingleton.elim i (eqToHom e)) ▸ inferInstance
  exact this _
def pullRatio (φ : Y ⟶ PSpace R N) (W : Y.Opens) (i : Fin (N + 1)) (hi : W ≤ φ ⁻¹ᵁ chart R N i)
    (j : Fin (N + 1)) : Γ(Y, W) :=
  (φ.appLE (chart R N i) W hi).hom (ratio R N i j)
section
variable {φ : Y ⟶ PSpace R N} {W V : Y.Opens} {i j k : Fin (N + 1)} {hi : W ≤ φ ⁻¹ᵁ chart R N i}
  {hj : W ≤ φ ⁻¹ᵁ chart R N j}
@[simp] theorem pullRatio_self : pullRatio φ W i hi i = 1 := by
  rw [pullRatio, ratio, ratioOn_self, map_one]
theorem appLE_ratioOn {U : (PSpace R N).Opens} (hU : U ≤ chart R N i) (hW : W ≤ φ ⁻¹ᵁ U) :
    (φ.appLE U W hW).hom (ratioOn U i hU j) = pullRatio φ W i (hW.trans (φ.preimage_mono hU)) j :=
  appLE_resG φ hU hW (ratio R N i j)
theorem pullRatio_mul_pullRatio :
    pullRatio φ W i hi j * pullRatio φ W j hj k = pullRatio φ W i hi k := by
  have hW : W ≤ φ ⁻¹ᵁ (chart R N i ⊓ chart R N j) := le_inf hi hj
  rw [← appLE_ratioOn inf_le_left hW, ← appLE_ratioOn inf_le_right hW, ← appLE_ratioOn inf_le_left hW,
    ← map_mul, ratioOn_mul_ratioOn]
theorem basicOpen_pullRatio : Y.basicOpen (pullRatio φ W i hi j) = W ⊓ φ ⁻¹ᵁ chart R N j := by
  refine (Scheme.basicOpen_appLE φ W _ hi _).trans ?_
  rw [ratio, basicOpen_ratioOn]
  exact le_antisymm (inf_le_inf_left _ (φ.preimage_mono inf_le_right))
    (le_inf inf_le_left (le_inf (inf_le_left.trans hi) inf_le_right))
theorem appLE_pullRatio (g : Z ⟶ Y) {T : Z.Opens} (h : T ≤ g ⁻¹ᵁ W) :
    (g.appLE W T h).hom (pullRatio φ W i hi j) =
      pullRatio (g ≫ φ) T i (h.trans (g.preimage_mono hi)) j :=
  congrArg (fun ψ => ψ.hom (ratio R N i j)) (Scheme.Hom.appLE_comp_appLE g φ _ _ _ hi h)
theorem appLE_comp_aeval_ratio :
    (φ.appLE (chart R N i) W hi).hom.comp
        (RingHomClass.toRingHom (aeval (R := R) (ratio R N i))) =
      eval₂Hom (baseRingHom (φ ≫ PSpace.str R N) W).hom (pullRatio φ W i hi) := by
  refine ringHom_ext (fun r => ?_) (fun j => ?_)
  · simp only [RingHom.comp_apply, RingHom.coe_coe, algHom_C, eval₂Hom_C]
    exact congrArg (fun ψ => ψ.hom r) (baseRingHom_appLE (PSpace.str R N) φ _ W hi)
  · simp only [RingHom.comp_apply, RingHom.coe_coe, aeval_X, eval₂Hom_X']
    rfl
end
theorem ι_comp_eq (φ : Y ⟶ PSpace R N) (W : Y.Opens) (i : Fin (N + 1)) (hi : W ≤ φ ⁻¹ᵁ chart R N i) :
    W.ι ≫ φ = W.toSpecΓ ≫ Spec.map (φ.appLE (chart R N i) W hi) ≫ (isAffineOpen_chart R N i).fromSpec := by
  rw [Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc, IsAffineOpen.toSpecΓ_fromSpec, Scheme.Hom.resLE_comp_ι]
theorem hom_ext {φ ψ : Y ⟶ PSpace R N} (h : φ ≫ PSpace.str R N = ψ ≫ PSpace.str R N)
    (H : ∀ y : Y, ∃ (W : Y.Opens) (_ : y ∈ W) (i : Fin (N + 1)) (h₁ : W ≤ φ ⁻¹ᵁ chart R N i)
      (h₂ : W ≤ ψ ⁻¹ᵁ chart R N i), ∀ j, pullRatio φ W i h₁ j = pullRatio ψ W i h₂ j) : φ = ψ := by
  refine Scheme.hom_ext_of_forall _ _ fun y => ?_
  obtain ⟨W, hy, i, h₁, h₂, e⟩ := H y
  refine ⟨W, hy, ?_⟩
  have : φ.appLE (chart R N i) W h₁ = ψ.appLE (chart R N i) W h₂ := by
    ext1
    refine RingHom.ext fun a => ?_
    obtain ⟨p, rfl⟩ := aeval_ratio_surjective R N i a
    have e₁ := congrArg (fun t => t p) (appLE_comp_aeval_ratio (φ := φ) (hi := h₁))
    have e₂ := congrArg (fun t => t p) (appLE_comp_aeval_ratio (φ := ψ) (hi := h₂))
    rw [h, funext e] at e₁
    exact e₁.trans e₂.symm
  rw [ι_comp_eq φ W i h₁, ι_comp_eq ψ W i h₂, this]
def ofChartHom (i : Fin (N + 1)) (ρ : Γ(PSpace R N, chart R N i) ⟶ Γ(Y, ⊤)) : Y ⟶ PSpace R N :=
  Y.toSpecΓ ≫ Spec.map ρ ≫ (isAffineOpen_chart R N i).fromSpec
theorem ofChartHom_preimage (i : Fin (N + 1)) (ρ : Γ(PSpace R N, chart R N i) ⟶ Γ(Y, ⊤)) :
    ⊤ ≤ ofChartHom i ρ ⁻¹ᵁ chart R N i := by
  rw [ofChartHom, Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage, IsAffineOpen.fromSpec_preimage_self]
  exact le_rfl
theorem ofChartHom_appLE (i : Fin (N + 1)) (ρ : Γ(PSpace R N, chart R N i) ⟶ Γ(Y, ⊤)) :
    (ofChartHom i ρ).appLE (chart R N i) ⊤ (ofChartHom_preimage i ρ) = ρ := by
  have h1 : (isAffineOpen_chart R N i).fromSpec.appLE (chart R N i) ⊤
      (isAffineOpen_chart R N i).fromSpec_preimage_self.ge = (Scheme.ΓSpecIso _).inv := by
    rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    exact (congrArg _ (CategoryTheory.Functor.map_id _ _)).trans (Category.comp_id _)
  have h2 : (Y.toSpecΓ ≫ Spec.map ρ).appLE ⊤ ⊤ le_rfl = (Scheme.ΓSpecIso _).hom ≫ ρ := by
    refine Eq.trans (Scheme.Hom.app_eq_appLE _).symm ?_
    change (Y.toSpecΓ ≫ Spec.map ρ).appTop = _
    rw [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, Scheme.ΓSpecIso_naturality]
  have h3 := Scheme.Hom.appLE_comp_appLE (Y.toSpecΓ ≫ Spec.map ρ) (isAffineOpen_chart R N i).fromSpec
    (chart R N i) ⊤ ⊤ (isAffineOpen_chart R N i).fromSpec_preimage_self.ge le_rfl
  rw [h1, h2, Iso.inv_hom_id_assoc] at h3
  exact h3.symm
def chartLift {A : Type} [CommRing A] (i : Fin (N + 1)) (c : R →+* A) (r : Fin (N + 1) → A) :
    Γ(PSpace R N, chart R N i) →+* A :=
  (eval₂Hom c fun j : {j // j ≠ i} => r j.1).comp
    (RingHomClass.toRingHom (chartAlgEquiv R N i).symm)
theorem chartLift_algebraMap {A : Type} [CommRing A] (i : Fin (N + 1)) (c : R →+* A) (r : Fin (N + 1) → A)
    (a : R) : chartLift i c r (algebraMap R _ a) = c a := by
  simp only [chartLift, RingHom.comp_apply, RingHom.coe_coe]
  rw [AlgEquiv.commutes]
  exact eval₂Hom_C _ _ a
theorem chartLift_ratio {A : Type} [CommRing A] (i : Fin (N + 1)) (c : R →+* A) {r : Fin (N + 1) → A}
    (hr : r i = 1) (j : Fin (N + 1)) : chartLift i c r (ratio R N i j) = r j := by
  by_cases h : j = i
  · subst h
    rw [ratio, ratioOn_self, map_one, hr]
  · simp only [chartLift, RingHom.comp_apply, RingHom.coe_coe]
    rw [← chartAlgEquiv_X R N i ⟨j, h⟩, AlgEquiv.symm_apply_apply, eval₂Hom_X']
def ofCoords (f : Y ⟶ Sp R) (U : Y.Opens) (i : Fin (N + 1)) (r : Fin (N + 1) → Γ(Y, U)) :
    U.toScheme ⟶ PSpace R N :=
  ofChartHom i (CommRingCat.ofHom (R := Γ(PSpace R N, chart R N i)) (S := Γ(Y, U))
      (chartLift i (baseRingHom f U).hom r) ≫
    U.ι.appLE U ⊤ U.ι_preimage_self.ge)
theorem ofCoords_preimage_top (f : Y ⟶ Sp R) (U : Y.Opens) (i : Fin (N + 1)) (r : Fin (N + 1) → Γ(Y, U)) :
    ⊤ ≤ ofCoords f U i r ⁻¹ᵁ chart R N i := by
  unfold ofCoords
  exact ofChartHom_preimage i _
theorem ofCoords_appLE (f : Y ⟶ Sp R) (U : Y.Opens) (i : Fin (N + 1)) (r : Fin (N + 1) → Γ(Y, U)) :
    (ofCoords f U i r).appLE (chart R N i) ⊤ (ofCoords_preimage_top f U i r) =
      CommRingCat.ofHom (R := Γ(PSpace R N, chart R N i)) (S := Γ(Y, U))
        (chartLift i (baseRingHom f U).hom r) ≫ U.ι.appLE U ⊤ U.ι_preimage_self.ge :=
  ofChartHom_appLE i _
theorem ofCoords_preimage (f : Y ⟶ Sp R) (U : Y.Opens) (i : Fin (N + 1)) (r : Fin (N + 1) → Γ(Y, U))
    (g : Z ⟶ U.toScheme) : ⊤ ≤ (g ≫ ofCoords f U i r) ⁻¹ᵁ chart R N i :=
  le_trans le_top (g.preimage_mono (ofCoords_preimage_top f U i r))
theorem ofCoords_str (f : Y ⟶ Sp R) (U : Y.Opens) (i : Fin (N + 1)) (r : Fin (N + 1) → Γ(Y, U)) :
    ofCoords f U i r ≫ PSpace.str R N = U.ι ≫ f := by
  refine eq_of_baseRingHom_top ?_
  rw [← baseRingHom_appLE _ (ofCoords f U i r) (chart R N i) ⊤ (ofCoords_preimage_top f U i r),
    ← baseRingHom_appLE f U.ι U ⊤ U.ι_preimage_self.ge, ofCoords_appLE, ← Category.assoc]
  congr 1
  ext1
  exact RingHom.ext fun a => chartLift_algebraMap i _ r a
theorem pullRatio_comp_ofCoords (f : Y ⟶ Sp R) (U : Y.Opens) (i : Fin (N + 1))
    {r : Fin (N + 1) → Γ(Y, U)} (hr : r i = 1) (g : Z ⟶ U.toScheme) (T : Z.Opens)
    (h : T ≤ (g ≫ ofCoords f U i r) ⁻¹ᵁ chart R N i) (h' : T ≤ (g ≫ U.ι) ⁻¹ᵁ U) (j : Fin (N + 1)) :
    pullRatio (g ≫ ofCoords f U i r) T i h j = ((g ≫ U.ι).appLE U T h').hom (r j) := by
  have e : pullRatio (ofCoords f U i r) ⊤ i (ofCoords_preimage_top f U i r) j =
      (U.ι.appLE U ⊤ U.ι_preimage_self.ge).hom (r j) :=
    (congrArg (fun ψ => ψ.hom (ratio R N i j)) (ofCoords_appLE f U i r)).trans
      (congrArg (U.ι.appLE U ⊤ U.ι_preimage_self.ge).hom (chartLift_ratio i _ hr j))
  rw [← appLE_pullRatio (hi := ofCoords_preimage_top f U i r) g (le_top : T ≤ g ⁻¹ᵁ ⊤), e]
  exact appLE_appLE g U.ι _ _ _
structure IsCoordFamily (U : Fin (N + 1) → Y.Opens) (r : ∀ i, Fin (N + 1) → Γ(Y, U i)) : Prop where

  cover : ⨆ i, U i = ⊤

  self : ∀ i, r i i = 1

  mul : ∀ i j k, resG Y (inf_le_left : U i ⊓ U j ≤ U i) (r i j) * resG Y inf_le_right (r j k) =
    resG Y inf_le_left (r i k)

  basicOpen_le : ∀ i j, Y.basicOpen (r i j) ≤ U j
namespace IsCoordFamily
variable {U : Fin (N + 1) → Y.Opens} {r : ∀ i, Fin (N + 1) → Γ(Y, U i)} (H : IsCoordFamily U r)
include H
theorem appLE_mul (g : Z ⟶ Y) {T : Z.Opens} {i j : Fin (N + 1)} (hi : T ≤ g ⁻¹ᵁ U i) (hj : T ≤ g ⁻¹ᵁ U j)
    (k : Fin (N + 1)) :
    (g.appLE _ T hi).hom (r i j) * (g.appLE _ T hj).hom (r j k) = (g.appLE _ T hi).hom (r i k) := by
  have hT : T ≤ g ⁻¹ᵁ (U i ⊓ U j) := le_inf hi hj
  have := congrArg (g.appLE (U i ⊓ U j) T hT).hom (H.mul i j k)
  rwa [map_mul, appLE_resG, appLE_resG, appLE_resG] at this
theorem isUnit_appLE (g : Z ⟶ Y) {T : Z.Opens} {i j : Fin (N + 1)} (hi : T ≤ g ⁻¹ᵁ U i)
    (hj : T ≤ g ⁻¹ᵁ U j) : IsUnit ((g.appLE _ T hi).hom (r i j)) :=
  .of_mul_eq_one _ ((H.appLE_mul g hi hj i).trans (by rw [H.self, map_one]))
theorem comp_ofCoords_eq (f : Y ⟶ Sp R) (i j : Fin (N + 1)) (a : Z ⟶ (U i).toScheme)
    (b : Z ⟶ (U j).toScheme) (e : a ≫ (U i).ι = b ≫ (U j).ι) :
    a ≫ ofCoords f (U i) i (r i) = b ≫ ofCoords f (U j) j (r j) := by
  have ha : ⊤ ≤ (a ≫ (U i).ι) ⁻¹ᵁ U i := a.preimage_mono (U i).ι_preimage_self.ge
  have hb : ⊤ ≤ (b ≫ (U j).ι) ⁻¹ᵁ U j := b.preimage_mono (U j).ι_preimage_self.ge
  have hb' : ⊤ ≤ (b ≫ (U j).ι) ⁻¹ᵁ U i := e ▸ ha
  have h₁ : ⊤ ≤ (a ≫ ofCoords f (U i) i (r i)) ⁻¹ᵁ chart R N i := ofCoords_preimage f _ i _ a
  have h₂ : ⊤ ≤ (b ≫ ofCoords f (U j) j (r j)) ⁻¹ᵁ chart R N j := ofCoords_preimage f _ j _ b
  have hu := H.isUnit_appLE (b ≫ (U j).ι) hb hb'
  have e₂ := pullRatio_comp_ofCoords f (U j) j (H.self j) b ⊤ h₂ hb
  have h₃ : ⊤ ≤ (b ≫ ofCoords f (U j) j (r j)) ⁻¹ᵁ chart R N i := by
    have := basicOpen_pullRatio (hi := h₂) (j := i)
    rw [e₂, Z.basicOpen_of_isUnit hu] at this
    exact this.le.trans inf_le_right
  refine hom_ext ?_ fun _ => ⟨⊤, trivial, i, h₁, h₃, fun k => ?_⟩
  · rw [Category.assoc, Category.assoc, ofCoords_str, ofCoords_str, reassoc_of% e]
  · refine hu.mul_left_cancel ?_
    rw [pullRatio_comp_ofCoords f (U i) i (H.self i) a ⊤ h₁ ha, appLE_of_eq e _ _ ha hb',
      H.appLE_mul _ hb hb', ← e₂, ← e₂, pullRatio_mul_pullRatio]
def toHom (f : Y ⟶ Sp R) : Y ⟶ PSpace R N :=
  (Y.openCoverOfIsOpenCover U H.cover).glueMorphisms (fun i => ofCoords f (U i) i (r i))
    fun i j => H.comp_ofCoords_eq f i j _ _ pullback.condition
theorem ι_toHom (f : Y ⟶ Sp R) (i : Fin (N + 1)) : (U i).ι ≫ H.toHom f = ofCoords f (U i) i (r i) :=
  (Y.openCoverOfIsOpenCover U H.cover).ι_glueMorphisms _ _ i
theorem le_toHom_preimage (f : Y ⟶ Sp R) (i : Fin (N + 1)) : U i ≤ H.toHom f ⁻¹ᵁ chart R N i := by
  intro y hy
  have : ⊤ ≤ ((U i).ι ≫ H.toHom f) ⁻¹ᵁ chart R N i := by
    rw [ι_toHom]
    exact ofCoords_preimage_top _ _ _ _
  exact this (Set.mem_univ (⟨y, hy⟩ : U i))
end IsCoordFamily
end GlobalTheory.ProjSpace


