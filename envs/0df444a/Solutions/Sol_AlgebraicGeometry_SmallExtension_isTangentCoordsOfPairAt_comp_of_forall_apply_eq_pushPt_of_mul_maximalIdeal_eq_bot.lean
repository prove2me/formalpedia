-- Prove2me | solution 1 for AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAt_comp_of_forall_apply_eq_pushPt_of_mul_maximalIdeal_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/a7bf88bc-caed-59a8-9a83-d4aa7b33b814

import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAt
import Definitions.Def_Algebra_PointDerivations
import Theorems.Thm_AlgebraicGeometry_SmallExtension_exists_pointDerivations_pushforward_natural_of_forall_apply_eq_pushPt
import Theorems.Thm_AlgebraicGeometry_SmallExtension_pointDerivations_natural_endo_eq_symm_map_tmul_of_apply_eq
import Theorems.Thm_AlgebraicGeometry_isPushout_specMap_of_isPullback_of_surjective_of_isNilpotent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAt_comp_of_forall_apply_eq_pushPt_of_mul_maximalIdeal_eq_bot

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing TensorProduct AlgebraicGeometry.SmallExtension CerednikDrinfeld.QM AlgebraicGeometry.Scheme.TwoAffineOpenCover"

universe u

noncomputable section

namespace ChainRule28

section Plumbing

variable {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)

theorem eq_specMap_appLE_comp_fromSpec {R : CommRingCat.{u}} (p : Spec R ⟶ X) (h : ⊤ ≤ p ⁻¹ᵁ U) :
    p = Spec.map (p.appLE U ⊤ h ≫ (Scheme.ΓSpecIso R).hom) ≫ hU.fromSpec := by
  have := IsAffineOpen.SpecMap_appLE_fromSpec p hU (isAffineOpen_top _) h
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at this
  rw [Spec.map_comp, Category.assoc, this, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
    Category.id_comp]

theorem specMap_comp_fromSpec_injective {R : CommRingCat.{u}} (θ θ' : Γ(X, U) ⟶ R)
    (h : Spec.map θ ≫ hU.fromSpec = Spec.map θ' ≫ hU.fromSpec) : θ = θ' := by
  apply Spec.map_injective
  rw [← IsAffineOpen.isoSpec_inv_ι] at h
  have h' : (Spec.map θ ≫ hU.isoSpec.inv) ≫ U.ι = (Spec.map θ' ≫ hU.isoSpec.inv) ≫ U.ι := by
    simpa only [Category.assoc] using h
  exact (cancel_mono hU.isoSpec.inv).1 ((cancel_mono U.ι).1 h')

theorem comp_ι_eq_specMap (R : Type u) [CommRing R] (p : Spec (CommRingCat.of R) ⟶ (U : Scheme.{u})) :
    p ≫ U.ι = Spec.map (CommRingCat.ofHom (U.topIso.inv ≫ p.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom) ≫
      hU.fromSpec := by
  have hι : ⊤ ≤ (p ≫ U.ι) ⁻¹ᵁ U := by
    rw [Scheme.Hom.comp_preimage, Scheme.Opens.ι_preimage_self]
    exact le_top
  have hePι := eq_specMap_appLE_comp_fromSpec hU (p ≫ U.ι) hι
  have happ : (p ≫ U.ι).appLE U ⊤ hι = U.topIso.inv ≫ p.appTop := by
    rw [← Scheme.Hom.appLE_comp_appLE p U.ι U ⊤ ⊤ (by rw [Scheme.Opens.ι_preimage_self]) le_top]
    congr 1
    simp only [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
    rfl
  have hev_hom : CommRingCat.ofHom (U.topIso.inv ≫ p.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom =
      (p ≫ U.ι).appLE U ⊤ hι ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom := by
    rw [happ, Category.assoc]; rfl
  rw [hev_hom]; exact hePι

end Plumbing

section Translate

variable {k : Type u} [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k x)
  (V : Type u) [AddCommGroup V] [Module k V] [Module kᵐᵒᵖ V] [IsCentralScalar k V]
  {Z₀ Z : Scheme.{u}} (f₀ : Z₀ ⟶ Spec (CommRingCat.of k))
  (q₁ : Z ⟶ Z₀) (q₂ : Z ⟶ SquareZero.spec k V) (hZ : IsPullback q₁ q₂ f₀ (SquareZero.toBase k V))
  (ψ : X ⟶ X) (hψ : ψ ≫ x = x)
  (hψhom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t x),
      pushPt ψ hψ (L.mul t P Q) = L.mul t (pushPt ψ hψ P) (pushPt ψ hψ Q))

include hψhom in
theorem pushPt_one {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) : pushPt ψ hψ (L.one t) = L.one t := by
  letI := L.pointGroup t
  have h := hψhom t (L.one t) (L.one t)
  rw [L.one_mul] at h
  change pushPt ψ hψ (L.one t) = pushPt ψ hψ (L.one t) * pushPt ψ hψ (L.one t) at h
  exact (mul_left_cancel (h.symm.trans (mul_one _).symm))

include hψhom in
theorem pushPt_inv {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t x) :
    pushPt ψ hψ (L.inv t P) = L.inv t (pushPt ψ hψ P) := by
  letI := L.pointGroup t
  have h := hψhom t (L.inv t P) P
  rw [L.inv_mul_cancel, pushPt_one x L ψ hψ hψhom] at h
  change (1 : SchemeHomOver t x) = pushPt ψ hψ (L.inv t P) * pushPt ψ hψ P at h
  exact eq_inv_of_mul_eq_one_left h.symm

include hψhom in

theorem translate_comp (w₀ : Z ⟶ X) (hw₀ : w₀ ≫ x = RelTangentPoints.base V q₂) :
    (RelTangentPoints.translate x L V f₀ q₁ q₂ hZ (w₀ ≫ ψ) (by rw [Category.assoc, hψ, hw₀])).1 =
      (RelTangentPoints.translate x L V f₀ q₁ q₂ hZ w₀ hw₀).1 ≫ ψ := by
  rw [RelTangentPoints.translate_coe, RelTangentPoints.translate_coe]
  have hA : (⟨q₁ ≫ SquareZero.zeroSection V f₀ q₁ q₂ hZ ≫ w₀ ≫ ψ, by
        rw [Category.assoc, Category.assoc, Category.assoc, hψ, hw₀, ← Category.assoc]
        exact RelTangentPoints.fst_zeroSection_base V f₀ q₁ q₂ hZ⟩ : SchemeHomOver (RelTangentPoints.base V q₂) x) =
      pushPt ψ hψ ⟨q₁ ≫ SquareZero.zeroSection V f₀ q₁ q₂ hZ ≫ w₀, by
        rw [Category.assoc, Category.assoc, hw₀, ← Category.assoc]
        exact RelTangentPoints.fst_zeroSection_base V f₀ q₁ q₂ hZ⟩ :=
    Subtype.ext (by simp only [pushPt, mapPt_coe, Category.assoc])
  have hW : (⟨w₀ ≫ ψ, by rw [Category.assoc, hψ, hw₀]⟩ : SchemeHomOver (RelTangentPoints.base V q₂) x) =
      pushPt ψ hψ ⟨w₀, hw₀⟩ := Subtype.ext rfl
  have := congrArg Subtype.val
    (hψhom (RelTangentPoints.base V q₂)
      (L.inv _ ⟨q₁ ≫ SquareZero.zeroSection V f₀ q₁ q₂ hZ ≫ w₀, by
        rw [Category.assoc, Category.assoc, hw₀, ← Category.assoc]
        exact RelTangentPoints.fst_zeroSection_base V f₀ q₁ q₂ hZ⟩)
      ⟨w₀, hw₀⟩)
  rw [pushPt_inv x L ψ hψ hψhom] at this
  rw [← hA, ← hW] at this
  rw [← this]
  rfl

end Translate

end ChainRule28

end

noncomputable section

namespace ChainRule28

section Chart

variable {T' : Type u} [CommRing T'] [IsLocalRing T']
  (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
  [IsCentralScalar (ResidueField T') V]
  (C : Type u) [CommRing C] [Algebra T' C]

def canMop (K : Type u) [Field K] (M : Type u) [AddCommGroup M] [Module K M] : Module Kᵐᵒᵖ M :=
  Module.compHom M (RingEquiv.toOpposite K).symm.toRingHom

theorem canCentral (K : Type u) [Field K] (M : Type u) [AddCommGroup M] [Module K M] :
    letI := canMop K M; IsCentralScalar K M := by
  letI := canMop K M
  exact ⟨fun r m => rfl⟩

def toE : (ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] V →ₗ[ResidueField T'] thickening T' V C :=
  TensorProduct.map LinearMap.id (TrivSqZeroExt.inrHom (ResidueField T') V)

theorem toE_tmul (xx : ResidueField T' ⊗[T'] C) (v : V) : toE V C (xx ⊗ₜ v) = xx ⊗ₜ TrivSqZeroExt.inr v := rfl

def sc (c : ResidueField T') : thickening T' V C :=
  algebraMap (ResidueField T') (ResidueField T' ⊗[T'] C) c ⊗ₜ (1 : TrivSqZeroExt (ResidueField T') V)

theorem sc_def (c : ResidueField T') :
    sc V C c = algebraMap (ResidueField T') (ResidueField T' ⊗[T'] C) c ⊗ₜ (1 : TrivSqZeroExt (ResidueField T') V) := rfl

theorem toE_mul_toE (s t : (ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] V) : toE V C s * toE V C t = 0 := by
  induction s using TensorProduct.induction_on with
  | zero => rw [map_zero]; ring
  | tmul xx v =>
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero]; ring
    | tmul yy w =>
      rw [toE_tmul, toE_tmul, Algebra.TensorProduct.tmul_mul_tmul, TrivSqZeroExt.inr_mul_inr, TensorProduct.tmul_zero]
    | add a b ha hb => rw [map_add]; linear_combination ha + hb
  | add a b ha hb => rw [map_add]; linear_combination ha + hb

theorem sc_mul_toE (c : ResidueField T') (t : (ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] V) :
    sc V C c * toE V C t = toE V C (c • t) := by
  induction t using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero]; ring
  | tmul yy w =>
    rw [toE_tmul, sc_def, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← Algebra.smul_def,
      TensorProduct.smul_tmul']
    exact (toE_tmul V C _ _).symm
  | add a b ha hb => rw [map_add, smul_add, map_add]; linear_combination ha + hb

theorem toE_mul_sc (c : ResidueField T') (t : (ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] V) :
    toE V C t * sc V C c = toE V C (c • t) := by
  linear_combination sc_mul_toE V C c t

theorem sc_mul_sc (c d : ResidueField T') : sc V C c * sc V C d = sc V C (c * d) := by
  rw [sc_def, sc_def, sc_def, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← map_mul]

theorem sc_one : sc V C (1 : ResidueField T') = 1 := by
  rw [sc_def, map_one]; rfl

theorem sc_zero : sc V C (0 : ResidueField T') = 0 := by
  rw [sc_def, map_zero, TensorProduct.zero_tmul]

theorem sc_add (c d : ResidueField T') : sc V C (c + d) = sc V C c + sc V C d := by
  rw [sc_def, sc_def, sc_def, map_add, TensorProduct.add_tmul]

theorem vPart_toE (t : (ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] V) : vPart T' V C (toE V C t) = t := by
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul xx v =>
    rw [toE_tmul, vPart, TensorProduct.map_tmul, LinearMap.id_apply]
    rfl
  | add a b ha hb => rw [map_add, map_add, ha, hb]

theorem vPart_sc (c : ResidueField T') : vPart T' V C (sc V C c) = 0 := by
  rw [sc_def, vPart, TensorProduct.map_tmul, LinearMap.id_apply]
  change _ ⊗ₜ (1 : TrivSqZeroExt (ResidueField T') V).snd = 0
  rw [TrivSqZeroExt.snd_one, TensorProduct.tmul_zero]

theorem ofId_eq_sc (c : ResidueField T') : Algebra.ofId (ResidueField T') (thickening T' V C) c = sc V C c := by
  rw [Algebra.ofId_apply, Algebra.TensorProduct.algebraMap_apply]; rfl

theorem smulCommClass_canMop (M : Type u) [AddCommGroup M] [Module (ResidueField T') M] :
    letI := canMop (ResidueField T') M; SMulCommClass (ResidueField T') (ResidueField T')ᵐᵒᵖ M := by
  letI := canMop (ResidueField T') M
  exact ⟨fun c d m => smul_comm c (MulOpposite.unop d) m⟩

theorem isScalarTower_canMop (M : Type u) [AddCommGroup M] [Module (ResidueField T') M] :
    letI := canMop (ResidueField T') M; IsScalarTower (ResidueField T') (ResidueField T')ᵐᵒᵖ M := by
  letI := canMop (ResidueField T') M
  exact ⟨fun c d m => mul_smul c (MulOpposite.unop d) m⟩

def jAlg : letI := canMop (ResidueField T') ((ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] V)
    letI := smulCommClass_canMop (T' := T') ((ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] V)
    letI := isScalarTower_canMop (T' := T') ((ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] V)
    TrivSqZeroExt (ResidueField T') ((ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] V) →ₐ[ResidueField T'] thickening T' V C :=
  letI := canMop (ResidueField T') ((ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] V)
  letI := canCentral (ResidueField T') ((ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] V)
  letI := smulCommClass_canMop (T' := T') ((ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] V)
  letI := isScalarTower_canMop (T' := T') ((ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] V)
  TrivSqZeroExt.lift (Algebra.ofId (ResidueField T') (thickening T' V C)) (toE V C) (toE_mul_toE V C)
    (fun r x => by rw [ofId_eq_sc, sc_mul_toE])
    (fun r x => by rw [ofId_eq_sc, toE_mul_sc, op_smul_eq_smul])

def jHom : letI := canMop (ResidueField T') ((ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] V)
    TrivSqZeroExt (ResidueField T') ((ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] V) →+* thickening T' V C :=
  letI := canMop (ResidueField T') ((ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] V)
  letI := smulCommClass_canMop (T' := T') ((ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] V)
  letI := isScalarTower_canMop (T' := T') ((ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] V)
  (jAlg V C).toRingHom

theorem jHom_apply' (z : letI := canMop (ResidueField T') ((ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] V)
    TrivSqZeroExt (ResidueField T') ((ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] V)) :
    letI := canMop (ResidueField T') ((ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] V)
    jHom V C z = sc V C z.fst + toE V C z.snd := by
  letI := canMop (ResidueField T') ((ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] V)
  letI := canCentral (ResidueField T') ((ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] V)
  letI := smulCommClass_canMop (T' := T') ((ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] V)
  letI := isScalarTower_canMop (T' := T') ((ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] V)
  rw [← ofId_eq_sc V C z.fst]
  exact TrivSqZeroExt.lift_def _ _ _ _ _ z

theorem vPart_jHom (z : letI := canMop (ResidueField T') ((ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] V)
    TrivSqZeroExt (ResidueField T') ((ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] V)) :
    letI := canMop (ResidueField T') ((ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] V)
    vPart T' V C (jHom V C z) = z.snd := by
  rw [jHom_apply', map_add, vPart_sc, vPart_toE, zero_add]

def mHom : thickening T' V C →ₐ[ResidueField T'] ResidueField T' ⊗[T'] C :=
  Algebra.TensorProduct.lift (AlgHom.id (ResidueField T') (ResidueField T' ⊗[T'] C))
    ((Algebra.ofId (ResidueField T') (ResidueField T' ⊗[T'] C)).comp
      (TrivSqZeroExt.fstHom (ResidueField T') (ResidueField T') V))
    (fun _ _ => Commute.all _ _)

theorem mHom_tmul (xx : ResidueField T' ⊗[T'] C) (t : TrivSqZeroExt (ResidueField T') V) :
    mHom V C (xx ⊗ₜ t) = t.fst • xx := by
  rw [mHom, Algebra.TensorProduct.lift_tmul, AlgHom.id_apply, AlgHom.comp_apply, Algebra.ofId_apply, Algebra.smul_def]
  exact (Algebra.commutes _ _).symm

theorem smul_one_eq_inl (c : ResidueField T') : c • (1 : TrivSqZeroExt (ResidueField T') V) = TrivSqZeroExt.inl c := by
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [TrivSqZeroExt.fst_smul, TrivSqZeroExt.fst_one, TrivSqZeroExt.fst_inl, smul_eq_mul, mul_one]
  · rw [TrivSqZeroExt.snd_smul, TrivSqZeroExt.snd_one, TrivSqZeroExt.snd_inl, smul_zero]

theorem decomp (e : thickening T' V C) :
    e = mHom V C e ⊗ₜ (1 : TrivSqZeroExt (ResidueField T') V) + toE V C (vPart T' V C e) := by
  induction e using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, TensorProduct.zero_tmul, add_zero]
  | tmul xx t =>
    rw [mHom_tmul, vPart, TensorProduct.map_tmul, LinearMap.id_apply, TensorProduct.smul_tmul, smul_one_eq_inl]
    change xx ⊗ₜ t = xx ⊗ₜ TrivSqZeroExt.inl t.fst + toE V C (xx ⊗ₜ t.snd)
    rw [toE_tmul, ← TensorProduct.tmul_add, TrivSqZeroExt.inl_fst_add_inr_snd_eq]
  | add a b ha hb =>
    conv_lhs => rw [ha, hb]
    rw [map_add, map_add, map_add, TensorProduct.add_tmul]
    abel

theorem eq_jHom_of_mHom_eq (e : thickening T' V C) (c : ResidueField T')
    (h : mHom V C e = algebraMap (ResidueField T') (ResidueField T' ⊗[T'] C) c) :
    letI := canMop (ResidueField T') ((ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] V)
    e = jHom V C (TrivSqZeroExt.inl c + TrivSqZeroExt.inr (vPart T' V C e)) := by
  letI := canMop (ResidueField T') ((ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] V)
  rw [jHom_apply']
  change e = sc V C (c + 0) + toE V C (0 + vPart T' V C e)
  rw [add_zero, zero_add, sc_def, ← h]
  exact decomp V C e

end Chart

end ChainRule28

end

noncomputable section

set_option synthInstance.maxHeartbeats 800000

namespace ChainRule28

section SpecSide

variable {T' : Type u} [CommRing T'] [IsLocalRing T']
  (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
  [IsCentralScalar (ResidueField T') V] [Module T' V] [IsScalarTower T' (ResidueField T') V]
  (C : Type u) [CommRing C] [Algebra T' C]

theorem vPart_tmul_one (y : ResidueField T' ⊗[T'] C) : vPart T' V C (y ⊗ₜ (1 : TrivSqZeroExt (ResidueField T') V)) = 0 := by
  rw [vPart, TensorProduct.map_tmul, LinearMap.id_apply]
  change y ⊗ₜ (1 : TrivSqZeroExt (ResidueField T') V).snd = 0
  rw [TrivSqZeroExt.snd_one, TensorProduct.tmul_zero]

theorem vPart_sc_mul (c : ResidueField T') (e : thickening T' V C) :
    vPart T' V C (sc V C c * e) = c • vPart T' V C e := by
  have key2 : sc V C c * (mHom V C e ⊗ₜ (1 : TrivSqZeroExt (ResidueField T') V)) =
      (algebraMap (ResidueField T') (ResidueField T' ⊗[T'] C) c * mHom V C e) ⊗ₜ (1 : TrivSqZeroExt (ResidueField T') V) := by
    rw [sc_def, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  have h : sc V C c * e = (algebraMap (ResidueField T') (ResidueField T' ⊗[T'] C) c * mHom V C e) ⊗ₜ (1 : TrivSqZeroExt (ResidueField T') V) +
      toE V C (c • vPart T' V C e) := by
    have hd := decomp V C e
    linear_combination (sc V C c) * hd + key2 + sc_mul_toE V C c (vPart T' V C e)
  rw [h, map_add, vPart_tmul_one, vPart_toE, zero_add]

theorem mHom_comp_includeLeft :
    (mHom (T' := T') V C).toRingHom.comp (Algebra.TensorProduct.includeLeftRingHom) = RingHom.id (ResidueField T' ⊗[T'] C) := by
  refine RingHom.ext fun xx => ?_
  show mHom V C (xx ⊗ₜ 1) = xx
  rw [mHom_tmul, TrivSqZeroExt.fst_one, one_smul]

theorem mHom_comp_includeRight :
    (mHom (T' := T') V C).toRingHom.comp
        (Algebra.TensorProduct.includeRight (R := ResidueField T') (A := ResidueField T' ⊗[T'] C)
          (B := TrivSqZeroExt (ResidueField T') V)).toRingHom =
      (algebraMap (ResidueField T') (ResidueField T' ⊗[T'] C)).comp (TrivSqZeroExt.fstHom (ResidueField T') (ResidueField T') V).toRingHom := by
  refine RingHom.ext fun t => ?_
  show mHom V C (1 ⊗ₜ t) = algebraMap (ResidueField T') (ResidueField T' ⊗[T'] C) t.fst
  rw [mHom_tmul, Algebra.algebraMap_eq_smul_one]

theorem zeroSection_eq :
    SquareZero.zeroSection V (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C) (thickening_isPullback V C) =
      Spec.map (CommRingCat.ofHom (mHom (T' := T') V C).toRingHom) := by
  apply (thickening_isPullback V C).hom_ext
  · rw [SquareZero.zeroSection_fst, thickeningFst, ← Spec.map_comp, ← CommRingCat.ofHom_comp, mHom_comp_includeLeft,
      CommRingCat.ofHom_id, Spec.map_id]
  · rw [SquareZero.zeroSection_snd, thickeningSnd, ← Spec.map_comp, ← CommRingCat.ofHom_comp, mHom_comp_includeRight,
      reductionBase, SquareZero.basePoint, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

variable {Ak : Scheme.{u}}

theorem specMap_chartRingHom (Ue : Ak.Opens) (hUe : IsAffineOpen Ue)
    (w₁ : Spec (CommRingCat.of (thickening T' V C)) ⟶ (Ue : Scheme.{u})) :
    Spec.map (CommRingCat.ofHom (chartRingHom V C Ue w₁)) ≫ hUe.fromSpec = w₁ ≫ Ue.ι :=
  (comp_ι_eq_specMap hUe _ w₁).symm

theorem mHom_comp_chartRingHom (xk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (Lk : RelativeGroupLaw (ResidueField T') xk)
    (Ue : Ak.Opens) (hUe : IsAffineOpen Ue)
    (e₁ : Spec (CommRingCat.of (ResidueField T')) ⟶ (Ue : Scheme.{u})) (he₁ : e₁ ≫ Ue.ι = (Lk.one (𝟙 _)).1)
    (τ : RelTangentPoints xk (Lk.one (𝟙 (Spec (CommRingCat.of (ResidueField T'))))).1 V
      (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C) (thickening_isPullback V C))
    (w₁ : Spec (CommRingCat.of (thickening T' V C)) ⟶ (Ue : Scheme.{u})) (hw₁ : w₁ ≫ Ue.ι = τ.1) :
    ∀ a, mHom V C (chartRingHom V C Ue w₁ a) =
      algebraMap (ResidueField T') (ResidueField T' ⊗[T'] C)
        ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom a) := by
  have h : Spec.map (CommRingCat.ofHom (chartRingHom V C Ue w₁) ≫ CommRingCat.ofHom (R := thickening T' V C) (S := ResidueField T' ⊗[T'] C) (mHom (T' := T') V C).toRingHom) ≫ hUe.fromSpec =
      Spec.map (CommRingCat.ofHom (Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom ≫
        CommRingCat.ofHom (algebraMap (ResidueField T') (ResidueField T' ⊗[T'] C))) ≫ hUe.fromSpec := by
    have e1 : Spec.map (CommRingCat.ofHom (chartRingHom V C Ue w₁) ≫ CommRingCat.ofHom (R := thickening T' V C) (S := ResidueField T' ⊗[T'] C) (mHom (T' := T') V C).toRingHom) ≫ hUe.fromSpec =
        SquareZero.zeroSection V (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C) (thickening_isPullback V C) ≫ τ.1 := by
      rw [Spec.map_comp, Category.assoc, specMap_chartRingHom V C Ue hUe w₁, ← zeroSection_eq V C, hw₁]
    have e2 : Spec.map (CommRingCat.ofHom (Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom ≫
        CommRingCat.ofHom (algebraMap (ResidueField T') (ResidueField T' ⊗[T'] C))) ≫ hUe.fromSpec =
        reductionBase T' C ≫ (Lk.one (𝟙 _)).1 := by
      rw [Spec.map_comp, Category.assoc, ← comp_ι_eq_specMap hUe _ e₁, he₁]
    exact e1.trans (τ.2.2.trans e2.symm)
  intro a
  have h2 := congrArg (fun f => f.hom a) (specMap_comp_fromSpec_injective hUe _ _ h)
  first
    | simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] using h2
    | (have h' := h2; simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at h' ⊢; exact h')
    | (have h' := h2; simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at h'; exact h')
    | exact h2

theorem chartRingHom_algebraMap (xk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (Lk : RelativeGroupLaw (ResidueField T') xk)
    (Ue : Ak.Opens) (hUe : IsAffineOpen Ue)
    (τ : RelTangentPoints xk (Lk.one (𝟙 (Spec (CommRingCat.of (ResidueField T'))))).1 V
      (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C) (thickening_isPullback V C))
    (w₁ : Spec (CommRingCat.of (thickening T' V C)) ⟶ (Ue : Scheme.{u})) (hw₁ : w₁ ≫ Ue.ι = τ.1) (c : ResidueField T') :
    letI := algebraOfHom xk Ue
    chartRingHom V C Ue w₁ (algebraMap (ResidueField T') Γ(Ak, Ue) c) = sc V C c := by
  letI := algebraOfHom xk Ue
  have hfx : hUe.fromSpec ≫ xk = Spec.map (CommRingCat.ofHom (algebraMap (ResidueField T') Γ(Ak, Ue))) := by
    have := IsAffineOpen.SpecMap_appLE_fromSpec xk (isAffineOpen_top _) hUe (le_top : Ue ≤ xk ⁻¹ᵁ ⊤)
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp] at this
    exact this.symm
  have h : Spec.map (CommRingCat.ofHom ((chartRingHom V C Ue w₁).comp (algebraMap (ResidueField T') Γ(Ak, Ue)))) =
      Spec.map (CommRingCat.ofHom (R := ResidueField T') (S := thickening T' V C)
        ((Algebra.TensorProduct.includeRight (R := ResidueField T') (A := ResidueField T' ⊗[T'] C)
          (B := TrivSqZeroExt (ResidueField T') V)).toRingHom.comp
        (algebraMap (ResidueField T') (TrivSqZeroExt (ResidueField T') V)))) := by
    calc Spec.map (CommRingCat.ofHom ((chartRingHom V C Ue w₁).comp (algebraMap (ResidueField T') Γ(Ak, Ue))))
        = Spec.map (CommRingCat.ofHom (chartRingHom V C Ue w₁)) ≫ hUe.fromSpec ≫ xk := by
          rw [CommRingCat.ofHom_comp, Spec.map_comp, hfx]
      _ = (w₁ ≫ Ue.ι) ≫ xk := by rw [← Category.assoc, specMap_chartRingHom V C Ue hUe w₁]
      _ = thickeningSnd T' V C ≫ SquareZero.toBase (ResidueField T') V := by rw [hw₁]; exact τ.2.1
      _ = _ := by rw [SquareZero.toBase, thickeningSnd, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have h2 := congrArg (fun f => f.hom c) (Spec.map_injective h)
  simp only [CommRingCat.hom_ofHom, RingHom.comp_apply] at h2
  rw [h2]
  change (1 : ResidueField T' ⊗[T'] C) ⊗ₜ (algebraMap (ResidueField T') (TrivSqZeroExt (ResidueField T') V) c) = sc V C c
  rw [sc_def, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
    TensorProduct.smul_tmul']

theorem chartRingHom_eq_jHom (xk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (Lk : RelativeGroupLaw (ResidueField T') xk)
    (Ue : Ak.Opens) (hUe : IsAffineOpen Ue)
    (e₁ : Spec (CommRingCat.of (ResidueField T')) ⟶ (Ue : Scheme.{u})) (he₁ : e₁ ≫ Ue.ι = (Lk.one (𝟙 _)).1)
    (τ : RelTangentPoints xk (Lk.one (𝟙 (Spec (CommRingCat.of (ResidueField T'))))).1 V
      (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C) (thickening_isPullback V C))
    (w₁ : Spec (CommRingCat.of (thickening T' V C)) ⟶ (Ue : Scheme.{u})) (hw₁ : w₁ ≫ Ue.ι = τ.1) (a : Γ(Ak, Ue)) :
    letI := canMop (ResidueField T') ((ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] V)
    chartRingHom V C Ue w₁ a =
      jHom V C (TrivSqZeroExt.inl ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom a) +
        TrivSqZeroExt.inr (vPart T' V C (chartRingHom V C Ue w₁ a))) :=
  eq_jHom_of_mHom_eq V C _ _ (mHom_comp_chartRingHom V C xk Lk Ue hUe e₁ he₁ τ w₁ hw₁ a)

def chiE (xk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (Lk : RelativeGroupLaw (ResidueField T') xk)
    (Ue : Ak.Opens) (hUe : IsAffineOpen Ue)
    (e₁ : Spec (CommRingCat.of (ResidueField T')) ⟶ (Ue : Scheme.{u})) (he₁ : e₁ ≫ Ue.ι = (Lk.one (𝟙 _)).1)
    (τ : RelTangentPoints xk (Lk.one (𝟙 (Spec (CommRingCat.of (ResidueField T'))))).1 V
      (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C) (thickening_isPullback V C))
    (w₁ : Spec (CommRingCat.of (thickening T' V C)) ⟶ (Ue : Scheme.{u})) (hw₁ : w₁ ≫ Ue.ι = τ.1) :
    letI := canMop (ResidueField T') ((ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] V)
    Γ(Ak, Ue) →+* TrivSqZeroExt (ResidueField T') ((ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] V) :=
  letI := canMop (ResidueField T') ((ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] V)
  { toFun := fun a => TrivSqZeroExt.inl ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom a) +
        TrivSqZeroExt.inr (vPart T' V C (chartRingHom V C Ue w₁ a))
    map_one' := by
      refine TrivSqZeroExt.ext ?_ ?_
      · simp
      · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add, TrivSqZeroExt.snd_one]
        rw [(chartRingHom V C Ue w₁).map_one, ← (jHom V C).map_one, vPart_jHom, TrivSqZeroExt.snd_one]
    map_mul' := fun a b => by
      have ha := chartRingHom_eq_jHom V C xk Lk Ue hUe e₁ he₁ τ w₁ hw₁ a
      have hb := chartRingHom_eq_jHom V C xk Lk Ue hUe e₁ he₁ τ w₁ hw₁ b
      refine TrivSqZeroExt.ext ?_ ?_
      · simp
      · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
        rw [(chartRingHom V C Ue w₁).map_mul]
        conv_lhs => rw [ha, hb, ← (jHom V C).map_mul, vPart_jHom]
    map_zero' := by
      refine TrivSqZeroExt.ext ?_ ?_
      · simp
      · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add, TrivSqZeroExt.snd_zero]
        rw [(chartRingHom V C Ue w₁).map_zero, map_zero]
    map_add' := fun a b => by
      refine TrivSqZeroExt.ext ?_ ?_
      · simp
      · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
        rw [(chartRingHom V C Ue w₁).map_add, map_add] }

theorem chiE_apply (xk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (Lk : RelativeGroupLaw (ResidueField T') xk)
    (Ue : Ak.Opens) (hUe : IsAffineOpen Ue)
    (e₁ : Spec (CommRingCat.of (ResidueField T')) ⟶ (Ue : Scheme.{u})) (he₁ : e₁ ≫ Ue.ι = (Lk.one (𝟙 _)).1)
    (τ : RelTangentPoints xk (Lk.one (𝟙 (Spec (CommRingCat.of (ResidueField T'))))).1 V
      (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C) (thickening_isPullback V C))
    (w₁ : Spec (CommRingCat.of (thickening T' V C)) ⟶ (Ue : Scheme.{u})) (hw₁ : w₁ ≫ Ue.ι = τ.1) (a : Γ(Ak, Ue)) :
    letI := canMop (ResidueField T') ((ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] V)
    chiE V C xk Lk Ue hUe e₁ he₁ τ w₁ hw₁ a =
      TrivSqZeroExt.inl ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom a) +
        TrivSqZeroExt.inr (vPart T' V C (chartRingHom V C Ue w₁ a)) := rfl

theorem jHom_comp_chiE (xk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (Lk : RelativeGroupLaw (ResidueField T') xk)
    (Ue : Ak.Opens) (hUe : IsAffineOpen Ue)
    (e₁ : Spec (CommRingCat.of (ResidueField T')) ⟶ (Ue : Scheme.{u})) (he₁ : e₁ ≫ Ue.ι = (Lk.one (𝟙 _)).1)
    (τ : RelTangentPoints xk (Lk.one (𝟙 (Spec (CommRingCat.of (ResidueField T'))))).1 V
      (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C) (thickening_isPullback V C))
    (w₁ : Spec (CommRingCat.of (thickening T' V C)) ⟶ (Ue : Scheme.{u})) (hw₁ : w₁ ≫ Ue.ι = τ.1) :
    letI := canMop (ResidueField T') ((ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] V)
    (jHom V C).comp (chiE V C xk Lk Ue hUe e₁ he₁ τ w₁ hw₁) = chartRingHom V C Ue w₁ := by
  letI := canMop (ResidueField T') ((ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] V)
  refine RingHom.ext fun a => ?_
  rw [RingHom.comp_apply, chiE_apply]
  exact (chartRingHom_eq_jHom V C xk Lk Ue hUe e₁ he₁ τ w₁ hw₁ a).symm

def derivE (xk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (Lk : RelativeGroupLaw (ResidueField T') xk)
    (Ue : Ak.Opens) (hUe : IsAffineOpen Ue)
    (e₁ : Spec (CommRingCat.of (ResidueField T')) ⟶ (Ue : Scheme.{u})) (he₁ : e₁ ≫ Ue.ι = (Lk.one (𝟙 _)).1)
    (τ : RelTangentPoints xk (Lk.one (𝟙 (Spec (CommRingCat.of (ResidueField T'))))).1 V
      (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C) (thickening_isPullback V C))
    (w₁ : Spec (CommRingCat.of (thickening T' V C)) ⟶ (Ue : Scheme.{u})) (hw₁ : w₁ ≫ Ue.ι = τ.1) :
    letI := algebraOfHom xk Ue
    ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak, Ue)
        ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom)
        ((ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] V)) := by
  letI := algebraOfHom xk Ue
  letI := canMop (ResidueField T') ((ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] V)
  letI := canCentral (ResidueField T') ((ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] V)
  have hsnd : ∀ a, (chiE V C xk Lk Ue hUe e₁ he₁ τ w₁ hw₁ a).snd = vPart T' V C (chartRingHom V C Ue w₁ a) := fun a => by
    rw [chiE_apply, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
  have hfst : ∀ a, (chiE V C xk Lk Ue hUe e₁ he₁ τ w₁ hw₁ a).fst =
      ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom) a := fun a => by
    rw [chiE_apply, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero]
  refine ⟨{ toFun := fun a => vPart T' V C (chartRingHom V C Ue w₁ a)
            map_add' := fun a b => by rw [(chartRingHom V C Ue w₁).map_add, map_add]
            map_smul' := fun c a => ?_ }, ?_⟩
  · rw [RingHom.id_apply, Algebra.smul_def, (chartRingHom V C Ue w₁).map_mul,
      chartRingHom_algebraMap V C xk Lk Ue hUe τ w₁ hw₁ c, vPart_sc_mul]
  · intro a b
    show vPart T' V C (chartRingHom V C Ue w₁ (a * b)) =
      ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom) a • vPart T' V C (chartRingHom V C Ue w₁ b) +
      ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom) b • vPart T' V C (chartRingHom V C Ue w₁ a)
    have hdec : ∀ x : Γ(Ak, Ue), chartRingHom V C Ue w₁ x =
        sc V C (((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom) x) +
          toE V C (vPart T' V C (chartRingHom V C Ue w₁ x)) := fun x => by
      conv_lhs => rw [chartRingHom_eq_jHom V C xk Lk Ue hUe e₁ he₁ τ w₁ hw₁ x, jHom_apply']
      first
        | rfl
        | (simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero,
            TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add])
    have prod : ∀ (x y : ResidueField T') (s t : (ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] V),
        (sc V C x + toE V C s) * (sc V C y + toE V C t) = sc V C (x * y) + toE V C (x • t) + toE V C (y • s) := by
      intro x y s t
      linear_combination sc_mul_sc V C x y + sc_mul_toE V C x t + toE_mul_sc V C y s + toE_mul_toE V C s t
    rw [(chartRingHom V C Ue w₁).map_mul]
    conv_lhs => rw [hdec a, hdec b, prod, map_add, map_add, vPart_sc, vPart_toE, vPart_toE, zero_add]

theorem derivE_apply (xk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (Lk : RelativeGroupLaw (ResidueField T') xk)
    (Ue : Ak.Opens) (hUe : IsAffineOpen Ue)
    (e₁ : Spec (CommRingCat.of (ResidueField T')) ⟶ (Ue : Scheme.{u})) (he₁ : e₁ ≫ Ue.ι = (Lk.one (𝟙 _)).1)
    (τ : RelTangentPoints xk (Lk.one (𝟙 (Spec (CommRingCat.of (ResidueField T'))))).1 V
      (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C) (thickening_isPullback V C))
    (w₁ : Spec (CommRingCat.of (thickening T' V C)) ⟶ (Ue : Scheme.{u})) (hw₁ : w₁ ≫ Ue.ι = τ.1) (a : Γ(Ak, Ue)) :
    letI := algebraOfHom xk Ue
    (derivE V C xk Lk Ue hUe e₁ he₁ τ w₁ hw₁).1 a = vPart T' V C (chartRingHom V C Ue w₁ a) := rfl

theorem chartRingHom_specMap (Ue : Ak.Opens) (hUe : IsAffineOpen Ue) (θ : Γ(Ak, Ue) →+* thickening T' V C) :
    chartRingHom V C Ue (Spec.map (CommRingCat.ofHom (S := thickening T' V C) θ) ≫ hUe.isoSpec.inv) = θ := by
  have h := specMap_comp_fromSpec_injective hUe
    (CommRingCat.ofHom (chartRingHom V C Ue (Spec.map (CommRingCat.ofHom (S := thickening T' V C) θ) ≫ hUe.isoSpec.inv)))
    (CommRingCat.ofHom (S := thickening T' V C) θ)
    (by rw [specMap_chartRingHom V C Ue hUe, Category.assoc, IsAffineOpen.isoSpec_inv_ι])
  exact congrArg (fun f => f.hom) h

theorem ofHom_jHom_comp {A : Type u} [CommRing A]
    (χ : letI := canMop (ResidueField T') ((ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] V)
      A →+* TrivSqZeroExt (ResidueField T') ((ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] V)) :
    letI := canMop (ResidueField T') ((ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] V)
    letI := canCentral (ResidueField T') ((ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] V)
    letI := smulCommClass_canMop (T' := T') ((ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] V)
    Spec.map (CommRingCat.ofHom (R := A) (S := thickening T' V C) ((jHom V C).comp χ)) =
      Spec.map (CommRingCat.ofHom (R := TrivSqZeroExt (ResidueField T') ((ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] V))
        (S := thickening T' V C) (jHom V C)) ≫
      Spec.map (CommRingCat.ofHom (R := A) (S := TrivSqZeroExt (ResidueField T') ((ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] V)) χ) := by
  rw [← Spec.map_comp]; rfl

theorem pushedChart_comp_ι (xk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (Lk : RelativeGroupLaw (ResidueField T') xk)
    (Ue : Ak.Opens) (hUe : IsAffineOpen Ue)
    (e₁ : Spec (CommRingCat.of (ResidueField T')) ⟶ (Ue : Scheme.{u})) (he₁ : e₁ ≫ Ue.ι = (Lk.one (𝟙 _)).1)
    (τ : RelTangentPoints xk (Lk.one (𝟙 (Spec (CommRingCat.of (ResidueField T'))))).1 V
      (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C) (thickening_isPullback V C))
    (w₁ : Spec (CommRingCat.of (thickening T' V C)) ⟶ (Ue : Scheme.{u})) (hw₁ : w₁ ≫ Ue.ι = τ.1) (ψ : Ak ⟶ Ak)
    (χ' : letI := canMop (ResidueField T') ((ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] V)
      Γ(Ak, Ue) →+* TrivSqZeroExt (ResidueField T') ((ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] V))
    (hχ' : letI := canMop (ResidueField T') ((ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] V)
      letI := canCentral (ResidueField T') ((ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] V)
      Spec.map (CommRingCat.ofHom (S := TrivSqZeroExt (ResidueField T') ((ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] V)) χ') ≫ hUe.fromSpec =
        Spec.map (CommRingCat.ofHom (S := TrivSqZeroExt (ResidueField T') ((ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] V))
          (chiE V C xk Lk Ue hUe e₁ he₁ τ w₁ hw₁)) ≫ hUe.fromSpec ≫ ψ) :
    letI := canMop (ResidueField T') ((ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] V)
    letI := canCentral (ResidueField T') ((ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] V)
    letI := smulCommClass_canMop (T' := T') ((ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] V)
    (Spec.map (CommRingCat.ofHom (S := thickening T' V C) ((jHom V C).comp χ')) ≫ hUe.isoSpec.inv) ≫ Ue.ι =
      τ.1 ≫ ψ := by
  rw [Category.assoc, IsAffineOpen.isoSpec_inv_ι, ofHom_jHom_comp, Category.assoc, hχ', ← Category.assoc (Spec.map _),
    ← ofHom_jHom_comp, jHom_comp_chiE, ← Category.assoc, specMap_chartRingHom V C Ue hUe w₁, hw₁]

end SpecSide

section Pushout

variable {T' : Type u} [CommRing T'] [IsLocalRing T'] (I : Ideal T')
  (hI : I ≤ maximalIdeal T') (hsmall : I * maximalIdeal T' = ⊥) (C : Type u) [CommRing C] [Algebra T' C]

include hI hsmall in

theorem isPushout_pairRing :
    IsPushout (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))))
      (Spec.map (CommRingCat.ofHom (pairFst I C))) (Spec.map (CommRingCat.ofHom (pairSnd I C))) := by
  refine AlgebraicGeometry.isPushout_specMap_of_isPullback_of_surjective_of_isNilpotent
    (R := CommRingCat.of (pairRing I C)) ?_ Ideal.Quotient.mk_surjective ?_
  · exact IsPullback.of_isLimit (CommRingCat.pullbackConeIsLimit
      (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C))))
      (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))))
  · intro x hx
    have hx' : x ∈ I.map (algebraMap T' C) := by
      simpa only [CommRingCat.hom_ofHom, Ideal.mk_ker] using hx
    refine ⟨2, ?_⟩
    have hII : I * I = ⊥ := le_bot_iff.1 ((Ideal.mul_mono_right hI).trans hsmall.le)
    have hmem : x * x ∈ I.map (algebraMap T' C) * I.map (algebraMap T' C) := Ideal.mul_mem_mul hx' hx'
    rw [← Ideal.map_mul, hII, Ideal.map_bot] at hmem
    rw [pow_two]
    exact (Submodule.mem_bot C).1 hmem

end Pushout

end ChainRule28

end

theorem solution
    (T' : Type u) [CommRing T'] [IsLocalRing T'] (I : Ideal T')

    (hI : I ≤ maximalIdeal T') (hsmall : I * maximalIdeal T' = ⊥)

    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module.Finite (ResidueField T') V]
    [Module T' V] [IsScalarTower T' (ResidueField T') V]
    [Module (ResidueField T')ᵐᵒᵖ V] [IsCentralScalar (ResidueField T') V]
    (ι : V →ₗ[T'] T')

    (C : Type u) [CommRing C] [Algebra T' C]
    {U Y Y' : Scheme.{u}} (z : U ⟶ Y) (z' : U ⟶ Y') (u v : Spec (CommRingCat.of C) ⟶ U)

    (huv : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ u
      = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ v)

    {Ak : Scheme.{u}} (xk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (Lk : RelativeGroupLaw (ResidueField T') xk)
    (Ue : Ak.Opens) (hUe : IsAffineOpen Ue)
    (e₁ : Spec (CommRingCat.of (ResidueField T')) ⟶ (Ue : Scheme.{u})) (he₁ : e₁ ≫ Ue.ι = (Lk.one (𝟙 _)).1)
    (ak : Ak ⟶ Y) (ak' : Ak ⟶ Y')

    (W : Type u) [AddCommGroup W] [Module (ResidueField T') W]
    (τW : W → SchemeHomOver (tangentBase (ResidueField T') (RingHom.id (ResidueField T'))) xk)
    (hWinj : Function.Injective τW)
    (hWrange : ∀ P : SchemeHomOver (tangentBase (ResidueField T') (RingHom.id (ResidueField T'))) xk, P ∈ Set.range τW ↔ IsTangentVector Lk (ResidueField T') (RingHom.id (ResidueField T')) P)
    (hWadd : ∀ v w : W, τW (v + w) = Lk.mul (tangentBase (ResidueField T') (RingHom.id (ResidueField T'))) (τW v) (τW w))
    (hWsmul : ∀ (a : (ResidueField T')) (v : W), (τW (a • v)).1 = tangentScale (ResidueField T') a ≫ (τW v).1)

    (Φ : letI := algebraOfHom xk Ue
      ∀ (M : Type u) [AddCommGroup M] [Module (ResidueField T') M], ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak, Ue) ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom) M) ≃ₗ[(ResidueField T')] (W ⊗[(ResidueField T')] M))
    (hΦnat : letI := algebraOfHom xk Ue
      ∀ (M M' : Type u) [AddCommGroup M] [Module (ResidueField T') M] [AddCommGroup M'] [Module (ResidueField T') M'] (g : M →ₗ[(ResidueField T')] M') (δ : ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak, Ue) ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom) M)),
        Φ M' (Algebra.PointDerivations.map ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom) g δ) = TensorProduct.map (LinearMap.id : W →ₗ[(ResidueField T')] W) g (Φ M δ))
    (hΦpin : letI := algebraOfHom xk Ue
      ∀ (δ : ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak, Ue) ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom) (ResidueField T'))) (χ : Γ(Ak, Ue) →+* DualNumber (ResidueField T')),
        (∀ a : Γ(Ak, Ue), TrivSqZeroExt.fst (χ a) = ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom) a) →
        (∀ a : Γ(Ak, Ue), TrivSqZeroExt.snd (χ a) = (δ : Γ(Ak, Ue) →ₗ[(ResidueField T')] (ResidueField T')) a) →
        (τW (TensorProduct.rid (ResidueField T') W (Φ (ResidueField T') δ))).1 = Spec.map (CommRingCat.ofHom χ) ≫ hUe.fromSpec)

    (ψ : Ak ⟶ Ak) (hψ : ψ ≫ xk = xk)
    (hψhom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of (ResidueField T'))) (P Q : SchemeHomOver t xk),
      pushPt ψ hψ (Lk.mul t P Q) = Lk.mul t (pushPt ψ hψ P) (pushPt ψ hψ Q))
    (θψ : W →ₗ[(ResidueField T')] W) (hθψ : ∀ w : W, τW (θψ w) = pushPt ψ hψ (τW w))

    (hzψ : ∀ {S : Scheme.{u}} (g : S ⟶ U) (gk : S ⟶ Ak), g ≫ z = gk ≫ ak → g ≫ z' = gk ≫ ψ ≫ ak')

    (δ : letI := algebraOfHom xk Ue
      ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak, Ue) ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom) (Module.Dual (ResidueField T') V →ₗ[(ResidueField T')] ((ResidueField T') ⊗[T'] C))))
    (hδ : letI := algebraOfHom xk Ue
      IsTangentCoordsOfPairAt I V ι C (u ≫ z) (v ≫ z) xk Lk ak Ue (fun a => δ.1 a)) :
    letI := algebraOfHom xk Ue
    IsTangentCoordsOfPairAt I V ι C (u ≫ z') (v ≫ z') xk Lk ak' Ue
      (fun a => ((Φ (Module.Dual (ResidueField T') V →ₗ[(ResidueField T')] ((ResidueField T') ⊗[T'] C))).symm (TensorProduct.map θψ (LinearMap.id : (Module.Dual (ResidueField T') V →ₗ[(ResidueField T')] ((ResidueField T') ⊗[T'] C)) →ₗ[(ResidueField T')] (Module.Dual (ResidueField T') V →ₗ[(ResidueField T')] ((ResidueField T') ⊗[T'] C))) (Φ (Module.Dual (ResidueField T') V →ₗ[(ResidueField T')] ((ResidueField T') ⊗[T'] C)) δ))).1 a) := by
  letI instA := algebraOfHom xk Ue
  obtain ⟨η, hηnat, hηpin, hηpush⟩ :=
    AlgebraicGeometry.SmallExtension.exists_pointDerivations_pushforward_natural_of_forall_apply_eq_pushPt T' xk Lk Ue hUe
      e₁ he₁ W τW hWinj hWrange hWadd hWsmul Φ hΦnat hΦpin ψ hψ θψ hθψ
  have hηδ := AlgebraicGeometry.SmallExtension.pointDerivations_natural_endo_eq_symm_map_tmul_of_apply_eq
    ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom) W Φ hΦnat θψ η hηnat hηpin
    (Module.Dual (ResidueField T') V →ₗ[(ResidueField T')] ((ResidueField T') ⊗[T'] C)) δ
  obtain ⟨w₀, hw₀, w₁, hpair, htrans, hcoords⟩ := hδ

  have hP := ChainRule28.isPushout_pairRing I hI hsmall C
  obtain ⟨ϑ, hϑ, φP, hφ1, hφ2, hwφ⟩ := hpair
  have hφP : φP = hP.desc u v huv ≫ z := by
    apply hP.hom_ext
    · rw [hφ1, ← Category.assoc, hP.inl_desc]
    · rw [hφ2, ← Category.assoc, hP.inr_desc]
  have hpair' : IsTangentOfPair I V ι C (u ≫ z') (v ≫ z') ((w₀ ≫ ψ) ≫ ak') := by
    refine ⟨ϑ, hϑ, hP.desc u v huv ≫ z', by rw [← Category.assoc, hP.inl_desc], by rw [← Category.assoc, hP.inr_desc], ?_⟩
    have := hzψ (Spec.map (CommRingCat.ofHom ϑ) ≫ hP.desc u v huv) w₀ (by rw [Category.assoc, ← hφP, ← hwφ])
    rw [Category.assoc, ← this, Category.assoc]

  have hw₀' : (w₀ ≫ ψ) ≫ xk = RelTangentPoints.base V (thickeningSnd T' V C) := by rw [Category.assoc, hψ, hw₀]
  have htr := ChainRule28.translate_comp xk Lk V (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C)
    (thickening_isPullback V C) ψ hψ hψhom w₀ hw₀

  letI := ChainRule28.canMop (ResidueField T') ((ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] V)
  letI := ChainRule28.canCentral (ResidueField T') ((ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] V)
  letI := ChainRule28.smulCommClass_canMop (T' := T') ((ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] V)
  obtain ⟨χ', hχ'1, hχ'2, hχ'3⟩ := hηpush ((ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] V)
    (ChainRule28.chiE V C xk Lk Ue hUe e₁ he₁ _ w₁ htrans)
    (ChainRule28.derivE V C xk Lk Ue hUe e₁ he₁ _ w₁ htrans)
    (fun a => by
      rw [ChainRule28.chiE_apply, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero])
    (fun a => by
      rw [ChainRule28.chiE_apply, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add,
        ChainRule28.derivE_apply])
  refine ⟨w₀ ≫ ψ, hw₀',
    Spec.map (CommRingCat.ofHom (S := thickening T' V C) ((ChainRule28.jHom V C).comp χ')) ≫ hUe.isoSpec.inv,
    hpair', ?_, ?_⟩
  · rw [ChainRule28.pushedChart_comp_ι V C xk Lk Ue hUe e₁ he₁ _ w₁ htrans ψ χ' hχ'3, htr]
  · funext a
    have hδ' : δ = Algebra.PointDerivations.map
        ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom)
        (tensorToDualHom (ResidueField T') (ResidueField T' ⊗[T'] C) V)
        (ChainRule28.derivE V C xk Lk Ue hUe e₁ he₁ _ w₁ htrans) := by
      apply Subtype.ext; apply LinearMap.ext; intro b
      have hb := congrFun hcoords b
      rw [Algebra.PointDerivations.map_apply_coe, ChainRule28.derivE_apply]
      exact hb
    rw [← hηδ, hδ', hηnat, Algebra.PointDerivations.map_apply_coe, ← hχ'2 a, ChainRule28.chartRingHom_specMap]
    show tensorToDualHom (ResidueField T') (ResidueField T' ⊗[T'] C) V (χ' a).snd =
      tensorToDualHom (ResidueField T') (ResidueField T' ⊗[T'] C) V (vPart T' V C ((ChainRule28.jHom V C).comp χ' a))
    rw [RingHom.comp_apply, ChainRule28.vPart_jHom]

end S_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAt_comp_of_forall_apply_eq_pushPt_of_mul_maximalIdeal_eq_bot
end P2MW
export P2MW.S_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAt_comp_of_forall_apply_eq_pushPt_of_mul_maximalIdeal_eq_bot (solution)
