-- Prove2me | solution 1 for AlgebraicGeometry.SmallExtension.mem_pointDerivations_tangentCoords_and_injective_and_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/bdc35697-e9e1-59c9-b241-e8dcde36fa38

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Definitions.Def_AlgebraicGeometry_SquareZeroRelTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPair
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAt
import Definitions.Def_Algebra_PointDerivations
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SmallExtension_mem_pointDerivations_tangentCoords_and_injective_and_surjective

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct IsLocalRing AlgebraicGeometry.SmallExtension AlgebraicGeometry.Scheme.TwoAffineOpenCover"

universe u

namespace I4aAux

variable (k : Type u) [Field k] (M : Type u) [CommRing M] [Algebra k M]
  (V : Type u) [AddCommGroup V] [Module k V] [Module kᵐᵒᵖ V] [IsCentralScalar k V]

noncomputable def aug : M ⊗[k] TrivSqZeroExt k V →ₐ[k] M :=
  Algebra.TensorProduct.lift (AlgHom.id k M) ((Algebra.ofId k M).comp (TrivSqZeroExt.fstHom k k V)) (fun _ _ => Commute.all _ _)

noncomputable def vP : M ⊗[k] TrivSqZeroExt k V →ₗ[k] M ⊗[k] V :=
  TensorProduct.map LinearMap.id (TrivSqZeroExt.sndHom k V)

noncomputable def inV : M ⊗[k] V →ₗ[k] M ⊗[k] TrivSqZeroExt k V :=
  TensorProduct.map LinearMap.id (TrivSqZeroExt.inrHom k V)

variable {k M V}

@[scoped simp] theorem aug_tmul (x : M) (t : TrivSqZeroExt k V) : aug k M V (x ⊗ₜ t) = x * algebraMap k M t.fst := by
  simp [aug, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply]

@[scoped simp] theorem vP_tmul (x : M) (t : TrivSqZeroExt k V) : vP k M V (x ⊗ₜ t) = x ⊗ₜ t.snd := by
  simp [vP]

@[scoped simp] theorem inV_tmul (x : M) (v : V) : inV k M V (x ⊗ₜ v) = x ⊗ₜ TrivSqZeroExt.inr v := by
  simp [inV]

theorem vP_inV (y : M ⊗[k] V) : vP k M V (inV k M V y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul x v => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb]

theorem aug_inV (y : M ⊗[k] V) : aug k M V (inV k M V y) = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul x v => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb, add_zero]

theorem aug_tmul_one (m : M) : aug k M V (m ⊗ₜ (1 : TrivSqZeroExt k V)) = m := by simp

theorem vP_tmul_one (m : M) : vP k M V (m ⊗ₜ (1 : TrivSqZeroExt k V)) = 0 := by simp

theorem decomp (z : M ⊗[k] TrivSqZeroExt k V) : z = (aug k M V z) ⊗ₜ (1 : TrivSqZeroExt k V) + inV k M V (vP k M V z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x t =>
    rw [aug_tmul, vP_tmul, inV_tmul, mul_comm, ← Algebra.smul_def, TensorProduct.smul_tmul, ← TensorProduct.tmul_add]
    congr 1
    rw [Algebra.smul_def, mul_one]
    exact (TrivSqZeroExt.inl_fst_add_inr_snd_eq t).symm
  | add a b ha hb =>
    conv_lhs => rw [ha, hb]
    rw [map_add, map_add, map_add, TensorProduct.add_tmul]
    abel

theorem vP_mul (z z' : M ⊗[k] TrivSqZeroExt k V) :
    vP k M V (z * z') = aug k M V z • vP k M V z' + aug k M V z' • vP k M V z := by
  show vP k M V (Algebra.TensorProduct.mul z z') = _
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb =>
    rw [LinearMap.map_add, LinearMap.add_apply, map_add, ha, hb]
    simp only [map_add, add_smul, smul_add]
    abel
  | tmul x t =>
    induction z' using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb =>
      rw [LinearMap.map_add, map_add, ha, hb]
      simp only [map_add, add_smul, smul_add]
      abel
    | tmul x' t' =>
      rw [Algebra.TensorProduct.mul_apply, vP_tmul, vP_tmul, vP_tmul, aug_tmul, aug_tmul, TrivSqZeroExt.snd_mul,
        op_smul_eq_smul, TensorProduct.tmul_add]
      simp only [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, Algebra.algebraMap_self, RingHom.id_apply]
      congr 1 <;> (congr 1; ring)

theorem aug_mul (z z' : M ⊗[k] TrivSqZeroExt k V) : aug k M V (z * z') = aug k M V z * aug k M V z' := map_mul _ _ _

theorem inV_mul_inV (y y' : M ⊗[k] V) : inV k M V y * inV k M V y' = 0 := by
  show Algebra.TensorProduct.mul (inV k M V y) (inV k M V y') = 0
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add, LinearMap.map_add, LinearMap.add_apply, ha, hb, add_zero]
  | tmul x v =>
    induction y' using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => rw [map_add, map_add, ha, hb, add_zero]
    | tmul x' v' => rw [inV_tmul, inV_tmul, Algebra.TensorProduct.mul_apply, TrivSqZeroExt.inr_mul_inr, TensorProduct.tmul_zero]

theorem tmul_one_mul_inV (m : M) (y : M ⊗[k] V) : (m ⊗ₜ (1 : TrivSqZeroExt k V)) * inV k M V y = inV k M V ((m • y : M ⊗[k] V)) := by
  show Algebra.TensorProduct.mul _ (inV k M V y) = _
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, smul_add, map_add, ha, hb]
  | tmul x v => rw [inV_tmul, Algebra.TensorProduct.mul_apply, one_mul, TensorProduct.smul_tmul', smul_eq_mul, inV_tmul]

theorem inV_mul_tmul_one (m : M) (y : M ⊗[k] V) : inV k M V y * (m ⊗ₜ (1 : TrivSqZeroExt k V)) = inV k M V ((m • y : M ⊗[k] V)) := by
  rw [mul_comm, tmul_one_mul_inV]

theorem tmul_one_mul_tmul_one (m m' : M) : (m ⊗ₜ[k] (1 : TrivSqZeroExt k V)) * (m' ⊗ₜ[k] (1 : TrivSqZeroExt k V)) = (m * m') ⊗ₜ[k] (1 : TrivSqZeroExt k V) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

end I4aAux
p2m_reactivate "P2MW.S_AlgebraicGeometry_SmallExtension_mem_pointDerivations_tangentCoords_and_injective_and_surjective.I4aAux"

namespace I4aAux

open CategoryTheory AlgebraicGeometry

theorem comp_toSpecΓ {X : Scheme.{u}} (U : X.Opens) {R : CommRingCat.{u}} (g : Spec R ⟶ (U : Scheme.{u})) :
    g ≫ U.toSpecΓ = Spec.map (U.topIso.inv ≫ g.appTop ≫ (Scheme.ΓSpecIso R).hom) := by
  rw [Scheme.Opens.toSpecΓ, Scheme.toSpecΓ_naturality_assoc, ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp, ← Spec.map_comp,
    Category.assoc]

theorem chart_comp {X : Scheme.{u}} (U : X.Opens) {R S : CommRingCat.{u}} (f : R ⟶ S) (g : Spec R ⟶ (U : Scheme.{u})) :
    U.topIso.inv ≫ (Spec.map f ≫ g).appTop ≫ (Scheme.ΓSpecIso S).hom = (U.topIso.inv ≫ g.appTop ≫ (Scheme.ΓSpecIso R).hom) ≫ f := by
  rw [Scheme.Hom.comp_appTop, Category.assoc, Category.assoc, Category.assoc, Scheme.ΓSpecIso_naturality]

theorem appLE_topIso_inv {X : Scheme.{u}} (U : X.Opens) {K : CommRingCat.{u}} (c : X ⟶ Spec K) :
    c.appLE ⊤ U le_top ≫ U.topIso.inv = (U.ι ≫ c).appTop := by
  rw [Scheme.Opens.topIso_inv]
  erw [Scheme.Hom.appLE_map]
  rw [Scheme.Hom.comp_appTop, Scheme.Opens.ι_appTop]
  rfl

theorem ext_to_Spec' {R K : CommRingCat.{u}} {f g : Spec R ⟶ Spec K}
    (h : (Scheme.ΓSpecIso K).inv ≫ f.appTop ≫ (Scheme.ΓSpecIso R).hom = (Scheme.ΓSpecIso K).inv ≫ g.appTop ≫ (Scheme.ΓSpecIso R).hom) :
    f = g := by
  have h' := congrArg (fun q => q ≫ (Scheme.ΓSpecIso R).inv) h
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at h'
  exact AlgebraicGeometry.ext_to_Spec (by rw [Scheme.Γ_map_op, Scheme.Γ_map_op]; exact h')

end I4aAux
p2m_reactivate "P2MW.S_AlgebraicGeometry_SmallExtension_mem_pointDerivations_tangentCoords_and_injective_and_surjective.I4aAux"

namespace I4aAux

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SmallExtension

section tTDH
variable (k : Type u) [Field k] (M : Type u) [AddCommGroup M] [Module k M]
  (W : Type u) [AddCommGroup W] [Module k W] [Module.Finite k W]

noncomputable def tInv : (Module.Dual k W →ₗ[k] M) →ₗ[k] M ⊗[k] W where
  toFun g := ∑ i, g ((Module.finBasis k W).coord i) ⊗ₜ (Module.finBasis k W) i
  map_add' g g' := by simp [TensorProduct.add_tmul, Finset.sum_add_distrib]
  map_smul' c g := by simp [TensorProduct.smul_tmul', Finset.smul_sum]

theorem tTDH_tInv (g : Module.Dual k W →ₗ[k] M) : tensorToDualHom k M W (tInv k M W g) = g := by
  apply LinearMap.ext; intro ξ
  simp only [tInv, LinearMap.coe_mk, AddHom.coe_mk, map_sum, LinearMap.coe_sum, Finset.sum_apply, tensorToDualHom_tmul]
  simp_rw [← LinearMap.map_smul]
  rw [← map_sum, Module.Basis.sum_dual_apply_smul_coord]

theorem tInv_tTDH (z : M ⊗[k] W) : tInv k M W (tensorToDualHom k M W z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp [tInv]
  | add a b ha hb => rw [map_add, map_add, ha, hb]
  | tmul m w =>
    simp only [tInv, LinearMap.coe_mk, AddHom.coe_mk, tensorToDualHom_tmul, Module.Basis.coord_apply]
    conv_rhs => rw [← Module.Basis.sum_repr (Module.finBasis k W) w, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']

theorem tTDH_injective : Function.Injective (tensorToDualHom k M W) := fun a b h => by
  rw [← tInv_tTDH k M W a, ← tInv_tTDH k M W b, h]

end tTDH
p2m_reactivate "P2MW.S_AlgebraicGeometry_SmallExtension_mem_pointDerivations_tangentCoords_and_injective_and_surjective.I4aAux"

section derivHom
variable (k : Type u) [Field k] (M : Type u) [CommRing M] [Algebra k M]
  (V : Type u) [AddCommGroup V] [Module k V] [Module kᵐᵒᵖ V] [IsCentralScalar k V] [Module.Finite k V]
  {A : Type u} [CommRing A] [Algebra k A] (ev : A →+* k)

noncomputable def derivHom (D : A →ₗ[k] (Module.Dual k V →ₗ[k] M))
    (hD : D ∈ Algebra.PointDerivations k A ev (Module.Dual k V →ₗ[k] M)) : A →+* M ⊗[k] TrivSqZeroExt k V where
  toFun a := (algebraMap k M (ev a)) ⊗ₜ (1 : TrivSqZeroExt k V) + inV k M V (tInv k M V (D a))
  map_one' := by
    rw [map_one, map_one, Algebra.PointDerivations.apply_one hD, map_zero, map_zero, add_zero]; rfl
  map_mul' a b := by
    rw [map_mul, map_mul, Algebra.PointDerivations.apply_mul hD, map_add, map_add, add_mul, mul_add, mul_add,
      tmul_one_mul_tmul_one, tmul_one_mul_inV, inV_mul_tmul_one, inV_mul_inV, add_zero, map_smul, map_smul, map_smul, map_smul,
      algebraMap_smul, algebraMap_smul, (inV k M V).map_smul, (inV k M V).map_smul, ← map_mul]
    abel
  map_zero' := by rw [map_zero, map_zero, map_zero, map_zero, map_zero, TensorProduct.zero_tmul, zero_add]
  map_add' a b := by
    rw [map_add, map_add, map_add, map_add, map_add, TensorProduct.add_tmul]; abel

theorem derivHom_apply (D : A →ₗ[k] (Module.Dual k V →ₗ[k] M)) (hD : D ∈ Algebra.PointDerivations k A ev (Module.Dual k V →ₗ[k] M)) (a : A) :
    derivHom k M V ev D hD a = (algebraMap k M (ev a)) ⊗ₜ (1 : TrivSqZeroExt k V) + inV k M V (tInv k M V (D a)) := rfl

theorem aug_derivHom (D : A →ₗ[k] (Module.Dual k V →ₗ[k] M)) (hD : D ∈ Algebra.PointDerivations k A ev (Module.Dual k V →ₗ[k] M)) (a : A) :
    aug k M V (derivHom k M V ev D hD a) = algebraMap k M (ev a) := by
  rw [derivHom_apply, map_add, aug_tmul_one, aug_inV, add_zero]

theorem vP_derivHom (D : A →ₗ[k] (Module.Dual k V →ₗ[k] M)) (hD : D ∈ Algebra.PointDerivations k A ev (Module.Dual k V →ₗ[k] M)) (a : A) :
    vP k M V (derivHom k M V ev D hD a) = tInv k M V (D a) := by
  rw [derivHom_apply, map_add, vP_tmul_one, vP_inV, zero_add]

end derivHom
p2m_reactivate "P2MW.S_AlgebraicGeometry_SmallExtension_mem_pointDerivations_tangentCoords_and_injective_and_surjective.I4aAux"

end I4aAux
p2m_reactivate "P2MW.S_AlgebraicGeometry_SmallExtension_mem_pointDerivations_tangentCoords_and_injective_and_surjective.I4aAux"

namespace I4aAux

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing AlgebraicGeometry.SmallExtension AlgebraicGeometry.Scheme.TwoAffineOpenCover"

section PartB

variable {T' : Type u} [CommRing T'] [IsLocalRing T']
  (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
  [IsCentralScalar (ResidueField T') V] [Module T' V] [IsScalarTower T' (ResidueField T') V]
  (C : Type u) [CommRing C] [Algebra T' C]

theorem base_eq : RelTangentPoints.base V (thickeningSnd T' V C) =
    Spec.map (CommRingCat.ofHom (R := ResidueField T') (S := thickening T' V C)
      (algebraMap (ResidueField T') (thickening T' V C))) := by
  show thickeningSnd T' V C ≫ SquareZero.toBase (ResidueField T') V = _
  rw [SquareZero.toBase, ← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun r => ?_)
  show (Algebra.TensorProduct.includeRight (R := ResidueField T') (A := ResidueField T' ⊗[T'] C)
      (B := TrivSqZeroExt (ResidueField T') V)) (algebraMap (ResidueField T') (TrivSqZeroExt (ResidueField T') V) r) = _
  exact AlgHom.commutes _ r

theorem zeroSection_eq : SquareZero.zeroSection V (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C)
      (thickening_isPullback V C) =
    Spec.map (CommRingCat.ofHom (R := thickening T' V C) (S := ResidueField T' ⊗[T'] C)
      (aug (ResidueField T') (ResidueField T' ⊗[T'] C) V).toRingHom) := by
  apply (thickening_isPullback V C).hom_ext
  · rw [SquareZero.zeroSection_fst, ← Spec.map_comp, ← Spec.map_id]
    congr 1
    refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
    change x = aug (ResidueField T') (ResidueField T' ⊗[T'] C) V (x ⊗ₜ 1)
    rw [aug_tmul_one]
  · rw [SquareZero.zeroSection_snd, SquareZero.basePoint, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    refine CommRingCat.hom_ext (RingHom.ext fun t => ?_)
    change algebraMap (ResidueField T') (ResidueField T' ⊗[T'] C) t.fst =
      aug (ResidueField T') (ResidueField T' ⊗[T'] C) V ((1 : ResidueField T' ⊗[T'] C) ⊗ₜ t)
    rw [aug_tmul, one_mul]

variable {Ak : Scheme.{u}} (xk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (Ue : Ak.Opens)

theorem chart_algebraMap_of_over {R : Type u} [CommRing R] (g : Spec (CommRingCat.of R) ⟶ (Ue : Scheme.{u}))
    (F : ResidueField T' →+* R)
    (hg : (g ≫ Ue.ι) ≫ xk = Spec.map (CommRingCat.ofHom F)) (r : ResidueField T') :
    letI := algebraOfHom xk Ue
    (Ue.topIso.inv ≫ g.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom (algebraMap (ResidueField T') Γ(Ak, Ue) r) =
      F r := by
  letI := algebraOfHom xk Ue
  rw [algebraMap_algebraOfHom]
  show ((xk.appLE ⊤ Ue le_top ≫ Ue.topIso.inv) ≫ g.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom
      ((Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).inv.hom r) = F r
  rw [appLE_topIso_inv, ← Category.assoc, ← Scheme.Hom.comp_appTop, ← Category.assoc, hg]
  have := congrArg (fun φ => φ.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom F))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
  show (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((Spec.map (CommRingCat.ofHom F)).appTop.hom
    ((Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).inv.hom r)) = F r
  rw [← this]
  exact CategoryTheory.Iso.inv_hom_id_apply _ _

theorem over_of_chart_algebraMap {R : Type u} [CommRing R] (g : Spec (CommRingCat.of R) ⟶ (Ue : Scheme.{u}))
    (F : ResidueField T' →+* R)
    (hg : letI := algebraOfHom xk Ue
      ∀ r : ResidueField T', (Ue.topIso.inv ≫ g.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom
        (algebraMap (ResidueField T') Γ(Ak, Ue) r) = F r) :
    (g ≫ Ue.ι) ≫ xk = Spec.map (CommRingCat.ofHom F) := by
  letI := algebraOfHom xk Ue
  apply ext_to_Spec'
  rw [← Scheme.ΓSpecIso_inv_naturality_assoc, Iso.inv_hom_id, Category.comp_id]
  refine CommRingCat.hom_ext (RingHom.ext fun r => ?_)
  rw [CommRingCat.hom_ofHom, ← hg r, algebraMap_algebraOfHom]
  show _ = ((xk.appLE ⊤ Ue le_top ≫ Ue.topIso.inv) ≫ g.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom
      ((Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).inv.hom r)
  rw [appLE_topIso_inv, ← Scheme.Hom.comp_appTop_assoc, Category.assoc g]
  rfl

theorem ev_comp_algebraMap (pt : Spec (CommRingCat.of (ResidueField T')) ⟶ Ak) (hpt : pt ≫ xk = 𝟙 _)
    (e₁ : Spec (CommRingCat.of (ResidueField T')) ⟶ (Ue : Scheme.{u})) (he₁ : e₁ ≫ Ue.ι = pt) :
    letI := algebraOfHom xk Ue
    (Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom.comp
      (algebraMap (ResidueField T') Γ(Ak, Ue)) = RingHom.id _ := by
  letI := algebraOfHom xk Ue
  apply RingHom.ext
  intro r
  have h : (e₁ ≫ Ue.ι) ≫ xk = Spec.map (CommRingCat.ofHom (RingHom.id (ResidueField T'))) := by
    rw [he₁, hpt, CommRingCat.ofHom_id, Spec.map_id]
  exact chart_algebraMap_of_over xk Ue e₁ (RingHom.id _) h r

theorem chart_inj (hUe : IsAffineOpen Ue) {R : CommRingCat.{u}} (g g' : Spec R ⟶ (Ue : Scheme.{u}))
    (h : Ue.topIso.inv ≫ g.appTop ≫ (Scheme.ΓSpecIso R).hom = Ue.topIso.inv ≫ g'.appTop ≫ (Scheme.ΓSpecIso R).hom) :
    g = g' := by
  haveI : IsIso Ue.toSpecΓ := by rw [← hUe.isoSpec_hom]; infer_instance
  rw [← cancel_mono Ue.toSpecΓ, comp_toSpecΓ, comp_toSpecΓ, h]

theorem chart_surj (hUe : IsAffineOpen Ue) {R : CommRingCat.{u}} (φ : Γ(Ak, Ue) ⟶ R) :
    ∃ g : Spec R ⟶ (Ue : Scheme.{u}), Ue.topIso.inv ≫ g.appTop ≫ (Scheme.ΓSpecIso R).hom = φ := by
  haveI : IsIso Ue.toSpecΓ := by rw [← hUe.isoSpec_hom]; infer_instance
  refine ⟨Spec.map φ ≫ inv Ue.toSpecΓ, ?_⟩
  have h1 := comp_toSpecΓ Ue (Spec.map φ ≫ inv Ue.toSpecΓ)
  rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id] at h1
  exact (Spec.map_injective h1).symm

theorem zeroSection_comp_iff (hUe : IsAffineOpen Ue)
    (pt : Spec (CommRingCat.of (ResidueField T')) ⟶ Ak)
    (e₁ : Spec (CommRingCat.of (ResidueField T')) ⟶ (Ue : Scheme.{u})) (he₁ : e₁ ≫ Ue.ι = pt)
    (g : Spec (CommRingCat.of (thickening T' V C)) ⟶ (Ue : Scheme.{u})) :
    SquareZero.zeroSection V (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C) (thickening_isPullback V C)
        ≫ g ≫ Ue.ι = reductionBase T' C ≫ pt ↔
      (aug (ResidueField T') (ResidueField T' ⊗[T'] C) V).toRingHom.comp (chartRingHom V C Ue g) =
        (algebraMap (ResidueField T') (ResidueField T' ⊗[T'] C)).comp
          (Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom := by
  rw [zeroSection_eq, ← he₁]
  have key : Spec.map (CommRingCat.ofHom (R := thickening T' V C) (S := ResidueField T' ⊗[T'] C)
        (aug (ResidueField T') (ResidueField T' ⊗[T'] C) V).toRingHom) ≫ g = reductionBase T' C ≫ e₁ ↔
      (aug (ResidueField T') (ResidueField T' ⊗[T'] C) V).toRingHom.comp (chartRingHom V C Ue g) =
        (algebraMap (ResidueField T') (ResidueField T' ⊗[T'] C)).comp
          (Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom := by
    constructor
    · intro h
      have h1 := chart_comp Ue (CommRingCat.ofHom (R := thickening T' V C) (S := ResidueField T' ⊗[T'] C)
        (aug (ResidueField T') (ResidueField T' ⊗[T'] C) V).toRingHom) g
      have h2 := chart_comp Ue (CommRingCat.ofHom (algebraMap (ResidueField T') (ResidueField T' ⊗[T'] C))) e₁
      rw [h] at h1
      have := h1.symm.trans h2
      exact congrArg CommRingCat.Hom.hom this
    · intro h
      apply chart_inj Ue hUe
      rw [chart_comp, chart_comp]
      exact CommRingCat.hom_ext h
  rw [← key]
  constructor
  · intro h
    rw [← cancel_mono Ue.ι]
    simpa only [Category.assoc] using h
  · intro h
    rw [← Category.assoc, h, Category.assoc]

end PartB
p2m_reactivate "P2MW.S_AlgebraicGeometry_SmallExtension_mem_pointDerivations_tangentCoords_and_injective_and_surjective.I4aAux"

end I4aAux
p2m_reactivate "P2MW.S_AlgebraicGeometry_SmallExtension_mem_pointDerivations_tangentCoords_and_injective_and_surjective.I4aAux"

theorem solution
    {T' : Type u} [CommRing T'] [IsLocalRing T']
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
    [IsCentralScalar (ResidueField T') V] [Module.Finite (ResidueField T') V]
    [Module T' V] [IsScalarTower T' (ResidueField T') V]
    (C : Type u) [CommRing C] [Algebra T' C]
    {Ak : Scheme.{u}} (xk : Ak ⟶ Spec (CommRingCat.of (ResidueField T')))
    (pt : Spec (CommRingCat.of (ResidueField T')) ⟶ Ak) (hpt : pt ≫ xk = 𝟙 _)
    (Ue : Ak.Opens) (hUe : IsAffineOpen Ue)
    (e₁ : Spec (CommRingCat.of (ResidueField T')) ⟶ (Ue : Scheme.{u})) (he₁ : e₁ ≫ Ue.ι = pt) :
    letI := algebraOfHom xk Ue
    (∀ w₁ : Spec (CommRingCat.of (thickening T' V C)) ⟶ (Ue : Scheme.{u}),
        (w₁ ≫ Ue.ι) ≫ xk = RelTangentPoints.base V (thickeningSnd T' V C) →
        SquareZero.zeroSection V (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C) (thickening_isPullback V C)
            ≫ w₁ ≫ Ue.ι = reductionBase T' C ≫ pt →
        ∃ D : ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak, Ue)
                ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom)
                (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] C))),
          ∀ a, D.1 a = tangentCoords T' V C (chartRingHom V C Ue w₁) a) ∧
    (∀ w₁ w₁' : Spec (CommRingCat.of (thickening T' V C)) ⟶ (Ue : Scheme.{u}),
        (w₁ ≫ Ue.ι) ≫ xk = RelTangentPoints.base V (thickeningSnd T' V C) →
        SquareZero.zeroSection V (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C) (thickening_isPullback V C)
            ≫ w₁ ≫ Ue.ι = reductionBase T' C ≫ pt →
        (w₁' ≫ Ue.ι) ≫ xk = RelTangentPoints.base V (thickeningSnd T' V C) →
        SquareZero.zeroSection V (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C) (thickening_isPullback V C)
            ≫ w₁' ≫ Ue.ι = reductionBase T' C ≫ pt →
        tangentCoords T' V C (chartRingHom V C Ue w₁) = tangentCoords T' V C (chartRingHom V C Ue w₁') → w₁ = w₁') ∧
    (∀ D : ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak, Ue)
                ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom)
                (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] C))),
        ∃ w₁ : Spec (CommRingCat.of (thickening T' V C)) ⟶ (Ue : Scheme.{u}),
          (w₁ ≫ Ue.ι) ≫ xk = RelTangentPoints.base V (thickeningSnd T' V C) ∧
          SquareZero.zeroSection V (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C) (thickening_isPullback V C)
              ≫ w₁ ≫ Ue.ι = reductionBase T' C ≫ pt ∧
          ∀ a, D.1 a = tangentCoords T' V C (chartRingHom V C Ue w₁) a) := by
  letI instA : Algebra (ResidueField T') Γ(Ak, Ue) := algebraOfHom xk Ue
  classical

  have hB0 : ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom).comp (algebraMap (ResidueField T') Γ(Ak, Ue)) = RingHom.id _ :=
    I4aAux.ev_comp_algebraMap xk Ue pt hpt e₁ he₁
  have hB1 : ∀ φ : Γ(Ak, Ue) →+* (thickening T' V C), ∃ w₁ : Spec (CommRingCat.of (thickening T' V C)) ⟶ (Ue : Scheme.{u}), chartRingHom V C Ue w₁ = φ := by
    intro φ
    obtain ⟨g, hg⟩ := I4aAux.chart_surj Ue hUe (CommRingCat.ofHom (R := Γ(Ak, Ue)) (S := (thickening T' V C)) φ)
    exact ⟨g, congrArg CommRingCat.Hom.hom hg⟩
  have hB2 : ∀ w₁ w₁' : Spec (CommRingCat.of (thickening T' V C)) ⟶ (Ue : Scheme.{u}), chartRingHom V C Ue w₁ = chartRingHom V C Ue w₁' → w₁ = w₁' :=
    fun w₁ w₁' h => I4aAux.chart_inj Ue hUe w₁ w₁' (CommRingCat.hom_ext h)
  have hB3 : ∀ w₁ : Spec (CommRingCat.of (thickening T' V C)) ⟶ (Ue : Scheme.{u}),
      (w₁ ≫ Ue.ι) ≫ xk = RelTangentPoints.base V (thickeningSnd T' V C) ↔
        ∀ c : (ResidueField T'), chartRingHom V C Ue w₁ (algebraMap (ResidueField T') Γ(Ak, Ue) c) = (algebraMap (ResidueField T') (ResidueField T' ⊗[T'] C) c) ⊗ₜ[(ResidueField T')] (1 : TrivSqZeroExt (ResidueField T') V) := by
    intro w₁
    rw [I4aAux.base_eq V C]
    constructor
    · intro h c
      rw [← Algebra.TensorProduct.algebraMap_apply]
      exact I4aAux.chart_algebraMap_of_over xk Ue w₁ _ h c
    · intro h
      apply I4aAux.over_of_chart_algebraMap xk Ue w₁
      intro c
      rw [Algebra.TensorProduct.algebraMap_apply]
      exact h c
  have hB4 : ∀ w₁ : Spec (CommRingCat.of (thickening T' V C)) ⟶ (Ue : Scheme.{u}),
      SquareZero.zeroSection V (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C) (thickening_isPullback V C)
            ≫ w₁ ≫ Ue.ι = reductionBase T' C ≫ pt ↔
        ∀ a, I4aAux.aug (ResidueField T') (ResidueField T' ⊗[T'] C) V (chartRingHom V C Ue w₁ a) =
          algebraMap (ResidueField T') (ResidueField T' ⊗[T'] C) ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom a) := by
    intro w₁
    rw [I4aAux.zeroSection_comp_iff V C Ue hUe pt e₁ he₁ w₁]
    exact ⟨fun h a => RingHom.congr_fun h a, fun h => RingHom.ext h⟩

  have htc : ∀ (φ : Γ(Ak, Ue) →+* (thickening T' V C)) (a : Γ(Ak, Ue)),
      tangentCoords T' V C φ a = tensorToDualHom (ResidueField T') (ResidueField T' ⊗[T'] C) V (I4aAux.vP (ResidueField T') (ResidueField T' ⊗[T'] C) V (φ a)) := fun φ a => rfl
  refine ⟨?_, ?_, ?_⟩
  ·
    intro w₁ hk hz
    have hφk := (hB3 w₁).1 hk
    have hφ0 := (hB4 w₁).1 hz
    have hφk' := hφk
    have hφ0' := hφ0
    refine ⟨⟨{ toFun := fun a => tangentCoords T' V C (chartRingHom V C Ue w₁) a
               map_add' := fun a b => tangentCoords_add V C _ a b
               map_smul' := fun c a => ?_ }, ?_⟩, fun a => rfl⟩
    · rw [htc, htc, Algebra.smul_def, (chartRingHom V C Ue w₁).map_mul, hφk', ← Algebra.TensorProduct.algebraMap_apply, ← Algebra.smul_def, LinearMap.map_smul,
        LinearMap.map_smul, RingHom.id_apply]
    · intro a b
      show tangentCoords T' V C (chartRingHom V C Ue w₁) (a * b) = _
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [htc, htc, htc, (chartRingHom V C Ue w₁).map_mul, I4aAux.vP_mul, hφ0', hφ0', algebraMap_smul, algebraMap_smul, map_add, LinearMap.map_smul,
        LinearMap.map_smul]
  ·
    intro w₁ w₁' hk hz hk' hz' hcoords
    apply hB2
    have hφ0 := (hB4 w₁).1 hz
    have hφ0' := (hB4 w₁').1 hz'
    refine RingHom.ext fun a => ?_
    have h1 : I4aAux.vP (ResidueField T') (ResidueField T' ⊗[T'] C) V (chartRingHom V C Ue w₁ a) = I4aAux.vP (ResidueField T') (ResidueField T' ⊗[T'] C) V (chartRingHom V C Ue w₁' a) := by
      apply I4aAux.tTDH_injective (ResidueField T') (ResidueField T' ⊗[T'] C) V
      rw [← htc, ← htc, hcoords]
    have h2 : I4aAux.aug (ResidueField T') (ResidueField T' ⊗[T'] C) V (chartRingHom V C Ue w₁ a) = I4aAux.aug (ResidueField T') (ResidueField T' ⊗[T'] C) V (chartRingHom V C Ue w₁' a) := by
      rw [hφ0 a, hφ0' a]
    rw [I4aAux.decomp (chartRingHom V C Ue w₁ a), I4aAux.decomp (chartRingHom V C Ue w₁' a), h1, h2]
  ·
    intro D
    obtain ⟨w₁, hw₁⟩ := hB1 (I4aAux.derivHom (ResidueField T') (ResidueField T' ⊗[T'] C) V _ D.1 D.2)
    refine ⟨w₁, (hB3 w₁).2 ?_, (hB4 w₁).2 ?_, fun a => ?_⟩
    · intro c
      rw [hw₁, I4aAux.derivHom_apply]
      have h1 : ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom) (algebraMap (ResidueField T') Γ(Ak, Ue) c) = c :=
        RingHom.congr_fun hB0 c
      have h2 : D.1 (algebraMap (ResidueField T') Γ(Ak, Ue) c) = 0 := by
        rw [Algebra.algebraMap_eq_smul_one, LinearMap.map_smul, Algebra.PointDerivations.apply_one D.2, smul_zero]
      rw [h1, h2, map_zero, map_zero, add_zero]
    · intro a
      rw [hw₁]
      exact I4aAux.aug_derivHom (ResidueField T') (ResidueField T' ⊗[T'] C) V _ D.1 D.2 a
    · rw [hw₁, htc, I4aAux.vP_derivHom, I4aAux.tTDH_tInv]

end S_AlgebraicGeometry_SmallExtension_mem_pointDerivations_tangentCoords_and_injective_and_surjective
end P2MW
export P2MW.S_AlgebraicGeometry_SmallExtension_mem_pointDerivations_tangentCoords_and_injective_and_surjective (solution)
