-- Prove2me | solution 1 for AlgebraicGeometry.SplitTorus.existsUnique_muLift_of_torusFibre_of_henselian
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/ab2d6216-af7a-5073-bc8c-8b16021eff9d

import Mathlib
import Definitions.Def_AlgebraicGeometry_SplitTorusMu
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_hopfAlgebra_finitePart_schemeKer_of_henselianLocalRing
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_schemeKerStr_props_of_schemeNsmul
import Theorems.Thm_HopfAlgebra_existsUnique_bialgHom_addMonoidAlgebra_lift_residueField_of_henselianLocalRing
import Theorems.Thm_Bialgebra_exists_bialgHom_coe_eq_of_comp_convMul
import Theorems.Thm_AddMonoidAlgebra_surjective_of_surjective_residueField_comp
import Theorems.Thm_AlgebraicGeometry_SplitTorus_forall_torusPt_mul_of_torusPtId_mul_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_SplitTorus_convPow_eq_one_and_comp_mapDomain_convMul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SplitTorus_existsUnique_muLift_of_torusFibre_of_henselian
p2m_attr_erase "instance" "MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange instIsScalarTowerTensorProduct_definitions CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra"
p2m_attr_erase "simp" "GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply HopfAlgebra.mem_vanishingIdealOfPoints_iff HopfAlgebra.liftPoint_mk HopfAlgebra.mem_ptSet_iff CartierDual.dualBaseChangeLin_tmul CartierDual.dualBaseChange_tmul mem_flatClosure_iff"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.SplitTorus IsLocalRing

open scoped TensorProduct

namespace TLGenPlumbing

theorem baseChange_convMul_comp_includeRight
    {R : Type u} [CommRing R] {S : Type u} [CommRing S] [Algebra R S]
    {H : Type u} [CommRing H] [Bialgebra R H] {T : Type u} [CommRing T] [Algebra S T]
    [Algebra R T] [IsScalarTower R S T]
    (f g : WithConv (S ⊗[R] H →ₐ[S] T)) :
    ((f * g).ofConv.restrictScalars R).comp (Algebra.TensorProduct.includeRight) =
      (WithConv.toConv ((f.ofConv.restrictScalars R).comp Algebra.TensorProduct.includeRight) *
        WithConv.toConv ((g.ofConv.restrictScalars R).comp Algebra.TensorProduct.includeRight)).ofConv := by
  apply AlgHom.ext
  intro h
  classical
  let ℛ := Coalgebra.Repr.arbitrary R h
  simp only [AlgHom.coe_comp, AlgHom.coe_restrictScalars', Function.comp_apply,
    Algebra.TensorProduct.includeRight_apply, AlgHom.convMul_apply, TensorProduct.comul_tmul,
    CommSemiring.comul_apply]
  rw [← ℛ.eq]
  simp only [TensorProduct.tmul_sum, map_sum, TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul,
    Algebra.TensorProduct.lift_tmul, AlgHom.coe_comp, AlgHom.coe_restrictScalars', Function.comp_apply,
    Algebra.TensorProduct.includeRight_apply]

theorem baseChange_convOne_comp_includeRight
    {R : Type u} [CommRing R] {S : Type u} [CommRing S] [Algebra R S]
    {H : Type u} [CommRing H] [Bialgebra R H] {T : Type u} [CommRing T] [Algebra S T]
    [Algebra R T] [IsScalarTower R S T] :
    ((1 : WithConv (S ⊗[R] H →ₐ[S] T)).ofConv.restrictScalars R).comp (Algebra.TensorProduct.includeRight) =
      (1 : WithConv (H →ₐ[R] T)).ofConv := by
  apply AlgHom.ext
  intro h
  simp only [AlgHom.coe_comp, AlgHom.coe_restrictScalars', Function.comp_apply,
    Algebra.TensorProduct.includeRight_apply, AlgHom.convOne_apply, TensorProduct.counit_tmul,
    CommSemiring.counit_apply]
  simp [Algebra.smul_def, ← IsScalarTower.algebraMap_apply]

theorem surjective_of_isClosedImmersion_specMap {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    [IsClosedImmersion (Spec.map (CommRingCat.ofHom φ))] :
    Function.Surjective φ := by
  have h := (IsClosedImmersion.isAffine_surjective_of_isAffine (Spec.map (CommRingCat.ofHom φ))).2
  have hn := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  have : (CommRingCat.ofHom φ) = (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
      Scheme.Hom.appTop (Spec.map (CommRingCat.ofHom φ)) ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom := by
    rw [hn, Iso.inv_hom_id_assoc]
  have hφ : (φ : A → B) = (CommRingCat.Hom.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
      Scheme.Hom.appTop (Spec.map (CommRingCat.ofHom φ)) ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom)) := by
    rw [← this]; rfl
  rw [hφ]
  simp only [CommRingCat.hom_comp, RingHom.coe_comp]
  exact (ConcreteCategory.bijective_of_isIso _).2.comp (h.comp (ConcreteCategory.bijective_of_isIso _).2)

end TLGenPlumbing

theorem TLGenPlumbing.plumbing1
    {R : Type u} [CommRing R] [IsLocalRing R] [IsAlgClosed (ResidueField R)]
    {G : Scheme.{u}} (g : G ⟶ Spec (CommRingCat.of R)) [IsSeparated g]
    (L : RelativeGroupLaw R g)
    (t : ℕ)
    (τ : SchemeHomOver (torusStr (ResidueField R) t)
      (RelativeGroupLaw.baseChangeStr (Spec.map (CommRingCat.ofHom (residue R))) g))
    (hτ : IsClosedImmersion τ.1)
    (hτmul : ∀ χ χ' : WithConv (torusCoord (ResidueField R) t →ₐ[ResidueField R] ResidueField R),
      NeronModelInfra.schemeHomOverComp (torusPtId (ResidueField R) t (χ * χ').ofConv) τ =
        (L.baseChange (Spec.map (CommRingCat.ofHom (residue R)))).mul _
          (NeronModelInfra.schemeHomOverComp (torusPtId (ResidueField R) t χ.ofConv) τ)
          (NeronModelInfra.schemeHomOverComp (torusPtId (ResidueField R) t χ'.ofConv) τ))
    (m : ℕ) (hm : 0 < m)
    (H : Type u) [CommRing H] [HopfAlgebra R H]
    (j : Spec (CommRingCat.of H) ⟶ L.schemeKer m)
    (e : ∀ (T : Type u) [CommRing T] [Algebra R T],
          WithConv (H →ₐ[R] T) → L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R T))) m)
    [IsClosedImmersion j]
    [IsClosedImmersion (pullback.fst (L.schemeNsmul m) (L.one (𝟙 (Spec (CommRingCat.of R)))).1)]
    (hej : ∀ (T : Type u) [CommRing T] [Algebra R T] (φ : WithConv (H →ₐ[R] T)),
          ((e T φ).val : SchemeHomOver _ g).1 =
            Spec.map (CommRingCat.ofHom φ.ofConv.toRingHom) ≫ j ≫
              pullback.fst (L.schemeNsmul m) (L.one (𝟙 (Spec (CommRingCat.of R)))).1)
    (heinj : ∀ (T : Type u) [CommRing T] [Algebra R T], Function.Injective (e T))
    (hesurj : ∀ (T : Type u) [CommRing T] [Algebra R T] [Module.Finite R T], Function.Surjective (e T))
    (hemul : ∀ (T : Type u) [CommRing T] [Algebra R T] (φ ψ : WithConv (H →ₐ[R] T)),
          ((e T (φ * ψ)).val : SchemeHomOver _ g) = L.mul _ (e T φ).val (e T ψ).val)
    (henat : ∀ (T T' : Type u) [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']
            (a : T →ₐ[R] T') (φ : WithConv (H →ₐ[R] T)),
          ((e T' (.toConv (a.comp φ.ofConv))).val : SchemeHomOver _ g).1 =
            Spec.map (CommRingCat.ofHom a.toRingHom) ≫ (e T φ).val.1) :
    ∃ ψ₀ : ResidueField R ⊗[R] H →ₐc[ResidueField R] AddMonoidAlgebra (ResidueField R) (Fin t → ZMod m),
      Function.Surjective ψ₀ ∧
      Spec.map (CommRingCat.ofHom (((ψ₀ : ResidueField R ⊗[R] H →ₐ[ResidueField R] _).restrictScalars R).comp
          (Algebra.TensorProduct.includeRight (R := R) (A := ResidueField R) (B := H))).toRingHom) ≫ j ≫
        pullback.fst (L.schemeNsmul m) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 =
      muToTorus (ResidueField R) t m ≫ τ.1 ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (residue R))) := by
  classical
  haveI : NeZero m := ⟨Nat.pos_iff_ne_zero.mp hm⟩
  haveI : Module.Finite R (muCoord (ResidueField R) t m) :=
    Module.Finite.trans (ResidueField R) (muCoord (ResidueField R) t m)

  obtain ⟨md, hmd⟩ : ∃ md : torusCoord (ResidueField R) t →ₐ[ResidueField R] muCoord (ResidueField R) t m,
      md = AddMonoidAlgebra.mapDomainAlgHom (ResidueField R) (ResidueField R)
        (AddMonoidHom.pi fun i => (Int.castAddHom (ZMod m)).comp (Pi.evalAddMonoidHom (fun _ : Fin t => ℤ) i)) :=
    ⟨_, rfl⟩
  have hmu : muToTorus (ResidueField R) t m = Spec.map (CommRingCat.ofHom md.toRingHom) := by rw [hmd]; rfl

  have hbase : ∀ (T : Type u) [CommRing T] [Algebra R T] [Algebra (ResidueField R) T]
      [IsScalarTower R (ResidueField R) T],
      𝟙 (Spec (CommRingCat.of T)) ≫ (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField R) T)) ≫
        Spec.map (CommRingCat.ofHom (residue R))) = Spec.map (CommRingCat.ofHom (algebraMap R T)) := by
    intro T _ _ _ _
    rw [Category.id_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact (IsScalarTower.algebraMap_eq R (ResidueField R) T).symm

  let Y : ∀ (T : Type u) [CommRing T] [Algebra R T] [Algebra (ResidueField R) T] [IsScalarTower R (ResidueField R) T],
      WithConv (muCoord (ResidueField R) t m →ₐ[ResidueField R] T) →
        SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R T))) g :=
    fun T _ _ _ _ θ => GoodReductionJacobian.schemeHomOverComp (𝟙 _) (hbase T)
      (RelativeGroupLaw.baseChangePointToBase (Spec.map (CommRingCat.ofHom (residue R)))
        (NeronModelInfra.schemeHomOverComp (torusPt (ResidueField R) T t (θ.ofConv.comp md)) τ))
  have hY1 : ∀ (T : Type u) [CommRing T] [Algebra R T] [Algebra (ResidueField R) T] [IsScalarTower R (ResidueField R) T]
      (θ : WithConv (muCoord (ResidueField R) t m →ₐ[ResidueField R] T)),
      (Y T θ).1 = Spec.map (CommRingCat.ofHom θ.ofConv.toRingHom) ≫ muToTorus (ResidueField R) t m ≫ τ.1 ≫
        pullback.fst g (Spec.map (CommRingCat.ofHom (residue R))) := by
    intro T _ _ _ _ θ
    simp only [Y, GoodReductionJacobian.schemeHomOverComp_coe, RelativeGroupLaw.baseChangePointToBase_coe,
      NeronModelInfra.schemeHomOverComp_coe, Category.id_comp, Category.assoc, hmu, torusPt]
    rw [show (θ.ofConv.comp md).toRingHom = θ.ofConv.toRingHom.comp md.toRingHom from rfl,
      CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  have hYmul : ∀ (T : Type u) [CommRing T] [Algebra R T] [Algebra (ResidueField R) T] [IsScalarTower R (ResidueField R) T]
      (θ θ' : WithConv (muCoord (ResidueField R) t m →ₐ[ResidueField R] T)),
      Y T (θ * θ') = L.mul _ (Y T θ) (Y T θ') := by
    intro T _ _ _ _ θ θ'
    have h3 := (AlgebraicGeometry.SplitTorus.convPow_eq_one_and_comp_mapDomain_convMul (ResidueField R) T t m).2.1 θ θ'
    rw [← hmd] at h3
    have h3' : (θ * θ').ofConv.comp md =
        (WithConv.toConv (θ.ofConv.comp md) * WithConv.toConv (θ'.ofConv.comp md)).ofConv :=
      congrArg WithConv.ofConv h3
    have hL2 := AlgebraicGeometry.SplitTorus.forall_torusPt_mul_of_torusPtId_mul_of_isAlgClosed
      (RelativeGroupLaw.baseChangeStr (Spec.map (CommRingCat.ofHom (residue R))) g)
      (L.baseChange (Spec.map (CommRingCat.ofHom (residue R)))) t τ hτmul T
      (WithConv.toConv (θ.ofConv.comp md)) (WithConv.toConv (θ'.ofConv.comp md))
    simp only [Y]
    rw [h3', hL2, RelativeGroupLaw.baseChangePointToBase_mul, L.mul_natural]
  have hYone : ∀ (T : Type u) [CommRing T] [Algebra R T] [Algebra (ResidueField R) T] [IsScalarTower R (ResidueField R) T],
      Y T 1 = L.one _ := by
    intro T _ _ _ _
    have h := hYmul T 1 1
    rw [one_mul] at h
    calc Y T 1 = L.mul _ (L.one _) (Y T 1) := (L.one_mul _ _).symm
      _ = L.mul _ (L.mul _ (L.inv _ (Y T 1)) (Y T 1)) (Y T 1) := by rw [L.inv_mul_cancel]
      _ = L.mul _ (L.inv _ (Y T 1)) (L.mul _ (Y T 1) (Y T 1)) := L.mul_assoc _ _ _ _
      _ = L.mul _ (L.inv _ (Y T 1)) (Y T 1) := by rw [← h]
      _ = L.one _ := L.inv_mul_cancel _ _
  have hYpow : ∀ (T : Type u) [CommRing T] [Algebra R T] [Algebra (ResidueField R) T] [IsScalarTower R (ResidueField R) T]
      (θ : WithConv (muCoord (ResidueField R) t m →ₐ[ResidueField R] T)) (k : ℕ),
      L.nsmul _ k (Y T θ) = Y T (θ ^ k) := by
    intro T _ _ _ _ θ k
    induction k with
    | zero => rw [pow_zero, hYone, RelativeGroupLaw.nsmul_zero]
    | succ k ih => rw [RelativeGroupLaw.nsmul_succ, ih, pow_succ, hYmul]

  have hPtors : Y (muCoord (ResidueField R) t m) (WithConv.toConv (AlgHom.id (ResidueField R) _)) ∈
      L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R (muCoord (ResidueField R) t m)))) m := by
    rw [RelativeGroupLaw.mem_torsionSubset, RelativeGroupLaw.isTorsionPoint_def, hYpow,
      (AlgebraicGeometry.SplitTorus.convPow_eq_one_and_comp_mapDomain_convMul (ResidueField R)
        (muCoord (ResidueField R) t m) t m).1, hYone]
  obtain ⟨φ₀, hφ₀⟩ := hesurj (muCoord (ResidueField R) t m) ⟨_, hPtors⟩
  have hid : Spec.map (CommRingCat.ofHom
      (WithConv.toConv (AlgHom.id (ResidueField R) (muCoord (ResidueField R) t m))).ofConv.toRingHom) = 𝟙 _ := by
    exact Spec.map_id _
  have hP1 : ((e (muCoord (ResidueField R) t m) φ₀).val : SchemeHomOver _ g).1 =
      muToTorus (ResidueField R) t m ≫ τ.1 ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (residue R))) := by
    rw [hφ₀]; dsimp only; rw [hY1, hid, Category.id_comp]

  have heY : ∀ (T : Type u) [CommRing T] [Algebra R T] [Algebra (ResidueField R) T] [IsScalarTower R (ResidueField R) T]
      (θ : WithConv (muCoord (ResidueField R) t m →ₐ[ResidueField R] T)),
      ((e T (WithConv.toConv ((θ.ofConv.restrictScalars R).comp φ₀.ofConv))).val : SchemeHomOver _ g) = Y T θ := by
    intro T _ _ _ _ θ
    apply Subtype.ext
    rw [henat, hP1, hY1]
    rfl
  have hφ₀mul : ∀ (T : Type u) [CommRing T] [Algebra R T] [Algebra (ResidueField R) T] [IsScalarTower R (ResidueField R) T]
      (θ θ' : WithConv (muCoord (ResidueField R) t m →ₐ[ResidueField R] T)),
      WithConv.toConv (((θ * θ').ofConv.restrictScalars R).comp φ₀.ofConv) =
        WithConv.toConv ((θ.ofConv.restrictScalars R).comp φ₀.ofConv) *
          WithConv.toConv ((θ'.ofConv.restrictScalars R).comp φ₀.ofConv) := by
    intro T _ _ _ _ θ θ'
    apply heinj T
    apply Subtype.ext
    rw [hemul, heY, heY, heY, hYmul]
  have hφ₀one : ∀ (T : Type u) [CommRing T] [Algebra R T] [Algebra (ResidueField R) T] [IsScalarTower R (ResidueField R) T],
      WithConv.toConv (((1 : WithConv (muCoord (ResidueField R) t m →ₐ[ResidueField R] T)).ofConv.restrictScalars R).comp
        φ₀.ofConv) = (1 : WithConv (H →ₐ[R] T)) := by
    intro T _ _ _ _
    apply heinj T
    apply Subtype.ext
    rw [heY, hYone]

    have h1 := hemul T 1 1
    rw [one_mul] at h1
    symm
    calc ((e T 1).val : SchemeHomOver _ g) = L.mul _ (L.one _) (e T 1).val := (L.one_mul _ _).symm
      _ = L.mul _ (L.mul _ (L.inv _ (e T 1).val) (e T 1).val) (e T 1).val := by rw [L.inv_mul_cancel]
      _ = L.mul _ (L.inv _ (e T 1).val) (L.mul _ (e T 1).val (e T 1).val) := L.mul_assoc _ _ _ _
      _ = L.mul _ (L.inv _ (e T 1).val) (e T 1).val := by rw [← h1]
      _ = L.one _ := L.inv_mul_cancel _ _

  let ψ : ResidueField R ⊗[R] H →ₐ[ResidueField R] muCoord (ResidueField R) t m :=
    Algebra.TensorProduct.lift (Algebra.ofId (ResidueField R) _) φ₀.ofConv (fun _ _ => Commute.all _ _)
  have hψR : (ψ.restrictScalars R).comp Algebra.TensorProduct.includeRight = φ₀.ofConv :=
    Algebra.TensorProduct.lift_comp_includeRight _ _ _
  have hψc : ∀ (T : Type u) [CommRing T] [Algebra R T] [Algebra (ResidueField R) T] [IsScalarTower R (ResidueField R) T]
      (ξ : muCoord (ResidueField R) t m →ₐ[ResidueField R] T),
      ((ξ.comp ψ).restrictScalars R).comp Algebra.TensorProduct.includeRight = (ξ.restrictScalars R).comp φ₀.ofConv := by
    intro T _ _ _ _ ξ; rw [← hψR]; rfl
  have hψmul : ∀ (T : Type u) [CommRing T] [Algebra (ResidueField R) T]
      (χ χ' : WithConv (muCoord (ResidueField R) t m →ₐ[ResidueField R] T)),
      WithConv.toConv ((χ * χ').ofConv.comp ψ) =
        WithConv.toConv (χ.ofConv.comp ψ) * WithConv.toConv (χ'.ofConv.comp ψ) := by
    intro T _ _ χ χ'
    letI : Algebra R T := ((algebraMap (ResidueField R) T).comp (algebraMap R (ResidueField R))).toAlgebra
    haveI : IsScalarTower R (ResidueField R) T := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    suffices h : (χ * χ').ofConv.comp ψ =
        (WithConv.toConv (χ.ofConv.comp ψ) * WithConv.toConv (χ'.ofConv.comp ψ)).ofConv by
      rw [h, WithConv.toConv_ofConv]
    apply Algebra.TensorProduct.ext
    · exact Subsingleton.elim _ _
    · rw [TLGenPlumbing.baseChange_convMul_comp_includeRight]
      rw [hψc, hψc, hψc]
      exact congrArg WithConv.ofConv (hφ₀mul T χ χ')
  have hψone : ∀ (T : Type u) [CommRing T] [Algebra (ResidueField R) T],
      WithConv.toConv ((1 : WithConv (muCoord (ResidueField R) t m →ₐ[ResidueField R] T)).ofConv.comp ψ) =
        (1 : WithConv (ResidueField R ⊗[R] H →ₐ[ResidueField R] T)) := by
    intro T _ _
    letI : Algebra R T := ((algebraMap (ResidueField R) T).comp (algebraMap R (ResidueField R))).toAlgebra
    haveI : IsScalarTower R (ResidueField R) T := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    suffices h : (1 : WithConv (muCoord (ResidueField R) t m →ₐ[ResidueField R] T)).ofConv.comp ψ =
        (1 : WithConv (ResidueField R ⊗[R] H →ₐ[ResidueField R] T)).ofConv by
      rw [h, WithConv.toConv_ofConv]
    apply Algebra.TensorProduct.ext
    · exact Subsingleton.elim _ _
    · rw [TLGenPlumbing.baseChange_convOne_comp_includeRight, hψc]
      exact congrArg WithConv.ofConv (hφ₀one T)

  obtain ⟨ψ₀, hψ₀⟩ := Bialgebra.exists_bialgHom_coe_eq_of_comp_convMul ψ hψmul hψone
  refine ⟨ψ₀, ?_, ?_⟩
  ·

    have hcl : IsClosedImmersion (Spec.map (CommRingCat.ofHom φ₀.ofConv.toRingHom)) := by
      have hc : Spec.map (CommRingCat.ofHom φ₀.ofConv.toRingHom) ≫
          (j ≫ pullback.fst (L.schemeNsmul m) (L.one (𝟙 (Spec (CommRingCat.of R)))).1) =
          muToTorus (ResidueField R) t m ≫ τ.1 ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (residue R))) := by
        rw [← hP1, hej]
      haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (residue R))) :=
        IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
      haveI : IsClosedImmersion (muToTorus (ResidueField R) t m) :=
        IsClosedImmersion.spec_of_surjective _ (by
          have hg : Function.Surjective
              (AddMonoidHom.pi fun i => (Int.castAddHom (ZMod m)).comp
                (Pi.evalAddMonoidHom (fun _ : Fin t => ℤ) i)) := by
            intro v
            exact ⟨fun i => (v i).val, by ext i; simp⟩
          intro y
          obtain ⟨x, hx⟩ := Finsupp.mapDomain_surjective hg y.coeff
          exact ⟨AddMonoidAlgebra.ofCoeff x, AddMonoidAlgebra.coeff_injective hx⟩)
      haveI : IsClosedImmersion τ.1 := hτ
      haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom φ₀.ofConv.toRingHom) ≫
          (j ≫ pullback.fst (L.schemeNsmul m) (L.one (𝟙 (Spec (CommRingCat.of R)))).1)) := by
        rw [hc]; infer_instance
      exact IsClosedImmersion.of_comp_isClosedImmersion _
        (j ≫ pullback.fst (L.schemeNsmul m) (L.one (𝟙 (Spec (CommRingCat.of R)))).1)
    have hφ₀surj : Function.Surjective φ₀.ofConv :=
      TLGenPlumbing.surjective_of_isClosedImmersion_specMap φ₀.ofConv.toRingHom
    intro y
    obtain ⟨x, hx⟩ := hφ₀surj y
    refine ⟨(1 : ResidueField R) ⊗ₜ[R] x, ?_⟩
    rw [← hx]
    change (ψ₀ : ResidueField R ⊗[R] H →ₐ[ResidueField R] muCoord (ResidueField R) t m) (1 ⊗ₜ[R] x) = _
    rw [hψ₀]
    simp only [ψ, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  ·
    rw [hψ₀, hψR, ← hej, hP1]

theorem solution
    {R : Type u} [CommRing R] [HenselianLocalRing R] [IsAlgClosed (ResidueField R)]
    {G : Scheme.{u}} (g : G ⟶ Spec (CommRingCat.of R)) [Smooth g] [IsSeparated g] [QuasiCompact g]
    (L : RelativeGroupLaw R g) (hcomm : L.IsCommutative)
    (t : ℕ)
    (τ : SchemeHomOver (torusStr (ResidueField R) t)
      (RelativeGroupLaw.baseChangeStr (Spec.map (CommRingCat.ofHom (residue R))) g))
    (hτ : IsClosedImmersion τ.1)
    (hτmul : ∀ χ χ' : WithConv (torusCoord (ResidueField R) t →ₐ[ResidueField R] ResidueField R),
      NeronModelInfra.schemeHomOverComp (torusPtId (ResidueField R) t (χ * χ').ofConv) τ =
        (L.baseChange (Spec.map (CommRingCat.ofHom (residue R)))).mul _
          (NeronModelInfra.schemeHomOverComp (torusPtId (ResidueField R) t χ.ofConv) τ)
          (NeronModelInfra.schemeHomOverComp (torusPtId (ResidueField R) t χ'.ofConv) τ))
    (m : ℕ) (hm : 0 < m) (hqf : LocallyQuasiFinite (L.schemeNsmul m)) (hfl : Flat (L.schemeNsmul m)) :
    ∃ ι : SchemeHomOver (muStr R t m) g,
      (IsClosedImmersion ι.1 ∧
      (∀ (S : Type u) [CommRing S] [Algebra R S] (χ χ' : WithConv (muCoord R t m →ₐ[R] S)),
        NeronModelInfra.schemeHomOverComp (muPt R S t m (χ * χ').ofConv) ι =
          L.mul _ (NeronModelInfra.schemeHomOverComp (muPt R S t m χ.ofConv) ι)
            (NeronModelInfra.schemeHomOverComp (muPt R S t m χ'.ofConv) ι)) ∧
      (muBaseChange (residue R) t m ≫ ι.1 =
        muToTorus (ResidueField R) t m ≫ τ.1 ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (residue R))))) ∧
      ∀ ι' : SchemeHomOver (muStr R t m) g,
        (∀ (S : Type u) [CommRing S] [Algebra R S] (χ χ' : WithConv (muCoord R t m →ₐ[R] S)),
        NeronModelInfra.schemeHomOverComp (muPt R S t m (χ * χ').ofConv) ι' =
          L.mul _ (NeronModelInfra.schemeHomOverComp (muPt R S t m χ.ofConv) ι')
            (NeronModelInfra.schemeHomOverComp (muPt R S t m χ'.ofConv) ι')) →
        (muBaseChange (residue R) t m ≫ ι'.1 =
        muToTorus (ResidueField R) t m ≫ τ.1 ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (residue R)))) →
        ι' = ι := by
  classical

  obtain ⟨hlqf, hqc, hflat, hsepK, hunit, hfst, hlft⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.schemeKerStr_props_of_schemeNsmul g L m hqf hfl
  haveI := hlqf; haveI := hqc; haveI := hflat
  haveI : LocallyOfFiniteType g := hlft inferInstance

  obtain ⟨H, instH, instHopf, hfinH, hflH, hcocomm, j, e, hjstr, hjopen, hjclosed, hspecial, hej, heinj, hesurj, hemul, henat⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_hopfAlgebra_finitePart_schemeKer_of_henselianLocalRing
      (f := g) L (fun t x y => hcomm t x y) m
  haveI := hfinH; haveI := hflH; haveI := hcocomm

  have P1 : ∃ ψ₀ : ResidueField R ⊗[R] H →ₐc[ResidueField R] AddMonoidAlgebra (ResidueField R) (Fin t → ZMod m),
      Function.Surjective ψ₀ ∧

      Spec.map (CommRingCat.ofHom (((ψ₀ : ResidueField R ⊗[R] H →ₐ[ResidueField R] _).restrictScalars R).comp
          (Algebra.TensorProduct.includeRight (R := R) (A := ResidueField R) (B := H))).toRingHom) ≫ j ≫
        pullback.fst (L.schemeNsmul m) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 =
      muToTorus (ResidueField R) t m ≫ τ.1 ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (residue R))) := by
    haveI := hjclosed; haveI := hfst
    exact TLGenPlumbing.plumbing1 g L t τ hτ hτmul m hm H j e hej heinj hesurj hemul henat
  obtain ⟨ψ₀, hψ₀surj, hψ₀E⟩ := P1
  haveI : NeZero m := ⟨Nat.pos_iff_ne_zero.mp hm⟩

  obtain ⟨ψ, hψred, hψuniq⟩ :=
    HopfAlgebra.existsUnique_bialgHom_addMonoidAlgebra_lift_residueField_of_henselianLocalRing (Fin t → ZMod m) ψ₀

  have hψsurj : Function.Surjective (ψ : H →ₐ[R] AddMonoidAlgebra R (Fin t → ZMod m)) :=
    AddMonoidAlgebra.surjective_of_surjective_residueField_comp (Fin t → ZMod m)
      (ψ : H →ₐ[R] AddMonoidAlgebra R (Fin t → ZMod m)) (ψ₀ : _ →ₐ[ResidueField R] _) hψ₀surj hψred

  let ι₁ : muScheme R t m ⟶ G :=
    Spec.map (CommRingCat.ofHom (ψ : H →ₐ[R] AddMonoidAlgebra R (Fin t → ZMod m)).toRingHom) ≫ j ≫
      pullback.fst (L.schemeNsmul m) (L.one (𝟙 (Spec (CommRingCat.of R)))).1

  have P2 : ι₁ ≫ g = muStr R t m := by
    have h1 : pullback.fst (L.schemeNsmul m) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ g = L.schemeKerStr m := by
      have h0 : pullback.fst (L.schemeNsmul m) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ g =
          pullback.fst (L.schemeNsmul m) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ (L.schemeNsmul m ≫ g) := by
        rw [L.schemeNsmul_over m]
      rw [h0, ← Category.assoc, pullback.condition, Category.assoc, (L.one (𝟙 _)).2, Category.comp_id]
    simp only [ι₁, Category.assoc, h1]
    rw [hjstr, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact (ψ : H →ₐ[R] AddMonoidAlgebra R (Fin t → ZMod m)).comp_algebraMap
  let ι : SchemeHomOver (muStr R t m) g := ⟨ι₁, P2⟩
  refine ⟨ι, ⟨?_, ?_, ?_⟩, ?_⟩
  ·
    haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (ψ : H →ₐ[R] AddMonoidAlgebra R (Fin t → ZMod m)).toRingHom)) :=
      IsClosedImmersion.spec_of_surjective _ hψsurj
    haveI := hjclosed; haveI := hfst
    change IsClosedImmersion ι₁
    infer_instance
  ·
    intro S _ _ χ χ'
    have key : ∀ θ : muCoord R t m →ₐ[R] S,
        NeronModelInfra.schemeHomOverComp (muPt R S t m θ) ι =
          ((e S (WithConv.toConv (θ.comp (ψ : H →ₐ[R] AddMonoidAlgebra R (Fin t → ZMod m))))).val :
            SchemeHomOver _ g) := by
      intro θ
      apply Subtype.ext
      rw [hej]
      change (muPt R S t m θ).1 ≫ ι₁ = _
      simp only [muPt, ι₁]
      rw [show (θ.comp (ψ : H →ₐ[R] AddMonoidAlgebra R (Fin t → ZMod m))).toRingHom =
          θ.toRingHom.comp (ψ : H →ₐ[R] AddMonoidAlgebra R (Fin t → ZMod m)).toRingHom from rfl,
        CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    rw [key, key, key]
    have hdist := AlgHom.convMul_comp_bialgHom_distrib χ χ' ψ
    rw [hdist, WithConv.toConv_ofConv, hemul]
  ·
    change muBaseChange (residue R) t m ≫ ι₁ = _
    rw [← hψ₀E]
    simp only [ι₁, muBaseChange, ← Category.assoc]
    congr 2
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    have := congrArg AlgHom.toRingHom hψred
    simpa [AlgHom.comp_toRingHom, AddMonoidAlgebra.toRingHom_mapAlgHom] using this
  ·
    intro ι' hhom hspec

    let Φ : ∀ (S : Type u) [CommRing S] [Algebra R S],
        WithConv (muCoord R t m →ₐ[R] S) → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R S))) g :=
      fun S _ _ χ => NeronModelInfra.schemeHomOverComp (muPt R S t m χ.ofConv) ι'
    have hΦmul : ∀ (S : Type u) [CommRing S] [Algebra R S] (χ χ' : WithConv (muCoord R t m →ₐ[R] S)),
        Φ S (χ * χ') = L.mul _ (Φ S χ) (Φ S χ') := fun S _ _ χ χ' => hhom S χ χ'
    have hΦone : ∀ (S : Type u) [CommRing S] [Algebra R S], Φ S 1 = L.one _ := by
      intro S _ _
      have h := hΦmul S 1 1
      rw [one_mul] at h
      calc Φ S 1 = L.mul _ (L.one _) (Φ S 1) := (L.one_mul _ _).symm
        _ = L.mul _ (L.mul _ (L.inv _ (Φ S 1)) (Φ S 1)) (Φ S 1) := by rw [L.inv_mul_cancel]
        _ = L.mul _ (L.inv _ (Φ S 1)) (L.mul _ (Φ S 1) (Φ S 1)) := L.mul_assoc _ _ _ _
        _ = L.mul _ (L.inv _ (Φ S 1)) (Φ S 1) := by rw [← h]
        _ = L.one _ := L.inv_mul_cancel _ _
    have hΦpow : ∀ (S : Type u) [CommRing S] [Algebra R S] (χ : WithConv (muCoord R t m →ₐ[R] S)) (k : ℕ),
        L.nsmul _ k (Φ S χ) = Φ S (χ ^ k) := by
      intro S _ _ χ k
      induction k with
      | zero => rw [pow_zero, hΦone, RelativeGroupLaw.nsmul_zero]
      | succ k ih => rw [RelativeGroupLaw.nsmul_succ, ih, pow_succ, hΦmul]

    have htors : Φ (muCoord R t m) (WithConv.toConv (AlgHom.id R (muCoord R t m))) ∈
        L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R (muCoord R t m)))) m := by
      rw [RelativeGroupLaw.mem_torsionSubset, RelativeGroupLaw.isTorsionPoint_def, hΦpow,
        (AlgebraicGeometry.SplitTorus.convPow_eq_one_and_comp_mapDomain_convMul R (muCoord R t m) t m).1, hΦone]
    haveI : Module.Finite R (muCoord R t m) := by
      exact Module.Finite.equiv (AddMonoidAlgebra.coeffLinearEquiv R).symm
    obtain ⟨φ', hφ'⟩ := hesurj (muCoord R t m) ⟨_, htors⟩

    have hι' : ι'.1 = Spec.map (CommRingCat.ofHom φ'.ofConv.toRingHom) ≫ j ≫
        pullback.fst (L.schemeNsmul m) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
      rw [← hej, hφ']
      change ι'.1 = (muPt R (muCoord R t m) t m (AlgHom.id R (muCoord R t m))).1 ≫ ι'.1
      simp [muPt]

    have heΦ : ∀ (S : Type u) [CommRing S] [Algebra R S] (χ : WithConv (muCoord R t m →ₐ[R] S)),
        ((e S (WithConv.toConv (χ.ofConv.comp φ'.ofConv))).val : SchemeHomOver _ g) = Φ S χ := by
      intro S _ _ χ
      apply Subtype.ext
      rw [henat, hφ']
      change Spec.map (CommRingCat.ofHom χ.ofConv.toRingHom) ≫ (Φ (muCoord R t m) (WithConv.toConv (AlgHom.id R _))).1 = _
      simp only [Φ, NeronModelInfra.schemeHomOverComp, muPt, WithConv.ofConv_toConv]
      simp

    have hφ'mul : ∀ (S : Type u) [CommRing S] [Algebra R S] (χ χ' : WithConv (muCoord R t m →ₐ[R] S)),
        WithConv.toConv ((χ * χ').ofConv.comp φ'.ofConv) =
          WithConv.toConv (χ.ofConv.comp φ'.ofConv) * WithConv.toConv (χ'.ofConv.comp φ'.ofConv) := by
      intro S _ _ χ χ'
      apply heinj S
      apply Subtype.ext
      rw [hemul, heΦ, heΦ, heΦ, hΦmul]
    have hφ'one : ∀ (S : Type u) [CommRing S] [Algebra R S],
        WithConv.toConv ((1 : WithConv (muCoord R t m →ₐ[R] S)).ofConv.comp φ'.ofConv) = (1 : WithConv (H →ₐ[R] S)) := by
      intro S _ _
      apply heinj S
      apply Subtype.ext
      rw [heΦ, hΦone]

      have h1 := hemul S 1 1
      rw [one_mul] at h1
      symm
      calc ((e S 1).val : SchemeHomOver _ g) = L.mul _ (L.one _) (e S 1).val := (L.one_mul _ _).symm
        _ = L.mul _ (L.mul _ (L.inv _ (e S 1).val) (e S 1).val) (e S 1).val := by rw [L.inv_mul_cancel]
        _ = L.mul _ (L.inv _ (e S 1).val) (L.mul _ (e S 1).val (e S 1).val) := L.mul_assoc _ _ _ _
        _ = L.mul _ (L.inv _ (e S 1).val) (e S 1).val := by rw [← h1]
        _ = L.one _ := L.inv_mul_cancel _ _

    obtain ⟨ψ'', hψ''⟩ := Bialgebra.exists_bialgHom_coe_eq_of_comp_convMul φ'.ofConv hφ'mul hφ'one

    have hred'' : (AddMonoidAlgebra.mapAlgHom (Fin t → ZMod m) (Algebra.ofId R (ResidueField R))).comp
          (ψ'' : H →ₐ[R] AddMonoidAlgebra R (Fin t → ZMod m)) =
        ((ψ₀ : ResidueField R ⊗[R] H →ₐ[ResidueField R] AddMonoidAlgebra (ResidueField R) (Fin t → ZMod m)).restrictScalars R).comp
          Algebra.TensorProduct.includeRight := by
      suffices h : WithConv.toConv ((AddMonoidAlgebra.mapAlgHom (Fin t → ZMod m) (Algebra.ofId R (ResidueField R))).comp
          (ψ'' : H →ₐ[R] AddMonoidAlgebra R (Fin t → ZMod m))) =
        WithConv.toConv (((ψ₀ : ResidueField R ⊗[R] H →ₐ[ResidueField R] _).restrictScalars R).comp
          Algebra.TensorProduct.includeRight) from congrArg WithConv.ofConv h
      apply heinj
      apply Subtype.ext
      apply Subtype.ext
      rw [hej, hej, WithConv.ofConv_toConv, WithConv.ofConv_toConv, hψ₀E, ← hspec, hι', hψ'']
      simp only [muBaseChange, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rfl
    have hψeq : ψ'' = ψ := hψuniq ψ'' hred''

    apply Subtype.ext
    rw [hι']
    change _ = ι₁
    simp only [ι₁]
    rw [← hψ'', hψeq]

end S_AlgebraicGeometry_SplitTorus_existsUnique_muLift_of_torusFibre_of_henselian
end P2MW
export P2MW.S_AlgebraicGeometry_SplitTorus_existsUnique_muLift_of_torusFibre_of_henselian (solution)
