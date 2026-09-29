-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.isLocallyFreeOfRank_pushforward_of_isFinite_of_flat_of_locallyTrivialOver
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/05d9c5b5-8f92-5f39-8f4f-526059c3cd0f

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_pushforward_of_forall_exists_isPullback
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isIso_fromTildeGamma_pushforward_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_tilde
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_of_iso
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_pushforward_of_isFinite_of_flat_of_locallyTrivialOver
p2m_attr_erase "simp" "AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app"

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry CategoryTheory.MonoidalCategory Opposite TopologicalSpace TensorProduct"

namespace Ws31X1

open AlgebraicGeometry.Scheme.Modules

section affine

variable {A B : CommRingCat.{u}} (φ : A ⟶ B)

noncomputable def trivCover (X : Scheme.{u}) [IsAffine X] : X.TwoAffineOpenCover where
  U0 := ⊤
  U1 := ⊤
  isAffineOpen_U0 := isAffineOpen_top X
  isAffineOpen_U1 := isAffineOpen_top X
  sup_eq_top := sup_top_eq _
  isAffineOpen_inf := by rw [inf_idem]; exact isAffineOpen_top X

noncomputable abbrev M₀ : (Spec A).Modules :=
  (Scheme.Modules.pushforward (Spec.map φ)).obj (𝟙_ (Spec B).Modules)

noncomputable abbrev P₀ : ModuleCat.{u} A :=
  (modulesSpecToSheaf.obj (M₀ φ)).presheaf.obj (op ⊤)

theorem isIso_fromTildeΓ : IsIso (Scheme.Modules.fromTildeΓ (R := A) (M₀ φ)) := by
  have h := isIso_fromTildeGamma_pushforward_of_locallyTrivial (A := A) (Spec.map φ) (trivCover (Spec B))
    (𝟙_ (Spec B).Modules) (fun x => ⟨⊤, trivial, ⟨pullbackTensorUnitObjIso (⊤ : (Spec B).Opens).ι⟩⟩)
  exact h

def Bmod (_φ : A ⟶ B) : Type u := B
noncomputable scoped instance : CommRing (Bmod φ) := inferInstanceAs (CommRing B)
noncomputable scoped instance algB : Algebra A (Bmod φ) := φ.hom.toAlgebra

lemma algebraMap_Bmod (a : A) : algebraMap A (Bmod φ) a = (φ.hom a : B) := rfl

theorem smul_P₀ (a : A) (s : P₀ φ) :
    (show Γ(Spec B, ⊤) from a • s) = (show Γ(Spec B, ⊤) from (Spec.map φ).appTop ((Scheme.ΓSpecIso A).inv a)) * (show Γ(Spec B, ⊤) from s) := by
  change (show Γ(Spec B, ⊤) from (Spec.map φ).app ⊤ ((Spec A).ringCatSheaf.val.map
      ((Limits.initialOpOfTerminal Limits.isTerminalTop).to (op ⊤)) ((StructureSheaf.globalSectionsIso A).hom a))) *
    (show Γ(Spec B, ⊤) from s) = _
  rw [Subsingleton.elim ((Limits.initialOpOfTerminal Limits.isTerminalTop).to (op (⊤ : (Spec A).Opens))) (𝟙 _),
    CategoryTheory.Functor.map_id]
  rfl

theorem exists_linearEquiv : Nonempty (P₀ φ ≃ₗ[A] Bmod φ) := by
  have hnat : ∀ a : A, (Scheme.ΓSpecIso B).hom ((Spec.map φ).appTop ((Scheme.ΓSpecIso A).inv a)) = φ.hom a := by
    intro a
    have h := CategoryTheory.ConcreteCategory.congr_hom (Scheme.ΓSpecIso_naturality φ) ((Scheme.ΓSpecIso A).inv a)
    change (Scheme.ΓSpecIso B).hom ((Spec.map φ).appTop ((Scheme.ΓSpecIso A).inv a))
      = φ.hom ((Scheme.ΓSpecIso A).hom ((Scheme.ΓSpecIso A).inv a)) at h
    rw [Iso.inv_hom_id_apply] at h
    exact h
  refine ⟨{ toFun := fun s => (show Bmod φ from (Scheme.ΓSpecIso B).hom (show Γ(Spec B, ⊤) from s))
            invFun := fun b => (show P₀ φ from (show Γ(Spec B, ⊤) from (Scheme.ΓSpecIso B).inv (show B from b)))
            map_add' := fun s s' => by
              change (Scheme.ΓSpecIso B).hom ((show Γ(Spec B, ⊤) from s) + (show Γ(Spec B, ⊤) from s')) = _
              rw [map_add]
              all_goals rfl
            map_smul' := fun a s => by
              change (Scheme.ΓSpecIso B).hom (show Γ(Spec B, ⊤) from a • s) = φ.hom a * (Scheme.ΓSpecIso B).hom _
              rw [smul_P₀, map_mul, hnat]
            left_inv := fun s => by
              change (show P₀ φ from (show Γ(Spec B, ⊤) from
                (Scheme.ΓSpecIso B).inv ((Scheme.ΓSpecIso B).hom (show Γ(Spec B, ⊤) from s)))) = s
              rw [Iso.hom_inv_id_apply]
              all_goals rfl
            right_inv := fun b => by
              change (Scheme.ΓSpecIso B).hom ((Scheme.ΓSpecIso B).inv b) = b
              rw [Iso.inv_hom_id_apply] }⟩

theorem finite_Bmod [IsFinite (Spec.map φ)] : Module.Finite A (Bmod φ) := by
  have h : φ.hom.Finite := (IsFinite.SpecMap_iff φ).mp inferInstance
  exact h

theorem flat_Bmod [Flat (Spec.map φ)] : Module.Flat A (Bmod φ) := by
  have h : φ.hom.Flat := Flat.SpecMap_iff.mp inferInstance
  exact h

theorem finitePresentation_Bmod [IsFinite (Spec.map φ)] [LocallyOfFinitePresentation (Spec.map φ)] :
    Module.FinitePresentation A (Bmod φ) := by
  have h : φ.hom.FinitePresentation := (LocallyOfFinitePresentation.SpecMap_iff φ).mp inferInstance
  haveI : Algebra.FinitePresentation A (Bmod φ) := h
  haveI := finite_Bmod φ
  exact Module.FinitePresentation.of_finite_of_finitePresentation A (Bmod φ)

theorem finrank_Bmod [IsFinite (Spec.map φ)] [Flat (Spec.map φ)] (n : ℕ)
    (hn : ∀ p : Spec A, (Spec.map φ).finrank p = n)
    (K : Type u) [Field K] [Algebra A K] : Module.finrank K (K ⊗[A] Bmod φ) = n := by
  haveI := finite_Bmod φ
  haveI := flat_Bmod φ

  let I : Ideal A := RingHom.ker (algebraMap A K)
  haveI hI : I.IsPrime := RingHom.ker_isPrime _

  have hrk : Module.rankAtStalk (R := A) (Bmod φ) ⟨I, hI⟩ = n := by
    have h1 := hn ⟨I, hI⟩
    rw [Scheme.Hom.finrank_SpecMap_eq_finrank ((IsFinite.SpecMap_iff φ).mp inferInstance)
      (Flat.SpecMap_iff.mp inferInstance)] at h1
    exact h1

  let ψ : I.ResidueField →+* K := Ideal.ResidueField.lift I (algebraMap A K) le_rfl (by
    intro a ha
    simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff]
    exact isUnit_iff_ne_zero.mpr (fun h0 => ha (by simpa [I, RingHom.mem_ker] using h0)))
  letI : Algebra I.ResidueField K := ψ.toAlgebra
  haveI : IsScalarTower A I.ResidueField K := IsScalarTower.of_algebraMap_eq (fun a =>
    (Ideal.ResidueField.lift_algebraMap I (algebraMap A K) le_rfl _ a).symm)
  let e : K ⊗[A] Bmod φ ≃ₗ[K] K ⊗[I.ResidueField] (I.ResidueField ⊗[A] Bmod φ) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange A I.ResidueField K K (Bmod φ)).symm
  rw [e.finrank_eq, Module.finrank_baseChange, Ideal.finrank_fiber_eq_rankAtStalk, hrk]

theorem core [IsFinite (Spec.map φ)] [Flat (Spec.map φ)] [LocallyOfFinitePresentation (Spec.map φ)]
    (n : ℕ) (hn : ∀ p : Spec A, (Spec.map φ).finrank p = n) :
    IsLocallyFreeOfRank n (M₀ φ) := by
  obtain ⟨e⟩ := exists_linearEquiv φ
  haveI := finite_Bmod φ
  haveI := flat_Bmod φ
  haveI := finitePresentation_Bmod φ
  haveI : Module.Projective A (Bmod φ) := Module.Flat.projective_of_finitePresentation
  haveI : Module.Finite A (P₀ φ) := Module.Finite.equiv e.symm
  haveI : Module.Projective A (P₀ φ) := Module.Projective.of_equiv e.symm
  have hP : IsLocallyFreeOfRank n (tilde (P₀ φ)) := by
    refine isLocallyFreeOfRank_tilde (P₀ φ) n fun K _ _ => ?_
    rw [← finrank_Bmod φ n hn K]
    exact LinearEquiv.finrank_eq (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl K K) e)
  haveI := isIso_fromTildeΓ φ
  exact IsLocallyFreeOfRank.of_iso (asIso (Scheme.Modules.fromTildeΓ (R := A) (M₀ φ))) hP

end affine

noncomputable def restrictTriv {Z : Scheme.{u}} {N : Z.Modules} {U₀ U : Z.Opens} (h : U ≤ U₀)
    (e : (Scheme.Modules.pullback U₀.ι).obj N ≅ 𝟙_ (U₀ : Scheme.{u}).Modules) :
    (Scheme.Modules.pullback U.ι).obj N ≅ 𝟙_ (U : Scheme.{u}).Modules :=
  (pullbackCongr (Z.homOfLE_ι h).symm).app N ≪≫
    ((pullbackComp (Z.homOfLE h) U₀.ι).app N).symm ≪≫
    (Scheme.Modules.pullback (Z.homOfLE h)).mapIso e ≪≫
    pullbackTensorUnitObjIso (Z.homOfLE h)

theorem main {Z T : Scheme.{u}} (q : Z ⟶ T) [IsFinite q] [Flat q] [LocallyOfFinitePresentation q] (n : ℕ)
    (hn : ∀ t : T, q.finrank t = n) (N : Z.Modules)
    (hN : ∀ t : T, ∃ W : T.Opens, t ∈ W ∧
      Nonempty ((Scheme.Modules.pullback (q ⁻¹ᵁ W).ι).obj N ≅ 𝟙_ (↑(q ⁻¹ᵁ W) : Scheme.{u}).Modules)) :
    IsLocallyFreeOfRank n ((Scheme.Modules.pushforward q).obj N) := by
  refine isLocallyFreeOfRank_pushforward_of_forall_exists_isPullback q N n fun y => ?_
  obtain ⟨W₀, hyW₀, ⟨e₀⟩⟩ := hN y
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, hWle⟩ :=
    T.isBasis_affineOpens.exists_subset_of_mem_open hyW₀ W₀.isOpen
  have hW' : IsAffineOpen (q ⁻¹ᵁ W) := hW.preimage q

  let φ : Γ(T, W) ⟶ Γ(Z, q ⁻¹ᵁ W) := q.appLE W (q ⁻¹ᵁ W) le_rfl
  have hsq : IsPullback hW'.fromSpec (Spec.map φ) q hW.fromSpec :=
    (IsOpenImmersion.isPullback (Spec.map φ) hW'.fromSpec hW.fromSpec q
      (hW.SpecMap_appLE_fromSpec q hW' le_rfl).symm
      (by rw [IsAffineOpen.opensRange_fromSpec, IsAffineOpen.opensRange_fromSpec])).flip
  refine ⟨W, hyW, Spec (Γ(T, W)), Spec (Γ(Z, q ⁻¹ᵁ W)), hW.isoSpec.symm, Spec.map φ, hW'.fromSpec,
    ?_, ?_⟩
  · simpa [IsAffineOpen.isoSpec_inv_ι] using hsq
  ·
    haveI : IsFinite (Spec.map φ) := MorphismProperty.of_isPullback hsq inferInstance
    haveI : Flat (Spec.map φ) := MorphismProperty.of_isPullback hsq inferInstance
    haveI : LocallyOfFinitePresentation (Spec.map φ) := MorphismProperty.of_isPullback hsq inferInstance
    have hn' : ∀ p : Spec Γ(T, W), (Spec.map φ).finrank p = n := fun p => by
      rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ hsq, hn]

    have eN : (Scheme.Modules.pullback hW'.fromSpec).obj N ≅ 𝟙_ (Spec Γ(Z, q ⁻¹ᵁ W)).Modules :=
      (pullbackCongr (show hW'.fromSpec = hW'.isoSpec.inv ≫ (q ⁻¹ᵁ W).ι from rfl)).app N ≪≫
        ((pullbackComp hW'.isoSpec.inv (q ⁻¹ᵁ W).ι).app N).symm ≪≫
        (Scheme.Modules.pullback hW'.isoSpec.inv).mapIso
          (restrictTriv (show q ⁻¹ᵁ W ≤ q ⁻¹ᵁ W₀ from fun z hz => hWle hz) e₀) ≪≫
        pullbackTensorUnitObjIso hW'.isoSpec.inv
    exact IsLocallyFreeOfRank.of_iso ((Scheme.Modules.pushforward (Spec.map φ)).mapIso eN.symm)
      (core φ n hn')

end Ws31X1
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_pushforward_of_isFinite_of_flat_of_locallyTrivialOver.Ws31X1"

theorem solution
    {Z T : Scheme.{u}} (q : Z ⟶ T) [IsFinite q] [Flat q] [LocallyOfFinitePresentation q] (n : ℕ)
    (hn : ∀ t : T, q.finrank t = n) (N : Z.Modules)
    (hN : ∀ t : T, ∃ W : T.Opens, t ∈ W ∧
      Nonempty ((Scheme.Modules.pullback (q ⁻¹ᵁ W).ι).obj N ≅ 𝟙_ (↑(q ⁻¹ᵁ W) : Scheme.{u}).Modules)) :
    Scheme.Modules.IsLocallyFreeOfRank n ((Scheme.Modules.pushforward q).obj N) :=
  Ws31X1.main q n hn N hN

end S_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_pushforward_of_isFinite_of_flat_of_locallyTrivialOver
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_pushforward_of_isFinite_of_flat_of_locallyTrivialOver (solution)
