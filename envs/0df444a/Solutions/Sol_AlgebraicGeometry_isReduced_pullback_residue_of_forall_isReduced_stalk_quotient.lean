-- Prove2me | solution 1 for AlgebraicGeometry.isReduced_pullback_residue_of_forall_isReduced_stalk_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/4c5e7db9-59f3-58f5-ae31-5628c28edf46

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isReduced_pullback_residue_of_forall_isReduced_stalk_quotient

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace CFSAux

theorem isReduced_quotient_map_of_forall_isReduced_localization
    {A R : Type*} [CommRing A] [CommRing R] (φ : A →+* R) (I : Ideal A)
    (h : ∀ (𝔮 : Ideal R) [𝔮.IsPrime], I.map φ ≤ 𝔮 →
      IsReduced (Localization.AtPrime 𝔮 ⧸ I.map ((algebraMap R (Localization.AtPrime 𝔮)).comp φ))) :
    IsReduced (R ⧸ I.map φ) := by
  classical
  set J : Ideal R := I.map φ with hJ

  have key : ∀ (x : R) (n : ℕ), x ^ n ∈ J → x ∈ J := by
    intro x n hxn
    refine Ideal.mem_of_localization_maximal fun P hP => ?_
    haveI := hP
    by_cases hle : J ≤ P
    ·
      have hred := h P hle
      have hJmap : I.map ((algebraMap R (Localization.AtPrime P)).comp φ) =
          J.map (algebraMap R (Localization.AtPrime P)) := by rw [hJ, Ideal.map_map]
      rw [hJmap] at hred
      have hnil : IsNilpotent (Ideal.Quotient.mk (J.map (algebraMap R (Localization.AtPrime P)))
          (algebraMap R (Localization.AtPrime P) x)) := by
        refine ⟨n, ?_⟩
        rw [← map_pow, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.mem_map_of_mem _ hxn
      have h0 := hnil.eq_zero
      rwa [Ideal.Quotient.eq_zero_iff_mem] at h0
    ·
      obtain ⟨j, hjJ, hjP⟩ := Set.not_subset.mp hle
      have hunit : IsUnit (algebraMap R (Localization.AtPrime P) j) :=
        IsLocalization.map_units (Localization.AtPrime P) (⟨j, hjP⟩ : P.primeCompl)
      have htop : J.map (algebraMap R (Localization.AtPrime P)) = ⊤ :=
        Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hjJ) hunit
      rw [htop]; exact Submodule.mem_top
  refine ⟨fun y hy => ?_⟩
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨n, hn⟩ := hy
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem] at hn
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (key x n hn)

theorem isReduced_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) [IsReduced R] :
    IsReduced S :=
  isReduced_of_injective e.symm.toRingHom e.symm.injective

end CFSAux

namespace CFSGlue

variable {A : Type u} [CommRing A] [IsLocalRing A]

theorem base_eq_closedPoint_iff {R : CommRingCat.{u}} (φ : Spec R ⟶ Spec (CommRingCat.of A)) (𝔮 : PrimeSpectrum R) :
    φ.base 𝔮 = IsLocalRing.closedPoint A ↔
      (IsLocalRing.maximalIdeal A).map (Spec.preimage φ).hom ≤ 𝔮.asIdeal := by
  set ψ := Spec.preimage φ with hψ
  have hφ : φ = Spec.map ψ := (Spec.map_preimage φ).symm
  have hbase : φ.base 𝔮 = PrimeSpectrum.comap ψ.hom 𝔮 := by
    rw [hφ, Spec.map_base]; rfl
  rw [hbase, Ideal.map_le_iff_le_comap]
  constructor
  · intro h
    have h2 : (PrimeSpectrum.comap ψ.hom 𝔮).asIdeal = (IsLocalRing.closedPoint A).asIdeal := by rw [h]
    rw [PrimeSpectrum.comap_asIdeal] at h2
    rw [← show (IsLocalRing.closedPoint A).asIdeal = IsLocalRing.maximalIdeal A from rfl, ← h2]
  · intro h
    apply PrimeSpectrum.ext
    rw [PrimeSpectrum.comap_asIdeal]
    exact ((IsLocalRing.maximalIdeal.isMaximal A).eq_of_le
      (Ideal.IsPrime.ne_top (Ideal.comap_isPrime ψ.hom 𝔮.asIdeal)) h).symm

theorem isReduced_pullback_affine {R : CommRingCat.{u}} (φ : Spec R ⟶ Spec (CommRingCat.of A))
    (h : ∀ 𝔮 : PrimeSpectrum R, (IsLocalRing.maximalIdeal A).map (Spec.preimage φ).hom ≤ 𝔮.asIdeal →
      _root_.IsReduced (Localization.AtPrime 𝔮.asIdeal ⧸
        (IsLocalRing.maximalIdeal A).map ((algebraMap R (Localization.AtPrime 𝔮.asIdeal)).comp (Spec.preimage φ).hom))) :
    IsReduced (pullback φ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))) := by
  classical
  set ψ := Spec.preimage φ with hψ
  have hφ : φ = Spec.map ψ := (Spec.map_preimage φ).symm
  letI : Algebra A R := ψ.hom.toAlgebra
  have hψalg : ψ = CommRingCat.ofHom (algebraMap A R) := rfl
  have hres : CommRingCat.ofHom (IsLocalRing.residue A) =
      CommRingCat.ofHom (algebraMap A (IsLocalRing.ResidueField A)) := rfl
  rw [hφ, hψalg, hres]

  let e := pullbackSpecIso A R (IsLocalRing.ResidueField A)
  haveI : IsReduced (Spec (CommRingCat.of (TensorProduct A R (IsLocalRing.ResidueField A)))) := by
    rw [affine_isReduced_iff]

    haveI : _root_.IsReduced (↑R ⧸ (IsLocalRing.maximalIdeal A).map (algebraMap A R)) := by
      refine CFSAux.isReduced_quotient_map_of_forall_isReduced_localization (algebraMap A R)
        (IsLocalRing.maximalIdeal A) (fun 𝔮 _ hle => ?_)
      exact h ⟨𝔮, inferInstance⟩ hle
    exact CFSAux.isReduced_of_ringEquiv
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (R : Type u) (IsLocalRing.maximalIdeal A)).toRingEquiv
  exact isReduced_of_isOpenImmersion e.hom

theorem isReduced_localization_quotient_of_stalk {X : Scheme.{u}} (toBase : X ⟶ Spec (CommRingCat.of A))
    {R : CommRingCat.{u}} (j : Spec R ⟶ X) [IsOpenImmersion j] (𝔮 : PrimeSpectrum R)
    (hred : _root_.IsReduced (X.presheaf.stalk (j.base 𝔮) ⧸
        Ideal.map ((X.presheaf.germ ⊤ (j.base 𝔮) trivial).hom.comp
          (toBase.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom))
          (IsLocalRing.maximalIdeal A))) :
    _root_.IsReduced (Localization.AtPrime 𝔮.asIdeal ⧸
      (IsLocalRing.maximalIdeal A).map
        ((algebraMap R (Localization.AtPrime 𝔮.asIdeal)).comp (Spec.preimage (j ≫ toBase)).hom)) := by
  classical
  set ψ := Spec.preimage (j ≫ toBase) with hψ
  have hjψ : j ≫ toBase = Spec.map ψ := (Spec.map_preimage _).symm

  set G : CommRingCat.of A ⟶ X.presheaf.stalk (j.base 𝔮) :=
    (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ toBase.appTop ≫ X.presheaf.germ ⊤ (j.base 𝔮) trivial with hG

  have hstep1 : ∀ t : Γ(X, ⊤), (j.stalkMap 𝔮).hom ((X.presheaf.germ ⊤ (j.base 𝔮) trivial).hom t) =
      ((Spec R).presheaf.germ ⊤ 𝔮 trivial).hom ((j.app ⊤).hom t) := by
    intro t
    have h := Scheme.Hom.germ_stalkMap j ⊤ 𝔮 trivial
    have h' := congrArg (fun f => f.hom t) h
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h'
    exact h'

  have hstep2 : ∀ s : Γ(Spec (CommRingCat.of A), ⊤), (j.app ⊤).hom (toBase.appTop.hom s) = (Spec.map ψ).appTop.hom s := by
    intro s
    have h : (j ≫ toBase).appTop = toBase.appTop ≫ j.appTop := rfl
    rw [← hjψ, h]; rfl

  have hstep3 : ∀ a : A, (Spec.map ψ).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) =
      (Scheme.ΓSpecIso R).inv.hom (ψ.hom a) := by
    intro a
    have h := congrArg (fun f => f.hom a) (Scheme.ΓSpecIso_inv_naturality ψ)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
    exact h.symm

  have hstep4 : ∀ r : R, ((Spec R).presheaf.germ ⊤ 𝔮 trivial).hom ((Scheme.ΓSpecIso R).inv.hom r) =
      (StructureSheaf.toStalk R 𝔮).hom r := by
    intro r
    have h := congrArg (fun f => f.hom r) (StructureSheaf.algebraMap_germ (R := R) ⊤ 𝔮 trivial)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
    rw [Scheme.ΓSpecIso_inv]
    exact h
  have hchain : ∀ a : A, (j.stalkMap 𝔮).hom (G.hom a) = (StructureSheaf.toStalk R 𝔮).hom (ψ.hom a) := by
    intro a
    rw [hG]
    simp only [CommRingCat.hom_comp, RingHom.comp_apply]
    rw [hstep1, hstep2, hstep3, hstep4]

  haveI : IsIso (j.stalkMap 𝔮) := inferInstance
  let e₁ : ↑(X.presheaf.stalk (j.base 𝔮)) ≃+* ↑((Spec R).presheaf.stalk 𝔮) :=
    (asIso (j.stalkMap 𝔮)).commRingCatIsoToRingEquiv
  let e₂ : ↑((Spec R).presheaf.stalk 𝔮) ≃+* Localization.AtPrime 𝔮.asIdeal :=
    (StructureSheaf.stalkIso R 𝔮).symm.toRingEquiv
  let T : ↑(X.presheaf.stalk (j.base 𝔮)) ≃+* Localization.AtPrime 𝔮.asIdeal := e₁.trans e₂
  have hT : ∀ a : A, T (G.hom a) = algebraMap R (Localization.AtPrime 𝔮.asIdeal) (ψ.hom a) := by
    intro a
    have h1 : (j.stalkMap 𝔮).hom (G.hom a) = (StructureSheaf.toStalk R 𝔮).hom (ψ.hom a) := hchain a
    show e₂ (e₁ (G.hom a)) = _
    have h2 : e₁ (G.hom a) = (j.stalkMap 𝔮).hom (G.hom a) := rfl
    rw [h2, h1, ← StructureSheaf.stalkAlgebra_map]
    exact (StructureSheaf.stalkIso R 𝔮).symm.commutes (ψ.hom a)

  have hideal : (Ideal.map ((X.presheaf.germ ⊤ (j.base 𝔮) trivial).hom.comp
        (toBase.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)) (IsLocalRing.maximalIdeal A)).map
        T.toRingHom =
      (IsLocalRing.maximalIdeal A).map ((algebraMap R (Localization.AtPrime 𝔮.asIdeal)).comp ψ.hom) := by
    rw [Ideal.map_map]
    congr 1
    ext a
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    rw [← hT a]
    rfl
  rw [← hideal]
  exact CFSAux.isReduced_of_ringEquiv (Ideal.quotientEquiv _ _ T rfl)

theorem isReduced_of_openCover {P : Scheme.{u}} (𝒰 : P.OpenCover) (h : ∀ i, IsReduced (𝒰.X i)) :
    IsReduced P := by
  haveI : ∀ p : P, _root_.IsReduced (P.presheaf.stalk p) := by
    intro p
    obtain ⟨i, y, hy⟩ := 𝒰.exists_eq p
    haveI := h i
    subst hy
    haveI : IsIso ((𝒰.f i).stalkMap y) := inferInstance
    have hbij := ConcreteCategory.bijective_of_isIso ((𝒰.f i).stalkMap y)

    exact isReduced_of_injective ((𝒰.f i).stalkMap y).hom hbij.1
  exact isReduced_of_isReduced_stalk P

end CFSGlue

open CFSGlue in

theorem solution
    {A : Type u} [CommRing A] [IsLocalRing A]
    {X : Scheme.{u}} (toBase : X ⟶ Spec (CommRingCat.of A))
    (h : ∀ x : X, toBase.base x = IsLocalRing.closedPoint A →
      _root_.IsReduced (X.presheaf.stalk x ⧸
        Ideal.map ((X.presheaf.germ ⊤ x trivial).hom.comp
          (toBase.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom))
          (IsLocalRing.maximalIdeal A))) :
    IsReduced (pullback toBase (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))) := by
  classical
  let g := Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))
  let 𝒱 := X.affineOpenCover
  let 𝒰 := Scheme.Pullback.openCoverOfLeft 𝒱.openCover toBase g
  apply isReduced_of_openCover 𝒰
  intro i

  show IsReduced (pullback (𝒱.f i ≫ toBase) g)
  apply isReduced_pullback_affine (𝒱.f i ≫ toBase)
  intro 𝔮 h𝔮
  apply isReduced_localization_quotient_of_stalk toBase (𝒱.f i) 𝔮
  apply h

  have := (base_eq_closedPoint_iff (𝒱.f i ≫ toBase) 𝔮).mpr h𝔮
  exact this

end S_AlgebraicGeometry_isReduced_pullback_residue_of_forall_isReduced_stalk_quotient
end P2MW
export P2MW.S_AlgebraicGeometry_isReduced_pullback_residue_of_forall_isReduced_stalk_quotient (solution)
