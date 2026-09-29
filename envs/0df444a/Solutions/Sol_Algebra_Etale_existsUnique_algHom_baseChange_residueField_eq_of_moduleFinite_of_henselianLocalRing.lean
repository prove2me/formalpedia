-- Prove2me | solution 1 for Algebra.Etale.existsUnique_algHom_baseChange_residueField_eq_of_moduleFinite_of_henselianLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/a6a19549-dd5c-53b3-aa9a-f562c604dd0d

import Mathlib
import Theorems.Thm_Algebra_Etale_algHom_ext_of_forall_sub_mem_map_maximalIdeal_of_henselianLocalRing
import Theorems.Thm_HenselianLocalRing_exists_completeOrthogonalIdempotents_forall_isLocalRing_quotient_of_moduleFinite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_Etale_existsUnique_algHom_baseChange_residueField_eq_of_moduleFinite_of_henselianLocalRing

set_option autoImplicit false

open scoped TensorProduct

universe u v w

namespace H1Aux

open IsLocalRing

section LocalHom

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

theorem isLocalHom_algebraMap_of_moduleFinite [IsLocalRing A] [IsLocalRing B] [Module.Finite A B] :
    IsLocalHom (algebraMap A B) := by
  refine ((local_hom_TFAE (algebraMap A B)).out 0 3).mpr ?_
  intro x hx
  rw [Ideal.mem_comap]
  by_contra hxB
  have hu : IsUnit (algebraMap A B x) := by
    simpa [mem_maximalIdeal, mem_nonunits_iff] using hxB

  have htop : (⊤ : Submodule A B) ≤ Ideal.span {x} • (⊤ : Submodule A B) := by
    intro b _
    obtain ⟨u, hu'⟩ := hu
    have : b = x • (↑u⁻¹ * b) := by
      rw [Algebra.smul_def, ← mul_assoc, ← hu', Units.mul_inv, one_mul]
    rw [this]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self x) Submodule.mem_top
  have hjac : Ideal.span {x} ≤ (⊥ : Ideal A).jacobson :=
    (Ideal.span_singleton_le_iff_mem _).mpr (maximalIdeal_le_jacobson ⊥ hx)
  have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (Ideal.span {x}) ⊤ Module.Finite.fg_top htop hjac
  exact one_ne_zero ((Submodule.eq_bot_iff _).mp hbot 1 Submodule.mem_top)

theorem restrictScalars_maximalIdeal_le_smul_top [IsLocalRing A] [IsLocalRing B]
    (h : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B) :
    ((maximalIdeal B).restrictScalars A : Submodule A B) ≤ maximalIdeal A • (⊤ : Submodule A B) := by
  rw [Ideal.smul_top_eq_map, h]

end LocalHom

section Residue

variable {R : Type u} [CommRing R] [IsLocalRing R] {C : Type w} [CommRing C] [Algebra R C]

theorem one_tmul_eq_zero_iff (c : C) :
    (1 : ResidueField R) ⊗ₜ[R] c = 0 ↔ c ∈ (maximalIdeal R).map (algebraMap R C) := by
  have h1 : (1 : ResidueField R) ⊗ₜ[R] c = 0 ↔ c ⊗ₜ[R] (1 : ResidueField R) = 0 := by
    rw [← (Algebra.TensorProduct.comm R (ResidueField R) C).injective.eq_iff, map_zero,
      Algebra.TensorProduct.comm_tmul]
  have h2 : c ∈ (maximalIdeal R).map (algebraMap R C) ↔ c ⊗ₜ[R] (1 : ResidueField R) = 0 := by
    rw [← Ideal.Quotient.eq_zero_iff_mem,
      ← (Algebra.TensorProduct.quotIdealMapEquivTensorQuot C (maximalIdeal R)).injective.eq_iff, map_zero,
      Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk]
    rfl
  exact h1.trans h2.symm

theorem exists_one_tmul (z : ResidueField R ⊗[R] C) : ∃ c : C, z = (1 : ResidueField R) ⊗ₜ[R] c := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul a c =>
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective a
    refine ⟨r • c, ?_⟩
    rw [show IsLocalRing.residue R r = r • (1 : ResidueField R) from Algebra.algebraMap_eq_smul_one r,
      TensorProduct.smul_tmul]
  | add x y hx hy =>
    obtain ⟨c, rfl⟩ := hx
    obtain ⟨c', rfl⟩ := hy
    exact ⟨c + c', by rw [TensorProduct.tmul_add]⟩

variable [IsLocalRing C] [IsLocalHom (algebraMap R C)]

theorem nontrivial_residueField_tensor : Nontrivial (ResidueField R ⊗[R] C) := by
  refine ⟨⟨(1 : ResidueField R) ⊗ₜ[R] (1 : C), 0, ?_⟩⟩
  rw [Ne, one_tmul_eq_zero_iff]
  intro h
  have hle : (maximalIdeal R).map (algebraMap R C) ≤ maximalIdeal C :=
    ((local_hom_TFAE (algebraMap R C)).out 0 2).mp ‹_›
  exact (maximalIdeal.isMaximal C).ne_top (Ideal.eq_top_of_isUnit_mem _ (hle h) isUnit_one)

theorem isLocalRing_residueField_tensor : IsLocalRing (ResidueField R ⊗[R] C) := by
  haveI := nontrivial_residueField_tensor (R := R) (C := C)
  refine IsLocalRing.of_surjective'
    (Algebra.TensorProduct.includeRight (R := R) (A := ResidueField R) (B := C) : C →+* ResidueField R ⊗[R] C) ?_
  intro z
  obtain ⟨c, rfl⟩ := exists_one_tmul z
  exact ⟨c, rfl⟩

end Residue

end H1Aux

namespace H1Aux

open IsLocalRing

section Core

variable {R : Type u} [CommRing R] [HenselianLocalRing R]
  {O : Type v} [CommRing O] [Algebra R O] [Module.Finite R O] [Algebra.Etale R O]
  {C : Type w} [CommRing C] [Algebra R C] [Module.Finite R C]

theorem algHom_eq_of_map_eq (ψ₁ ψ₂ : O →ₐ[R] C)
    (h : Algebra.TensorProduct.map (AlgHom.id (ResidueField R) (ResidueField R)) ψ₁ =
      Algebra.TensorProduct.map (AlgHom.id (ResidueField R) (ResidueField R)) ψ₂) : ψ₁ = ψ₂ := by
  apply Algebra.Etale.algHom_ext_of_forall_sub_mem_map_maximalIdeal_of_henselianLocalRing R O C
  intro x
  rw [← one_tmul_eq_zero_iff, TensorProduct.tmul_sub, sub_eq_zero]
  have := AlgHom.congr_fun h ((1 : ResidueField R) ⊗ₜ[R] x)
  simpa [Algebra.TensorProduct.map_tmul] using this

theorem exists_algHom_of_isLocalRing [IsLocalRing C]
    (ψbar : ResidueField R ⊗[R] O →ₐ[ResidueField R] ResidueField R ⊗[R] C) :
    ∃ ψ : O →ₐ[R] C, Algebra.TensorProduct.map (AlgHom.id (ResidueField R) (ResidueField R)) ψ = ψbar := by
  classical
  haveI : IsLocalHom (algebraMap R C) := isLocalHom_algebraMap_of_moduleFinite

  let f₀ : ResidueField R →ₐ[R] ResidueField C :=
    { toRingHom := ResidueField.map (algebraMap R C), commutes' := fun r => rfl }
  let θ : ResidueField R ⊗[R] C →ₐ[R] ResidueField C :=
    Algebra.TensorProduct.lift f₀ (IsScalarTower.toAlgHom R C (ResidueField C)) (fun _ _ => Commute.all _ _)
  have hθ : ∀ (a : ResidueField R) (c : C), θ (a ⊗ₜ[R] c) = f₀ a * residue C c :=
    fun a c => Algebra.TensorProduct.lift_tmul _ _ _ a c

  let q : O →ₐ[R] ResidueField C :=
    θ.comp ((ψbar.restrictScalars R).comp (Algebra.TensorProduct.includeRight (A := ResidueField R)))
  let pbar : C ⊗[R] O →ₐ[C] ResidueField C :=
    Algebra.TensorProduct.lift (Algebra.ofId C (ResidueField C)) q (fun _ _ => Commute.all _ _)
  have hpbar : ∀ (c : C) (o : O), pbar (c ⊗ₜ[R] o) = residue C c * q o :=
    fun c o => Algebra.TensorProduct.lift_tmul _ _ _ c o
  have hpsurj : Function.Surjective pbar := by
    intro x
    obtain ⟨c, rfl⟩ := residue_surjective (R := C) x
    exact ⟨c ⊗ₜ 1, by rw [hpbar, map_one, mul_one]⟩

  obtain ⟨hfin, e, hce, hnot, -, hloc⟩ :=
    HenselianLocalRing.exists_completeOrthogonalIdempotents_forall_isLocalRing_quotient_of_moduleFinite
      (R := R) (S := C ⊗[R] O)
  let m₀ : MaximalSpectrum (C ⊗[R] O) :=
    ⟨RingHom.ker (pbar : C ⊗[R] O →+* ResidueField C), RingHom.ker_isMaximal_of_surjective _ hpsurj⟩
  have he₀ : pbar (e m₀) = 1 := by
    have hne : pbar (e m₀) ≠ 0 := fun h => hnot m₀ (by
      show e m₀ ∈ RingHom.ker (pbar : C ⊗[R] O →+* ResidueField C)
      rwa [RingHom.mem_ker])
    have hid : IsIdempotentElem (pbar (e m₀)) := (hce.idem m₀).map pbar
    exact (IsIdempotentElem.iff_eq_zero_or_one.mp hid).resolve_left hne
  let I : Ideal (C ⊗[R] O) := Ideal.span {1 - e m₀}
  haveI hL : IsLocalRing ((C ⊗[R] O) ⧸ I) := hloc m₀

  haveI : IsLocalHom (algebraMap C ((C ⊗[R] O) ⧸ I)) :=
    isLocalHom_algebraMap_of_moduleFinite (A := C) (B := (C ⊗[R] O) ⧸ I)
  haveI : Algebra.FormallyUnramified C ((C ⊗[R] O) ⧸ I) := Algebra.FormallyUnramified.quotient I

  haveI : Module.Flat C ((C ⊗[R] O) ⧸ I) := by
    let r : (C ⊗[R] O) →ₗ[C] ((C ⊗[R] O) ⧸ I) := (Ideal.Quotient.mkₐ C I).toLinearMap
    let i₀ : ((C ⊗[R] O) ⧸ I.restrictScalars C) →ₗ[C] (C ⊗[R] O) :=
      (I.restrictScalars C).liftQ (LinearMap.mulLeft C (e m₀)) (by
        intro x hx
        rw [Submodule.restrictScalars_mem, Ideal.mem_span_singleton] at hx
        obtain ⟨y, rfl⟩ := hx
        rw [LinearMap.mem_ker, LinearMap.mulLeft_apply, ← mul_assoc, (hce.idem m₀).mul_one_sub_self, zero_mul])
    let i : ((C ⊗[R] O) ⧸ I) →ₗ[C] (C ⊗[R] O) :=
      i₀ ∘ₗ (Submodule.Quotient.restrictScalarsEquiv C I).symm.toLinearMap
    refine Module.Flat.of_retract i r ?_
    apply LinearMap.ext
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    show Ideal.Quotient.mk I (i₀ ((Submodule.Quotient.restrictScalarsEquiv C I).symm (Ideal.Quotient.mk I x))) =
      Ideal.Quotient.mk I x
    rw [show (Submodule.Quotient.restrictScalarsEquiv C I).symm (Ideal.Quotient.mk I x) =
        Submodule.Quotient.mk x from rfl]
    show Ideal.Quotient.mk I (e m₀ * x) = Ideal.Quotient.mk I x
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
    exact ⟨-x, by ring⟩
  haveI : Module.Free C ((C ⊗[R] O) ⧸ I) := Module.free_of_flat_of_isLocalRing
  have hmL := Algebra.FormallyUnramified.map_maximalIdeal (R := C) (S := (C ⊗[R] O) ⧸ I)

  let pL : ((C ⊗[R] O) ⧸ I) →ₐ[C] ResidueField C := Ideal.Quotient.liftₐ I pbar (by
    intro a ha
    rw [Ideal.mem_span_singleton] at ha
    obtain ⟨b, rfl⟩ := ha
    rw [map_mul, map_sub, map_one, he₀, sub_self, zero_mul])
  have hpL : ∀ d, pL (Ideal.Quotient.mk I d) = pbar d := fun d => rfl
  have hpLsurj : Function.Surjective pL := by
    intro x
    obtain ⟨d, rfl⟩ := hpsurj x
    exact ⟨Ideal.Quotient.mk I d, rfl⟩
  let ιₐ : C →ₐ[C] ((C ⊗[R] O) ⧸ I) := Algebra.ofId C ((C ⊗[R] O) ⧸ I)

  have hιsurj : Function.Surjective ιₐ := by
    have key : (⊤ : Submodule C ((C ⊗[R] O) ⧸ I)) ≤ LinearMap.range ιₐ.toLinearMap ⊔
        (maximalIdeal ((C ⊗[R] O) ⧸ I)).restrictScalars C := by
      intro ℓ _
      obtain ⟨c, hc⟩ := residue_surjective (R := C) (pL ℓ)
      have hmem : ℓ - ιₐ c ∈ maximalIdeal ((C ⊗[R] O) ⧸ I) := by
        rw [mem_maximalIdeal, mem_nonunits_iff]
        intro hu
        apply (hu.map pL).ne_zero
        rw [map_sub, sub_eq_zero, ← hc]
        exact (pL.commutes c).symm
      exact Submodule.mem_sup.mpr ⟨ιₐ c, ⟨c, rfl⟩, ℓ - ιₐ c, hmem, by abel⟩
    have hsmul : ((maximalIdeal ((C ⊗[R] O) ⧸ I)).restrictScalars C : Submodule C ((C ⊗[R] O) ⧸ I)) ≤
        maximalIdeal C • (⊤ : Submodule C ((C ⊗[R] O) ⧸ I)) :=
      restrictScalars_maximalIdeal_le_smul_top (A := C) (B := (C ⊗[R] O) ⧸ I) hmL
    have hle : (⊤ : Submodule C ((C ⊗[R] O) ⧸ I)) ≤ LinearMap.range ιₐ.toLinearMap :=
      Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top (maximalIdeal_le_jacobson ⊥)
        (key.trans (sup_le_sup_left hsmul _))
    intro ℓ
    obtain ⟨c, hc⟩ := hle (Submodule.mem_top : ℓ ∈ ⊤)
    exact ⟨c, hc⟩

  have hιinj : Function.Injective ιₐ := by
    let b := Module.Free.chooseBasis C ((C ⊗[R] O) ⧸ I)
    obtain ⟨i₀⟩ := b.index_nonempty
    let g : C →ₗ[C] C := (b.coord i₀) ∘ₗ ιₐ.toLinearMap
    have hg : Function.Surjective g := by
      intro t
      obtain ⟨c, hc⟩ := hιsurj (t • b i₀)
      refine ⟨c, ?_⟩
      show b.coord i₀ (ιₐ c) = t
      rw [hc, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same, smul_eq_mul,
        mul_one]
    have hginj := OrzechProperty.injective_of_surjective_endomorphism g hg
    intro x y hxy
    apply hginj
    show b.coord i₀ (ιₐ x) = b.coord i₀ (ιₐ y)
    rw [hxy]

  let E : C ≃ₐ[C] ((C ⊗[R] O) ⧸ I) := AlgEquiv.ofBijective ιₐ ⟨hιinj, hιsurj⟩
  let σ : (C ⊗[R] O) →ₐ[C] C := (E.symm : ((C ⊗[R] O) ⧸ I) →ₐ[C] C).comp (Ideal.Quotient.mkₐ C I)
  have hEσ : ∀ d, E (σ d) = Ideal.Quotient.mk I d := fun d => E.apply_symm_apply _
  have hσ : ∀ d, residue C (σ d) = pbar d := by
    intro d
    rw [← hpL, ← hEσ]
    show _ = pL (ιₐ (σ d))
    exact (pL.commutes (σ d)).symm
  let ψ : O →ₐ[R] C := (σ.restrictScalars R).comp (Algebra.TensorProduct.includeRight (A := C))
  have hψ : ∀ o, residue C (ψ o) = q o := by
    intro o
    show residue C (σ (1 ⊗ₜ o)) = q o
    rw [hσ, hpbar, map_one, one_mul]
  refine ⟨ψ, ?_⟩

  haveI : IsLocalRing (ResidueField R ⊗[R] C) := isLocalRing_residueField_tensor
  haveI : IsArtinianRing (ResidueField R ⊗[R] C) := IsArtinianRing.of_finite (ResidueField R) _
  have hθsurj : Function.Surjective θ := by
    intro x
    obtain ⟨c, rfl⟩ := residue_surjective (R := C) x
    exact ⟨1 ⊗ₜ c, by rw [hθ, map_one, one_mul]⟩
  have hnil : IsNilpotent (RingHom.ker (θ : ResidueField R ⊗[R] C →+* ResidueField C)) := by
    rw [ker_eq_maximalIdeal (θ : ResidueField R ⊗[R] C →+* ResidueField C) hθsurj,
      ← jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact IsArtinianRing.isNilpotent_jacobson_bot
  apply Algebra.FormallyUnramified.ext' (θ : ResidueField R ⊗[R] C →+* ResidueField C) hnil
  intro z
  suffices hcomp : θ.comp ((Algebra.TensorProduct.map (AlgHom.id (ResidueField R) (ResidueField R)) ψ).restrictScalars R) =
      θ.comp (ψbar.restrictScalars R) from AlgHom.congr_fun hcomp z
  apply Algebra.TensorProduct.ext'
  intro a o
  have hz : a ⊗ₜ[R] o = algebraMap (ResidueField R) (ResidueField R ⊗[R] O) a * ((1 : ResidueField R) ⊗ₜ[R] o) := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rfl
  show θ (Algebra.TensorProduct.map (AlgHom.id (ResidueField R) (ResidueField R)) ψ (a ⊗ₜ[R] o)) =
    θ (ψbar (a ⊗ₜ[R] o))
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hθ, hψ, hz, map_mul, AlgHom.commutes, map_mul,
    Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, hθ, map_one, mul_one]
  rfl

end Core

end H1Aux

namespace H1Aux

open IsLocalRing

section Assemble

variable {R : Type u} [CommRing R] [HenselianLocalRing R]
  {O : Type v} [CommRing O] [Algebra R O] [Module.Finite R O] [Algebra.Etale R O]
  {C : Type w} [CommRing C] [Algebra R C] [Module.Finite R C]

omit [HenselianLocalRing R] [Module.Finite R C] in

theorem mul_mem_map_maximalIdeal_of_mk_mem [IsLocalRing R] (e c : C) (he : IsIdempotentElem e)
    (h : Ideal.Quotient.mk (Ideal.span {1 - e}) c ∈
      (maximalIdeal R).map (algebraMap R (C ⧸ Ideal.span {1 - e}))) :
    c * e ∈ (maximalIdeal R).map (algebraMap R C) := by
  rw [IsScalarTower.algebraMap_eq R C (C ⧸ Ideal.span {1 - e}), ← Ideal.map_map, Ideal.Quotient.algebraMap_eq,
    Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at h
  obtain ⟨c', hc', hcc'⟩ := h
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at hcc'
  obtain ⟨d, hd⟩ := hcc'
  have : c * e = c' * e := by
    calc c * e = (c' - (c' - c)) * e := by ring
      _ = (c' - (1 - e) * d) * e := by rw [hd]
      _ = c' * e - d * ((1 - e) * e) := by ring
      _ = c' * e := by rw [he.one_sub_mul_self, mul_zero, sub_zero]
  rw [this]
  exact Ideal.mul_mem_right _ _ hc'

omit [Module.Finite R O] [Algebra.Etale R O] [Module.Finite R C] in

theorem eq_zero_of_forall_map_mk_eq_zero {ι : Type*} [Fintype ι] (e : ι → C)
    (hce : CompleteOrthogonalIdempotents e) (z : ResidueField R ⊗[R] C)
    (hz : ∀ i, Algebra.TensorProduct.map (AlgHom.id (ResidueField R) (ResidueField R))
      (Ideal.Quotient.mkₐ R (Ideal.span {1 - e i})) z = 0) : z = 0 := by
  obtain ⟨c, rfl⟩ := exists_one_tmul z
  rw [one_tmul_eq_zero_iff]
  have hi : ∀ i, c * e i ∈ (maximalIdeal R).map (algebraMap R C) := by
    intro i
    have h := hz i
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Ideal.Quotient.mkₐ_eq_mk, one_tmul_eq_zero_iff] at h
    exact mul_mem_map_maximalIdeal_of_mk_mem (R := R) (e i) c (hce.idem i) h
  have hc : c = ∑ i, c * e i := by rw [← Finset.mul_sum, hce.complete, mul_one]
  rw [hc]
  exact Ideal.sum_mem _ fun i _ => hi i

theorem exists_algHom
    (ψbar : ResidueField R ⊗[R] O →ₐ[ResidueField R] ResidueField R ⊗[R] C) :
    ∃ ψ : O →ₐ[R] C, Algebra.TensorProduct.map (AlgHom.id (ResidueField R) (ResidueField R)) ψ = ψbar := by
  classical
  obtain ⟨hfin, e, hce, -, -, hloc⟩ :=
    HenselianLocalRing.exists_completeOrthogonalIdempotents_forall_isLocalRing_quotient_of_moduleFinite
      (R := R) (S := C)

  let Cq : MaximalSpectrum C → Type w := fun m => C ⧸ Ideal.span {1 - e m}
  let π : (m : MaximalSpectrum C) → (C →ₐ[R] Cq m) := fun m => Ideal.Quotient.mkₐ R (Ideal.span {1 - e m})
  have hψm : ∀ m, ∃ ψm : O →ₐ[R] Cq m,
      Algebra.TensorProduct.map (AlgHom.id (ResidueField R) (ResidueField R)) ψm =
        (Algebra.TensorProduct.map (AlgHom.id (ResidueField R) (ResidueField R)) (π m)).comp ψbar := by
    intro m
    haveI : IsLocalRing (Cq m) := hloc m
    haveI : Module.Finite R (Cq m) := inferInstance
    exact exists_algHom_of_isLocalRing _
  choose ψm hψm using hψm

  let Φ : C →ₐ[R] ((m : MaximalSpectrum C) → Cq m) := Pi.algHom R Cq π
  have hΦ : Function.Bijective Φ := by
    have := CompleteOrthogonalIdempotents.bijective_pi hce
    exact this
  let EΦ : C ≃ₐ[R] ((m : MaximalSpectrum C) → Cq m) := AlgEquiv.ofBijective Φ hΦ
  let ψ : O →ₐ[R] C := (EΦ.symm : ((m : MaximalSpectrum C) → Cq m) →ₐ[R] C).comp (Pi.algHom R Cq ψm)
  have hπψ : ∀ m, (π m).comp ψ = ψm m := by
    intro m
    apply AlgHom.ext
    intro o
    show (Φ (EΦ.symm (Pi.algHom R Cq ψm o))) m = ψm m o
    rw [show Φ (EΦ.symm (Pi.algHom R Cq ψm o)) = Pi.algHom R Cq ψm o from EΦ.apply_symm_apply _]
    rfl
  refine ⟨ψ, ?_⟩
  apply AlgHom.ext
  intro x
  rw [← sub_eq_zero]
  apply eq_zero_of_forall_map_mk_eq_zero e hce
  intro m
  rw [map_sub, sub_eq_zero]
  show (Algebra.TensorProduct.map (AlgHom.id _ _) (π m)).comp
      (Algebra.TensorProduct.map (AlgHom.id (ResidueField R) (ResidueField R)) ψ) x =
    (Algebra.TensorProduct.map (AlgHom.id _ _) (π m)).comp ψbar x
  rw [← Algebra.TensorProduct.map_comp, AlgHom.comp_id, hπψ, hψm]

end Assemble

end H1Aux

theorem solution
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    (O : Type v) [CommRing O] [Algebra R O] [Module.Finite R O] [Algebra.Etale R O]
    (C : Type w) [CommRing C] [Algebra R C] [Module.Finite R C]
    (ψbar : IsLocalRing.ResidueField R ⊗[R] O →ₐ[IsLocalRing.ResidueField R] IsLocalRing.ResidueField R ⊗[R] C) :
    ∃! ψ : O →ₐ[R] C,
      Algebra.TensorProduct.map (AlgHom.id (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R)) ψ = ψbar := by
  refine ⟨(H1Aux.exists_algHom ψbar).choose, (H1Aux.exists_algHom ψbar).choose_spec, ?_⟩
  intro ψ' hψ'
  exact H1Aux.algHom_eq_of_map_eq _ _ (hψ'.trans (H1Aux.exists_algHom ψbar).choose_spec.symm)

end S_Algebra_Etale_existsUnique_algHom_baseChange_residueField_eq_of_moduleFinite_of_henselianLocalRing
end P2MW
export P2MW.S_Algebra_Etale_existsUnique_algHom_baseChange_residueField_eq_of_moduleFinite_of_henselianLocalRing (solution)
