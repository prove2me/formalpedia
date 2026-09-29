-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.IdealSheafData.isInvertible_of_isInvertible_comap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/d3fa8e71-b723-5122-88c6-22b1ed36f1a8

import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Localization.Free
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.IsTensorProduct
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_isInvertible_of_isInvertible_comap

set_option autoImplicit false

universe u

open TensorProduct

section FreeIdeal

variable {R : Type*} [CommRing R]

namespace Ideal p2m_export "Ideal" "map_le_iff_le_comap map_map submodule_span_eq mem_span_singleton map_span primeCompl isUnit_iff mem_bot span mul_mem_left map span_singleton_le_iff_mem exists_le_maximal FG ext span_eq mem_span_singleton' map_coe mem_map_of_mem comap_symm under comap comap_coe subset_span exists_isPrime_liesOver_of_faithfullyFlat mem_span_singleton_self" end Ideal
p2m_open_scoped "Ideal" in

noncomputable def Ideal.equivSpanSingletonOfMemNonZeroDivisors {g : R}
    (hg : g ∈ nonZeroDivisors R) : R ≃ₗ[R] (Ideal.span {g} : Ideal R) :=
  LinearEquiv.ofInjective (LinearMap.toSpanSingleton R R g)
      ((injective_iff_map_eq_zero _).mpr fun r hr ↦
        (mul_right_mem_nonZeroDivisors_eq_zero_iff hg).mp (by simpa using hr)) ≪≫ₗ
    LinearEquiv.ofEq _ _ (by rw [← LinearMap.span_singleton_eq_range, Ideal.submodule_span_eq])

p2m_open_scoped "Ideal" in

theorem Ideal.free_span_singleton_of_mem_nonZeroDivisors {g : R} (hg : g ∈ nonZeroDivisors R) :
    Module.Free R (Ideal.span {g} : Ideal R) :=
  Module.Free.of_equiv (Ideal.equivSpanSingletonOfMemNonZeroDivisors hg)

p2m_open_scoped "Ideal" in

theorem Ideal.eq_bot_or_exists_span_singleton_nonZeroDivisor_of_free (I : Ideal R)
    [Module.Free R I] : I = ⊥ ∨ ∃ j ∈ nonZeroDivisors R, I = Ideal.span {j} := by
  classical
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Or.inl (Subsingleton.elim _ _)
  let b := Module.Free.chooseBasis R I
  rcases isEmpty_or_nonempty (Module.Free.ChooseBasisIndex R I) with hι | ⟨⟨i⟩⟩
  · left
    have : Subsingleton I := b.repr.toEquiv.subsingleton
    rw [Submodule.eq_bot_iff]
    intro x hx
    simpa using congr_arg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : I) 0)
  · right

    have key : ∀ i', i' = i := by
      intro i'
      by_contra h
      have h0 : ((b i' : I) : R) • (b i) - ((b i : I) : R) • (b i') = (0 : I) := by
        ext
        simp [mul_comm]
      have := congr_arg (fun v ↦ b.repr v i) h0
      simp [h] at this
      exact b.ne_zero i' (by simpa using this)
    refine ⟨(b i : R), ?_, ?_⟩
    · rw [mem_nonZeroDivisors_iff_right]
      intro z hz
      have h0 : z • (b i) = (0 : I) := Subtype.ext (by simpa using hz)
      simpa using congr_arg (fun v ↦ b.repr v i) h0
    · apply le_antisymm
      · intro x hx
        have hmem : (⟨x, hx⟩ : I) ∈ Submodule.span R (Set.range b) := by
          rw [b.span_eq]; trivial
        have hrange : Set.range b = {b i} := by
          ext v
          constructor
          · rintro ⟨i', rfl⟩
            rw [key i']
            rfl
          · rintro rfl
            exact ⟨i, rfl⟩
        rw [hrange, Submodule.mem_span_singleton] at hmem
        obtain ⟨c, hc⟩ := hmem
        rw [Ideal.mem_span_singleton']
        exact ⟨c, by simpa using congr_arg Subtype.val hc⟩
      · rw [Ideal.span_singleton_le_iff_mem]
        exact (b i).2

end FreeIdeal

section Transport

variable {R S S' : Type*} [CommRing R] [CommRing S] [CommRing S'] [Algebra R S] [Algebra R S']

p2m_open_scoped "Ideal" in

theorem Ideal.exists_nonZeroDivisor_map_eq_span_of_algEquiv (e : S ≃ₐ[R] S') (I : Ideal R)
    (h : ∃ g ∈ nonZeroDivisors S, I.map (algebraMap R S) = Ideal.span {g}) :
    ∃ g ∈ nonZeroDivisors S', I.map (algebraMap R S') = Ideal.span {g} := by
  obtain ⟨g, hg, hI⟩ := h
  refine ⟨e g, ?_, ?_⟩
  · rw [mem_nonZeroDivisors_iff_right] at hg ⊢
    intro x hx
    have h1 : e.symm x * g = 0 := e.injective (by simpa using hx)
    simpa using congr_arg e (hg _ h1)
  · rw [← e.toAlgHom.comp_algebraMap, ← Ideal.map_map, hI, Ideal.map_span, Set.image_singleton]
    rfl

end Transport

section LocalAndDescent

variable {A : Type u} [CommRing A]

namespace Submodule p2m_export "Submodule" "span_singleton_eq_range span_eq span_singleton_le_iff_mem mk mem_bot mem_span_singleton_self span mem_map_of_mem mem_span_singleton baseChange map_smul' zero of_localizationSpan' one map_span map toLocalized' map_coe subset_span localized' module smul_def FG comap_comp ext comap_coe add comap span_induction map_le_iff_le_comap" end Submodule
p2m_open_scoped "Submodule" in

theorem Submodule.fg_of_localizationSpan' {M : Type*} [AddCommGroup M] [Module A M]
    {N : Submodule A M} (s : Set A) (hs : Ideal.span s = ⊤)
    {Mₚ : ∀ (_ : s), Type*} [∀ (g : s), AddCommGroup (Mₚ g)] [∀ (g : s), Module A (Mₚ g)]
    {Rₚ : ∀ (_ : s), Type u} [∀ (g : s), CommRing (Rₚ g)] [∀ (g : s), Algebra A (Rₚ g)]
    [∀ (g : s), IsLocalization.Away g.val (Rₚ g)]
    [∀ (g : s), Module (Rₚ g) (Mₚ g)] [∀ (g : s), IsScalarTower A (Rₚ g) (Mₚ g)]
    (ϕ : ∀ (g : s), M →ₗ[A] Mₚ g) [∀ (g : s), IsLocalizedModule (Submonoid.powers g.val) (ϕ g)]
    (H : ∀ (g : s), (N.localized' (Rₚ g) (Submonoid.powers g.1) (ϕ g)).FG) :
    N.FG := by
  simp [← Module.Finite.iff_fg, Module.Finite.of_localizationSpan' s hs
    (fun g ↦ N.toLocalized' (Rₚ g) (Submonoid.powers g.1) (ϕ g))
    (fun g ↦ Module.Finite.iff_fg.mpr (H g))]

namespace Module p2m_export "Module" "FaithfullyFlat.of_comap_surjective Flat Injective Free.chooseBasis Free.ChooseBasisIndex End.isUnit_iff FinitePresentation.fg_ker Finite.exists_fin' equiv Finite.equiv free_of_flat_of_isLocalRing Finite.of_localizationSpan' Finite.of_finite_tensorProduct_of_faithfullyFlat Flat.of_flat_tensorProduct FinitePresentation.of_equiv Free algebraMap_end_apply mk FaithfullyFlat Free.of_equiv Flat.of_linearEquiv Finite.iff_fg End flat_of_isLocalized_span FinitePresentation Flat.trans Flat.lTensor_preserves_injective_linearMap FinitePresentation.exists_free_localizedModule_powers FinitePresentation.fg_ker_iff Finite.of_isLocalizedModule" namespace FinitePresentation p2m_export "Module.FinitePresentation" "mk trans fg_ker of_equiv of_localizationSpan' exists_free_localizedModule_powers fg_ker_iff" end Module.FinitePresentation
p2m_open_scoped "Module Module.FinitePresentation" in

theorem Module.FinitePresentation.of_localizationSpan_of_isLocalizedModule
    {M : Type*} [AddCommGroup M] [Module A M] (s : Set A) (hs : Ideal.span s = ⊤)
    {Mₚ : ∀ (_ : s), Type*} [∀ (g : s), AddCommGroup (Mₚ g)] [∀ (g : s), Module A (Mₚ g)]
    {Rₚ : ∀ (_ : s), Type u} [∀ (g : s), CommRing (Rₚ g)] [∀ (g : s), Algebra A (Rₚ g)]
    [∀ (g : s), IsLocalization.Away g.val (Rₚ g)]
    [∀ (g : s), Module (Rₚ g) (Mₚ g)] [∀ (g : s), IsScalarTower A (Rₚ g) (Mₚ g)]
    (ϕ : ∀ (g : s), M →ₗ[A] Mₚ g) [∀ (g : s), IsLocalizedModule (Submonoid.powers g.val) (ϕ g)]
    (h : ∀ (g : s), Module.FinitePresentation (Rₚ g) (Mₚ g)) :
    Module.FinitePresentation A M := by
  have : Module.Finite A M :=
    Module.Finite.of_localizationSpan' (Rₚ := Rₚ) s hs ϕ (fun _ ↦ inferInstance)
  obtain ⟨n, f, fsurj⟩ := Module.Finite.exists_fin' A M
  rw [← Module.FinitePresentation.fg_ker_iff f fsurj]
  refine Submodule.fg_of_localizationSpan' s hs (Rₚ := Rₚ)
    (fun g ↦ TensorProduct.mk A (Rₚ g) (Fin n → A) 1) (fun g ↦ ?_)
  rw [LinearMap.localized'_ker_eq_ker_localizedMap (Rₚ g) (Submonoid.powers g.1) _ (ϕ g) f]
  apply Module.FinitePresentation.fg_ker
  rw [← LinearMap.range_eq_top] at fsurj ⊢
  simp [← LinearMap.localized'_range_eq_range_localizedMap (Rₚ g) (Submonoid.powers g.1), fsurj]

variable (B : Type*) [CommRing B] [Algebra A B]

p2m_open_scoped "Module Module.FinitePresentation" in

theorem Module.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat'
    (M : Type*) [AddCommGroup M] [Module A M] [Module.FaithfullyFlat A B]
    [Module.FinitePresentation B (B ⊗[A] M)] : Module.FinitePresentation A M := by
  have : Module.Finite A M := Module.Finite.of_finite_tensorProduct_of_faithfullyFlat B
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' A M
  rw [← Module.FinitePresentation.fg_ker_iff f hf, ← Module.Finite.iff_fg]

  set K := LinearMap.ker f
  have hex : Function.Exact (K.subtype.baseChange B) (f.baseChange B) := by
    have := lTensor_exact B (f.exact_subtype_ker_map) hf
    rwa [← LinearMap.baseChange_eq_ltensor, ← LinearMap.baseChange_eq_ltensor] at this
  have hinj : Function.Injective (K.subtype.baseChange B) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
  have hsurj : Function.Surjective (f.baseChange B) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact LinearMap.lTensor_surjective B hf
  let e : B ⊗[A] K ≃ₗ[B] LinearMap.ker (f.baseChange B) :=
    LinearEquiv.ofInjective _ hinj ≪≫ₗ LinearEquiv.ofEq _ _ (LinearMap.exact_iff.mp hex).symm
  have : Module.Finite B (LinearMap.ker (f.baseChange B)) :=
    Module.Finite.iff_fg.mpr (Module.FinitePresentation.fg_ker _ hsurj)
  have : Module.Finite B (B ⊗[A] K) := Module.Finite.equiv e.symm
  exact Module.Finite.of_finite_tensorProduct_of_faithfullyFlat B

p2m_open_scoped "Ideal" in

theorem Ideal.nonempty_tensorProduct_linearEquiv_map [Module.Flat A B] (J : Ideal A) :
    Nonempty (B ⊗[A] J ≃ₗ[B] (J.map (algebraMap A B) : Ideal B)) := by
  let f : B ⊗[A] J →ₗ[B] B :=
    (AlgebraTensorModule.rid _ _ _).toLinearMap ∘ₗ AlgebraTensorModule.lTensor B B J.subtype
  have hf : Function.Injective f := by
    simpa [f] using
      Module.Flat.lTensor_preserves_injective_linearMap (M := B) J.subtype Subtype.val_injective
  have : J.map (algebraMap A B) = LinearMap.range f := by
    refine le_antisymm ?_ ?_
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      use 1 ⊗ₜ ⟨x, hx⟩
      simp [f, Algebra.smul_def]
    · rintro - ⟨x, rfl⟩
      induction x with
      | zero => simp
      | add _ _ _ _ => simp_all [Ideal.add_mem]
      | tmul s x =>
        have : f (s ⊗ₜ[A] x) = s • f (1 ⊗ₜ x) := by simp [f]
        rw [this]
        apply Ideal.mul_mem_left
        simpa [f, Algebra.smul_def] using Ideal.mem_map_of_mem _ x.2
  exact ⟨.ofInjective _ hf ≪≫ₗ .ofEq _ _ this.symm⟩

variable {B}

p2m_open_scoped "Ideal" in

theorem Ideal.free_map_of_free_localizedModule (J : Ideal A) (r : A)
    [Module.Free (Localization (.powers r)) (LocalizedModule (.powers r) J)]
    (Aᵣ : Type*) [CommRing Aᵣ] [Algebra A Aᵣ] [IsLocalization.Away r Aᵣ] :
    Module.Free Aᵣ (J.map (algebraMap A Aᵣ) : Ideal Aᵣ) := by
  letI := RingHomInvPair.of_ringEquiv
    (IsLocalization.algEquiv (.powers r) (Localization (.powers r)) Aᵣ).toRingEquiv
  letI := RingHomInvPair.of_ringEquiv
    (IsLocalization.algEquiv (.powers r) (Localization (.powers r)) Aᵣ).toRingEquiv.symm
  set e := (IsLocalization.algEquiv (.powers r) (Localization (.powers r)) Aᵣ).toRingEquiv
  refine Module.Free.of_equiv (σ := (e : Localization (.powers r) →+* Aᵣ))
    (M := LocalizedModule (.powers r) J) ?_
  refine { __ := IsLocalizedModule.iso (.powers r) (Algebra.idealMap Aᵣ J),
           map_smul' := ?_ }
  intro c x
  obtain ⟨c, t, rfl⟩ := IsLocalization.exists_mk'_eq (.powers r) c
  apply ((Module.End.isUnit_iff _).mp
    (IsLocalizedModule.map_units (Algebra.idealMap Aᵣ J) t)).1
  simp only [e, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
    Module.algebraMap_end_apply, AlgEquiv.toRingEquiv_toRingHom, RingHom.coe_coe,
    IsLocalization.algEquiv_apply, IsLocalization.map_id_mk']
  simp only [← map_smul, ← smul_assoc, IsLocalization.smul_mk'_self, algebraMap_smul]

end LocalAndDescent

section Main

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

namespace Ideal
p2m_open_scoped "Ideal" in

private theorem _root_.Ideal.exists_span_singleton_nonZeroDivisor_of_faithfullyFlat [Module.FaithfullyFlat A B]
    (J : Ideal A)
    (hB : ∀ 𝔮 : PrimeSpectrum B, ∃ u ∉ 𝔮.asIdeal, ∃ g ∈ nonZeroDivisors (Localization.Away u),
      (J.map (algebraMap A B)).map (algebraMap B (Localization.Away u)) = Ideal.span {g})
    (𝔭 : PrimeSpectrum A) :
    ∃ s ∉ 𝔭.asIdeal, ∃ j ∈ nonZeroDivisors (Localization.Away s),
      J.map (algebraMap A (Localization.Away s)) = Ideal.span {j} := by
  classical
  set I : Ideal B := J.map (algebraMap A B) with hIdef

  let T : Set B := {u | ∃ g ∈ nonZeroDivisors (Localization.Away u),
      I.map (algebraMap B (Localization.Away u)) = Ideal.span {g}}
  have hT : Ideal.span T = ⊤ := by
    by_contra hne
    obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨u, hu, g, hg, hgen⟩ := hB ⟨𝔪, h𝔪.isPrime⟩
    exact hu (hle (Ideal.subset_span ⟨g, hg, hgen⟩))
  have hTequiv : ∀ u ∈ T, Nonempty (Localization.Away u ≃ₗ[Localization.Away u]
      (I.map (algebraMap B (Localization.Away u)) : Ideal (Localization.Away u))) := by
    rintro u ⟨g, hg, hgen⟩
    exact ⟨Ideal.equivSpanSingletonOfMemNonZeroDivisors hg ≪≫ₗ LinearEquiv.ofEq _ _ hgen.symm⟩

  have hIflat : Module.Flat B I := by
    refine Module.flat_of_isLocalized_span B I T hT
      (fun u ↦ (I.map (algebraMap B (Localization.Away (u : B))) : Ideal _))
      (fun u ↦ Algebra.idealMap (Localization.Away (u : B)) I) fun u ↦ ?_
    obtain ⟨e⟩ := hTequiv u u.2
    have : Module.Flat (Localization.Away (u : B))
        (I.map (algebraMap B (Localization.Away (u : B))) : Ideal _) := Module.Flat.of_linearEquiv e.symm
    exact Module.Flat.trans B (Localization.Away (u : B)) _
  have hIfp : Module.FinitePresentation B I := by
    refine Module.FinitePresentation.of_localizationSpan_of_isLocalizedModule T hT
      (Rₚ := fun u ↦ Localization.Away (u : B))
      (fun u ↦ Algebra.idealMap (Localization.Away (u : B)) I) fun u ↦ ?_
    obtain ⟨e⟩ := hTequiv u u.2
    exact Module.FinitePresentation.of_equiv e

  obtain ⟨e⟩ := Ideal.nonempty_tensorProduct_linearEquiv_map B J
  have : Module.Flat B (B ⊗[A] J) := Module.Flat.of_linearEquiv e
  have : Module.FinitePresentation B (B ⊗[A] J) := Module.FinitePresentation.of_equiv e.symm
  have hJflat : Module.Flat A J := Module.Flat.of_flat_tensorProduct A J B
  have hJfp : Module.FinitePresentation A J :=
    Module.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat' B J

  have : Module.Finite (Localization.AtPrime 𝔭.asIdeal)
      (LocalizedModule 𝔭.asIdeal.primeCompl J) :=
    Module.Finite.of_isLocalizedModule 𝔭.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap 𝔭.asIdeal.primeCompl J)
  have : Module.Free (Localization.AtPrime 𝔭.asIdeal)
      (LocalizedModule 𝔭.asIdeal.primeCompl J) := Module.free_of_flat_of_isLocalRing
  obtain ⟨s, hs, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    𝔭.asIdeal.primeCompl (LocalizedModule.mkLinearMap 𝔭.asIdeal.primeCompl J)
    (Localization.AtPrime 𝔭.asIdeal)
  refine ⟨s, hs, ?_⟩
  have hfree' : Module.Free (Localization.Away s)
      (J.map (algebraMap A (Localization.Away s)) : Ideal _) :=
    Ideal.free_map_of_free_localizedModule J s _

  refine (Ideal.eq_bot_or_exists_span_singleton_nonZeroDivisor_of_free _).resolve_left ?_
  intro hbot

  have hJfg : J.FG := Module.Finite.iff_fg.mp inferInstance
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ∀ a ∈ J, s ^ n * a = 0 := by
    obtain ⟨F, hF⟩ := hJfg
    have h1 : ∀ a ∈ J, ∃ n : ℕ, s ^ n * a = 0 := by
      intro a ha
      have : algebraMap A (Localization.Away s) a ∈ J.map (algebraMap A (Localization.Away s)) :=
        Ideal.mem_map_of_mem _ ha
      rw [hbot, Ideal.mem_bot,
        IsLocalization.map_eq_zero_iff (.powers s) (Localization.Away s)] at this
      obtain ⟨⟨_, n, rfl⟩, hn⟩ := this
      exact ⟨n, hn⟩
    choose! n hn using h1
    refine ⟨F.sup n, fun a ha ↦ ?_⟩
    rw [← hF] at ha
    refine Submodule.span_induction ?_ ?_ ?_ ?_ ha
    · intro x hx
      have hxJ : x ∈ J := hF ▸ Submodule.subset_span hx
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Finset.le_sup (f := n) hx)
      rw [hk, pow_add, mul_comm (s ^ n x), mul_assoc, hn x hxJ, mul_zero]
    · simp
    · intro x y _ _ hx hy
      rw [mul_add, hx, hy, add_zero]
    · intro c x _ hx
      rw [smul_eq_mul, mul_left_comm, hx, mul_zero]

  obtain ⟨𝔮, h𝔮, h𝔮𝔭⟩ := Ideal.exists_isPrime_liesOver_of_faithfullyFlat (B := B) 𝔭.asIdeal
  obtain ⟨u, hu, g, hg, hgen⟩ := hB ⟨𝔮, h𝔮⟩

  have hkill : algebraMap A (Localization.Away u) (s ^ n) * g = 0 := by
    have hgmem : g ∈ I.map (algebraMap B (Localization.Away u)) :=
      hgen ▸ Ideal.mem_span_singleton_self g
    rw [hIdef, Ideal.map_map, ← IsScalarTower.algebraMap_eq] at hgmem
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hgmem
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_mul, hn a ha, map_zero]
    · simp
    · intro x y _ _ hx hy
      rw [mul_add, hx, hy, add_zero]
    · intro c x _ hx
      rw [smul_eq_mul, mul_left_comm, hx, mul_zero]
  have hzero : algebraMap A (Localization.Away u) (s ^ n) = 0 :=
    (mul_right_mem_nonZeroDivisors_eq_zero_iff hg).mp hkill
  rw [IsScalarTower.algebraMap_apply A B (Localization.Away u),
    IsLocalization.map_eq_zero_iff (.powers u) (Localization.Away u)] at hzero
  obtain ⟨⟨_, m, rfl⟩, hm⟩ := hzero

  have hmem : u ^ m * algebraMap A B (s ^ n) ∈ 𝔮 := by
    rw [show u ^ m * algebraMap A B (s ^ n) = 0 from hm]
    exact 𝔮.zero_mem
  rcases h𝔮.mem_or_mem hmem with h | h
  · exact hu (h𝔮.mem_of_pow_mem _ h)
  · refine hs ?_
    have : s ^ n ∈ 𝔭.asIdeal := by
      rw [h𝔮𝔭.over]
      exact h
    exact 𝔭.isPrime.mem_of_pow_mem _ this

end Ideal
p2m_export "" "Ideal.exists_span_singleton_nonZeroDivisor_of_faithfullyFlat"
namespace Ideal
p2m_open_scoped "Ideal" in

private theorem _root_.Ideal.exists_span_singleton_nonZeroDivisor_of_faithfullyFlat'
    [Module.FaithfullyFlat A B] (J : Ideal A)
    (hB : ∀ 𝔮 : PrimeSpectrum B, ∃ u ∉ 𝔮.asIdeal, ∃ g ∈ nonZeroDivisors (Localization.Away u),
      (J.map (algebraMap A B)).map (algebraMap B (Localization.Away u)) = Ideal.span {g})
    (𝔭 : PrimeSpectrum A) :
    ∃ s ∉ 𝔭.asIdeal, ∀ (Aₛ : Type*) [CommRing Aₛ] [Algebra A Aₛ] [IsLocalization.Away s Aₛ],
      ∃ j ∈ nonZeroDivisors Aₛ, J.map (algebraMap A Aₛ) = Ideal.span {j} := by
  obtain ⟨s, hs, h⟩ := J.exists_span_singleton_nonZeroDivisor_of_faithfullyFlat hB 𝔭
  exact ⟨s, hs, fun Aₛ _ _ _ ↦ Ideal.exists_nonZeroDivisor_map_eq_span_of_algEquiv
    (IsLocalization.algEquiv (.powers s) (Localization.Away s) Aₛ) J h⟩

end Ideal
p2m_export "" "Ideal.exists_span_singleton_nonZeroDivisor_of_faithfullyFlat'"
p2m_open_scoped "Ideal" in

theorem Ideal.exists_span_singleton_nonZeroDivisor_of_flat_of_surjective [Module.Flat A B]
    (hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap A B))) (J : Ideal A)
    (hB : ∀ 𝔮 : PrimeSpectrum B, ∃ u ∉ 𝔮.asIdeal, ∃ g ∈ nonZeroDivisors (Localization.Away u),
      (J.map (algebraMap A B)).map (algebraMap B (Localization.Away u)) = Ideal.span {g})
    (𝔭 : PrimeSpectrum A) :
    ∃ s ∉ 𝔭.asIdeal, ∃ j ∈ nonZeroDivisors (Localization.Away s),
      J.map (algebraMap A (Localization.Away s)) = Ideal.span {j} :=
  have := Module.FaithfullyFlat.of_comap_surjective hsurj
  J.exists_span_singleton_nonZeroDivisor_of_faithfullyFlat hB 𝔭

end Main

open CategoryTheory CategoryTheory.Limits TensorProduct

namespace Algebra
p2m_export "Algebra" "TensorProduct.rid ofId IsPushout TensorProduct.includeRight mk algebraMap TensorProduct.lTensor_ker IsPushout.equiv idealMap smul_def TensorProduct.includeLeft id mem_bot TensorProduct.map subsingleton FinitePresentation"
namespace IsPushout
p2m_export "Algebra.IsPushout" "of_equiv mk equiv symm"
p2m_open "Algebra.IsPushout Algebra"

theorem ker_algebraMap_eq_map_ker
    (R B C P : Type*) [CommRing R] [CommRing B] [CommRing C] [CommRing P]
    [Algebra R B] [Algebra R C] [Algebra B P] [Algebra C P] [Algebra R P]
    [IsScalarTower R B P] [IsScalarTower R C P] [Algebra.IsPushout R B C P]
    (hC : Function.Surjective (algebraMap R C)) :
    RingHom.ker (algebraMap B P) = (RingHom.ker (algebraMap R C)).map (algebraMap R B) := by
  let e : B ⊗[R] C ≃ₐ[B] P := Algebra.IsPushout.equiv R B C P

  have h1 : algebraMap B P = e.toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := B) (B := C)).toRingHom := by
    ext b
    simp [e]
  rw [h1, RingHom.ker_comp_of_injective _ e.toRingEquiv.injective]

  let g : R →ₐ[R] C := Algebra.ofId R C
  have h2 : (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := B) (B := C)).toRingHom =
      (Algebra.TensorProduct.map (AlgHom.id R B) g).toRingHom.comp
        (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := B) (B := R)).toRingHom := by
    ext b
    simp [g]
  have h3 : RingHom.ker (Algebra.TensorProduct.map (AlgHom.id R B) g).toRingHom =
      (RingHom.ker (algebraMap R C)).map
        (Algebra.TensorProduct.includeRight (R := R) (A := B) (B := R)).toRingHom := by
    have := Algebra.TensorProduct.lTensor_ker (A := B) g hC
    simp [g] at this
    exact this
  rw [h2, ← RingHom.comap_ker, h3]

  let r : B ⊗[R] R ≃ₐ[R] B := Algebra.TensorProduct.rid R R B
  have h4 : (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := B) (B := R)).toRingHom =
      (r.toRingEquiv.symm : B →+* B ⊗[R] R) := by
    ext b
    apply r.toRingEquiv.injective
    simp [r]
  have h5 : (algebraMap R B) = (r.toRingEquiv : B ⊗[R] R →+* B).comp
      (Algebra.TensorProduct.includeRight (R := R) (A := B) (B := R)).toRingHom := by
    ext x
    simp [r, Algebra.smul_def]
  rw [h4, h5, ← Ideal.map_map, Ideal.comap_coe, Ideal.map_coe, Ideal.comap_symm]

end Algebra.IsPushout

namespace CommRingCat
p2m_export "CommRingCat" "hom_comp free of flat toAlgHom Hom isPushout_iff_isPushout"
p2m_open "CommRingCat"

theorem ker_eq_map_ker_of_isPushout {R B C P : CommRingCat.{u}} {f : R ⟶ B} {g : R ⟶ C}
    {inl : B ⟶ P} {inr : C ⟶ P} (h : IsPushout f g inl inr)
    (hg : Function.Surjective g.hom) :
    RingHom.ker inl.hom = (RingHom.ker g.hom).map f.hom := by
  algebraize [f.hom, g.hom, inl.hom, inr.hom, inl.hom.comp f.hom]
  have hw : inl.hom.comp f.hom = inr.hom.comp g.hom := by
    simpa only [CommRingCat.hom_comp] using congr(($(h.w)).hom)
  have : IsScalarTower R C P := .of_algebraMap_eq' hw
  have : Algebra.IsPushout R B C P := CommRingCat.isPushout_iff_isPushout.mp h
  exact Algebra.IsPushout.ker_algebraMap_eq_map_ker R B C P hg

end CommRingCat

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.resLE_comp_ι Scheme.Hom.map_appLE Scheme.Opens.topIso_inv Surjective isPushout_appTop_of_isPullback Scheme.Hom exists_basicOpen_le_affine_inter Scheme.Opens.ι_appIso IsFinite isAffine_of_isAffineHom IsAffine Spec Scheme Scheme.Hom.appTop Scheme.Opens.topIso_hom Flat isAffineOpen_top IsAffineOpen.comap_primeIdealOf_appLE Scheme.IdealSheafData.ideal_map_of_isAffineHom IsAffineOpen IsAffineOpen.fromSpec_primeIdealOf Scheme.Hom.ker_apply Scheme.Opens Scheme.Hom.appLE_map Scheme.Hom.app_eq_appLE Flat.flat_appLE Scheme.Hom.resLE_app_top Scheme.Opens.ι_image_top IsAffineHom geometrically Scheme.IdealSheafData"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Hom.resLE_comp_ι Hom.map_appLE mem_basicOpen Opens.topIso_inv Hom mk Γ Opens.ι_appIso topIso_hom Hom.appTop Opens.topIso_hom affineBasicOpen affineOpens basicOpen IdealSheafData.ideal_map_of_isAffineHom isBasis_affineOpens Hom.ker_apply Opens Hom.appLE_map Hom.app_eq_appLE Hom.resLE_app_top Opens.ι_image_top basicOpen_le restrict IdealSheafData"
namespace IdealSheafData
p2m_export "AlgebraicGeometry.Scheme.IdealSheafData" "comap_comp mk map subscheme subschemeι_app_surjective ideal ideal_map_of_isAffineHom subschemeι comap map_ideal_basicOpen map_ideal ker_subschemeι_app ideal_comap_of_isOpenImmersion IsInvertible resLE"
p2m_open "AlgebraicGeometry.Scheme.IdealSheafData AlgebraicGeometry.Scheme AlgebraicGeometry"

variable {X Y : Scheme.{u}}

theorem ideal_comap_top [IsAffine X] [IsAffine Y] (I : X.IdealSheafData) (f : Y ⟶ X) :
    (I.comap f).ideal ⟨⊤, isAffineOpen_top Y⟩ =
      (I.ideal ⟨⊤, isAffineOpen_top X⟩).map f.appTop.hom := by
  have : IsAffine I.subscheme := isAffine_of_isAffineHom I.subschemeι
  have H := isPushout_appTop_of_isPullback (IsPullback.of_hasPullback f I.subschemeι)
  have := CommRingCat.ker_eq_map_ker_of_isPushout H
    (I.subschemeι_app_surjective ⟨⊤, isAffineOpen_top X⟩)
  rw [← ker_subschemeι_app I ⟨⊤, isAffineOpen_top X⟩, comap, Scheme.Hom.ker_apply]
  exact this

set_option backward.isDefEq.respectTransparency false in

theorem ideal_comap_of_le (I : X.IdealSheafData) (f : Y ⟶ X) (U : X.affineOpens)
    (V : Y.affineOpens) (hVU : (V : Y.Opens) ≤ f ⁻¹ᵁ (U : X.Opens)) :
    (I.comap f).ideal V = (I.ideal U).map (f.appLE U V hVU).hom := by

  suffices key : ∀ (U' : X.affineOpens) (V' : Y.affineOpens),
      U' = ⟨(U : X.Opens).ι ''ᵁ ⊤, by simpa only [Scheme.Opens.ι_image_top] using U.2⟩ →
      V' = ⟨(V : Y.Opens).ι ''ᵁ ⊤, by simpa only [Scheme.Opens.ι_image_top] using V.2⟩ →
      ∀ (e : (V' : Y.Opens) ≤ f ⁻¹ᵁ (U' : X.Opens)),
        (I.comap f).ideal V' = (I.ideal U').map (f.appLE U' V' e).hom from
    key U V (Subtype.ext (U : X.Opens).ι_image_top.symm)
      (Subtype.ext (V : Y.Opens).ι_image_top.symm) hVU
  rintro _ _ rfl rfl e
  have : IsAffine (U : X.Opens) := U.2
  have : IsAffine (V : Y.Opens) := V.2

  have h := ideal_comap_top (I.comap (U : X.Opens).ι) (f.resLE U V hVU)
  rw [← comap_comp, Scheme.Hom.resLE_comp_ι, comap_comp,
    ideal_comap_of_isOpenImmersion (I.comap f) (V : Y.Opens).ι,
    ideal_comap_of_isOpenImmersion I (U : X.Opens).ι] at h
  simp only [Scheme.Opens.ι_appIso, Iso.refl_inv, Scheme.Hom.appTop,
    Scheme.Hom.resLE_app_top] at h
  erw [CommRingCat.hom_id, Ideal.comap_id] at h
  erw [CommRingCat.hom_id, Ideal.comap_id] at h
  convert h using 2
  all_goals try rfl
  congr 1
  simp only [Scheme.Opens.topIso_hom, Scheme.Opens.topIso_inv, eqToHom_op, Scheme.Hom.appLE_map,
    Scheme.Hom.map_appLE]

private theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.ideal_comap_of_isAffineHom (I : X.IdealSheafData) (f : Y ⟶ X) [IsAffineHom f]
    (U : X.affineOpens) :
    (I.comap f).ideal ⟨f ⁻¹ᵁ U, U.2.preimage f⟩ = (I.ideal U).map (f.app U).hom := by
  rw [Scheme.Hom.app_eq_appLE]
  exact ideal_comap_of_le I f U ⟨f ⁻¹ᵁ U, U.2.preimage f⟩ le_rfl

p2m_export "AlgebraicGeometry.Scheme.IdealSheafData" "ideal_comap_of_isAffineHom"
end AlgebraicGeometry.Scheme.IdealSheafData

section SchemeGlue

p2m_open "CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_isInvertible_of_isInvertible_comap.AlgebraicGeometry"

namespace InvertibleIdealDescent

theorem chart {X Y : Scheme.{u}} (π : Y ⟶ X) [IsAffineHom π] [Flat π] [Surjective π]
    (I : X.IdealSheafData) (h : (I.comap π).IsInvertible) (U : X.affineOpens) (x : X)
    (hxU : x ∈ (U : X.Opens)) :
    ∃ s : Γ(X, U), x ∈ X.basicOpen s ∧
      ∃ g ∈ nonZeroDivisors Γ(X, X.affineBasicOpen s),
        I.ideal (X.affineBasicOpen s) = Ideal.span {g} := by
  classical
  have hU : IsAffineOpen (U : X.Opens) := U.2

  have hG := I.ideal_comap_of_isAffineHom π U
  set V : Y.affineOpens := ⟨π ⁻¹ᵁ U, U.2.preimage π⟩ with hVdef
  have hV : IsAffineOpen (V : Y.Opens) := V.2

  letI alg : Algebra Γ(X, U) Γ(Y, V) := (π.appLE U V le_rfl).hom.toAlgebra
  have hφ : algebraMap Γ(X, U) Γ(Y, V) = (π.appLE U V le_rfl).hom := rfl
  have happ : (π.app U).hom = algebraMap Γ(X, U) Γ(Y, V) := by
    rw [hφ, Scheme.Hom.app_eq_appLE]

  haveI : Module.Flat Γ(X, U) Γ(Y, V) :=
    Flat.flat_appLE π hU hV le_rfl

  have hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap Γ(X, U) Γ(Y, V))) := by
    intro 𝔭
    have h𝔭U : hU.fromSpec 𝔭 ∈ (U : X.Opens) := by
      rw [← SetLike.mem_coe, ← hU.range_fromSpec]
      exact Set.mem_range_self 𝔭
    obtain ⟨y, hy⟩ := π.surjective (hU.fromSpec 𝔭)
    have hyV : y ∈ (V : Y.Opens) := show π y ∈ (U : X.Opens) by rwa [hy]
    refine ⟨hV.primeIdealOf ⟨y, hyV⟩, hU.fromSpec.isOpenEmbedding.injective ?_⟩
    rw [hφ, IsAffineOpen.comap_primeIdealOf_appLE (U : X.Opens) hU (V : Y.Opens) hV le_rfl hyV,
      IsAffineOpen.fromSpec_primeIdealOf]
    exact hy
  haveI : Module.FaithfullyFlat Γ(X, U) Γ(Y, V) := Module.FaithfullyFlat.of_comap_surjective hsurj

  have hB : ∀ 𝔮 : PrimeSpectrum Γ(Y, V), ∃ u ∉ 𝔮.asIdeal,
      ∃ g ∈ nonZeroDivisors (Localization.Away u),
        ((I.ideal U).map (algebraMap Γ(X, U) Γ(Y, V))).map
          (algebraMap Γ(Y, V) (Localization.Away u)) = Ideal.span {g} := by
    intro 𝔮
    have hyV : hV.fromSpec 𝔮 ∈ (V : Y.Opens) := by
      rw [← SetLike.mem_coe, ← hV.range_fromSpec]
      exact Set.mem_range_self 𝔮
    obtain ⟨W, u', hyu', g', hg', hgen'⟩ := h (hV.fromSpec 𝔮)

    obtain ⟨b, b', hbb', hyb⟩ :=
      exists_basicOpen_le_affine_inter hV (Y.affineBasicOpen u').2 (hV.fromSpec 𝔮) ⟨hyV, hyu'⟩
    have hWW' : (Y.affineBasicOpen (U := V) b : Y.Opens) ≤ Y.affineBasicOpen u' :=
      hbb'.trans_le (Y.basicOpen_le b')
    refine ⟨b, ?_, ?_⟩
    ·
      have : 𝔮 ∈ hV.fromSpec ⁻¹ᵁ Y.basicOpen b := hyb
      rw [hV.fromSpec_preimage_basicOpen] at this
      exact (PrimeSpectrum.mem_basicOpen _ _).mp this
    · haveI := hV.isLocalization_basicOpen b
      refine Ideal.exists_nonZeroDivisor_map_eq_span_of_algEquiv
        (IsLocalization.algEquiv (.powers b) Γ(Y, Y.basicOpen b) (Localization.Away b)) _ ?_
      refine ⟨(Y.presheaf.map (homOfLE hWW').op).hom g', ?_, ?_⟩
      ·
        letI := (Y.presheaf.map (homOfLE hWW').op).hom.toAlgebra
        haveI := (Y.affineBasicOpen u').2.isLocalization_of_eq_basicOpen b' (homOfLE hWW') hbb'
        exact IsLocalization.nonZeroDivisors_le_comap (M := .powers b')
          (S := Γ(Y, Y.affineBasicOpen (U := V) b)) hg'
      ·
        have e1 : (I.comap π).ideal (Y.affineBasicOpen (U := V) b) =
            Ideal.span {(Y.presheaf.map (homOfLE hWW').op).hom g'} := by
          rw [← (I.comap π).map_ideal (U := Y.affineBasicOpen (U := V) b)
            (V := Y.affineBasicOpen u') hWW', hgen', Ideal.map_span, Set.image_singleton]
          rfl
        have e2 : (I.comap π).ideal (Y.affineBasicOpen (U := V) b) =
            ((I.ideal U).map (algebraMap Γ(X, U) Γ(Y, V))).map
              (algebraMap Γ(Y, V) Γ(Y, Y.basicOpen b)) := by
          rw [← (I.comap π).map_ideal_basicOpen V b, hG, happ]
          rfl
        exact e2.symm.trans e1

  obtain ⟨s, hs, hloc⟩ := (I.ideal U).exists_span_singleton_nonZeroDivisor_of_faithfullyFlat' hB
    (hU.primeIdealOf ⟨x, hxU⟩)
  haveI := hU.isLocalization_basicOpen s
  obtain ⟨j, hj, hgen⟩ := hloc Γ(X, X.basicOpen s)
  refine ⟨s, ?_, j, hj, ?_⟩
  · have : hU.primeIdealOf ⟨x, hxU⟩ ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen s := by
      rw [hU.fromSpec_preimage_basicOpen]
      exact (PrimeSpectrum.mem_basicOpen _ _).mpr hs
    have hx : hU.fromSpec (hU.primeIdealOf ⟨x, hxU⟩) = x := hU.fromSpec_primeIdealOf ⟨x, hxU⟩
    rw [← hx]
    exact this
  · rw [← I.map_ideal_basicOpen U s]
    exact hgen

theorem isInvertible_of_isInvertible_comap {X Y : Scheme.{u}} (π : Y ⟶ X) [IsAffineHom π] [Flat π]
    [Surjective π] (I : X.IdealSheafData) (h : (I.comap π).IsInvertible) : I.IsInvertible := by
  intro x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  obtain ⟨s, hxs, g, hg, hgen⟩ := chart π I h ⟨U, hU⟩ x hxU
  exact ⟨⟨U, hU⟩, s, hxs, g, hg, hgen⟩

end InvertibleIdealDescent

end SchemeGlue

open CategoryTheory _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_isInvertible_of_isInvertible_comap.AlgebraicGeometry in

theorem solution
    {X Y : Scheme.{u}} (π : Y ⟶ X) [IsFinite π] [Flat π] [Surjective π]
    (I : X.IdealSheafData) (h : (I.comap π).IsInvertible) : I.IsInvertible :=
  InvertibleIdealDescent.isInvertible_of_isInvertible_comap π I h

end S_AlgebraicGeometry_Scheme_IdealSheafData_isInvertible_of_isInvertible_comap
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_isInvertible_of_isInvertible_comap (solution)
