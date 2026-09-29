-- Prove2me | solution 1 for AlgHom.length_cotangent_eq_of_exists_presentation
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/dc098b7c-2f48-5e6d-9fa4-04344f0c3671

import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.FiniteLength
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Finiteness.Ideal
import Theorems.Thm_MvPowerSeries_annihilator_ker_eq_span_det
import Theorems.Thm_AlgHom_length_quotient_congruenceIdeal_le_length_cotangent
import Theorems.Thm_MvPowerSeries_mem_pow_span_X_of_coeff_eq_zero
import Theorems.Thm_MvPowerSeries_isAdicComplete_maximalIdeal
import Theorems.Thm_MvPowerSeries_exists_algHom_apply_X_eq
import Theorems.Thm_MvPowerSeries_algHom_ext_of_apply_X_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgHom_length_cotangent_eq_of_exists_presentation

universe u v w x

open IsLocalRing Module
open scoped Matrix

namespace FrobDictCONV

section LengthPID

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪]

theorem length_quotient_span_mul (a b : 𝒪) (hb : b ≠ 0) :
    Module.length 𝒪 (𝒪 ⧸ Ideal.span {a * b}) =
      Module.length 𝒪 (𝒪 ⧸ Ideal.span {a}) + Module.length 𝒪 (𝒪 ⧸ Ideal.span {b}) := by

  let f : (𝒪 ⧸ Ideal.span {a}) →ₗ[𝒪] (𝒪 ⧸ Ideal.span {a * b}) :=
    Submodule.mapQ (Ideal.span {a}) (Ideal.span {a * b}) (LinearMap.lsmul 𝒪 𝒪 b) (by
      intro x hx
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
      change b • (c * a) ∈ Ideal.span {a * b}
      exact Ideal.mem_span_singleton'.mpr ⟨c, by rw [smul_eq_mul]; ring⟩)
  let g : (𝒪 ⧸ Ideal.span {a * b}) →ₗ[𝒪] (𝒪 ⧸ Ideal.span {b}) :=
    Submodule.mapQ (Ideal.span {a * b}) (Ideal.span {b}) LinearMap.id (by
      intro x hx
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
      exact Ideal.mem_span_singleton'.mpr ⟨c * a, by simp [mul_assoc]⟩)
  have hfx : ∀ x : 𝒪, f (Submodule.Quotient.mk x) = Submodule.Quotient.mk (b * x) := fun x => rfl
  have hgx : ∀ x : 𝒪, g (Submodule.Quotient.mk x) = Submodule.Quotient.mk x := fun x => rfl
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [hfx, Submodule.Quotient.mk_eq_zero] at hx
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hx
    have : x = c * a := by
      have h1 : b * x = b * (c * a) := by rw [← hc]; ring
      exact mul_left_cancel₀ hb h1
    exact (Submodule.Quotient.mk_eq_zero _).mpr (Ideal.mem_span_singleton'.mpr ⟨c, this.symm⟩)
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact ⟨Submodule.Quotient.mk y, hgx y⟩
  have hfg : Function.Exact f g := by
    intro y
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    constructor
    · intro hy
      rw [hgx, Submodule.Quotient.mk_eq_zero] at hy
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hy
      exact ⟨Submodule.Quotient.mk c, by rw [hfx]; exact congrArg _ (mul_comm b c)⟩
    · rintro ⟨x, hx⟩
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [hfx] at hx
      rw [← hx, hgx, Submodule.Quotient.mk_eq_zero]
      exact Ideal.mem_span_singleton'.mpr ⟨x, by rw [mul_comm]⟩
  rw [Module.length_eq_add_of_exact f g hf hg hfg]

theorem length_quotient_span_prod {ι : Type*} (s : Finset ι) (a : ι → 𝒪) (ha : ∀ i ∈ s, a i ≠ 0) :
    Module.length 𝒪 (𝒪 ⧸ Ideal.span {∏ i ∈ s, a i}) =
      ∑ i ∈ s, Module.length 𝒪 (𝒪 ⧸ Ideal.span {a i}) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    refine Module.length_eq_zero_iff.mpr ?_
    rw [Submodule.Quotient.subsingleton_iff, Finset.prod_empty]
    exact Ideal.span_singleton_one
  | insert j s hj ih =>
    have e := Submodule.quotEquivOfEq (Ideal.span {∏ i ∈ insert j s, a i})
      (Ideal.span {(∏ i ∈ s, a i) * a j}) (by rw [Finset.prod_insert hj, mul_comm])
    rw [e.length_eq, Finset.sum_insert hj,
      length_quotient_span_mul _ _ (ha j (Finset.mem_insert_self j s)), add_comm,
      ih (fun i hi => ha i (Finset.mem_insert_of_mem hi))]

end LengthPID

end FrobDictCONV

namespace FrobDictCONV

section Cotangent

variable {𝒪 : Type*} [CommRing 𝒪] {R : Type*} [CommRing R] [Algebra 𝒪 R] (π : R →ₐ[𝒪] 𝒪)

theorem smul_cotangent_eq (r : R) (m : (RingHom.ker π).Cotangent) : r • m = (π r) • m := by
  obtain ⟨x, rfl⟩ := (RingHom.ker π).toCotangent_surjective m
  rw [← IsScalarTower.algebraMap_smul R (π r), ← sub_eq_zero, ← sub_smul, ← map_smul,
    Ideal.toCotangent_eq_zero, sq]
  refine Ideal.mul_mem_mul ?_ x.2
  simp [RingHom.mem_ker]

variable {n : ℕ} (a : Fin n → R) (hI : Ideal.span (Set.range a) = RingHom.ker π)

def gen (i : Fin n) : RingHom.ker π := ⟨a i, hI ▸ Ideal.subset_span (Set.mem_range_self i)⟩

@[scoped simp] theorem coe_gen (i : Fin n) : (gen π a hI i : R) = a i := rfl

noncomputable def psi : (Fin n → 𝒪) →ₗ[𝒪] (RingHom.ker π).Cotangent :=
  Fintype.linearCombination 𝒪 (fun i => (RingHom.ker π).toCotangent (gen π a hI i))

theorem psi_apply (w : Fin n → 𝒪) :
    psi π a hI w = (RingHom.ker π).toCotangent (∑ i, algebraMap 𝒪 R (w i) • gen π a hI i) := by
  simp only [psi, Fintype.linearCombination_apply, map_sum, map_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [IsScalarTower.algebraMap_smul]

include hI in
theorem psi_surjective : Function.Surjective (psi π a hI) := by
  intro m
  obtain ⟨x, rfl⟩ := (RingHom.ker π).toCotangent_surjective m
  have hx : (x : R) ∈ Ideal.span (Set.range a) := by rw [hI]; exact x.2
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hx
  refine ⟨fun i => π (c i), ?_⟩
  rw [psi_apply]
  have hx' : x = ∑ i, c i • gen π a hI i := by
    apply Subtype.ext
    simp [← hc]
  rw [hx', map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, map_smul, IsScalarTower.algebraMap_smul, ← smul_cotangent_eq]

theorem exists_syzygy_of_psi_eq_zero (w : Fin n → 𝒪) (hw : psi π a hI w = 0) :
    ∃ c : Fin n → R, (∀ i, c i ∈ RingHom.ker π) ∧
      ∑ i, (algebraMap 𝒪 R (w i) - c i) * a i = 0 := by
  classical
  rw [psi_apply, Ideal.toCotangent_eq_zero] at hw
  have h2 : (RingHom.ker π) ^ 2 = (RingHom.ker π) • Ideal.span (Set.range a) := by
    rw [sq, hI]; rfl
  rw [h2] at hw
  have hw' : (∑ i, algebraMap 𝒪 R (w i) * a i) ∈ (RingHom.ker π) • Submodule.span R (Set.range a) := by
    convert hw using 1
    simp [Algebra.smul_def]
  obtain ⟨cf, hcf, hsum⟩ := (Submodule.mem_ideal_smul_span_iff_exists_sum _ _ _).mp hw'
  refine ⟨fun i => cf i, hcf, ?_⟩
  rw [Finsupp.sum_fintype _ _ (by simp)] at hsum
  simp only [sub_mul, Finset.sum_sub_distrib, sub_eq_zero]
  rw [← hsum]
  simp [smul_eq_mul]

theorem det_mem_eta (v : Fin n → (Fin n → 𝒪)) (hv : ∀ j, psi π a hI (v j) = 0) :
    (Matrix.of fun i j => v j i).det ∈ (RingHom.ker π).annihilator.map π := by
  classical
  choose C hC hCsum using fun j => exists_syzygy_of_psi_eq_zero π a hI (v j) (hv j)
  let V : Matrix (Fin n) (Fin n) R := Matrix.of fun j i => algebraMap 𝒪 R (v j i) - C j i
  have hVa : V *ᵥ a = 0 := by
    ext j
    simp only [V, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
    exact hCsum j
  have hdet : ∀ i, V.det * a i = 0 := by
    intro i
    have h := congrArg (fun u => (V.adjugate *ᵥ u) i) hVa
    simp only [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.mulVec_zero, Pi.zero_apply] at h
    rw [Matrix.smul_mulVec, Matrix.one_mulVec] at h
    simpa using h
  have hann : V.det ∈ (RingHom.ker π).annihilator := by
    rw [← hI, show Ideal.span (Set.range a) = Submodule.span R (Set.range a) from rfl,
      Submodule.mem_annihilator_span]
    rintro ⟨_, ⟨i, rfl⟩⟩
    exact hdet i
  have hmap : π V.det = (Matrix.of fun i j => v j i).det := by
    rw [AlgHom.map_det, ← Matrix.det_transpose]
    congr 1
    ext i j
    have : π (C j i) = 0 := hC j i
    simp [V, Matrix.transpose_apply, AlgHom.mapMatrix_apply, this]
  rw [← hmap]
  exact Ideal.mem_map_of_mem _ hann

end Cotangent

section DVR

variable {𝒪 : Type u} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]

theorem length_self_eq_top : Module.length 𝒪 𝒪 = ⊤ := by
  by_contra h
  have hfl := Module.length_ne_top_iff.mp h
  obtain ⟨-, hart⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hfl
  haveI : IsArtinianRing 𝒪 := hart
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪
  exact hϖ.not_isUnit (IsArtinianRing.isUnit_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero))

theorem length_quotient_bot_eq_top : Module.length 𝒪 (𝒪 ⧸ (⊥ : Ideal 𝒪)) = ⊤ := by
  rw [(Submodule.quotEquivOfEqBot (⊥ : Ideal 𝒪) rfl).length_eq, length_self_eq_top]

end DVR

section SpanX

variable {𝒪 : Type u} [CommRing 𝒪] {n : ℕ}

theorem mem_span_X_iff (q : MvPowerSeries (Fin n) 𝒪) :
    q ∈ Ideal.span (Set.range (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) 𝒪)) ↔
      MvPowerSeries.constantCoeff q = 0 := by
  constructor
  · intro hq
    have hle : Ideal.span (Set.range (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) 𝒪)) ≤
        RingHom.ker MvPowerSeries.constantCoeff :=
      Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact MvPowerSeries.constantCoeff_X i)
    exact hle hq
  · intro hq
    have h := MvPowerSeries.mem_pow_span_X_of_coeff_eq_zero 1 q (fun m hm => by
      have hm0 : m = 0 := (Finsupp.degree_eq_zero_iff m).mp (by omega)
      subst hm0
      rwa [MvPowerSeries.coeff_zero_eq_constantCoeff_apply])
    rwa [pow_one] at h

theorem ker_eq_span (f : Fin n → MvPowerSeries (Fin n) 𝒪)
    (hfX : ∀ i, f i ∈ Ideal.span (Set.range (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) 𝒪)))
    (π : (MvPowerSeries (Fin n) 𝒪 ⧸ Ideal.span (Set.range f)) →ₐ[𝒪] 𝒪)
    (hπ : (π : _ →+* 𝒪).comp (Ideal.Quotient.mk (Ideal.span (Set.range f))) = MvPowerSeries.constantCoeff) :
    Ideal.span (Set.range fun i => Ideal.Quotient.mk (Ideal.span (Set.range f)) (MvPowerSeries.X i)) =
      RingHom.ker π := by
  have hπ' : ∀ q, π (Ideal.Quotient.mk _ q) = MvPowerSeries.constantCoeff q := fun q => by
    have := RingHom.congr_fun hπ q
    simpa using this
  have hJI : Ideal.span (Set.range f) ≤
      Ideal.span (Set.range (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) 𝒪)) :=
    Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hfX i)
  have hmap : Ideal.span (Set.range fun i => Ideal.Quotient.mk (Ideal.span (Set.range f)) (MvPowerSeries.X i)) =
      (Ideal.span (Set.range (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) 𝒪))).map
        (Ideal.Quotient.mk (Ideal.span (Set.range f))) := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  rw [hmap]
  ext t
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective t
  rw [RingHom.mem_ker, hπ', ← mem_span_X_iff, Ideal.mem_quotient_iff_mem_sup, sup_eq_left.mpr hJI]

end SpanX

section Core

variable {𝒪 : Type u} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  [IsAdicComplete (maximalIdeal 𝒪) 𝒪] {n : ℕ}

omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsAdicComplete (maximalIdeal 𝒪) 𝒪] in

theorem basisFun_det_eq (v : Fin n → (Fin n → 𝒪)) :
    (Pi.basisFun 𝒪 (Fin n)).det v = (Matrix.of fun i j => v j i).det := by
  rw [Module.Basis.det_apply]
  congr 1

theorem core (g : Matrix (Fin n) (Fin n) (MvPowerSeries (Fin n) 𝒪))
    (f : Fin n → MvPowerSeries (Fin n) 𝒪) (hf : ∀ i, f i = ∑ j, g i j * MvPowerSeries.X j)
    [Module.Finite 𝒪 (MvPowerSeries (Fin n) 𝒪 ⧸ Ideal.span (Set.range f))]
    [Module.Free 𝒪 (MvPowerSeries (Fin n) 𝒪 ⧸ Ideal.span (Set.range f))]
    (π : (MvPowerSeries (Fin n) 𝒪 ⧸ Ideal.span (Set.range f)) →ₐ[𝒪] 𝒪)
    (hπ : (π : _ →+* 𝒪).comp (Ideal.Quotient.mk (Ideal.span (Set.range f))) =
      MvPowerSeries.constantCoeff) :
    Module.length 𝒪 (RingHom.ker π).Cotangent =
      Module.length 𝒪 (𝒪 ⧸ (RingHom.ker π).annihilator.map π) := by
  classical
  set T := MvPowerSeries (Fin n) 𝒪 ⧸ Ideal.span (Set.range f)
  have hπ' : ∀ q, π (Ideal.Quotient.mk _ q) = MvPowerSeries.constantCoeff q := fun q => by
    have := RingHom.congr_fun hπ q
    simpa using this
  refine le_antisymm ?_ ?_
  swap
  ·
    haveI : IsNoetherian 𝒪 T := inferInstance
    haveI : IsNoetherianRing T := isNoetherian_of_tower 𝒪 inferInstance
    exact AlgHom.length_quotient_congruenceIdeal_le_length_cotangent (AlgHom.id 𝒪 T)
      Function.surjective_id π π (AlgHom.comp_id π) (IsNoetherian.noetherian _)

  obtain ⟨-, hη⟩ := MvPowerSeries.annihilator_ker_eq_span_det n g f hf π hπ
  set δ := (g.map MvPowerSeries.constantCoeff).det with hδdef
  rw [hη]
  by_cases hδ : δ = 0
  · rw [hδ, Ideal.span_singleton_eq_bot.mpr rfl, length_quotient_bot_eq_top]
    exact le_top

  have hfX : ∀ i, f i ∈ Ideal.span (Set.range (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) 𝒪)) :=
    fun i => by
      rw [hf i]
      exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)
  let a : Fin n → T := fun i => Ideal.Quotient.mk _ (MvPowerSeries.X i)
  have hI : Ideal.span (Set.range a) = RingHom.ker π := ker_eq_span f hfX π hπ
  let ψ := psi π a hI
  have hψ := psi_surjective π a hI
  let v : Fin n → (Fin n → 𝒪) := fun i j => MvPowerSeries.constantCoeff (g i j)
  have hv : ∀ i, ψ (v i) = 0 := fun i => by

    have h0 : (∑ j, (Ideal.Quotient.mk (Ideal.span (Set.range f)) (g i j)) • gen π a hI j :
        RingHom.ker π) = 0 := by
      apply Subtype.ext
      simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul, coe_gen, smul_eq_mul, ZeroMemClass.coe_zero,
        a, ← map_mul, ← map_sum, ← hf i]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
    have h1 := congrArg (RingHom.ker π).toCotangent h0
    rw [map_zero, map_sum] at h1
    simp only [map_smul, smul_cotangent_eq, hπ'] at h1
    have h2 : ψ (v i) = ∑ j, (v i j) • (RingHom.ker π).toCotangent (gen π a hI j) := by
      simp [ψ, psi, Fintype.linearCombination_apply]
    rw [h2]
    exact h1
  set N := LinearMap.ker ψ
  have hvN : ∀ i, v i ∈ N := fun i => LinearMap.mem_ker.mpr (hv i)
  have hΦ : Module.length 𝒪 (RingHom.ker π).Cotangent = Module.length 𝒪 ((Fin n → 𝒪) ⧸ N) :=
    ((ψ.quotKerEquivOfSurjective hψ).length_eq).symm
  rw [hΦ]
  set e := Pi.basisFun 𝒪 (Fin n)

  have hdetv : e.det v = δ := by
    rw [basisFun_det_eq, hδdef, ← Matrix.det_transpose]
    rfl
  obtain ⟨m, snf⟩ := N.smithNormalForm e
  by_cases hmn : m = n
  · have h : Module.finrank 𝒪 N = Module.finrank 𝒪 (Fin n → 𝒪) := by
      rw [Module.finrank_eq_card_basis snf.bN, Module.finrank_fin_fun, Fintype.card_fin, hmn]
    set c := Submodule.smithNormalFormCoeffs e h
    have hc : ∀ i, c i ≠ 0 := Submodule.smithNormalFormCoeffs_ne_zero e h
    have hlen : Module.length 𝒪 ((Fin n → 𝒪) ⧸ N) =
        Module.length 𝒪 (𝒪 ⧸ Ideal.span {∏ i, c i}) := by
      rw [(Submodule.quotientEquivPiSpan N e h).length_eq, Module.length_pi_of_fintype,
        length_quotient_span_prod _ _ (fun i _ => hc i)]

    have hδmem : δ ∈ Ideal.span {∏ i, c i} := by
      let botB := Submodule.smithNormalFormBotBasis e h
      let topB := Submodule.smithNormalFormTopBasis e h
      let ω : N [⋀^Fin n]→ₗ[𝒪] 𝒪 := e.det.compLinearMap N.subtype
      let v' : Fin n → N := fun i => ⟨v i, hvN i⟩
      have h1 : ω v' = ω botB * botB.det v' := by
        conv_lhs => rw [ω.eq_smul_basis_det botB]
        rfl
      have h2 : ω v' = δ := by
        rw [← hdetv]
        rfl
      have h3 : ω botB = (∏ i, c i) * e.det topB := by
        have hb : (fun j => ((botB j : N) : Fin n → 𝒪)) = fun j => c j • topB j := by
          funext j; exact Submodule.smithNormalFormBotBasis_def e h j
        change e.det (fun j => ((botB j : N) : Fin n → 𝒪)) = _
        rw [hb, AlternatingMap.map_smul_univ, smul_eq_mul]
      rw [← h2, h1, h3]
      exact Ideal.mem_span_singleton'.mpr ⟨e.det topB * botB.det v', by ring⟩
    rw [hlen]
    refine Module.length_le_of_surjective
      (Submodule.mapQ (Ideal.span {δ}) (Ideal.span {∏ i, c i}) LinearMap.id ?_) ?_
    · simpa [Ideal.span_le] using hδmem
    · intro y; obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      exact ⟨Submodule.Quotient.mk y, rfl⟩
  ·
    exfalso
    have hns : ∃ i, i ∉ Set.range snf.f := by
      by_contra hcon
      have hsurj : Function.Surjective snf.f := fun i => by
        by_contra h'
        exact hcon ⟨i, fun ⟨j, hj⟩ => h' ⟨j, hj⟩⟩
      have := Fintype.card_le_of_surjective _ hsurj
      have := Fintype.card_le_of_embedding snf.f
      simp only [Fintype.card_fin] at *
      omega
    obtain ⟨i, hi⟩ := hns
    have hle := snf.le_ker_coord_of_notMem_range hi
    have hrow : ∀ k, snf.bM.toMatrix v i k = 0 := fun k => by
      rw [Module.Basis.toMatrix_apply]
      exact LinearMap.mem_ker.mp (hle (hvN k))
    have h0 : (snf.bM.toMatrix v).det = 0 := Matrix.det_eq_zero_of_row_eq_zero i hrow
    apply hδ
    rw [← hdetv, Module.Basis.det_apply, ← Module.Basis.toMatrix_mul_toMatrix e snf.bM v, Matrix.det_mul, h0,
      mul_zero]

end Core

end FrobDictCONV
p2m_reactivate "P2MW.S_AlgHom_length_cotangent_eq_of_exists_presentation.FrobDictCONV"

namespace FrobDictCONV

section Transport

variable {𝒪 : Type u} [CommRing 𝒪] {A : Type v} {B : Type w} [CommRing A] [CommRing B] [Algebra 𝒪 A] [Algebra 𝒪 B]

theorem length_cotangent_comp_equiv (E : A ≃ₐ[𝒪] B) (πB : B →ₐ[𝒪] 𝒪) :
    Module.length 𝒪 (RingHom.ker (πB.comp (E : A →ₐ[𝒪] B))).Cotangent =
      Module.length 𝒪 (RingHom.ker πB).Cotangent := by
  set πA : A →ₐ[𝒪] 𝒪 := πB.comp (E : A →ₐ[𝒪] B) with hπA
  have hA : ∀ x, x ∈ RingHom.ker πA ↔ E x ∈ RingHom.ker πB := fun x => by
    simp only [RingHom.mem_ker, hπA, AlgHom.comp_apply, AlgEquiv.coe_algHom]
  have h12 : RingHom.ker πA ≤ (RingHom.ker πB).comap (E : A →ₐ[𝒪] B) := fun x hx => (hA x).mp hx
  have h21 : RingHom.ker πB ≤ (RingHom.ker πA).comap (E.symm : B →ₐ[𝒪] A) := fun y hy => by
    change E.symm y ∈ RingHom.ker πA
    rw [hA, AlgEquiv.apply_symm_apply]
    exact hy
  let L₁ := (RingHom.ker πA).mapCotangent (RingHom.ker πB) (E : A →ₐ[𝒪] B) h12
  let L₂ := (RingHom.ker πB).mapCotangent (RingHom.ker πA) (E.symm : B →ₐ[𝒪] A) h21
  have h₁ : L₂.comp L₁ = LinearMap.id := by
    apply LinearMap.ext
    intro m
    obtain ⟨x, rfl⟩ := (RingHom.ker πA).toCotangent_surjective m
    rw [LinearMap.comp_apply, LinearMap.id_apply, Ideal.mapCotangent_toCotangent, Ideal.mapCotangent_toCotangent]
    congr 1
    apply Subtype.ext
    exact E.symm_apply_apply x
  have h₂ : L₁.comp L₂ = LinearMap.id := by
    apply LinearMap.ext
    intro m
    obtain ⟨y, rfl⟩ := (RingHom.ker πB).toCotangent_surjective m
    rw [LinearMap.comp_apply, LinearMap.id_apply, Ideal.mapCotangent_toCotangent, Ideal.mapCotangent_toCotangent]
    congr 1
    apply Subtype.ext
    exact E.apply_symm_apply y
  exact (LinearEquiv.ofLinear L₁ L₂ h₂ h₁).length_eq

theorem congruenceIdeal_comp_equiv (E : A ≃ₐ[𝒪] B) (πB : B →ₐ[𝒪] 𝒪) :
    (RingHom.ker (πB.comp (E : A →ₐ[𝒪] B))).annihilator.map (πB.comp (E : A →ₐ[𝒪] B)) =
      (RingHom.ker πB).annihilator.map πB := by
  set πA : A →ₐ[𝒪] 𝒪 := πB.comp (E : A →ₐ[𝒪] B) with hπA
  have hA : ∀ x, x ∈ RingHom.ker πA ↔ E x ∈ RingHom.ker πB := fun x => by
    simp only [RingHom.mem_ker, hπA, AlgHom.comp_apply, AlgEquiv.coe_algHom]

  have hann : ∀ x, x ∈ (RingHom.ker πA).annihilator ↔ E x ∈ (RingHom.ker πB).annihilator := fun x => by
    rw [Submodule.mem_annihilator, Submodule.mem_annihilator]
    constructor
    · intro h y hy
      have := h (E.symm y) (by rw [hA, AlgEquiv.apply_symm_apply]; exact hy)
      rw [smul_eq_mul] at this ⊢
      have := congrArg E this
      rwa [map_mul, AlgEquiv.apply_symm_apply, map_zero] at this
    · intro h x' hx'
      have := h (E x') ((hA x').mp hx')
      rw [smul_eq_mul] at this ⊢
      rw [← map_mul] at this
      exact (map_eq_zero_iff E E.injective).mp this
  apply le_antisymm
  · refine Ideal.map_le_iff_le_comap.mpr fun x hx => ?_
    rw [Ideal.mem_comap, hπA, AlgHom.comp_apply]
    exact Ideal.mem_map_of_mem _ ((hann x).mp hx)
  · refine Ideal.map_le_iff_le_comap.mpr fun y hy => ?_
    rw [Ideal.mem_comap]
    have : πB y = πA (E.symm y) := by rw [hπA, AlgHom.comp_apply, AlgEquiv.coe_algHom, AlgEquiv.apply_symm_apply]
    rw [this]
    exact Ideal.mem_map_of_mem _ ((hann _).mpr (by rw [AlgEquiv.apply_symm_apply]; exact hy))

end Transport
p2m_reactivate "P2MW.S_AlgHom_length_cotangent_eq_of_exists_presentation.FrobDictCONV"

section Normalize

variable {𝒪 : Type u} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsAdicComplete (maximalIdeal 𝒪) 𝒪]
  {T : Type w} [CommRing T] [IsLocalRing T] [Algebra 𝒪 T] [Module.Finite 𝒪 T] [Module.Free 𝒪 T]

omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsAdicComplete (maximalIdeal 𝒪) 𝒪] in

theorem C_eq_algebraMap {n : ℕ} (c : 𝒪) :
    (MvPowerSeries.C c : MvPowerSeries (Fin n) 𝒪) = algebraMap 𝒪 _ c := by
  rw [MvPowerSeries.algebraMap_apply]; rfl

noncomputable def ccAlg (n : ℕ) : MvPowerSeries (Fin n) 𝒪 →ₐ[𝒪] 𝒪 :=
  { (MvPowerSeries.constantCoeff : MvPowerSeries (Fin n) 𝒪 →+* 𝒪) with
    commutes' := fun c => by
      change MvPowerSeries.constantCoeff (algebraMap 𝒪 (MvPowerSeries (Fin n) 𝒪) c) = c
      rw [← C_eq_algebraMap, MvPowerSeries.constantCoeff_C] }

omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsAdicComplete (maximalIdeal 𝒪) 𝒪] in
theorem ccAlg_toRingHom (n : ℕ) :
    ((ccAlg n : MvPowerSeries (Fin n) 𝒪 →ₐ[𝒪] 𝒪) : MvPowerSeries (Fin n) 𝒪 →+* 𝒪) = MvPowerSeries.constantCoeff :=
  rfl

omit [IsLocalRing T] in

theorem main (πT : T →ₐ[𝒪] 𝒪)
    (hCI : ∃ (n : ℕ) (f : Fin n → MvPowerSeries (Fin n) 𝒪),
      Nonempty ((MvPowerSeries (Fin n) 𝒪 ⧸ Ideal.span (Set.range f)) ≃ₐ[𝒪] T)) :
    Module.length 𝒪 (RingHom.ker πT).Cotangent =
      Module.length 𝒪 (𝒪 ⧸ (RingHom.ker πT).annihilator.map πT) := by
  classical
  obtain ⟨n, f₀, ⟨e⟩⟩ := hCI
  haveI : IsAdicComplete (maximalIdeal (MvPowerSeries (Fin n) 𝒪)) (MvPowerSeries (Fin n) 𝒪) := MvPowerSeries.isAdicComplete_maximalIdeal
  let ψ₀ : (MvPowerSeries (Fin n) 𝒪) →ₐ[𝒪] T := (e : _ →ₐ[𝒪] T).comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span (Set.range f₀)))
  have hψ₀ : Function.Surjective ψ₀ := e.surjective.comp (Ideal.Quotient.mkₐ_surjective 𝒪 _)
  have hkerψ₀ : RingHom.ker ψ₀ = Ideal.span (Set.range f₀) := by
    ext q
    simp only [ψ₀, RingHom.mem_ker, AlgHom.comp_apply, AlgEquiv.coe_algHom, map_eq_zero_iff e e.injective,
      Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
  let χ : (MvPowerSeries (Fin n) 𝒪) →ₐ[𝒪] 𝒪 := πT.comp ψ₀
  have hχsurj : Function.Surjective χ := fun c => ⟨algebraMap 𝒪 (MvPowerSeries (Fin n) 𝒪) c, χ.commutes c⟩
  haveI : IsLocalHom (χ : (MvPowerSeries (Fin n) 𝒪) →+* 𝒪) := IsLocalHom.of_surjective _ hχsurj
  let a : Fin n → 𝒪 := fun i => χ (MvPowerSeries.X i)
  have hXmax : ∀ i, (MvPowerSeries.X i : (MvPowerSeries (Fin n) 𝒪)) ∈ maximalIdeal (MvPowerSeries (Fin n) 𝒪) := fun i => by
    rw [mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff, MvPowerSeries.constantCoeff_X]
    exact not_isUnit_zero
  have ha : ∀ i, a i ∈ maximalIdeal 𝒪 := fun i => map_nonunit (χ : (MvPowerSeries (Fin n) 𝒪) →+* 𝒪) _ (hXmax i)

  have hmem : ∀ (ε : 𝒪) (i : Fin n), (MvPowerSeries.X i + MvPowerSeries.C (ε * a i) : (MvPowerSeries (Fin n) 𝒪)) ∈ maximalIdeal (MvPowerSeries (Fin n) 𝒪) :=
    fun ε i => by
      rw [mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff, map_add,
        MvPowerSeries.constantCoeff_X, MvPowerSeries.constantCoeff_C, zero_add]
      exact (mem_maximalIdeal _).mp (Ideal.mul_mem_left _ _ (ha i))
  obtain ⟨sp, hsp⟩ := MvPowerSeries.exists_algHom_apply_X_eq (σ := Fin n) (𝒪 := 𝒪) (maximalIdeal (MvPowerSeries (Fin n) 𝒪))
    (fun i => (MvPowerSeries.X i + MvPowerSeries.C (1 * a i) : (MvPowerSeries (Fin n) 𝒪))) (hmem 1)
  obtain ⟨sm, hsm⟩ := MvPowerSeries.exists_algHom_apply_X_eq (σ := Fin n) (𝒪 := 𝒪) (maximalIdeal (MvPowerSeries (Fin n) 𝒪))
    (fun i => (MvPowerSeries.X i + MvPowerSeries.C ((-1) * a i) : (MvPowerSeries (Fin n) 𝒪))) (hmem (-1))
  have hC : ∀ (s : (MvPowerSeries (Fin n) 𝒪) →ₐ[𝒪] (MvPowerSeries (Fin n) 𝒪)) (c : 𝒪), s (MvPowerSeries.C c) = MvPowerSeries.C c := fun s c => by
    rw [C_eq_algebraMap, s.commutes]
  have hcomp1 : sm.comp sp = AlgHom.id 𝒪 (MvPowerSeries (Fin n) 𝒪) := by
    refine MvPowerSeries.algHom_ext_of_apply_X_mem (maximalIdeal (MvPowerSeries (Fin n) 𝒪)) _ _ (fun i => ?_) (fun i => ?_)
    · rw [AlgHom.comp_apply, hsp, map_add, hsm, hC]
      convert hXmax i using 1
      simp only [one_mul, neg_mul, map_neg]; abel
    · rw [AlgHom.comp_apply, hsp, map_add, hsm, hC, AlgHom.id_apply]
      simp only [one_mul, neg_mul, map_neg]; abel
  have hcomp2 : sp.comp sm = AlgHom.id 𝒪 (MvPowerSeries (Fin n) 𝒪) := by
    refine MvPowerSeries.algHom_ext_of_apply_X_mem (maximalIdeal (MvPowerSeries (Fin n) 𝒪)) _ _ (fun i => ?_) (fun i => ?_)
    · rw [AlgHom.comp_apply, hsm, map_add, hsp, hC]
      convert hXmax i using 1
      simp only [one_mul, neg_mul, map_neg]; abel
    · rw [AlgHom.comp_apply, hsm, map_add, hsp, hC, AlgHom.id_apply]
      simp only [one_mul, neg_mul, map_neg]; abel
  let S : (MvPowerSeries (Fin n) 𝒪) ≃ₐ[𝒪] (MvPowerSeries (Fin n) 𝒪) := AlgEquiv.ofAlgHom sm sp hcomp1 hcomp2

  let ψ' : (MvPowerSeries (Fin n) 𝒪) →ₐ[𝒪] T := ψ₀.comp (S : (MvPowerSeries (Fin n) 𝒪) →ₐ[𝒪] (MvPowerSeries (Fin n) 𝒪))
  have hψ' : Function.Surjective ψ' := hψ₀.comp S.surjective
  have hχ' : πT.comp ψ' = ccAlg n := by
    refine MvPowerSeries.algHom_ext_of_apply_X_mem (maximalIdeal 𝒪) _ _ (fun i => ?_) (fun i => ?_)
    · have : (πT.comp ψ') (MvPowerSeries.X i) = 0 := by
        change χ (sm (MvPowerSeries.X i)) = 0
        rw [hsm, map_add, C_eq_algebraMap, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]
        change a i + (-1) * a i = 0
        ring
      rw [this]
      exact zero_mem _
    · change χ (sm (MvPowerSeries.X i)) = MvPowerSeries.constantCoeff (MvPowerSeries.X i)
      rw [hsm, map_add, MvPowerSeries.constantCoeff_X, C_eq_algebraMap, AlgHom.commutes, Algebra.algebraMap_self,
        RingHom.id_apply]
      change a i + (-1) * a i = 0
      ring

  let f : Fin n → (MvPowerSeries (Fin n) 𝒪) := fun i => sp (f₀ i)
  have hkerψ' : RingHom.ker ψ' = Ideal.span (Set.range f) := by
    have h1 : RingHom.ker ψ' = (Ideal.span (Set.range f₀)).comap (S : (MvPowerSeries (Fin n) 𝒪) ≃+* (MvPowerSeries (Fin n) 𝒪)) := by
      ext q
      rw [RingHom.mem_ker, Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem, ← map_eq_zero_iff e e.injective]
      rfl
    rw [h1, ← Ideal.map_symm, Ideal.map_span, ← Set.range_comp]
    rfl

  let E : ((MvPowerSeries (Fin n) 𝒪) ⧸ Ideal.span (Set.range f)) ≃ₐ[𝒪] T :=
    (Ideal.quotientEquivAlgOfEq 𝒪 hkerψ'.symm).trans (Ideal.quotientKerAlgEquivOfSurjective hψ')
  have hE : ∀ q, E (Ideal.Quotient.mk _ q) = ψ' q := fun q => by
    simp [E]
  haveI : Module.Finite 𝒪 ((MvPowerSeries (Fin n) 𝒪) ⧸ Ideal.span (Set.range f)) := Module.Finite.equiv E.symm.toLinearEquiv
  haveI : Module.Free 𝒪 ((MvPowerSeries (Fin n) 𝒪) ⧸ Ideal.span (Set.range f)) := Module.Free.of_equiv E.symm.toLinearEquiv
  let π' : ((MvPowerSeries (Fin n) 𝒪) ⧸ Ideal.span (Set.range f)) →ₐ[𝒪] 𝒪 := πT.comp (E : _ →ₐ[𝒪] T)
  have hπ'q : ∀ q, π' (Ideal.Quotient.mk _ q) = MvPowerSeries.constantCoeff q := fun q => by
    change πT (E (Ideal.Quotient.mk _ q)) = _
    rw [hE, ← AlgHom.comp_apply, hχ']
    rfl
  have hπ' : (π' : _ →+* 𝒪).comp (Ideal.Quotient.mk (Ideal.span (Set.range f))) = MvPowerSeries.constantCoeff :=
    RingHom.ext hπ'q

  have hfX : ∀ i, f i ∈ Ideal.span (Set.range (MvPowerSeries.X : Fin n → (MvPowerSeries (Fin n) 𝒪))) := fun i => by
    have h0 : Ideal.Quotient.mk (Ideal.span (Set.range f)) (f i) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self i))
    rw [mem_span_X_iff, ← hπ'q, h0, map_zero]
  choose g hg using fun i => (Submodule.mem_span_range_iff_exists_fun (MvPowerSeries (Fin n) 𝒪)).mp (hfX i)
  have hf : ∀ i, f i = ∑ j, (Matrix.of g) i j * MvPowerSeries.X j := fun i => by
    rw [← hg i]; rfl

  have hcore := core (Matrix.of g) f hf π' hπ'
  rw [← length_cotangent_comp_equiv E πT, ← congruenceIdeal_comp_equiv E πT]
  exact hcore

end Normalize
p2m_reactivate "P2MW.S_AlgHom_length_cotangent_eq_of_exists_presentation.FrobDictCONV"

end FrobDictCONV
p2m_reactivate "P2MW.S_AlgHom_length_cotangent_eq_of_exists_presentation.FrobDictCONV"

open FrobDictCONV in
theorem solution
    {𝒪 : Type u} {T : Type w}
    [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    [CommRing T] [IsLocalRing T] [Algebra 𝒪 T] [Module.Finite 𝒪 T] [Module.Free 𝒪 T]
    (πT : T →ₐ[𝒪] 𝒪)
    (hCI : ∃ (n : ℕ) (f : Fin n → MvPowerSeries (Fin n) 𝒪),
        Nonempty ((MvPowerSeries (Fin n) 𝒪 ⧸ Ideal.span (Set.range f)) ≃ₐ[𝒪] T)) :
    Module.length 𝒪 (RingHom.ker πT).Cotangent =
      Module.length 𝒪 (𝒪 ⧸ (RingHom.ker πT).annihilator.map πT) :=
  main πT hCI

end S_AlgHom_length_cotangent_eq_of_exists_presentation
end P2MW
export P2MW.S_AlgHom_length_cotangent_eq_of_exists_presentation (solution)
