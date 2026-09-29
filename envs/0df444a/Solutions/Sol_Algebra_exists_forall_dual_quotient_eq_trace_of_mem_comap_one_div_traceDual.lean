-- Prove2me | solution 1 for Algebra.exists_forall_dual_quotient_eq_trace_of_mem_comap_one_div_traceDual
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/c475a6c3-e5b6-5e50-be30-0725a6ebcbe4

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_exists_forall_dual_quotient_eq_trace_of_mem_comap_one_div_traceDual

set_option autoImplicit false
universe u
open IsLocalRing nonZeroDivisors Algebra Module

namespace KBAux

section Quot

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (I : Ideal R)

local notation "IS" => Ideal.map (algebraMap R S) I

theorem span_mk_image_eq_top {s : Set S} (hs : Submodule.span R s = ⊤) :
    Submodule.span (R ⧸ I) ((Ideal.Quotient.mk IS) '' s) = ⊤ := by
  have hcoe : ⇑((IsScalarTower.toAlgHom R S (S ⧸ IS)).toLinearMap) = ⇑(Ideal.Quotient.mk IS) := by
    rw [AlgHom.coe_toLinearMap, IsScalarTower.coe_toAlgHom', Ideal.Quotient.algebraMap_eq]
  have H : (Submodule.span (R ⧸ I) ((Ideal.Quotient.mk IS) '' s)).restrictScalars R =
      (Submodule.span R s).map (IsScalarTower.toAlgHom R S (S ⧸ IS)).toLinearMap := by
    rw [Submodule.map_span, ← Submodule.restrictScalars_span R (R ⧸ I) Ideal.Quotient.mk_surjective, hcoe]
  rwa [hs, Submodule.map_top, LinearMap.range_eq_top.mpr, Submodule.restrictScalars_eq_top_iff] at H
  rw [hcoe]
  exact Ideal.Quotient.mk_surjective

variable {ι : Type*}

theorem linearIndependent_mk_comp (b : Basis ι R S) :
    LinearIndependent (R ⧸ I) (Ideal.Quotient.mk IS ∘ b) := by
  classical
  rw [linearIndependent_iff']
  intro t g hg i hi
  choose g' hg' using fun j => Ideal.Quotient.mk_surjective (g j)

  have hsum : Ideal.Quotient.mk IS (∑ j ∈ t, g' j • b j) = 0 := by
    rw [map_sum, ← hg]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Function.comp_apply, ← hg' j, Algebra.smul_def, map_mul, Ideal.Quotient.mk_smul_mk_quotient_map_quotient,
      map_mul, Ideal.Quotient.mk_algebraMap]
  rw [Ideal.Quotient.eq_zero_iff_mem] at hsum
  have hsmul : (∑ j ∈ t, g' j • b j) ∈ I • (⊤ : Submodule R S) := by
    rw [Ideal.smul_top_eq_map]; exact hsum
  rw [← b.span_eq, Submodule.mem_ideal_smul_span_iff_exists_sum] at hsmul
  obtain ⟨a, ha, hax⟩ := hsmul

  have hcoord : b.repr (∑ j ∈ t, g' j • b j) i = g' i := by
    simp only [map_sum, map_smul, Basis.repr_self, Finsupp.coe_finsetSum, Finset.sum_apply,
      Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', if_pos hi]
  have hcoord' : b.repr (a.sum fun j c => c • b j) i = a i := by
    have : (a.sum fun j c => c • b j) = Finsupp.linearCombination R b a := rfl
    rw [this, b.repr_linearCombination]
  have hgi : g' i = a i := by rw [← hcoord, ← hcoord', hax]
  rw [← hg' i, hgi, Ideal.Quotient.eq_zero_iff_mem]
  exact ha i

noncomputable def basisQuot (b : Basis ι R S) : Basis ι (R ⧸ I) (S ⧸ IS) :=
  Basis.mk (linearIndependent_mk_comp I b) (by rw [Set.range_comp]; exact (span_mk_image_eq_top I b.span_eq).ge)

theorem basisQuot_apply (b : Basis ι R S) (i : ι) : basisQuot I b i = Ideal.Quotient.mk IS (b i) := by
  rw [basisQuot, Basis.coe_mk, Function.comp_apply]

theorem basisQuot_repr [Fintype ι] (b : Basis ι R S) (x : S) (i : ι) :
    (basisQuot I b).repr (Ideal.Quotient.mk IS x) i = Ideal.Quotient.mk I (b.repr x i) := by
  classical
  refine congr_fun (g := Ideal.Quotient.mk I ∘ b.repr x) ?_ i
  apply (Finsupp.linearEquivFunOnFinite (R ⧸ I) _ _).symm.injective
  apply (basisQuot I b).repr.symm.injective
  simp only [Finsupp.linearEquivFunOnFinite_symm_coe, LinearEquiv.symm_apply_apply, Basis.repr_symm_apply]
  rw [Finsupp.linearCombination_eq_fintype_linearCombination_apply (R ⧸ I), Fintype.linearCombination_apply]
  simp only [Function.comp_apply, basisQuot_apply, Ideal.Quotient.mk_smul_mk_quotient_map_quotient, ← Algebra.smul_def]
  rw [← map_sum, Basis.sum_repr b x]

theorem trace_quot_mk [Module.Free R S] [Module.Finite R S] (x : S) :
    Algebra.trace (R ⧸ I) (S ⧸ IS) (Ideal.Quotient.mk IS x) = Ideal.Quotient.mk I (Algebra.trace R S x) := by
  classical
  let ιb := Module.Free.ChooseBasisIndex R S
  let b : Basis ιb R S := Module.Free.chooseBasis R S
  rw [Algebra.trace_eq_matrix_trace b, Algebra.trace_eq_matrix_trace (basisQuot I b), AddMonoidHom.map_trace]
  congr 1
  ext i j
  simp only [Algebra.leftMulMatrix_apply, Algebra.coe_lmul_eq_mul, LinearMap.toMatrix_apply, basisQuot_apply,
    LinearMap.mul_apply', Matrix.map_apply, ← map_mul, basisQuot_repr]

end Quot

end KBAux

open KBAux in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in

theorem solution
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (S : Type u) [CommRing S] [IsDomain S] [IsIntegrallyClosed S] [Algebra R S] [Module.Finite R S] [Module.Free R S]
    (F : Type u) [Field F] [Algebra S F] [IsFractionRing S F] [Algebra K F] [Algebra R F]
    [IsScalarTower R K F] [IsScalarTower R S F] [Algebra.IsSeparable K F]
    (I : Ideal R) (s : S)
    (hs : s ∈ ((1 / Submodule.traceDual R K (1 : Submodule S F) : Submodule S F).comap (Algebra.linearMap S F))) :
    ∀ φ : Module.Dual (R ⧸ I) (S ⧸ I.map (algebraMap R S)),
      ∃ x : S ⧸ I.map (algebraMap R S), ∀ y : S ⧸ I.map (algebraMap R S),
        φ (Ideal.Quotient.mk (I.map (algebraMap R S)) s * y) =
          Algebra.trace (R ⧸ I) (S ⧸ I.map (algebraMap R S)) (x * y) := by
  classical
  intro φb
  haveI : IsLocalization (Algebra.algebraMapSubmonoid S R⁰) F := IsIntegralClosure.isLocalization R K F S
  haveI : FiniteDimensional K F := Module.Finite.of_isLocalization R S R⁰
  have hinjK : Function.Injective (algebraMap R K) := IsFractionRing.injective R K

  let b := Module.Free.chooseBasis R S
  choose g hg using fun i => Ideal.Quotient.mk_surjective (φb (Ideal.Quotient.mk (I.map (algebraMap R S)) (b i)))
  let φ : S →ₗ[R] R := b.constr R g
  have hφb : ∀ i, φ (b i) = g i := fun i => b.constr_basis R g i
  have hφ : ∀ y : S, Ideal.Quotient.mk I (φ y) = φb (Ideal.Quotient.mk (I.map (algebraMap R S)) y) := by
    intro y
    let L1 : S →ₗ[R] (R ⧸ I) := (Ideal.Quotient.mkₐ R I).toLinearMap ∘ₗ φ
    let L2 : S →ₗ[R] (R ⧸ I) := (φb.restrictScalars R) ∘ₗ (Ideal.Quotient.mkₐ R (I.map (algebraMap R S))).toLinearMap
    have hL : L1 = L2 := b.ext fun i => by
      simp only [L1, L2, LinearMap.comp_apply, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk,
        LinearMap.restrictScalars_apply, hφb, hg]
    exact LinearMap.congr_fun hL y

  let bF := b.localizationLocalization K R⁰ F
  have hbF : ∀ i, bF i = algebraMap S F (b i) := fun i => Basis.localizationLocalization_apply K R⁰ F b i
  let ψ : F →ₗ[K] K := bF.constr K (fun i => algebraMap R K (g i))
  have hψ : ∀ y : S, ψ (algebraMap S F y) = algebraMap R K (φ y) := by
    intro y
    let M1 : S →ₗ[R] K := (ψ.restrictScalars R) ∘ₗ (IsScalarTower.toAlgHom R S F).toLinearMap
    let M2 : S →ₗ[R] K := (Algebra.linearMap R K) ∘ₗ φ
    have hM : M1 = M2 := b.ext fun i => by
      simp only [M1, M2, LinearMap.comp_apply, AlgHom.toLinearMap_apply, IsScalarTower.coe_toAlgHom',
        LinearMap.restrictScalars_apply, Algebra.linearMap_apply, hφb, ← hbF, ψ, Basis.constr_basis]
    exact LinearMap.congr_fun hM y
  have hnd := traceForm_nondegenerate K F
  let z : F := ((Algebra.traceForm K F).toDual hnd).symm ψ
  have hz : ∀ w : F, Algebra.traceForm K F z w = ψ w := fun w => by
    rw [← LinearMap.BilinForm.toDual_def hnd, LinearEquiv.apply_symm_apply]

  have hzd : z ∈ Submodule.traceDual R K (1 : Submodule S F) := by
    rw [Submodule.mem_traceDual]
    intro a ha
    obtain ⟨y, rfl⟩ := Submodule.mem_one.mp ha
    rw [hz, hψ]
    exact ⟨_, rfl⟩
  have hs' : algebraMap S F s * z ∈ (1 : Submodule S F) := by
    rw [Submodule.mem_comap, Algebra.linearMap_apply, Submodule.mem_div_iff_forall_mul_mem] at hs
    exact hs z hzd
  obtain ⟨x, hx⟩ := Submodule.mem_one.mp hs'

  have key : ∀ y : S, φ (s * y) = Algebra.trace R S (x * y) := by
    intro y
    apply hinjK
    rw [← hψ, ← Algebra.trace_localization R R⁰ (Rₘ := K) (Sₘ := F), RingHom.map_mul (algebraMap S F),
      RingHom.map_mul (algebraMap S F), hx, ← hz, Algebra.traceForm_apply]
    congr 1
    ring

  refine ⟨Ideal.Quotient.mk _ x, fun yb => ?_⟩
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective yb
  rw [← map_mul, ← hφ, key, ← map_mul, trace_quot_mk]

end S_Algebra_exists_forall_dual_quotient_eq_trace_of_mem_comap_one_div_traceDual
end P2MW
export P2MW.S_Algebra_exists_forall_dual_quotient_eq_trace_of_mem_comap_one_div_traceDual (solution)
