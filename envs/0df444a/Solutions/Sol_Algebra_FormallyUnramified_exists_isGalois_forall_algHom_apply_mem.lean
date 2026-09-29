-- Prove2me | solution 1 for Algebra.FormallyUnramified.exists_isGalois_forall_algHom_apply_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/ce7d3265-878f-5f0b-822d-aeffe347f1ba

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_FormallyUnramified_exists_isGalois_forall_algHom_apply_mem

set_option autoImplicit false

universe u

namespace P2mEtaleSplitting

open IntermediateField

section PiFactor

variable (K : Type*) [Field K] {I : Type u} [Finite I] (Ai : I → Type u) [∀ i, Field (Ai i)]
  [∀ i, Algebra K (Ai i)] {Ω : Type*} [Field Ω] [Algebra K Ω]

noncomputable def factorHom [DecidableEq I] (φ : (Π i, Ai i) →ₐ[K] Ω) (i : I)
    (hi : φ (Pi.single i 1) = 1) : Ai i →ₐ[K] Ω where
  toFun a := φ (Pi.single i a)
  map_one' := hi
  map_mul' a b := by rw [← map_mul, ← Pi.single_mul]
  map_zero' := by rw [Pi.single_zero, map_zero]
  map_add' a b := by rw [← map_add, ← Pi.single_add]
  commutes' k := by
    rw [Algebra.algebraMap_eq_smul_one, show (Pi.single i (k • (1 : Ai i)) : Π j, Ai j) =
        k • Pi.single i (1 : Ai i) from Pi.single_smul i k (1 : Ai i), map_smul, hi,
      Algebra.algebraMap_eq_smul_one]

omit [Finite I] in
theorem factorHom_apply [DecidableEq I] (φ : (Π i, Ai i) →ₐ[K] Ω) (i : I)
    (hi : φ (Pi.single i 1) = 1) (a : Ai i) : factorHom K Ai φ i hi a = φ (Pi.single i a) := rfl

theorem exists_eq_comp_evalAlgHom (φ : (Π i, Ai i) →ₐ[K] Ω) :
    ∃ (i : I) (ψ : Ai i →ₐ[K] Ω), ∀ x, φ x = ψ (x i) := by
  classical
  obtain ⟨_⟩ := nonempty_fintype I

  have hsum : ∑ i, φ (Pi.single i (1 : Ai i)) = 1 := by
    rw [← map_sum, Finset.univ_sum_single (fun _ => (1 : _))]
    exact map_one φ
  have hex : ∃ i, φ (Pi.single i (1 : Ai i)) ≠ 0 := by
    by_contra h
    push Not at h
    rw [Finset.sum_eq_zero (fun i _ => h i)] at hsum
    exact zero_ne_one hsum
  obtain ⟨i, hi0⟩ := hex
  have hidem : φ (Pi.single i (1 : Ai i)) * φ (Pi.single i (1 : Ai i)) =
      φ (Pi.single i (1 : Ai i)) := by
    rw [← map_mul, ← Pi.single_mul, mul_one]
  have hi : φ (Pi.single i (1 : Ai i)) = 1 := by
    have h := hidem
    rwa [mul_left_eq_self₀, or_iff_left hi0] at h
  refine ⟨i, factorHom K Ai φ i hi, fun x => ?_⟩
  rw [factorHom_apply]
  have hx : x = Pi.single i (x i) + x * (1 - Pi.single i 1) := by
    ext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  conv_lhs => rw [hx]
  rw [map_add, map_mul, map_sub, map_one, hi, sub_self, mul_zero, add_zero]

end PiFactor

theorem exists_isGalois_forall_algHom_apply_mem
    (K : Type u) [Field K] (E : Type u) [CommRing E] [Algebra K E]
    [Module.Finite K E] [Algebra.FormallyUnramified K E]
    (Ω : Type*) [Field Ω] [Algebra K Ω] [Normal K Ω] :
    ∃ L : IntermediateField K Ω, FiniteDimensional K L ∧ IsGalois K L ∧
      ∀ (φ : E →ₐ[K] Ω) (e : E), φ e ∈ L := by
  classical
  haveI : Algebra.FormallyEtale K E := Algebra.FormallyEtale.of_formallyUnramified_of_field K E
  obtain ⟨I, hI, Ai, hF, hA, iso, hsep⟩ :=
    (Algebra.FormallyEtale.iff_exists_algEquiv_prod K E).mp inferInstance

  haveI hfin : ∀ i, FiniteDimensional K (Ai i) := fun i =>
    Module.Finite.of_surjective ((LinearMap.proj i).comp iso.toLinearMap)
      ((Function.surjective_eval i).comp iso.surjective)
  let N : I → IntermediateField K Ω := fun i => normalClosure K (Ai i) Ω
  refine ⟨⨆ i, N i, ?_, ?_, ?_⟩
  · exact IntermediateField.finiteDimensional_iSup_of_finite
  · haveI : Normal K (⨆ i, N i : IntermediateField K Ω) :=
      IntermediateField.normal_iSup (F := K) (K := Ω) N
    haveI : ∀ i, Algebra.IsSeparable K (N i) := by
      intro i
      rw [← le_separableClosure_iff]
      refine (normalClosure_le_iff).mpr fun ψ => ?_
      rintro _ ⟨a, rfl⟩
      rw [mem_separableClosure_iff]
      change IsSeparable K (ψ a)
      rw [IsSeparable, minpoly.algHom_eq ψ ψ.injective]
      exact Algebra.IsSeparable.isSeparable K a
    haveI : Algebra.IsSeparable K (⨆ i, N i : IntermediateField K Ω) :=
      IntermediateField.isSeparable_iSup K Ω
    exact ⟨⟩
  · intro φ e
    obtain ⟨i, ψ, hψ⟩ := exists_eq_comp_evalAlgHom K Ai (φ.comp iso.symm.toAlgHom)
    have hφ : φ e = ψ (iso e i) := by
      have h := hψ (iso e)
      simpa using h
    rw [hφ]
    have hle : N i ≤ ⨆ j, N j := le_iSup N i
    apply hle
    exact AlgHom.fieldRange_le_normalClosure ψ ⟨iso e i, rfl⟩

end P2mEtaleSplitting

theorem solution
    (K : Type u) [Field K] (E : Type u) [CommRing E] [Algebra K E]
    [Module.Finite K E] [Algebra.FormallyUnramified K E]
    (Ω : Type*) [Field Ω] [Algebra K Ω] [Normal K Ω] :
    ∃ L : IntermediateField K Ω, FiniteDimensional K L ∧ IsGalois K L ∧
      ∀ (φ : E →ₐ[K] Ω) (e : E), φ e ∈ L :=
  P2mEtaleSplitting.exists_isGalois_forall_algHom_apply_mem K E Ω

end S_Algebra_FormallyUnramified_exists_isGalois_forall_algHom_apply_mem
end P2MW
export P2MW.S_Algebra_FormallyUnramified_exists_isGalois_forall_algHom_apply_mem (solution)
