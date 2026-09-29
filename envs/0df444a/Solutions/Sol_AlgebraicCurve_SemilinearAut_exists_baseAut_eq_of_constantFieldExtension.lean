-- Prove2me | solution 1 for AlgebraicCurve.SemilinearAut.exists_baseAut_eq_of_constantFieldExtension
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/b7bbc5cc-6a4f-53a2-b14b-109c34c3dd1f

import Mathlib
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Theorems.Thm_AlgebraicCurve_linearIndependent_of_constantFieldExtension
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_SemilinearAut_exists_baseAut_eq_of_constantFieldExtension

open scoped TensorProduct

open AlgebraicCurve in
theorem solution
    (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K] [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (τ : K' ≃ₐ[K] K') :
    ∃ g : SemilinearAut K' F',
      (∀ a : K', SemilinearAut.baseAut g a = τ a) ∧
      ∀ y : F, g • algebraMap F F' y = algebraMap F F' y := by
  classical

  let μ : K' ⊗[K] F →ₐ[K'] F' :=
    Algebra.TensorProduct.lift (Algebra.ofId K' F') (IsScalarTower.toAlgHom K F F')
      (fun _ _ => Commute.all _ _)
  have hμ_tmul : ∀ (a : K') (y : F), μ (a ⊗ₜ y) = algebraMap K' F' a * algebraMap F F' y :=
    fun a y => by simp [μ]

  have hμ : Function.Injective μ := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    let bF := Module.Free.chooseBasis K F
    let B := Algebra.TensorProduct.basis K' bF
    have hli : LinearIndependent K' (fun i => algebraMap F F' (bF i)) :=
      AlgebraicCurve.linearIndependent_of_constantFieldExtension K F K' F' hfg hfg' hgen
        bF.linearIndependent
    have hcomp : (μ.toLinearMap : K' ⊗[K] F → F') ∘ (B : _ → K' ⊗[K] F) =
        fun i => algebraMap F F' (bF i) := by
      funext i
      simp [B, Algebra.TensorProduct.basis_apply, hμ_tmul]
    have hz' : Finsupp.linearCombination K' (fun i => algebraMap F F' (bF i)) (B.repr z) = 0 := by
      rw [← hcomp, ← Finsupp.apply_linearCombination, B.linearCombination_repr]
      exact hz
    have hrepr : B.repr z = 0 := linearIndependent_iff.mp hli _ hz'
    simpa using hrepr

  set S : Subalgebra K' F' := μ.range with hS
  let e : (K' ⊗[K] F) ≃ₐ[K'] S := AlgEquiv.ofInjective μ hμ
  have he : ∀ z, ((e z : S) : F') = μ z := fun z => AlgEquiv.ofInjective_apply μ hμ z
  haveI : FaithfulSMul S F' := (faithfulSMul_iff_algebraMap_injective S F').mpr Subtype.val_injective
  have hFS : ∀ y : F, algebraMap F F' y ∈ S := fun y =>
    ⟨1 ⊗ₜ y, show μ (1 ⊗ₜ y) = _ by rw [hμ_tmul, map_one, one_mul]⟩
  have hadj : Algebra.adjoin K' (Set.range (algebraMap F F')) ≤ S :=
    Algebra.adjoin_le (by rintro _ ⟨y, rfl⟩; exact hFS y)
  haveI : IsFractionRing S F' := by
    refine IsFractionRing.of_field S F' fun z => ?_
    have hz : z ∈ IntermediateField.adjoin K' (Set.range (algebraMap F F')) := by
      rw [hgen]; exact IntermediateField.mem_top
    obtain ⟨r, hr, s, hs, hrs⟩ := (IntermediateField.mem_adjoin_iff_div (F := K')).mp hz
    exact ⟨⟨r, hadj hr⟩, ⟨s, hadj hs⟩, hrs⟩

  let θ : K' ⊗[K] F ≃ₐ[K] K' ⊗[K] F := Algebra.TensorProduct.congr τ AlgEquiv.refl
  have hθ : ∀ (a : K') (y : F), θ (a ⊗ₜ y) = τ a ⊗ₜ y := fun a y => by
    simp [θ, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
  let ΦS : S ≃+* S := (e.symm.toRingEquiv.trans θ.toRingEquiv).trans e.toRingEquiv
  have hΦS : ∀ z, ΦS (e z) = e (θ z) := fun z => by
    simp [ΦS]
  let Φ : F' ≃+* F' := IsFractionRing.ringEquivOfRingEquiv ΦS
  have hΦ : ∀ s : S, Φ (s : F') = ((ΦS s : S) : F') := fun s =>
    IsFractionRing.ringEquivOfRingEquiv_algebraMap ΦS s
  have hΦμ : ∀ z, Φ (μ z) = μ (θ z) := fun z => by
    rw [← he, hΦ, hΦS, he]
  have hΦK : ∀ a : K', Φ (algebraMap K' F' a) = algebraMap K' F' (τ a) := fun a => by
    have h1 : algebraMap K' F' a = μ (a ⊗ₜ 1) := by rw [hμ_tmul, map_one, mul_one]
    rw [h1, hΦμ, hθ, hμ_tmul, map_one, mul_one]
  have hΦF : ∀ y : F, Φ (algebraMap F F' y) = algebraMap F F' y := fun y => by
    have h1 : algebraMap F F' y = μ (1 ⊗ₜ y) := by rw [hμ_tmul, map_one, one_mul]
    rw [h1, hΦμ, hθ, map_one]
  refine ⟨⟨(Φ, (τ : K' ≃+* K')), SemilinearAut.mem_iff.mpr fun a => ?_⟩, fun a => rfl,
    fun y => ?_⟩
  · exact hΦK a
  · rw [SemilinearAut.smul_def]
    exact hΦF y

end S_AlgebraicCurve_SemilinearAut_exists_baseAut_eq_of_constantFieldExtension
end P2MW
export P2MW.S_AlgebraicCurve_SemilinearAut_exists_baseAut_eq_of_constantFieldExtension (solution)
