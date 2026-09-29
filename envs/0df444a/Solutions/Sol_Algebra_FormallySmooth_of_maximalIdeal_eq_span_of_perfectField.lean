-- Prove2me | solution 1 for Algebra.FormallySmooth.of_maximalIdeal_eq_span_of_perfectField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/3d33287e-e4b4-55b8-a875-eac3a673218b

import Mathlib
import Theorems.Thm_Algebra_FormallySmooth_of_maximalIdeal_eq_span_of_isSeparable_residueField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_FormallySmooth_of_maximalIdeal_eq_span_of_perfectField

set_option autoImplicit false

universe u v

open IsLocalRing

theorem solution
    (K : Type u) [Field K] [PerfectField K] (𝒪 : Type v) [CommRing 𝒪] [IsLocalRing 𝒪] [IsDomain 𝒪] [IsNoetherianRing 𝒪]
    [Algebra K 𝒪] [Algebra.EssFiniteType K 𝒪]
    (u : 𝒪) (hu0 : u ≠ 0) (hu : maximalIdeal 𝒪 = Ideal.span {u}) :
    Algebra.FormallySmooth K 𝒪 := by
  classical

  haveI : Algebra.EssFiniteType K (ResidueField 𝒪) :=
    Algebra.EssFiniteType.comp K 𝒪 (ResidueField 𝒪)
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField K (ResidueField 𝒪)
  have hinj : Function.Injective (MvPolynomial.aeval (R := K) ((↑) : s → ResidueField 𝒪)) :=
    algebraicIndependent_iff_injective_aeval.1 hs.1

  choose t ht using fun x : s => IsLocalRing.residue_surjective (R := 𝒪) (x : ResidueField 𝒪)
  let P := MvPolynomial s K
  let φ : P →ₐ[K] 𝒪 := MvPolynomial.aeval t
  have hφres : ∀ f : P, IsLocalRing.residue 𝒪 (φ f) = MvPolynomial.aeval ((↑) : s → ResidueField 𝒪) f := by
    intro f
    have hcomp : ((IsScalarTower.toAlgHom K 𝒪 (ResidueField 𝒪)).comp φ) =
        MvPolynomial.aeval ((↑) : s → ResidueField 𝒪) := by
      refine MvPolynomial.algHom_ext fun i => ?_
      simp [φ, ht i]
    exact congrArg (fun g : P →ₐ[K] ResidueField 𝒪 => g f) hcomp

  have hunit : ∀ f : P, f ≠ 0 → IsUnit (φ f) := by
    intro f hf
    by_contra h
    have hmem : φ f ∈ maximalIdeal 𝒪 := h
    have h0 : IsLocalRing.residue 𝒪 (φ f) = 0 := (IsLocalRing.residue_eq_zero_iff _).mpr hmem
    rw [hφres] at h0
    exact hf (hinj (by rw [h0, map_zero]))

  let K₀ := FractionRing P
  let ψ : K₀ →ₐ[K] 𝒪 := IsLocalization.liftAlgHom (M := nonZeroDivisors P) (f := φ)
    (fun y => hunit y.1 (nonZeroDivisors.ne_zero y.2))
  letI : Algebra K₀ 𝒪 := ψ.toRingHom.toAlgebra
  have hψ : ∀ z : K₀, algebraMap K₀ 𝒪 z = ψ z := fun _ => rfl
  haveI : IsScalarTower K K₀ 𝒪 := IsScalarTower.of_algebraMap_eq fun x => by
    rw [hψ, ψ.commutes]
  letI : Algebra P 𝒪 := φ.toRingHom.toAlgebra
  have hφ : ∀ f : P, algebraMap P 𝒪 f = φ f := fun _ => rfl
  haveI : IsScalarTower P K₀ 𝒪 := IsScalarTower.of_algebraMap_eq fun f => by
    rw [hψ, hφ]
    change φ f = IsLocalization.lift (M := nonZeroDivisors P) _ (algebraMap P K₀ f)
    rw [IsLocalization.lift_eq]
    rfl

  haveI : Algebra.FormallySmooth P K₀ := Algebra.FormallySmooth.of_isLocalization (Rₘ := K₀) (nonZeroDivisors P)
  haveI : Algebra.FormallySmooth K K₀ := Algebra.FormallySmooth.comp K P K₀
  haveI : Algebra.EssFiniteType K₀ 𝒪 := Algebra.EssFiniteType.of_comp K K₀ 𝒪

  let F : IntermediateField K (ResidueField 𝒪) := IntermediateField.adjoin K (Set.range ((↑) : s → ResidueField 𝒪))
  let e : K₀ ≃ₐ[K] F := hs.1.aevalEquivField
  have hrange : (Set.range ((↑) : s → ResidueField 𝒪)) = (s : Set (ResidueField 𝒪)) := by
    ext x; simp
  haveI : Algebra.IsSeparable F (ResidueField 𝒪) := by
    have : F = IntermediateField.adjoin K (s : Set (ResidueField 𝒪)) := by rw [← hrange]
    rw [this]; exact hsep
  have hcompat : (algebraMap K₀ (ResidueField 𝒪)).comp (e.symm.toRingEquiv : F →+* K₀) =
      (RingEquiv.refl (ResidueField 𝒪) : ResidueField 𝒪 →+* ResidueField 𝒪).comp (algebraMap F (ResidueField 𝒪)) := by

    have key : (algebraMap K₀ (ResidueField 𝒪)) = (algebraMap F (ResidueField 𝒪)).comp (e.toRingEquiv : K₀ →+* F) := by
      refine IsLocalization.ringHom_ext (nonZeroDivisors P) ?_
      ext f
      · simp only [RingHom.coe_comp, Function.comp_apply]
        rw [IsScalarTower.algebraMap_apply K₀ 𝒪 (ResidueField 𝒪), ← IsScalarTower.algebraMap_apply P K₀ 𝒪]
        change IsLocalRing.residue 𝒪 (φ (MvPolynomial.C f)) = _
        rw [hφres]
        change MvPolynomial.aeval _ (MvPolynomial.C f) =
          ((e (algebraMap P K₀ (MvPolynomial.C f)) : F) : ResidueField 𝒪)
        rw [AlgebraicIndependent.aevalEquivField_algebraMap_apply_coe]
      · simp only [RingHom.coe_comp, Function.comp_apply]
        rw [IsScalarTower.algebraMap_apply K₀ 𝒪 (ResidueField 𝒪), ← IsScalarTower.algebraMap_apply P K₀ 𝒪]
        change IsLocalRing.residue 𝒪 (φ (MvPolynomial.X _)) = _
        rw [hφres]
        change MvPolynomial.aeval _ (MvPolynomial.X _) =
          ((e (algebraMap P K₀ (MvPolynomial.X _)) : F) : ResidueField 𝒪)
        rw [AlgebraicIndependent.aevalEquivField_algebraMap_apply_coe]
    rw [key]
    ext x
    simp
  haveI : Algebra.IsSeparable K₀ (ResidueField 𝒪) :=
    Algebra.IsSeparable.of_equiv_equiv (e.symm.toRingEquiv : F ≃+* K₀) (RingEquiv.refl (ResidueField 𝒪)) hcompat
  haveI : Algebra.IsAlgebraic K₀ (ResidueField 𝒪) := Algebra.IsSeparable.isAlgebraic _ _

  haveI := Algebra.FormallySmooth.of_maximalIdeal_eq_span_of_isSeparable_residueField K₀ 𝒪 u hu0 hu
  exact Algebra.FormallySmooth.comp K K₀ 𝒪

end S_Algebra_FormallySmooth_of_maximalIdeal_eq_span_of_perfectField
end P2MW
export P2MW.S_Algebra_FormallySmooth_of_maximalIdeal_eq_span_of_perfectField (solution)
