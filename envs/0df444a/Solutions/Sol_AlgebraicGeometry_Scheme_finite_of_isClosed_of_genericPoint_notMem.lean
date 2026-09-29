-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.finite_of_isClosed_of_genericPoint_notMem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/4d5f1631-ee34-5908-9630-7f0e425e882f

import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_finite_of_isClosed_of_genericPoint_notMem

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Topology

namespace OneDimAux

private lemma isClosed_singleton_of_ne_genericPoint {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] (hdim : ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ 1)
    {z : X} (hz : z ≠ genericPoint X) : IsClosed ({z} : Set X) := by
  rw [← closure_subset_iff_isClosed]
  intro x hx
  have hzx : z ⤳ x := specializes_iff_mem_closure.mpr hx
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) trivial
  have hzU : z ∈ U := hzx.mem_open U.isOpen hxU
  have hηU : genericPoint X ∈ U := (genericPoint_specializes x).mem_open U.isOpen hxU
  haveI : Nonempty U := ⟨⟨x, hxU⟩⟩
  haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hxU⟩ : U)

  set px := hU.primeIdealOf ⟨x, hxU⟩ with hpx
  set pz := hU.primeIdealOf ⟨z, hzU⟩ with hpz
  have hle : pz ≤ px := by
    rw [PrimeSpectrum.le_iff_specializes, hpz, hpx]
    refine Specializes.map ?_ hU.isoSpec.hom.base.hom.continuous
    exact (IsInducing.subtypeVal.specializes_iff).mp hzx

  have hloc := hU.isLocalization_stalk ⟨x, hxU⟩
  have hheight : (px.asIdeal.height : WithBot ℕ∞) ≤ 1 := by
    rw [← IsLocalization.AtPrime.ringKrullDim_eq_height px.asIdeal
      (X.presheaf.stalk ((⟨x, hxU⟩ : U) : X))]
    exact hdim x
  rcases eq_or_ne pz px with h | h
  ·
    have := congrArg hU.fromSpec h
    rw [hpz, hpx, hU.fromSpec_primeIdealOf, hU.fromSpec_primeIdealOf] at this
    exact Set.mem_singleton_iff.mpr this.symm
  · exfalso
    have hlt : pz < px := lt_of_le_of_ne hle h
    rcases eq_or_ne pz.asIdeal ⊥ with hbot | hbot
    ·
      apply hz
      have hgen : pz = genericPoint (Spec Γ(X, U)) := by
        rw [genericPoint_eq_bot_of_affine]; exact PrimeSpectrum.ext hbot
      have := hU.fromSpec_primeIdealOf ⟨z, hzU⟩
      rw [← hpz, hgen, ← hU.primeIdealOf_genericPoint, hU.fromSpec_primeIdealOf] at this
      exact this.symm
    ·
      have h1 : (⊥ : Ideal Γ(X, U)).height < pz.asIdeal.height :=
        Ideal.height_strict_mono_of_isPrime_of_isPrime (bot_lt_iff_ne_bot.mpr hbot)
      have h2 : pz.asIdeal.height < px.asIdeal.height :=
        Ideal.height_strict_mono_of_isPrime_of_isPrime hlt
      rw [Ideal.height_bot] at h1
      have e1 : (1 : ℕ∞) ≤ pz.asIdeal.height := by
        have := Order.add_one_le_of_lt h1; rwa [zero_add] at this
      have e2 : pz.asIdeal.height + 1 ≤ px.asIdeal.height := Order.add_one_le_of_lt h2
      have h3 : (2 : ℕ∞) ≤ px.asIdeal.height :=
        calc (2 : ℕ∞) = 1 + 1 := one_add_one_eq_two.symm
          _ ≤ pz.asIdeal.height + 1 := by gcongr
          _ ≤ px.asIdeal.height := e2
      have h4 : ((2 : ℕ∞) : WithBot ℕ∞) ≤ ((1 : ℕ∞) : WithBot ℕ∞) :=
        (WithBot.coe_le_coe.mpr h3).trans hheight
      rw [WithBot.coe_le_coe] at h4
      exact absurd h4 (by norm_num)

end OneDimAux

open OneDimAux in
theorem solution {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [CompactSpace X]
    (hdim : ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ 1)
    {Z : Set X} (hZ : IsClosed Z) (hη : genericPoint X ∉ Z) : Z.Finite := by
  haveI : IsNoetherian X := {}
  suffices H : ∀ C : Closeds X, genericPoint X ∉ (C : Set X) → (C : Set X).Finite from
    H ⟨Z, hZ⟩ hη
  intro C
  induction C using WellFoundedLT.induction with
  | ind C ih =>
    intro hC
    by_cases hirr : IsPreirreducible (C : Set X)
    · rcases (C : Set X).eq_empty_or_nonempty with h | hne
      · rw [h]; exact Set.finite_empty
      · obtain ⟨w, hw⟩ := QuasiSober.sober ⟨hne, hirr⟩ C.isClosed
        have hwC : w ∈ (C : Set X) := hw.mem
        have hwη : w ≠ genericPoint X := fun h => hC (h ▸ hwC)
        have : (C : Set X) = {w} := by
          rw [← isGenericPoint_def.mp hw,
            (isClosed_singleton_of_ne_genericPoint hdim hwη).closure_eq]
        rw [this]; exact Set.finite_singleton w
    · rw [isPreirreducible_iff_isClosed_union_isClosed] at hirr
      push Not at hirr
      obtain ⟨z₁, z₂, hz₁, hz₂, hsub, h₁, h₂⟩ := hirr
      have lt₁ : C ⊓ ⟨z₁, hz₁⟩ < C := by
        refine lt_of_le_of_ne inf_le_left fun h => h₁ ?_
        have := congrArg (fun D : Closeds X => (D : Set X)) h
        simp only [Closeds.coe_inf, Closeds.coe_mk] at this
        rw [← this]; exact Set.inter_subset_right
      have lt₂ : C ⊓ ⟨z₂, hz₂⟩ < C := by
        refine lt_of_le_of_ne inf_le_left fun h => h₂ ?_
        have := congrArg (fun D : Closeds X => (D : Set X)) h
        simp only [Closeds.coe_inf, Closeds.coe_mk] at this
        rw [← this]; exact Set.inter_subset_right
      have f₁ := ih _ lt₁ (fun h => hC h.1)
      have f₂ := ih _ lt₂ (fun h => hC h.1)
      refine (f₁.union f₂).subset fun y hy => ?_
      rcases hsub hy with h | h
      · exact Or.inl ⟨hy, h⟩
      · exact Or.inr ⟨hy, h⟩

end S_AlgebraicGeometry_Scheme_finite_of_isClosed_of_genericPoint_notMem
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_finite_of_isClosed_of_genericPoint_notMem (solution)
