-- Prove2me | solution 1 for AlgebraicCurve.RegularProlongation.exists_forall_transcendental_residue
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/d9497543-d916-58f8-b327-45381c334748

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Theorems.Thm_ValuationSubring_exists_forall_mem_and_sub_mem_nonunits
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RegularProlongation_exists_forall_transcendental_residue

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open AlgebraicCurve IsLocalRing IntermediateField

namespace W10XK3P

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]

section single
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

theorem residue_eq_zero_of_mem_nonunits (R : RegularProlongation A F Fbar) {w : F}
    (hw : w ∈ R.integers) (hn : w ∈ R.integers.nonunits) : R.residue ⟨w, hw⟩ = 0 := by
  have h1 : (⟨w, hw⟩ : R.integers) ∈ maximalIdeal R.integers :=
    (R.integers.valuation_lt_one_iff ⟨w, hw⟩).mpr ((R.integers.mem_nonunits_iff).mp hn)
  rw [← R.ker_residue] at h1; exact h1

theorem integers_eq_of_le {Fbar' : Type*} [Field Fbar'] [Algebra (ResidueField A) Fbar']
    (R₁ : RegularProlongation A F Fbar) (R₂ : RegularProlongation A F Fbar')
    (h : R₁.integers ≤ R₂.integers) : R₁.integers = R₂.integers := by
  refine le_antisymm h fun y hy₂ => ?_
  by_contra hy₁
  have hy0 : y ≠ 0 := by rintro rfl; exact hy₁ (zero_mem _)
  obtain ⟨c, hcy, hres⟩ := R₁.exists_smul_mem y hy0
  have hc0 : c ≠ 0 := R₁.smul_const_ne_zero hcy hres
  set v₁ := R₁.integers.valuation with hv₁
  set v₂ := R₂.integers.valuation with hv₂
  set cF : F := algebraMap L F c with hcF
  have hcF0 : cF ≠ 0 := by rw [hcF]; exact (map_ne_zero _).mpr hc0
  have hcy' : c • y = cF * y := Algebra.smul_def c y
  have hu : IsUnit (⟨c • y, hcy⟩ : R₁.integers) := R₁.isUnit_of_residue_ne_zero hres
  have h1 : v₁ (cF * y) = 1 := by
    have h' : v₁ (c • y) = 1 := (R₁.integers.valuation_eq_one_iff ⟨c • y, hcy⟩).mp hu
    rwa [hcy'] at h'
  have hy1 : 1 < v₁ y := by
    rw [← not_le]; intro hle; exact hy₁ ((R₁.integers.valuation_le_one_iff y).mp hle)
  have hc1 : v₁ cF < 1 := by
    by_contra hge; rw [not_lt] at hge
    have h' : 1 * v₁ y ≤ v₁ cF * v₁ y := mul_le_mul' hge le_rfl
    rw [one_mul, ← map_mul, h1] at h'; exact (not_le.mpr hy1) h'
  have hcA : c ∈ A := (R₁.algebraMap_mem_iff c).mp ((R₁.integers.valuation_le_one_iff cF).mp hc1.le)
  have hcinv : c⁻¹ ∉ A := by
    intro hinv
    have hmem : cF⁻¹ ∈ R₁.integers := by
      have := (R₁.algebraMap_mem_iff c⁻¹).mpr hinv; rwa [map_inv₀] at this
    have hle : v₁ cF⁻¹ ≤ 1 := (R₁.integers.valuation_le_one_iff _).mpr hmem
    have h' : v₁ cF⁻¹ * v₁ cF ≤ 1 * v₁ cF := mul_le_mul' hle le_rfl
    rw [← map_mul, inv_mul_cancel₀ hcF0, map_one, one_mul] at h'
    exact (not_lt.mpr h') hc1
  have hcF2 : v₂ cF ≤ 1 :=
    (R₂.integers.valuation_le_one_iff cF).mpr ((R₂.algebraMap_mem_iff c).mpr hcA)
  have hy2 : v₂ y ≤ 1 := (R₂.integers.valuation_le_one_iff y).mpr hy₂
  have hinv1 : (cF * y)⁻¹ ∈ R₁.integers := by
    rw [← R₁.integers.valuation_le_one_iff, map_inv₀, h1, inv_one]
  have hinv2 : v₂ (cF * y)⁻¹ ≤ 1 := (R₂.integers.valuation_le_one_iff _).mpr (h hinv1)
  have hcy0 : cF * y ≠ 0 := mul_ne_zero hcF0 hy0
  have hc2 : v₂ cF = 1 := by
    refine le_antisymm hcF2 ?_
    by_contra hlt; rw [not_le] at hlt
    have hprod : v₂ (cF * y) < 1 := by
      rw [map_mul]
      calc v₂ cF * v₂ y ≤ v₂ cF * 1 := mul_le_mul' le_rfl hy2
        _ = v₂ cF := mul_one _
        _ < 1 := hlt
    have h' : v₂ (cF * y)⁻¹ * v₂ (cF * y) ≤ 1 * v₂ (cF * y) := mul_le_mul' hinv2 le_rfl
    rw [← map_mul, inv_mul_cancel₀ hcy0, map_one, one_mul] at h'
    exact (not_lt.mpr h') hprod
  have hmem2 : cF⁻¹ ∈ R₂.integers := by
    rw [← R₂.integers.valuation_le_one_iff, map_inv₀, hc2, inv_one]
  have : c⁻¹ ∈ A := by
    rw [← R₂.algebraMap_mem_iff, map_inv₀]; exact hmem2
  exact hcinv this

end single

open scoped _root_.IntermediateField.algebraAdjoinAdjoin in

theorem finiteDimensional_adjoin_of_transcendental
    (hF : ∃ x : F, Transcendental L x ∧
      FiniteDimensional (IntermediateField.adjoin L ({x} : Set F)) F)
    {z : F} (hz : Transcendental L z) :
    FiniteDimensional (IntermediateField.adjoin L ({z} : Set F)) F := by
  obtain ⟨x, htrx, hfdx⟩ := hF

  have hzLx : IsAlgebraic (Algebra.adjoin L ({x} : Set F)) z := by
    refine isAlgebraic_adjoin_iff.mp ?_
    exact (Algebra.IsAlgebraic.of_finite L⟮x⟯ F).isAlgebraic z
  have hxLz' : IsAlgebraic (Algebra.adjoin L ({z} : Set F)) x := by
    have := IsAlgebraic.adjoin_singleton (R := L) (A := F) (B := F) htrx hz hzLx
    simpa using this
  have hxLz : IsAlgebraic L⟮z⟯ x := isAlgebraic_adjoin_iff.mpr hxLz'

  let Lzx : IntermediateField L⟮z⟯ F := L⟮z⟯⟮x⟯
  have hfd1 : FiniteDimensional L⟮z⟯ Lzx :=
    IntermediateField.adjoin.finiteDimensional hxLz.isIntegral

  have hle : L⟮x⟯ ≤ Lzx.restrictScalars L := by
    refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro _ ⟨rfl⟩
    exact IntermediateField.subset_adjoin L⟮z⟯ {x} rfl

  letI : Algebra L⟮x⟯ (Lzx.restrictScalars L) :=
    (IntermediateField.inclusion hle).toAlgebra
  have hst : IsScalarTower L⟮x⟯ (Lzx.restrictScalars L) F := by
    refine IsScalarTower.of_algebraMap_eq fun a => ?_
    rfl
  have hfd2 : FiniteDimensional (Lzx.restrictScalars L) F :=
    Module.Finite.of_restrictScalars_finite L⟮x⟯ (Lzx.restrictScalars L) F
  have hfd2' : FiniteDimensional Lzx F := hfd2
  exact FiniteDimensional.trans L⟮z⟯ Lzx F

end W10XK3P

open W10XK3P

theorem solution
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    (hF : ∃ x : F, Transcendental L x ∧
      FiniteDimensional (IntermediateField.adjoin L ({x} : Set F)) F)
    {ι : Type*} [Fintype ι] (Fb : ι → Type*) [∀ i, Field (Fb i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i))
    (hR : Function.Injective fun i => (R i).integers)
    (hnA : ∀ i, ¬ Algebra.IsAlgebraic (IsLocalRing.ResidueField A) (Fb i)) :
    ∃ f : F, ∃ hf : ∀ i, f ∈ (R i).integers,
      Transcendental L f ∧
      FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F ∧
      ∀ i, Transcendental (IsLocalRing.ResidueField A) ((R i).residue ⟨f, hf i⟩) := by
  classical
  set k := IsLocalRing.ResidueField A
  rcases isEmpty_or_nonempty ι with hι | hι
  · obtain ⟨x, htrx, hfdx⟩ := hF
    exact ⟨x, fun i => (hι.false i).elim, htrx, hfdx, fun i => (hι.false i).elim⟩
  have hy : ∀ i, ∃ y : Fb i, Transcendental k y := by
    intro i; by_contra h; push_neg at h
    exact (hnA i) ⟨fun y => not_not.mp (h y)⟩
  choose y hytr using hy
  choose u hu using fun i => (R i).residue_surjective (y i)
  have hincomp : ∀ i j, (R i).integers ≤ (R j).integers → i = j :=
    fun i j hle => hR (integers_eq_of_le (R i) (R j) hle)
  obtain ⟨z, hz⟩ := ValuationSubring.exists_forall_mem_and_sub_mem_nonunits
    (fun i => (R i).integers) hincomp (fun i => (u i : F)) (fun i => (u i).2)
  have hmem : ∀ i, z ∈ (R i).integers := fun i => (hz i).1
  have hres : ∀ i, (R i).residue ⟨z, hmem i⟩ = y i := by
    intro i
    have h0 := residue_eq_zero_of_mem_nonunits (R i) (sub_mem (hz i).1 (u i).2) (hz i).2
    have e : (⟨z - (u i : F), sub_mem (hz i).1 (u i).2⟩ : (R i).integers) =
        ⟨z, hmem i⟩ - u i := by
      apply Subtype.ext; simp
    rw [e, map_sub, sub_eq_zero] at h0
    rw [h0, hu i]
  have htrL : Transcendental L z := by
    intro halg
    obtain ⟨i⟩ := hι
    have : Algebra.IsAlgebraic L L⟮z⟯ :=
      isAlgebraic_adjoin_simple halg.isIntegral
    have hbot : L⟮z⟯ = (⊥ : IntermediateField L F) :=
      IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic L⟮z⟯
    have hzbot : z ∈ (⊥ : IntermediateField L F) :=
      hbot ▸ IntermediateField.mem_adjoin_simple_self L z
    obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp hzbot
    have hcA : c ∈ A := by rw [← (R i).algebraMap_mem_iff, hc]; exact hmem i
    have hrk : (R i).residue ⟨z, hmem i⟩ =
        algebraMap k (Fb i) (IsLocalRing.residue A ⟨c, hcA⟩) := by
      have := (R i).residue_algebraMap ⟨c, hcA⟩
      rw [← this]; congr 1; exact Subtype.ext hc.symm
    rw [hres i] at hrk
    exact (hytr i) (hrk ▸ isAlgebraic_algebraMap _)
  exact ⟨z, hmem, htrL, finiteDimensional_adjoin_of_transcendental hF htrL,
    fun i => hres i ▸ hytr i⟩

end
end S_AlgebraicCurve_RegularProlongation_exists_forall_transcendental_residue
end P2MW
export P2MW.S_AlgebraicCurve_RegularProlongation_exists_forall_transcendental_residue (solution)
