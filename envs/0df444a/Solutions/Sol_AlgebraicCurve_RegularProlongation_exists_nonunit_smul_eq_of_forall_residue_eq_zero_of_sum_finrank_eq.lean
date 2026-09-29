-- Prove2me | solution 1 for AlgebraicCurve.RegularProlongation.exists_nonunit_smul_eq_of_forall_residue_eq_zero_of_sum_finrank_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/e0e7173e-c72e-5b2d-80ea-f19a98efd896

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_basis_mem_integers_piResidue_linearIndependent_of_sum_finrank_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RegularProlongation_exists_nonunit_smul_eq_of_forall_residue_eq_zero_of_sum_finrank_eq

set_option autoImplicit false
set_option maxHeartbeats 6400000

noncomputable section
open AlgebraicCurve IsLocalRing

namespace E81QM

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {ι : Type*} [Fintype ι] {Fb : ι → Type*} [∀ i, Field (Fb i)]
  [∀ i, Algebra (ResidueField A) (Fb i)]

section single
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

def constHom (R : RegularProlongation A F Fbar) : A →+* R.integers where
  toFun a := ⟨algebraMap L F a, (R.algebraMap_mem_iff a).mpr a.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

@[scoped simp] theorem coe_constHom (R : RegularProlongation A F Fbar) (a : A) :
    ((constHom R a : R.integers) : F) = algebraMap L F a := rfl

theorem residue_constHom (R : RegularProlongation A F Fbar) (a : A) :
    R.residue (constHom R a) = algebraMap (ResidueField A) Fbar (IsLocalRing.residue A a) :=
  R.residue_algebraMap a

private theorem _root_.E81QM.residue_eq_zero_iff (R : RegularProlongation A F Fbar) (w : R.integers) :
    R.residue w = 0 ↔ w ∈ maximalIdeal R.integers := by
  change w ∈ RingHom.ker R.residue ↔ _; rw [R.ker_residue]

p2m_export "E81QM" "residue_eq_zero_iff"
theorem residue_eq_zero_of_mem_nonunits (R : RegularProlongation A F Fbar) {w : F}
    (hw : w ∈ R.integers) (hn : w ∈ R.integers.nonunits) : R.residue ⟨w, hw⟩ = 0 :=
  (residue_eq_zero_iff R _).mpr
    ((R.integers.valuation_lt_one_iff ⟨w, hw⟩).mpr ((R.integers.mem_nonunits_iff).mp hn))
end single

variable (A) in
theorem exists_normalizer {J : Type*} (t : Finset J) (g : J → L) {i₀ : J} (hi₀ : i₀ ∈ t)
    (hg : g i₀ ≠ 0) :
    ∃ i₁ ∈ t, g i₁ ≠ 0 ∧ (∀ i ∈ t, (g i₁)⁻¹ * g i ∈ A) ∧
      (∀ i ∈ t, A.valuation (g i) ≤ A.valuation (g i₁)) := by
  obtain ⟨i₁, hi₁t, hmax⟩ := t.exists_max_image (fun i => A.valuation (g i)) ⟨i₀, hi₀⟩
  have hg₁ : g i₁ ≠ 0 := by
    intro h0; have h := hmax i₀ hi₀
    rw [h0, map_zero, le_zero_iff, map_eq_zero] at h; exact hg h
  have hv₁ : A.valuation (g i₁) ≠ 0 := by rwa [ne_eq, map_eq_zero]
  refine ⟨i₁, hi₁t, hg₁, fun i hi => ?_, hmax⟩
  rw [← A.valuation_le_one_iff, map_mul, map_inv₀]
  calc (A.valuation (g i₁))⁻¹ * A.valuation (g i)
      ≤ (A.valuation (g i₁))⁻¹ * A.valuation (g i₁) := by gcongr; exact hmax i hi
    _ = 1 := inv_mul_cancel₀ hv₁

section jointResIndep

variable (R : ∀ i, RegularProlongation A F (Fb i))
  {J : Type*} (E : J → F) (hEmem : ∀ j i, E j ∈ (R i).integers)

def jointRes (j : J) : ∀ i, Fb i := fun i => (R i).residue ⟨E j, hEmem j i⟩

include hEmem in
theorem sum_smul_mem (t : Finset J) (a : J → A) (i : ι) :
    ∑ j ∈ t, (a j : L) • E j ∈ (R i).integers := by
  refine (R i).integers.toSubring.sum_mem fun j _ => ?_
  rw [Algebra.smul_def]
  exact (R i).integers.toSubring.mul_mem
    ((R i).algebraMap_mem_iff _ |>.mpr (a j).2) (hEmem j i)

theorem residue_sum_smul (t : Finset J) (a : J → A) (i : ι) :
    (R i).residue ⟨∑ j ∈ t, (a j : L) • E j, sum_smul_mem R E hEmem t a i⟩ =
      ∑ j ∈ t, IsLocalRing.residue A (a j) • jointRes R E hEmem j i := by
  have hXeq : (⟨∑ j ∈ t, (a j : L) • E j, sum_smul_mem R E hEmem t a i⟩ : (R i).integers) =
      ∑ j ∈ t, constHom (R i) (a j) * ⟨E j, hEmem j i⟩ := by
    refine Subtype.ext ?_
    push_cast
    exact Finset.sum_congr rfl fun j _ => by
      simp only [coe_constHom]; exact Algebra.smul_def _ _
  rw [hXeq, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, residue_constHom, Algebra.smul_def]
  rfl

variable (hE : LinearIndependent (ResidueField A) (jointRes R E hEmem))
include hE

theorem residue_coeff_eq_zero_joint (t : Finset J) (a : J → A)
    (h : ∀ i, (R i).residue ⟨∑ j ∈ t, (a j : L) • E j, sum_smul_mem R E hEmem t a i⟩ = 0) :
    ∀ j ∈ t, IsLocalRing.residue A (a j) = 0 := by
  have hsum : ∑ j ∈ t, IsLocalRing.residue A (a j) • jointRes R E hEmem j = 0 := by
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply]
    rw [← residue_sum_smul R E hEmem t a i, h i]
  exact linearIndependent_iff'.mp hE t (fun j => IsLocalRing.residue A (a j)) hsum

end jointResIndep
end E81QM
p2m_reactivate "P2MW.S_AlgebraicCurve_RegularProlongation_exists_nonunit_smul_eq_of_forall_residue_eq_zero_of_sum_finrank_eq.E81QM"

open E81QM

theorem solution
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {ι : Type*} [Fintype ι] (Fb : ι → Type*) [∀ i, Field (Fb i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i))
    (hR : Function.Injective fun i => (R i).integers)
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (htr : ∀ i, Transcendental (IsLocalRing.ResidueField A) ((R i).residue ⟨f, hf i⟩))
    [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    (heq : ∑ i, Module.finrank (IntermediateField.adjoin (IsLocalRing.ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)
      = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F)
    (V : Submodule L F) [FiniteDimensional L V]
    (u : F) (huO : ∀ i, u ∈ (R i).integers) (huV : u ∈ V)
    (hres : ∀ i, (R i).residue ⟨u, huO i⟩ = 0) :
    ∃ (a : A) (u' : F), ¬ IsUnit a ∧ (∀ i, u' ∈ (R i).integers) ∧ u' ∈ V ∧
      u = (a : L) • u' := by
  classical

  obtain ⟨w, hwO, hwV, hwLI, hwspan⟩ :=
    AlgebraicCurve.RegularProlongation.exists_basis_mem_integers_piResidue_linearIndependent_of_sum_finrank_eq
      A Fb R hR f hf htr heq V

  obtain ⟨c, hc⟩ := hwspan u huO huV

  have hwLI' : LinearIndependent (ResidueField A) (jointRes R w hwO) := hwLI

  have hres' : ∀ i, (R i).residue ⟨∑ a, (c a : L) • w a, sum_smul_mem R w hwO Finset.univ c i⟩ = 0 := by
    intro i
    have he : (⟨∑ a, (c a : L) • w a, sum_smul_mem R w hwO Finset.univ c i⟩ : (R i).integers)
        = ⟨u, huO i⟩ := Subtype.ext (by simp only [← hc])
    rw [he]; exact hres i
  have hczero : ∀ a ∈ Finset.univ, IsLocalRing.residue A (c a) = 0 :=
    residue_coeff_eq_zero_joint R w hwO hwLI' Finset.univ c hres'

  rcases eq_or_ne u 0 with hu0 | hune
  · exact ⟨0, 0, not_isUnit_zero, fun i => zero_mem _, zero_mem V, by simp [hu0]⟩

  have hcex : ∃ a₀, (c a₀ : L) ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply hune
    rw [hc]
    exact Finset.sum_eq_zero fun a _ => by rw [hall a, zero_smul]
  obtain ⟨a₀, ha₀⟩ := hcex

  obtain ⟨i₁, -, hci₁, hcA, hcmax⟩ :=
    exists_normalizer A Finset.univ (fun a => (c a : L)) (Finset.mem_univ a₀) ha₀

  have hnu : ¬ IsUnit (c i₁) := by
    rw [← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff]
    exact hczero i₁ (Finset.mem_univ i₁)

  let d : Fin (Module.finrank L V) → A := fun a => ⟨(c i₁ : L)⁻¹ * (c a : L), hcA a (Finset.mem_univ a)⟩
  refine ⟨c i₁, ∑ a, (d a : L) • w a, hnu, fun i => sum_smul_mem R w hwO Finset.univ d i, ?_, ?_⟩
  · exact V.sum_mem fun a _ => V.smul_mem _ (hwV a)
  · rw [hc, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [smul_smul]
    congr 1
    simp only [d, mul_inv_cancel_left₀ hci₁]

end
end S_AlgebraicCurve_RegularProlongation_exists_nonunit_smul_eq_of_forall_residue_eq_zero_of_sum_finrank_eq
end P2MW
export P2MW.S_AlgebraicCurve_RegularProlongation_exists_nonunit_smul_eq_of_forall_residue_eq_zero_of_sum_finrank_eq (solution)
