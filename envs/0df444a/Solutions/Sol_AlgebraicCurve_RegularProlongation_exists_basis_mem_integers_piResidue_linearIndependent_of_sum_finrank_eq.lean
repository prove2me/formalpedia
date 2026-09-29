-- Prove2me | solution 1 for AlgebraicCurve.RegularProlongation.exists_basis_mem_integers_piResidue_linearIndependent_of_sum_finrank_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/2a2b235a-1944-57e9-993d-36301d6746ed

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Theorems.Thm_AlgebraicCurve_RegularProlongation_finrank_span_pi_residue_eq_finrank_of_sum_finrank_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RegularProlongation_exists_basis_mem_integers_piResidue_linearIndependent_of_sum_finrank_eq

set_option autoImplicit false
set_option maxHeartbeats 6400000

noncomputable section
open AlgebraicCurve IsLocalRing

namespace E78MVfree

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

private theorem _root_.E78MVfree.residue_eq_zero_iff (R : RegularProlongation A F Fbar) (w : R.integers) :
    R.residue w = 0 ↔ w ∈ maximalIdeal R.integers := by
  change w ∈ RingHom.ker R.residue ↔ _; rw [R.ker_residue]

p2m_export "E78MVfree" "residue_eq_zero_iff"
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

theorem mem_of_sum_smul_mem_joint (t : Finset J) (g : J → L)
    (h : ∀ i, ∑ j ∈ t, g j • E j ∈ (R i).integers) : ∀ j ∈ t, g j ∈ A := by
  classical
  by_contra hne
  obtain ⟨j₀, hj₀t, hgj₀⟩ := not_forall₂.mp hne
  have hg0 : g j₀ ≠ 0 := by rintro h0; exact hgj₀ (h0 ▸ zero_mem A)
  obtain ⟨j₁, hj₁t, hg₁, hcA, hmax⟩ := exists_normalizer A t g hj₀t hg0
  set c : L := (g j₁)⁻¹
  have hv₁ : 1 < A.valuation (g j₁) := lt_of_lt_of_le
    (by rw [← not_le, A.valuation_le_one_iff]; exact hgj₀) (hmax j₀ hj₀t)
  have hcv : A.valuation c < 1 := by
    rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hv₁
  have hcmem : c ∈ A := (A.valuation_le_one_iff c).mp hcv.le
  have hcres : IsLocalRing.residue A ⟨c, hcmem⟩ = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]; exact hcv
  let a : J → A := fun j => if hj : j ∈ t then ⟨c * g j, hcA j hj⟩ else 0
  have ha : ∀ j ∈ t, (a j : L) = c * g j := fun j hj => by simp [a, dif_pos hj]
  have hsum_eq : ∑ j ∈ t, (a j : L) • E j = algebraMap L F c * ∑ j ∈ t, g j • E j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [ha j hj, mul_smul, Algebra.smul_def]
  have hres0 : ∀ i, (R i).residue ⟨∑ j ∈ t, (a j : L) • E j, sum_smul_mem R E hEmem t a i⟩ = 0 := by
    intro i
    have heq : (⟨∑ j ∈ t, (a j : L) • E j, sum_smul_mem R E hEmem t a i⟩ : (R i).integers) =
        constHom (R i) ⟨c, hcmem⟩ * ⟨∑ j ∈ t, g j • E j, h i⟩ := by
      refine Subtype.ext ?_; push_cast; simp only [coe_constHom]; exact hsum_eq
    rw [heq, map_mul, residue_constHom, hcres, map_zero, zero_mul]
  have hall := residue_coeff_eq_zero_joint R E hEmem hE t a hres0 j₁ hj₁t
  have ha1 : a j₁ = 1 := Subtype.ext (by
    simp only [ha j₁ hj₁t, c, inv_mul_cancel₀ hg₁, OneMemClass.coe_one])
  rw [ha1, map_one] at hall; exact one_ne_zero hall

theorem linearIndependent_coe_joint : LinearIndependent L E := by
  classical
  rw [linearIndependent_iff']
  intro t g hsum j hj
  have hmem : ∀ i, ∑ j ∈ t, g j • E j ∈ (R i).integers := fun i => hsum ▸ zero_mem _
  have h0 : ∀ i, (R i).residue ⟨_, hmem i⟩ = 0 := fun i => by
    have : (⟨_, hmem i⟩ : (R i).integers) = 0 := Subtype.ext hsum; rw [this, map_zero]
  by_contra hgj
  have hsum' : ∑ j' ∈ t, ((g j)⁻¹ * g j') • E j' = 0 := by
    simp_rw [mul_smul, ← Finset.smul_sum, hsum, smul_zero]
  have hmem' : ∀ i, ∑ j' ∈ t, ((g j)⁻¹ * g j') • E j' ∈ (R i).integers :=
    fun i => hsum' ▸ zero_mem _
  have hA := mem_of_sum_smul_mem_joint R E hEmem hE t (fun j' => (g j)⁻¹ * g j') hmem'
  have h0' : ∀ i, (R i).residue ⟨_, hmem' i⟩ = 0 := fun i => by
    have : (⟨_, hmem' i⟩ : (R i).integers) = 0 := Subtype.ext hsum'; rw [this, map_zero]

  let a : J → A := fun j' => if hj' : j' ∈ t then ⟨(g j)⁻¹ * g j', hA j' hj'⟩ else 0
  have ha : ∀ j' ∈ t, (a j' : L) = (g j)⁻¹ * g j' := fun j' hj' => by simp [a, dif_pos hj']
  have heq : ∀ i, (⟨_, hmem' i⟩ : (R i).integers) =
      ⟨∑ j' ∈ t, (a j' : L) • E j', sum_smul_mem R E hEmem t a i⟩ := fun i => by
    apply Subtype.ext
    exact Finset.sum_congr rfl fun j' hj' => by rw [ha j' hj']
  have hres : ∀ i, (R i).residue ⟨∑ j' ∈ t, (a j' : L) • E j',
      sum_smul_mem R E hEmem t a i⟩ = 0 := fun i => (heq i ▸ h0' i :)
  have hall := residue_coeff_eq_zero_joint R E hEmem hE t a hres j hj
  have ha1 : a j = 1 := Subtype.ext (by simp only [ha j hj, inv_mul_cancel₀ hgj, OneMemClass.coe_one])
  rw [ha1, map_one] at hall; exact one_ne_zero hall

end jointResIndep

end E78MVfree
p2m_reactivate "P2MW.S_AlgebraicCurve_RegularProlongation_exists_basis_mem_integers_piResidue_linearIndependent_of_sum_finrank_eq.E78MVfree"

open E78MVfree

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
    (V : Submodule L F) [FiniteDimensional L V] :
    ∃ w : Fin (Module.finrank L V) → F, ∃ hwO : ∀ a i, w a ∈ (R i).integers,
      (∀ a, w a ∈ V) ∧
      LinearIndependent (IsLocalRing.ResidueField A)
        (fun a => fun i => (R i).residue ⟨w a, hwO a i⟩) ∧
      (∀ u : F, (∀ i, u ∈ (R i).integers) → u ∈ V →
        ∃ c : Fin (Module.finrank L V) → A, u = ∑ a, (c a : L) • w a) := by
  classical
  set k := ResidueField A
  set m := Module.finrank L V with hm
  set S : Set (∀ i, Fb i) := {h | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
    u ∈ V ∧ ∀ i, (R i).residue ⟨u, hu i⟩ = h i}
  have hdim : Module.finrank k (Submodule.span k S) = m :=
    RegularProlongation.finrank_span_pi_residue_eq_finrank_of_sum_finrank_eq
      A Fb R hR f hf htr heq V
  have hSclosed : ∀ h ∈ Submodule.span k S, ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
      u ∈ V ∧ ∀ i, (R i).residue ⟨u, hu i⟩ = h i := by
    intro h hh
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hh
    · exact fun x hx => hx
    · exact ⟨0, fun i => zero_mem _, zero_mem V, fun i => by
        simp only [Pi.zero_apply]; exact map_zero _⟩
    · rintro x y - - ⟨ux, hux, huxV, huxR⟩ ⟨uy, huy, huyV, huyR⟩
      refine ⟨ux + uy, fun i => add_mem (hux i) (huy i), add_mem huxV huyV, fun i => ?_⟩
      have e : (⟨ux + uy, _⟩ : (R i).integers) = ⟨ux, hux i⟩ + ⟨uy, huy i⟩ := Subtype.ext rfl
      rw [e, map_add, huxR i, huyR i]; rfl
    · rintro c x - ⟨ux, hux, huxV, huxR⟩
      obtain ⟨ĉ, hĉ⟩ := IsLocalRing.residue_surjective (R := A) c
      refine ⟨(ĉ : L) • ux, fun i => ?_, V.smul_mem _ huxV, fun i => ?_⟩
      · rw [Algebra.smul_def]
        exact mul_mem ((R i).algebraMap_mem_iff _ |>.mpr ĉ.2) (hux i)
      · have hmem' : (ĉ : L) • ux ∈ (R i).integers := by
          rw [Algebra.smul_def]
          exact mul_mem ((R i).algebraMap_mem_iff _ |>.mpr ĉ.2) (hux i)
        have e : (⟨(ĉ : L) • ux, hmem'⟩ : (R i).integers) =
            constHom (R i) ĉ * ⟨ux, hux i⟩ := by
          refine Subtype.ext ?_
          simp only [MulMemClass.coe_mul, coe_constHom]
          exact Algebra.smul_def (ĉ : L) ux
        rw [show (⟨(ĉ : L) • ux, _⟩ : (R i).integers) = ⟨(ĉ : L) • ux, hmem'⟩ from rfl,
          e, map_mul, residue_constHom, hĉ, huxR i, Pi.smul_apply]
        exact (Algebra.smul_def c (x i)).symm
  rcases Nat.eq_zero_or_pos m with hm0 | hmp
  · haveI : IsEmpty (Fin m) := by rw [hm0]; infer_instance
    refine ⟨isEmptyElim, fun a => isEmptyElim a, fun a => isEmptyElim a,
      linearIndependent_empty_type, fun u _ huV => ?_⟩
    have hVbot : V = ⊥ := Submodule.finrank_eq_zero.mp (hm ▸ hm0)
    refine ⟨isEmptyElim, ?_⟩
    rw [hVbot, Submodule.mem_bot] at huV
    simp [huV]
  · haveI : FiniteDimensional k (Submodule.span k S) :=
      FiniteDimensional.of_finrank_pos (hdim ▸ hmp)
    let b := Module.finBasisOfFinrankEq k (Submodule.span k S) hdim
    choose w hwO hwV hwR using fun a : Fin m => hSclosed (b a : ∀ i, Fb i) (b a).2
    have hwres_eq : (fun a => fun i => (R i).residue ⟨w a, hwO a i⟩) =
        fun a => ((b a : Submodule.span k S) : ∀ i, Fb i) := funext fun a => funext (hwR a)
    have hwLI : LinearIndependent k (fun a => fun i => (R i).residue ⟨w a, hwO a i⟩) := by
      rw [hwres_eq]
      exact b.linearIndependent.map' (Submodule.span k S).subtype (Submodule.ker_subtype _)
    have hwLI' : LinearIndependent k (jointRes R w hwO) := hwLI
    have hwLLI : LinearIndependent L w := linearIndependent_coe_joint R w hwO hwLI'
    have hwspanV : Submodule.span L (Set.range w) = V := by
      have hle : Submodule.span L (Set.range w) ≤ V := by
        rw [Submodule.span_le, Set.range_subset_iff]; exact hwV
      have hfr : Module.finrank L (Submodule.span L (Set.range w)) = m := by
        rw [finrank_span_eq_card hwLLI, Fintype.card_fin]
      exact Submodule.eq_of_le_of_finrank_le hle (hfr.trans hm).ge
    refine ⟨w, hwO, hwV, hwLI, fun u huO huV => ?_⟩
    rw [← hwspanV, Finsupp.mem_span_range_iff_exists_finsupp] at huV
    obtain ⟨g, hg⟩ := huV
    have hgsum : u = ∑ a, g a • w a := by
      rw [← hg, Finsupp.sum_fintype]; exact fun a => zero_smul L (w a)
    have hgsum' : ∀ i, ∑ a ∈ Finset.univ, g a • w a ∈ (R i).integers := fun i => by
      rw [← hgsum]; exact huO i
    have hgA : ∀ a ∈ Finset.univ, g a ∈ A :=
      mem_of_sum_smul_mem_joint R w hwO hwLI' Finset.univ g hgsum'
    exact ⟨fun a => ⟨g a, hgA a (Finset.mem_univ a)⟩, hgsum⟩

end
end S_AlgebraicCurve_RegularProlongation_exists_basis_mem_integers_piResidue_linearIndependent_of_sum_finrank_eq
end P2MW
export P2MW.S_AlgebraicCurve_RegularProlongation_exists_basis_mem_integers_piResidue_linearIndependent_of_sum_finrank_eq (solution)
