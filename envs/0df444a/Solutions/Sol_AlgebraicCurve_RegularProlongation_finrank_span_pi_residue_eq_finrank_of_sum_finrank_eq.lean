-- Prove2me | solution 1 for AlgebraicCurve.RegularProlongation.finrank_span_pi_residue_eq_finrank_of_sum_finrank_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/b9898eb3-f2ad-5e9a-b0be-ceeffed87b92

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Theorems.Thm_ValuationSubring_exists_forall_mem_and_sub_mem_nonunits
import Theorems.Thm_AlgebraicCurve_RegularProlongation_sum_finrank_adjoin_residue_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RegularProlongation_finrank_span_pi_residue_eq_finrank_of_sum_finrank_eq

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open AlgebraicCurve IsLocalRing Polynomial

namespace W10XK3ER2

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

private theorem _root_.W10XK3ER2.residue_eq_zero_iff (R : RegularProlongation A F Fbar) (w : R.integers) :
    R.residue w = 0 ↔ w ∈ maximalIdeal R.integers := by
  change w ∈ RingHom.ker R.residue ↔ _; rw [R.ker_residue]

p2m_export "W10XK3ER2" "residue_eq_zero_iff"
theorem residue_eq_zero_of_mem_nonunits (R : RegularProlongation A F Fbar) {w : F}
    (hw : w ∈ R.integers) (hn : w ∈ R.integers.nonunits) : R.residue ⟨w, hw⟩ = 0 :=
  (residue_eq_zero_iff R _).mpr
    ((R.integers.valuation_lt_one_iff ⟨w, hw⟩).mpr ((R.integers.mem_nonunits_iff).mp hn))

theorem integers_eq_of_le {Fbar' : Type*} [Field Fbar'] [Algebra (ResidueField A) Fbar']
    (R₁ : RegularProlongation A F Fbar) (R₂ : RegularProlongation A F Fbar')
    (h : R₁.integers ≤ R₂.integers) : R₁.integers = R₂.integers := by
  refine le_antisymm h fun y hy₂ => ?_
  by_contra hy₁
  have hy0 : y ≠ 0 := by rintro rfl; exact hy₁ (zero_mem _)
  obtain ⟨c, hcy, hres⟩ := R₁.exists_smul_mem y hy0
  have hc0 : c ≠ 0 := R₁.smul_const_ne_zero hcy hres
  set v₁ := R₁.integers.valuation; set v₂ := R₂.integers.valuation
  set cF : F := algebraMap L F c
  have hcF0 : cF ≠ 0 := by simp only [cF, ne_eq, FaithfulSMul.algebraMap_eq_zero_iff]; exact hc0
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
  exact hcinv ((R₂.algebraMap_mem_iff c⁻¹).mp (by rw [map_inv₀]; exact hmem2))

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

variable (A) in
theorem exists_adapted {V : Type*} [AddCommGroup V] [Module L V] {J : Type*} [Fintype J]
    (ℓ : J → V →ₗ[L] L) :
    ∀ (d : ℕ) (W : Submodule L V), (∀ v ∈ W, (∀ j, ℓ j v = 0) → v = 0) →
      Module.finrank L W = d →
      ∃ (b : Fin d → V) (c : Fin d → J), Function.Injective c ∧ (∀ a, b a ∈ W) ∧
        (∀ a j, ℓ j (b a) ∈ A) ∧ (∀ a a', ℓ (c a) (b a') = if a = a' then 1 else 0) := by
  classical
  intro d
  induction d with
  | zero =>
    intro W _ _
    exact ⟨Fin.elim0, Fin.elim0, fun a => Fin.elim0 a, fun a => Fin.elim0 a,
      fun a => Fin.elim0 a, fun a => Fin.elim0 a⟩
  | succ d ih =>
    intro W hinj hW
    haveI : Module.Finite L W := Module.finite_of_finrank_eq_succ hW
    have hWne : W ≠ ⊥ := by
      intro hbot; rw [hbot, finrank_bot] at hW; exact Nat.succ_ne_zero d hW.symm
    obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWne
    have hex : ∃ j, ℓ j w ≠ 0 := by
      by_contra hall; push_neg at hall; exact hw0 (hinj w hwW hall)
    obtain ⟨j₁, hj₁⟩ := hex
    obtain ⟨j₀, -, hj₀, hcA, -⟩ :=
      exists_normalizer A Finset.univ (fun j => ℓ j w) (Finset.mem_univ j₁) hj₁
    set w' : V := (ℓ j₀ w)⁻¹ • w with hw'
    have hw'W : w' ∈ W := W.smul_mem _ hwW
    have hw'A : ∀ j, ℓ j w' ∈ A := fun j => by
      rw [hw', map_smul, smul_eq_mul]; exact hcA j (Finset.mem_univ j)
    have hw'1 : ℓ j₀ w' = 1 := by rw [hw', map_smul, smul_eq_mul, inv_mul_cancel₀ hj₀]
    let φ : W →ₗ[L] L := (ℓ j₀).domRestrict W
    have hφsurj : Function.Surjective φ := by
      intro c; refine ⟨⟨c • w', W.smul_mem _ hw'W⟩, ?_⟩; simp [φ, hw'1]
    have hrange : Module.finrank L (LinearMap.range φ) = 1 := by
      rw [LinearMap.range_eq_top.mpr hφsurj, finrank_top, Module.finrank_self]
    have hsum := LinearMap.finrank_range_add_finrank_ker φ
    have hker : Module.finrank L (LinearMap.ker φ) = d := by rw [hrange, hW] at hsum; omega
    set W' : Submodule L V := (LinearMap.ker φ).map W.subtype with hW'def
    have hW' : Module.finrank L W' = d := by
      rw [hW'def, Submodule.finrank_map_subtype_eq, hker]
    have hmemW' : ∀ v, v ∈ W' ↔ v ∈ W ∧ ℓ j₀ v = 0 := by
      intro v; rw [hW'def, Submodule.mem_map]
      constructor
      · rintro ⟨y, hy, rfl⟩; exact ⟨y.2, hy⟩
      · rintro ⟨hvW, hv0⟩; exact ⟨⟨v, hvW⟩, hv0, rfl⟩
    have hinj' : ∀ v ∈ W', (∀ j, ℓ j v = 0) → v = 0 := fun v hv hall =>
      hinj v ((hmemW' v).mp hv).1 hall
    obtain ⟨b', c', hc'inj, hb'W', hb'A, hδ'⟩ := ih W' hinj' hW'
    have hb'W : ∀ a, b' a ∈ W := fun a => ((hmemW' _).mp (hb'W' a)).1
    have hb'0 : ∀ a, ℓ j₀ (b' a) = 0 := fun a => ((hmemW' _).mp (hb'W' a)).2
    have hc'ne : ∀ a, c' a ≠ j₀ := by
      intro a h
      have h1 := hδ' a a; rw [if_pos rfl, h, hb'0] at h1; exact zero_ne_one h1
    set b₀ : V := w' - ∑ a, ℓ (c' a) w' • b' a with hb₀
    have hb₀W : b₀ ∈ W := W.sub_mem hw'W (W.sum_mem fun a _ => W.smul_mem _ (hb'W a))
    have hℓb₀ : ∀ j, ℓ j b₀ = ℓ j w' - ∑ a, ℓ (c' a) w' * ℓ j (b' a) := by
      intro j; rw [hb₀, map_sub, map_sum]; simp_rw [map_smul, smul_eq_mul]
    refine ⟨Fin.cons b₀ b', Fin.cons j₀ c', ?_, ?_, ?_, ?_⟩
    · rw [Fin.cons_injective_iff]; refine ⟨?_, hc'inj⟩
      rintro ⟨a, ha⟩; exact hc'ne a ha
    · intro a; refine Fin.cases ?_ (fun a => ?_) a
      · simpa using hb₀W
      · simpa using hb'W a
    · intro a j; refine Fin.cases ?_ (fun a => ?_) a
      · simp only [Fin.cons_zero]; rw [hℓb₀]
        exact A.sub_mem (hw'A j)
          (A.toSubring.sum_mem fun a _ => A.toSubring.mul_mem (hw'A (c' a)) (hb'A a j))
      · simp only [Fin.cons_succ]; exact hb'A a j
    · intro a a'
      refine Fin.cases ?_ (fun a => ?_) a <;> refine Fin.cases ?_ (fun a' => ?_) a'
      · simp only [Fin.cons_zero]; rw [hℓb₀, hw'1]; simp [hb'0]
      · simp only [Fin.cons_zero, Fin.cons_succ]
        rw [hb'0, if_neg (Fin.succ_ne_zero a').symm]
      · simp only [Fin.cons_zero, Fin.cons_succ]
        rw [hℓb₀, if_neg (Fin.succ_ne_zero a)]
        simp_rw [hδ' a, mul_ite, mul_one, mul_zero]
        rw [Finset.sum_ite_eq Finset.univ a, if_pos (Finset.mem_univ a), sub_self]
      · simp only [Fin.cons_succ]; rw [hδ' a a']
        by_cases h : a = a'
        · subst h; simp
        · rw [if_neg h, if_neg (fun h' => h (Fin.succ_inj.mp h'))]

section frame

variable (R : ∀ i, RegularProlongation A F (Fb i))
  (hR : Function.Injective fun i => (R i).integers)

omit [Fintype ι] in
include hR in
theorem eq_of_integers_le (i j : ι) (h : (R i).integers ≤ (R j).integers) : i = j :=
  hR (integers_eq_of_le (R i) (R j) h)

include hR in

theorem exists_lift (i : ι) (x : Fb i) :
    ∃ z : F, ∃ hz : ∀ l, z ∈ (R l).integers,
      (R i).residue ⟨z, hz i⟩ = x ∧ ∀ l, l ≠ i → (R l).residue ⟨z, hz l⟩ = 0 := by
  classical
  obtain ⟨y, hy⟩ := (R i).residue_surjective x
  let a : ι → F := fun l => if l = i then (y : F) else 0
  have ha : ∀ l, a l ∈ (R l).integers := by
    intro l; by_cases hl : l = i
    · subst hl; simp only [a, if_pos rfl]; exact y.2
    · simp only [a, if_neg hl]; exact zero_mem _
  obtain ⟨z, hz⟩ := ValuationSubring.exists_forall_mem_and_sub_mem_nonunits
    (fun l => (R l).integers) (fun l l' hle => eq_of_integers_le R hR l l' hle) a ha
  refine ⟨z, fun l => (hz l).1, ?_, ?_⟩
  · have h0 := residue_eq_zero_of_mem_nonunits (R i) (sub_mem (hz i).1 (ha i)) (hz i).2
    have e : (⟨z - a i, sub_mem (hz i).1 (ha i)⟩ : (R i).integers) = ⟨z, (hz i).1⟩ - y := by
      apply Subtype.ext; simp [a, if_pos rfl]
    rw [e, map_sub, sub_eq_zero] at h0; rw [h0, hy]
  · intro l hl
    have h0 := residue_eq_zero_of_mem_nonunits (R l) (sub_mem (hz l).1 (ha l)) (hz l).2
    have e : (⟨z - a l, sub_mem (hz l).1 (ha l)⟩ : (R l).integers) = ⟨z, (hz l).1⟩ := by
      apply Subtype.ext; simp [a, if_neg hl]
    rwa [e] at h0

variable [DecidableEq ι]
variable (f : F) (hf : ∀ i, f ∈ (R i).integers)
  (htr : ∀ i, Transcendental (ResidueField A) ((R i).residue ⟨f, hf i⟩))

theorem linearIndependent_pow_of_transcendental {K B : Type*} [Field K] [Ring B] [Algebra K B]
    {x : B} (hx : Transcendental K x) : LinearIndependent K (fun j : ℕ => x ^ j) := by
  rw [linearIndependent_iff]
  intro l hl
  have := transcendental_iff.mp hx ⟨.ofCoeff l⟩ (by
    simp only [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def,
      Polynomial.support_ofFinsupp, Polynomial.coeff_ofFinsupp, AddMonoidAlgebra.coeff_ofCoeff] at *
    rw [Finsupp.linearCombination_apply, Finsupp.sum] at hl
    simp only [Algebra.smul_def] at hl; exact hl)
  exact AddMonoidAlgebra.ofCoeff_eq_zero.mp (Polynomial.ofFinsupp_eq_zero.mp this)

include htr in

theorem linearIndependent_residue_perFrame (i : ι) {n : ℕ} (y : Fin n → Fb i)
    (hy : LinearIndependent
      (IntermediateField.adjoin (ResidueField A) ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) y) :
    LinearIndependent (ResidueField A)
      (fun p : ℕ × Fin n => ((R i).residue ⟨f, hf i⟩) ^ p.1 * y p.2) := by
  set k := ResidueField A
  set xb := (R i).residue ⟨f, hf i⟩
  have hgen : LinearIndependent k
      (fun j : ℕ => (IntermediateField.AdjoinSimple.gen k xb) ^ j) := by
    apply LinearIndependent.of_comp
      ((IntermediateField.adjoin k ({xb} : Set (Fb i))).val.toLinearMap)
    have heq : ((IntermediateField.adjoin k ({xb} : Set (Fb i))).val.toLinearMap : _ → Fb i) ∘
        (fun j : ℕ => (IntermediateField.AdjoinSimple.gen k xb) ^ j) =
        fun j : ℕ => xb ^ j := by funext j; simp
    rw [heq]
    exact linearIndependent_pow_of_transcendental (htr i)
  exact linearIndependent_smul hgen hy

variable {d : ι → ℕ} (yb : ∀ i, Fin (d i) → Fb i)
  (hyb : ∀ i, LinearIndependent
    (IntermediateField.adjoin (ResidueField A) ({(R i).residue ⟨f, hf i⟩} : Set (Fb i)))
    (yb i))
  (z : (Σ i, Fin (d i)) → F) (hzmem : ∀ τ l, z τ ∈ (R l).integers)
  (hzi : ∀ τ : Σ i, Fin (d i), (R τ.1).residue ⟨z τ, hzmem τ τ.1⟩ = yb τ.1 τ.2)
  (hzl : ∀ (τ : Σ i, Fin (d i)) l, l ≠ τ.1 → (R l).residue ⟨z τ, hzmem τ l⟩ = 0)

include hzi hzl in

theorem jointRes_jointFrame_eq_single (p : ℕ × (Σ i, Fin (d i))) :
    jointRes R (fun p : ℕ × (Σ i, Fin (d i)) => f ^ p.1 * z p.2)
        (fun p l => mul_mem (pow_mem (hf l) _) (hzmem p.2 l)) p =
      Pi.single p.2.1 (((R p.2.1).residue ⟨f, hf p.2.1⟩) ^ p.1 * yb p.2.1 p.2.2) := by
  funext l
  simp only [jointRes]
  have e : (⟨f ^ p.1 * z p.2, mul_mem (pow_mem (hf l) _) (hzmem p.2 l)⟩ : (R l).integers)
      = ⟨f, hf l⟩ ^ p.1 * ⟨z p.2, hzmem p.2 l⟩ := by apply Subtype.ext; push_cast; ring
  rw [e, map_mul, map_pow]
  by_cases hl : l = p.2.1
  · subst hl; rw [Pi.single_eq_same, hzi p.2]
  · rw [Pi.single_eq_of_ne hl, hzl p.2 l hl, mul_zero]

include htr hyb hzi hzl in

theorem linearIndependent_jointRes_jointFrame :
    LinearIndependent (ResidueField A)
      (jointRes R (fun p : ℕ × (Σ i, Fin (d i)) => f ^ p.1 * z p.2)
        (fun p l => mul_mem (pow_mem (hf l) _) (hzmem p.2 l))) := by
  classical

  set k := ResidueField A
  let e : (ℕ × (Σ i, Fin (d i))) ≃ (Σ i, ℕ × Fin (d i)) :=
    { toFun := fun p => ⟨p.2.1, p.1, p.2.2⟩
      invFun := fun σ => (σ.2.1, ⟨σ.1, σ.2.2⟩)
      left_inv := fun p => rfl
      right_inv := fun σ => rfl }
  have hper : ∀ i, LinearIndependent k
      (fun q : ℕ × Fin (d i) => ((R i).residue ⟨f, hf i⟩) ^ q.1 * yb i q.2) :=
    fun i => linearIndependent_residue_perFrame R f hf htr i (yb i) (hyb i)
  have hpi : LinearIndependent k (fun σ : Σ i, ℕ × Fin (d i) =>
      Pi.single (M := Fb) σ.1 (((R σ.1).residue ⟨f, hf σ.1⟩) ^ σ.2.1 * yb σ.1 σ.2.2)) :=
    Pi.linearIndependent_single (R := k) (Ms := Fb)
      (fun i (q : ℕ × Fin (d i)) => ((R i).residue ⟨f, hf i⟩) ^ q.1 * yb i q.2) hper
  have hfam : jointRes R (fun p : ℕ × (Σ i, Fin (d i)) => f ^ p.1 * z p.2)
      (fun p l => mul_mem (pow_mem (hf l) _) (hzmem p.2 l)) =
      (fun σ : Σ i, ℕ × Fin (d i) =>
        Pi.single (M := Fb) σ.1 (((R σ.1).residue ⟨f, hf σ.1⟩) ^ σ.2.1 * yb σ.1 σ.2.2)) ∘ e :=
    funext fun p => jointRes_jointFrame_eq_single R f hf yb z hzmem hzi hzl p
  rw [hfam]; exact hpi.comp e e.injective

end frame

section covering

variable (R : ∀ i, RegularProlongation A F (Fb i))
  (hR : Function.Injective fun i => (R i).integers) [DecidableEq ι]
  (f : F) (hf : ∀ i, f ∈ (R i).integers)
  (htr : ∀ i, Transcendental (ResidueField A) ((R i).residue ⟨f, hf i⟩))
  {d : ι → ℕ} (yb : ∀ i, Fin (d i) → Fb i)
  (hyb : ∀ i, LinearIndependent
    (IntermediateField.adjoin (ResidueField A) ({(R i).residue ⟨f, hf i⟩} : Set (Fb i)))
    (yb i))
  (z : (Σ i, Fin (d i)) → F) (hzmem : ∀ τ l, z τ ∈ (R l).integers)
  (hzi : ∀ τ : Σ i, Fin (d i), (R τ.1).residue ⟨z τ, hzmem τ τ.1⟩ = yb τ.1 τ.2)
  (hzl : ∀ (τ : Σ i, Fin (d i)) l, l ≠ τ.1 → (R l).residue ⟨z τ, hzmem τ l⟩ = 0)
  [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
  (heq : ∑ i, d i = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F)

include hR htr hyb hzi hzl in

theorem linearIndependent_adjoinField_z :
    LinearIndependent (IntermediateField.adjoin L ({f} : Set F)) z := by
  classical
  have hFrame := linearIndependent_coe_joint R
    (fun p : ℕ × (Σ i, Fin (d i)) => f ^ p.1 * z p.2)
    (fun p l => mul_mem (pow_mem (hf l) _) (hzmem p.2 l))
    (linearIndependent_jointRes_jointFrame R f hf htr yb hyb z hzmem hzi hzl)
  rw [linearIndependent_iff']
  intro t g hsum τ₀ hτ₀

  have hg : ∀ τ, ∃ P Q : Polynomial L, Polynomial.aeval f Q ≠ 0 ∧
      (g τ : F) = Polynomial.aeval f P / Polynomial.aeval f Q := fun τ => by
    obtain ⟨P, Q, hPQ⟩ := (IntermediateField.mem_adjoin_simple_iff L (g τ : F)).mp (g τ).2
    by_cases hQ : Polynomial.aeval f Q = 0
    · exact ⟨0, 1, by simp, by rw [hPQ, hQ, div_zero]; simp⟩
    · exact ⟨P, Q, hQ, hPQ⟩
  choose P Q hQne hPQ using hg
  have hQ0 : ∀ τ, Q τ ≠ 0 := fun τ h => hQne τ (h ▸ map_zero _)

  let H : (Σ i, Fin (d i)) → Polynomial L := fun τ => (∏ σ ∈ t.erase τ, Q σ) * P τ
  set D : F := ∏ σ ∈ t, Polynomial.aeval f (Q σ) with hD
  have hDne : D ≠ 0 := Finset.prod_ne_zero_iff.mpr fun σ _ => hQne σ
  have hH : ∀ τ ∈ t, D * (g τ : F) = Polynomial.aeval f (H τ) := fun τ hτ => by
    simp only [H, map_mul, map_prod, hPQ τ, hD]
    rw [← Finset.mul_prod_erase t (fun σ => Polynomial.aeval f (Q σ)) hτ]
    field_simp [hQne τ] <;> ring
  have hsum' : ∑ τ ∈ t, Polynomial.aeval f (H τ) * z τ = 0 := by
    have h0 : D * ∑ τ ∈ t, (g τ : F) * z τ = 0 := by
      rw [show ∑ τ ∈ t, (g τ : F) * z τ = (0 : F) from ?_, mul_zero]
      rw [← hsum]; exact Finset.sum_congr rfl fun τ _ => by
        rw [Algebra.smul_def]; rfl
    rw [Finset.mul_sum] at h0
    exact h0 ▸ Finset.sum_congr rfl fun τ hτ => by rw [← hH τ hτ, mul_assoc]
  set N := (t.sup fun τ => (H τ).natDegree) + 1
  have hlt : ∀ τ ∈ t, (H τ).natDegree < N := fun τ hτ =>
    Nat.lt_succ_of_le (Finset.le_sup (f := fun τ => (H τ).natDegree) hτ)
  have hzero := linearIndependent_iff'.mp hFrame (Finset.range N ×ˢ t)
    (fun q => (H q.2).coeff q.1) (by
      rw [Finset.sum_product_right, ← hsum']
      refine Finset.sum_congr rfl fun τ hτ => ?_
      rw [Polynomial.aeval_eq_sum_range' (hlt τ hτ), Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => (smul_mul_assoc _ _ _).symm)
  have hHτ₀ : H τ₀ = 0 := Polynomial.ext fun j => by
    by_cases hj : j < N
    · exact hzero (j, τ₀) (Finset.mk_mem_product (Finset.mem_range.mpr hj) hτ₀)
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (hlt τ₀ hτ₀) (not_lt.mp hj))
  have hPτ₀ : P τ₀ = 0 := (mul_eq_zero.mp hHτ₀).resolve_left
    (Finset.prod_ne_zero_iff.mpr fun σ _ => hQ0 σ)
  exact Subtype.ext (by rw [ZeroMemClass.coe_zero, hPQ τ₀, hPτ₀, map_zero, zero_div])

include hR htr hyb hzi hzl heq in

theorem exists_repr_adjoinField_z (v : F) :
    ∃ r : (Σ i, Fin (d i)) → IntermediateField.adjoin L ({f} : Set F),
      v = ∑ τ, (r τ : F) * z τ := by
  set E := IntermediateField.adjoin L ({f} : Set F)
  have hcard : Fintype.card (Σ i, Fin (d i)) = Module.finrank E F := by
    rw [Fintype.card_sigma]; simp [heq]
  let B : Module.Basis (Σ i, Fin (d i)) E F :=
    basisOfLinearIndependentOfCardEqFinrank' _
      (linearIndependent_adjoinField_z R hR f hf htr yb hyb z hzmem hzi hzl) hcard
  refine ⟨fun τ => B.repr v τ, ?_⟩
  conv_lhs => rw [← B.sum_repr v]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [coe_basisOfLinearIndependentOfCardEqFinrank', IntermediateField.smul_def, smul_eq_mul]

include htr in

theorem exists_joint_normalize_aeval (q : Polynomial L) (hq : q ≠ 0) :
    ∃ U : F, ∃ hU : ∀ i, U ∈ (R i).integers,
      (∀ i, (R i).residue ⟨U, hU i⟩ ≠ 0) ∧ ∃ c : L, c ≠ 0 ∧
        U = algebraMap L F c⁻¹ * Polynomial.aeval f q := by
  classical
  set t := Finset.range (q.natDegree + 1)
  have hi₀ : q.natDegree ∈ t := Finset.self_mem_range_succ _
  have hg : q.coeff q.natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq
  obtain ⟨j₁, hj₁t, hj₁, hcA, -⟩ := exists_normalizer A t (fun j => q.coeff j) hi₀ hg
  let a : ℕ → A := fun j => if hj : j ∈ t then ⟨(q.coeff j₁)⁻¹ * q.coeff j, hcA j hj⟩ else 0
  have ha1 : a j₁ = 1 := Subtype.ext (by simp [a, dif_pos hj₁t, inv_mul_cancel₀ hj₁])
  refine ⟨∑ j ∈ t, (a j : L) • f ^ j, fun i => sum_smul_mem R (fun j => f ^ j)
    (fun j i => pow_mem (hf i) _) t a i, ?_, q.coeff j₁, hj₁, ?_⟩
  · intro i h0
    have hpow : ∀ j (l : ι), f ^ j ∈ (R l).integers := fun j l => pow_mem (hf l) _
    have hE := linearIndependent_pow_of_transcendental (htr i)
    have hres := residue_sum_smul R (fun j => f ^ j) hpow t a i
    simp only [jointRes] at hres
    have hres' : ∀ j, (R i).residue ⟨f ^ j, hpow j i⟩ = ((R i).residue ⟨f, hf i⟩) ^ j := fun j => by
      have e : (⟨f ^ j, hpow j i⟩ : (R i).integers) = ⟨f, hf i⟩ ^ j := Subtype.ext (by push_cast; ring)
      rw [e, map_pow]
    rw [h0] at hres
    simp_rw [hres'] at hres
    have hcoeff := linearIndependent_iff'.mp hE t (fun j => IsLocalRing.residue A (a j))
      hres.symm j₁ hj₁t
    rw [ha1, map_one] at hcoeff; exact one_ne_zero hcoeff
  · rw [Polynomial.aeval_eq_sum_range, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjt : j ∈ t := hj
    simp only [Algebra.smul_def, a, dif_pos hjt, map_mul, map_inv₀]
    ring

include hR htr hyb hzi hzl heq in

theorem exists_joint_unit_mul_mem_span (V : Submodule L F) [FiniteDimensional L V] :
    ∃ U : F, ∃ hU : ∀ i, U ∈ (R i).integers,
      (∀ i, (R i).residue ⟨U, hU i⟩ ≠ 0) ∧
      ∃ T : Finset (ℕ × (Σ i, Fin (d i))),
        ∀ v ∈ V, U * v ∈
          Submodule.span L (Set.range fun p : T => f ^ p.1.1 * z p.1.2) := by
  classical
  let bV := Module.finBasis L V
  choose r hr using fun a => exists_repr_adjoinField_z R hR f hf htr yb hyb z hzmem hzi hzl heq
    ((bV a : V) : F)
  have hfrac : ∀ a τ, ∃ PQ : Polynomial L × Polynomial L, Polynomial.aeval f PQ.2 ≠ 0 ∧
      (r a τ : F) = Polynomial.aeval f PQ.1 / Polynomial.aeval f PQ.2 := by
    intro a τ
    obtain ⟨P, Q, hPQ⟩ := (IntermediateField.mem_adjoin_simple_iff L (r a τ : F)).mp (r a τ).2
    by_cases hQ : Polynomial.aeval f Q = 0
    · exact ⟨(0, 1), by simp, by rw [hPQ, hQ, div_zero]; simp⟩
    · exact ⟨(P, Q), hQ, hPQ⟩
  choose PQ hQne hPQ using hfrac
  set q : Polynomial L := ∏ p : Fin (Module.finrank L V) × (Σ i, Fin (d i)), (PQ p.1 p.2).2
  have haevalq : Polynomial.aeval f q =
      ∏ p : Fin (Module.finrank L V) × (Σ i, Fin (d i)), Polynomial.aeval f (PQ p.1 p.2).2 := by
    simp only [q, map_prod]
  have hqx : Polynomial.aeval f q ≠ 0 := by
    rw [haevalq]; exact Finset.prod_ne_zero_iff.mpr fun p _ => hQne p.1 p.2
  have hq0 : q ≠ 0 := fun h => hqx (h ▸ map_zero _)
  obtain ⟨U, hUmem, hUres, c, hc, hUq⟩ := exists_joint_normalize_aeval R f hf htr q hq0
  obtain ⟨H, hH⟩ : ∃ H : Fin (Module.finrank L V) → (Σ i, Fin (d i)) → Polynomial L,
      ∀ a τ, U * ((r a τ : F) * z τ) = Polynomial.aeval f (H a τ) * z τ := by
    refine ⟨fun a τ => Polynomial.C c⁻¹ *
      ((∏ p ∈ Finset.univ.erase (a, τ), (PQ p.1 p.2).2) * (PQ a τ).1), fun a τ => ?_⟩
    rw [hUq, hPQ a τ, ← mul_assoc]; congr 1
    simp only [map_mul, Polynomial.aeval_C, map_prod]
    rw [haevalq, ← Finset.mul_prod_erase Finset.univ
      (fun p => Polynomial.aeval f (PQ p.1 p.2).2) (Finset.mem_univ (a, τ))]
    have hQ := hQne a τ; field_simp
  obtain ⟨N, hlt⟩ : ∃ N, ∀ a τ, (H a τ).natDegree < N := by
    refine ⟨(Finset.univ.sup fun p : _ × _ => (H p.1 p.2).natDegree) + 1, fun a τ => ?_⟩
    exact Nat.lt_succ_of_le (Finset.le_sup (f := fun p : _ × _ => (H p.1 p.2).natDegree)
      (Finset.mem_univ (a, τ)))
  refine ⟨U, hUmem, hUres, Finset.range N ×ˢ Finset.univ, ?_⟩
  let S := Submodule.span L (Set.range fun p : ↥(Finset.range N ×ˢ (Finset.univ :
    Finset (Σ i, Fin (d i)))) => f ^ p.1.1 * z p.1.2)
  have hgen : ∀ j < N, ∀ τ, f ^ j * z τ ∈ S := fun j hj τ =>
    Submodule.subset_span ⟨⟨(j, τ), Finset.mk_mem_product (Finset.mem_range.mpr hj)
      (Finset.mem_univ τ)⟩, rfl⟩
  have hbasis : ∀ a, U * ((bV a : V) : F) ∈ S := by
    intro a; rw [hr a, Finset.mul_sum]
    refine S.sum_mem fun τ _ => ?_
    rw [hH a τ, Polynomial.aeval_eq_sum_range' (hlt a τ), Finset.sum_mul]
    refine S.sum_mem fun j hj => ?_
    rw [smul_mul_assoc]
    exact S.smul_mem _ (hgen j (Finset.mem_range.mp hj) τ)
  intro v hv
  have hvsum : v = ∑ a, bV.repr ⟨v, hv⟩ a • ((bV a : V) : F) := by
    have h := congrArg (fun w : V => (w : F)) (bV.sum_repr ⟨v, hv⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h; exact h.symm
  rw [hvsum, Finset.mul_sum]
  exact S.sum_mem fun a _ => by rw [mul_smul_comm]; exact S.smul_mem _ (hbasis a)

end covering

section core

variable (R : ∀ i, RegularProlongation A F (Fb i))
  {J : Type*} [Fintype J] (E : J → F) (hEmem : ∀ j i, E j ∈ (R i).integers)
  (hE : LinearIndependent (ResidueField A) (jointRes R E hEmem))

include hE in

theorem exists_jointResidue_linearIndependent (W : Submodule L F)
    (hW : W ≤ Submodule.span L (Set.range E)) {m : ℕ} (hm : Module.finrank L W = m) :
    ∃ w : Fin m → F, ∃ hwmem : ∀ a i, w a ∈ (R i).integers,
      (∀ a, w a ∈ W) ∧
      LinearIndependent (ResidueField A) (fun a => jointRes R w hwmem a) := by
  classical
  have hli := linearIndependent_coe_joint R E hEmem hE
  let ℓ : J → Submodule.span L (Set.range E) →ₗ[L] L :=
    fun j => (Finsupp.lapply j).comp hli.repr
  have hexp : ∀ s : Submodule.span L (Set.range E), (s : F) = ∑ j, ℓ j s • E j := by
    intro s
    have h := hli.linearCombination_repr s
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (fun j => zero_smul L (E j))] at h
    exact h.symm
  let W₀ : Submodule L (Submodule.span L (Set.range E)) :=
    W.comap (Submodule.span L (Set.range E)).subtype
  have hW₀ : Module.finrank L W₀ = m := by
    rw [← hm]; exact (Submodule.comapSubtypeEquivOfLe hW).finrank_eq
  have hinj : ∀ v ∈ W₀, (∀ j, ℓ j v = 0) → v = 0 := by
    intro v _ hv; apply Subtype.ext
    rw [hexp v]; exact Finset.sum_eq_zero fun j _ => by rw [hv j, zero_smul]
  obtain ⟨b, c, hcinj, hbW, hbA, hδ⟩ := exists_adapted A ℓ m W₀ hinj hW₀

  let aA : Fin m → J → A := fun a j => ⟨ℓ j (b a), hbA a j⟩
  have haA : ∀ a j, ((aA a j : A) : L) = ℓ j (b a) := fun a j => rfl
  have hwexp : ∀ a, ((b a : Submodule.span L (Set.range E)) : F) =
      ∑ j, ((aA a j : A) : L) • E j := fun a => by
    exact hexp (b a)
  refine ⟨fun a => (b a : F), fun a i => ?_, fun a => (hbW a), ?_⟩
  · show ((b a : Submodule.span L (Set.range E)) : F) ∈ (R i).integers
    rw [hwexp a]; exact sum_smul_mem R E hEmem Finset.univ (aA a) i
  ·
    rw [Fintype.linearIndependent_iff]
    intro κ hκ a'

    have hκ' : ∀ i, ∑ a, κ a • (R i).residue ⟨(b a : F), by
        rw [hwexp a]; exact sum_smul_mem R E hEmem Finset.univ (aA a) i⟩ = 0 := by
      intro i; have := congrFun hκ i
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, jointRes] at this; exact this
    have hswap : ∀ j, ∑ a, κ a • IsLocalRing.residue A (aA a j) = 0 := by
      intro j
      have hsum2 : ∑ j', (∑ a, κ a • IsLocalRing.residue A (aA a j')) • jointRes R E hEmem j' = 0 := by
        funext i
        simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply]
        rw [← hκ' i]
        simp_rw [Finset.sum_smul, smul_eq_mul, mul_smul]
        rw [Finset.sum_comm]
        simp_rw [← Finset.smul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        congr 1
        have hres := residue_sum_smul R E hEmem Finset.univ (aA a) i
        have heq : (⟨(b a : F), by rw [hwexp a]; exact sum_smul_mem R E hEmem Finset.univ (aA a) i⟩ :
            (R i).integers) =
            ⟨∑ j, ((aA a j : A) : L) • E j, sum_smul_mem R E hEmem Finset.univ (aA a) i⟩ :=
          Subtype.ext (hwexp a)
        simp only [jointRes] at hres
        rw [heq, hres]
        simp only [jointRes]
      exact linearIndependent_iff'.mp hE Finset.univ
        (fun j' => ∑ a, κ a • IsLocalRing.residue A (aA a j')) hsum2 j (Finset.mem_univ j)

    have heval := hswap (c a')
    have haδ : ∀ a, (aA a (c a') : L) = if a' = a then 1 else 0 := fun a => by
      rw [haA]; exact hδ a' a
    simp_rw [show ∀ a, IsLocalRing.residue A (aA a (c a')) =
        if a' = a then 1 else 0 from fun a => by
      have := haδ a
      by_cases h : a' = a
      · rw [if_pos h] at this ⊢
        have : aA a (c a') = 1 := Subtype.ext this
        rw [this, map_one]
      · rw [if_neg h] at this ⊢
        have : aA a (c a') = 0 := Subtype.ext this
        rw [this, map_zero]] at heval
    simp only [smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true] at heval
    simpa [smul_eq_mul, mul_one] using heval

end core

end W10XK3ER2
p2m_reactivate "P2MW.S_AlgebraicCurve_RegularProlongation_finrank_span_pi_residue_eq_finrank_of_sum_finrank_eq.W10XK3ER2"

open W10XK3ER2

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
    Module.finrank (IsLocalRing.ResidueField A)
        (Submodule.span (IsLocalRing.ResidueField A)
          {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
            u ∈ V ∧ ∀ i, (R i).residue ⟨u, hu i⟩ = h i}) =
      Module.finrank L V := by
  classical
  set k := ResidueField A
  haveI : DecidableEq ι := Classical.decEq ι

  have hfin := (RegularProlongation.sum_finrank_adjoin_residue_le A Fb R hR f hf htr).1
  let d : ι → ℕ := fun i => Module.finrank
    (IntermediateField.adjoin k ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)
  let yb : ∀ i, Fin (d i) → Fb i := fun i => (Module.finBasis _ (Fb i) : _)
  have hyb : ∀ i, LinearIndependent _ (yb i) := fun i => (Module.finBasis _ (Fb i)).linearIndependent
  choose z hzmem hzi hzl using fun τ : Σ i, Fin (d i) => exists_lift R hR τ.1 (yb τ.1 τ.2)
  have heq' : ∑ i, d i = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F := heq

  have hrank_le : Module.rank k (Submodule.span k
      {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
        u ∈ V ∧ ∀ i, (R i).residue ⟨u, hu i⟩ = h i}) ≤ Module.finrank L V := by

    have hSclosed : ∀ h ∈ Submodule.span k
        {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
          u ∈ V ∧ ∀ i, (R i).residue ⟨u, hu i⟩ = h i},
        ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
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
            rw [Algebra.smul_def]; exact mul_mem ((R i).algebraMap_mem_iff _ |>.mpr ĉ.2) (hux i)
          have e : (⟨(ĉ : L) • ux, hmem'⟩ : (R i).integers) = constHom (R i) ĉ * ⟨ux, hux i⟩ := by
            refine Subtype.ext ?_; simp only [MulMemClass.coe_mul, coe_constHom]
            exact Algebra.smul_def (ĉ : L) ux
          rw [show (⟨(ĉ : L) • ux, _⟩ : (R i).integers) = ⟨(ĉ : L) • ux, hmem'⟩ from rfl,
            e, map_mul, residue_constHom, hĉ, huxR i, Pi.smul_apply]
          exact (Algebra.smul_def c (x i)).symm
    apply rank_le
    intro s hs

    choose u hu huV huRes using fun a : s => hSclosed a.1.1 a.1.2
    have hli := linearIndependent_coe_joint R (fun a : s => u a) (fun a => hu a)
      (by
        have heq : ∀ a i, jointRes R (fun a : s => u a) (fun a => hu a) a i = (a.1 : ∀ i, Fb i) i :=
          fun a i => huRes a i
        have heq' : jointRes R (fun a : s => u a) (fun a => hu a) =
            (Submodule.span k _).subtype ∘ (fun a : s => a.1) := funext fun a => funext fun i => heq a i
        rw [heq']
        exact hs.map' (Submodule.span k _).subtype (Submodule.ker_subtype _))
    have hmemV : ∀ a : s, u a ∈ V := huV
    have : LinearIndependent L (fun a : s => (⟨u a, hmemV a⟩ : V)) :=
      LinearIndependent.of_comp V.subtype hli
    simpa only [Fintype.card_coe] using this.fintype_card_le_finrank
  haveI : Module.Finite k (Submodule.span k
      {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
        u ∈ V ∧ ∀ i, (R i).residue ⟨u, hu i⟩ = h i}) := by
    rw [← Module.rank_lt_aleph0_iff]
    exact lt_of_le_of_lt hrank_le (Cardinal.natCast_lt_aleph0)
  apply le_antisymm (Module.finrank_le_of_rank_le hrank_le)

  obtain ⟨U, hUmem, hUres, T, hT⟩ :=
    exists_joint_unit_mul_mem_span R hR f hf htr yb hyb z hzmem hzi hzl heq' V
  have hUne : U ≠ 0 := by
    intro h0
    rcases isEmpty_or_nonempty ι with hι | ⟨⟨i⟩⟩
    ·
      simp only [Finset.univ_eq_empty, Finset.sum_empty] at heq
      exact absurd heq.symm Module.finrank_pos.ne'
    · exact hUres i (by rw [show (⟨U, hUmem i⟩ : (R i).integers) = 0 from Subtype.ext h0, map_zero])
  let μ : F →ₗ[L] F := LinearMap.mulLeft L U
  have hμinj : Function.Injective μ := mul_right_injective₀ hUne
  have hWfin : Module.finrank L (V.map μ) = Module.finrank L V :=
    (Submodule.equivMapOfInjective μ hμinj V).finrank_eq.symm
  let ET : T → F := fun p => f ^ p.1.1 * z p.1.2
  have hETmem : ∀ (p : T) i, ET p ∈ (R i).integers :=
    fun p i => mul_mem (pow_mem (hf i) _) (hzmem p.1.2 i)
  have hET : LinearIndependent k (jointRes R ET hETmem) :=
    (linearIndependent_jointRes_jointFrame R f hf htr yb hyb z hzmem hzi hzl).comp
      (fun p : T => p.1) Subtype.val_injective
  have hWle : V.map μ ≤ Submodule.span L (Set.range ET) := by
    rintro _ ⟨v, hv, rfl⟩; exact hT v hv
  obtain ⟨w, hwmem, hwW, hwLI⟩ :=
    exists_jointResidue_linearIndependent R ET hETmem hET (V.map μ) hWle hWfin

  have hUunit : ∀ i, IsUnit (⟨U, hUmem i⟩ : (R i).integers) :=
    fun i => (R i).isUnit_of_residue_ne_zero (hUres i)
  have hUinv_mem : ∀ i, U⁻¹ ∈ (R i).integers := fun i => by
    have hv : (R i).integers.valuation U = 1 :=
      ((R i).integers.valuation_eq_one_iff ⟨U, hUmem i⟩).mp (hUunit i)
    rw [← (R i).integers.valuation_le_one_iff, map_inv₀, hv, inv_one]
  have hw'mem : ∀ a i, U⁻¹ * w a ∈ (R i).integers := fun a i =>
    mul_mem (hUinv_mem i) (hwmem a i)
  have hw'V : ∀ a, U⁻¹ * w a ∈ V := by
    intro a; obtain ⟨v, hv, hμv⟩ := hwW a
    have : U⁻¹ * w a = v := by
      rw [← hμv]; simp only [μ, LinearMap.mulLeft_apply]
      rw [← mul_assoc, inv_mul_cancel₀ hUne, one_mul]
    rw [this]; exact hv
  have hw'LI : LinearIndependent k (fun a => jointRes R (fun a => U⁻¹ * w a) hw'mem a) := by

    rw [Fintype.linearIndependent_iff]
    intro κ hκ a'
    refine Fintype.linearIndependent_iff.mp hwLI κ ?_ a'
    funext i
    have h := congrFun hκ i
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, jointRes] at h ⊢
    have hfact : ∀ a, (R i).residue ⟨U, hUmem i⟩ * (R i).residue ⟨U⁻¹ * w a, hw'mem a i⟩ =
        (R i).residue ⟨w a, hwmem a i⟩ := fun a => by
      rw [← map_mul]; congr 1
      exact Subtype.ext (by push_cast; rw [← mul_assoc, mul_inv_cancel₀ hUne, one_mul])
    calc ∑ a, κ a • (R i).residue ⟨w a, hwmem a i⟩
        = ∑ a, κ a • ((R i).residue ⟨U, hUmem i⟩ * (R i).residue ⟨U⁻¹ * w a, hw'mem a i⟩) := by
          simp_rw [← hfact]
      _ = (R i).residue ⟨U, hUmem i⟩ * ∑ a, κ a • (R i).residue ⟨U⁻¹ * w a, hw'mem a i⟩ := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun a _ => (mul_smul_comm _ _ _).symm
      _ = 0 := by rw [h, mul_zero]
  have hmemS : ∀ a, jointRes R (fun a => U⁻¹ * w a) hw'mem a ∈ Submodule.span k
      {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
        u ∈ V ∧ ∀ i, (R i).residue ⟨u, hu i⟩ = h i} :=
    fun a => Submodule.subset_span ⟨U⁻¹ * w a, hw'mem a, hw'V a, fun i => rfl⟩
  have hind2 : LinearIndependent k (fun a => (⟨_, hmemS a⟩ : Submodule.span k _)) :=
    LinearIndependent.of_comp (Submodule.span k _).subtype hw'LI
  simpa using hind2.fintype_card_le_finrank

end
end S_AlgebraicCurve_RegularProlongation_finrank_span_pi_residue_eq_finrank_of_sum_finrank_eq
end P2MW
export P2MW.S_AlgebraicCurve_RegularProlongation_finrank_span_pi_residue_eq_finrank_of_sum_finrank_eq (solution)
