-- Prove2me | solution 1 for AlgebraicCurve.RegularProlongation.exists_regularProlongation_mem_integers_iff_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/2cc2e16d-5c65-50fb-b990-096119653e5f

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RegularProlongation_exists_regularProlongation_mem_integers_iff_of_le

open Polynomial AlgebraicCurve IsLocalRing

namespace CoarsenSol

universe u

section Basic

variable {L : Type*} [Field L] {A A' : ValuationSubring L} (hA : A ≤ A')
variable {F : Type u} [Field F] [Algebra L F]
variable {Fb : Type*} [Field Fb] [Algebra (ResidueField A) Fb]
variable (R : RegularProlongation A F Fb)

theorem algebraMap_mem {a : L} (ha : a ∈ A) : algebraMap L F a ∈ R.integers :=
  (R.algebraMap_mem_iff a).mpr ha

theorem smul_mem_of_mem {a : L} (ha : a ∈ A) {x : F} (hx : x ∈ R.integers) : a • x ∈ R.integers := by
  rw [Algebra.smul_def]; exact mul_mem (algebraMap_mem R ha) hx

def cst : A →+* R.integers :=
  ((algebraMap L F).comp A.subtype).codRestrict R.integers fun a => algebraMap_mem R a.2

@[scoped simp] theorem coe_cst (a : A) : ((cst R a : R.integers) : F) = algebraMap L F a := rfl

theorem residue_cst (a : A) : R.residue (cst R a) = algebraMap (ResidueField A) Fb (residue A a) :=
  R.residue_algebraMap a

theorem residue_eq_zero_iff_mem (x : R.integers) : R.residue x = 0 ↔ x ∈ maximalIdeal R.integers := by
  rw [← R.ker_residue, RingHom.mem_ker]

include hA in
theorem mem_A'_of_mem {a : L} (ha : a ∈ A) : a ∈ A' := hA ha

theorem mem_of_valuation_eq_one {a : L} (ha : A'.valuation a = 1) : a ∈ A' :=
  (A'.valuation_le_one_iff a).mp ha.le

theorem ne_zero_of_valuation_eq_one {a : L} (ha : A'.valuation a = 1) : a ≠ 0 := by
  rintro rfl; rw [map_zero] at ha; exact zero_ne_one ha

theorem valuation_inv_eq_one {a : L} (ha : A'.valuation a = 1) : A'.valuation a⁻¹ = 1 := by
  rw [map_inv₀, ha, inv_one]

include hA in

theorem mem_A_of_valuation_lt_one {m : L} (hm : A'.valuation m < 1) : m ∈ A := by
  have hmn : m ∈ A'.nonunits := (A'.mem_nonunits_iff).mpr hm
  have : m ∈ A.nonunits := (ValuationSubring.nonunits_le_nonunits.mpr hA) hmn
  exact A.nonunits_subset this

include hA in
theorem A_valuation_lt_one_of_valuation_lt_one {m : L} (hm : A'.valuation m < 1) : A.valuation m < 1 := by
  have hmn : m ∈ A'.nonunits := (A'.mem_nonunits_iff).mpr hm
  exact (A.mem_nonunits_iff).mp ((ValuationSubring.nonunits_le_nonunits.mpr hA) hmn)

def carrier' (A' : ValuationSubring L) (R : RegularProlongation A F Fb) : Set F :=
  {x | ∃ a : L, A'.valuation a = 1 ∧ a • x ∈ R.integers}

theorem mem_carrier'_of_mem {x : F} (hx : x ∈ R.integers) : x ∈ carrier' A' R :=
  ⟨1, by rw [map_one], by rw [one_smul]; exact hx⟩

theorem exists_common {x y : F} (hx : x ∈ carrier' A' R) (hy : y ∈ carrier' A' R) :
    ∃ c : L, A'.valuation c = 1 ∧ c • x ∈ R.integers ∧ c • y ∈ R.integers := by
  obtain ⟨a, ha, hax⟩ := hx
  obtain ⟨b, hb, hby⟩ := hy
  have ha0 := ne_zero_of_valuation_eq_one ha
  have hb0 := ne_zero_of_valuation_eq_one hb
  rcases le_total (A.valuation b) (A.valuation a) with hle | hle
  ·
    have hba : b / a ∈ A := by
      rw [← A.valuation_le_one_iff, map_div₀]; exact div_le_one_of_le₀ hle zero_le'
    refine ⟨b, hb, ?_, hby⟩
    have : b • x = (b / a) • (a • x) := by
      rw [smul_smul, div_mul_cancel₀ b ha0]
    rw [this]; exact smul_mem_of_mem R hba hax
  · have hab : a / b ∈ A := by
      rw [← A.valuation_le_one_iff, map_div₀]; exact div_le_one_of_le₀ hle zero_le'
    refine ⟨a, ha, hax, ?_⟩
    have : a • y = (a / b) • (b • y) := by
      rw [smul_smul, div_mul_cancel₀ a hb0]
    rw [this]; exact smul_mem_of_mem R hab hby

include hA in

def O' : ValuationSubring F where
  carrier := carrier' A' R
  mul_mem' := by
    rintro x y ⟨a, ha, hax⟩ ⟨b, hb, hby⟩
    refine ⟨a * b, by rw [map_mul, ha, hb, mul_one], ?_⟩
    rw [show (a * b) • (x * y) = (a • x) * (b • y) by
      rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, map_mul]; ring]
    exact mul_mem hax hby
  one_mem' := mem_carrier'_of_mem R (one_mem _)
  add_mem' := by
    intro x y hx hy
    obtain ⟨c, hc, hcx, hcy⟩ := exists_common R hx hy
    exact ⟨c, hc, by rw [smul_add]; exact add_mem hcx hcy⟩
  zero_mem' := mem_carrier'_of_mem R (zero_mem _)
  neg_mem' := by
    rintro x ⟨a, ha, hax⟩
    exact ⟨a, ha, by rw [smul_neg]; exact neg_mem hax⟩
  mem_or_inv_mem' := by
    intro x
    by_cases hx : x ∈ carrier' A' R
    · exact Or.inl hx
    right
    have hx0 : x ≠ 0 := by rintro rfl; exact hx (mem_carrier'_of_mem R (zero_mem _))
    obtain ⟨c, hcx, hres⟩ := R.exists_smul_mem x hx0
    have hc0 : c ≠ 0 := R.smul_const_ne_zero hcx hres
    have hunit : IsUnit (⟨c • x, hcx⟩ : R.integers) := R.isUnit_of_residue_ne_zero hres

    have hc1 : A'.valuation c ≠ 1 := fun h => hx ⟨c, h, hcx⟩
    rcases lt_or_gt_of_ne hc1 with hlt | hgt
    ·
      have hcA : c ∈ A := mem_A_of_valuation_lt_one hA hlt
      refine ⟨1, by rw [map_one], ?_⟩
      rw [one_smul]
      have hv1 : R.integers.valuation (c • x) = 1 :=
        (R.integers.valuation_eq_one_iff ⟨_, hcx⟩).mp hunit
      have hmem : (c • x)⁻¹ ∈ R.integers :=
        R.integers.mem_of_valuation_le_one _ (by rw [map_inv₀, hv1, inv_one])
      have : x⁻¹ = algebraMap L F c * (c • x)⁻¹ := by
        rw [Algebra.smul_def, mul_inv, ← mul_assoc, mul_inv_cancel₀ ((_root_.map_ne_zero _).mpr hc0),
          one_mul]
      rw [this]
      exact mul_mem (algebraMap_mem R hcA) hmem
    ·
      exfalso
      have hlt : A'.valuation c⁻¹ < 1 := by
        rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hgt
      have hcA : c⁻¹ ∈ A := mem_A_of_valuation_lt_one hA hlt
      apply hx
      refine mem_carrier'_of_mem R ?_
      have : x = c⁻¹ • (c • x) := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
      rw [this]
      exact smul_mem_of_mem R hcA hcx

theorem mem_O'_iff {x : F} : x ∈ O' hA R ↔ ∃ a : L, A'.valuation a = 1 ∧ a • x ∈ R.integers :=
  Iff.rfl

theorem le_O' : R.integers ≤ O' hA R := fun _ hx => mem_carrier'_of_mem R hx

theorem algebraMap_mem_O'_iff (x : L) : algebraMap L F x ∈ O' hA R ↔ x ∈ A' := by
  constructor
  · rintro ⟨a, ha, hax⟩
    rw [Algebra.smul_def, ← map_mul, R.algebraMap_mem_iff] at hax
    have ha0 := ne_zero_of_valuation_eq_one ha
    have : x = a⁻¹ * (a * x) := by rw [← mul_assoc, inv_mul_cancel₀ ha0, one_mul]
    rw [this]
    exact mul_mem (mem_of_valuation_eq_one (valuation_inv_eq_one ha)) (hA hax)
  · intro hx
    by_cases hxA : x ∈ A
    · exact le_O' hA R (algebraMap_mem R hxA)
    ·
      have hx1 : A'.valuation x = 1 := by
        rcases (A'.valuation_le_one_iff x).mpr hx |>.lt_or_eq with h | h
        · exact absurd (mem_A_of_valuation_lt_one hA h) hxA
        · exact h
      have hx0 := ne_zero_of_valuation_eq_one hx1
      refine ⟨x⁻¹, valuation_inv_eq_one hx1, ?_⟩
      rw [Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hx0, map_one]
      exact one_mem _

theorem mem_maximalIdeal_of_mem {x : F} (hx : x ∈ R.integers)
    (hm : (⟨x, le_O' hA R hx⟩ : O' hA R) ∈ maximalIdeal (O' hA R)) :
    (⟨x, hx⟩ : R.integers) ∈ maximalIdeal R.integers := by
  have h1 : x ∈ (O' hA R).nonunits := (ValuationSubring.coe_mem_nonunits_iff).mpr hm
  have h2 : x ∈ R.integers.nonunits :=
    (ValuationSubring.nonunits_le_nonunits.mpr (le_O' hA R)) h1
  exact (ValuationSubring.coe_mem_nonunits_iff).mp h2

theorem isUnit_O'_of_isUnit {x : F} (hx : x ∈ R.integers) (hu : IsUnit (⟨x, hx⟩ : R.integers)) :
    IsUnit (⟨x, le_O' hA R hx⟩ : O' hA R) := by
  by_contra h
  exact (IsLocalRing.mem_maximalIdeal _).mp
    (mem_maximalIdeal_of_mem hA R hx ((IsLocalRing.mem_maximalIdeal _).mpr h)) hu

def cst' : A' →+* O' hA R :=
  ((algebraMap L F).comp A'.subtype).codRestrict (O' hA R) fun a =>
    (algebraMap_mem_O'_iff hA R a).mpr a.2

@[scoped simp] theorem coe_cst' (a : A') : ((cst' hA R a : O' hA R) : F) = algebraMap L F a := rfl

scoped instance isLocalHom_cst' : IsLocalHom (cst' hA R) := by
  refine ⟨fun a ha => ?_⟩
  have hne : (a : L) ≠ 0 := by
    rintro h0
    apply ha.ne_zero
    exact Subtype.ext (by rw [coe_cst', h0, map_zero]; rfl)
  obtain ⟨u, hu⟩ := ha
  have hinv : (algebraMap L F a)⁻¹ ∈ O' hA R := by
    have h' : (((u⁻¹ : (O' hA R)ˣ) : O' hA R) : F) = (algebraMap L F a)⁻¹ := by
      rw [← coe_cst' hA R a, ← hu]
      exact map_units_inv (O' hA R).subtype u
    rw [← h']; exact SetLike.coe_mem _
  rw [← map_inv₀, algebraMap_mem_O'_iff] at hinv
  exact ⟨⟨a, ⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ hne), Subtype.ext (inv_mul_cancel₀ hne)⟩, rfl⟩

noncomputable scoped instance algebraResidue :
    Algebra (ResidueField A') (ResidueField (O' hA R)) :=
  (ResidueField.map (cst' hA R)).toAlgebra

theorem algebraMap_residue (a : A') :
    algebraMap (ResidueField A') (ResidueField (O' hA R)) (IsLocalRing.residue _ a) =
      IsLocalRing.residue _ (cst' hA R a) := rfl

noncomputable def R' : RegularProlongation A' F (ResidueField (O' hA R)) where
  integers := O' hA R
  residue := IsLocalRing.residue (O' hA R)
  algebraMap_mem_iff := algebraMap_mem_O'_iff hA R
  residue_surjective := IsLocalRing.residue_surjective
  ker_residue := IsLocalRing.ker_residue
  residue_algebraMap a := (algebraMap_residue hA R a).symm
  exists_smul_mem g hg := by
    obtain ⟨c, hcg, hres⟩ := R.exists_smul_mem g hg
    refine ⟨c, le_O' hA R hcg, ?_⟩
    rw [Ne, IsLocalRing.residue_eq_zero_iff]
    intro hm
    exact hres ((residue_eq_zero_iff_mem R _).mpr (mem_maximalIdeal_of_mem hA R hcg hm))

@[scoped simp] theorem R'_integers : (R' hA R).integers = O' hA R := rfl

theorem R'_residue : (R' hA R).residue = IsLocalRing.residue (O' hA R) := rfl

end Basic

section Poly

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type u} [Field F] [Algebra L F]
variable {Fb : Type*} [Field Fb] [Algebra (ResidueField A) Fb]

theorem residue_ne_zero_iff_isUnit (R : RegularProlongation A F Fb) (x : R.integers) :
    R.residue x ≠ 0 ↔ IsUnit x :=
  ⟨R.isUnit_of_residue_ne_zero, R.residue_ne_zero_of_isUnit⟩

noncomputable def evalO (R : RegularProlongation A F Fb) (x : R.integers) (r : A[X]) : R.integers :=
  r.eval₂ (cst R) x

theorem coe_evalO (R : RegularProlongation A F Fb) (x : R.integers) (r : A[X]) :
    ((evalO R x r : R.integers) : F) = aeval (x : F) (r.map A.subtype) := by
  unfold evalO
  rw [show ((r.eval₂ (cst R) x : R.integers) : F) = R.integers.subtype (r.eval₂ (cst R) x)
    from rfl, hom_eval₂, aeval_def, eval₂_map]
  rfl

theorem residue_evalO (R : RegularProlongation A F Fb) (x : R.integers) (r : A[X]) :
    R.residue (evalO R x r) = aeval (R.residue x) (r.map (IsLocalRing.residue A)) := by
  unfold evalO
  rw [hom_eval₂, aeval_def, eval₂_map]
  congr 1
  ext a
  exact residue_cst R a

theorem map_residue_eq_zero_iff (r : A[X]) :
    r.map (IsLocalRing.residue A) = 0 ↔ ∀ j, A.valuation ((r.coeff j : A) : L) < 1 := by
  rw [Polynomial.ext_iff]
  refine forall_congr' fun j => ?_
  rw [coeff_map, coeff_zero, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]

variable (A) in
theorem exists_map_subtype_eq {p : L[X]} (hp : ∀ j, p.coeff j ∈ A) :
    ∃ r : A[X], r.map A.subtype = p := by
  have h : p ∈ lifts A.subtype := by
    rw [lifts_iff_coeff_lifts]
    intro j
    exact ⟨⟨p.coeff j, hp j⟩, rfl⟩
  exact (mem_lifts _).mp h

theorem isUnit_of_aeval_eq (R : RegularProlongation A F Fb) (x : R.integers)
    (hx : Transcendental (ResidueField A) (R.residue x)) (q : L[X])
    (hq : ∀ j, q.coeff j ∈ A) (hq1 : ∃ d, A.valuation (q.coeff d) = 1) :
    ∃ h : aeval (x : F) q ∈ R.integers, IsUnit (⟨aeval (x : F) q, h⟩ : R.integers) := by
  obtain ⟨qA, rfl⟩ := exists_map_subtype_eq A hq
  refine ⟨by rw [← coe_evalO]; exact (evalO R x qA).2, ?_⟩
  rw [show (⟨aeval (x : F) (qA.map A.subtype), _⟩ : R.integers) = evalO R x qA from
    Subtype.ext (coe_evalO R x qA).symm]
  rw [← residue_ne_zero_iff_isUnit, residue_evalO]
  intro h0
  obtain ⟨d, hd⟩ := hq1
  rw [coeff_map] at hd
  have hne : qA.map (IsLocalRing.residue A) ≠ 0 := by
    intro h
    have := (map_residue_eq_zero_iff qA).mp h d
    rw [show A.subtype (qA.coeff d) = ((qA.coeff d : A) : L) from rfl] at hd
    rw [hd] at this
    exact lt_irrefl _ this
  exact hne (transcendental_iff.mp hx _ h0)

theorem exists_normalize (P : L[X]) (hP : P ≠ 0) :
    ∃ d, P.coeff d ≠ 0 ∧ (∀ j, A.valuation (P.coeff j) ≤ A.valuation (P.coeff d)) ∧
      (∀ j, (C (P.coeff d)⁻¹ * P).coeff j ∈ A) ∧ A.valuation ((C (P.coeff d)⁻¹ * P).coeff d) = 1 := by
  classical
  set t := Finset.range (P.natDegree + 1) with ht
  have hmem : P.natDegree ∈ t := Finset.self_mem_range_succ _
  obtain ⟨d, hd, hmax⟩ := t.exists_max_image (fun j => A.valuation (P.coeff j)) ⟨_, hmem⟩
  have hmax' : ∀ j, A.valuation (P.coeff j) ≤ A.valuation (P.coeff d) := by
    intro j
    by_cases hj : j < P.natDegree + 1
    · exact hmax j (Finset.mem_range.mpr hj)
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), map_zero]
      exact zero_le'
  set c := P.coeff d with hc
  have hc0 : c ≠ 0 := by
    intro h0
    have h := hmax _ hmem
    rw [h0, map_zero, le_zero_iff, map_eq_zero, Polynomial.coeff_natDegree,
      Polynomial.leadingCoeff_eq_zero] at h
    exact hP h
  have hv0 : A.valuation c ≠ 0 := by rw [ne_eq, map_eq_zero]; exact hc0
  refine ⟨d, hc0, hmax', fun j => ?_, ?_⟩
  · rw [coeff_C_mul, ← A.valuation_le_one_iff, map_mul, map_inv₀]
    calc (A.valuation c)⁻¹ * A.valuation (P.coeff j)
        ≤ (A.valuation c)⁻¹ * A.valuation c := by gcongr; exact hmax' j
      _ = 1 := inv_mul_cancel₀ hv0
  · rw [coeff_C_mul, ← hc, inv_mul_cancel₀ hc0, map_one]

end Poly

section Transc

variable {L : Type*} [Field L] {A A' : ValuationSubring L} (hA : A ≤ A')
variable {F : Type u} [Field F] [Algebra L F]
variable {Fb : Type*} [Field Fb] [Algebra (ResidueField A) Fb]
variable (R : RegularProlongation A F Fb)

include hA in
theorem A'_valuation_le_of_le {x y : L} (h : A.valuation x ≤ A.valuation y) :
    A'.valuation x ≤ A'.valuation y := by
  have := ValuationSubring.monotone_mapOfLE A A' hA h
  rwa [ValuationSubring.mapOfLE_valuation_apply, ValuationSubring.mapOfLE_valuation_apply] at this

theorem transcendental_residue' (f : F) (hf : f ∈ R.integers)
    (htr : Transcendental (ResidueField A) (R.residue ⟨f, hf⟩)) :
    Transcendental (ResidueField A')
      (IsLocalRing.residue (O' hA R) ⟨f, le_O' hA R hf⟩) := by
  classical
  intro halg
  obtain ⟨p, hp0, hp⟩ := halg

  obtain ⟨P, hP⟩ := Polynomial.map_surjective (IsLocalRing.residue A') IsLocalRing.residue_surjective p
  have hP0 : P ≠ 0 := by rintro rfl; rw [Polynomial.map_zero] at hP; exact hp0 hP.symm
  set P₁ : L[X] := P.map A'.subtype with hP₁
  have hP₁0 : P₁ ≠ 0 := (Polynomial.map_ne_zero_iff A'.subtype_injective).mpr hP0
  have hP₁coeff : ∀ j, P₁.coeff j = ((P.coeff j : A') : L) := fun j => by rw [hP₁, coeff_map]; rfl

  set fO : O' hA R := ⟨f, le_O' hA R hf⟩ with hfO
  set y : O' hA R := evalO (R' hA R) fO P with hy_def
  have hy : y ∈ maximalIdeal (O' hA R) := by
    rw [← IsLocalRing.residue_eq_zero_iff]
    have := residue_evalO (R' hA R) fO P
    rw [R'_residue] at this
    rw [hy_def]
    refine this.trans ?_
    rw [hP]
    convert hp using 1
    rfl
  have hcoe_y : (y : F) = aeval f P₁ := by rw [hy_def, coe_evalO]

  obtain ⟨d, hc0, hmax, hQ, hQd⟩ := exists_normalize (A := A) P₁ hP₁0
  set c := P₁.coeff d with hc

  have hcA' : c ∈ A' := by rw [hc, hP₁coeff]; exact SetLike.coe_mem _
  have hc1 : A'.valuation c = 1 := by
    rcases ((A'.valuation_le_one_iff c).mpr hcA').lt_or_eq with hlt | h
    · exfalso
      apply hp0
      rw [← hP, Polynomial.ext_iff]
      intro j
      rw [coeff_map, coeff_zero, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
      calc A'.valuation ((P.coeff j : A') : L) = A'.valuation (P₁.coeff j) := by rw [hP₁coeff]
        _ ≤ A'.valuation c := A'_valuation_le_of_le hA (hmax j)
        _ < 1 := hlt
    · exact h

  obtain ⟨hQmem, hQunit⟩ := isUnit_of_aeval_eq R ⟨f, hf⟩ htr (C c⁻¹ * P₁) hQ ⟨d, hQd⟩

  have hval : aeval f (C c⁻¹ * P₁) = algebraMap L F c⁻¹ * (y : F) := by
    rw [map_mul, aeval_C, hcoe_y]
  have hmemO' : (⟨aeval f (C c⁻¹ * P₁), le_O' hA R hQmem⟩ : O' hA R) ∈ maximalIdeal (O' hA R) := by
    have : (⟨aeval f (C c⁻¹ * P₁), le_O' hA R hQmem⟩ : O' hA R) =
        cst' hA R ⟨c⁻¹, mem_of_valuation_eq_one (valuation_inv_eq_one hc1)⟩ * y := by
      apply Subtype.ext
      show aeval f (C c⁻¹ * P₁) = _
      rw [hval]; rfl
    rw [this]
    exact Ideal.mul_mem_left _ _ hy
  have hmemO : (⟨aeval f (C c⁻¹ * P₁), hQmem⟩ : R.integers) ∈ maximalIdeal R.integers :=
    mem_maximalIdeal_of_mem hA R hQmem hmemO'
  exact (IsLocalRing.mem_maximalIdeal _).mp hmemO hQunit

end Transc

end CoarsenSol
p2m_reactivate "P2MW.S_AlgebraicCurve_RegularProlongation_exists_regularProlongation_mem_integers_iff_of_le.CoarsenSol"

open CoarsenSol in
theorem solution.{u}
    {L : Type*} [Field L] (A A' : ValuationSubring L) (hA : A ≤ A')
    {F : Type u} [Field F] [Algebra L F]
    {Fb : Type*} [Field Fb] [Algebra (IsLocalRing.ResidueField A) Fb]
    (R : RegularProlongation A F Fb)
    (f : F) (hf : f ∈ R.integers)
    (htr : Transcendental (IsLocalRing.ResidueField A) (R.residue ⟨f, hf⟩)) :
    ∃ (Fb' : Type u) (_ : Field Fb') (_ : Algebra (IsLocalRing.ResidueField A') Fb')
      (R' : RegularProlongation A' F Fb') (hle : R.integers ≤ R'.integers),
      (∀ x : F, x ∈ R'.integers ↔ ∃ a : L, A'.valuation a = 1 ∧ a • x ∈ R.integers) ∧
      Transcendental (IsLocalRing.ResidueField A') (R'.residue ⟨f, hle hf⟩) :=
  ⟨ResidueField (O' hA R), inferInstance, inferInstance, R' hA R, le_O' hA R,
    fun _ => mem_O'_iff hA R, transcendental_residue' hA R f hf htr⟩

end S_AlgebraicCurve_RegularProlongation_exists_regularProlongation_mem_integers_iff_of_le
end P2MW
export P2MW.S_AlgebraicCurve_RegularProlongation_exists_regularProlongation_mem_integers_iff_of_le (solution)
