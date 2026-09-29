-- Prove2me | solution 1 for AlgebraicCurve.RegularProlongation.exists_regularProlongation_intermediateField_sum_finrank_adjoin_residue_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/2bec61e8-9279-5e72-94d5-9e8814a74393

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Theorems.Thm_ValuationSubring_exists_pow_valuation_eq_valuation_algebraMap_of_isAlgebraic
import Theorems.Thm_AlgebraicCurve_RegularProlongation_sum_finrank_adjoin_residue_le
import Theorems.Thm_AlgebraicCurve_RegularProlongation_transcendental_of_residue_transcendental
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RegularProlongation_exists_regularProlongation_intermediateField_sum_finrank_adjoin_residue_eq

open Polynomial AlgebraicCurve IsLocalRing

namespace DescSol

universe u

section Infra

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
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

theorem residue_ne_zero_iff_isUnit (R : RegularProlongation A F Fbar) (x : R.integers) :
    R.residue x ≠ 0 ↔ IsUnit x :=
  ⟨R.isUnit_of_residue_ne_zero, R.residue_ne_zero_of_isUnit⟩

scoped instance isLocalHom_residue (R : RegularProlongation A F Fbar) : IsLocalHom R.residue :=
  ⟨fun _ hu => R.isUnit_of_residue_ne_zero hu.ne_zero⟩

noncomputable def evalO (R : RegularProlongation A F Fbar) (x : R.integers) (r : A[X]) :
    R.integers :=
  r.eval₂ (constHom R) x

theorem coe_evalO (R : RegularProlongation A F Fbar) (x : R.integers) (r : A[X]) :
    ((evalO R x r : R.integers) : F) = aeval (x : F) (r.map A.subtype) := by
  unfold evalO
  rw [show ((r.eval₂ (constHom R) x : R.integers) : F) = R.integers.subtype (r.eval₂ (constHom R) x)
    from rfl, hom_eval₂, aeval_def, eval₂_map]
  rfl

theorem residue_evalO (R : RegularProlongation A F Fbar) (x : R.integers) (r : A[X]) :
    R.residue (evalO R x r) = aeval (R.residue x) (r.map (IsLocalRing.residue A)) := by
  unfold evalO
  rw [hom_eval₂, aeval_def, eval₂_map]
  congr 1
  ext a
  exact residue_constHom R a

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

theorem isUnit_of_aeval_eq (R : RegularProlongation A F Fbar) (x : R.integers)
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

end Infra

section Restrict

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type u} [Field F] [Algebra L F]
variable {ι : Type*} {Fb : ι → Type*} [∀ i, Field (Fb i)]
  [∀ i, Algebra (ResidueField A) (Fb i)]
variable (R : ∀ i, RegularProlongation A F (Fb i))
variable {L₁ : Type*} [Field L₁] [Algebra L₁ L] [Algebra L₁ F] [IsScalarTower L₁ L F]
variable (F₁ : IntermediateField L₁ F)

def O₁ (i : ι) : ValuationSubring F₁ := (R i).integers.comap (algebraMap F₁ F)

omit [Algebra L₁ L] [IsScalarTower L₁ L F] in
theorem mem_O₁ {i : ι} {u : F₁} : u ∈ O₁ R F₁ i ↔ (u : F) ∈ (R i).integers := Iff.rfl

def incl (i : ι) : O₁ R F₁ i →+* (R i).integers where
  toFun x := ⟨(x : F₁), x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

omit [Algebra L₁ L] [IsScalarTower L₁ L F] in
@[scoped simp] theorem coe_incl (i : ι) (x : O₁ R F₁ i) : ((incl R F₁ i x : (R i).integers) : F) = (x : F₁) :=
  rfl

scoped instance isLocalHom_incl (i : ι) : IsLocalHom (incl R F₁ i) := by
  refine ⟨fun x hx => ?_⟩
  have hx0 : ((x : F₁) : F) ≠ 0 := fun h => hx.ne_zero (Subtype.ext h)
  have hx0' : (x : F₁) ≠ 0 := fun h => hx0 (by rw [h]; rfl)
  obtain ⟨ux, hux⟩ := hx
  have hinv : (((x : F₁) : F))⁻¹ ∈ (R i).integers := by
    have h : ((((ux⁻¹ : (R i).integersˣ) : (R i).integers)) : F) = (((x : F₁) : F))⁻¹ := by
      refine eq_inv_of_mul_eq_one_left ?_
      have h := congrArg (fun y : (R i).integers => (y : F)) ux.inv_mul
      rwa [Subring.coe_mul, OneMemClass.coe_one, hux] at h
    rw [← h]; exact ((ux⁻¹ : (R i).integersˣ) : (R i).integers).2
  have hinv₁ : (x : F₁)⁻¹ ∈ O₁ R F₁ i := by
    rw [mem_O₁]
    have : (((x : F₁)⁻¹ : F₁) : F) = (((x : F₁) : F))⁻¹ := by push_cast; rfl
    rw [this]; exact hinv
  refine ⟨⟨x, ⟨(x : F₁)⁻¹, hinv₁⟩, Subtype.ext (mul_inv_cancel₀ hx0'),
    Subtype.ext (inv_mul_cancel₀ hx0')⟩, rfl⟩

abbrev A₁ : ValuationSubring L₁ := A.comap (algebraMap L₁ L)

omit [Algebra L₁ F] [IsScalarTower L₁ L F] in
theorem mem_A₁ {x : L₁} : x ∈ A₁ (A := A) (L₁ := L₁) ↔ algebraMap L₁ L x ∈ A := Iff.rfl

def cA : A₁ (A := A) (L₁ := L₁) →+* A where
  toFun a := ⟨algebraMap L₁ L a, a.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

omit [Algebra L₁ F] [IsScalarTower L₁ L F] in
@[scoped simp] theorem coe_cA (a : A₁ (A := A) (L₁ := L₁)) : ((cA a : A) : L) = algebraMap L₁ L a := rfl

scoped instance isLocalHom_cA : IsLocalHom (cA (A := A) (L₁ := L₁)) := by
  refine ⟨fun a ha => ?_⟩
  have ha0 : (algebraMap L₁ L a) ≠ 0 := fun h => ha.ne_zero (Subtype.ext h)
  have ha0' : (a : L₁) ≠ 0 := fun h => ha0 (by rw [h, map_zero])
  have hv : A.valuation (algebraMap L₁ L a) = 1 := (A.valuation_eq_one_iff _).mp ha
  have hinv : (a : L₁)⁻¹ ∈ A₁ (A := A) (L₁ := L₁) := by
    rw [mem_A₁, map_inv₀, ← A.valuation_le_one_iff, map_inv₀, hv, inv_one]
  refine ⟨⟨a, ⟨(a : L₁)⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ ha0'),
    Subtype.ext (inv_mul_cancel₀ ha0')⟩, rfl⟩

def c₁ (i : ι) : A₁ (A := A) (L₁ := L₁) →+* O₁ R F₁ i where
  toFun a := ⟨algebraMap L₁ F₁ a, by
    rw [mem_O₁, IntermediateField.coe_algebraMap_apply, IsScalarTower.algebraMap_apply L₁ L F]
    exact ((R i).algebraMap_mem_iff _).mpr a.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

theorem incl_c₁ (i : ι) (a : A₁ (A := A) (L₁ := L₁)) : incl R F₁ i (c₁ R F₁ i a) = constHom (R i) (cA a) := by
  apply Subtype.ext
  change ((algebraMap L₁ F₁ a : F₁) : F) = algebraMap L F (algebraMap L₁ L a)
  rw [IntermediateField.coe_algebraMap_apply, ← IsScalarTower.algebraMap_apply]

scoped instance isLocalHom_c₁ (i : ι) : IsLocalHom (c₁ R F₁ i) := by
  refine ⟨fun a ha => ?_⟩
  have h := (incl R F₁ i).isUnit_map ha
  rw [incl_c₁] at h

  have hA : IsUnit (cA a) := by
    have hne : ((cA a : A) : L) ≠ 0 := by
      intro h0
      apply h.ne_zero
      apply Subtype.ext
      rw [coe_constHom, h0, map_zero]
      rfl
    obtain ⟨u, hu⟩ := h
    have hinv : (algebraMap L F ((cA a : A) : L))⁻¹ ∈ (R i).integers := by
      have h' : ((((u⁻¹ : (R i).integersˣ) : (R i).integers)) : F) =
          (algebraMap L F ((cA a : A) : L))⁻¹ := by
        refine eq_inv_of_mul_eq_one_left ?_
        have h := congrArg (fun y : (R i).integers => (y : F)) u.inv_mul
        rwa [Subring.coe_mul, OneMemClass.coe_one, hu] at h
      rw [← h']; exact ((u⁻¹ : (R i).integersˣ) : (R i).integers).2
    rw [← map_inv₀, (R i).algebraMap_mem_iff] at hinv
    exact ⟨⟨cA a, ⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ hne), Subtype.ext (inv_mul_cancel₀ hne)⟩,
      rfl⟩
  exact isUnit_of_map_unit (cA (A := A) (L₁ := L₁)) a hA

noncomputable scoped instance algebraResidue (i : ι) :
    Algebra (ResidueField (A₁ (A := A) (L₁ := L₁))) (ResidueField (O₁ R F₁ i)) :=
  (ResidueField.map (c₁ R F₁ i)).toAlgebra

theorem algebraMap_residue (i : ι) (a : A₁ (A := A) (L₁ := L₁)) :
    algebraMap (ResidueField (A₁ (A := A) (L₁ := L₁))) (ResidueField (O₁ R F₁ i))
      (IsLocalRing.residue _ a) = IsLocalRing.residue _ (c₁ R F₁ i a) := rfl

noncomputable def φ (i : ι) : ResidueField (O₁ R F₁ i) →+* Fb i :=
  ResidueField.lift ((R i).residue.comp (incl R F₁ i))

omit [Algebra L₁ L] [IsScalarTower L₁ L F] in
theorem φ_residue (i : ι) (x : O₁ R F₁ i) :
    φ R F₁ i (IsLocalRing.residue _ x) = (R i).residue (incl R F₁ i x) := rfl

theorem φ_algebraMap (i : ι) (a : A₁ (A := A) (L₁ := L₁)) :
    φ R F₁ i (algebraMap _ (ResidueField (O₁ R F₁ i)) (IsLocalRing.residue _ a)) =
      algebraMap (ResidueField A) (Fb i) (IsLocalRing.residue A (cA a)) := by
  rw [algebraMap_residue, φ_residue, incl_c₁, residue_constHom]

end Restrict

section Regular

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type u} [Field F] [Algebra L F]
variable {ι : Type*} {Fb : ι → Type*} [∀ i, Field (Fb i)]
  [∀ i, Algebra (ResidueField A) (Fb i)]
variable (R : ∀ i, RegularProlongation A F (Fb i))
variable {L₁ : Type*} [Field L₁] [Algebra L₁ L] [Algebra L₁ F] [IsScalarTower L₁ L F]
variable (F₁ : IntermediateField L₁ F)
variable (f : F) (hf : ∀ i, f ∈ (R i).integers) (hf₁ : f ∈ F₁)
  (htr : ∀ i, Transcendental (ResidueField A) ((R i).residue ⟨f, hf i⟩))

theorem exists_normalize (P : L₁[X]) (hP : P ≠ 0) :
    ∃ c : L₁, c ≠ 0 ∧ (∀ j, algebraMap L₁ L ((C c⁻¹ * P).coeff j) ∈ A) ∧
      ∃ d, A.valuation (algebraMap L₁ L ((C c⁻¹ * P).coeff d)) = 1 := by
  classical
  set t := Finset.range (P.natDegree + 1) with ht
  have hmem : P.natDegree ∈ t := Finset.self_mem_range_succ _
  obtain ⟨d, hd, hmax⟩ := t.exists_max_image (fun j => A.valuation (algebraMap L₁ L (P.coeff j)))
    ⟨_, hmem⟩
  have hmax' : ∀ j, A.valuation (algebraMap L₁ L (P.coeff j)) ≤
      A.valuation (algebraMap L₁ L (P.coeff d)) := by
    intro j
    by_cases hj : j < P.natDegree + 1
    · exact hmax j (Finset.mem_range.mpr hj)
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), map_zero, map_zero]
      exact zero_le'
  set c := P.coeff d with hc
  have hc0 : c ≠ 0 := by
    intro h0
    have h := hmax _ hmem
    rw [h0, map_zero, map_zero, le_zero_iff, map_eq_zero, map_eq_zero,
      Polynomial.coeff_natDegree, Polynomial.leadingCoeff_eq_zero] at h
    exact hP h
  have hv0 : A.valuation (algebraMap L₁ L c) ≠ 0 := by
    rw [ne_eq, map_eq_zero, map_eq_zero]; exact hc0
  refine ⟨c, hc0, fun j => ?_, d, ?_⟩
  · rw [coeff_C_mul, map_mul, ← A.valuation_le_one_iff, map_mul, map_inv₀, map_inv₀]
    calc (A.valuation (algebraMap L₁ L c))⁻¹ * A.valuation (algebraMap L₁ L (P.coeff j))
        ≤ (A.valuation (algebraMap L₁ L c))⁻¹ * A.valuation (algebraMap L₁ L c) := by
          gcongr; exact hmax' j
      _ = 1 := inv_mul_cancel₀ hv0
  · rw [coeff_C_mul, ← hc, inv_mul_cancel₀ hc0, map_one, map_one]

include htr in

theorem valuation_aeval_eq_one (i : ι) (P : L₁[X])
    (hP : ∀ j, algebraMap L₁ L (P.coeff j) ∈ A)
    (hP1 : ∃ d, A.valuation (algebraMap L₁ L (P.coeff d)) = 1) :
    (O₁ R F₁ i).valuation (aeval (⟨f, hf₁⟩ : F₁) P) = 1 := by
  have hmap : ∀ j, (P.map (algebraMap L₁ L)).coeff j ∈ A := fun j => by
    rw [coeff_map]; exact hP j
  have hmap1 : ∃ d, A.valuation ((P.map (algebraMap L₁ L)).coeff d) = 1 := by
    obtain ⟨d, hd⟩ := hP1; exact ⟨d, by rw [coeff_map]; exact hd⟩
  obtain ⟨hmemO, hunit⟩ := isUnit_of_aeval_eq (R i) ⟨f, hf i⟩ (htr i) _ hmap hmap1
  have hcoe : ((aeval (⟨f, hf₁⟩ : F₁) P : F₁) : F) = aeval f (P.map (algebraMap L₁ L)) := by
    rw [aeval_map_algebraMap, ← IntermediateField.aeval_coe]
  have hmem₁ : aeval (⟨f, hf₁⟩ : F₁) P ∈ O₁ R F₁ i := by
    rw [mem_O₁, hcoe]; exact hmemO
  have hu₁ : IsUnit (⟨_, hmem₁⟩ : O₁ R F₁ i) := by
    refine isUnit_of_map_unit (incl R F₁ i) _ ?_
    rw [show incl R F₁ i ⟨_, hmem₁⟩ = ⟨aeval f (P.map (algebraMap L₁ L)), hmemO⟩ from
      Subtype.ext hcoe]
    exact hunit
  exact ((O₁ R F₁ i).valuation_eq_one_iff ⟨_, hmem₁⟩).mp hu₁

include htr in

theorem exists_smul_mem₁ [IsAlgClosed L₁]
    (hfd₁ : FiniteDimensional (IntermediateField.adjoin L₁ ({(⟨f, hf₁⟩ : F₁)} : Set F₁)) F₁)
    (i : ι) (g : F₁) (hg : g ≠ 0) :
    ∃ c : L₁, ∃ h : c • g ∈ O₁ R F₁ i, IsLocalRing.residue (O₁ R F₁ i) ⟨c • g, h⟩ ≠ 0 := by
  classical
  set f₁ : F₁ := ⟨f, hf₁⟩ with hf₁def
  set E := IntermediateField.adjoin L₁ ({f₁} : Set F₁) with hE
  haveI := hfd₁
  haveI : Algebra.IsAlgebraic E F₁ := Algebra.IsAlgebraic.of_finite E F₁
  set O := O₁ R F₁ i with hO
  obtain ⟨n, hn, e, he, hval⟩ :=
    ValuationSubring.exists_pow_valuation_eq_valuation_algebraMap_of_isAlgebraic (E := E) O hg

  obtain ⟨P, Q, hPQ⟩ := (IntermediateField.mem_adjoin_simple_iff L₁ (e : F₁)).mp e.2
  have htrf : ∀ S : L₁[X], aeval f₁ S = 0 → S = 0 := by
    intro S hS
    by_contra hS0
    obtain ⟨c, hc0, hcoef, hd⟩ := exists_normalize (A := A) S hS0
    have h1 := valuation_aeval_eq_one R F₁ f hf hf₁ htr i _ hcoef hd
    rw [map_mul, aeval_C, hS, mul_zero, map_zero] at h1
    exact zero_ne_one h1
  have he0 : (e : F₁) ≠ 0 := fun h => he (Subtype.ext h)
  have hP0 : P ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div] at hPQ
    exact he0 hPQ
  have hQ0 : Q ≠ 0 := by
    rintro rfl
    rw [map_zero, div_zero] at hPQ
    exact he0 hPQ
  obtain ⟨cP, hcP, hPcoef, hPd⟩ := exists_normalize (A := A) P hP0
  obtain ⟨cQ, hcQ, hQcoef, hQd⟩ := exists_normalize (A := A) Q hQ0
  have hvP := valuation_aeval_eq_one R F₁ f hf hf₁ htr i _ hPcoef hPd
  have hvQ := valuation_aeval_eq_one R F₁ f hf hf₁ htr i _ hQcoef hQd
  rw [map_mul, aeval_C] at hvP hvQ
  change O.valuation (algebraMap L₁ F₁ cP⁻¹ * aeval f₁ P) = 1 at hvP
  change O.valuation (algebraMap L₁ F₁ cQ⁻¹ * aeval f₁ Q) = 1 at hvQ

  have hve : O.valuation (algebraMap E F₁ e) = O.valuation (algebraMap L₁ F₁ (cP / cQ)) := by
    rw [show (algebraMap E F₁ e : F₁) = (e : F₁) from rfl, hPQ]
    have hP' : aeval f₁ P = algebraMap L₁ F₁ cP * (algebraMap L₁ F₁ cP⁻¹ * aeval f₁ P) := by
      rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hcP, map_one, one_mul]
    have hQ' : aeval f₁ Q = algebraMap L₁ F₁ cQ * (algebraMap L₁ F₁ cQ⁻¹ * aeval f₁ Q) := by
      rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hcQ, map_one, one_mul]
    rw [hP', hQ', map_div₀, map_mul (O.valuation) (algebraMap L₁ F₁ cP),
      map_mul (O.valuation) (algebraMap L₁ F₁ cQ), hvP, hvQ, mul_one, mul_one, map_div₀, map_div₀]

  obtain ⟨δ, hδ⟩ := IsAlgClosed.exists_pow_nat_eq (cP / cQ) hn
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne'] at hδ
    exact div_ne_zero hcP hcQ hδ.symm
  have hval1 : O.valuation (δ⁻¹ • g) = 1 := by
    have hpow : O.valuation (δ⁻¹ • g) ^ n = 1 := by
      have h1 : (δ⁻¹ • g) ^ n = algebraMap L₁ F₁ ((cP / cQ)⁻¹) * g ^ n := by
        rw [_root_.smul_pow, Algebra.smul_def, inv_pow, hδ]
      rw [← map_pow, h1, map_mul, hval, hve, ← map_mul, ← map_mul,
        inv_mul_cancel₀ (div_ne_zero hcP hcQ), map_one, map_one]
    exact (pow_eq_one_iff_left hn.ne').mp hpow
  have hmem : δ⁻¹ • g ∈ O := (O.valuation_le_one_iff _).mp hval1.le
  refine ⟨δ⁻¹, hmem, ?_⟩
  rw [ne_eq, IsLocalRing.residue_eq_zero_iff]
  intro hmax
  have hu : IsUnit (⟨δ⁻¹ • g, hmem⟩ : O) := (O.valuation_eq_one_iff _).mpr hval1
  exact (IsLocalRing.mem_maximalIdeal _).mp hmax hu

noncomputable def R₁ [IsAlgClosed L₁]
    (hfd₁ : FiniteDimensional (IntermediateField.adjoin L₁ ({(⟨f, hf₁⟩ : F₁)} : Set F₁)) F₁)
    (i : ι) :
    RegularProlongation (A₁ (A := A) (L₁ := L₁)) F₁ (ResidueField (O₁ R F₁ i)) where
  integers := O₁ R F₁ i
  residue := IsLocalRing.residue (O₁ R F₁ i)
  algebraMap_mem_iff x := by
    rw [mem_O₁, mem_A₁, IntermediateField.coe_algebraMap_apply,
      IsScalarTower.algebraMap_apply L₁ L F, (R i).algebraMap_mem_iff]
  residue_surjective := IsLocalRing.residue_surjective
  ker_residue := IsLocalRing.ker_residue
  residue_algebraMap a := by
    rw [algebraMap_residue]
    rfl
  exists_smul_mem g hg := exists_smul_mem₁ R F₁ f hf hf₁ htr hfd₁ i g hg

end Regular

section Complete

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type u} [Field F] [Algebra L F]
variable {ι : Type*} [Fintype ι] {Fb : ι → Type*} [∀ i, Field (Fb i)]
  [∀ i, Algebra (ResidueField A) (Fb i)]
variable (R : ∀ i, RegularProlongation A F (Fb i))
variable {L₁ : Type*} [Field L₁] [IsAlgClosed L₁] [Algebra L₁ L] [Algebra L₁ F] [IsScalarTower L₁ L F]
variable (F₁ : IntermediateField L₁ F)
variable (f : F) (hf : ∀ i, f ∈ (R i).integers) (hf₁ : f ∈ F₁)
  (htr : ∀ i, Transcendental (ResidueField A) ((R i).residue ⟨f, hf i⟩))
  (hfd₁ : FiniteDimensional (IntermediateField.adjoin L₁ ({(⟨f, hf₁⟩ : F₁)} : Set F₁)) F₁)

noncomputable def ψ : ResidueField (A₁ (A := A) (L₁ := L₁)) →+* ResidueField A :=
  ResidueField.map (cA (A := A) (L₁ := L₁))

omit [Fintype ι] [IsAlgClosed L₁] in
theorem φ_algebraMap' (i : ι) (c : ResidueField (A₁ (A := A) (L₁ := L₁))) :
    φ R F₁ i (algebraMap _ (ResidueField (O₁ R F₁ i)) c) =
      algebraMap (ResidueField A) (Fb i) (ψ (A := A) (L₁ := L₁) c) := by
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
  rw [φ_algebraMap]
  rfl

omit [Fintype ι] [IsAlgClosed L₁] in
theorem φ_comp_algebraMap (i : ι) :
    (φ R F₁ i).comp (algebraMap _ (ResidueField (O₁ R F₁ i))) =
      (algebraMap (ResidueField A) (Fb i)).comp (ψ (A := A) (L₁ := L₁)) :=
  RingHom.ext fun c => φ_algebraMap' R F₁ i c

omit [Fintype ι] [IsAlgClosed L₁] in

theorem φ_mem_adjoin (i : ι) (x : ResidueField (O₁ R F₁ i))
    (c : ResidueField (O₁ R F₁ i))
    (hc : c ∈ IntermediateField.adjoin (ResidueField (A₁ (A := A) (L₁ := L₁))) ({x} : Set _)) :
    φ R F₁ i c ∈ IntermediateField.adjoin (ResidueField A) ({φ R F₁ i x} : Set (Fb i)) := by
  obtain ⟨p, q, hpq⟩ := (IntermediateField.mem_adjoin_simple_iff _ c).mp hc
  rw [IntermediateField.mem_adjoin_simple_iff]
  refine ⟨p.map (ψ (A := A) (L₁ := L₁)), q.map (ψ (A := A) (L₁ := L₁)), ?_⟩
  rw [hpq, map_div₀, aeval_def, aeval_def, aeval_def, aeval_def, hom_eval₂, hom_eval₂,
    φ_comp_algebraMap, eval₂_map, eval₂_map]

include htr in
omit [Fintype ι] [IsAlgClosed L₁] in

theorem transcendental_residue₁ (i : ι) :
    Transcendental (ResidueField (A₁ (A := A) (L₁ := L₁)))
      (IsLocalRing.residue (O₁ R F₁ i) ⟨⟨f, hf₁⟩, hf i⟩) := by
  rw [transcendental_iff]
  intro p hp
  have h := congrArg (φ R F₁ i) hp
  rw [map_zero, aeval_def, hom_eval₂, φ_comp_algebraMap, ← eval₂_map, ← aeval_def, φ_residue] at h
  change aeval ((R i).residue ⟨f, hf i⟩) (p.map (ψ (A := A) (L₁ := L₁))) = 0 at h
  have h0 := transcendental_iff.mp (htr i) _ h
  exact (Polynomial.map_eq_zero_iff (ψ (A := A) (L₁ := L₁)).injective).mp h0

omit [Fintype ι] [IsAlgClosed L₁] [Algebra L₁ L] [IsScalarTower L₁ L F] in

theorem injective_O₁
    (hsep : ∀ i j, i ≠ j → ∃ u ∈ F₁, ¬ (u ∈ (R i).integers ↔ u ∈ (R j).integers)) :
    Function.Injective fun i => O₁ R F₁ i := by
  intro i j hij
  by_contra hne
  obtain ⟨u, huF₁, hu⟩ := hsep i j hne
  apply hu
  have h : (⟨u, huF₁⟩ : F₁) ∈ O₁ R F₁ i ↔ (⟨u, huF₁⟩ : F₁) ∈ O₁ R F₁ j := by
    change _ ∈ (fun i => O₁ R F₁ i) i ↔ _
    rw [hij]
  exact h

include htr hfd₁ in
omit [Fintype ι] in

theorem finrank_le_finrank₁ (i : ι)
    [FiniteDimensional (IntermediateField.adjoin (ResidueField (A₁ (A := A) (L₁ := L₁)))
      ({(R₁ R F₁ f hf hf₁ htr hfd₁ i).residue ⟨⟨f, hf₁⟩, hf i⟩} : Set (ResidueField (O₁ R F₁ i))))
      (ResidueField (O₁ R F₁ i))]
    {m : ℕ} (b : Fin m → F) (hb : ∀ l, b l ∈ (R i).integers) (hbF₁ : ∀ l, b l ∈ F₁)
    (hli : LinearIndependent (IntermediateField.adjoin (ResidueField A)
      ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (fun l => (R i).residue ⟨b l, hb l⟩)) :
    m ≤ Module.finrank (IntermediateField.adjoin (ResidueField (A₁ (A := A) (L₁ := L₁)))
      ({(R₁ R F₁ f hf hf₁ htr hfd₁ i).residue ⟨⟨f, hf₁⟩, hf i⟩} : Set (ResidueField (O₁ R F₁ i))))
      (ResidueField (O₁ R F₁ i)) := by
  set x₁ := (R₁ R F₁ f hf hf₁ htr hfd₁ i).residue ⟨⟨f, hf₁⟩, hf i⟩ with hx₁
  set K₁ := IntermediateField.adjoin (ResidueField (A₁ (A := A) (L₁ := L₁)))
    ({x₁} : Set (ResidueField (O₁ R F₁ i))) with hK₁
  set K := IntermediateField.adjoin (ResidueField A) ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))
    with hK
  set β : Fin m → ResidueField (O₁ R F₁ i) :=
    fun l => IsLocalRing.residue (O₁ R F₁ i) ⟨⟨b l, hbF₁ l⟩, hb l⟩ with hβ
  have hφx : φ R F₁ i x₁ = (R i).residue ⟨f, hf i⟩ := rfl
  have hφβ : ∀ l, φ R F₁ i (β l) = (R i).residue ⟨b l, hb l⟩ := fun l => rfl
  have hβli : LinearIndependent K₁ β := by
    rw [Fintype.linearIndependent_iff]
    intro g hg l
    have hmem : ∀ l, φ R F₁ i (g l : ResidueField (O₁ R F₁ i)) ∈ K := fun l => by
      rw [hK, ← hφx]; exact φ_mem_adjoin R F₁ i x₁ _ (g l).2
    have hrel : ∑ l, (⟨φ R F₁ i (g l), hmem l⟩ : K) • (R i).residue ⟨b l, hb l⟩ = 0 := by
      have h := congrArg (φ R F₁ i) hg
      rw [map_sum, map_zero] at h
      rw [← h]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [IntermediateField.smul_def, smul_eq_mul, IntermediateField.smul_def, smul_eq_mul, map_mul,
        hφβ]
    have h0 := Fintype.linearIndependent_iff.mp hli _ hrel l
    rw [Subtype.ext_iff, ZeroMemClass.coe_zero] at h0
    change φ R F₁ i (g l) = 0 at h0
    rw [map_eq_zero_iff _ (φ R F₁ i).injective] at h0
    exact Subtype.ext h0
  have h := hβli.fintype_card_le_finrank
  rwa [Fintype.card_fin] at h

end Complete

section Assembly

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type u} [Field F] [Algebra L F]
variable {ι : Type*} [Fintype ι] {Fb : ι → Type*} [∀ i, Field (Fb i)]
  [∀ i, Algebra (ResidueField A) (Fb i)]

theorem main (R : ∀ i, RegularProlongation A F (Fb i))
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (htr : ∀ i, Transcendental (IsLocalRing.ResidueField A) ((R i).residue ⟨f, hf i⟩))
    (heq : ∑ i, Module.finrank (IntermediateField.adjoin (IsLocalRing.ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)
      = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F)
    {L₁ : Type*} [Field L₁] [IsAlgClosed L₁] [Algebra L₁ L] [Algebra L₁ F] [IsScalarTower L₁ L F]
    (F₁ : IntermediateField L₁ F) (hf₁ : f ∈ F₁)
    (hfd₁ : FiniteDimensional (IntermediateField.adjoin L₁ ({(⟨f, hf₁⟩ : F₁)} : Set F₁)) F₁)
    (hdeg : Module.finrank (IntermediateField.adjoin L₁ ({(⟨f, hf₁⟩ : F₁)} : Set F₁)) F₁ ≤
      Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F)
    (hsep : ∀ i j, i ≠ j → ∃ u ∈ F₁, ¬ (u ∈ (R i).integers ↔ u ∈ (R j).integers))
    (hbas : ∀ i, ∃ (b : Fin (Module.finrank (IntermediateField.adjoin (IsLocalRing.ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)) → F) (hb : ∀ l, b l ∈ (R i).integers),
        (∀ l, b l ∈ F₁) ∧
        LinearIndependent (IntermediateField.adjoin (IsLocalRing.ResidueField A)
          ({(R i).residue ⟨f, hf i⟩} : Set (Fb i)))
          (fun l => (R i).residue ⟨b l, hb l⟩)) :
    ∃ (Fb₁ : ι → Type u) (_ : ∀ i, Field (Fb₁ i))
      (_ : ∀ i, Algebra (IsLocalRing.ResidueField (A.comap (algebraMap L₁ L))) (Fb₁ i))
      (R₁ : ∀ i, RegularProlongation (A.comap (algebraMap L₁ L)) F₁ (Fb₁ i))
      (φ : ∀ i, Fb₁ i →+* Fb i)
      (hO : ∀ i (u : F₁), u ∈ (R₁ i).integers ↔ (u : F) ∈ (R i).integers),
      Function.Injective (fun i => (R₁ i).integers) ∧
      (∀ i (u : F₁) (hu : (u : F) ∈ (R i).integers),
        φ i ((R₁ i).residue ⟨u, (hO i u).mpr hu⟩) = (R i).residue ⟨u, hu⟩) ∧
      (∀ i (a : A.comap (algebraMap L₁ L)),
        φ i (algebraMap (IsLocalRing.ResidueField (A.comap (algebraMap L₁ L))) (Fb₁ i)
          (IsLocalRing.residue _ a)) =
        algebraMap (IsLocalRing.ResidueField A) (Fb i)
          (IsLocalRing.residue A ⟨algebraMap L₁ L a, ValuationSubring.mem_comap.mp a.2⟩)) ∧
      Transcendental L₁ (⟨f, hf₁⟩ : F₁) ∧
      (∀ i, Transcendental (IsLocalRing.ResidueField (A.comap (algebraMap L₁ L)))
        ((R₁ i).residue ⟨⟨f, hf₁⟩, (hO i _).mpr (hf i)⟩)) ∧
      ∑ i, Module.finrank (IntermediateField.adjoin
          (IsLocalRing.ResidueField (A.comap (algebraMap L₁ L)))
          ({(R₁ i).residue ⟨⟨f, hf₁⟩, (hO i _).mpr (hf i)⟩} : Set (Fb₁ i))) (Fb₁ i)
        = Module.finrank (IntermediateField.adjoin L₁ ({(⟨f, hf₁⟩ : F₁)} : Set F₁)) F₁ ∧
      Module.finrank (IntermediateField.adjoin L₁ ({(⟨f, hf₁⟩ : F₁)} : Set F₁)) F₁ =
        Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F := by
  classical
  haveI := hfd₁
  set f₁ : F₁ := ⟨f, hf₁⟩ with hf₁def
  set Rr := R₁ R F₁ f hf hf₁ htr hfd₁ with hRr
  have hO : ∀ i (u : F₁), u ∈ (Rr i).integers ↔ (u : F) ∈ (R i).integers := fun i u => Iff.rfl
  have hRr_inj : Function.Injective (fun i => (Rr i).integers) := injective_O₁ R F₁ hsep
  have htr₁ : ∀ i, Transcendental (ResidueField (A₁ (A := A) (L₁ := L₁)))
      ((Rr i).residue ⟨f₁, hf i⟩) := fun i => transcendental_residue₁ R F₁ f hf hf₁ htr i

  obtain ⟨hfin, hle⟩ :=
    AlgebraicCurve.RegularProlongation.sum_finrank_adjoin_residue_le (A₁ (A := A) (L₁ := L₁))
      (fun i => ResidueField (O₁ R F₁ i)) Rr hRr_inj f₁ (fun i => hf i) htr₁

  have hge : ∀ i, Module.finrank (IntermediateField.adjoin (ResidueField A)
      ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i) ≤
      Module.finrank (IntermediateField.adjoin (ResidueField (A₁ (A := A) (L₁ := L₁)))
        ({(Rr i).residue ⟨f₁, hf i⟩} : Set (ResidueField (O₁ R F₁ i)))) (ResidueField (O₁ R F₁ i)) := by
    intro i
    haveI := hfin i
    obtain ⟨b, hb, hbF₁, hli⟩ := hbas i
    exact finrank_le_finrank₁ R F₁ f hf hf₁ htr hfd₁ i b hb hbF₁ hli
  have hsum_ge := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hge i
  rw [heq] at hsum_ge
  have heq₁ : ∑ i, Module.finrank (IntermediateField.adjoin (ResidueField (A₁ (A := A) (L₁ := L₁)))
      ({(Rr i).residue ⟨f₁, hf i⟩} : Set (ResidueField (O₁ R F₁ i)))) (ResidueField (O₁ R F₁ i)) =
      Module.finrank (IntermediateField.adjoin L₁ ({f₁} : Set F₁)) F₁ :=
    le_antisymm hle (hdeg.trans hsum_ge)
  have hdeg' : Module.finrank (IntermediateField.adjoin L₁ ({f₁} : Set F₁)) F₁ =
      Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F :=
    le_antisymm hdeg (hsum_ge.trans hle)

  have hpos : 0 < Module.finrank (IntermediateField.adjoin L₁ ({f₁} : Set F₁)) F₁ :=
    Module.finrank_pos
  haveI : Nonempty ι := by
    by_contra hι
    rw [not_nonempty_iff] at hι
    rw [← heq₁, Finset.univ_eq_empty, Finset.sum_empty] at hpos
    exact lt_irrefl _ hpos
  obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
  have htrL₁ : Transcendental L₁ f₁ :=
    AlgebraicCurve.RegularProlongation.transcendental_of_residue_transcendental
      (A₁ (A := A) (L₁ := L₁)) (Rr i₀) ⟨f₁, hf i₀⟩ (htr₁ i₀)
  refine ⟨fun i => ResidueField (O₁ R F₁ i), inferInstance, inferInstance, Rr,
    fun i => φ R F₁ i, hO, hRr_inj, fun i u hu => rfl, fun i a => φ_algebraMap R F₁ i a,
    htrL₁, htr₁, heq₁, hdeg'⟩

end Assembly

end DescSol
p2m_reactivate "P2MW.S_AlgebraicCurve_RegularProlongation_exists_regularProlongation_intermediateField_sum_finrank_adjoin_residue_eq.DescSol"

open AlgebraicCurve in
theorem solution.{u}
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type u} [Field F] [Algebra L F]
    {ι : Type*} [Fintype ι] (Fb : ι → Type*) [∀ i, Field (Fb i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i))
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (htr : ∀ i, Transcendental (IsLocalRing.ResidueField A) ((R i).residue ⟨f, hf i⟩))
    (heq : ∑ i, Module.finrank (IntermediateField.adjoin (IsLocalRing.ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)
      = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F)
    {L₁ : Type*} [Field L₁] [IsAlgClosed L₁] [Algebra L₁ L] [Algebra L₁ F] [IsScalarTower L₁ L F]
    (F₁ : IntermediateField L₁ F) (hf₁ : f ∈ F₁)
    (hfd₁ : FiniteDimensional (IntermediateField.adjoin L₁ ({(⟨f, hf₁⟩ : F₁)} : Set F₁)) F₁)
    (hdeg : Module.finrank (IntermediateField.adjoin L₁ ({(⟨f, hf₁⟩ : F₁)} : Set F₁)) F₁ ≤
      Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F)
    (hsep : ∀ i j, i ≠ j → ∃ u ∈ F₁, ¬ (u ∈ (R i).integers ↔ u ∈ (R j).integers))
    (hbas : ∀ i, ∃ (b : Fin (Module.finrank (IntermediateField.adjoin (IsLocalRing.ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)) → F) (hb : ∀ l, b l ∈ (R i).integers),
        (∀ l, b l ∈ F₁) ∧
        LinearIndependent (IntermediateField.adjoin (IsLocalRing.ResidueField A)
          ({(R i).residue ⟨f, hf i⟩} : Set (Fb i)))
          (fun l => (R i).residue ⟨b l, hb l⟩)) :
    ∃ (Fb₁ : ι → Type u) (_ : ∀ i, Field (Fb₁ i))
      (_ : ∀ i, Algebra (IsLocalRing.ResidueField (A.comap (algebraMap L₁ L))) (Fb₁ i))
      (R₁ : ∀ i, RegularProlongation (A.comap (algebraMap L₁ L)) F₁ (Fb₁ i))
      (φ : ∀ i, Fb₁ i →+* Fb i)
      (hO : ∀ i (u : F₁), u ∈ (R₁ i).integers ↔ (u : F) ∈ (R i).integers),
      Function.Injective (fun i => (R₁ i).integers) ∧
      (∀ i (u : F₁) (hu : (u : F) ∈ (R i).integers),
        φ i ((R₁ i).residue ⟨u, (hO i u).mpr hu⟩) = (R i).residue ⟨u, hu⟩) ∧
      (∀ i (a : A.comap (algebraMap L₁ L)),
        φ i (algebraMap (IsLocalRing.ResidueField (A.comap (algebraMap L₁ L))) (Fb₁ i)
          (IsLocalRing.residue _ a)) =
        algebraMap (IsLocalRing.ResidueField A) (Fb i)
          (IsLocalRing.residue A ⟨algebraMap L₁ L a, ValuationSubring.mem_comap.mp a.2⟩)) ∧
      Transcendental L₁ (⟨f, hf₁⟩ : F₁) ∧
      (∀ i, Transcendental (IsLocalRing.ResidueField (A.comap (algebraMap L₁ L)))
        ((R₁ i).residue ⟨⟨f, hf₁⟩, (hO i _).mpr (hf i)⟩)) ∧
      ∑ i, Module.finrank (IntermediateField.adjoin
          (IsLocalRing.ResidueField (A.comap (algebraMap L₁ L)))
          ({(R₁ i).residue ⟨⟨f, hf₁⟩, (hO i _).mpr (hf i)⟩} : Set (Fb₁ i))) (Fb₁ i)
        = Module.finrank (IntermediateField.adjoin L₁ ({(⟨f, hf₁⟩ : F₁)} : Set F₁)) F₁ ∧
      Module.finrank (IntermediateField.adjoin L₁ ({(⟨f, hf₁⟩ : F₁)} : Set F₁)) F₁ =
        Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F :=
  DescSol.main R f hf htr heq F₁ hf₁ hfd₁ hdeg hsep hbas

end S_AlgebraicCurve_RegularProlongation_exists_regularProlongation_intermediateField_sum_finrank_adjoin_residue_eq
end P2MW
export P2MW.S_AlgebraicCurve_RegularProlongation_exists_regularProlongation_intermediateField_sum_finrank_adjoin_residue_eq (solution)
