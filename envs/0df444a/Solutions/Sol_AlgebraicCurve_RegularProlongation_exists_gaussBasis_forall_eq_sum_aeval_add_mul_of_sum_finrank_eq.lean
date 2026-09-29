-- Prove2me | solution 1 for AlgebraicCurve.RegularProlongation.exists_gaussBasis_forall_eq_sum_aeval_add_mul_of_sum_finrank_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/d90fb43b-5981-55fd-8a25-e1f4559a35a6

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_Algebra_finite_integralClosure_adjoin_singleton_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_RegularProlongation_finiteDimensional_adjoin_residue_of_sum_finrank_eq
import Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_eq_integers_of_forall_mem_adjoin_iff_of_sum_finrank_eq_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_RegularProlongation_coe_minpoly_adjoin_coeff_mem_integers
import Theorems.Thm_AlgebraicCurve_RegularProlongation_coeff_mem_of_aeval_mem_integers
import Theorems.Thm_AlgebraicCurve_RegularProlongation_isIntegral_adjoin_residue_of_exists_monic_bivariate_eval_eq_zero
import Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_gaussBasis_mem_integralClosure_piResidue_uniqueRepr_of_sum_finrank_eq
import Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_nonunit_smul_eq_of_forall_residue_eq_zero_of_sum_finrank_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RegularProlongation_exists_gaussBasis_forall_eq_sum_aeval_add_mul_of_sum_finrank_eq

open Polynomial AlgebraicCurve IsLocalRing

namespace RGSol

section PID

variable {k : Type*} [Field k] {E : Type*} [CommRing E] [Algebra k E]

theorem exists_polynomial_basis (fb : E) (M : Submodule k E)
    (hM : ∀ m ∈ M, fb * m ∈ M)
    (htf : ∀ (q : k[X]) (h : E), aeval fb q * h = 0 → q = 0 ∨ h = 0)
    {γ : Type*} [Fintype γ] (g : γ → E)
    (hN : ∀ m ∈ M, ∃ q : γ → k[X], m = ∑ c, aeval fb (q c) * g c) :
    ∃ (d : ℕ) (zb : Fin d → E), (∀ σ, zb σ ∈ M) ∧
      (∀ q q' : Fin d → k[X],
        ∑ σ, aeval fb (q σ) * zb σ = ∑ σ, aeval fb (q' σ) * zb σ → q = q') ∧
      (∀ m ∈ M, ∃ q : Fin d → k[X], m = ∑ σ, aeval fb (q σ) * zb σ) ∧
      (∀ (d' : ℕ) (zb' : Fin d' → E), (∀ τ, zb' τ ∈ M) →
        (∀ q q' : Fin d' → k[X],
          ∑ τ, aeval fb (q τ) * zb' τ = ∑ τ, aeval fb (q' τ) * zb' τ → q = q') → d' ≤ d) := by
  classical

  letI inst : Module k[X] E := Module.compHom E (aeval fb).toRingHom
  have hsmul : ∀ (q : k[X]) (h : E), q • h = aeval fb q * h := fun _ _ => rfl

  let M' : Submodule k[X] E :=
    { carrier := M
      add_mem' := fun ha hb => M.add_mem ha hb
      zero_mem' := M.zero_mem
      smul_mem' := by
        intro q m hm
        change q • m ∈ M
        rw [hsmul]
        induction q using Polynomial.induction_on' with
        | add p q hp hq => rw [map_add, add_mul]; exact M.add_mem hp hq
        | monomial n a =>
          rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow, aeval_C, aeval_X, mul_assoc,
            Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
          refine M.smul_mem a ?_
          induction n with
          | zero => rwa [pow_zero, one_mul]
          | succ n ih => rw [pow_succ', mul_assoc]; exact hM _ ih }
  have hM'mem : ∀ {m : E}, m ∈ M' ↔ m ∈ M := Iff.rfl

  let N' : Submodule k[X] E := Submodule.span k[X] (Set.range g)
  have hle : M' ≤ N' := by
    intro m hm
    obtain ⟨q, rfl⟩ := hN m hm
    refine N'.sum_mem fun c _ => ?_
    rw [← hsmul]
    exact N'.smul_mem _ (Submodule.subset_span ⟨c, rfl⟩)
  haveI : IsNoetherian k[X] N' := isNoetherian_of_fg_of_noetherian _
    (Submodule.fg_span (Set.finite_range g))
  haveI : IsNoetherian k[X] M' := isNoetherian_of_le hle
  haveI : Module.Finite k[X] M' := inferInstance
  haveI : Module.IsTorsionFree k[X] M' := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun q m hqm => ?_
    have h0 : aeval fb q * (m : E) = 0 := by
      rw [← hsmul]; exact congrArg Subtype.val hqm
    rcases htf q m h0 with h | h
    · exact Or.inl h
    · exact Or.inr (Subtype.ext h)
  obtain ⟨d, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := k[X]) (M := M')
  refine ⟨d, fun σ => (b σ : E), fun σ => (b σ).2, ?_, ?_, ?_⟩
  ·
    intro q q' hqq'
    have hsum : ∀ r : Fin d → k[X],
        ((∑ σ, r σ • b σ : M') : E) = ∑ σ, aeval fb (r σ) * (b σ : E) := by
      intro r
      rw [Submodule.coe_sum]
      exact Finset.sum_congr rfl fun σ _ => rfl
    have h1 : (∑ σ, q σ • b σ : M') = ∑ σ, q' σ • b σ := by
      apply Subtype.ext
      rw [hsum, hsum, hqq']
    have h2 : ∑ σ, (q σ - q' σ) • b σ = (0 : M') := by
      have hsub : ∀ σ, (q σ - q' σ) • b σ = q σ • b σ - q' σ • b σ := fun σ => sub_smul (q σ) (q' σ) (b σ)
      simp_rw [hsub, Finset.sum_sub_distrib, h1, sub_self]
    have h3 := Fintype.linearIndependent_iff.mp b.linearIndependent (fun σ => q σ - q' σ) h2
    funext σ
    exact sub_eq_zero.mp (h3 σ)
  ·
    intro m hm
    refine ⟨fun σ => b.repr ⟨m, hm⟩ σ, ?_⟩
    have h := congrArg (fun x : M' => (x : E)) (b.sum_repr ⟨m, hm⟩)
    simp only [Submodule.coe_sum] at h
    exact h.symm.trans (Finset.sum_congr rfl fun σ _ => rfl)
  ·
    intro d' zb' hzb' hind
    let v : Fin d' → M' := fun τ => ⟨zb' τ, hzb' τ⟩
    have hv : LinearIndependent k[X] v := by
      rw [Fintype.linearIndependent_iff]
      intro q hq τ
      have h0 : ∑ τ, aeval fb (q τ) * zb' τ = ∑ τ, aeval fb ((0 : Fin d' → k[X]) τ) * zb' τ := by
        have h := congrArg (fun x : M' => (x : E)) hq
        simp only [Submodule.coe_sum, ZeroMemClass.coe_zero] at h
        rw [show ∑ τ, aeval fb ((0 : Fin d' → k[X]) τ) * zb' τ = 0 by simp]
        rw [← h]
        exact Finset.sum_congr rfl fun τ _ => rfl
      exact congrFun (hind q 0 h0) τ
    have := hv.fintype_card_le_finrank
    rwa [Fintype.card_fin, Module.finrank_eq_card_basis b, Fintype.card_fin] at this

end PID

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

theorem residue_ne_zero_iff_isUnit (R : RegularProlongation A F Fbar) (u : R.integers) :
    R.residue u ≠ 0 ↔ IsUnit u :=
  ⟨R.isUnit_of_residue_ne_zero, R.residue_ne_zero_of_isUnit⟩

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

theorem coeff_map_subtype_mem (r : A[X]) (j : ℕ) : (r.map A.subtype).coeff j ∈ A := by
  rw [coeff_map]; exact (r.coeff j).2

def IsT (f u : F) : Prop :=
  ∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f ∈ V → u ∈ V

omit [Algebra (ResidueField A) Fbar] in
theorem IsT.add {f u v : F} (hu : IsT (L := L) f u) (hv : IsT (L := L) f v) :
    IsT (L := L) f (u + v) := fun V hV hfV => add_mem (hu V hV hfV) (hv V hV hfV)

omit [Algebra (ResidueField A) Fbar] in
theorem IsT.mul {f u v : F} (hu : IsT (L := L) f u) (hv : IsT (L := L) f v) :
    IsT (L := L) f (u * v) := fun V hV hfV => mul_mem (hu V hV hfV) (hv V hV hfV)

omit [Algebra (ResidueField A) Fbar] in
theorem IsT.zero (f : F) : IsT (L := L) f 0 := fun V _ _ => V.zero_mem

omit [Algebra (ResidueField A) Fbar] in
theorem IsT.const (f : F) (c : L) : IsT (L := L) f (algebraMap L F c) := fun _ hV _ => hV c

omit [Algebra (ResidueField A) Fbar] in
theorem IsT.self (f : F) : IsT (L := L) f f := fun _ _ hfV => hfV

omit [Algebra (ResidueField A) Fbar] in
theorem IsT.aeval (f : F) (p : L[X]) : IsT (L := L) f (aeval f p) := by
  intro V hV hfV
  rw [aeval_eq_sum_range]
  refine V.toSubring.sum_mem fun j _ => ?_
  rw [Algebra.smul_def]
  exact mul_mem (hV _) (pow_mem hfV _)

variable (A) in

def IsW (f w : F) : Prop :=
  ∃ p q : L[X], (∀ j, p.coeff j ∈ A) ∧
    ((∀ j, A.valuation (q.coeff j) ≤ 1) ∧ ∃ d, A.valuation (q.coeff d) = 1) ∧
    w * aeval f q = aeval f p

variable (A) in

def IsMW (f μ : F) : Prop :=
  ∃ p q : L[X], (∀ j, A.valuation (p.coeff j) < 1) ∧
    ((∀ j, A.valuation (q.coeff j) ≤ 1) ∧ ∃ d, A.valuation (q.coeff d) = 1) ∧
    μ * aeval f q = aeval f p

section transc

variable (R : RegularProlongation A F Fbar) (x : R.integers)
  (hx : Transcendental (ResidueField A) (R.residue x))
include hx

theorem isUnit_evalO_of_exists_coeff (q : A[X]) (hq : ∃ d, A.valuation ((q.coeff d : A) : L) = 1) :
    IsUnit (evalO R x q) := by
  rw [← residue_ne_zero_iff_isUnit, residue_evalO]
  intro h0
  obtain ⟨d, hd⟩ := hq
  have hne : q.map (IsLocalRing.residue A) ≠ 0 := by
    intro h
    have := (map_residue_eq_zero_iff q).mp h d
    rw [hd] at this
    exact lt_irrefl _ this
  exact hne (transcendental_iff.mp hx _ h0)

theorem IsW.mem {w : F} (hw : IsW A (x : F) w) : w ∈ R.integers := by
  obtain ⟨p, q, hp, ⟨hq, hqd⟩, hwq⟩ := hw
  obtain ⟨pA, rfl⟩ := exists_map_subtype_eq A hp
  obtain ⟨qA, rfl⟩ := exists_map_subtype_eq A (fun j => (A.valuation_le_one_iff _).mp (hq j))
  have hu : IsUnit (evalO R x qA) := by
    refine isUnit_evalO_of_exists_coeff R x hx qA ?_
    obtain ⟨d, hd⟩ := hqd
    exact ⟨d, by rwa [coeff_map] at hd⟩
  obtain ⟨uq, huq⟩ := hu
  have hq0 : (aeval (x : F) (qA.map A.subtype)) ≠ 0 := by
    rw [← coe_evalO, ← huq]
    exact fun h => (Units.ne_zero uq) (Subtype.ext h)
  have hw' : w = aeval (x : F) (pA.map A.subtype) * (aeval (x : F) (qA.map A.subtype))⁻¹ := by
    rw [← hwq, mul_inv_cancel_right₀ hq0]
  have hinv : ((((uq⁻¹ : R.integersˣ) : R.integers) : F)) = (aeval (x : F) (qA.map A.subtype))⁻¹ := by
    rw [← coe_evalO, ← huq]
    refine eq_inv_of_mul_eq_one_left ?_
    have h := congrArg (fun y : R.integers => (y : F)) uq.inv_mul
    rwa [Subring.coe_mul, OneMemClass.coe_one] at h
  rw [hw', ← hinv, ← coe_evalO]
  exact mul_mem (evalO R x pA).2 ((uq⁻¹ : R.integersˣ) : R.integers).2

omit hx in

theorem IsW.mem_adjoin {f w : F} (hf : Transcendental L f) (hw : IsW A f w) :
    w ∈ IntermediateField.adjoin L ({f} : Set F) := by
  obtain ⟨p, q, -, ⟨-, d, hd⟩, hwq⟩ := hw
  have hq0 : q ≠ 0 := by
    rintro rfl
    rw [coeff_zero, map_zero] at hd
    exact zero_ne_one hd
  have hq0' : aeval f q ≠ 0 := fun h => hq0 ((transcendental_iff.mp hf) q h)
  rw [IntermediateField.mem_adjoin_simple_iff]
  exact ⟨p, q, by rw [← hwq, mul_div_cancel_right₀ _ hq0']⟩

end transc

end Infra

section Family

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {ι : Type*} {Fb : ι → Type*} [∀ i, Field (Fb i)]
  [∀ i, Algebra (ResidueField A) (Fb i)]
variable (R : ∀ i, RegularProlongation A F (Fb i)) (f : F) (hf : ∀ i, f ∈ (R i).integers)

def fb : ∀ i, Fb i := fun i => (R i).residue ⟨f, hf i⟩

theorem aeval_fb_apply (q : (ResidueField A)[X]) (i : ι) :
    aeval (fb R f hf) q i = aeval ((R i).residue ⟨f, hf i⟩) q :=
  (aeval_algHom_apply (Pi.evalAlgHom (ResidueField A) Fb i) (fb R f hf) q).symm

def resSet : Set (∀ i, Fb i) :=
  {h | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
    IsT (L := L) f u ∧ ∀ i, (R i).residue ⟨u, hu i⟩ = h i}

def resMod : Submodule (ResidueField A) (∀ i, Fb i) where
  carrier := resSet R f
  add_mem' := by
    rintro h h' ⟨u, hu, huT, hru⟩ ⟨u', hu', hu'T, hru'⟩
    refine ⟨u + u', fun i => add_mem (hu i) (hu' i), huT.add hu'T, fun i => ?_⟩
    rw [Pi.add_apply, ← hru i, ← hru' i, ← map_add]
    rfl
  zero_mem' := ⟨0, fun i => zero_mem _, IsT.zero f, fun i => by
    rw [Pi.zero_apply, ← map_zero (R i).residue]; rfl⟩
  smul_mem' := by
    rintro c h ⟨u, hu, huT, hru⟩
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
    refine ⟨algebraMap L F a * u, fun i => mul_mem (((R i).algebraMap_mem_iff _).mpr a.2) (hu i),
      (IsT.const f (a : L)).mul huT, fun i => ?_⟩
    rw [Pi.smul_apply, Algebra.smul_def, ← hru i, ← residue_constHom (R i) a, ← map_mul]
    rfl

theorem fb_mul_mem {h : ∀ i, Fb i} (hh : h ∈ resMod R f) : fb R f hf * h ∈ resMod R f := by
  obtain ⟨u, hu, huT, hru⟩ := hh
  refine ⟨f * u, fun i => mul_mem (hf i) (hu i), (IsT.self f).mul huT, fun i => ?_⟩
  rw [Pi.mul_apply, ← hru i, fb, ← map_mul]
  rfl

variable (htr : ∀ i, Transcendental (ResidueField A) ((R i).residue ⟨f, hf i⟩))

include htr in
theorem aeval_fb_mul_eq_zero (q : (ResidueField A)[X]) (h : ∀ i, Fb i)
    (h0 : aeval (fb R f hf) q * h = 0) : q = 0 ∨ h = 0 := by
  by_cases hq : q = 0
  · exact Or.inl hq
  · refine Or.inr (funext fun i => ?_)
    have hi := congrFun h0 i
    rw [Pi.mul_apply, aeval_fb_apply, Pi.zero_apply] at hi
    rcases mul_eq_zero.mp hi with h1 | h1
    · exact absurd (transcendental_iff.mp (htr i) q h1) hq
    · exact h1

section sums

variable {κ : Type*} [Fintype κ] (z : κ → F) (hz : ∀ σ i, z σ ∈ (R i).integers)

def zres : κ → ∀ i, Fb i := fun σ i => (R i).residue ⟨z σ, hz σ i⟩

noncomputable def sumO (rA : κ → A[X]) (i : ι) : (R i).integers :=
  ∑ σ, evalO (R i) ⟨f, hf i⟩ (rA σ) * ⟨z σ, hz σ i⟩

theorem coe_sumO (rA : κ → A[X]) (i : ι) :
    ((sumO R f hf z hz rA i : (R i).integers) : F) = ∑ σ, aeval f ((rA σ).map A.subtype) * z σ := by
  unfold sumO
  push_cast
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [coe_evalO]

theorem residue_sumO (rA : κ → A[X]) (i : ι) :
    (R i).residue (sumO R f hf z hz rA i) =
      (∑ σ, aeval (fb R f hf) ((rA σ).map (IsLocalRing.residue A)) * zres R z hz σ) i := by
  unfold sumO
  rw [map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_mul, residue_evalO, Pi.mul_apply, aeval_fb_apply]
  rfl

theorem map_residue_eq_zero_of_residue_sumO_eq_zero
    (huniq : ∀ q q' : κ → (ResidueField A)[X],
      ∑ σ, aeval (fb R f hf) (q σ) * zres R z hz σ = ∑ σ, aeval (fb R f hf) (q' σ) * zres R z hz σ →
      q = q')
    (rA : κ → A[X]) (h0 : ∀ i, (R i).residue (sumO R f hf z hz rA i) = 0) (σ : κ) :
    (rA σ).map (IsLocalRing.residue A) = 0 := by
  have h : ∑ σ, aeval (fb R f hf) ((rA σ).map (IsLocalRing.residue A)) * zres R z hz σ =
      ∑ σ, aeval (fb R f hf) ((0 : κ → (ResidueField A)[X]) σ) * zres R z hz σ := by
    rw [show ∑ σ, aeval (fb R f hf) ((0 : κ → (ResidueField A)[X]) σ) * zres R z hz σ = 0 by simp]
    funext i
    rw [← residue_sumO, h0 i, Pi.zero_apply]
  exact congrFun (huniq _ _ h) σ

theorem false_of_coeff_eq_one
    (huniq : ∀ q q' : κ → (ResidueField A)[X],
      ∑ σ, aeval (fb R f hf) (q σ) * zres R z hz σ = ∑ σ, aeval (fb R f hf) (q' σ) * zres R z hz σ →
      q = q')
    (rA : κ → A[X]) (h0 : ∀ i, (R i).residue (sumO R f hf z hz rA i) = 0)
    {σ₀ : κ} {j₀ : ℕ} (h1 : (((rA σ₀).coeff j₀ : A) : L) = 1) : False := by
  have h := map_residue_eq_zero_of_residue_sumO_eq_zero R f hf z hz huniq rA h0 σ₀
  have hlt := (map_residue_eq_zero_iff _).mp h j₀
  rw [h1, map_one] at hlt
  exact lt_irrefl _ hlt

omit [Fintype κ] in

theorem exists_lift (r : κ → L[X]) (hr : ∀ σ j, (r σ).coeff j ∈ A) :
    ∃ rA : κ → A[X], ∀ σ, (rA σ).map A.subtype = r σ := by
  choose rA hrA using fun σ => exists_map_subtype_eq A (hr σ)
  exact ⟨rA, hrA⟩

theorem exists_max_coeff (r : κ → L[X]) {σ₁ : κ} (hσ₁ : r σ₁ ≠ 0) :
    ∃ σ₀ j₀, (r σ₀).coeff j₀ ≠ 0 ∧ ∀ σ j, A.valuation ((r σ).coeff j) ≤ A.valuation ((r σ₀).coeff j₀) := by
  classical
  set N := Finset.univ.sup (fun σ => (r σ).natDegree) + 1 with hN
  have hlt : ∀ σ, (r σ).natDegree < N := fun σ =>
    Nat.lt_succ_of_le (Finset.le_sup (f := fun σ => (r σ).natDegree) (Finset.mem_univ σ))
  set t : Finset (κ × ℕ) := Finset.univ ×ˢ Finset.range N with ht
  have hmem : (σ₁, (r σ₁).natDegree) ∈ t :=
    Finset.mk_mem_product (Finset.mem_univ _) (Finset.mem_range.mpr (hlt σ₁))
  obtain ⟨⟨σ₀, j₀⟩, hp₀, hmax⟩ :=
    t.exists_max_image (fun p : κ × ℕ => A.valuation ((r p.1).coeff p.2)) ⟨_, hmem⟩
  refine ⟨σ₀, j₀, ?_, fun σ j => ?_⟩
  · intro h0
    have h := hmax _ hmem
    rw [h0, map_zero, le_zero_iff, map_eq_zero, Polynomial.coeff_natDegree,
      Polynomial.leadingCoeff_eq_zero] at h
    exact hσ₁ h
  · by_cases hj : j < N
    · exact hmax (σ, j) (Finset.mk_mem_product (Finset.mem_univ _) (Finset.mem_range.mpr hj))
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (hlt σ) (not_lt.mp hj)),
        map_zero]
      exact zero_le'

omit [Fintype κ] in

theorem coeff_C_mul_mem (r : κ → L[X]) {c : L} (hc : c ≠ 0)
    (hmax : ∀ σ j, A.valuation ((r σ).coeff j) ≤ A.valuation c) (σ : κ) (j : ℕ) :
    (C c⁻¹ * r σ).coeff j ∈ A := by
  rw [coeff_C_mul, ← A.valuation_le_one_iff, map_mul, map_inv₀]
  have hv : A.valuation c ≠ 0 := by rwa [ne_eq, map_eq_zero]
  calc (A.valuation c)⁻¹ * A.valuation ((r σ).coeff j)
      ≤ (A.valuation c)⁻¹ * A.valuation c := by gcongr; exact hmax σ j
    _ = 1 := inv_mul_cancel₀ hv

variable (htrL : Transcendental L f)

theorem eq_zero_of_sum_aeval_mul_eq_zero
    (huniq : ∀ q q' : κ → (ResidueField A)[X],
      ∑ σ, aeval (fb R f hf) (q σ) * zres R z hz σ = ∑ σ, aeval (fb R f hf) (q' σ) * zres R z hz σ →
      q = q')
    (r : κ → L[X]) (hsum : ∑ σ, aeval f (r σ) * z σ = 0) : ∀ σ, r σ = 0 := by
  by_contra hne
  obtain ⟨σ₁, hσ₁⟩ := not_forall.mp hne
  obtain ⟨σ₀, j₀, hc, hmax⟩ := exists_max_coeff (A := A) r hσ₁
  set c := (r σ₀).coeff j₀ with hcdef
  set r' : κ → L[X] := fun σ => C c⁻¹ * r σ with hr'
  obtain ⟨rA, hrA⟩ := exists_lift (A := A) r' (fun σ j => coeff_C_mul_mem r hc hmax σ j)
  have hsum' : ∀ i, ((sumO R f hf z hz rA i : (R i).integers) : F) = 0 := by
    intro i
    rw [coe_sumO]
    simp_rw [hrA, hr', map_mul, aeval_C, mul_assoc, ← Finset.mul_sum, hsum, mul_zero]
  have h0 : ∀ i, (R i).residue (sumO R f hf z hz rA i) = 0 := by
    intro i
    have : sumO R f hf z hz rA i = 0 := Subtype.ext (hsum' i)
    rw [this, map_zero]
  refine false_of_coeff_eq_one R f hf z hz huniq rA h0 (σ₀ := σ₀) (j₀ := j₀) ?_
  have h := congrArg (fun p : L[X] => p.coeff j₀) (hrA σ₀)
  simp only [coeff_map] at h
  rw [show A.subtype ((rA σ₀).coeff j₀) = (((rA σ₀).coeff j₀ : A) : L) from rfl] at h
  rw [h, hr']
  simp only [coeff_C_mul]
  rw [← hcdef, inv_mul_cancel₀ hc]

include htrL in

theorem isW_div_of_mul_aeval_eq_sum
    (huniq : ∀ q q' : κ → (ResidueField A)[X],
      ∑ σ, aeval (fb R f hf) (q σ) * zres R z hz σ = ∑ σ, aeval (fb R f hf) (q' σ) * zres R z hz σ →
      q = q')
    (b : F) (hb : ∀ i, b ∈ (R i).integers) (s : L[X]) (hs : s ≠ 0) (r : κ → L[X])
    (hbs : b * aeval f s = ∑ σ, aeval f (r σ) * z σ) (σ : κ) :
    IsW A f (aeval f (r σ) / aeval f s) := by
  classical
  have hs0 : aeval f s ≠ 0 := fun h => hs (transcendental_iff.mp htrL s h)

  set ts := Finset.range (s.natDegree + 1) with hts
  have hmem : s.natDegree ∈ ts := Finset.self_mem_range_succ _
  obtain ⟨e₀, he₀, hmaxs⟩ := ts.exists_max_image (fun e => A.valuation (s.coeff e)) ⟨_, hmem⟩
  have hmaxs' : ∀ e, A.valuation (s.coeff e) ≤ A.valuation (s.coeff e₀) := by
    intro e
    by_cases he : e < s.natDegree + 1
    · exact hmaxs e (Finset.mem_range.mpr he)
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), map_zero]; exact zero_le'
  have hce : s.coeff e₀ ≠ 0 := by
    intro h0
    have h := hmaxs _ hmem
    rw [h0, map_zero, le_zero_iff, map_eq_zero, Polynomial.coeff_natDegree,
      Polynomial.leadingCoeff_eq_zero] at h
    exact hs h
  by_cases hA : ∀ τ j, A.valuation ((r τ).coeff j) ≤ A.valuation (s.coeff e₀)
  ·
    set c := s.coeff e₀ with hcdef
    refine ⟨C c⁻¹ * r σ, C c⁻¹ * s, fun j => coeff_C_mul_mem r hce hA σ j, ⟨fun j => ?_, e₀, ?_⟩, ?_⟩
    · rw [A.valuation_le_one_iff]
      exact coeff_C_mul_mem (fun _ : Unit => s) hce (fun _ j => hmaxs' j) () j
    · rw [coeff_C_mul, ← hcdef, inv_mul_cancel₀ hce, map_one]
    · rw [map_mul, map_mul, aeval_C]
      field_simp
  ·
    exfalso
    simp only [not_forall, not_le] at hA
    obtain ⟨τ₁, j₁, hlt₁⟩ := hA
    have hτ₁ : r τ₁ ≠ 0 := by
      intro h0
      rw [h0, coeff_zero, map_zero] at hlt₁
      exact not_lt_zero hlt₁
    obtain ⟨σ₀, j₀, hc, hmax⟩ := exists_max_coeff (A := A) r hτ₁
    set c := (r σ₀).coeff j₀ with hcdef
    have hslt : ∀ e, A.valuation ((C c⁻¹ * s).coeff e) < 1 := by
      intro e
      rw [coeff_C_mul, map_mul, map_inv₀]
      have hv : A.valuation c ≠ 0 := by rwa [ne_eq, map_eq_zero]
      have hlt : A.valuation (s.coeff e) < A.valuation c :=
        lt_of_le_of_lt (hmaxs' e) (lt_of_lt_of_le hlt₁ (hmax τ₁ j₁))
      rw [inv_mul_lt_one₀ (zero_lt_iff.mpr hv)]
      exact hlt
    obtain ⟨sA, hsA⟩ := exists_map_subtype_eq A
      (fun e => (A.valuation_le_one_iff _).mp (hslt e).le)
    have hsA0 : sA.map (IsLocalRing.residue A) = 0 := by
      rw [map_residue_eq_zero_iff]
      intro j
      have h := hslt j
      rwa [← hsA, coeff_map] at h
    set r' : κ → L[X] := fun τ => C c⁻¹ * r τ with hr'
    obtain ⟨rA, hrA⟩ := exists_lift (A := A) r' (fun τ j => coeff_C_mul_mem r hc hmax τ j)
    have hcoe : ∀ i, ((sumO R f hf z hz rA i : (R i).integers) : F) =
        ((evalO (R i) ⟨f, hf i⟩ sA * ⟨b, hb i⟩ : (R i).integers) : F) := by
      intro i
      rw [coe_sumO, Subring.coe_mul, coe_evalO, hsA]
      change _ = aeval f (C c⁻¹ * s) * b
      simp_rw [hrA, hr', map_mul, aeval_C, mul_assoc, ← Finset.mul_sum, ← hbs]
      ring
    have h0 : ∀ i, (R i).residue (sumO R f hf z hz rA i) = 0 := by
      intro i
      rw [show sumO R f hf z hz rA i = evalO (R i) ⟨f, hf i⟩ sA * ⟨b, hb i⟩ from
        Subtype.ext (hcoe i), map_mul, residue_evalO, hsA0, map_zero, zero_mul]
    refine false_of_coeff_eq_one R f hf z hz huniq rA h0 (σ₀ := σ₀) (j₀ := j₀) ?_
    have h := congrArg (fun p : L[X] => p.coeff j₀) (hrA σ₀)
    simp only [coeff_map] at h
    rw [show A.subtype ((rA σ₀).coeff j₀) = (((rA σ₀).coeff j₀ : A) : L) from rfl] at h
    rw [h, hr']
    simp only [coeff_C_mul]
    rw [← hcdef, inv_mul_cancel₀ hc]

end sums

end Family

section Integrality

variable {L : Type*} [Field L] [IsAlgClosed L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {ι : Type*} [Fintype ι] {Fb : ι → Type*} [∀ i, Field (Fb i)]
  [∀ i, Algebra (ResidueField A) (Fb i)]
variable (R : ∀ i, RegularProlongation A F (Fb i))
  (hR : Function.Injective fun i => (R i).integers)
  (f : F) (hf : ∀ i, f ∈ (R i).integers)
  (hfd : FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F)
  (htr : ∀ i, Transcendental (ResidueField A) ((R i).residue ⟨f, hf i⟩))
  (heq : ∑ i, Module.finrank (IntermediateField.adjoin (ResidueField A)
      ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)
    = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F)

omit [IsAlgClosed L] [Fintype ι] in

theorem isIntegralElem_of_forall_mem {S : Type*} [CommRing S] (φ : S →+* F) (x : F)
    (hx : ∀ V : ValuationSubring F, (∀ r, φ r ∈ V) → x ∈ V) : φ.IsIntegralElem x := by
  set s : Set F := Set.range φ with hs
  have hmem : x ∈ (⨅ V : {V : ValuationSubring F // s ⊆ V.toSubring}, V.1.toSubring) := by
    refine Subring.mem_iInf.mpr ?_
    rintro ⟨V, hV⟩
    exact hx V (fun r => hV ⟨r, rfl⟩)
  rw [iInf_valuationSubring_superset] at hmem
  have hint : IsIntegral (Subring.closure s) x :=
    (mem_integralClosure_iff _ _).mp (Subalgebra.mem_toSubring.mp hmem)
  obtain ⟨P, hPm, hPx⟩ := hint
  have hTle : Subring.closure s ≤ φ.range :=
    Subring.closure_le.mpr (by rintro _ ⟨r, rfl⟩; exact ⟨r, rfl⟩)
  have hP'm : (P.map (algebraMap (Subring.closure s) F)).Monic := hPm.map _
  have hP'x : (P.map (algebraMap (Subring.closure s) F)).eval x = 0 := by
    rw [eval_map]; exact hPx
  have hlifts : P.map (algebraMap (Subring.closure s) F) ∈ lifts φ := by
    rw [lifts_iff_coeff_lifts]
    intro n
    rw [coeff_map]
    exact hTle (P.coeff n).2
  obtain ⟨q, hq, -, hqm⟩ := lifts_and_degree_eq_and_monic hlifts hP'm
  refine ⟨q, hqm, ?_⟩
  rw [← eval_map, hq, hP'x]

include hR htr heq hfd in

theorem isIntegral_residue (u : F) (hu : ∀ i, u ∈ (R i).integers) (huT : IsT (L := L) f u)
    (i : ι) :
    IsIntegral (Algebra.adjoin (ResidueField A) {(R i).residue ⟨f, hf i⟩})
      ((R i).residue ⟨u, hu i⟩) := by
  haveI := hfd
  haveI : Nonempty ι := ⟨i⟩
  set D := Algebra.adjoin L ({f} : Set F) with hD
  set xO : (R i).integers := ⟨f, hf i⟩ with hxO

  have hint : IsIntegral D u := by
    refine isIntegralElem_of_forall_mem (algebraMap D F) u fun V hV => huT V ?_ ?_
    · intro c
      have := hV (algebraMap L D c)
      rwa [← IsScalarTower.algebraMap_apply] at this
    · exact hV ⟨f, Algebra.self_mem_adjoin_singleton L f⟩

  have h₃ : ∀ V : ValuationSubring F,
      (∀ e : F, e ∈ IntermediateField.adjoin L {(xO : F)} → (e ∈ V ↔ e ∈ (R i).integers)) →
        u ∈ V := by
    intro V hV
    obtain ⟨j, rfl⟩ :=
      AlgebraicCurve.RegularProlongation.exists_eq_integers_of_forall_mem_adjoin_iff_of_sum_finrank_eq_of_isAlgClosed
        A Fb R hR f hf htr heq i V hV
    exact hu j
  have hcoeff := AlgebraicCurve.RegularProlongation.coe_minpoly_adjoin_coeff_mem_integers
    A (R i) xO (htr i) u hint h₃

  set φ : A[X] →+* F := eval₂RingHom ((algebraMap L F).comp A.subtype) f with hφ
  set Q : F[X] := (minpoly D u).map (algebraMap D F) with hQ
  have hQm : Q.Monic := (minpoly.monic hint).map _
  have hQu : Q.eval u = 0 := by rw [hQ, eval_map, ← aeval_def]; exact minpoly.aeval D u
  have hlifts : Q ∈ lifts φ := by
    rw [lifts_iff_coeff_lifts]
    intro n
    rw [hQ, coeff_map]
    have hmemD : (((minpoly D u).coeff n : D) : F) ∈ (aeval (R := L) f).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval]; exact ((minpoly D u).coeff n).2
    obtain ⟨r, hr⟩ := (AlgHom.mem_range _).1 hmemD
    have hrA : ∀ l, r.coeff l ∈ A := fun l =>
      AlgebraicCurve.RegularProlongation.coeff_mem_of_aeval_mem_integers A (R i) xO (htr i) r
        (by rw [show ((xO : F)) = f from rfl, hr]; exact hcoeff n) l
    obtain ⟨rA, rfl⟩ := exists_map_subtype_eq A hrA
    refine ⟨rA, ?_⟩
    rw [show algebraMap D F ((minpoly D u).coeff n) = (((minpoly D u).coeff n : D) : F) from rfl,
      ← hr, hφ]
    change eval₂ ((algebraMap L F).comp A.subtype) f rA = _
    rw [← eval₂_map, ← aeval_def]
  obtain ⟨P, hP, -, hPm⟩ := lifts_and_degree_eq_and_monic hlifts hQm
  have hPu : P.eval₂ φ u = 0 := by rw [eval₂_eq_eval_map, hP, hQu]
  exact AlgebraicCurve.RegularProlongation.isIntegral_adjoin_residue_of_exists_monic_bivariate_eval_eq_zero
    A (R i) xO ⟨u, hu i⟩ ⟨P, hPm, hPu⟩

include hR htr heq hfd in

theorem exists_generators :
    ∃ (m : ℕ) (g : Fin m → ∀ i, Fb i), ∀ h ∈ resMod R f,
      ∃ q : Fin m → (ResidueField A)[X], h = ∑ c, aeval (fb R f hf) (q c) * g c := by
  classical
  haveI := hfd
  haveI : IsAlgClosed (ResidueField A) := ValuationSubring.isAlgClosed_residueField A
  set k := ResidueField A with hk

  have hgen : ∀ i, ∃ (m : ℕ) (s : Fin m → Fb i), ∀ η : Fb i,
      IsIntegral (Algebra.adjoin k {(R i).residue ⟨f, hf i⟩}) η →
        ∃ q : Fin m → k[X], η = ∑ a, aeval ((R i).residue ⟨f, hf i⟩) (q a) * s a := by
    intro i
    set x := (R i).residue ⟨f, hf i⟩ with hx
    set D := Algebra.adjoin k ({x} : Set (Fb i)) with hD
    haveI : FiniteDimensional (IntermediateField.adjoin k ({x} : Set (Fb i))) (Fb i) :=
      AlgebraicCurve.RegularProlongation.finiteDimensional_adjoin_residue_of_sum_finrank_eq
        A Fb R hR f hf htr heq i
    haveI : Module.Finite D (integralClosure D (Fb i)) :=
      Algebra.finite_integralClosure_adjoin_singleton_of_isAlgClosed x (htr i) inferInstance
    obtain ⟨S, hS⟩ := (Module.Finite.fg_top : (⊤ : Submodule D (integralClosure D (Fb i))).FG)
    set e := S.equivFin with he
    refine ⟨S.card, fun a => ((e.symm a : S) : integralClosure D (Fb i)), fun η hη => ?_⟩
    have hmem : (⟨η, hη⟩ : integralClosure D (Fb i)) ∈ Submodule.span D (S : Set _) := by
      rw [hS]; exact Submodule.mem_top
    obtain ⟨c, hc⟩ := Submodule.mem_span_finset'.mp hmem

    have hcpoly : ∀ a, ∃ q : k[X], ((c a : D) : Fb i) = aeval x q := by
      intro a
      have h : ((c a : D) : Fb i) ∈ (aeval (R := k) x).range := by
        rw [← Algebra.adjoin_singleton_eq_range_aeval]; exact (c a).2
      obtain ⟨q, hq⟩ := (AlgHom.mem_range _).1 h
      exact ⟨q, hq.symm⟩
    choose q hq using hcpoly
    refine ⟨fun a => q (e.symm a), ?_⟩
    have h := congrArg (fun y : integralClosure D (Fb i) => (y : Fb i)) hc
    dsimp only at h
    rw [AddSubmonoidClass.coe_finsetSum] at h
    rw [← h, ← e.symm.sum_comp]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Subalgebra.coe_smul, Algebra.smul_def, ← hq]
    rfl
  choose m s hs using hgen

  set Γ := Σ i, Fin (m i)
  set eΓ := Fintype.equivFin Γ with heΓ
  refine ⟨Fintype.card Γ, fun c => Pi.single (eΓ.symm c).1 (s _ (eΓ.symm c).2), ?_⟩
  rintro h ⟨u, hu, huT, hru⟩
  have hq : ∀ i, ∃ q : Fin (m i) → k[X],
      h i = ∑ a, aeval ((R i).residue ⟨f, hf i⟩) (q a) * s i a := fun i => by
    obtain ⟨q, hq⟩ := hs i (h i) (by rw [← hru i]; exact isIntegral_residue R hR f hf hfd htr heq u hu huT i)
    exact ⟨q, hq⟩
  choose q hq using hq
  refine ⟨fun c => q (eΓ.symm c).1 (eΓ.symm c).2, ?_⟩
  set φ : Γ → ∀ i, Fb i := fun c => aeval (fb R f hf) (q c.1 c.2) * Pi.single c.1 (s c.1 c.2)
    with hφ
  rw [show (∑ c, aeval (fb R f hf) (q (eΓ.symm c).1 (eΓ.symm c).2) *
      Pi.single (eΓ.symm c).1 (s (eΓ.symm c).1 (eΓ.symm c).2)) = ∑ c, φ (eΓ.symm c) from rfl,
    Equiv.sum_comp eΓ.symm φ, hφ, Fintype.sum_sigma]
  conv_lhs => rw [← Finset.univ_sum_single h]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hterm : ∀ a : Fin (m i), aeval (fb R f hf) (q i a) * Pi.single i (s i a) =
      Pi.single i (aeval ((R i).residue ⟨f, hf i⟩) (q i a) * s i a) := by
    intro a
    funext j
    rw [Pi.mul_apply, ← Pi.single_mul_right_apply, aeval_fb_apply]
  simp_rw [hterm]
  rw [hq i]
  exact map_sum (AddMonoidHom.single Fb i) _ Finset.univ

end Integrality

section Main

variable {L : Type*} [Field L] [IsAlgClosed L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {ι : Type*} [Fintype ι] {Fb : ι → Type*} [∀ i, Field (Fb i)]
  [∀ i, Algebra (ResidueField A) (Fb i)]
variable (R : ∀ i, RegularProlongation A F (Fb i))
  (hR : Function.Injective fun i => (R i).integers)
  (f : F) (hf : ∀ i, f ∈ (R i).integers) (htrL : Transcendental L f)
  (hfd : FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F)
  (htr : ∀ i, Transcendental (ResidueField A) ((R i).residue ⟨f, hf i⟩))
  (heq : ∑ i, Module.finrank (IntermediateField.adjoin (ResidueField A)
      ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)
    = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F)

include hR hfd htr heq in

theorem exists_raw :
    ∃ (d : ℕ) (z : Fin d → F) (hz : ∀ σ i, z σ ∈ (R i).integers),
      (∀ σ, IsT (L := L) f (z σ)) ∧
      (∀ q q' : Fin d → (ResidueField A)[X],
        ∑ σ, aeval (fb R f hf) (q σ) * zres R z hz σ =
          ∑ σ, aeval (fb R f hf) (q' σ) * zres R z hz σ → q = q') ∧
      (∀ h ∈ resMod R f, ∃ q : Fin d → (ResidueField A)[X],
        h = ∑ σ, aeval (fb R f hf) (q σ) * zres R z hz σ) ∧
      (∀ (d' : ℕ) (zb' : Fin d' → ∀ i, Fb i), (∀ τ, zb' τ ∈ resMod R f) →
        (∀ q q' : Fin d' → (ResidueField A)[X],
          ∑ τ, aeval (fb R f hf) (q τ) * zb' τ = ∑ τ, aeval (fb R f hf) (q' τ) * zb' τ → q = q') →
        d' ≤ d) := by
  obtain ⟨m, g, hg⟩ := exists_generators R hR f hf hfd htr heq
  obtain ⟨d, zb, hzbM, huniq, hgen, hcard⟩ :=
    exists_polynomial_basis (fb R f hf) (resMod R f) (fun _ hh => fb_mul_mem R f hf hh)
      (aeval_fb_mul_eq_zero R f hf htr) g hg
  choose u hu huT hru using fun σ => (hzbM σ : zb σ ∈ resSet R f)
  have hzres : zres R u hu = zb := by
    funext σ i
    exact hru σ i
  refine ⟨d, u, hu, huT, ?_, ?_, hcard⟩
  · rw [hzres]; exact huniq
  · rw [hzres]; exact hgen

section raw

variable {d : ℕ} (z : Fin d → F) (hz : ∀ σ i, z σ ∈ (R i).integers)
  (huniq : ∀ q q' : Fin d → (ResidueField A)[X],
    ∑ σ, aeval (fb R f hf) (q σ) * zres R z hz σ =
      ∑ σ, aeval (fb R f hf) (q' σ) * zres R z hz σ → q = q')

include huniq in
omit [IsAlgClosed L] [Fintype ι] in

theorem linearIndependent_algebraAdjoin :
    LinearIndependent (Algebra.adjoin L ({f} : Set F)) z := by
  classical
  rw [linearIndependent_iff']
  intro t g hsum σ hσ
  have hg : ∀ σ, ∃ p : L[X], aeval f p = (g σ : F) := fun σ => by
    have h : (g σ : F) ∈ (aeval (R := L) f).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval]; exact (g σ).2
    exact (AlgHom.mem_range _).1 h
  choose p hp using hg
  set r : Fin d → L[X] := fun σ => if σ ∈ t then p σ else 0 with hr
  have hsum' : ∑ σ, aeval f (r σ) * z σ = 0 := by
    rw [← hsum, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun σ => σ ∈ t)]
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
    have h0 : ∑ σ ∈ Finset.univ.filter (fun σ => σ ∉ t), aeval f (r σ) * z σ = 0 :=
      Finset.sum_eq_zero fun σ hσ => by
        rw [Finset.mem_filter] at hσ
        simp [hr, hσ.2]
    rw [h0, add_zero]
    refine Finset.sum_congr rfl fun σ hσ => ?_
    rw [hr]
    simp only [hσ, if_true]
    rw [hp, Subalgebra.smul_def, smul_eq_mul]
  have hzero := eq_zero_of_sum_aeval_mul_eq_zero R f hf z hz huniq r hsum' σ
  simp only [hr, hσ, if_true] at hzero
  apply Subtype.ext
  rw [← hp σ, hzero, map_zero]
  rfl

include huniq in
omit [IsAlgClosed L] [Fintype ι] in
open scoped IntermediateField.algebraAdjoinAdjoin in

theorem linearIndependent_adjoin :
    LinearIndependent (IntermediateField.adjoin L ({f} : Set F)) z :=
  (LinearIndependent.iff_fractionRing (Algebra.adjoin L ({f} : Set F))
    (IntermediateField.adjoin L ({f} : Set F))).mp (linearIndependent_algebraAdjoin R f hf z hz huniq)

end raw

omit [IsAlgClosed L] in

theorem exists_smul_mem_forall (x : F) : ∃ c : L, c ≠ 0 ∧ ∀ i, c • x ∈ (R i).integers := by
  classical
  by_cases hx : x = 0
  · exact ⟨1, one_ne_zero, fun i => by rw [hx, smul_zero]; exact zero_mem _⟩
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, one_ne_zero, fun i => (IsEmpty.false i).elim⟩
  choose c hc hres using fun i => (R i).exists_smul_mem x hx
  have hc0 : ∀ i, c i ≠ 0 := fun i => (R i).smul_const_ne_zero (hc i) (hres i)
  obtain ⟨i₁, -, hmin⟩ := Finset.univ.exists_min_image (fun i => A.valuation (c i)) Finset.univ_nonempty
  refine ⟨c i₁, hc0 i₁, fun i => ?_⟩
  have hdiv : c i₁ / c i ∈ A := by
    rw [← A.valuation_le_one_iff, map_div₀]
    exact div_le_one_of_le₀ (hmin i (Finset.mem_univ i)) zero_le'
  have h : c i₁ • x = algebraMap L F (c i₁ / c i) * (c i • x) := by
    rw [Algebra.smul_def, Algebra.smul_def, ← mul_assoc, ← map_mul, div_mul_cancel₀ _ (hc0 i)]
  rw [h]
  exact mul_mem (((R i).algebraMap_mem_iff _).mpr hdiv) (hc i)

include hR htrL hfd htr heq in

theorem finrank_le {d : ℕ}
    (hcard : ∀ (d' : ℕ) (zb' : Fin d' → ∀ i, Fb i), (∀ τ, zb' τ ∈ resMod R f) →
      (∀ q q' : Fin d' → (ResidueField A)[X],
        ∑ τ, aeval (fb R f hf) (q τ) * zb' τ = ∑ τ, aeval (fb R f hf) (q' τ) * zb' τ → q = q') →
      d' ≤ d) :
    Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F ≤ d := by
  classical
  haveI := hfd
  rcases isEmpty_or_nonempty ι with hι | hι
  ·
    rw [← heq, Finset.univ_eq_empty, Finset.sum_empty]
    exact Nat.zero_le _
  haveI := hι
  obtain ⟨i₀⟩ := hι
  set K := IntermediateField.adjoin L ({f} : Set F) with hK
  have hcomplete : ∀ W : ValuationSubring F,
      (∀ e ∈ IntermediateField.adjoin L ({f} : Set F), e ∈ W ↔ e ∈ (R i₀).integers) →
        ∃ j, W = (R j).integers := fun W hW =>
    AlgebraicCurve.RegularProlongation.exists_eq_integers_of_forall_mem_adjoin_iff_of_sum_finrank_eq_of_isAlgClosed
      A Fb R hR f hf htr heq i₀ W hW
  obtain ⟨d', z', hz'O, hz'T, huniq', hspan'⟩ :=
    AlgebraicCurve.RegularProlongation.exists_gaussBasis_mem_integralClosure_piResidue_uniqueRepr_of_sum_finrank_eq
      A Fb R hR f hf htrL hfd htr i₀ hcomplete heq

  have hspan : (⊤ : Submodule K F) ≤ Submodule.span K (Set.range z') := by
    intro x _
    obtain ⟨c, hc, hcx⟩ := exists_smul_mem_forall R x
    obtain ⟨κ, -, hκ⟩ := hspan' (c • x) hcx
    have hmem : c • x ∈ Submodule.span K (Set.range z') := by
      rw [hκ]
      refine Submodule.sum_mem _ fun τ _ => ?_
      rw [show (κ τ : F) * z' τ = κ τ • z' τ from rfl]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨τ, rfl⟩)
    have hx : x = (algebraMap L K c⁻¹) • (c • x) := by
      rw [algebraMap_smul, inv_smul_smul₀ hc]
    rw [hx]
    exact Submodule.smul_mem _ _ hmem
  have h1 : Module.finrank K F ≤ d' := by
    have h := finrank_range_le_card (R := K) z'
    rw [Fintype.card_fin] at h
    calc Module.finrank K F = Module.finrank K (⊤ : Submodule K F) := (finrank_top K F).symm
      _ ≤ Module.finrank K (Submodule.span K (Set.range z')) := Submodule.finrank_mono hspan
      _ ≤ d' := h

  have h2 : d' ≤ d := by
    refine hcard d' (fun τ i => (R i).residue ⟨z' τ, hz'O τ i⟩)
      (fun τ => ⟨z' τ, hz'O τ, hz'T τ, fun i => rfl⟩) fun q q' hqq' => huniq' q q' fun i => ?_
    have h := congrFun hqq' i
    simp only [Finset.sum_apply, Pi.mul_apply, aeval_fb_apply] at h
    exact h
  exact h1.trans h2

end Main

section coords

variable {L : Type*} [Field L] [IsAlgClosed L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {ι : Type*} [Fintype ι] {Fb : ι → Type*} [∀ i, Field (Fb i)]
  [∀ i, Algebra (ResidueField A) (Fb i)]
variable (R : ∀ i, RegularProlongation A F (Fb i))
  (hR : Function.Injective fun i => (R i).integers)
  (f : F) (hf : ∀ i, f ∈ (R i).integers) (htrL : Transcendental L f)
  (hfd : FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F)
  (htr : ∀ i, Transcendental (ResidueField A) ((R i).residue ⟨f, hf i⟩))
  (heq : ∑ i, Module.finrank (IntermediateField.adjoin (ResidueField A)
      ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)
    = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F)
variable {d : ℕ} (z : Fin d → F) (hz : ∀ σ i, z σ ∈ (R i).integers)
  (hzT : ∀ σ, IsT (L := L) f (z σ))
  (huniq : ∀ q q' : Fin d → (ResidueField A)[X],
    ∑ σ, aeval (fb R f hf) (q σ) * zres R z hz σ =
      ∑ σ, aeval (fb R f hf) (q' σ) * zres R z hz σ → q = q')
  (hgen : ∀ h ∈ resMod R f, ∃ q : Fin d → (ResidueField A)[X],
    h = ∑ σ, aeval (fb R f hf) (q σ) * zres R z hz σ)
  (hd : Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F = d)

include htrL hfd huniq hd in
omit [IsAlgClosed L] [Fintype ι] in

theorem exists_coords (b : F) (hb : ∀ i, b ∈ (R i).integers) :
    ∃ w : Fin d → F, (∀ σ, IsW A f (w σ)) ∧ b = ∑ σ, w σ * z σ := by
  classical
  haveI := hfd
  set K := IntermediateField.adjoin L ({f} : Set F) with hK
  have hli := linearIndependent_adjoin R f hf z hz huniq
  let Bz : Module.Basis (Fin d) K F :=
    basisOfLinearIndependentOfCardEqFinrank' z hli (by rw [Fintype.card_fin, hd])
  set g : Fin d → K := fun σ => Bz.repr b σ with hg
  have hb_eq : b = ∑ σ, (g σ : F) * z σ := by
    conv_lhs => rw [← Bz.sum_repr b]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [coe_basisOfLinearIndependentOfCardEqFinrank', IntermediateField.smul_def, smul_eq_mul]

  have hfrac : ∀ σ, ∃ PQ : L[X] × L[X], aeval f PQ.2 ≠ 0 ∧
      (g σ : F) = aeval f PQ.1 / aeval f PQ.2 := by
    intro σ
    obtain ⟨P, Q, hPQ⟩ := (IntermediateField.mem_adjoin_simple_iff L (g σ : F)).mp (g σ).2
    by_cases hQ : aeval f Q = 0
    · refine ⟨(0, 1), by simp, ?_⟩
      rw [hPQ, hQ, div_zero]
      simp
    · exact ⟨(P, Q), hQ, hPQ⟩
  choose PQ hQne hPQ using hfrac
  set s : L[X] := ∏ σ, (PQ σ).2 with hs
  have hs0 : aeval f s ≠ 0 := by
    rw [hs, map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun σ _ => hQne σ
  have hs0' : s ≠ 0 := by
    rintro h
    rw [h, map_zero] at hs0
    exact hs0 rfl
  set r : Fin d → L[X] := fun σ => (∏ τ ∈ Finset.univ.erase σ, (PQ τ).2) * (PQ σ).1 with hr
  have hgr : ∀ σ, (g σ : F) * aeval f s = aeval f (r σ) := by
    intro σ
    rw [hPQ σ, hr]
    simp only [map_mul, map_prod]
    rw [hs, map_prod, ← Finset.mul_prod_erase Finset.univ (fun τ => aeval f (PQ τ).2)
      (Finset.mem_univ σ)]
    have hQ := hQne σ
    field_simp
  have hbs : b * aeval f s = ∑ σ, aeval f (r σ) * z σ := by
    rw [hb_eq, Finset.sum_mul]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [mul_right_comm, hgr σ]
  refine ⟨fun σ => (g σ : F), fun σ => ?_, hb_eq⟩
  have h := isW_div_of_mul_aeval_eq_sum R f hf z hz htrL huniq b hb s hs0' r hbs σ
  rwa [← hgr σ, mul_div_cancel_right₀ _ hs0] at h

include hR htrL hfd htr heq huniq hgen hd in
omit [IsAlgClosed L] in

theorem exists_residual (y : F) (w : Fin d → F) (hyT : IsT (L := L) f y)
    (hw : ∀ σ, IsW A f (w σ)) (hy : y = ∑ σ, w σ * z σ) :
    ∃ (C₁ : Fin d → L[X]) (μ : Fin d → F), (∀ σ j, (C₁ σ).coeff j ∈ A) ∧
      (∀ σ, IsMW A f (μ σ)) ∧ y = ∑ σ, (aeval f (C₁ σ) + μ σ) * z σ := by
  classical
  haveI := hfd
  set K := IntermediateField.adjoin L ({f} : Set F) with hK

  have hyO : ∀ i, y ∈ (R i).integers := fun i => by
    rw [hy]
    exact sum_mem fun σ _ => mul_mem (IsW.mem (R i) ⟨f, hf i⟩ (htr i) (hw σ)) (hz σ i)

  obtain ⟨q, hq⟩ := hgen (fun i => (R i).residue ⟨y, hyO i⟩) ⟨y, hyO, hyT, fun i => rfl⟩

  have hlift : ∀ σ, ∃ Ca : A[X], Ca.map (IsLocalRing.residue A) = q σ := fun σ =>
    Polynomial.map_surjective _ IsLocalRing.residue_surjective (q σ)
  choose Ca hCa using hlift
  set C₁ : Fin d → L[X] := fun σ => (Ca σ).map A.subtype with hC₁
  set μ : Fin d → F := fun σ => w σ - aeval f (C₁ σ) with hμ
  refine ⟨C₁, μ, fun σ j => coeff_map_subtype_mem (Ca σ) j, fun σ => ?_, ?_⟩
  swap
  · rw [hy]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [hμ]
    ring_nf

  set y' : F := y - ∑ σ, aeval f (C₁ σ) * z σ with hy'
  have hy'O : ∀ i, y' ∈ (R i).integers := fun i =>
    sub_mem (hyO i) (by rw [← coe_sumO R f hf z hz Ca i]; exact (sumO R f hf z hz Ca i).2)
  have hres0 : ∀ i, (R i).residue ⟨y', hy'O i⟩ = 0 := by
    intro i
    have h : (⟨y', hy'O i⟩ : (R i).integers) = ⟨y, hyO i⟩ - sumO R f hf z hz Ca i :=
      Subtype.ext (by rw [AddSubgroupClass.coe_sub, coe_sumO])
    rw [h, map_sub, residue_sumO, sub_eq_zero]
    have hqi := congrFun hq i
    rw [hqi]
    simp_rw [hCa]
  have hy'eq : y' = ∑ σ, μ σ * z σ := by
    rw [hy', hy, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [hμ]
    ring

  set V : Submodule L F := Submodule.span L {y'} with hV
  haveI : FiniteDimensional L V := Module.Finite.span_singleton L y'
  obtain ⟨a, u', ha, hu'O, -, hyu'⟩ :=
    AlgebraicCurve.RegularProlongation.exists_nonunit_smul_eq_of_forall_residue_eq_zero_of_sum_finrank_eq
      A Fb R hR f hf htr heq V y' hy'O (Submodule.mem_span_singleton_self y') hres0

  obtain ⟨w', hw', hu'eq⟩ := exists_coords R f hf htrL hfd z hz huniq hd u' hu'O
  have hli := linearIndependent_adjoin R f hf z hz huniq
  have haeval_mem : ∀ p : L[X], aeval f p ∈ K := fun p =>
    IntermediateField.algebra_adjoin_le_adjoin L _
      (by rw [Algebra.adjoin_singleton_eq_range_aeval]; exact ⟨p, rfl⟩)
  have hμK : ∀ τ, μ τ - (a : L) • w' τ ∈ K := fun τ =>
    sub_mem (sub_mem (IsW.mem_adjoin htrL (hw τ)) (haeval_mem _))
      (K.smul_mem (IsW.mem_adjoin htrL (hw' τ)))
  have hrel : ∑ τ, (⟨μ τ - (a : L) • w' τ, hμK τ⟩ : K) • z τ = 0 := by
    have h1 : ∑ τ, (⟨μ τ - (a : L) • w' τ, hμK τ⟩ : K) • z τ = y' - (a : L) • u' := by
      rw [hy'eq, hu'eq, Finset.smul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [IntermediateField.smul_def, smul_eq_mul, sub_mul, smul_mul_assoc]
    rw [h1, hyu', sub_self]
  have hμeq : μ σ = (a : L) • w' σ := by
    have h := Fintype.linearIndependent_iff.mp hli _ hrel σ
    rw [Subtype.ext_iff, ZeroMemClass.coe_zero] at h
    exact sub_eq_zero.mp h

  obtain ⟨p, q', hp, hq', hwq⟩ := hw' σ
  refine ⟨C (a : L) * p, q', fun j => ?_, hq', ?_⟩
  · rw [coeff_C_mul, map_mul]
    refine mul_lt_one_of_lt_of_le ?_ ((A.valuation_le_one_iff _).mpr (hp j))
    exact (ValuationSubring.valuation_lt_one_iff A a).mp
      ((IsLocalRing.mem_maximalIdeal a).mpr ha)
  · rw [hμeq, map_mul, aeval_C, ← hwq, Algebra.smul_def, mul_assoc]

end coords

section Assembly

variable {L : Type*} [Field L] [IsAlgClosed L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {ι : Type*} [Fintype ι] {Fb : ι → Type*} [∀ i, Field (Fb i)]
  [∀ i, Algebra (ResidueField A) (Fb i)]

theorem main (R : ∀ i, RegularProlongation A F (Fb i))
    (hR : Function.Injective fun i => (R i).integers)
    (f : F) (hf : ∀ i, f ∈ (R i).integers) (htrL : Transcendental L f)
    (hfd : FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F)
    (htr : ∀ i, Transcendental (ResidueField A) ((R i).residue ⟨f, hf i⟩))
    (heq : ∑ i, Module.finrank (IntermediateField.adjoin (ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)
      = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F) :
    ∃ z : Fin (Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F) → F,
      (∀ σ i, z σ ∈ (R i).integers) ∧
      (∀ σ, IsT (L := L) f (z σ)) ∧
      LinearIndependent (IntermediateField.adjoin L ({f} : Set F)) z ∧
      (∀ b : F, (∀ i, b ∈ (R i).integers) →
        ∃ w : Fin (Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F) → F,
          (∀ σ, IsW A f (w σ)) ∧ b = ∑ σ, w σ * z σ) ∧
      (∀ (y : F) (w : Fin (Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F) → F),
        IsT (L := L) f y → (∀ σ, IsW A f (w σ)) → y = ∑ σ, w σ * z σ →
        ∃ (C₁ : Fin (Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F) → L[X])
          (μ : Fin (Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F) → F),
          (∀ σ j, (C₁ σ).coeff j ∈ A) ∧ (∀ σ, IsMW A f (μ σ)) ∧
          y = ∑ σ, (aeval f (C₁ σ) + μ σ) * z σ) := by
  haveI := hfd
  obtain ⟨d, z, hz, hzT, huniq, hgen, hcard⟩ := exists_raw R hR f hf hfd htr heq
  have hli := linearIndependent_adjoin R f hf z hz huniq
  have h1 : Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F ≤ d :=
    finrank_le R hR f hf htrL hfd htr heq hcard
  have h2 : d ≤ Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F := by
    have h := hli.fintype_card_le_finrank
    rwa [Fintype.card_fin] at h
  have hd : Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F = d := le_antisymm h1 h2
  subst hd
  exact ⟨z, hz, hzT, hli,
    fun b hb => exists_coords R f hf htrL hfd z hz huniq rfl b hb,
    fun y w hyT hw hy => exists_residual R hR f hf htrL hfd htr heq z hz huniq hgen rfl y w hyT hw hy⟩

end Assembly

end RGSol
p2m_reactivate "P2MW.S_AlgebraicCurve_RegularProlongation_exists_gaussBasis_forall_eq_sum_aeval_add_mul_of_sum_finrank_eq.RGSol"

open RGSol in
theorem solution
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {ι : Type*} [Fintype ι] (Fb : ι → Type*) [∀ i, Field (Fb i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i))
    (hR : Function.Injective fun i => (R i).integers)
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (htrL : Transcendental L f)
    (hfd : FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F)
    (htr : ∀ i, Transcendental (IsLocalRing.ResidueField A) ((R i).residue ⟨f, hf i⟩))
    (heq : ∑ i, Module.finrank (IntermediateField.adjoin (IsLocalRing.ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)
      = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F) :
    ∃ z : Fin (Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F) → F,
      (∀ σ i, z σ ∈ (R i).integers) ∧
      (∀ σ, ∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f ∈ V → z σ ∈ V) ∧
      LinearIndependent (IntermediateField.adjoin L ({f} : Set F)) z ∧
      (∀ b : F, (∀ i, b ∈ (R i).integers) →
        ∃ w : Fin (Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F) → F,
          (∀ σ, ∃ p q : L[X], (∀ j, p.coeff j ∈ A) ∧
            ((∀ j, A.valuation (q.coeff j) ≤ 1) ∧ ∃ d, A.valuation (q.coeff d) = 1) ∧
            w σ * aeval f q = aeval f p) ∧
          b = ∑ σ, w σ * z σ) ∧
      (∀ (y : F) (w : Fin (Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F) → F),
        (∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f ∈ V → y ∈ V) →
        (∀ σ, ∃ p q : L[X], (∀ j, p.coeff j ∈ A) ∧
          ((∀ j, A.valuation (q.coeff j) ≤ 1) ∧ ∃ d, A.valuation (q.coeff d) = 1) ∧
          w σ * aeval f q = aeval f p) →
        y = ∑ σ, w σ * z σ →
        ∃ (C₁ : Fin (Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F) → L[X])
          (μ : Fin (Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F) → F),
          (∀ σ j, (C₁ σ).coeff j ∈ A) ∧
          (∀ σ, ∃ p q : L[X], (∀ j, A.valuation (p.coeff j) < 1) ∧
            ((∀ j, A.valuation (q.coeff j) ≤ 1) ∧ ∃ d, A.valuation (q.coeff d) = 1) ∧
            μ σ * aeval f q = aeval f p) ∧
          y = ∑ σ, (aeval f (C₁ σ) + μ σ) * z σ) :=
  main R hR f hf htrL hfd htr heq

end S_AlgebraicCurve_RegularProlongation_exists_gaussBasis_forall_eq_sum_aeval_add_mul_of_sum_finrank_eq
end P2MW
export P2MW.S_AlgebraicCurve_RegularProlongation_exists_gaussBasis_forall_eq_sum_aeval_add_mul_of_sum_finrank_eq (solution)
