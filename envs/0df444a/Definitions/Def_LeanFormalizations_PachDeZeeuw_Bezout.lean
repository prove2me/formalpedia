-- Prove2me | Definitions.Def_LeanFormalizations_PachDeZeeuw_Bezout
-- name    : LeanFormalizations_PachDeZeeuw_Bezout
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:46:17.255301+00:00
-- url     : https://prove2.me/theorems/cf568458-7497-47df-b297-3e5c1e89eeb2
-- title:
--   Real curve intersections and singular points
-- statement:
--   This defines singular loci, Cartesian evaluation and local implicit functions, and supplies degree bounds for singular sets and finite real zero sets of irreducible polynomials. For two nonzero plane polynomials of degrees at most $d_1,d_2$ having no common infinite irreducible factor, it proves that the common zero set is finite with at most $(d_1+d_2+1)^8$ points and derives the corresponding curve-level finite-intersection assertion.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_LeanFormalizations_PachDeZeeuw_AlgebraicPrelim
import Mathlib

set_option autoImplicit true

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


set_option linter.style.longLine false
set_option maxHeartbeats 16000000

namespace PachDeZeeuw.Algebraic

open EuclideanGeometry
open scoped Topology


section ImplicitAdapter

variable {𝕜 E₁ E₂ F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [CompleteSpace E₁]
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂] [CompleteSpace E₂]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  {f : E₁ × E₂ → F} {f' : E₁ × E₂ →L[𝕜] F} {a : E₁ × E₂} {n : WithTop ℕ∞}

omit [CompleteSpace E₁] in
 

theorem hasFDerivAt_isInvertible_partial (hf : HasFDerivAt f f' a)
    (hbij : Function.Bijective (f'.comp (ContinuousLinearMap.inr 𝕜 E₁ E₂))) :
    ((fderiv 𝕜 f a) ∘L (ContinuousLinearMap.inr 𝕜 E₁ E₂)).IsInvertible := by
  have hfderiv : fderiv 𝕜 f a = f' := hf.fderiv
  have hker : (f'.comp (ContinuousLinearMap.inr 𝕜 E₁ E₂)).ker = ⊥ := by
    rw [LinearMap.ker_eq_bot]; exact hbij.1
  have hrange : (f'.comp (ContinuousLinearMap.inr 𝕜 E₁ E₂)).range = ⊤ := by
    rw [LinearMap.range_eq_top]; exact hbij.2
  have hinv : (f'.comp (ContinuousLinearMap.inr 𝕜 E₁ E₂)).IsInvertible :=
    ⟨ContinuousLinearEquiv.ofBijective _ hker hrange,
      ContinuousLinearEquiv.coe_ofBijective _ hker hrange⟩
  rwa [hfderiv]


noncomputable def cdImplicitFunction (hf : ContDiffAt 𝕜 n f a) (hn : n ≠ 0)
    (hinv : ((fderiv 𝕜 f a) ∘L (ContinuousLinearMap.inr 𝕜 E₁ E₂)).IsInvertible) :
    E₁ → E₂ :=
  hf.implicitFunction hn hinv

 
theorem cdApplyImplicitFunction (hf : ContDiffAt 𝕜 n f a) (hn : n ≠ 0)
    (hinv : ((fderiv 𝕜 f a) ∘L (ContinuousLinearMap.inr 𝕜 E₁ E₂)).IsInvertible) :
    ∀ᶠ x in 𝓝 a.1, f (x, cdImplicitFunction hf hn hinv x) = f a :=
  hf.eventually_apply_implicitFunction hn hinv

end ImplicitAdapter

 
lemma degreeOf_coeff_curry0_le (p : MvPolynomial (Fin 2) ℝ) (k : ℕ) :
    MvPolynomial.degreeOf (0 : Fin 1) ((Curry0 p).coeff k) ≤ MvPolynomial.degreeOf (1 : Fin 2) p := by
  simpa [Curry0] using
    (MvPolynomial.degreeOf_coeff_finSuccEquiv (R := ℝ) (n := 1) (p := p) (j := 0) (i := k))


lemma degreeOf_sylvester_entry_bound
    (p q : MvPolynomial (Fin 2) ℝ)
    {d₁ d₂ : ℕ}
    (i j : Fin ((Curry0 p).natDegree + (Curry0 q).natDegree))
    (hpdeg : p.totalDegree ≤ d₁)
    (hqdeg : q.totalDegree ≤ d₂) :
    MvPolynomial.degreeOf (0 : Fin 1)
      (Polynomial.sylvester (Curry0 p) (Curry0 q)
        (Curry0 p).natDegree (Curry0 q).natDegree i j) ≤ max d₁ d₂ := by
  classical
  have hpbound : ∀ k : ℕ, MvPolynomial.degreeOf (0 : Fin 1) ((Curry0 p).coeff k) ≤ max d₁ d₂ := by
    intro k
    exact le_trans (degreeOf_coeff_curry0_le p k)
      (le_trans (MvPolynomial.degreeOf_le_totalDegree p 1) (le_trans hpdeg (le_max_left _ _)))
  have hqbound : ∀ k : ℕ, MvPolynomial.degreeOf (0 : Fin 1) ((Curry0 q).coeff k) ≤ max d₁ d₂ := by
    intro k
    exact le_trans (degreeOf_coeff_curry0_le q k)
      (le_trans (MvPolynomial.degreeOf_le_totalDegree q 1) (le_trans hqdeg (le_max_right _ _)))
  refine Fin.addCases (motive := fun j =>
      MvPolynomial.degreeOf (0 : Fin 1)
        (Polynomial.sylvester (Curry0 p) (Curry0 q)
          (Curry0 p).natDegree (Curry0 q).natDegree i j) ≤ max d₁ d₂) ?_ ?_ j
  · intro jl
    rw [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left]
    by_cases hmem : (i : ℕ) ∈ Set.Icc (jl : ℕ) ((jl : ℕ) + (Curry0 q).natDegree)
    · rw [if_pos hmem]; exact hqbound _
    · rw [if_neg hmem]; exact Nat.zero_le _
  · intro jr
    rw [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right]
    by_cases hmem : (i : ℕ) ∈ Set.Icc (jr : ℕ) ((jr : ℕ) + (Curry0 p).natDegree)
    · rw [if_pos hmem]; exact hpbound _
    · rw [if_neg hmem]; exact Nat.zero_le _


lemma degreeOf_resultant_le
    (p q : MvPolynomial (Fin 2) ℝ)
    {d₁ d₂ : ℕ}
    (hpdeg : p.totalDegree ≤ d₁)
    (hqdeg : q.totalDegree ≤ d₂) :
    MvPolynomial.degreeOf (0 : Fin 1) (ResultantCoeff p q) ≤ (d₁ + d₂) ^ 2 := by
  classical
  set m := (Curry0 p).natDegree with hm_def
  set n := (Curry0 q).natDegree with hn_def
  have hm : m ≤ d₁ := by
    rw [hm_def]
    calc
      (Curry0 p).natDegree = MvPolynomial.degreeOf (0 : Fin 2) p := by
        simpa [Curry0] using
          (MvPolynomial.natDegree_finSuccEquiv (R := ℝ) (n := 1) (f := p))
      _ ≤ p.totalDegree := MvPolynomial.degreeOf_le_totalDegree p 0
      _ ≤ d₁ := hpdeg
  have hn : n ≤ d₂ := by
    rw [hn_def]
    calc
      (Curry0 q).natDegree = MvPolynomial.degreeOf (0 : Fin 2) q := by
        simpa [Curry0] using
          (MvPolynomial.natDegree_finSuccEquiv (R := ℝ) (n := 1) (f := q))
      _ ≤ q.totalDegree := MvPolynomial.degreeOf_le_totalDegree q 0
      _ ≤ d₂ := hqdeg
  rw [ResultantCoeff, Polynomial.resultant, Matrix.det_apply]
  refine le_trans (MvPolynomial.degreeOf_sum_le (0 : Fin 1) Finset.univ _) ?_
  refine Finset.sup_le ?_
  intro σ hσ
  have hsign :
      MvPolynomial.degreeOf (0 : Fin 1)
        (Equiv.Perm.sign σ • ∏ i, Polynomial.sylvester (Curry0 p) (Curry0 q)
          (Curry0 p).natDegree (Curry0 q).natDegree (σ i) i) ≤
      MvPolynomial.degreeOf (0 : Fin 1)
        (∏ i, Polynomial.sylvester (Curry0 p) (Curry0 q)
          (Curry0 p).natDegree (Curry0 q).natDegree (σ i) i) := by
    rw [Units.smul_def, zsmul_eq_mul]
    simpa using
      (MvPolynomial.degreeOf_C_mul_le
        (∏ i, Polynomial.sylvester (Curry0 p) (Curry0 q)
          (Curry0 p).natDegree (Curry0 q).natDegree (σ i) i) 0
        ((Equiv.Perm.sign σ : ℤ) : ℝ))
  have hprod :
      MvPolynomial.degreeOf (0 : Fin 1)
        (∏ i, Polynomial.sylvester (Curry0 p) (Curry0 q)
          (Curry0 p).natDegree (Curry0 q).natDegree (σ i) i) ≤
      ∑ _i : Fin (m + n), max d₁ d₂ := by
    refine le_trans (by
      simpa using
        (MvPolynomial.degreeOf_prod_le (0 : Fin 1) Finset.univ
          (fun i : Fin (m + n) =>
            Polynomial.sylvester (Curry0 p) (Curry0 q)
              (Curry0 p).natDegree (Curry0 q).natDegree (σ i) i))) ?_
    refine Finset.sum_le_sum ?_
    intro i hi
    exact degreeOf_sylvester_entry_bound p q (σ i) i hpdeg hqdeg
  have hsum : (∑ _i : Fin (m + n), max d₁ d₂) = (m + n) * max d₁ d₂ := by
    simp [Finset.sum_const, Finset.card_univ]
  have hmn : (m + n) * max d₁ d₂ ≤ (d₁ + d₂) ^ 2 := by
    have hmn_le : m + n ≤ d₁ + d₂ := Nat.add_le_add hm hn
    have hmax_le : max d₁ d₂ ≤ d₁ + d₂ := max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
    calc
      (m + n) * max d₁ d₂ ≤ (d₁ + d₂) * (d₁ + d₂) :=
        Nat.mul_le_mul hmn_le hmax_le
      _ = (d₁ + d₂) ^ 2 := by rw [pow_two]
  have hprod' :
      MvPolynomial.degreeOf (0 : Fin 1)
        (∏ i, Polynomial.sylvester (Curry0 p) (Curry0 q)
          (Curry0 p).natDegree (Curry0 q).natDegree (σ i) i) ≤
      (d₁ + d₂) ^ 2 := by
    refine le_trans hprod ?_
    rw [hsum]; exact hmn
  exact le_trans hsign hprod'


theorem primitive_nonvertical_pair_intersection_bound
    (p q : MvPolynomial (Fin 2) ℝ)
    {d₁ d₂ : ℕ}
    (hpdeg : p.totalDegree ≤ d₁)
    (hqdeg : q.totalDegree ≤ d₂)
    (hpprim : (Curry0 p).IsPrimitive)
    (hqprim : (Curry0 q).IsPrimitive)
    (hp0deg : 0 < (Curry0 p).natDegree)
    (hq0deg : 0 < (Curry0 q).natDegree)
    (hrel : IsRelPrime (Curry0 p) (Curry0 q)) :
    (PlaneCurveZeroSet p ∩ PlaneCurveZeroSet q).Finite ∧
      (PlaneCurveZeroSet p ∩ PlaneCurveZeroSet q).ncard ≤
        ((d₁ + d₂) ^ 2 + 1) * max d₁ d₂ := by
  classical
  let S : Set Point2 := PlaneCurveZeroSet p ∩ PlaneCurveZeroSet q
  let rootSet : Set ℝ := CoeffRootSet (ResultantCoeff p q)
  have hR : ResultantCoeff p q ≠ 0 := by
    have hp0 : p ≠ 0 := by
      intro hp0
      have hp0' : (Curry0 p).natDegree = 0 := by
        simp [hp0, Curry0]
      rw [hp0'] at hp0deg
      exact (Nat.lt_irrefl 0) hp0deg
    have hq0 : q ≠ 0 := by
      intro hq0
      have hq0' : (Curry0 q).natDegree = 0 := by
        simp [hq0, Curry0]
      rw [hq0'] at hq0deg
      exact (Nat.lt_irrefl 0) hq0deg
    simpa [ResultantCoeff] using
      (resultant_ne_zero_of_isRelPrime_primitive_curry p q hpprim hqprim hrel)
  have hrootFinite : rootSet.Finite := by
    simpa [rootSet] using (finite_coeff_roots_of_ne_zero (ResultantCoeff p q) hR)
  let rootFinset := hrootFinite.toFinset
  let fiberSet : ℝ → Set Point2 :=
    fun x => {z : Point2 | coeffCoord z = x ∧ z ∈ S}
  have hroot_ncard : rootSet.ncard ≤ (d₁ + d₂) ^ 2 := by
    exact le_trans (ncard_coeff_roots_le_degreeOf (ResultantCoeff p q) hR)
      (degreeOf_resultant_le p q hpdeg hqdeg)
  have hfiber_finite : ∀ x ∈ rootFinset, (fiberSet x).Finite := by
    intro x hx
    have hxroot : x ∈ rootSet := by
      simpa [rootFinset, rootSet] using hx
    have hnonzero : Specialized0 x p ≠ 0 ∨ Specialized0 x q ≠ 0 := by
      exact not_both_specializations_zero_of_isRelPrime p q x hpprim hqprim hrel
    have htarget_finite : (FiberCommonZeros x p q).Finite := by
      exact fiber_finite_of_one_specialization_nonzero p q x hnonzero
    have hmapsTo : Set.MapsTo elimCoord (fiberSet x) (FiberCommonZeros x p q) := by
      intro z hz
      rcases hz with ⟨hcoeff, hz⟩
      rcases hz with ⟨hzp, hzq⟩
      constructor
      · simpa [FiberCommonZeros, hcoeff, eval_eq_specialized_eval] using hzp
      · simpa [FiberCommonZeros, hcoeff, eval_eq_specialized_eval] using hzq
    have hinj : Set.InjOn elimCoord (fiberSet x) := by
      intro z₁ hz₁ z₂ hz₂ h
      ext i
      fin_cases i
      · exact h
      · exact by
          simpa [coeffCoord] using (hz₁.1.trans hz₂.1.symm)
    exact Set.Finite.of_injOn hmapsTo hinj htarget_finite
  have hfiber_bound : ∀ x ∈ rootFinset, (fiberSet x).ncard ≤ max d₁ d₂ := by
    intro x hx
    have hxroot : x ∈ rootSet := by
      simpa [rootFinset, rootSet] using hx
    have hnonzero : Specialized0 x p ≠ 0 ∨ Specialized0 x q ≠ 0 := by
      exact not_both_specializations_zero_of_isRelPrime p q x hpprim hqprim hrel
    have hle_root : (fiberSet x).ncard ≤ (FiberCommonZeros x p q).ncard := by
      have htarget_finite : (FiberCommonZeros x p q).Finite := by
        exact fiber_finite_of_one_specialization_nonzero p q x hnonzero
      have hmapsTo : Set.MapsTo elimCoord (fiberSet x) (FiberCommonZeros x p q) := by
        intro z hz
        rcases hz with ⟨hcoeff, hz⟩
        rcases hz with ⟨hzp, hzq⟩
        constructor
        · simpa [FiberCommonZeros, hcoeff, eval_eq_specialized_eval] using hzp
        · simpa [FiberCommonZeros, hcoeff, eval_eq_specialized_eval] using hzq
      have hinj : Set.InjOn elimCoord (fiberSet x) := by
        intro z₁ hz₁ z₂ hz₂ h
        ext i
        fin_cases i
        · exact h
        · exact by
            simpa [coeffCoord] using (hz₁.1.trans hz₂.1.symm)
      exact Set.ncard_le_ncard_of_injOn elimCoord hmapsTo hinj htarget_finite
    have hfiberBound : (FiberCommonZeros x p q).ncard ≤ max d₁ d₂ := by
      exact le_trans (fiber_ncard_le_max_totalDegree p q x hnonzero) (max_le_max hpdeg hqdeg)
    exact le_trans hle_root hfiberBound
  have hcover : S = ⋃ x ∈ rootFinset, fiberSet x := by
    ext z
    constructor
    · intro hz
      have hxroot : coeffCoord z ∈ rootSet := by
        exact resultant_vanishes_at_common_zero p q hp0deg hq0deg hz
      have hx : coeffCoord z ∈ rootFinset := by
        simpa [rootFinset, rootSet] using hxroot
      have hzfiber : z ∈ fiberSet (coeffCoord z) := by
        exact ⟨rfl, hz⟩
      refine Set.mem_iUnion.2 ?_
      refine ⟨coeffCoord z, Set.mem_iUnion.2 ?_⟩
      exact ⟨hx, hzfiber⟩
    · intro hz
      rcases Set.mem_iUnion.1 hz with ⟨x, hz⟩
      rcases Set.mem_iUnion.1 hz with ⟨hx, hz⟩
      rcases hz with ⟨hcoeff, hzS⟩
      simpa [S] using hzS
  have hrootcard : rootFinset.card ≤ (d₁ + d₂) ^ 2 + 1 := by
    have hrootcard' : rootFinset.card = rootSet.ncard := by
      simpa [rootFinset, rootSet] using
        (Set.ncard_eq_toFinset_card rootSet hrootFinite).symm
    calc
      rootFinset.card = rootSet.ncard := hrootcard'
      _ ≤ (d₁ + d₂) ^ 2 := hroot_ncard
      _ ≤ (d₁ + d₂) ^ 2 + 1 := Nat.le_succ _
  have hunion_ncard :
      (⋃ x ∈ rootFinset, fiberSet x).ncard ≤ ((d₁ + d₂) ^ 2 + 1) * max d₁ d₂ := by
    refine le_trans (Finset.set_ncard_biUnion_le rootFinset fiberSet) ?_
    have hsum :
        ∑ x ∈ rootFinset, (fiberSet x).ncard ≤ ∑ x ∈ rootFinset, max d₁ d₂ := by
      refine Finset.sum_le_sum ?_
      intro x hx
      exact hfiber_bound x hx
    have hsum' : ∑ x ∈ rootFinset, max d₁ d₂ = rootFinset.card * max d₁ d₂ := by
      simp
    calc
      ∑ x ∈ rootFinset, (fiberSet x).ncard ≤ ∑ x ∈ rootFinset, max d₁ d₂ := hsum
      _ = rootFinset.card * max d₁ d₂ := hsum'
      _ ≤ ((d₁ + d₂) ^ 2 + 1) * max d₁ d₂ := by
        exact Nat.mul_le_mul_right _ hrootcard
  have hunion_finite : (⋃ x ∈ rootFinset, fiberSet x).Finite := by
    change (⋃ x ∈ (rootFinset : Set ℝ), fiberSet x).Finite
    exact Set.Finite.biUnion rootFinset.finite_toSet (by
      intro x hx
      exact hfiber_finite x hx)
  have hfinite : S.Finite := by
    simpa [hcover] using hunion_finite
  have hncard : S.ncard ≤ ((d₁ + d₂) ^ 2 + 1) * max d₁ d₂ := by
    calc
      S.ncard = (⋃ x ∈ rootFinset, fiberSet x).ncard := by rw [hcover]
      _ ≤ ((d₁ + d₂) ^ 2 + 1) * max d₁ d₂ := hunion_ncard
  exact ⟨hfinite, hncard⟩

 
theorem irreducible_pair_intersection_bound
    (h k : MvPolynomial (Fin 2) ℝ)
    (hh : Irreducible h) (hk : Irreducible k)
    (hdeg : h.totalDegree ≤ d₁)
    (kdeg : k.totalDegree ≤ d₂)
    (hnot : ¬ Associated h k) :
    (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).Finite ∧
      (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).ncard ≤
        (d₁ + d₂ + 1) ^ 4 := by
  have htarget_mul : d₁ * d₂ ≤ (d₁ + d₂ + 1) ^ 4 := by
    have hle : d₁ * d₂ ≤ (d₁ + d₂ + 1) ^ 2 := by
      have hd1 : d₁ ≤ d₁ + d₂ + 1 := by omega
      have hd2 : d₂ ≤ d₁ + d₂ + 1 := by omega
      calc
        d₁ * d₂ ≤ (d₁ + d₂ + 1) * d₂ := Nat.mul_le_mul_right _ hd1
        _ ≤ (d₁ + d₂ + 1) * (d₁ + d₂ + 1) := Nat.mul_le_mul_left _ hd2
        _ = (d₁ + d₂ + 1) ^ 2 := by simp [pow_two]
    have hpos : 0 < (d₁ + d₂ + 1) ^ 2 := by
      have hbase : 0 < d₁ + d₂ + 1 := by omega
      exact Nat.pow_pos hbase
    have hsq : (d₁ + d₂ + 1) ^ 2 ≤ (d₁ + d₂ + 1) ^ 4 := by
      have hle2 : (d₁ + d₂ + 1) ^ 2 ≤ (d₁ + d₂ + 1) ^ 2 * (d₁ + d₂ + 1) ^ 2 := by
        exact Nat.le_mul_of_pos_right _ hpos
      simp [pow_succ] at hle2 ⊢
    exact le_trans hle hsq
  have htarget_prim :
      ((d₁ + d₂) ^ 2 + 1) * max d₁ d₂ ≤ (d₁ + d₂ + 1) ^ 4 := by
     
    have hmax : max d₁ d₂ ≤ d₁ + d₂ + 1 :=
      max_le (by omega) (by omega)
    have hfac : (d₁ + d₂) ^ 2 + 1 ≤ (d₁ + d₂ + 1) ^ 3 := by
      have h2 : (d₁ + d₂) ^ 2 + 1 ≤ (d₁ + d₂ + 1) ^ 2 := by
        have : (d₁ + d₂ + 1) ^ 2 = (d₁ + d₂) ^ 2 + (2 * (d₁ + d₂) + 1) := by ring
        omega
      have h3 : (d₁ + d₂ + 1) ^ 2 ≤ (d₁ + d₂ + 1) ^ 3 :=
        Nat.pow_le_pow_right (by omega) (by omega)
      exact le_trans h2 h3
    calc
      ((d₁ + d₂) ^ 2 + 1) * max d₁ d₂
          ≤ (d₁ + d₂ + 1) ^ 3 * (d₁ + d₂ + 1) := Nat.mul_le_mul hfac hmax
      _ = (d₁ + d₂ + 1) ^ 4 := by ring
  by_cases hdeg0 : (Curry0 h).natDegree = 0
  · by_cases kdeg0 : (Curry0 k).natDegree = 0
    · exact zeroCurry_zeroCurry_pair_intersection_bound h k hh hk hnot hdeg0 kdeg0
    · have kpos : 0 < (Curry0 k).natDegree := Nat.pos_of_ne_zero kdeg0
      have hbound :=
        zeroCurry_nonvertical_pair_intersection_bound h k hh hk hdeg kdeg hnot hdeg0 kpos
      exact ⟨hbound.1, le_trans hbound.2 htarget_mul⟩
  · have hpos : 0 < (Curry0 h).natDegree := Nat.pos_of_ne_zero hdeg0
    by_cases kdeg0 : (Curry0 k).natDegree = 0
    · have hnot' : ¬ Associated k h := by
        intro hAssoc
        exact hnot hAssoc.symm
      have hbound :=
        zeroCurry_nonvertical_pair_intersection_bound k h hk hh kdeg hdeg hnot' kdeg0 hpos
      have hbound' :
          (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).Finite ∧
            (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).ncard ≤ d₁ * d₂ := by
        simpa [Set.inter_comm, Nat.mul_comm] using hbound
      exact ⟨hbound'.1, le_trans hbound'.2 htarget_mul⟩
    · have kpos : 0 < (Curry0 k).natDegree := Nat.pos_of_ne_zero kdeg0
      have hprim : (Curry0 h).IsPrimitive :=
        curry_isPrimitive_of_irreducible_positive_natDegree h hh hpos
      have kprim : (Curry0 k).IsPrimitive :=
        curry_isPrimitive_of_irreducible_positive_natDegree k hk kpos
      have hrel : IsRelPrime (Curry0 h) (Curry0 k) :=
        curry_isRelPrime_of_nonassociated_irreducibles h k hh hk hnot
      have hbound :=
        primitive_nonvertical_pair_intersection_bound h k hdeg kdeg hprim kprim hpos kpos hrel
      exact ⟨hbound.1, le_trans hbound.2 htarget_prim⟩


def SingularPointSet (p : PlanePoly) : Set Point2 :=
  PlaneCurveZeroSet p ∩
    {z | MvPolynomial.eval (fun i => z i) (MvPolynomial.pderiv (0 : Fin 2) p) = 0} ∩
    {z | MvPolynomial.eval (fun i => z i) (MvPolynomial.pderiv (1 : Fin 2) p) = 0}

 
noncomputable def evalPlane (p : PlanePoly) : ℝ × ℝ → ℝ :=
  fun xy => MvPolynomial.eval (fun i => if i = 0 then xy.1 else xy.2) p

 
noncomputable def mkPoint2 (x y : ℝ) : Point2 :=
  WithLp.toLp 2 ![x, y]

 
noncomputable def swapPoint (z : Point2) : Point2 :=
  mkPoint2 (z 1) (z 0)

 
lemma swapPoint_swapPoint (z : Point2) : swapPoint (swapPoint z) = z := by
  ext i
  fin_cases i <;> simp [swapPoint, mkPoint2]

 
lemma swapPoint_injective : Function.Injective swapPoint := by
  intro z₁ z₂ h
  have h' := congrArg swapPoint h
  simpa [swapPoint_swapPoint] using h'

 
lemma evalPlane_contDiff (p : PlanePoly) :
    ContDiff ℝ ⊤ (evalPlane p) := by
  change ContDiff ℝ ⊤ (fun xy : ℝ × ℝ =>
    MvPolynomial.eval (fun i => if i = 0 then xy.1 else xy.2) p)
  refine MvPolynomial.induction_on
    (motive := fun p => ContDiff ℝ ⊤ (fun xy : ℝ × ℝ =>
      MvPolynomial.eval (fun i => if i = 0 then xy.1 else xy.2) p)) p ?_ ?_ ?_
  · intro a
    simpa [MvPolynomial.eval_C] using
      (contDiff_const : ContDiff ℝ ⊤ (fun _ : ℝ × ℝ => a))
  · intro p q hp hq
    simpa [MvPolynomial.eval_add] using hp.add hq
  · intro p i hp
    fin_cases i
    · simpa [MvPolynomial.eval_mul, MvPolynomial.eval_X] using hp.mul contDiff_fst
    · simpa [MvPolynomial.eval_mul, MvPolynomial.eval_X] using hp.mul contDiff_snd

 
lemma toSpanSingleton_bijective_of_ne_zero (b : ℝ) (hb : b ≠ 0) :
    Function.Bijective (ContinuousLinearMap.toSpanSingleton ℝ b) := by
  constructor
  · intro x y hxy
    have hxy' : x * b = y * b := by
      simpa [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] using hxy
    exact mul_right_cancel₀ hb hxy'
  · intro y
    refine ⟨y / b, ?_⟩
    simp [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
    field_simp [hb]

 
lemma curry0_pderiv0 (p : PlanePoly) :
    Curry0 (MvPolynomial.pderiv (0 : Fin 2) p) = Polynomial.derivative (Curry0 p) := by
  refine MvPolynomial.induction_on
    (motive := fun p =>
      Curry0 (MvPolynomial.pderiv (0 : Fin 2) p) = Polynomial.derivative (Curry0 p)) p ?_ ?_ ?_
  · intro a
    simp [Curry0, MvPolynomial.finSuccEquiv_apply]
  · intro p q hp hq
    simpa [Curry0, map_add] using congrArg₂ (fun a b => a + b) hp hq
  · intro p i hp
    have hp' :
        MvPolynomial.eval₂ (Polynomial.C.comp MvPolynomial.C)
            (fun i ↦ Fin.cases Polynomial.X (fun k ↦ Polynomial.C (MvPolynomial.X k)) i)
            (MvPolynomial.pderiv (0 : Fin 2) p) =
          Polynomial.derivative
            (MvPolynomial.eval₂ (Polynomial.C.comp MvPolynomial.C)
              (fun i ↦ Fin.cases Polynomial.X (fun k ↦ Polynomial.C (MvPolynomial.X k)) i) p) := by
      simpa [Curry0, MvPolynomial.finSuccEquiv_apply] using hp
    fin_cases i
    · simp [Curry0, MvPolynomial.finSuccEquiv_apply, map_add, map_mul,
        MvPolynomial.pderiv_X, Polynomial.derivative_mul]
      rw [hp']
      ring
    · simp [Curry0, MvPolynomial.finSuccEquiv_apply, map_mul,
        MvPolynomial.pderiv_X, Polynomial.derivative_mul]
      rw [hp']
      change Polynomial.C (MvPolynomial.X 0) *
            Polynomial.derivative
              (MvPolynomial.eval₂ (Polynomial.C.comp MvPolynomial.C)
                (fun i ↦ Fin.cases Polynomial.X (fun k ↦ Polynomial.C (MvPolynomial.X k)) i) p) =
          Polynomial.derivative
              (MvPolynomial.eval₂ (Polynomial.C.comp MvPolynomial.C)
                (fun i ↦ Fin.cases Polynomial.X (fun k ↦ Polynomial.C (MvPolynomial.X k)) i) p) *
            Polynomial.C (MvPolynomial.X 0) +
              MvPolynomial.eval₂ (Polynomial.C.comp MvPolynomial.C)
                (fun i ↦ Fin.cases Polynomial.X (fun k ↦ Polynomial.C (MvPolynomial.X k)) i) p *
              Polynomial.derivative (Polynomial.C (MvPolynomial.X 0))
      simp [mul_comm]


lemma nonsingular_point_has_infinite_zeroSet_of_partial1
    (h : PlanePoly) {z : Point2}
    (hz : z ∈ PlaneCurveZeroSet h)
    (hnonsing :
      MvPolynomial.eval (fun i => z i) (MvPolynomial.pderiv (1 : Fin 2) h) ≠ 0) :
    (PlaneCurveZeroSet h).Infinite := by
  letI : AddCommGroup ℝ := Real.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ ℝ := RCLike.toInnerProductSpaceReal.toModule
  let a : ℝ × ℝ := (z 0, z 1)
  have hcoords : (fun i : Fin 2 => if i = 0 then a.1 else a.2) = fun i => z i := by
    funext i
    fin_cases i <;> simp [a]
  have hcont : ContDiffAt ℝ ⊤ (evalPlane h) a := (evalPlane_contDiff h).contDiffAt
  rcases (show ∃ f' : (ℝ × ℝ) →L[ℝ] ℝ, HasFDerivAt (evalPlane h) f' a by
      simpa [DifferentiableAt] using hcont.differentiableAt) with ⟨f', hfd⟩
  let g : ℝ → ℝ := fun y => evalPlane h (a.1, y)
  let hswap : PlanePoly := MvPolynomial.rename (Equiv.swap 0 1) h
  let q : Polynomial ℝ := Specialized0 a.1 hswap
  have hg_eq : g = fun y => Polynomial.eval y q := by
    funext y
    have hslice := eval_eq_specialized_eval hswap (mkPoint2 y a.1)
    have hswapCoords :
        ((fun i => mkPoint2 y a.1 i) ∘ (Equiv.swap 0 1)) =
          (fun i : Fin 2 => if i = 0 then a.1 else y) := by
      funext i
      fin_cases i <;> simp [Function.comp, mkPoint2]
    dsimp [hswap] at hslice
    rw [MvPolynomial.eval_rename] at hslice
    rw [hswapCoords] at hslice
    simpa [g, q, evalPlane, elimCoord, coeffCoord, mkPoint2] using hslice
  have hinr : HasFDerivAt (fun y : ℝ => (a.1, y))
      (ContinuousLinearMap.inr ℝ ℝ ℝ) a.2 := by
    simpa [ContinuousLinearMap.inr] using
      (hasFDerivAt_const a.1 a.2).prodMk (hasFDerivAt_id a.2)
  have hgfd : HasFDerivAt g (f'.comp (ContinuousLinearMap.inr ℝ ℝ ℝ)) a.2 := by
    convert hfd.comp a.2 hinr using 1
    funext y
    rfl
  have hq_deriv : Polynomial.derivative q =
      Specialized0 a.1 (MvPolynomial.pderiv (0 : Fin 2) hswap) := by
    unfold q Specialized0
    rw [Polynomial.derivative_map, curry0_pderiv0]
  have hslice_deriv :
      Polynomial.eval a.2 (Polynomial.derivative q) =
        MvPolynomial.eval (fun i => z i) (MvPolynomial.pderiv (1 : Fin 2) h) := by
    rw [hq_deriv]
    have hslice :=
      eval_eq_specialized_eval (MvPolynomial.pderiv (0 : Fin 2) hswap) (swapPoint z)
    have hrename :
        MvPolynomial.pderiv (0 : Fin 2) hswap =
          MvPolynomial.rename (Equiv.swap 0 1) (MvPolynomial.pderiv (1 : Fin 2) h) := by
      dsimp [hswap]
      simpa using
        (MvPolynomial.pderiv_rename (Equiv.swap 0 1).injective (x := (1 : Fin 2)) (p := h))
    have hswapCoords :
        ((fun i => swapPoint z i) ∘ (Equiv.swap 0 1)) = fun i => z i := by
      funext i
      fin_cases i <;> simp [Function.comp, swapPoint, mkPoint2]
    calc
      Polynomial.eval a.2 (Specialized0 a.1 (MvPolynomial.pderiv (0 : Fin 2) hswap)) =
          MvPolynomial.eval (fun i => swapPoint z i) (MvPolynomial.pderiv (0 : Fin 2) hswap) := by
            simpa [a, swapPoint, mkPoint2, elimCoord, coeffCoord] using hslice.symm
      _ = MvPolynomial.eval ((fun i => swapPoint z i) ∘ (Equiv.swap 0 1))
            (MvPolynomial.pderiv (1 : Fin 2) h) := by
              rw [hrename, MvPolynomial.eval_rename]
      _ = MvPolynomial.eval (fun i => z i) (MvPolynomial.pderiv (1 : Fin 2) h) := by
            simp [hswapCoords]
  have hpoly : HasFDerivAt g
      (ContinuousLinearMap.toSpanSingleton ℝ (Polynomial.eval a.2 (Polynomial.derivative q))) a.2 := by
    have hq' :
        HasFDerivAt (fun y => Polynomial.eval y q)
          (ContinuousLinearMap.toSpanSingleton ℝ (Polynomial.eval a.2 (Polynomial.derivative q))) a.2 := by
      simpa [Polynomial.aeval_def] using (Polynomial.hasDerivAt_aeval q a.2).hasFDerivAt
    simpa [hg_eq] using hq'
  have hscalar_ne : Polynomial.eval a.2 (Polynomial.derivative q) ≠ 0 := by
    simpa [hslice_deriv] using hnonsing
  have hcomp :
      Function.Bijective (f'.comp (ContinuousLinearMap.inr ℝ ℝ ℝ)) := by
    have hcomp_eq :
        f'.comp (ContinuousLinearMap.inr ℝ ℝ ℝ) =
          ContinuousLinearMap.toSpanSingleton ℝ
            (Polynomial.eval a.2 (Polynomial.derivative q)) :=
      HasFDerivAt.unique hgfd hpoly
    simpa [hcomp_eq] using
      toSpanSingleton_bijective_of_ne_zero
        (Polynomial.eval a.2 (Polynomial.derivative q)) hscalar_ne
  have hn : (⊤ : WithTop ℕ∞) ≠ 0 := by simp
  have hinv :
      ((fderiv ℝ (evalPlane h) a) ∘L (ContinuousLinearMap.inr ℝ ℝ ℝ)).IsInvertible :=
    hasFDerivAt_isInvertible_partial hfd hcomp
  let ψ : ℝ → ℝ := cdImplicitFunction hcont hn hinv
  have ha : evalPlane h a = 0 := by
    simpa [PlaneCurveZeroSet, evalPlane, hcoords] using hz
  have hevent : ∀ᶠ x in 𝓝 a.1, evalPlane h (x, ψ x) = 0 := by
    simpa [ha, ψ] using cdApplyImplicitFunction hcont hn hinv
  have hnhds : {x | evalPlane h (x, ψ x) = 0} ∈ 𝓝 a.1 := by
    simpa [Filter.Eventually] using hevent
  rcases Metric.mem_nhds_iff.mp hnhds with ⟨ε, hε, hball⟩
  have hball_infinite : (Metric.ball a.1 ε).Infinite := by
    simpa [Real.ball_eq_Ioo] using Set.Ioo_infinite (show a.1 - ε < a.1 + ε by linarith)
  let g : ℝ → Point2 := fun x => mkPoint2 x (ψ x)
  have hg_inj : Set.InjOn g (Metric.ball a.1 ε) := by
    intro x hx y hy hxy
    have h0 := congrArg (fun p : Point2 => p 0) hxy
    simp [g, mkPoint2] at h0
    exact h0
  have hsubset : g '' Metric.ball a.1 ε ⊆ PlaneCurveZeroSet h := by
    intro z' hz'
    rcases hz' with ⟨x, hx, rfl⟩
    have hx' : evalPlane h (x, ψ x) = 0 := hball hx
    change MvPolynomial.eval (fun i => g x i) h = 0
    dsimp [g]
    convert hx' using 1
    show MvPolynomial.eval (fun i => mkPoint2 x (ψ x) i) h =
      MvPolynomial.eval (fun i : Fin 2 => if i = 0 then x else ψ x) h
    apply congrArg (fun f => MvPolynomial.eval f h)
    funext i
    fin_cases i <;> simp [mkPoint2]
  exact Set.Infinite.mono hsubset (Set.Infinite.image hg_inj hball_infinite)


lemma nonsingular_point_has_infinite_zeroSet_of_partial0
    (h : PlanePoly) {z : Point2}
    (hz : z ∈ PlaneCurveZeroSet h)
    (hnonsing :
      MvPolynomial.eval (fun i => z i) (MvPolynomial.pderiv (0 : Fin 2) h) ≠ 0) :
    (PlaneCurveZeroSet h).Infinite := by
  let h' : PlanePoly := MvPolynomial.rename (Equiv.swap 0 1) h
  have hz' : swapPoint z ∈ PlaneCurveZeroSet h' := by
    dsimp [h']
    change MvPolynomial.eval (fun i => swapPoint z i)
      (MvPolynomial.rename (Equiv.swap 0 1) h) = 0
    rw [MvPolynomial.eval_rename]
    have hswapCoords :
        ((fun i => swapPoint z i) ∘ (Equiv.swap 0 1)) = fun i => z i := by
      funext i
      fin_cases i <;> simp [Function.comp, swapPoint, mkPoint2]
    simpa [hswapCoords] using hz
  have h1' :
      MvPolynomial.eval (fun i => swapPoint z i) (MvPolynomial.pderiv (1 : Fin 2) h') ≠ 0 := by
    dsimp [h']
    have hrename :
        MvPolynomial.pderiv (1 : Fin 2) (MvPolynomial.rename (Equiv.swap 0 1) h) =
          MvPolynomial.rename (Equiv.swap 0 1) (MvPolynomial.pderiv (0 : Fin 2) h) := by
      simpa using
        (MvPolynomial.pderiv_rename (Equiv.swap 0 1).injective (x := (0 : Fin 2)) (p := h))
    rw [hrename, MvPolynomial.eval_rename]
    have hswapCoords :
        ((fun i => swapPoint z i) ∘ (Equiv.swap 0 1)) = fun i => z i := by
      funext i
      fin_cases i <;> simp [Function.comp, swapPoint, mkPoint2]
    simpa [hswapCoords] using hnonsing
  have hinf' := nonsingular_point_has_infinite_zeroSet_of_partial1 h' hz' h1'
  have hswap : swapPoint '' PlaneCurveZeroSet h' = PlaneCurveZeroSet h := by
    ext w
    constructor
    · rintro ⟨u, hu, rfl⟩
      change MvPolynomial.eval (fun i => swapPoint u i) h = 0
      have hu' : MvPolynomial.eval (fun i => u i)
          (MvPolynomial.rename (Equiv.swap 0 1) h) = 0 := hu
      rw [MvPolynomial.eval_rename] at hu'
      have hswapCoords :
          ((fun i => u i) ∘ (Equiv.swap 0 1)) = fun i => swapPoint u i := by
        funext i
        fin_cases i <;> simp [Function.comp, swapPoint, mkPoint2]
      rw [hswapCoords] at hu'
      exact hu'
    · intro hw
      refine ⟨swapPoint w, ?_, ?_⟩
      · change MvPolynomial.eval (fun i => swapPoint w i)
          (MvPolynomial.rename (Equiv.swap 0 1) h) = 0
        rw [MvPolynomial.eval_rename]
        have hswapCoords :
            ((fun i => swapPoint w i) ∘ (Equiv.swap 0 1)) = fun i => w i := by
          funext i
          fin_cases i <;> simp [Function.comp, swapPoint, mkPoint2]
        rw [hswapCoords]
        exact hw
      · simp [swapPoint_swapPoint]
  have hswap_inf : (swapPoint '' PlaneCurveZeroSet h').Infinite :=
    hinf'.image (Function.Injective.injOn swapPoint_injective)
  simpa [hswap] using hswap_inf

 
theorem nonsingular_point_has_infinite_zeroSet
    (h : PlanePoly) {z : Point2}
    (hz : z ∈ PlaneCurveZeroSet h)
    (hnonsing :
      MvPolynomial.eval (fun i => z i) (MvPolynomial.pderiv (0 : Fin 2) h) ≠ 0 ∨
      MvPolynomial.eval (fun i => z i) (MvPolynomial.pderiv (1 : Fin 2) h) ≠ 0) :
    (PlaneCurveZeroSet h).Infinite := by
  rcases hnonsing with h0 | h1
  · exact nonsingular_point_has_infinite_zeroSet_of_partial0 h hz h0
  · exact nonsingular_point_has_infinite_zeroSet_of_partial1 h hz h1

 
lemma finite_zeroSet_subset_singularities
    (h : PlanePoly)
    (hfin : (PlaneCurveZeroSet h).Finite) :
    PlaneCurveZeroSet h ⊆ SingularPointSet h := by
  intro z hz
  refine ⟨⟨hz, ?_⟩, ?_⟩
  · by_contra h0
    have hinf := nonsingular_point_has_infinite_zeroSet h hz (by
      left
      simpa using h0)
    exact hfin.not_infinite hinf
  · by_contra h1
    have hinf := nonsingular_point_has_infinite_zeroSet h hz (by
      right
      simpa using h1)
    exact hfin.not_infinite hinf


lemma irreducible_has_nonzero_partial
    (h : PlanePoly) (hh : Irreducible h) :
    MvPolynomial.pderiv (0 : Fin 2) h ≠ 0 ∨
    MvPolynomial.pderiv (1 : Fin 2) h ≠ 0 := by
  classical
  by_cases h0 : MvPolynomial.pderiv (0 : Fin 2) h = 0
  · by_cases h1 : MvPolynomial.pderiv (1 : Fin 2) h = 0
    · exfalso
      let p : Polynomial (Polynomial ℝ) := (Polynomial.Bivariate.equivMvPolynomial ℝ).symm h
      have hp : (Polynomial.Bivariate.equivMvPolynomial ℝ) p = h := by
        simp [p]
      have hp1 : Polynomial.derivative p = 0 := by
        have h1' : (MvPolynomial.pderiv (1 : Fin 2)) ((Polynomial.Bivariate.equivMvPolynomial ℝ) p) = 0 := by
          simpa [p, hp] using h1
        rw [Polynomial.Bivariate.pderiv_one_equivMvPolynomial] at h1'
        have h1'' :
            (Polynomial.Bivariate.equivMvPolynomial ℝ) (Polynomial.derivative p) =
              (Polynomial.Bivariate.equivMvPolynomial ℝ) 0 := by
          simpa using h1'
        exact (Polynomial.Bivariate.equivMvPolynomial ℝ).injective h1''
      have hp_nat : p.natDegree = 0 :=
        Polynomial.natDegree_eq_zero_of_derivative_eq_zero hp1
      rcases (Polynomial.natDegree_eq_zero.mp hp_nat) with ⟨q, hq⟩
      have h0' : PolynomialModule.single (Polynomial ℝ) 0 (Polynomial.derivative q) = 0 := by
        have h0'' : Polynomial.derivative'.mapCoeffs p = 0 := by
          have h0''0 : (MvPolynomial.pderiv (0 : Fin 2)) ((Polynomial.Bivariate.equivMvPolynomial ℝ) p) = 0 := by
            simpa [p, hp] using h0
          rw [Polynomial.Bivariate.pderiv_zero_equivMvPolynomial] at h0''0
          have h0''1 : PolynomialModule.equivPolynomialSelf
              (Polynomial.derivative'.mapCoeffs p) = 0 := by
            have h0''0' :
                (Polynomial.Bivariate.equivMvPolynomial ℝ)
                    (PolynomialModule.equivPolynomialSelf (Polynomial.derivative'.mapCoeffs p)) =
                  (Polynomial.Bivariate.equivMvPolynomial ℝ) 0 := by
              simpa using h0''0
            exact (Polynomial.Bivariate.equivMvPolynomial ℝ).injective h0''0'
          have h0''1' :
              PolynomialModule.equivPolynomialSelf (Polynomial.derivative'.mapCoeffs p) =
                PolynomialModule.equivPolynomialSelf 0 := by
            simpa using h0''1
          exact PolynomialModule.equivPolynomialSelf.injective h0''1'
        rw [← hq] at h0''
        simpa [Polynomial.derivative'_apply] using h0''
      have hqder : Polynomial.derivative q = 0 := by
        have hqder' :=
          congrArg (fun r : PolynomialModule (Polynomial ℝ) (Polynomial ℝ) => r.coeff 0) h0'
        simpa [PolynomialModule.coeff_single] using hqder'
      have hq_nat : q.natDegree = 0 :=
        Polynomial.natDegree_eq_zero_of_derivative_eq_zero hqder
      rcases (Polynomial.natDegree_eq_zero.mp hq_nat) with ⟨r, hr⟩
      have hconst : h = MvPolynomial.C r := by
        rw [← hp, ← hq, ← hr]
        simp
      by_cases hr0 : r = 0
      · subst hr0
        have hz0 := hh.ne_zero
        rw [hconst] at hz0
        simp at hz0
      · have hunitq : IsUnit r := by
          exact isUnit_iff_ne_zero.2 hr0
        have hunit : IsUnit h := by
          rw [hconst]
          exact IsUnit.map (MvPolynomial.C : ℝ →+* MvPolynomial (Fin 2) ℝ) hunitq
        exact hh.not_isUnit hunit
    · exact Or.inr h1
  · exact Or.inl h0

 
lemma irreducible_not_dvd_nonzero_partial
    (h : PlanePoly) (hh : Irreducible h) {i : Fin 2}
    (hpi : MvPolynomial.pderiv i h ≠ 0) :
    ¬ h ∣ MvPolynomial.pderiv i h := by
  intro hdiv
  have hpos : 0 < h.totalDegree := by
    by_contra hnonpos
    have hdeg0 : h.totalDegree = 0 := by omega
    have hC : h = MvPolynomial.C (MvPolynomial.coeff 0 h) := by
      exact (MvPolynomial.totalDegree_eq_zero_iff_eq_C).mp hdeg0
    have hcoeff : MvPolynomial.coeff 0 h ≠ 0 := by
      intro hzero
      exact hh.ne_zero (by rw [hC, hzero]; simp)
    have hunit : IsUnit h := by
      rw [hC]
      exact IsUnit.map (MvPolynomial.C : ℝ →+* MvPolynomial (Fin 2) ℝ)
        (isUnit_iff_ne_zero.mpr hcoeff)
    exact hh.not_isUnit hunit
  have hlt := totalDegree_pderiv_lt_of_nonzero h hpos hpi
  have hle := MvPolynomial.totalDegree_le_of_dvd_of_isDomain hdiv hpi
  exact (not_lt_of_ge hle) hlt


lemma singularPointSet_subset_partial_factor_union
    (h : PlanePoly) {i : Fin 2}
    (hpi : MvPolynomial.pderiv i h ≠ 0) :
    SingularPointSet h ⊆
      ⋃ k ∈ (UniqueFactorizationMonoid.normalizedFactors
          (MvPolynomial.pderiv i h)).toFinset,
        PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k := by
  classical
  intro z hz
  rw [SingularPointSet, Set.mem_inter_iff, Set.mem_inter_iff] at hz
  obtain ⟨⟨hz0, hz1⟩, hz2⟩ := hz
  fin_cases i
  · have hsubset := zeroSet_subset_normalizedFactor_union
        (p := MvPolynomial.pderiv (0 : Fin 2) h) hpi
    have hzder : z ∈ PlaneCurveZeroSet (MvPolynomial.pderiv (0 : Fin 2) h) := by
      simpa [PlaneCurveZeroSet] using hz1
    rcases Set.mem_iUnion.mp (hsubset hzder) with ⟨k, hk⟩
    rcases Set.mem_iUnion.mp hk with ⟨hkmem, hzk⟩
    refine Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨hkmem, ?_⟩⟩
    exact ⟨hz0, hzk⟩
  · have hsubset := zeroSet_subset_normalizedFactor_union
        (p := MvPolynomial.pderiv (1 : Fin 2) h) hpi
    have hzder : z ∈ PlaneCurveZeroSet (MvPolynomial.pderiv (1 : Fin 2) h) := by
      simpa [PlaneCurveZeroSet] using hz2
    rcases Set.mem_iUnion.mp (hsubset hzder) with ⟨k, hk⟩
    rcases Set.mem_iUnion.mp hk with ⟨hkmem, hzk⟩
    refine Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨hkmem, ?_⟩⟩
    exact ⟨hz0, hzk⟩


lemma partial_factor_not_associated
    (h k : PlanePoly) (hh : Irreducible h) {i : Fin 2}
    (hpi : MvPolynomial.pderiv i h ≠ 0)
    (hk : k ∈ UniqueFactorizationMonoid.normalizedFactors
        (MvPolynomial.pderiv i h)) :
    ¬ Associated h k := by
  intro hassoc
  have hdiv : h ∣ MvPolynomial.pderiv i h := by
    exact (Associated.dvd_iff_dvd_left hassoc).2
      (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hk)
  exact irreducible_not_dvd_nonzero_partial h hh hpi hdiv

 
lemma mul_self_le_fourth_succ (d : ℕ) : d * d ≤ (d + 1) ^ 4 := by
  have hd : (0 : ℚ) ≤ d := by exact_mod_cast Nat.zero_le d
  exact_mod_cast (by
    ring_nf
    nlinarith [hd])

 
lemma primitive_bound_le_fourth_succ (d : ℕ) :
    (((d + d) ^ 2 + 1) * d : ℕ) ≤ (d + 1) ^ 4 := by
  have hd : (0 : ℚ) ≤ d := by exact_mod_cast Nat.zero_le d
  exact_mod_cast (by
    ring_nf
    nlinarith [hd])


lemma factor_intersection_bound
    (h : PlanePoly)
    (hh : Irreducible h)
    (hdeg : h.totalDegree ≤ d)
    {i : Fin 2}
    (hpi : MvPolynomial.pderiv i h ≠ 0)
    {k : PlanePoly}
    (hk : k ∈ UniqueFactorizationMonoid.normalizedFactors (MvPolynomial.pderiv i h))
    (hnot : ¬ Associated h k) :
    (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).Finite ∧
      (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).ncard ≤ (d + 1) ^ 4 := by
  classical
  have hkirr : Irreducible k :=
    normalized_factor_irreducible (p := MvPolynomial.pderiv i h) hk
  have hkdeg : k.totalDegree ≤ d := by
    calc
      k.totalDegree ≤ (MvPolynomial.pderiv i h).totalDegree :=
        normalized_factor_degree_le (p := MvPolynomial.pderiv i h) (h := k) hpi hk
      _ ≤ h.totalDegree := totalDegree_pderiv_le h i
      _ ≤ d := hdeg
  by_cases hdeg0 : (Curry0 h).natDegree = 0
  · by_cases hkdeg0 : (Curry0 k).natDegree = 0
    · have hbound :=
        zeroCurry_zeroCurry_pair_intersection_bound
          (B := (d + 1) ^ 4) h k hh hkirr hnot hdeg0 hkdeg0
      simpa using hbound
    · have hkpos : 0 < (Curry0 k).natDegree := Nat.pos_of_ne_zero hkdeg0
      have hbound :=
        zeroCurry_nonvertical_pair_intersection_bound h k hh hkirr hdeg hkdeg hnot hdeg0 hkpos
      exact ⟨hbound.1, le_trans hbound.2 (mul_self_le_fourth_succ d)⟩
  · by_cases hkdeg0 : (Curry0 k).natDegree = 0
    · have hpos : 0 < (Curry0 h).natDegree := Nat.pos_of_ne_zero hdeg0
      have hnot' : ¬ Associated k h := by
        intro hassoc
        exact hnot hassoc.symm
      have hbound :=
        zeroCurry_nonvertical_pair_intersection_bound k h hkirr hh hkdeg hdeg hnot' hkdeg0 hpos
      have hbound' : (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).Finite ∧
          (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).ncard ≤ d * d := by
        simpa [Set.inter_comm] using hbound
      exact ⟨hbound'.1, le_trans hbound'.2 (mul_self_le_fourth_succ d)⟩
    · have hpos : 0 < (Curry0 h).natDegree := Nat.pos_of_ne_zero hdeg0
      have hkpos : 0 < (Curry0 k).natDegree := Nat.pos_of_ne_zero hkdeg0
      have hprim : (Curry0 h).IsPrimitive :=
        curry_isPrimitive_of_irreducible_positive_natDegree h hh hpos
      have kprim : (Curry0 k).IsPrimitive :=
        curry_isPrimitive_of_irreducible_positive_natDegree k hkirr hkpos
      have hrel : IsRelPrime (Curry0 h) (Curry0 k) :=
        curry_isRelPrime_of_nonassociated_irreducibles h k hh hkirr hnot
      have hbound :=
        primitive_nonvertical_pair_intersection_bound h k hdeg hkdeg hprim kprim hpos hkpos hrel
      have hbound' : (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).Finite ∧
          (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).ncard ≤ ((d + d) ^ 2 + 1) * d := by
        simpa using hbound
      exact ⟨hbound'.1, le_trans hbound'.2 (primitive_bound_le_fourth_succ d)⟩

 
theorem finite_singularities_of_irreducible_bound
    (h : PlanePoly)
    (hh : Irreducible h)
    (hdeg : h.totalDegree ≤ d)
    {i : Fin 2}
    (hpi : MvPolynomial.pderiv i h ≠ 0) :
    (SingularPointSet h).Finite ∧
      (SingularPointSet h).ncard ≤ (d + 1) ^ 5 := by
  classical
  let s : Multiset (MvPolynomial (Fin 2) ℝ) :=
    UniqueFactorizationMonoid.normalizedFactors (MvPolynomial.pderiv i h)
  have hsubset :
      SingularPointSet h ⊆
        ⋃ k ∈ s.toFinset, PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k := by
    simpa [s] using singularPointSet_subset_partial_factor_union h hpi
  have hfactor_bound : ∀ k ∈ s.toFinset,
      (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).Finite ∧
        (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).ncard ≤ (d + 1) ^ 4 := by
    intro k hk
    have hk' : k ∈ s := by
      exact Multiset.mem_toFinset.mp hk
    exact factor_intersection_bound h hh hdeg hpi hk'
      (partial_factor_not_associated h k hh hpi hk')
  have hfinite_union :
      (⋃ k ∈ s.toFinset, PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).Finite := by
    exact Set.Finite.biUnion s.toFinset.finite_toSet (by
      intro k hk
      exact (hfactor_bound k hk).1)
  have hcard_union :
      (SingularPointSet h).ncard ≤
        (⋃ k ∈ s.toFinset, PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).ncard := by
    exact Set.ncard_le_ncard hsubset hfinite_union
  have hcard_biUnion :
      (⋃ k ∈ s.toFinset, PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).ncard ≤
        ∑ k ∈ s.toFinset, (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).ncard := by
    simpa using
      Finset.set_ncard_biUnion_le s.toFinset
        (fun k => PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k)
  have hsum :
      ∑ k ∈ s.toFinset, (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).ncard ≤
        s.toFinset.card * (d + 1) ^ 4 := by
    have hsum' :
        ∑ k ∈ s.toFinset, (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).ncard ≤
          ∑ k ∈ s.toFinset, (d + 1) ^ 4 := by
      refine Finset.sum_le_sum ?_
      intro k hk
      exact (hfactor_bound k hk).2
    calc
      ∑ k ∈ s.toFinset, (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).ncard ≤
          ∑ k ∈ s.toFinset, (d + 1) ^ 4 := hsum'
      _ = s.toFinset.card * (d + 1) ^ 4 := by simp
  have hcard_s : s.toFinset.card ≤ d := by
    calc
      s.toFinset.card ≤ s.card := Multiset.toFinset_card_le _
      _ ≤ (MvPolynomial.pderiv i h).totalDegree :=
        card_normalizedFactors_le_totalDegree (p := MvPolynomial.pderiv i h) hpi
      _ ≤ h.totalDegree := totalDegree_pderiv_le h i
      _ ≤ d := hdeg
  have hcard_mul :
      s.toFinset.card * (d + 1) ^ 4 ≤ d * (d + 1) ^ 4 := by
    exact Nat.mul_le_mul_right _ hcard_s
  have hpow : d * (d + 1) ^ 4 ≤ (d + 1) ^ 5 := by
    calc
      d * (d + 1) ^ 4 ≤ (d + 1) * (d + 1) ^ 4 := by
        exact Nat.mul_le_mul_right _ (Nat.le_succ d)
      _ = (d + 1) ^ 5 := by
        ring_nf
  have hfinite : (SingularPointSet h).Finite := hfinite_union.subset hsubset
  exact ⟨hfinite, le_trans hcard_union (le_trans hcard_biUnion (le_trans hsum (le_trans hcard_mul hpow)))⟩

 
theorem finite_real_zero_set_of_irreducible_factor_bound
    (h : PlanePoly)
    (hh : Irreducible h)
    (hdeg : h.totalDegree ≤ d)
    (hfin : ¬ (PlaneCurveZeroSet h).Infinite) :
    (PlaneCurveZeroSet h).Finite ∧
      (PlaneCurveZeroSet h).ncard ≤ (d + 1) ^ 5 := by
  classical
  have hfinite : (PlaneCurveZeroSet h).Finite := (Set.not_infinite).mp hfin
  have hsubset : PlaneCurveZeroSet h ⊆ SingularPointSet h :=
    finite_zeroSet_subset_singularities h hfinite
  rcases irreducible_has_nonzero_partial h hh with hpi | hpi
  · have hsingu := finite_singularities_of_irreducible_bound h hh hdeg hpi
    exact ⟨hfinite, le_trans (Set.ncard_le_ncard hsubset hsingu.1) hsingu.2⟩
  · have hsingu := finite_singularities_of_irreducible_bound h hh hdeg hpi
    exact ⟨hfinite, le_trans (Set.ncard_le_ncard hsubset hsingu.1) hsingu.2⟩

 
theorem factorized_bezout_bound
    (p q : PlanePoly)
    (hp0 : p ≠ 0) (hq0 : q ≠ 0)
    (hpdeg : p.totalDegree ≤ d₁)
    (hqdeg : q.totalDegree ≤ d₂)
    (hnoinf : ¬ HasCommonInfiniteIrreducibleFactor p q) :
    (PlaneCurveZeroSet p ∩ PlaneCurveZeroSet q).Finite ∧
      (PlaneCurveZeroSet p ∩ PlaneCurveZeroSet q).ncard ≤
        (d₁ + d₂ + 1) ^ 8 := by
  classical
  let sp : Multiset (PlanePoly) := UniqueFactorizationMonoid.normalizedFactors p
  let sq : Multiset (PlanePoly) := UniqueFactorizationMonoid.normalizedFactors q
  let pairs : Finset (PlanePoly × PlanePoly) := sp.toFinset.product sq.toFinset
  let pairSet : PlanePoly × PlanePoly → Set Point2 :=
    fun hk => PlaneCurveZeroSet hk.1 ∩ PlaneCurveZeroSet hk.2
  have hcover :
      PlaneCurveZeroSet p ∩ PlaneCurveZeroSet q ⊆ ⋃ x ∈ pairs, pairSet x := by
    intro z hz
    rcases hz with ⟨hzp, hzq⟩
    have hpW := zeroSet_subset_normalizedFactor_union (p := p) hp0 hzp
    have hqW := zeroSet_subset_normalizedFactor_union (p := q) hq0 hzq
    rcases Set.mem_iUnion.mp hpW with ⟨hpFactor, hpW⟩
    rcases Set.mem_iUnion.mp hpW with ⟨hpMem, hzhp⟩
    rcases Set.mem_iUnion.mp hqW with ⟨hqFactor, hqW⟩
    rcases Set.mem_iUnion.mp hqW with ⟨hqMem, hzhq⟩
    refine Set.mem_iUnion.2 ?_
    refine ⟨(hpFactor, hqFactor), Set.mem_iUnion.2 ?_⟩
    refine ⟨by
      exact Finset.mem_product.2 ⟨by
        exact Multiset.mem_toFinset.mpr (Multiset.mem_toFinset.mp hpMem), by
        exact Multiset.mem_toFinset.mpr (Multiset.mem_toFinset.mp hqMem)⟩, ?_⟩
    exact ⟨hzhp, hzhq⟩
  have hpairBound : ∀ x ∈ pairs, (pairSet x).Finite ∧ (pairSet x).ncard ≤ (d₁ + d₂ + 1) ^ 5 := by
    intro x hx
    have hx' : x.1 ∈ sp.toFinset ∧ x.2 ∈ sq.toFinset := by
      simpa [pairs] using hx
    rcases hx' with ⟨hx1, hx2⟩
    have hx1' : x.1 ∈ sp := Multiset.mem_toFinset.mp hx1
    have hx2' : x.2 ∈ sq := Multiset.mem_toFinset.mp hx2
    have hirr : Irreducible x.1 := normalized_factor_irreducible (p := p) (h := x.1) hx1'
    have kirr : Irreducible x.2 := normalized_factor_irreducible (p := q) (h := x.2) hx2'
    have hdeg : x.1.totalDegree ≤ d₁ := by
      exact le_trans
        (normalized_factor_degree_le (p := p) (h := x.1) hp0 hx1')
        hpdeg
    have kdeg : x.2.totalDegree ≤ d₂ := by
      exact le_trans
        (normalized_factor_degree_le (p := q) (h := x.2) hq0 hx2')
        hqdeg
    have hspos : 0 < d₁ + d₂ + 1 := by omega
    by_cases hAssoc : Associated x.1 x.2
    · have hdiv12 : x.1 ∣ x.2 := by
        exact (hAssoc.dvd_iff_dvd_left).2 dvd_rfl
      have hdiv21 : x.2 ∣ x.1 := by
        exact (hAssoc.dvd_iff_dvd_left).1 dvd_rfl
      have hEq : PlaneCurveZeroSet x.1 = PlaneCurveZeroSet x.2 := by
        exact Set.Subset.antisymm
          (PlaneCurveZeroSet_subset_of_dvd hdiv12)
          (PlaneCurveZeroSet_subset_of_dvd hdiv21)
      have hnotinf : ¬ (PlaneCurveZeroSet x.1).Infinite := by
        intro hinf
        have hpdiv : x.1 ∣ p := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hx1'
        have hqdiv : x.1 ∣ q := by
          have hqdiv' : x.2 ∣ q := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hx2'
          exact (hAssoc.dvd_iff_dvd_left).2 hqdiv'
        exact hnoinf ⟨x.1, hirr, hinf, hpdiv, hqdiv⟩
      have hfin := finite_real_zero_set_of_irreducible_factor_bound
        (d := d₁ + d₂) x.1 hirr
        (le_trans hdeg (by omega)) hnotinf
      have hpairFin : (pairSet x).Finite := by
        simpa [pairSet, hEq] using hfin.1
      have hpairNcard : (pairSet x).ncard ≤ (d₁ + d₂ + 1) ^ 5 := by
        simpa [pairSet, hEq] using hfin.2
      exact ⟨hpairFin, hpairNcard⟩
    · have hpair := irreducible_pair_intersection_bound
        (d₁ := d₁) (d₂ := d₂) x.1 x.2 hirr kirr hdeg kdeg hAssoc
      exact ⟨hpair.1, le_trans hpair.2 (Nat.le_mul_of_pos_right _ hspos)⟩
  have hfinitePairs : (⋃ x ∈ pairs, pairSet x).Finite := by
    exact Set.Finite.biUnion pairs.finite_toSet (by
      intro x hx
      exact (hpairBound x hx).1)
  have hcard_cover :
      (PlaneCurveZeroSet p ∩ PlaneCurveZeroSet q).ncard ≤
        (⋃ x ∈ pairs, pairSet x).ncard := by
    exact Set.ncard_le_ncard hcover hfinitePairs
  have hcard_biUnion :
      (⋃ x ∈ pairs, pairSet x).ncard ≤ ∑ x ∈ pairs, (pairSet x).ncard := by
    simpa [pairSet] using Finset.set_ncard_biUnion_le pairs (fun x => pairSet x)
  have hsum_le :
      ∑ x ∈ pairs, (pairSet x).ncard ≤ pairs.card * (d₁ + d₂ + 1) ^ 5 := by
    calc ∑ x ∈ pairs, (pairSet x).ncard
        ≤ ∑ _x ∈ pairs, (d₁ + d₂ + 1) ^ 5 :=
          Finset.sum_le_sum (fun x hx => (hpairBound x hx).2)
      _ = pairs.card * (d₁ + d₂ + 1) ^ 5 := by
          rw [Finset.sum_const, smul_eq_mul]
  have hpaircard : pairs.card ≤ (d₁ + d₂ + 1) ^ 2 := by
    have hsp : sp.toFinset.card ≤ d₁ := by
      calc
        sp.toFinset.card ≤ sp.card := Multiset.toFinset_card_le _
        _ ≤ p.totalDegree := card_normalizedFactors_le_totalDegree (p := p) hp0
        _ ≤ d₁ := hpdeg
    have hsq : sq.toFinset.card ≤ d₂ := by
      calc
        sq.toFinset.card ≤ sq.card := Multiset.toFinset_card_le _
        _ ≤ q.totalDegree := card_normalizedFactors_le_totalDegree (p := q) hq0
        _ ≤ d₂ := hqdeg
    have hle : sp.toFinset.card * sq.toFinset.card ≤ (d₁ + d₂ + 1) ^ 2 := by
      have hd1 : d₁ ≤ d₁ + d₂ + 1 := by omega
      have hd2 : d₂ ≤ d₁ + d₂ + 1 := by omega
      calc
        sp.toFinset.card * sq.toFinset.card ≤ d₁ * sq.toFinset.card := by
          exact Nat.mul_le_mul_right _ hsp
        _ ≤ d₁ * d₂ := by
          exact Nat.mul_le_mul_left _ hsq
        _ ≤ (d₁ + d₂ + 1) * (d₁ + d₂ + 1) := by
          calc
            d₁ * d₂ ≤ (d₁ + d₂ + 1) * d₂ := Nat.mul_le_mul_right _ hd1
            _ ≤ (d₁ + d₂ + 1) * (d₁ + d₂ + 1) := Nat.mul_le_mul_left _ hd2
        _ = (d₁ + d₂ + 1) ^ 2 := by simp [pow_two]
    simpa [pairs, Finset.card_product] using hle
  have hspos : 0 < d₁ + d₂ + 1 := by omega
  have hfinal :
      pairs.card * (d₁ + d₂ + 1) ^ 5 ≤ (d₁ + d₂ + 1) ^ 8 := by
    calc
      pairs.card * (d₁ + d₂ + 1) ^ 5 ≤ (d₁ + d₂ + 1) ^ 2 * (d₁ + d₂ + 1) ^ 5 := by
        exact Nat.mul_le_mul_right _ hpaircard
      _ = (d₁ + d₂ + 1) ^ 7 := by
        rw [← pow_add]
      _ ≤ (d₁ + d₂ + 1) ^ 8 := by
        exact Nat.le_mul_of_pos_right _ hspos
  have hfinite : (PlaneCurveZeroSet p ∩ PlaneCurveZeroSet q).Finite := hfinitePairs.subset hcover
  have hcard : (PlaneCurveZeroSet p ∩ PlaneCurveZeroSet q).ncard ≤
      (d₁ + d₂ + 1) ^ 8 := by
    calc
      (PlaneCurveZeroSet p ∩ PlaneCurveZeroSet q).ncard ≤
          (⋃ x ∈ pairs, pairSet x).ncard := hcard_cover
      _ ≤ ∑ x ∈ pairs, (pairSet x).ncard := hcard_biUnion
      _ ≤ pairs.card * (d₁ + d₂ + 1) ^ 5 := hsum_le
      _ ≤ (d₁ + d₂ + 1) ^ 8 := hfinal
  exact ⟨hfinite, hcard⟩

 
theorem bezout : BezoutFiniteIntersectionStatement := by
  intro d₁ d₂
  refine ⟨(d₁ + d₂ + 1) ^ 8 + 1, Nat.succ_pos _, ?_⟩
  intro C₁ C₂ hC₁ hC₂ hno
  rcases hC₁ with ⟨p, hp0, hpdeg, hpzero⟩
  rcases hC₂ with ⟨q, hq0, hqdeg, hqzero⟩
  have hnoinf :
      ¬ HasCommonInfiniteIrreducibleFactor p q := by
    exact noCommonCurveComponent_of_no_common_infinite_factor
      hp0 hq0 hpzero hqzero hno
  have hbound := factorized_bezout_bound (d₁ := d₁) (d₂ := d₂) p q hp0 hq0 hpdeg hqdeg hnoinf
  have hfinite : (C₁ ∩ C₂).Finite := by
    rw [hpzero, hqzero]
    exact hbound.1
  refine ⟨hfinite, ?_⟩
  have hle : (PlaneCurveZeroSet p ∩ PlaneCurveZeroSet q).ncard ≤ (d₁ + d₂ + 1) ^ 8 + 1 := by
    exact Nat.le_trans hbound.2 (Nat.le_succ _)
  rw [hpzero, hqzero]
  exact hle

end PachDeZeeuw.Algebraic


