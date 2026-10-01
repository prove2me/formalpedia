-- Prove2me | Definitions.Def_Yukon_764c0ea7bc9f2561ee2ad916
-- name    : Yukon_764c0ea7bc9f2561ee2ad916
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T17:55:39.01699+00:00
-- url     : https://prove2.me/theorems/2c48578d-f8c6-4b43-b023-8947f8c0031e
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.HFreeDedekind6812.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.HFreeDedekind6812.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/HFreeDedekind6812.lean
--
--   yukon-proof-operation:62feee1971519a8cbe4f5bb0453b4634d40b23088db64a73008f867061056928
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246NjJmZWVlMTk3MTUxOWE4Y2JlNGY1YmIwNDUzYjQ2MzRkNDBiMjMwODhkYjY0YTczMDA4Zjg2NzA2MTA1NjkyOCIsImhhc2giOiI0M2IxMTAyOWJhZmVjMjU4ODhhMWJjOWMxOWFmMmVhMTU4MDBhOTllNGM2NGQyYzBkZGI2NTNjZjJiNWYzYWFkIiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl83NjRjMGVhN2JjOWYyNTYxZWUyYWQ5MTYiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.FieldTheory.Minpoly.Finite
import Definitions.Def_Yukon_a9a7f17ede75ca0ceb0597e1



import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Init
set_option backward.isDefEq.respectTransparency.types false
/-!
# H-free bridge, pieces 3 and 4: the Dedekind engine

Setting: `L` a field over `K`, `D : Derivation K L L`, `v : Valuation L ℤᵐ⁰` normalized, `A` a
Dedekind domain with `v ≤ 1` on `A`, `K' = Frac A`, and `L / K'` finite separable.  Then every
`z ∈ O_v` is `r / u` with `r, u` integral over `A` and `v u = 1` (`integral_fraction`: the
localization of the integral closure at the centre of `v` is a DVR, hence equals `O_v`).

The engine (`engine`) specializes to `A = k[s]` for a subfield `k` on which `v` is trivial and
`D` bounded, and `s ∈ O_v` transcendental over `k`, with `L = k(s)(b)` and `[L : k(s)] ≤ N`
below the characteristic.  It gives `CrudeBound` (the integral closure is finite over `A`) and
`ResiduallySeparable` (every residue is a root of a monic polynomial of degree `≤ N` over the
residues of the tame elements `k ∪ {s₀}`, when `s ≡ s₀` with `s₀` tame).
-/

namespace ProximityPrize.SubmissionLower.HFree6812

open WithZero Polynomial

section Basic

/-- An irreducible polynomial whose degree is a unit is separable. -/
theorem separable_of_natDegree_ne_zero {F : Type*} [Field F] {f : F[X]} (hf : Irreducible f)
    (hn : (f.natDegree : F) ≠ 0) : f.Separable := by
  rw [separable_iff_derivative_ne_zero hf]
  intro h
  obtain ⟨m, hm⟩ : ∃ m, f.natDegree = m + 1 :=
    ⟨f.natDegree - 1, (Nat.succ_pred_eq_of_pos (Irreducible.natDegree_pos hf)).symm⟩
  have h1 := congrArg (fun g => g.coeff m) h
  simp only [coeff_derivative, coeff_zero] at h1
  have h2 : ((m : F) + 1) = (f.natDegree : F) := by rw [hm]; push_cast; ring
  rw [h2, ← hm] at h1
  rcases mul_eq_zero.1 h1 with h3 | h3
  · exact (leadingCoeff_ne_zero.2 hf.ne_zero) h3
  · exact hn h3

variable {L : Type*} [Field L] (v : Valuation L ℤᵐ⁰)

/-- Elements integral over a ring of integral elements are integral. -/
theorem le_one_of_isIntegral {R : Type*} [CommRing R] [Algebra R L]
    (hR : ∀ r : R, v (algebraMap R L r) ≤ 1) {x : L} (hx : IsIntegral R x) : v x ≤ 1 := by
  obtain ⟨f, hf, hfx⟩ := hx
  by_contra h
  rw [not_le] at h
  have hx0 : v x ≠ 0 := (lt_trans zero_lt_one h).ne'
  rw [hf.as_sum, eval₂_add, eval₂_X_pow, eval₂_finsetSum] at hfx
  have hlt : v (∑ i ∈ Finset.range f.natDegree,
      eval₂ (algebraMap R L) x (C (f.coeff i) * X ^ i)) < v (x ^ f.natDegree) := by
    refine v.map_sum_lt (by rw [v.map_pow]; exact pow_ne_zero _ hx0) fun i hi => ?_
    rw [eval₂_mul, eval₂_C, eval₂_X_pow, v.map_mul, v.map_pow, v.map_pow]
    refine lt_of_le_of_lt (mul_le_of_le_one_left' (hR _)) ?_
    exact pow_lt_pow_right₀ h (Finset.mem_range.1 hi)
  have := v.map_add_eq_of_lt_left hlt
  rw [hfx, v.map_zero, v.map_pow] at this
  exact pow_ne_zero _ hx0 this.symm

end Basic

section Dedekind

variable {L : Type*} [Field L] (v : Valuation L ℤᵐ⁰)
variable (A K' : Type*) [CommRing A] [IsDedekindDomain A] [Algebra A L]
  [Field K'] [Algebra A K'] [IsFractionRing A K'] [Algebra K' L] [IsScalarTower A K' L]
  [FiniteDimensional K' L] [Algebra.IsSeparable K' L]

include K' in
/-- **`O_v` is a localization of the integral closure.** -/
theorem integral_fraction (hA : ∀ a : A, v (algebraMap A L a) ≤ 1) (hπ : ∃ x, v x = exp (-1))
    (z : L) (hz : v z ≤ 1) :
    ∃ r u : L, IsIntegral A r ∧ IsIntegral A u ∧ v u = 1 ∧ z = r / u := by
  classical
  set C := integralClosure A L
  haveI : IsDedekindDomain C := integralClosure.isDedekindDomain A K' L
  haveI : IsFractionRing C L := IsIntegralClosure.isFractionRing_of_finite_extension A K' L C
  have hCv : ∀ c : C, v (c : L) ≤ 1 := fun c => le_one_of_isIntegral v hA c.2
  let ρ : C →+* v.valuationSubring :=
    (algebraMap C L).codRestrict v.valuationSubring fun c => (Valuation.mem_valuationSubring_iff _ _).2 (hCv c)
  set 𝔓 : Ideal C := (IsLocalRing.maximalIdeal v.valuationSubring).comap ρ
  have hmem : ∀ c : C, c ∈ 𝔓 ↔ v (c : L) < 1 := by
    intro c
    rw [Ideal.mem_comap, ← IsLocalRing.residue_eq_zero_iff, ← residue_eq_zero_iff_lt_one v _ (hCv c),
      residue_of_le v _ (hCv c)]
    rfl
  have hunit : ∀ c : C, c ∉ 𝔓 → v (c : L) = 1 := fun c hc =>
    le_antisymm (hCv c) (not_lt.1 fun h => hc ((hmem c).2 h))
  have h𝔓 : 𝔓 ≠ ⊥ := by
    obtain ⟨π, hπ⟩ := hπ
    obtain ⟨y, hy0, hy⟩ := exists_integral_multiples A K' ({π} : Finset L)
    have hint := hy π (Finset.mem_singleton_self π)
    have hinj : Function.Injective (algebraMap A L) := by
      rw [IsScalarTower.algebraMap_eq A K' L]
      exact (algebraMap K' L).injective.comp (IsFractionRing.injective A K')
    have hπ0 : π ≠ 0 := by rintro rfl; rw [v.map_zero] at hπ; exact exp_ne_zero hπ.symm
    intro hbot
    have hmem' : (⟨y • π, hint⟩ : C) ∈ 𝔓 := by
      rw [hmem]
      change v (y • π) < 1
      rw [Algebra.smul_def, v.map_mul, hπ]
      refine lt_of_le_of_lt (mul_le_of_le_one_left' (hA y)) ?_
      rw [← exp_zero, exp_lt_exp]; omega
    rw [hbot, Ideal.mem_bot] at hmem'
    have h0 := congrArg (fun c : C => (c : L)) hmem'
    simp only [ZeroMemClass.coe_zero] at h0
    change y • π = 0 at h0
    rw [Algebra.smul_def] at h0
    rcases mul_eq_zero.1 h0 with h | h
    · exact hy0 (hinj (h.trans (map_zero _).symm))
    · exact hπ0 h
  haveI : 𝔓.IsPrime := Ideal.comap_isPrime _ _
  set Bp := Localization.subalgebra.ofField L 𝔓.primeCompl 𝔓.primeCompl_le_nonZeroDivisors
  haveI : IsDiscreteValuationRing Bp :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain C h𝔓 Bp
  have hBp : ∀ y : Bp, ∃ a s : C, s ∉ 𝔓 ∧ (y : L) = (a : L) / (s : L) := by
    intro y
    obtain ⟨a, s, hs, hy⟩ := y.2
    exact ⟨a, s, hs, by rw [hy, div_eq_mul_inv]; rfl⟩
  rcases ValuationRing.isInteger_or_isInteger Bp z with ⟨y, hy⟩ | ⟨y, hy⟩
  · obtain ⟨a, s, hs, hys⟩ := hBp y
    refine ⟨a, s, a.2, s.2, hunit s hs, ?_⟩
    rw [← hy, ← hys]; rfl
  · obtain ⟨a, s, hs, hys⟩ := hBp y
    have hyz : z⁻¹ = (a : L) / (s : L) := by rw [← hy, ← hys]; rfl
    by_cases hz0 : z = 0
    · exact ⟨0, 1, isIntegral_zero, isIntegral_one, v.map_one, by rw [hz0, zero_div]⟩
    by_cases ha : a ∈ 𝔓
    · exfalso
      have h1 : v z⁻¹ < 1 := by
        rw [hyz, map_div₀, hunit s hs, div_one]; exact (hmem a).1 ha
      rw [map_inv₀] at h1
      have hz1 : v z ≠ 0 := (Valuation.ne_zero_iff v).2 hz0
      have : 1 < v z := by
        by_contra hle; rw [not_lt] at hle
        exact absurd h1 (not_lt.2 (one_le_inv₀ (zero_lt_iff.2 hz1) |>.2 hle))
      exact absurd hz (not_le.2 this)
    · have ha0 : (a : L) ≠ 0 := by
        intro h; have := hunit a ha; rw [h, v.map_zero] at this; exact zero_ne_one this
      refine ⟨s, a, s.2, a.2, hunit a ha, ?_⟩
      rw [← inv_inv z, hyz, inv_div]

end Dedekind

section Tame

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (v : Valuation L ℤᵐ⁰)
  (D : Derivation K L L)
variable (A K' : Type*) [CommRing A] [IsDedekindDomain A] [Algebra A L]
  [Field K'] [Algebra A K'] [IsFractionRing A K'] [Algebra K' L] [IsScalarTower A K' L]
  [FiniteDimensional K' L] [Algebra.IsSeparable K' L]

omit [Field K] [Algebra K L] in
theorem v_le_exp_max_log (x : L) : v x ≤ exp (max 0 (v x).log) := by
  by_cases hx : v x = 0
  · rw [hx]; exact zero_le
  · calc v x = exp (v x).log := (exp_log hx).symm
      _ ≤ exp (max 0 (v x).log) := by rw [exp_le_exp]; exact le_max_right _ _

include K' in
/-- The integral closure is a finite `A`-module, so `D` is bounded on it. -/
theorem integral_tame (Λ0 : ℤ) (hA : ∀ a : A, Tame v D (exp Λ0) (algebraMap A L a)) :
    ∃ C : ℤ, ∀ r : L, IsIntegral A r → Tame v D (exp C) r := by
  classical
  set B := integralClosure A L
  haveI : Module.Finite A B := IsIntegralClosure.finite A K' L B
  obtain ⟨G, hG⟩ := Module.Finite.fg_top (R := A) (M := B)
  set n : ℤ := ∑ g ∈ G, max 0 (v (D (g : L))).log
  refine ⟨max Λ0 n, fun r hr => ?_⟩
  have hgen : ∀ g ∈ G, Tame v D (exp (max Λ0 n)) (g : L) := by
    intro g hg
    refine ⟨le_one_of_isIntegral v (fun a => (hA a).1) g.2, (v_le_exp_max_log v _).trans ?_⟩
    rw [exp_le_exp]
    refine le_trans ?_ (le_max_right _ _)
    exact Finset.single_le_sum (f := fun g : B => max 0 (v (D (g : L))).log)
      (fun _ _ => le_max_left _ _) hg
  have key : ∀ c : B, c ∈ Submodule.span A (G : Set B) → Tame v D (exp (max Λ0 n)) (c : L) := by
    intro c hc
    induction hc using Submodule.span_induction with
    | mem x hx => exact hgen x hx
    | zero => exact (tameSubring v D _).zero_mem
    | add x y _ _ hx hy => exact (tameSubring v D _).add_mem hx hy
    | smul a x _ hx =>
      change Tame v D _ (a • (x : L))
      rw [Algebra.smul_def]
      exact (tameSubring v D _).mul_mem
        ((hA a).mono v D (by rw [exp_le_exp]; exact le_max_left _ _)) hx
  exact key ⟨r, hr⟩ (by rw [hG]; exact Submodule.mem_top)

omit [Field K] [Algebra K L] in
theorem residue_add (x y : L) (hx : v x ≤ 1) (hy : v y ≤ 1) :
    residue v (x + y) = residue v x + residue v y := by
  rw [residue_of_le v _ hx, residue_of_le v _ hy,
    residue_of_le v _ ((v.map_add _ _).trans (max_le hx hy)), ← map_add]; rfl

omit [Field K] [Algebra K L] in
theorem residue_mul (x y : L) (hx : v x ≤ 1) (hy : v y ≤ 1) :
    residue v (x * y) = residue v x * residue v y := by
  have h : v (x * y) ≤ 1 := by rw [v.map_mul]; exact mul_le_one' hx hy
  rw [residue_of_le v _ hx, residue_of_le v _ hy, residue_of_le v _ h, ← map_mul]; rfl

omit [Field K] [Algebra K L] [Algebra.IsSeparable K' L] in
include K' in
/-- Residues of integral elements are separable over any subfield containing the residues of
`A`, when `[L : K'] ≤ N` and `1, …, N` are units. -/
theorem residue_isSeparable (hA : ∀ a : A, v (algebraMap A L a) ≤ 1)
    (F' : Subfield (IsLocalRing.ResidueField v.valuationSubring))
    (hF' : ∀ a : A, residue v (algebraMap A L a) ∈ F') (N : ℕ) (hN : Module.finrank K' L ≤ N)
    (hNF : ∀ n : ℕ, 0 < n → n ≤ N → (n : IsLocalRing.ResidueField v.valuationSubring) ≠ 0)
    (r : L) (hr : IsIntegral A r) :
    IsSeparable F' (residue v r) := by
  classical
  have hr1 : v r ≤ 1 := le_one_of_isIntegral v hA hr
  let ρA : A →+* v.valuationSubring := (algebraMap A L).codRestrict v.valuationSubring fun a =>
    (Valuation.mem_valuationSubring_iff _ _).2 (hA a)
  let ψ0 : A →+* IsLocalRing.ResidueField v.valuationSubring :=
    (IsLocalRing.residue v.valuationSubring).comp ρA
  have hψ0 : ∀ a, ψ0 a = residue v (algebraMap A L a) := fun a => (residue_of_le v _ (hA a)).symm
  let φ : A →+* F' := ψ0.codRestrict F' fun a => by rw [hψ0]; exact hF' a
  set f := minpoly A r
  have hfm : f.Monic := minpoly.monic hr
  have hfdeg : f.natDegree ≤ N := by
    have h1 := minpoly.isIntegrallyClosed_eq_field_fractions' K' hr
    have h2 : (minpoly K' r).natDegree ≤ Module.finrank K' L := minpoly.natDegree_le r
    rw [h1, hfm.natDegree_map] at h2
    exact h2.trans hN
  set g := f.map φ
  have hgm : g.Monic := hfm.map φ
  have hg0 : aeval (residue v r) g = 0 := by
    have hcomp : (algebraMap F' (IsLocalRing.ResidueField v.valuationSubring)).comp φ = ψ0 := by
      ext a; rfl
    rw [aeval_def, eval₂_map, hcomp, residue_of_le v r hr1]
    change eval₂ ((IsLocalRing.residue v.valuationSubring).comp ρA)
      (IsLocalRing.residue v.valuationSubring ⟨r, hr1⟩) f = 0
    rw [← hom_eval₂]
    have h0 : eval₂ ρA ⟨r, (Valuation.mem_valuationSubring_iff _ _).2 hr1⟩ f = 0 := by
      apply Subtype.ext
      have := hom_eval₂ f ρA v.valuationSubring.subtype
        ⟨r, (Valuation.mem_valuationSubring_iff _ _).2 hr1⟩
      refine this.trans ?_
      exact minpoly.aeval A r
    rw [h0, map_zero]
  have hint : IsIntegral F' (residue v r) := ⟨g, hgm, hg0⟩
  have hdvd := minpoly.dvd F' (residue v r) hg0
  have hdeg : (minpoly F' (residue v r)).natDegree ≤ N :=
    (natDegree_le_of_dvd hdvd hgm.ne_zero).trans (by rw [hfm.natDegree_map]; exact hfdeg)
  refine separable_of_natDegree_ne_zero (minpoly.irreducible hint) ?_
  intro h0
  apply hNF _ (minpoly.natDegree_pos hint) hdeg
  have := congrArg (algebraMap F' (IsLocalRing.ResidueField v.valuationSubring)) h0
  simpa using this

end Tame

section Engine

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (v : Valuation L ℤᵐ⁰)
  (D : Derivation K L L)

/-- **The engine.**  `k` a subfield on which `v` is trivial and `D` is `exp Λ0`-bounded,
`s ∈ O_v` transcendental over `k`, `L` generated by `k, s, b`, and `b` a root of a nonzero
polynomial of degree `≤ N` over `k(s)`, with `1, …, N` units.  Then `D` is crudely bounded on
`O_v`, and residually separable over `exp Λ0`-tame coefficients as soon as `s` is congruent to
an `exp Λ0`-tame element. -/
theorem engine (k : IntermediateField K L) (hkv : ∀ a ∈ k, a ≠ 0 → v a = 1) (Λ0 : ℤ)
    (hkD : ∀ a ∈ k, v (D a) ≤ exp Λ0) (s : L) (hs1 : v s ≤ 1) (hst : Transcendental k s)
    (b : L) (hgen : ∀ E : Subfield L, (∀ x ∈ k, x ∈ E) → s ∈ E → b ∈ E → ∀ x, x ∈ E)
    (P : L[X]) (hP0 : P ≠ 0) (hPb : P.eval b = 0)
    (hPc : ∀ n, P.coeff n ∈ IntermediateField.adjoin k {s}) (N : ℕ) (hPN : P.natDegree ≤ N)
    (hNK : ∀ n : ℕ, 0 < n → n ≤ N → (n : K) ≠ 0) (hπ : ∃ x, v x = exp (-1)) :
    (∃ C, CrudeBound v D C) ∧
      ∀ s₀ : L, Tame v D (exp Λ0) s₀ → v (s - s₀) < 1 → ResiduallySeparable v D (exp Λ0) := by
  classical
  let A := Polynomial k
  letI : Algebra A L := (Polynomial.aeval s).toRingHom.toAlgebra
  have hAmap : ∀ a : A, algebraMap A L a = aeval s a := fun _ => rfl
  have hinj : Function.Injective (algebraMap A L) := transcendental_iff_injective.1 hst
  haveI : FaithfulSMul A L := (faithfulSMul_iff_algebraMap_injective A L).2 hinj
  let K' := FractionRing A
  letI : Algebra K' L := FractionRing.liftAlgebra A L
  have hAK' : ∀ a : A, algebraMap K' L (algebraMap A K' a) = aeval s a := fun a => by
    rw [← IsScalarTower.algebraMap_apply]; rfl
  have hrange : ∀ x ∈ IntermediateField.adjoin k {s}, ∃ y : K', algebraMap K' L y = x := by
    intro x hx
    obtain ⟨r, t, rfl⟩ := (IntermediateField.mem_adjoin_simple_iff k x).1 hx
    exact ⟨algebraMap A K' r / algebraMap A K' t, by rw [map_div₀, hAK', hAK']⟩
  have hlift : P ∈ Polynomial.lifts (algebraMap K' L) := by
    rw [Polynomial.lifts_iff_coeff_lifts]; intro n; exact hrange _ (hPc n)
  obtain ⟨P', hP'⟩ := (Polynomial.mem_lifts P).1 hlift
  have hP'0 : P' ≠ 0 := by rintro rfl; exact hP0 (by rw [← hP', Polynomial.map_zero])
  have hP'b : aeval b P' = 0 := by rw [aeval_def, ← eval_map, hP']; exact hPb
  have hbint : IsIntegral K' b := IsAlgebraic.isIntegral ⟨P', hP'0, hP'b⟩
  have hdegb : (minpoly K' b).natDegree ≤ N := by
    refine (natDegree_le_of_dvd (minpoly.dvd K' b hP'b) hP'0).trans ?_
    rw [← natDegree_map_eq_of_injective (algebraMap K' L).injective, hP']; exact hPN
  have htop : IntermediateField.adjoin K' {b} = ⊤ := by
    have hK'E : ∀ y : K', algebraMap K' L y ∈ (IntermediateField.adjoin K' {b}).toSubfield :=
      fun y => (IntermediateField.adjoin K' {b}).algebraMap_mem y
    have hall := hgen (IntermediateField.adjoin K' {b}).toSubfield
      (fun x hx => by
        have h1 := hAK' (Polynomial.C ⟨x, hx⟩)
        rw [aeval_C] at h1
        rw [← show algebraMap k L ⟨x, hx⟩ = x from rfl, ← h1]; exact hK'E _)
      (by have h1 := hAK' Polynomial.X
          rw [aeval_X] at h1
          rw [← h1]; exact hK'E _)
      (IntermediateField.subset_adjoin K' {b} (Set.mem_singleton b))
    exact eq_top_iff.2 fun x _ => hall x
  let e : IntermediateField.adjoin K' {b} ≃ₐ[K'] L :=
    (IntermediateField.equivOfEq htop).trans IntermediateField.topEquiv
  haveI : FiniteDimensional K' (IntermediateField.adjoin K' {b}) :=
    IntermediateField.adjoin.finiteDimensional hbint
  haveI : FiniteDimensional K' L := e.toLinearEquiv.finiteDimensional
  have hfinrank : Module.finrank K' L ≤ N := by
    rw [← e.toLinearEquiv.finrank_eq, IntermediateField.adjoin.finrank hbint]; exact hdegb
  have hcharL : ∀ n : ℕ, 0 < n → n ≤ N → (n : L) ≠ 0 := by
    intro n hn hnN h
    apply hNK n hn hnN
    rw [← map_natCast (algebraMap K L)] at h
    exact (map_eq_zero_iff _ (algebraMap K L).injective).1 h
  haveI : Algebra.IsSeparable K' L := ⟨fun x => by
    have hx : IsIntegral K' x := Algebra.IsIntegral.isIntegral x
    refine separable_of_natDegree_ne_zero (minpoly.irreducible hx) fun h => ?_
    refine hcharL _ (minpoly.natDegree_pos hx) ((minpoly.natDegree_le x).trans hfinrank) ?_
    have := congrArg (algebraMap K' L) h
    rwa [map_natCast, map_zero] at this⟩
  -- `v` and `D` on `A`
  have hkle : ∀ a ∈ k, v a ≤ 1 := by
    intro a ha
    by_cases h0 : a = 0
    · rw [h0, v.map_zero]; exact zero_le
    · exact (hkv a ha h0).le
  set Λ1 : ℤ := max Λ0 (max 0 (v (D s)).log)
  have hAtame : ∀ Λ : ℤ, Λ0 ≤ Λ → Tame v D (exp Λ) s → ∀ a : A, Tame v D (exp Λ) (aeval s a) := by
    intro Λ hΛ hs a
    induction a using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add]; exact (tameSubring v D _).add_mem hp hq
    | monomial n c =>
      rw [aeval_monomial]
      refine (tameSubring v D _).mul_mem ⟨hkle _ c.2, (hkD _ c.2).trans ?_⟩
        ((tameSubring v D _).pow_mem hs n)
      rw [exp_le_exp]; exact hΛ
  have hsΛ1 : Tame v D (exp Λ1) s :=
    ⟨hs1, (v_le_exp_max_log v _).trans (by rw [exp_le_exp]; exact le_max_right _ _)⟩
  have hA1 : ∀ a : A, Tame v D (exp Λ1) (algebraMap A L a) :=
    hAtame Λ1 (le_max_left _ _) hsΛ1
  have hfrac := integral_fraction v A K' (fun a => (hA1 a).1) hπ
  refine ⟨?_, fun s₀ hs₀ hss₀ => ?_⟩
  · obtain ⟨C, hC⟩ := integral_tame v D A K' Λ1 hA1
    refine ⟨C, continuity_of_localization v D (tameSubring v D (exp C)) C (fun r hr => hr)
      fun z hz => ?_⟩
    obtain ⟨r, u, hr, hu, hu1, rfl⟩ := hfrac z hz
    exact ⟨r, hC r hr, u, hC u hu, hu1, rfl⟩
  · set S : Set L := (k : Set L) ∪ {s₀}
    have hS : ∀ z ∈ S, Tame v D (exp Λ0) z := by
      rintro z (hz | hz)
      · exact ⟨hkle z hz, hkD z hz⟩
      · rw [Set.mem_singleton_iff.1 hz]; exact hs₀
    set F' := Subfield.closure (residue v '' S)
    have hs₀1 : v s₀ ≤ 1 := hs₀.1
    have hress : residue v s = residue v s₀ := by
      have h1 : v (s - s₀) ≤ 1 := hss₀.le
      have h2 := residue_add v (s - s₀) s₀ h1 hs₀1
      rw [sub_add_cancel, (residue_eq_zero_iff_lt_one v _ h1).2 hss₀, zero_add] at h2
      exact h2
    have hF' : ∀ a : A, residue v (algebraMap A L a) ∈ F' := by
      intro a
      induction a using Polynomial.induction_on' with
      | add p q hp hq =>
        rw [map_add, residue_add v _ _ (hA1 p).1 (hA1 q).1]; exact F'.add_mem hp hq
      | monomial n c =>
        have hpow : ∀ n : ℕ, v (s ^ n) ≤ 1 := fun n => by rw [v.map_pow]; exact pow_le_one' hs1 n
        rw [hAmap, aeval_monomial]
        change residue v ((c : L) * s ^ n) ∈ F'
        rw [residue_mul v _ _ (hkle _ c.2) (hpow n)]
        refine F'.mul_mem (Subfield.subset_closure ⟨c, Or.inl c.2, rfl⟩) ?_
        induction n with
        | zero =>
          rw [pow_zero]; exact Subfield.subset_closure ⟨1, Or.inl k.one_mem, rfl⟩
        | succ n ih =>
          rw [pow_succ, residue_mul v _ _ (hpow n) hs1, hress]
          exact F'.mul_mem ih (Subfield.subset_closure ⟨s₀, Or.inr rfl, rfl⟩)
    have hNF : ∀ n : ℕ, 0 < n → n ≤ N →
        (n : IsLocalRing.ResidueField v.valuationSubring) ≠ 0 := by
      intro n hn hnN h
      have hvn : v (n : L) = 1 := hkv _ (by
        rw [← map_natCast (algebraMap K L)]; exact k.algebraMap_mem _) (hcharL n hn hnN)
      have h1 : residue v (n : L) = 0 := by
        rw [residue_of_le v _ hvn.le, ← h, ← map_natCast (IsLocalRing.residue _)]; rfl
      rw [residue_eq_zero_iff_lt_one v _ hvn.le, hvn] at h1
      exact lt_irrefl _ h1
    have hsepres := residue_isSeparable v A K' (fun a => (hA1 a).1) F' hF' N hfinrank hNF
    haveI : Algebra.IsSeparable F' (IsLocalRing.ResidueField v.valuationSubring) := ⟨fun x => by
      obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective x
      obtain ⟨r, u, hr, hu, hu1, hz⟩ := hfrac z z.2
      have hr1 : v r ≤ 1 := le_one_of_isIntegral v (fun a => (hA1 a).1) hr
      have hu0 : residue v u ≠ 0 := fun h =>
        (lt_irrefl (1 : ℤᵐ⁰)) (hu1 ▸ (residue_eq_zero_iff_lt_one v u hu1.le).1 h)
      have hzr : residue v (z : L) * residue v u = residue v r := by
        rw [← residue_mul v _ _ z.2 hu1.le, hz, div_mul_cancel₀]
        intro h; rw [h, v.map_zero] at hu1; exact zero_ne_one hu1
      have hx : IsLocalRing.residue v.valuationSubring z = residue v r / residue v u := by
        rw [eq_div_iff hu0, ← hzr, residue_of_le v _ z.2]
      rw [hx]
      exact (separableClosure F' _).div_mem (hsepres r hr) (hsepres u hu)⟩
    exact residuallySeparable_of_isSeparable v D (exp Λ0) S hS

end Engine

end ProximityPrize.SubmissionLower.HFree6812


