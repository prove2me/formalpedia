-- Prove2me | Definitions.Def_NumberField_Completion_HenselianLocalRing
-- name    : NumberField_Completion_HenselianLocalRing
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/bdcddeed-0375-5a2e-8b1f-1bd91873182b
-- title:
--   Henselian local rings: compact local rings and adic completions
-- statement:
--   The module supplies Henselianity and adic completeness for the local rings occurring as completions of rings of integers, and a root-extraction tool built from them.
--
--   The first group concerns a commutative ring $R$ carrying a topological ring structure which is compact, Hausdorff, Noetherian and local. Under these standing assumptions an instance asserts `IsAdicComplete (maximalIdeal R) R`, i.e. that $R$ is separated and complete for the $\mathfrak m$-adic filtration: every sequence $(f_n)$ with $f_{n+1} \equiv f_n \pmod{\mathfrak m^n}$ has a limit $L$ with $L \equiv f_n \pmod{\mathfrak m^n}$ for all $n$. The proof takes the nested closed cosets $f_n + \mathfrak m^n$ and uses compactness to produce a point of their intersection. Next, [`henselianLocalRing_of_henselianRing`](../def/NumberField_Completion_HenselianLocalRing.html#L47) records that for a local ring $S$ the property `HenselianRing S (maximalIdeal S)` (lifting of simple roots of monic polynomials modulo $\mathfrak m$, with the unit condition on the derivative stated in the quotient) yields `HenselianLocalRing S`; combined with adic completeness this gives a `HenselianLocalRing` instance for every compact Hausdorff Noetherian topological local ring.
--
--   These are then applied, for a number field $K$ and a finite place $v \in$ `HeightOneSpectrum (𝓞 K)`, to the valuation ring $\mathcal O_{K_v} =$ `v.adicCompletionIntegers K`: it is adically complete for its maximal ideal and is a Henselian local ring, the compactness and discrete-valuation-ring inputs coming from the completion modules imported here.
--
--   Finally, two root-extraction statements for an arbitrary Henselian local ring $R$. Given a unit $u$, a natural number $n$ whose image in $R$ is a unit, and $a_0$ with $a_0^n - u \in \mathfrak m$, there is $a \in R$ with $a^n = u$ and $a \equiv a_0 \pmod{\mathfrak m}$; the polynomial used is $X^n - u$, whose derivative at $a_0$ is $n a_0^{n-1}$. The specialisation with $a_0 = 1$ gives: if $u \equiv 1 \pmod{\mathfrak m}$ and $n$ is invertible in $R$, then $u$ has an $n$-th root congruent to $1$ modulo $\mathfrak m$.
--
--   **Relation to Mathlib.** `HenselianRing`, `HenselianLocalRing` and `IsAdicComplete` are Mathlib notions; what is added here is the passage from Henselianity along the maximal ideal to `HenselianLocalRing`, the adic completeness of a compact Hausdorff Noetherian topological local ring, the resulting instances for `v.adicCompletionIntegers K`, and the $n$-th root lemmas.
--
--   **Where it is used.** The Henselian property of $\mathcal O_{K_v}$ and the extraction of $n$-th roots of units congruent to $1$ are the local inputs used when analysing units and Teichmüller-type decompositions in the completions at finite places, which enter the local conditions on Galois representations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_NumberField_Completion_HenselianLocalRing.lean

import Mathlib
import Definitions.Def_NumberField_Completion_Finite

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false

open IsLocalRing Pointwise

noncomputable section

section CompactNoetherianLocal

variable {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [CompactSpace R] [T2Space R] [IsNoetherianRing R] [IsLocalRing R]

instance (priority := 80) instIsAdicCompleteMaximalIdealOfCompactSpace :
    IsAdicComplete (maximalIdeal R) R where
  prec' f hf := by

    let S : ℕ → Set R := fun n => f n +ᵥ ((maximalIdeal R ^ n : Ideal R) : Set R)

    have hSclosed : ∀ n, IsClosed (S n) := fun n =>
      (IsNoetherianRing.isClosed_ideal (maximalIdeal R ^ n)).vadd (f n)
    have hSne : ∀ n, (S n).Nonempty := fun n =>
      ⟨f n, ⟨0, Ideal.zero_mem _, by simp⟩⟩

    have hSmono : ∀ n, S (n + 1) ⊆ S n := by
      intro n x ⟨y, hy, hxy⟩
      have hcauchy : f (n + 1) - f n ∈ (maximalIdeal R) ^ n := by
        have h := hf (Nat.le_succ n)
        rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← neg_sub, neg_mem_iff] at h
      exact ⟨(f (n + 1) - f n) + y,
        Ideal.add_mem _ hcauchy (Ideal.pow_le_pow_right (Nat.le_succ n) hy),
        by simp only [vadd_eq_add] at hxy ⊢; linear_combination hxy⟩

    obtain ⟨L, hL⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S
      hSmono hSne (hSclosed 0).isCompact hSclosed
    refine ⟨L, fun n => ?_⟩
    obtain ⟨y, hy, hLy⟩ := Set.mem_iInter.mp hL n
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    simp only [vadd_eq_add] at hLy
    have h : f n - L = -y := by linear_combination hLy
    rw [h]; exact neg_mem hy

theorem henselianLocalRing_of_henselianRing {S : Type*} [CommRing S] [IsLocalRing S]
    [HenselianRing S (maximalIdeal S)] : HenselianLocalRing S where
  is_henselian f hf a₀ h₁ h₂ :=
    HenselianRing.is_henselian f hf a₀ h₁ (h₂.map (Ideal.Quotient.mk (maximalIdeal S)))

instance (priority := 80) instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing :
    HenselianLocalRing R :=
  henselianLocalRing_of_henselianRing

end CompactNoetherianLocal

section AdicCompletionIntegers

open IsDedekindDomain NumberField

variable (K : Type*) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

instance NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers :
    IsAdicComplete (maximalIdeal (v.adicCompletionIntegers K)) (v.adicCompletionIntegers K) :=
  instIsAdicCompleteMaximalIdealOfCompactSpace

instance NumberField.instHenselianLocalRingAdicCompletionIntegers :
    HenselianLocalRing (v.adicCompletionIntegers K) :=
  instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing

example : HenselianLocalRing (Valued.integer (v.adicCompletion K)) :=
  inferInstanceAs (HenselianLocalRing (v.adicCompletionIntegers K))

end AdicCompletionIntegers

section NthRootEngine

open Polynomial

variable {R : Type*} [CommRing R] [HenselianLocalRing R]

theorem exists_nthRoot_of_isUnit_natCast {u : R} (hu : IsUnit u) {n : ℕ}
    (hn : IsUnit (n : R)) {a₀ : R} (ha₀ : a₀ ^ n - u ∈ maximalIdeal R) :
    ∃ a : R, a ^ n = u ∧ a - a₀ ∈ maximalIdeal R := by

  have hn0 : n ≠ 0 := by
    rintro rfl; simp only [Nat.cast_zero] at hn; exact not_isUnit_zero hn

  have ha₀unit : IsUnit a₀ := by
    rw [← isUnit_pow_iff hn0, ← notMem_maximalIdeal]
    intro hmem
    have h : u ∈ maximalIdeal R := by
      have := Ideal.sub_mem _ hmem ha₀; simpa using this
    exact notMem_maximalIdeal.mpr hu h

  set f : R[X] := X ^ n - C u with hfdef
  have hfmonic : f.Monic := by
    simpa [hfdef] using monic_X_pow_sub_C u hn0
  have hfeval : f.eval a₀ ∈ maximalIdeal R := by simpa [hfdef] using ha₀
  have hfderiv : IsUnit (f.derivative.eval a₀) := by
    simp only [hfdef, derivative_sub, derivative_X_pow, derivative_C, sub_zero,
      eval_mul, eval_natCast, eval_pow, eval_X, map_natCast]
    exact hn.mul (ha₀unit.pow (n - 1))
  obtain ⟨a, hroot, hmem⟩ := HenselianLocalRing.is_henselian f hfmonic a₀ hfeval hfderiv
  refine ⟨a, ?_, hmem⟩
  have h : a ^ n - u = 0 := by simpa [hfdef] using hroot
  linear_combination h

theorem exists_nthRoot_of_sub_one_mem_maximalIdeal {u : R} (hu : u - 1 ∈ maximalIdeal R)
    {n : ℕ} (hn : IsUnit (n : R)) :
    ∃ a : R, a ^ n = u ∧ a - 1 ∈ maximalIdeal R := by
  refine exists_nthRoot_of_isUnit_natCast ?_ hn (a₀ := 1) ?_
  · rw [← notMem_maximalIdeal]
    intro hmem

    have h := Ideal.sub_mem _ hmem hu
    simp at h
  · simpa using (Ideal.neg_mem_iff _).mpr hu

end NthRootEngine

section Gates

open IsDedekindDomain NumberField

example (K : Type*) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    HenselianLocalRing (v.adicCompletionIntegers K) := inferInstance

example (K : Type*) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    IsAdicComplete (maximalIdeal (v.adicCompletionIntegers K)) (v.adicCompletionIntegers K) :=
  inferInstance

example {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [CompactSpace R] [T2Space R] [IsNoetherianRing R] [IsLocalRing R] :
    HenselianLocalRing R := inferInstance

example {R : Type*} [CommRing R] [HenselianLocalRing R] (x : R) (hx : x ∈ maximalIdeal R)
    {n : ℕ} (hn : IsUnit (n : R)) :
    ∃ a : R, a ^ n = 1 + x ∧ a - 1 ∈ maximalIdeal R :=
  exists_nthRoot_of_sub_one_mem_maximalIdeal (by simpa) hn

end Gates

/-- info: 'instIsAdicCompleteMaximalIdealOfCompactSpace' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms instIsAdicCompleteMaximalIdealOfCompactSpace

/-- info: 'instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing

/-- info: 'NumberField.instHenselianLocalRingAdicCompletionIntegers' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NumberField.instHenselianLocalRingAdicCompletionIntegers

/-- info: 'exists_nthRoot_of_isUnit_natCast' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_nthRoot_of_isUnit_natCast

/-- info: 'exists_nthRoot_of_sub_one_mem_maximalIdeal' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_nthRoot_of_sub_one_mem_maximalIdeal


