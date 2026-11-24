-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_FiniteWeightedEuler
-- name    : Sensitivity214439_Phase0_RiemannHypothesisCurves_FiniteWeightedEuler
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T12:14:56.9015+00:00
-- url     : https://prove2.me/theorems/2dba4ed6-5b1a-4dec-ab08-95809535fcb7
-- title:
--   Weighted multiplicity vectors and finite coefficient antidiagonals
-- statement:
--   Given natural degree weights d_i, convert a finitely supported multiplicity vector m to the degree vector with entries m_i d_i, and recover multiplicities by componentwise division. For a finite index set T and total degree n, define the finite antidiagonal of vectors supported in T whose entries sum to n and whose i-th entry is divisible by d_i. When every d_i is positive and T contains every index with d_i ≤ n, these vectors are in bijection with all finitely supported multiplicities satisfying the weighted equation Σ_i m_i d_i = n. The accompanying support and sum identities justify this finite reindexing.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source research/hec-lean433/RiemannHypothesisCurves/FiniteWeightedEuler.lean lines 21–107; SHA256 d42988791e3b0a458c77b5682af6868195554567c5fd62062a5c14f75fc34356; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Mathlib.Data.Finsupp.Weight
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Tactic.LinearCombination
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace Finset
end Finset
namespace PaleyWeil
end PaleyWeil
namespace PowerSeries
end PowerSeries



/-!
The coefficient identity for a finite weighted Euler product.  The antidiagonal
bijection follows the finite counting argument in Christian Merten's
`WeilConjectures/EulerProductAux.lean` (Apache-2.0), extended here to arbitrary
integer weights and kept entirely finite.
-/

open scoped PowerSeries
open PowerSeries Finset

namespace PaleyWeil

noncomputable section

variable {ι : Type*}

def degreeVector (d : ι → ℕ) (m : ι →₀ ℕ) : ι →₀ ℕ :=
  Finsupp.ofSupportFinite (fun i ↦ m i * d i)
    (m.hasFiniteSupport.subset fun i hi ↦ by
      simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at hi
      exact hi.1)

def multiplicityVector (d : ι → ℕ) (l : ι →₀ ℕ) : ι →₀ ℕ :=
  Finsupp.ofSupportFinite (fun i ↦ l i / d i)
    (l.hasFiniteSupport.subset fun i hi ↦ by
      simp only [Function.mem_support, ne_eq] at hi ⊢
      intro h
      exact hi (by rw [h, Nat.zero_div]))

@[simp] theorem degreeVector_apply (d : ι → ℕ) (m : ι →₀ ℕ) (i : ι) :
    degreeVector d m i = m i * d i := rfl

@[simp] theorem multiplicityVector_apply (d : ι → ℕ) (l : ι →₀ ℕ) (i : ι) :
    multiplicityVector d l i = l i / d i := rfl

theorem weighted_support_subset (d : ι → ℕ) (T : Finset ι) (n : ℕ)
    (hT : ∀ i, d i ≤ n → i ∈ T)
    (m : ι →₀ ℕ) (hm : (m.sum fun i k ↦ k * d i) = n) : m.support ⊆ T := by
  intro i hi
  apply hT i
  have hle : m i * d i ≤ m.sum fun i k ↦ k * d i :=
    Finset.single_le_sum (f := fun i ↦ m i * d i) (fun _ _ ↦ Nat.zero_le _) hi
  have hpos : 1 ≤ m i := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
  nlinarith

theorem sum_degreeVector (d : ι → ℕ) (T : Finset ι) (m : ι →₀ ℕ)
    (hm : m.support ⊆ T) :
    (m.sum fun i k ↦ k * d i) = ∑ i ∈ T, degreeVector d m i := by
  classical
  rw [Finsupp.sum, Finset.sum_subset hm fun i _ hi ↦ by
    rw [Finsupp.notMem_support_iff.mp hi, zero_mul]]
  rfl

def divisibleAntidiag [DecidableEq ι] (d : ι → ℕ) (T : Finset ι) (n : ℕ) :
    Finset (ι →₀ ℕ) := by
  classical
  exact (Finset.finsuppAntidiag T n).filter (fun l ↦ ∀ i ∈ T, d i ∣ l i)

def weightedAntidiagEquiv [DecidableEq ι] (d : ι → ℕ) (T : Finset ι) (n : ℕ)
    (hd : ∀ i, d i ≠ 0) (hT : ∀ i, d i ≤ n → i ∈ T) :
    {l // l ∈ divisibleAntidiag d T n} ≃
      {m : ι →₀ ℕ // (m.sum fun i k ↦ k * d i) = n} := by
  classical
  refine
    { toFun := fun l ↦ ⟨multiplicityVector d l.1, ?_⟩
      invFun := fun m ↦ ⟨degreeVector d m.1, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · obtain ⟨hl, hdvd⟩ := Finset.mem_filter.mp l.2
    rw [Finset.mem_finsuppAntidiag] at hl
    have hlm : degreeVector d (multiplicityVector d l.1) = l.1 := by
      ext i
      simp only [degreeVector_apply, multiplicityVector_apply]
      by_cases hi : i ∈ T
      · exact Nat.div_mul_cancel (hdvd i hi)
      · rw [Finsupp.notMem_support_iff.mp fun h ↦ hi (hl.2 h), Nat.zero_div, zero_mul]
    have hsub : (multiplicityVector d l.1).support ⊆ T := fun i hi ↦ by
      by_contra hiT
      apply Finsupp.mem_support_iff.mp hi
      rw [multiplicityVector_apply,
        Finsupp.notMem_support_iff.mp fun h ↦ hiT (hl.2 h), Nat.zero_div]
    rw [sum_degreeVector d T _ hsub, hlm, hl.1]
  · have hsub := weighted_support_subset d T n hT m.1 m.2
    refine Finset.mem_filter.mpr ⟨Finset.mem_finsuppAntidiag.mpr ⟨?_, fun i hi ↦ ?_⟩,
      fun i _ ↦ ⟨m.1 i, by rw [degreeVector_apply, mul_comm]⟩⟩
    · rw [← sum_degreeVector d T _ hsub, m.2]
    · refine hsub (Finsupp.mem_support_iff.mpr fun h ↦ ?_)
      apply Finsupp.mem_support_iff.mp hi
      rw [degreeVector_apply, h, zero_mul]
  · intro l
    obtain ⟨hl, hdvd⟩ := Finset.mem_filter.mp l.2
    rw [Finset.mem_finsuppAntidiag] at hl
    refine Subtype.ext (Finsupp.ext fun i ↦ ?_)
    change degreeVector d (multiplicityVector d l.1) i = l.1 i
    rw [degreeVector_apply, multiplicityVector_apply]
    by_cases hi : i ∈ T
    · exact Nat.div_mul_cancel (hdvd i hi)
    · rw [Finsupp.notMem_support_iff.mp fun h ↦ hi (hl.2 h), Nat.zero_div, zero_mul]
  · intro m
    refine Subtype.ext (Finsupp.ext fun i ↦ ?_)
    change multiplicityVector d (degreeVector d m.1) i = m.1 i
    rw [multiplicityVector_apply, degreeVector_apply,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero (hd i))]





end
end PaleyWeil


