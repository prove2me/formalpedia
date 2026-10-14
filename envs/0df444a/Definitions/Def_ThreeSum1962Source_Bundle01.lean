-- Prove2me | Definitions.Def_ThreeSum1962Source_Bundle01
-- name    : ThreeSum1962Source_Bundle01
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-14T05:33:10.620503+00:00
-- url     : https://prove2.me/theorems/d9a25a7e-4362-4ca4-9ec8-7af177a47e51
-- title:
--   Arithmetic, subset transforms, and encoding parameters
-- statement:
--   This bundle introduces the finite mathematical objects used by the construction: modular incidence counts, weighted histograms and correlations, local subset graphs, one-hot hash events, greedy covers, positional radix representations, and compact subset-mask addresses. For an integer-valued function on finite subsets, its zeta transform is
--   $$
--   Zf(Q)=\sum_{S\subseteq Q}f(S).
--   $$
--   The accompanying definitions include Möbius transforms, partial transforms, forced prefixes and sparse query boxes. It also fixes the rational exponent parameters, local prime and bucket-capacity choices, deterministic coloring family, original-triple indexing, and polynomial coefficient interfaces. These objects provide the common vocabulary for the later counting and machine-execution results.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/Arithmetic.lean#L38-L289
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/Asymptotics.lean#L41-L43
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/Balancing.lean#L19-L19
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/Bands.lean#L42-L104
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/BinarySearch.lean#L16-L109
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/BlockRows.lean#L22-L114
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/BlockSourceEncoding.lean#L52-L52
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/BruteTripleIndex.lean#L7-L55
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/Coloring.lean#L56-L166
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/CyclicFold.lean#L48-L140
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/Greedy.lean#L16-L62
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/HashFamily.lean#L28-L704
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/Histograms.lean#L22-L89
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/Karatsuba.lean#L21-L30
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/KaratsubaBounds.lean#L35-L35
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LayerCounts.lean#L20-L35
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LocalCoverBounds.lean#L29-L300
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/MaskErase.lean#L16-L21
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/OneHotMask.lean#L20-L74
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/Parameters.lean#L31-L518
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/PrimeChain.lean#L19-L20
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/Radix.lean#L25-L40
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/SourceFlagProduct.lean#L12-L12
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/SparseBoxes.lean#L27-L547
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/Subset.lean#L27-L478
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/SubsetAddress.lean#L27-L434
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/SubsetTransport.lean#L12-L13
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/WeightedModuli.lean#L16-L16
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSumApsp/Lang/Logic.lean#L55-L59
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSumApsp/Util/List.lean#L73-L78

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_Arithmetic


set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# Exact arithmetic interface for the deterministic histogram construction

These are finite arithmetic and counting theorems.  They do not assert a
running-time bound or the existence of a word-RAM implementation.
-/

namespace ThreeSum.Arithmetic

open Finset
open scoped BigOperators

/-! ## Guarded arithmetic-to-radix lifts -/















/-- The only three signed lifts queried by the algorithm. -/
def SmallLift (j : ℤ) : Prop := j = -1 ∨ j = 0 ∨ j = 1





































































































/-! ## The weighted false-count identity -/

























/-- Integer-valued divisibility is converted to a natural indicator. -/
def dividesIndicator (m x : ℤ) : ℕ := if m ∣ x then 1 else 0

/-- Number of auxiliary divisibility tests failed by an integer difference. -/
def missWeight (L : Finset ℤ) (x : ℤ) : ℕ :=
  ∑ l ∈ L, if l ∣ x then 0 else 1



































def modCount {ι : Type*} (T : Finset ι) (difference : ι → ℤ) (m : ℤ) : ℕ :=
  ∑ i ∈ T, dividesIndicator m (difference i)

def weightedFalseCount {ι : Type*} (T : Finset ι) (difference : ι → ℤ)
    (L : Finset ℤ) (m : ℤ) : ℕ :=
  ∑ i ∈ T, if m ∣ difference i then missWeight L (difference i) else 0










































/-- Pairwise coprime auxiliary moduli whose product exceeds the absolute
difference separate every nonzero difference.  No primality is necessary. -/
theorem exists_aux_not_dvd_of_prod_bound (L : Finset ℤ) (x : ℤ)
    (hcop : (L : Set ℤ).Pairwise (fun a b => IsCoprime a b))
    (hx : x ≠ 0) (hbound : x.natAbs < (∏ l ∈ L, l).natAbs) :
    ∃ l ∈ L, ¬ l ∣ x := by
  classical
  by_contra hnone
  push_neg at hnone
  have hdiv : (∏ l ∈ L, l) ∣ x := Finset.prod_dvd_of_coprime hcop hnone
  have hle := Int.natAbs_le_of_dvd_ne_zero hdiv hx
  omega

















/-! ## Exact early YES from per-original-triple representation caps -/

def fiberWeight {ι τ : Type*} [DecidableEq τ] (I : Finset ι)
    (owner : ι → τ) (weight : ι → ℕ) (t : τ) : ℕ :=
  ∑ i ∈ I, if owner i = t then weight i else 0































































end ThreeSum.Arithmetic

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LocalCoverBounds


set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# Finite numerical bounds for the local cover

The graph degree bound follows from exact finite cardinalities: the degree
is no larger than the number of vertices, while vertices times degree equal
outputs times representations per output.  This avoids any approximation
of factorials.  The prime-interval and normalized first-moment estimates
are stated explicitly in terms of the concrete binomial coefficients.
-/

namespace ThreeSum.LocalCoverBounds

open scoped BigOperators

def outputCount (L h : ℕ) : ℕ := L.choose (2 * h)
def vertexCount (L h : ℕ) : ℕ := L.choose h
def degree (L h : ℕ) : ℕ := (L - h).choose h
def groupSize (h : ℕ) : ℕ := (2 * h).choose h























































































/-- The exact expectation of the actual edge count, once its hash moment
identity has been proved. -/
noncomputable def mean (L h p : ℕ) : ℝ :=
  (outputCount L h : ℝ) * groupSize h / (p : ℝ) ^ 2



































/-! ## A deterministic selected prime -/

/-- For positive `N`, this is exactly the integer ceiling of `sqrt N`. -/
def rootCeiling (N : ℕ) : ℕ := Nat.sqrt (N - 1) + 1

theorem rootCeiling_pos (N : ℕ) : 0 < rootCeiling N := by
  unfold rootCeiling
  omega

theorem le_rootCeiling_sq (N : ℕ) : N ≤ rootCeiling N ^ 2 := by
  have hs := Nat.lt_succ_sqrt' (N - 1)
  simp only [Nat.succ_eq_add_one] at hs
  unfold rootCeiling
  omega

theorem rootCeiling_sq_le_four {N : ℕ} (hN : 0 < N) : rootCeiling N ^ 2 ≤ 4 * N := by
  have hmono := Nat.sqrt_le_sqrt (Nat.sub_le N 1)
  have hpos := Nat.sqrt_pos.mpr hN
  have hlo := Nat.sqrt_le' N
  have hroot : rootCeiling N ≤ 2 * Nat.sqrt N := by
    unfold rootCeiling
    omega
  have hsq := Nat.pow_le_pow_left hroot 2
  nlinarith

/-- The interval is finite and explicitly enumerated; primality is decidable. -/
def primeCandidates (N : ℕ) : Finset ℕ :=
  (Finset.range (2 * rootCeiling N + 1)).filter
    (fun p => Nat.Prime p ∧ rootCeiling N < p)

theorem mem_primeCandidates {N p : ℕ} :
    p ∈ primeCandidates N ↔ Nat.Prime p ∧ rootCeiling N < p ∧ p ≤ 2 * rootCeiling N := by
  simp only [primeCandidates, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hup, hp, hlo⟩
    exact ⟨hp, hlo, by omega⟩
  · rintro ⟨hp, hlo, hup⟩
    exact ⟨by omega, hp, hlo⟩

theorem primeCandidates_nonempty (N : ℕ) : (primeCandidates N).Nonempty := by
  obtain ⟨p, hp, hlo, hup⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (rootCeiling N) (rootCeiling_pos N).ne'
  exact ⟨p, mem_primeCandidates.mpr ⟨hp, hlo, hup⟩⟩

def selectedPrime (N : ℕ) : ℕ :=
  (primeCandidates N).min' (primeCandidates_nonempty N)

theorem selectedPrime_spec (N : ℕ) :
    Nat.Prime (selectedPrime N) ∧ rootCeiling N < selectedPrime N ∧
      selectedPrime N ≤ 2 * rootCeiling N :=
  mem_primeCandidates.mp (Finset.min'_mem _ _)




theorem selectedPrime_sq_lower (N : ℕ) : N ≤ selectedPrime N ^ 2 := by
  exact (le_rootCeiling_sq N).trans
    (Nat.pow_le_pow_left (selectedPrime_spec N).2.1.le 2)

theorem selectedPrime_sq_upper {N : ℕ} (hN : 0 < N) :
    selectedPrime N ^ 2 ≤ 16 * N := by
  have hu := (selectedPrime_spec N).2.2
  have hsq := Nat.pow_le_pow_left hu 2
  have hr := rootCeiling_sq_le_four hN
  nlinarith















/-! ## Exact integer rounding of the separable bucket cap -/

/-- Integer ceiling of `4*(1+V/p)`, expressed using computable ceiling division. -/
def bucketCap (V p : ℕ) : ℕ := (4 * (p + V)) ⌈/⌉ p




























/-! ## The actual local parameters at `L=512*h` -/

def localThreshold (h : ℕ) : ℕ := outputCount (512 * h) h * 2 ^ (2 * h)
def localPrime (h : ℕ) : ℕ := selectedPrime (localThreshold h)
def localBucketCap (h : ℕ) : ℕ := bucketCap (vertexCount (512 * h) h) (localPrime h)

theorem localThreshold_pos (h : ℕ) : 0 < localThreshold h :=
  Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.pow_pos (by decide))







theorem localPrime_prime (h : ℕ) : Nat.Prime (localPrime h) :=
  (selectedPrime_spec (localThreshold h)).1

theorem localPrime_pos (h : ℕ) : 0 < localPrime h := (localPrime_prime h).pos




theorem localPrime_sq_lower (h : ℕ) :
    outputCount (512 * h) h * 2 ^ (2 * h) ≤ localPrime h ^ 2 :=
  selectedPrime_sq_lower (localThreshold h)

theorem localPrime_sq_upper (h : ℕ) :
    localPrime h ^ 2 ≤ 16 * (outputCount (512 * h) h * 2 ^ (2 * h)) :=
  selectedPrime_sq_upper (localThreshold_pos h)
































end ThreeSum.LocalCoverBounds

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSumApsp_Lang_Logic
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/



set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# Proof rules for the light language

Ends lim P d s σ T Q says: the statement s, started in σ, ends within T steps in a state that
satisfies Q.  There is one rule for each construct; a rule turns a goal about a statement into goals
about its parts, so a proof follows the text of the program from top to bottom.  Recursion needs no
rule: a statement about a recursive procedure is proved by induction (in Lean) on a measure, and the
rule for calls unfolds the body.

There are three rules for loops: with an invariant indexed by the number of the round and a cost for
each round (Ends.while), the same with one cost for all rounds (Ends.whileConst), and, for a loop
whose number of rounds depends on the data, with a quantity that every round decreases
(Ends.whileVariant).

The file also has the basic facts about runs (a run stays a run when procedures are appended to the
program), notation for writing programs, the simplification set
`light_norm`, and the standing assumptions `Std` about the limits.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Runs -/















/-- Procedure number i of a list that is appended to the program P₀ has the number |P₀| + i. -/
theorem getElem?_append_length_add (P₀ : Program) {R : Program} {i : ℕ} {body : Stmt}
    (h : R[i]? = some body) : (P₀ ++ R)[P₀.length + i]? = some body := by
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
  exact h















/-! ## The rules -/






































































































































/-! ## Notation for writing programs

Not trusted: a theorem about a program does not depend on how the program was typed in. -/




























/-! ## Simplification -/

attribute [simp] Expr.val Expr.cost Expr.Safe Op.eval Cond.Holds Cond.cost Cond.Safe frame
















/-! ## The limits -/
























end Light

end
end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_Asymptotics


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.Parameters
end ThreeSum.Parameters


/-!
# Absorbing the explicit subpolynomial overhead budget

`Parameters` proves the real exponent ledger. This file proves the analytic absorption
step, including an explicit overhead envelope whose four terms account for:

* exhaustive local work on blocks of size proportional to `(log n)^(1/3)`;
* prime-window enumeration on the `exp(O(sqrt(log n)))` scale;
* polynomial local factors raised to `O(log n / (log n)^(1/3))` schedules;
* fixed constants and ordinary polylogarithmic factors.

This file does **not** assert that the algorithm has the stated envelope without a proof.
Its final runtime lemmas explicitly require the eventual upper bound on the actual cost.
Deriving that bound from the deterministic routines, their word sizes, all loop counts,
the integer-rounded block schedule and prime construction remains an algorithmic obligation.
-/

noncomputable section

namespace ThreeSum.Asymptotics

open Filter Real _root_.Asymptotics
open ThreeSum.Parameters
open scoped Topology

set_option maxRecDepth 10000











theorem log_nat_tendsto_atTop :
    Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop














































end ThreeSum.Asymptotics

end
end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_Balancing


set_option autoImplicit false
set_option relaxedAutoImplicit false


/-! # An exact global offset chosen by a cyclic correlation -/

namespace ThreeSum.Balancing

open Finset
open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

def correlation (F H : G → ℕ) (d : G) : ℕ := ∑ k, F k * H (k - d)











































end ThreeSum.Balancing

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_BinarySearch


set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# Executable binary search with a comparison budget

`upperSearch` finds the first array entry strictly above a query.  Its fuel is
logarithmic, and the proof accounts for the actual branches taken.  Array
accesses here are explicit function calls; a machine realization must still
implement those calls by bounded-address loads.
-/

namespace ThreeSum.BinarySearch

def upperSearch (f : ℕ → ℤ) (x : ℤ) : ℕ → ℕ → ℕ → ℕ
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
      if lo < hi then
        let mid := (lo + hi) / 2
        if f mid ≤ x then upperSearch f x fuel (mid + 1) hi
        else upperSearch f x fuel lo mid
      else lo
























def Partition (f : ℕ → ℤ) (x : ℤ) (n k : ℕ) : Prop :=
  k ≤ n ∧ (∀ i < k, f i ≤ x) ∧ (∀ i, k ≤ i → i < n → x < f i)







































def upperBound (f : ℕ → ℤ) (n : ℕ) (x : ℤ) : ℕ :=
  upperSearch f x (Nat.log 2 n + 1) 0 n













/-- Return the interval containing `x`, with no scan through earlier bands. -/
def locate (lo hi : ℕ → ℤ) (n : ℕ) (x : ℤ) : Option ℕ :=
  let k := upperBound lo n x
  if 0 < k then
    if x ≤ hi (k - 1) then some (k - 1) else none
  else none






































end ThreeSum.BinarySearch

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_Bands


set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# The quadratic cardinal bound for relevant sorted-band triples

The proof is an explicit injection.  A relevant A interval either contains
the lower endpoint of a B/C difference interval, or its own lower endpoint
cuts that rectangle.  For a fixed cut, interval intersections inject into
the endpoints of the two families.

This file proves the combinatorial output bound and solution coverage.
It does not assign that bound to a cubic filtering implementation.
-/

namespace ThreeSum.Bands

variable {I J K : Type*}


















def Overlap (alo ahi : I → ℤ) (blo bhi : J → ℤ) (p : I × J) : Prop :=
  alo p.1 ≤ bhi p.2 ∧ blo p.2 ≤ ahi p.1

instance (alo ahi : I → ℤ) (blo bhi : J → ℤ) (p : I × J) :
    Decidable (Overlap alo ahi blo bhi p) :=
  inferInstanceAs (Decidable (alo p.1 ≤ bhi p.2 ∧ blo p.2 ≤ ahi p.1))

def overlapOwner (alo : I → ℤ) (blo : J → ℤ) (p : I × J) : I ⊕ J :=
  if alo p.1 ≤ blo p.2 then Sum.inr p.2 else Sum.inl p.1









































def Relevant (alo ahi : I → ℤ) (blo bhi : J → ℤ) (clo chi : K → ℤ)
    (p : I × (J × K)) : Prop :=
  alo p.1 ≤ chi p.2.2 - blo p.2.1 ∧ clo p.2.2 - bhi p.2.1 ≤ ahi p.1

instance (alo ahi : I → ℤ) (blo bhi : J → ℤ) (clo chi : K → ℤ)
    (p : I × (J × K)) : Decidable (Relevant alo ahi blo bhi clo chi p) :=
  inferInstanceAs (Decidable
    (alo p.1 ≤ chi p.2.2 - blo p.2.1 ∧ clo p.2.2 - bhi p.2.1 ≤ ahi p.1))

def tripleOwner (alo : I → ℤ) (blo bhi : J → ℤ) (clo : K → ℤ)
    (p : I × (J × K)) : (J × K) ⊕ (I × (J ⊕ K)) :=
  if alo p.1 < clo p.2.2 - bhi p.2.1 then Sum.inl p.2
  else Sum.inr (p.1, overlapOwner (fun j => alo p.1 + blo j) clo p.2)


































































end ThreeSum.Bands

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_Parameters


set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# Analytic and rational parameter certificate for the proposed 3SUM algorithm

This module certifies the real-variable inequalities and the resulting exponent ledger.
It does not by itself prove that an implementation has those costs: the reduction,
cover, encoding, reporting, arithmetic and machine-model lemmas are separate obligations.

All decimal-looking constants below are exact rational numbers. There are no numerical
oracles, admitted declarations, or native-code decision procedures in this certificate.
-/

noncomputable section

namespace ThreeSum.Parameters

open Set Real

set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048

/-- Binary entropy measured in bits. -/
noncomputable def entropy (t : ℝ) : ℝ := Real.binEntropy t / Real.log 2

/-- Half of the output-support exponent at `c = 256`. -/
noncomputable def E : ℝ := 128 * entropy (1 / 256)

/-- The vertex-multiplicity exponent of the trimmed cover at `c = 256`. -/
noncomputable def kappa : ℝ :=
  512 * entropy (1 / 512) - 256 * entropy (1 / 256) - 1

/-- Entropy loss when the output layer is reduced by a fraction `t`. -/
noncomputable def gamma (t : ℝ) : ℝ :=
  256 * entropy (1 / 256) - 256 * entropy ((1 - t) / 256)

/-- A rational polynomial below `gamma` on the interval used by the algorithm. -/
def phi (t : ℝ) : ℝ := 799 / 100 * t + 18 / 25 * t ^ 2 + 6 / 25 * t ^ 3

def phiDeriv (t : ℝ) : ℝ := 799 / 100 + 36 / 25 * t + 18 / 25 * t ^ 2

def epsilon : ℝ := 1 / 5
def bandShift : ℝ := -(1 / 20)
def boxSaving : ℝ := 191 / 1000
def terminalFraction : ℝ := 13 / 20
def entropyRatio : ℝ := 277 / 1000
def initialTheta : ℝ := 1 / 25
def tangentPoint : ℝ := 17 / 100
def kappaCap : ℝ := 3 / 2000
def certificateExponent : ℝ := 9809107 / 5000000
def targetExponent : ℝ := 981 / 500

theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

theorem log_two_lower : (2 / 3 : ℝ) < Real.log 2 := by
  linarith [Real.log_two_gt_d9]

theorem log_two_upper : Real.log 2 < (25 / 36 : ℝ) := by
  linarith [Real.log_two_lt_d9]

/-! ## Exact integer witnesses for the logarithmic comparisons -/
































 theorem log_256 : Real.log 256 = 8 * Real.log 2 := by
  have h := Real.log_pow (2 : ℝ) 8
  norm_num at h
  exact h






theorem E_formula : E = 4 + 255 * Real.log (256 / 255) / (2 * Real.log 2) := by
  norm_num [E, entropy, Real.binEntropy]
  rw [log_256]
  field_simp
  ring

theorem E_bounds : (4 : ℝ) < E ∧ E < 19 / 4 := by
  have hpos : 0 < Real.log (256 / 255 : ℝ) := Real.log_pos (by norm_num)
  have hlt : Real.log (256 / 255 : ℝ) < 1 / 255 := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 256 / 255)
      (by norm_num : (256 / 255 : ℝ) ≠ 1)
    norm_num at h
    exact h
  rw [E_formula]
  constructor
  · have : 0 < 255 * Real.log (256 / 255 : ℝ) / (2 * Real.log 2) := by positivity
    linarith
  · have : 255 * Real.log (256 / 255 : ℝ) / (2 * Real.log 2) < 3 / 4 := by
      apply (div_lt_iff₀ (by positivity : 0 < 2 * Real.log 2)).2
      linarith [log_two_lower]
    linarith














































/-- Coefficients of the tangent to binary entropy at `17/100`. -/
noncomputable def tangentA : ℝ := (Real.log 100 - Real.log 83) / Real.log 2
noncomputable def tangentB : ℝ := (Real.log 83 - Real.log 17) / Real.log 2















































/-! ## Exact rational inequalities for the schedule -/

























































































































noncomputable def gammaNumerator (t : ℝ) : ℝ :=
  (1 - t) * Real.log (1 - t) + (255 + t) * Real.log (255 + t) - 255 * Real.log 255































































































/-- The rational threshold tested by the integer cubic switch. -/
def switchThreshold (a : ℝ) : ℝ := (boxSaving - 2 * bandShift + a) / (1 - a)





















































/-! ## The real-valued ledger, before the algorithmic cost lemmas are applied -/

/-- The twelve charges in the proposed implementation, including reading the input. -/
def costLedger (e k h : ℝ) : List ℝ :=
  [2 * epsilon * e,
   1 + epsilon * (e - bandShift),
   2 - epsilon * boxSaving,
   2 - epsilon * (1 / 2 + bandShift - h),
   2 - epsilon * (1 / 2 - bandShift - k - entropyRatio * (1 + boxSaving - 2 * bandShift)),
   2 - epsilon * (terminalFraction - 1 / 2 - bandShift - k),
   epsilon * (8 / 5) * (e + 1 / 2),
   2 + epsilon * (4 / 5 - (2 / 5) * e - 2 * bandShift),
   1 + epsilon * (1 / 2 - bandShift),
   2 - epsilon * (e + bandShift),
   2 - 2 * epsilon * (e + bandShift),
   1]














































end ThreeSum.Parameters

end
end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_LayerCounts


set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# Exact counts for the local subset graph

These are counts of the executable finite sets used by the graph, rather
than abstract numerical cardinality hypotheses.  An edge is an ordered
pair of disjoint `h`-subsets of `Fin L`.
-/

namespace ThreeSum.LayerCounts

open Finset

def vertices (L h : ℕ) : Finset (Finset (Fin L)) :=
  Finset.univ.powersetCard h

def edgeSet (L h : ℕ) : Finset (Finset (Fin L) × Finset (Fin L)) :=
  (vertices L h ×ˢ vertices L h).filter (fun p => Disjoint p.1 p.2)

@[simp] theorem mem_vertices {L h : ℕ} {S : Finset (Fin L)} :
    S ∈ vertices L h ↔ S.card = h := by
  simp [vertices]




@[simp] theorem mem_edgeSet {L h : ℕ} {p : Finset (Fin L) × Finset (Fin L)} :
    p ∈ edgeSet L h ↔ p.1.card = h ∧ p.2.card = h ∧ Disjoint p.1 p.2 := by
  simp [edgeSet, and_assoc]






























































































end ThreeSum.LayerCounts

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_HashFamily


set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# The actual one-hot hash family

This file develops the dependence classification of the binary one-hot hash
vectors used in the local cover. Hash weights are independent field elements
at coordinate/symbol pairs. The independence statements concern this concrete
family, not an assumed random oracle.
-/

namespace ThreeSum.HashFamily

open scoped BigOperators

variable {α K : Type*}

def oneHot [Zero K] [One K] (s : α → Bool) : α × Bool → K :=
  fun p => if s p.1 = p.2 then 1 else 0








section Relations

variable [Ring K]



























































end Relations

section LinearIndependence

variable [Field K]

































end LinearIndependence

section UniformFibers

variable {σ ι : Type*} [Fintype σ] [Fintype ι] [Field K]

/-- The linear map associated with any concrete list of hash coefficient
vectors. This is the ordinary row-by-weight product. -/
noncomputable def hashMap (v : ι → σ → K) : (σ → K) →ₗ[K] (ι → K) := by
  classical
  exact LinearMap.pi (fun i => dotProductEquiv K σ (v i))

























































end UniformFibers

section ActualHashes

variable {ι : Type*} [Fintype α] [Field K]

/-- One independent weight for each coordinate/symbol pair. -/
def hashValue (w : α × Bool → K) (s : α → Bool) : K :=
  ∑ i, w (i, s i)












end ActualHashes

section WordEvents

variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]





/-- The simultaneous prescribed hashes of a concrete word tuple. -/
def wordEvent {r : ℕ} (words : Fin r → α → Bool) (target : Fin r → K) :
    Finset (α × Bool → K) :=
  Finset.univ.filter (fun w => ∀ i, hashValue w (words i) = target i)





























def pairEvent (s t : α → Bool) (a b : K) : Finset (α × Bool → K) :=
  Finset.univ.filter (fun w => hashValue w s = a ∧ hashValue w t = b)




































































































end WordEvents

section IncidenceCounting

variable {Ω E : Type*} [Fintype Ω] [Fintype E] [DecidableEq Ω]

/-- Number of represented edges in one weight assignment. -/
def incidenceCount (events : E → Finset Ω) (w : Ω) : ℕ :=
  (Finset.univ.filter (fun e => w ∈ events e)).card





















































end IncidenceCounting

section GraphMoments

variable {E : Type*} [Fintype E] [DecidableEq E]
variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]

def outputMask (left right : E → α → Bool) (e : E) : α → Bool :=
  fun i => left e i == right e i

def badPartners (left right : E → α → Bool) (e : E) : Finset E :=
  Finset.univ.filter (fun f => left e = left f ∨ right e = right f ∨
    outputMask left right e = outputMask left right f)















































































































































end GraphMoments

section SeparableTrimming

variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]

def bucketSize (vertices : Finset (α → Bool)) (w : α × Bool → K) (target : K) : ℕ :=
  (vertices.filter (fun s => hashValue w s = target)).card

def loadedPairMass (s t : α → Bool) (a b : K) (vertices : Finset (α → Bool)) : ℕ :=
  ∑ w ∈ pairEvent s t a b, bucketSize vertices w a

























































def heavyPairEvent (s t : α → Bool) (a b : K)
    (vertices : Finset (α → Bool)) (B : ℕ) : Finset (α × Bool → K) :=
  (pairEvent s t a b).filter (fun w => B < bucketSize vertices w a)







































def trimmedPairEvent (s t : α → Bool) (a b : K)
    (leftVertices rightVertices : Finset (α → Bool)) (B : ℕ) :
    Finset (α × Bool → K) :=
  (pairEvent s t a b).filter (fun w =>
    bucketSize leftVertices w a ≤ B ∧ bucketSize rightVertices w b ≤ B)







































end SeparableTrimming

section TrimmedGraphMoments

variable {E : Type*} [Fintype E] [DecidableEq E]
variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]
































end TrimmedGraphMoments

end ThreeSum.HashFamily

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_OneHotMask


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# Evaluating a one-hot hash from a subset mask

The executable recursion examines exactly one bit per level using a cached
power of two.  Its result is the sum of the selected symbol coefficients,
and is connected here to the raw hashes used by the global encoding.
-/

namespace ThreeSum.OneHotMask

open Finset SubsetAddress LocalHashMoments
open scoped BigOperators

set_option linter.deprecated false
set_option linter.unusedSimpArgs false

def eval (w0 w1 : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | L+1, m =>
    if m < 2^L then eval w0 w1 L m + w0 L
    else eval w0 w1 L (m-2^L) + w1 L
















































def extend {L : ℕ} (f : Fin L → ℕ) (i : ℕ) : ℕ :=
  if hi : i < L then f ⟨i,hi⟩ else 0












































end ThreeSum.OneHotMask

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_Greedy


set_option autoImplicit false
set_option relaxedAutoImplicit false


/-! # An executable finite greedy cover and its logarithmic length bound -/

namespace ThreeSum.Cover

open Finset
open scoped BigOperators

variable {Ω U : Type*} [Inhabited Ω] [DecidableEq U]

/-- Exhaustive finite search, breaking ties by the order of the input list. -/
def selectMap (maps : List Ω) (covers : Ω → U → Prop) [DecidableRel covers]
    (targets : Finset U) : Ω :=
  (maps.argmax fun ω => (targets.filter (covers ω)).card).getD default
























def greedyState (maps : List Ω) (covers : Ω → U → Prop) [DecidableRel covers]
    (targets : Finset U) : ℕ → Finset U
  | 0 => targets
  | t + 1 =>
    let old := greedyState maps covers targets t
    old.filter fun u => ¬ covers (selectMap maps covers old) u

def greedyChoices (maps : List Ω) (covers : Ω → U → Prop) [DecidableRel covers]
    (targets : Finset U) : ℕ → List Ω
  | 0 => []
  | t + 1 => greedyChoices maps covers targets t ++
      [selectMap maps covers (greedyState maps covers targets t)]

theorem greedyChoices_length (maps : List Ω) (covers : Ω → U → Prop)
    [DecidableRel covers] (targets : Finset U) (t : ℕ) :
    (greedyChoices maps covers targets t).length = t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [greedyChoices, ih]








































































































end ThreeSum.Cover

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_BlockRows


set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# Flattening a block family of subsets

The coordinates retain the block index explicitly. Joining and slicing are
mutually inverse, preserve Boolean set operations, and give exact cardinalities
for balanced full inputs and forced prefixes.
-/

namespace ThreeSum.BlockRows

open Finset
open scoped BigOperators

abbrev Coord (J L : ℕ) := Σ _i : Fin J, Fin L

def join {J L : ℕ} (I : Finset (Fin J)) (u : Fin J → Finset (Fin L)) :
    Finset (Coord J L) := I.sigma u

def flat {J L : ℕ} (u : Fin J → Finset (Fin L)) : Finset (Coord J L) := join univ u

def row {J L : ℕ} (S : Finset (Coord J L)) (i : Fin J) : Finset (Fin L) :=
  Finset.univ.filter fun x => Sigma.mk i x ∈ S









@[simp] theorem mem_row {J L : ℕ} {S : Finset (Coord J L)} {i : Fin J} {x : Fin L} :
    x ∈ row S i ↔ Sigma.mk i x ∈ S := by
  simp only [row, Finset.mem_filter, Finset.mem_univ, true_and]







































































def prefixIndices (J k : ℕ) : Finset (Fin J) := univ.filter fun i => i.val < k






















end ThreeSum.BlockRows

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_Radix


set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# Exact radix composition of finite local covers

The recursion enumerates only representations of one supplied target pair.
The coverage and multiplicity proofs quantify over arbitrary integer targets;
no enumeration of the square of the global modulus is used in the definition.
-/

namespace ThreeSum.Radix

open Finset
open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

def localFiber (p : ℤ) (left right : Ω → ℤ) (a b : ℤ) : Finset Ω :=
  univ.filter fun ω => p ∣ a - left ω ∧ p ∣ b - right ω

/-- The value of a positional hash, starting with its low digit. -/
def positionalHash (p : ℤ) (raw : Ω → ℤ) : List Ω → ℤ
  | [] => 0
  | ω :: rest => raw ω + p * positionalHash p raw rest

/-- Exact candidate recursion.  Each local choice determines the next pair
of quotient targets, so carries do not create an independent branching factor. -/
def representations (p : ℤ) (left right : Ω → ℤ) : ℕ → ℤ → ℤ → Finset (List Ω)
  | 0, _, _ => {[]}
  | j + 1, a, b =>
    (localFiber p left right a b).biUnion fun ω =>
      (representations p left right j ((a - left ω) / p) ((b - right ω) / p)).image
        (List.cons ω)





























































































end ThreeSum.Radix

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_Subset


set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# Exact subset identities used by the proposed 3SUM algorithm

This module proves the algebraic identities, rather than taking the claimed
algorithm or its running time as an assumption.  `zeta` is the ordinary finite
subset sum; `mobius` is its signed inverse.  The fixed-cardinality specialization
is the identity used by the repeated histogram construction.
-/

namespace ThreeSum.Subset

open scoped BigOperators

variable {α : Type*} [DecidableEq α]

/-- Ordinary zeta transform on the finite-subset lattice. -/
def zeta (f : Finset α → ℤ) (q : Finset α) : ℤ :=
  ∑ s ∈ q.powerset, f s

/-- Signed Möbius transform on the finite-subset lattice. -/
def mobius (f : Finset α → ℤ) (q : Finset α) : ℤ :=
  ∑ s ∈ q.powerset, (-1 : ℤ) ^ (q.card - s.card) * f s






























































/-- Union convolution, before the fixed-cardinality disjointness reduction. -/
def unionConvolution (f g : Finset α → ℤ) (q : Finset α) : ℤ :=
  ∑ s ∈ q.powerset, ∑ v ∈ q.powerset,
    if s ∪ v = q then f s * g v else 0























































































/-- The single-sum disjoint subset convolution used by the algorithm. -/
def disjointConvolution (f g : Finset α → ℤ) (q : Finset α) : ℤ :=
  ∑ s ∈ q.powerset, f s * g (q \ s)



























































































/-! ## Stored partial zeta stages -/

/-- Value after exactly the coordinates in `processed` have been zeta-transformed.
All other coordinates of `u` are still forced to be present. -/
def partialZeta (processed : Finset α) (f : Finset α → ℤ) (u : Finset α) : ℤ :=
  ∑ x ∈ (u ∩ processed).powerset, f ((u \ processed) ∪ x)

/-- One ordinary zeta addition, with the old stage read at both inputs. -/
def zetaStep (a : α) (F : Finset α → ℤ) (u : Finset α) : ℤ :=
  if a ∈ u then F u + F (u.erase a) else F u


















































































































/-- The original histogram with a fixed pre and a suffix-domain guard. -/
def forcedInput (f : Finset α → ℤ) (pre suffix x : Finset α) : ℤ :=
  if x ⊆ suffix then f (pre ∪ x) else 0

































































/-! ## Prefix reporting mass -/

/-- Weighted mass of one refinement fiber. -/
def fiberMass {β γ : Type*} [DecidableEq γ]
    (domain : Finset β) (label : β → γ) (weight : β → ℕ) (value : γ) : ℕ :=
  ∑ p ∈ domain with label p = value, weight p























































end ThreeSum.Subset

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_SubsetAddress


set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# Compact addresses for bounded-cardinality bit masks

Both ranking and enumeration recurse on the highest available bit. The
enumerator stops immediately when the requested layer is empty. In
particular, it does not enumerate the ambient Boolean cube and filter it.
-/

namespace ThreeSum.SubsetAddress

set_option maxRecDepth 4000

open Finset
open scoped BigOperators

/-- Number of selected bits among the first `L` positions, evaluated by
removing the highest available bit. Its intended domain is `m < 2^L`. -/
def weight : ℕ → ℕ → ℕ
  | 0, _ => 0
  | L + 1, m => if m < 2 ^ L then weight L m else weight L (m - 2 ^ L) + 1

def IsMask (L k m : ℕ) : Prop := m < 2 ^ L ∧ weight L m = k

instance (L k m : ℕ) : Decidable (IsMask L k m) := by
  unfold IsMask
  infer_instance

 theorem pow_two_succ (L : ℕ) : 2 ^ (L + 1) = 2 ^ L + 2 ^ L := by
  rw [pow_succ]
  omega

@[simp] theorem weight_zero (L : ℕ) : weight L 0 = 0 := by
  induction L with
  | zero => rfl
  | succ L ih => simpa [weight, Nat.two_pow_pos] using ih

theorem weight_le_width {L m : ℕ} (hm : m < 2 ^ L) : weight L m ≤ L := by
  induction L generalizing m with
  | zero => simp [weight]
  | succ L ih =>
      rw [pow_two_succ] at hm
      by_cases hc : m < 2 ^ L
      · simpa [weight, hc] using (ih hc).trans (Nat.le_succ L)
      · have hr : m - 2 ^ L < 2 ^ L := by omega
        simpa [weight, hc] using Nat.succ_le_succ (ih hr)

theorem IsMask.le_width {L k m : ℕ} (hm : IsMask L k m) : k ≤ L := by
  rw [← hm.2]
  exact weight_le_width hm.1

theorem weight_eq_zero_iff {L m : ℕ} (hm : m < 2 ^ L) :
    weight L m = 0 ↔ m = 0 := by
  induction L generalizing m with
  | zero =>
      simp only [pow_zero] at hm
      have hz : m = 0 := by omega
      simp [hz, weight]
  | succ L ih =>
      by_cases hc : m < 2 ^ L
      · simpa [weight, hc] using ih hc
      · have hp := Nat.two_pow_pos L
        have hn : m ≠ 0 := by omega
        simp [weight, hc, hn]

@[simp] theorem isMask_zero (L m : ℕ) : IsMask L 0 m ↔ m = 0 := by
  constructor
  · intro hm
    exact (weight_eq_zero_iff hm.1).mp hm.2
  · rintro rfl
    exact ⟨Nat.two_pow_pos L, weight_zero L⟩

theorem IsMask.low {L k m : ℕ} (hm : IsMask (L + 1) k m) (hc : m < 2 ^ L) :
    IsMask L k m := ⟨hc, by simpa [weight, hc] using hm.2⟩

theorem IsMask.high {L k m : ℕ} (hm : IsMask (L + 1) k m) (hc : 2 ^ L ≤ m) :
    0 < k ∧ IsMask L (k - 1) (m - 2 ^ L) := by
  have hb := hm.1
  rw [pow_two_succ] at hb
  have hw := hm.2
  simp only [weight, if_neg (Nat.not_lt.mpr hc)] at hw
  exact ⟨by omega, by constructor <;> omega⟩

theorem IsMask.succ_low {L k m : ℕ} (hm : IsMask L k m) : IsMask (L + 1) k m := by
  have hb := hm.1
  refine ⟨?_, ?_⟩
  · rw [pow_two_succ]
    omega
  · simpa [weight, hm.1] using hm.2

theorem IsMask.succ_high {L k m : ℕ} (hm : IsMask L k m) :
    IsMask (L + 1) (k + 1) (2 ^ L + m) := by
  have hb := hm.1
  refine ⟨?_, ?_⟩
  · rw [pow_two_succ]
    omega
  · have hc : ¬2 ^ L + m < 2 ^ L := by omega
    simpa [weight, hc] using hm.2

/-- Zero-based rank within a fixed-cardinality layer. The table-based
implementation below replaces each binomial coefficient by a lookup. -/
def layerRank : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | L + 1, k, m =>
      if m < 2 ^ L then layerRank L k m
      else L.choose k + layerRank L (k - 1) (m - 2 ^ L)










































/-- Construct every `k`-bit mask once, lower half before upper half. The
guard prevents recursion through empty layers. -/
def enumerateLayer : ℕ → ℕ → List ℕ
  | _, 0 => [0]
  | 0, _ + 1 => []
  | L + 1, k + 1 =>
      if k + 1 ≤ L + 1 then
        enumerateLayer L (k + 1) ++ (enumerateLayer L k).map (fun m => 2 ^ L + m)
      else []

theorem enumerateLayer_length (L k : ℕ) : (enumerateLayer L k).length = L.choose k := by
  induction L generalizing k with
  | zero => cases k <;> simp [enumerateLayer]
  | succ L ih =>
      cases k with
      | zero => simp [enumerateLayer]
      | succ k =>
          by_cases hk : k + 1 ≤ L + 1
          · simp [enumerateLayer, hk, ih, Nat.choose_succ_succ, Nat.add_comm]
          · simp [enumerateLayer, hk, Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hk)]

theorem mem_enumerateLayer (L k m : ℕ) : m ∈ enumerateLayer L k ↔ IsMask L k m := by
  induction L generalizing k m with
  | zero =>
      cases k with
      | zero => simp [enumerateLayer]
      | succ k => simp [enumerateLayer, IsMask, weight]
  | succ L ih =>
      cases k with
      | zero => simp [enumerateLayer]
      | succ k =>
          by_cases hk : k + 1 ≤ L + 1
          · simp only [enumerateLayer, if_pos hk, List.mem_append, List.mem_map, ih]
            constructor
            · rintro (hm | ⟨a, ha, rfl⟩)
              · exact hm.succ_low
              · exact ha.succ_high
            · intro hm
              by_cases hc : m < 2 ^ L
              · exact Or.inl (hm.low hc)
              · right
                refine ⟨m - 2 ^ L, ?_, by omega⟩
                simpa only [Nat.add_sub_cancel] using (hm.high (Nat.le_of_not_gt hc)).2
          · have hn : ¬IsMask (L + 1) (k + 1) m := fun hm => hk hm.le_width
            simp [enumerateLayer, hk, hn]


















/-- The work recurrence charges each recursive invocation, every emitted
upper mask, and every cell copied by the lower-list append. Bit-mask
addition and the guards are individual arithmetic operations. -/
def enumerationWork : ℕ → ℕ → ℕ
  | _, 0 => 1
  | 0, _ + 1 => 1
  | L + 1, k + 1 =>
      if k + 1 ≤ L + 1 then
        1 + enumerationWork L (k + 1) + enumerationWork L k +
          (enumerateLayer L (k + 1)).length + (enumerateLayer L k).length
      else 1



















/-- Offset of the layer of cardinality `k` within the full cardinality
ordering. -/
def layerOffset (L k : ℕ) : ℕ := ∑ r ∈ Finset.range k, L.choose r














def downsetCap (L cut : ℕ) : ℕ := layerOffset L (min cut L + 1)

def downsetRank (L m : ℕ) : ℕ :=
  layerOffset L (weight L m) + layerRank L (weight L m) m
































/-- Enumerate consecutive layers by concatenation, with no ambient-cube
enumeration. The public downset enumerator caps the cutoff at the width. -/
def enumerateThrough (L : ℕ) : ℕ → List ℕ
  | 0 => enumerateLayer L 0
  | k + 1 => enumerateThrough L k ++ enumerateLayer L (k + 1)

def enumerateDownset (L cut : ℕ) : List ℕ := enumerateThrough L (min cut L)




































































/-- Integer bit mask of a finite set of coordinate positions. -/
def maskOf (s : Finset ℕ) : ℕ := ∑ i ∈ s, 2 ^ i

theorem maskOf_injective : Function.Injective maskOf :=
  Finset.geomSum_injective (by decide)

 theorem subset_range_pred {L : ℕ} {s : Finset ℕ}
    (hs : s ⊆ Finset.range (L + 1)) (hL : L ∉ s) : s ⊆ Finset.range L := by
  intro i hi
  have hb := Finset.mem_range.mp (hs hi)
  have hn : i ≠ L := by rintro rfl; exact hL hi
  exact Finset.mem_range.mpr (by omega)

theorem maskOf_isMask {L : ℕ} {s : Finset ℕ} (hs : s ⊆ Finset.range L) :
    IsMask L s.card (maskOf s) := by
  induction L generalizing s with
  | zero =>
      have he : s = ∅ := by simpa using hs
      subst s
      simp [maskOf]
  | succ L ih =>
      by_cases hL : L ∈ s
      · have ht : s.erase L ⊆ Finset.range L :=
          subset_range_pred ((Finset.erase_subset L s).trans hs) (Finset.notMem_erase _ _)
        have hm := (ih ht).succ_high
        have hcard : (s.erase L).card + 1 = s.card := Finset.card_erase_add_one hL
        have he : 2 ^ L + maskOf (s.erase L) = maskOf s :=
          Finset.add_sum_erase s (fun i => 2 ^ i) hL
        simpa only [hcard, he] using hm
      · exact (ih (subset_range_pred hs hL)).succ_low

def natPositions {L : ℕ} (s : Finset (Fin L)) : Finset ℕ := s.map Fin.valEmbedding

theorem natPositions_subset {L : ℕ} (s : Finset (Fin L)) :
    natPositions s ⊆ Finset.range L := by
  intro i hi
  obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
  exact Finset.mem_range.mpr j.isLt

@[simp] theorem natPositions_card {L : ℕ} (s : Finset (Fin L)) :
    (natPositions s).card = s.card := Finset.card_map _

theorem natPositions_injective (L : ℕ) :
    Function.Injective (@natPositions L) := Finset.map_injective _

def subsetMask {L : ℕ} (s : Finset (Fin L)) : ℕ := maskOf (natPositions s)

theorem subsetMask_isMask {L : ℕ} (s : Finset (Fin L)) :
    IsMask L s.card (subsetMask s) := by
  simpa only [natPositions_card, subsetMask] using maskOf_isMask (natPositions_subset s)

theorem subsetMask_injective (L : ℕ) : Function.Injective (@subsetMask L) :=
  maskOf_injective.comp (natPositions_injective L)

def subsetRank {L : ℕ} (s : Finset (Fin L)) : ℕ := downsetRank L (subsetMask s)












































end ThreeSum.SubsetAddress

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_SubsetTransport


set_option autoImplicit false
set_option relaxedAutoImplicit false


/-! # Transporting compact subset transforms across an explicit equivalence -/

namespace ThreeSum.SubsetTransport

open Finset
open scoped BigOperators

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

def reindex (e : α ≃ β) (f : Finset α → ℤ) (S : Finset β) : ℤ :=
  f (S.map e.symm.toEmbedding)

















































end ThreeSum.SubsetTransport

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_MaskErase


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


/-!
# Deleting one coordinate from an integer subset mask

The routine inspects the highest remaining power of two at each recursive
step. It uses no division or scan proportional to the mask's numeric value.
-/

namespace ThreeSum.MaskErase

open Finset
open scoped BigOperators
open SubsetAddress

def eraseMask : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | L+1, a, m =>
    if m < 2^L then eraseMask L a m
    else if a = L then m-2^L
    else 2^L + eraseMask L a (m-2^L)














































































end ThreeSum.MaskErase

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_BruteTripleIndex


set_option autoImplicit false
set_option relaxedAutoImplicit false


/-! # A literal order of all original-position triples for the finite fallback -/

namespace ThreeSum.BruteTripleIndex

def first (n t : ℕ) : ℕ := t/n/n
def second (n t : ℕ) : ℕ := t/n%n
def third (n t : ℕ) : ℕ := t%n

theorem bounds {n t : ℕ} (hn : 0 < n) (ht : t < n^3) :
    first n t < n ∧ second n t < n ∧ third n t < n := by
  have ht' : t < (n*n)*n := by simpa only [pow_succ,pow_zero,one_mul] using ht
  have hq : t/n < n*n := (Nat.div_lt_iff_lt_mul hn).mpr ht'
  exact ⟨(Nat.div_lt_iff_lt_mul hn).mpr hq,Nat.mod_lt _ hn,Nat.mod_lt _ hn⟩

def code {n : ℕ} (i j k : Fin n) : ℕ := (i.val*n+j.val)*n+k.val






























def witness {n t : ℕ} (x : Fin n → ℤ) (hn : 0 < n) (ht : t < n^3) : Prop :=
  let a : Fin n := ⟨first n t,(bounds hn ht).1⟩
  let b : Fin n := ⟨second n t,(bounds hn ht).2.1⟩
  let c : Fin n := ⟨third n t,(bounds hn ht).2.2⟩
  a≠b ∧ a≠c ∧ b≠c ∧ x a+x b+x c=0

def Hit {n : ℕ} (x : Fin n → ℤ) (hn : 0 < n) (t : ℕ) : Prop :=
  ∃ i, ∃ hi : i < n^3, i < t ∧ witness x hn hi

































end ThreeSum.BruteTripleIndex

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_Coloring


set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# A finite, deterministic three-color reduction

The family below enumerates two positions of the binary representation of an
array index and all 81 maps from their four patterns to three colors.  Its
parameter count is exactly `81 * d^2`.  In particular it never enumerates all
three-colorings of the input.  The final equivalence allows repeated input
values and deduplicates each color class into a finite set.
-/

namespace ThreeSum.Coloring

variable {α : Type*}






























/-- An explicitly enumerable parameter space: two coordinates and an 81-entry
choice of a color map. -/
abbrev Parameter (d : ℕ) := (Fin d × Fin d) × ((Bool × Bool) → Fin 3)

def applyColor {d : ℕ} (p : Parameter d) (word : Fin d → Bool) : Fin 3 :=
  p.2 (word p.1.1, word p.1.2)


















































































/-- Values are deduplicated inside each class, retaining original index
witnesses through image membership. -/
def values {n : ℕ} (x : Fin n → ℤ) (c : Fin n → Fin 3) (color : Fin 3) :
    Finset ℤ :=
  (Finset.univ.filter (fun i => c i = color)).image x

def negValues {n : ℕ} (x : Fin n → ℤ) (c : Fin n → Fin 3) : Finset ℤ :=
  (values x c 2).image (fun z => -z)










def DistinctZeroSum {n : ℕ} (x : Fin n → ℤ) : Prop :=
  ∃ i j k, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ x i + x j + x k = 0

def ThreeSetWitness (a b c : Finset ℤ) : Prop :=
  ∃ u ∈ a, ∃ v ∈ b, ∃ w ∈ c, u + v = w



















































end ThreeSum.Coloring

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_CyclicFold


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.Karatsuba
end ThreeSum.Karatsuba


/-!
# Folding a dense polynomial product into a cyclic convolution

The product of two vectors of length at most `p` has only two possible
contributions to an output residue `r < p`: coefficients `r` and `r+p`.
The double sum below specifies the answer; the implementation obtains it
by one fast product and a linear pass over the output coefficients.
-/

namespace ThreeSum.CyclicFold

open Finset Polynomial Karatsuba
open scoped BigOperators





























def cyclic (p : ℕ) (as bs : List ℤ) (r : ℕ) : ℤ :=
  ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range p,
    if (i + j) % p = r then as.getD i 0 * bs.getD j 0 else 0















def vector (p : ℕ) (f : ZMod p → ℕ) : List ℤ :=
  (List.range p).map fun (i : ℕ) => (f (i : ZMod p) : ℤ)







































































def padTo (n : ℕ) (as : List ℤ) : List ℤ :=
  as ++ List.replicate (n - as.length) 0
































end ThreeSum.CyclicFold

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSumApsp_Util_List
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/



set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# Lists: entries with a default, blocks, sums, counting, sorted lists

General facts about lists. Arrays are lists here, and entry `i` of a list is `l.getD i d`. The
sections:

* Entries with a default: `getD` of a list that was appended to, cut, tabulated, mapped or changed
  in one place.
* Blocks: `(List.range n).flatMap f` puts the blocks `f 0, …, f (n - 1)` one after the other. Where
  an entry of a block stands, for blocks of any lengths and for blocks of one length.
* Sums: partial sums, the triangle inequality, and the sum over a list that enumerates the image of
  a finite set.
* A running minimum.
* Counting: how often a value occurs among the first entries of a list, or among the values of a
  function on `Fin n`; the list of the `j < n` with a property.
* Sorted lists: what `dropWhile` and `takeWhile` leave of a strictly increasing list; first
  occurrences in a weakly increasing list.
* Two notions of this project: `AbsLe l U` says that all members of `l` have absolute value at most
  `U`, and `sumLists` is the entrywise sum of lists of one length.
-/

@[expose] public section

namespace List

variable {α β : Type*}

/-! ## Entries with a default -/





























/-- Entry `i < l.length` of `l.map f`, whatever the two defaults. Mathlib's `List.getD_map` is for
all `i`, with the default `f d`. -/
theorem getD_map_of_lt (f : α → β) {l : List α} {i : ℕ} (hi : i < l.length) (d : α) (d' : β) :
    (l.map f).getD i d' = f (l.getD i d) := by
  rw [List.getD_eq_getElem _ _ (by rwa [List.length_map]), List.getD_eq_getElem _ _ hi,
    List.getElem_map]




























/-! ## Blocks one after the other -/











































































/-! ## Sums -/









































section

variable {R : Type*} [AddCommGroup R] [LinearOrder R] [IsOrderedAddMonoid R]














end



































/-! ## A running minimum -/
























/-! ## Counting -/












































































/-! ## Sorted lists -/

section Sorted

variable [LinearOrder α]








































end Sorted

end List

namespace ThreeSumApsp

variable {α β : Type*}

/-! ## Lists of integers that are bounded in absolute value -/



















/-! ## The entrywise sum of lists -/






















end ThreeSumApsp

end
end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_Histograms


set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# Exact histogram and correlation counts

All weights are natural multiplicities.  In particular, raw A incidences and
repeated selected-map occurrences need not be deduplicated to use these
identities. The common offset is chosen from the actual key histograms.
-/

namespace ThreeSum.Histograms

open Finset
open scoped BigOperators

variable {ι τ ν G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

def histogram (I : Finset ι) (key : ι → G) (weight : ι → ℕ) (k : G) : ℕ :=
  ∑ i ∈ I, if key i = k then weight i else 0









def pairMass (I : Finset ι) (J : Finset τ) (left : ι → G) (right : τ → G)
    (weightL : ι → ℕ) (weightR : τ → ℕ) (d : G) : ℕ :=
  ∑ i ∈ I, ∑ j ∈ J, if right j - left i = d then weightL i * weightR j else 0

















































def tripleMass (A : Finset ι) (B : Finset τ) (C : Finset ν)
    (a : ι → G) (b : τ → G) (c : ν → G)
    (wa : ι → ℕ) (wb : τ → ℕ) (wc : ν → ℕ) : ℕ :=
  ∑ i ∈ A, ∑ j ∈ B, ∑ k ∈ C,
    if a i + b j = c k then wa i * wb j * wc k else 0

























end ThreeSum.Histograms

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_Karatsuba


set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# Dense integer Karatsuba multiplication

This file implements a dense, low-coefficient-first list algorithm. Its
correctness theorem is an equality of integer polynomials. The instrumented
work model counts list traversal and scalar arithmetic primitives; it is a
separate obligation to compile this implementation to `Light` and prove the
benchmark's word-RAM step and word-size bounds.
-/

namespace ThreeSum.Karatsuba

open Polynomial

/-- Low-degree-first coefficient semantics, retaining padding zeros. -/
noncomputable def asPolynomial : List ℤ → Polynomial ℤ
  | [] => 0
  | a :: as => C a + X * asPolynomial as

/-- Linear dense addition; unequal inputs are implicitly padded by zeros. -/
def plus : List ℤ → List ℤ → List ℤ
  | [], bs => bs
  | as, [] => as
  | a :: as, b :: bs => (a + b) :: plus as bs






















































































































































/-! ## Explicit traversal/arithmetic work model

The following charges reflect the operations in the executable list code:
two units per matched coefficient of `plus`; two per mapped coefficient of
`negate`; two per generated/concatenated zero of `shift`; and the two scans
used by `take` and `drop`. The fixed per-call charges include list tests.
They are a conventional unit-cost list/arithmetic model, **not** a theorem
about the benchmark machine or Lean's runtime system.

The recursive charge below uses the actual intermediate list sizes. The
uniform three-subcall recurrence is proved from those sizes; it is not an
assumption that the desired multiplication bound already holds.
-/




















































































end ThreeSum.Karatsuba

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_KaratsubaBounds


set_option autoImplicit false
set_option relaxedAutoImplicit false


/-! # Coefficient and intermediate-value bounds for the array realization -/

namespace ThreeSum.Karatsuba

open Polynomial
open scoped BigOperators






















def CoeffBound (as : List ℤ) (U : ℤ) : Prop := ∀ j, |as.getD j 0| ≤ U




















































































end ThreeSum.Karatsuba

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_SparseBoxes


set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# Finite sparse-query boxes

The largest-missing-element partition and the reusable box recurrence are proved
here as exact finite identities.  The accompanying cardinalities concern the
actual canonical box family, not the family of all arbitrary free-coordinate
subsets.
-/

namespace ThreeSum.SparseBoxes

open scoped BigOperators

variable {α : Type*} [LinearOrder α]

/-- A deterministic selection of the `t` largest elements, by successive maxima. -/
def largest : ℕ → Finset α → Finset α
  | 0, _ => ∅
  | t + 1, m =>
      if hm : m.Nonempty then
        insert (m.max' hm) (largest t (m.erase (m.max' hm)))
      else ∅

/-- A selected set consists of exactly the `t` largest elements of `m`. -/
def IsLargest (t : ℕ) (m u : Finset α) : Prop :=
  u ⊆ m ∧ u.card = t ∧ ∀ a ∈ u, ∀ b ∈ m, b ∉ u → b < a
















































/-- A box contains exactly the subsets between its required and allowed sets. -/
def BoxMember (flags free leaf : Finset α) : Prop :=
  leaf ⊆ flags ∧ flags \ free ⊆ leaf

/-- For a query set and a proposed largest-missing set, free positions lie below
every chosen missing position. -/
def queryFree (q u : Finset α) : Finset α :=
  (q \ u).filter (fun x => ∀ y ∈ u, x < y)

def QueryBox (q u leaf : Finset α) : Prop :=
  BoxMember (q \ u) (queryFree q u) leaf

















































































/-! ## Canonical free prefixes and the finite preprocessing family -/








































































































































































/-! ## The exact addition recurrence and query sum -/

instance (flags free leaf : Finset α) : Decidable (BoxMember flags free leaf) := by
  unfold BoxMember
  infer_instance

instance (q u leaf : Finset α) : Decidable (QueryBox q u leaf) := by
  unfold QueryBox
  infer_instance

/-- The signed sum stored in one box record. -/
def boxSum (flags free : Finset α) (weight : Finset α → ℤ) : ℤ :=
  ∑ leaf ∈ flags.powerset, if flags \ free ⊆ leaf then weight leaf else 0
























































































































































































/-! ## Number of query accesses -/

def explicitLeaves (q : Finset α) (t : ℕ) : Finset (Finset α) :=
  ((Finset.range t).biUnion (fun j => q.powersetCard j)).image (fun missing => q \ missing)





























































end ThreeSum.SparseBoxes

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_SourceFlagProduct


set_option autoImplicit false
set_option relaxedAutoImplicit false


/-! # Conjunction represented by the product of independently computed flags -/

namespace ThreeSum.SourceFlagProduct

open Finset
open scoped BigOperators

def product (flag : ℕ → ℕ) (n : ℕ) : ℕ := ∏ i ∈ range n, flag i








































end ThreeSum.SourceFlagProduct

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_WeightedModuli


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.Arithmetic
end ThreeSum.Arithmetic


/-!
# Weighted counting with possibly shared prime factors

For prime `p`, simultaneous divisibility by `q` and `p` is tested at `q`
when `p ∣ q`, and at `q*p` otherwise. This executable branch permits one
finite prime pool to supply both contraction and auxiliary tests.
-/

namespace ThreeSum.WeightedModuli

open Finset Arithmetic
open scoped BigOperators

def joint (q p : ℕ) : ℕ := if p ∣ q then q else q * p












































































end ThreeSum.WeightedModuli

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_PrimeChain


set_option autoImplicit false
set_option relaxedAutoImplicit false


/-! # Exact deterministic contraction of the weighted modular score -/

namespace ThreeSum.PrimeChain

open Finset
open scoped BigOperators

variable {ι : Type*}

def score (T : Finset ι) (difference : ι → ℤ) (weight : ℤ → ℕ) (q : ℕ) : ℕ :=
  ∑ i ∈ T, if q ∣ (difference i).natAbs then weight (difference i) else 0



































































































































































end ThreeSum.PrimeChain

end

section
-- Source fragment: Definitions.Def_ThreeSum1962Source_ThreeSum_BlockSourceEncoding


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSum.BlockEncoding
end ThreeSum.BlockEncoding
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightSourceResidues
end ThreeSum.LightSourceResidues
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds


/-!
# Original-input histograms give the exact independently trimmed sources

The histogram keys retain the first modular reduction and the signed carry
offset. Looking up the endpoint's final residue therefore counts precisely
the original divisibility condition in `BlockEncoding`. An explicit finite
enumeration accounts for every original input incidence once.
-/

namespace ThreeSum.BlockSourceEncoding

open Finset BlockEncoding GlobalEncoding LocalCoverBounds LightSourceResidues
open scoped BigOperators

set_option maxHeartbeats 1000000

































def modulus (h J : ℕ) : ℕ := localPrime h ^ J






section OriginalSources

variable {β : Type*} [DecidableEq β]



























end OriginalSources

end ThreeSum.BlockSourceEncoding

end


