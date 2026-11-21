-- Prove2me | Definitions.Def_VWZClique_NativeProjectionContract
-- name    : VWZClique_NativeProjectionContract
-- status  : Definition
-- author  : @orz
-- created : 2026-11-20T13:36:58.573848+00:00
-- url     : https://prove2.me/theorems/26311ba5-9dc2-47a7-9958-1689bc9015a7
-- title:
--   Native projection kernel for weighted nine-part clique counting
-- statement:
--   For a weighted pattern on nine vertices, the projection kernel is a finite word-RAM program that initializes a recursive frame. Its inputs are binary unary and pair weights on a common domain of size $2^L$, together with the pattern, the vertex permutation, and the current recursion depth. Its output is the integer projected trace for the left branch and the data required to enumerate later recursive calls. The contract specifies the words preserved for the caller, an instruction bound in terms of the square-multiplication cost, and a polynomial bound on the largest address. A single program and the constants in both bounds serve all domain sizes.
-- source:
--   V. Vassilevska Williams and O. Zamir, The k-Clique hypothesis is dead, for good, Theorem 1.1 and Appendix A, pp. 21–22. This module defines the word-RAM interface for the projected contraction and its recursive caller. https://zamir.prof/kclq.pdf

import Definitions.Def_OAI_MatrixMultiplication_Arithmetic_omega
import Definitions.Def_VWZClique_Contraction
import Definitions.Def_VWZClique_Count
import Definitions.Def_VWZClique_FoldedSum
import Definitions.Def_VWZClique_Operators
import Definitions.Def_VWZClique_Weighted
import Mathlib
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Fintype.EquivFin
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Ring


/- CliqueVM -/
section

/-! Simulation of bounded integer arithmetic, indirect addressing and branches on
    the fixed-width instruction interpreter used for clique counting. -/

namespace VWZClique.IntegerRAM
open TrulySubcubicAPSP

abbrev Memory := ℤ → ℤ

/-- Exact signed-word representability at positive width. -/
def Fits (W : ℕ) (x : ℤ) : Prop := -(2 : ℤ)^(W-1) ≤ x ∧ x < (2 : ℤ)^(W-1)


def update (m : Memory) (i x : ℤ) : Memory := fun a => if a = i then x else m a










end VWZClique.IntegerRAM

end

/- LoopCompiler -/
section

open TrulySubcubicAPSP
namespace VWZClique.IntegerRAM.Structured

inductive Atom where
  | one (dst : ℤ)
  | add (dst a b : ℤ)
  | sub (dst a b : ℤ)
  | mul (dst a b : ℤ)
  | load (dst ptr : ℤ)
  | store (ptr src : ℤ)


inductive Step (W : ℕ) : Atom → Memory → Memory → Prop where
  | one (m d) : Step W (.one d) m (update m d 1)
  | add (m d a b) : Step W (.add d a b) m (update m d (m a + m b))
  | sub (m d a b) : Step W (.sub d a b) m (update m d (m a - m b))
  | mul (m d a b) : Step W (.mul d a b) m (update m d (m a * m b))
  | load (m d p) (fit : Fits W (m p)) : Step W (.load d p) m (update m d (m (m p)))
  | store (m p s) (fit : Fits W (m p)) : Step W (.store p s) m (update m (m p) (m s))

inductive Command where
  | skip
  | atom (a : Atom)
  | seq (c d : Command)
  | whenNonnegative (reg : ℤ) (body : Command)
  | repeatWhileNegative (body : Command) (reg : ℤ)




/-- Structured integer computation. The index counts primitive machine instructions,
including each guard or loop test. -/
inductive Runs (W : ℕ) : Command → Memory → ℕ → Memory → Prop where
  | skip (m) : Runs W .skip m 0 m
  | atom {a m m'} (s : Step W a m m') : Runs W (.atom a) m 1 m'
  | seq {c d m x out s t} (h : Runs W c m s x) (k : Runs W d x t out) :
      Runs W (.seq c d) m (s+t) out
  | guard_skip {reg c m} (hf : Fits W (m reg)) (hn : m reg < 0) :
      Runs W (.whenNonnegative reg c) m 1 m
  | guard_take {reg c m out t} (hf : Fits W (m reg)) (hn : ¬ m reg < 0)
      (run : Runs W c m t out) : Runs W (.whenNonnegative reg c) m (1+t) out
  | loop_done {reg c m out t} (run : Runs W c m t out) (hf : Fits W (out reg))
      (hn : ¬ out reg < 0) : Runs W (.repeatWhileNegative c reg) m (t+1) out
  | loop_again {reg c m x out s t} (body : Runs W c m s x) (hf : Fits W (x reg))
      (hn : x reg < 0) (more : Runs W (.repeatWhileNegative c reg) x t out) :
      Runs W (.repeatWhileNegative c reg) m (s+1+t) out











end VWZClique.IntegerRAM.Structured

end

/- NativeMaskScan -/
section

/-! Uniform stable compaction for mask and projected-label records. -/
namespace VWZClique.IntegerRAM.MaskScan
open Structured 



def rank (keep : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | x+1 => rank keep x + (if keep x then 1 else 0)


theorem rank_le (keep : ℕ → Bool) (i : ℕ) : rank keep i ≤ i := by
  induction i with
  | zero => exact Nat.le_refl _
  | succ i ih => simp only [rank]; split <;> omega






end VWZClique.IntegerRAM.MaskScan

end

/- WordGraphDivide -/
section

/-! Repeated subtraction for radix decoding. It uses one graph-order cell and
four negative cells, with a time linear in the quotient. A blocked input table
can afford linear work per packed key. -/

namespace VWZClique.IntegerRAM.Graph
open Structured 

namespace Division










/-- Largest permitted magnitude of a comparison in a division by n. -/
def Room (W M : ℕ) : Prop := (M:ℤ) < (2:ℤ)^(W-1)





end Division
end VWZClique.IntegerRAM.Graph

end

/- NativeMaskScanClass -/
section

namespace VWZClique.IntegerRAM.MaskScan
open Structured Graph

/-- Digits at least the threshold contribute one unit, or one minus sign. -/
def localN (h x : ℕ) : ℕ := if h≤x then 1 else 0

def totalN (b h z : ℕ) : ℕ → ℕ
  | 0 => 0
  | j+1 => totalN b h z j + localN h (z/b^j%b)








end VWZClique.IntegerRAM.MaskScan

end

/- NativeMaskScanTable -/
section

namespace VWZClique.IntegerRAM.MaskScan
open Structured Graph 



def selected (left right : ℤ) (a : ℕ) : Bool := decide ((a:ℤ)≤left ∨ right≤(a:ℤ))








end VWZClique.IntegerRAM.MaskScan

end

/- RankSwapIdentities -/
section

open VWZClique
namespace VWZClique.RankSwap

/-- The three one-coordinate operators used in the interpolation argument. -/
inductive Factor where
  | identity | swap | difference
  deriving DecidableEq

def factorEntry (o : Factor) (s u v t : Bool) : ℚ :=
  let id : ℚ := if s = v ∧ u = t then 1 else 0
  let swap : ℚ := if s = t ∧ u = v then 1 else 0
  match o with
  | .identity => id
  | .swap => swap
  | .difference => id - swap

def inverseNormSq (j : Fin 4) : ℚ := if j < 2 then 1 else 1/2

def eigenvalue (o : Factor) (j : Fin 4) : ℚ :=
  match o with
  | .identity => 1
  | .swap => if j = 3 then -1 else 1
  | .difference => if j = 3 then 2 else 0

theorem oneBit_resolution : ∀ (o : Factor) (s u v t : Bool),
    factorEntry o s u v t = ∑ j : Fin 4,
      (eigenvalue o j * inverseNormSq j) * oneBit j s u * oneBit j v t := by
  intro o
  cases o <;> decide +kernel

/-- An arbitrary tensor word in I, P, and I-P, expanded in exactly the
unnormalized product basis of the submitted rank-or-swap statement. -/
theorem tensor_resolution {L : ℕ} (o : Fin L → Factor) (x y : PairBits L) :
    (∏ i, factorEntry (o i) (x.1 i) (x.2 i) (y.1 i) (y.2 i)) =
    ∑ j : BasisLabel L, (∏ i, eigenvalue (o i) (j i) * inverseNormSq (j i)) *
      basisEntry j x * basisEntry j y := by
  simp_rw [oneBit_resolution]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp [basisEntry, Finset.prod_mul_distrib]

theorem identity_resolution {L : ℕ} (x y : PairBits L) :
    (if x = y then (1 : ℚ) else 0) = ∑ j : BasisLabel L,
      (∏ i, inverseNormSq (j i)) * basisEntry j x * basisEntry j y := by
  classical
  have h := tensor_resolution (fun _ : Fin L => .identity) x y
  simp only [eigenvalue, one_mul] at h
  rw [← h]
  by_cases hxy : x = y
  · subst y
    simp [factorEntry]
  · rw [if_neg hxy]
    symm
    apply Finset.prod_eq_zero_iff.mpr
    obtain ⟨i,hi⟩ : ∃ i, ¬ (x.1 i = y.1 i ∧ x.2 i = y.2 i) := by
      by_contra! hh
      exact hxy (Prod.ext (funext fun i => (hh i).1) (funext fun i => (hh i).2))
    exact ⟨i, Finset.mem_univ _, by simp [factorEntry, hi]⟩

/-- The four signed matrix units of I-P, in row/column bit order. -/
def unitBits (i : ℕ) : Bool × Bool × Bool × Bool :=
  if i = 0 then (false,true,false,true)
  else if i = 1 then (true,false,true,false)
  else if i = 2 then (false,true,true,false)
  else (true,false,false,true)

def localMatch (b : Option (Bool × Bool × Bool × Bool)) (s u v t : Bool) : Prop :=
  match b with
  | none => s = t ∧ u = v
  | some a => (s,u,v,t) = a

instance (b : Option (Bool × Bool × Bool × Bool)) (s u v t : Bool) :
    Decidable (localMatch b s u v t) := by cases b <;> unfold localMatch <;> infer_instance

def maskBit (active : Bool) (i : ℕ) := if active then some (unitBits i) else none
def signBit (active : Bool) (i : ℕ) : ℤ := if active && decide (2 ≤ i) then -1 else 1
abbrev choices (active : Bool) : ℕ := if active then 4 else 1

theorem local_units (active s u v t : Bool) :
    factorEntry (if active then .difference else .swap) s u v t =
    ∑ k : Fin (choices active), (signBit active k.val : ℚ) *
      (if localMatch (maskBit active k.val) s u v t then 1 else 0) := by
  cases active
  · cases s <;> cases u <;> cases v <;> cases t <;>
      norm_num [factorEntry, signBit, maskBit, localMatch]
  · have four (f : Fin (choices true) → ℚ) :
        ∑ k, f k = f 0 + f 1 + f 2 + f 3 := Fin.sum_univ_four f
    rw [four]
    cases s <;> cases u <;> cases v <;> cases t <;>
      norm_num [factorEntry, signBit, maskBit, unitBits, localMatch, choices]

theorem mask_product {L : ℕ} (m : Mask L) (x y : PairBits L) :
    (∏ i, (if localMatch (m i) (x.1 i) (x.2 i) (y.1 i) (y.2 i) then (1 : ℚ) else 0))
      = swapEntry m x y := by
  classical
  by_cases hs : swapOK m x y
  · rw [swapEntry, if_pos hs]
    exact Finset.prod_eq_one fun i _ => if_pos (hs i)
  · rw [swapEntry, if_neg hs]
    apply Finset.prod_eq_zero_iff.mpr
    change ¬ (∀ i, localMatch (m i) (x.1 i) (x.2 i) (y.1 i) (y.2 i)) at hs
    obtain ⟨i, hi⟩ := not_forall.mp hs
    exact ⟨i, Finset.mem_univ _, if_neg hi⟩

/-- A tensor word with h difference factors expands into 4^h signed partial
swaps. Each element of the dependent index type is one term of this sum. -/
theorem word_to_partial_swaps {L : ℕ} (a : Fin L → Bool) (x y : PairBits L) :
    (∏ i, factorEntry (if a i then .difference else .swap) (x.1 i) (x.2 i) (y.1 i) (y.2 i)) =
    ∑ k : (∀ i, Fin (choices (a i))),
      ((∏ i, signBit (a i) (k i).val : ℤ) : ℚ) * swapEntry (fun i => maskBit (a i) (k i).val) x y := by
  simp_rw [local_units]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.prod_mul_distrib, ← mask_product, Int.cast_prod]

theorem word_term_count {L : ℕ} (a : Fin L → Bool) :
    Fintype.card (∀ i, Fin (choices (a i))) = 4 ^ (Finset.univ.filter fun i => a i = true).card := by
  rw [Fintype.card_pi]
  calc
    _ = ∏ i, choices (a i) := Finset.prod_congr rfl fun i _ => Fintype.card_fin _
    _ = _ := by simp [choices, ← Finset.prod_filter]

end VWZClique.RankSwap

end

/- RankInterpolation -/
section

open VWZClique
open scoped BigOperators
namespace VWZClique.RankSwap

/-- Translation by one in the binomial basis scaled by powers of -2. -/
def shift (c : ℕ → ℤ) (h : ℕ) : ℤ := c h - 2 * c (h+1)



theorem shift_constant {c : ℕ → ℤ} (n : ℕ) (v : ℤ) (h : ∀ i ≤ n, c i = v) :
    (shift^[n] c) 0 = (-1)^n * v := by
  induction n generalizing c v with
  | zero => simpa using h 0 (by omega)
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    have hs : ∀ i ≤ n, shift c i = -v := by
      intro i hi
      rw [shift, h i (by omega), h (i+1) (by omega)]
      ring
    rw [ih (-v) hs, pow_succ]
    ring


theorem subset_evaluation {ι : Type*} (B : Finset ι) (c : ℕ → ℤ) (u : ℕ) :
    ∑ S ∈ B.powerset, (-2 : ℤ)^S.card * c (u + S.card) = (shift^[B.card] c) u := by
  classical
  induction B using Finset.induction_on generalizing c with
  | empty => simp
  | @insert b B hb ih =>
    rw [Finset.card_insert_of_notMem hb, Function.iterate_succ_apply, ← ih]
    rw [Finset.sum_powerset_insert hb, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro S hS
    have hnot : b ∉ S := fun h => hb (Finset.mem_powerset.mp hS h)
    rw [Finset.card_insert_of_notMem hnot, pow_succ, shift]
    simp only [Nat.add_assoc]
    ring

end VWZClique.RankSwap

end

/- RankFinite -/
section

open VWZClique
namespace VWZClique.RankSwap

def antisymmetric {L : ℕ} (j : BasisLabel L) : Finset (Fin L) :=
  Finset.univ.filter fun i => j i = 3

def smallSets (L d : ℕ) : Finset (Finset (Fin L)) := Finset.univ.filter fun S => S.card ≤ d

def outside (L a d : ℕ) : Finset (BasisLabel L) := Finset.univ.filter fun j =>
  ¬ (a ≤ (antisymmetric j).card ∧ (antisymmetric j).card ≤ a+d)

def active {L : ℕ} (S : Finset (Fin L)) (i : Fin L) : Bool := decide (i ∈ S)
def op {L : ℕ} (S : Finset (Fin L)) (i : Fin L) : Factor :=
  if active S i then .difference else .swap

def spec {L : ℕ} (S : Finset (Fin L)) (j : BasisLabel L) : ℚ := ∏ i, eigenvalue (op S i) (j i)

theorem word_eigenvalue {L : ℕ} (S : Finset (Fin L)) (j : BasisLabel L) :
    spec S j = (-1 : ℚ)^(antisymmetric j).card *
      (if S ⊆ antisymmetric j then (-2 : ℚ)^S.card else 0) := by
  classical
  have each (i : Fin L) : eigenvalue (op S i) (j i) =
      (if i ∈ antisymmetric j then (-1 : ℚ) else 1) *
      (if i ∈ S then (if i ∈ antisymmetric j then -2 else 0) else 1) := by
    by_cases hi : i ∈ S <;> by_cases hj : j i = 3 <;> simp [op, active, eigenvalue, hi, hj, antisymmetric]
  simp only [spec, each, Finset.prod_mul_distrib, Fintype.prod_ite_mem, Finset.prod_const]
  congr 1
  by_cases hs : S ⊆ antisymmetric j
  · rw [if_pos hs, ← Finset.prod_const]
    exact Finset.prod_congr rfl fun i hi => if_pos (hs hi)
  · rw [if_neg hs]
    obtain ⟨i,hi,hn⟩ := Finset.not_subset.mp hs
    exact Finset.prod_eq_zero hi (if_neg hn)

theorem aggregate_eigenvalue {L d : ℕ} (j : BasisLabel L) (c : ℕ → ℤ) (hc : ∀ h > d, c h = 0) :
    ∑ S ∈ smallSets L d, (c S.card : ℚ) * spec S j =
    ((-1 : ℤ)^(antisymmetric j).card * (shift^[(antisymmetric j).card] c) 0 : ℤ) := by
  classical
  let B := antisymmetric j
  have full : ∑ S ∈ smallSets L d, (c S.card : ℚ) * spec S j =
      ∑ S : Finset (Fin L), (c S.card : ℚ) * spec S j := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro S _ h
    have hh : d < S.card := by simpa [smallSets] using h
    simp [hc _ hh]
  rw [full]
  simp_rw [word_eigenvalue]
  change (∑ S : Finset (Fin L), (c S.card : ℚ) * ((-1)^B.card * (if S ⊆ B then (-2)^S.card else 0))) = _
  have single (S : Finset (Fin L)) : (c S.card : ℚ) *
        ((-1)^B.card * (if S ⊆ B then (-2)^S.card else 0)) =
      (-1)^B.card * (if S ∈ B.powerset then (-2 : ℚ)^S.card * c S.card else 0) := by
    by_cases hs : S ⊆ B <;> simp [hs, Finset.mem_powerset] <;> ring
  simp_rw [single]
  rw [← Finset.mul_sum, Finset.sum_ite_mem]
  have hs := subset_evaluation B c 0
  simp only [zero_add] at hs
  push_cast
  change _ = (-1:ℚ)^B.card * ((shift^[B.card] c) 0 : ℤ)
  rw [← hs]
  push_cast
  simp

abbrev Terms (L d : ℕ) := (S : ↥(smallSets L d)) × ((i : Fin L) → Fin (choices (active S.val i)))

def termMask {L d : ℕ} (t : Terms L d) : Mask L := fun i => maskBit (active t.1.val i) (t.2 i).val
def termCoeff {L d : ℕ} (c : ℕ → ℤ) (t : Terms L d) : ℤ :=
  c t.1.val.card * ∏ i, signBit (active t.1.val i) (t.2 i).val

theorem terms_card (L d : ℕ) : Fintype.card (Terms L d) = ∑ S ∈ smallSets L d, 4^S.card := by
  rw [Fintype.card_sigma]
  simp_rw [word_term_count]
  simp [active]
  exact Finset.sum_attach _ (fun S : Finset (Fin L) => 4 ^ S.card)

def normWeight {L : ℕ} (j : BasisLabel L) := ∏ i, inverseNormSq (j i)

theorem two_expansions {L d : ℕ} (c : ℕ → ℤ) (x y : PairBits L) :
    (∑ j : BasisLabel L, (∑ S ∈ smallSets L d, (c S.card : ℚ) * spec S j) *
      normWeight j * basisEntry j x * basisEntry j y) =
    ∑ t : Terms L d, (termCoeff c t : ℚ) * swapEntry (termMask t) x y := by
  classical
  have word (S : Finset (Fin L)) :
      ∑ j : BasisLabel L, spec S j * normWeight j * basisEntry j x * basisEntry j y =
      ∑ k : (∀ i, Fin (choices (active S i))),
        ((∏ i, signBit (active S i) (k i).val : ℤ) : ℚ) *
          swapEntry (fun i => maskBit (active S i) (k i).val) x y := by
    have h := tensor_resolution (op S) x y
    simp only [Finset.prod_mul_distrib] at h
    exact h.symm.trans (word_to_partial_swaps (active S) x y)
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm, Fintype.sum_sigma]
  rw [← Finset.sum_attach (smallSets L d) (fun S => ∑ j : BasisLabel L,
    (c S.card : ℚ) * spec S j * normWeight j * basisEntry j x * basisEntry j y)]
  apply Finset.sum_congr rfl
  intro S _
  simp only [termCoeff, Int.cast_mul]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  congr 1
  unfold termMask
  convert! (word S.val) using 1 <;> simp only [mul_assoc]


end VWZClique.RankSwap

end

/- RankRates -/
section

open Filter Topology Real
namespace VWZClique.RankSwap

/-- One-coordinate exponential moment, centered at a proposed tail cutoff p. -/
noncomputable def moment (s p t : ℝ) : ℝ := (3 + exp (s*t)) * exp (-(p*s)*t)

theorem moment_pos (s p t : ℝ) : 0 < moment s p t := by unfold moment; positivity

theorem improving_tilt (s p : ℝ) (hp : s * (1 - 4*p) < 0) :
    ∃ t : ℝ, 0 < t ∧ moment s p t < 4 := by
  have h₁ := ((hasDerivAt_const (0 : ℝ) (3 : ℝ)).add
    (((hasDerivAt_id (0 : ℝ)).const_mul s).exp))
  have h₂ := (((hasDerivAt_id (0 : ℝ)).const_mul (-(p*s))).exp)
  have hd : HasDerivAt (moment s p) (s*(1-4*p)) 0 := by
    convert! h₁.mul h₂ using 1 <;> simp [moment] <;> ring
  have hh := hd.tendsto_slope_zero_right.eventually_lt_const hp
  have pos : ∀ᶠ x in 𝓝[>] (0 : ℝ), 0 < x := self_mem_nhdsWithin
  obtain ⟨t, ht, h⟩ := (pos.and hh).exists
  have ht' : 0 < t := ht
  simp only [zero_add, smul_eq_mul, moment, mul_zero, exp_zero, mul_one] at h
  exact ⟨t, ht', by
    unfold moment
    by_contra! hn
    exact (not_lt_of_ge (mul_nonneg (inv_pos.mpr ht').le (by linarith))) h⟩

theorem positive_near_zero {f : ℝ → ℝ} {B : ℝ} (hf : ContinuousAt f 0) (h : f 0 < B) :
    ∃ x : ℝ, 0 < x ∧ x < 1/4 ∧ f x < B := by
  have hh : ∀ᶠ x in 𝓝[>] (0 : ℝ), f x < B :=
    (hf.eventually_lt_const h).filter_mono nhdsWithin_le_nhds
  have hx : ∀ᶠ x in 𝓝[>] (0 : ℝ), x < 1/4 :=
    (gt_mem_nhds (by norm_num : (0:ℝ) < 1/4)).filter_mono nhdsWithin_le_nhds
  have pos : ∀ᶠ x in 𝓝[>] (0 : ℝ), 0 < x := self_mem_nhdsWithin
  exact (pos.and (hx.and hh)).exists

theorem sparse_parameters (ε : ℝ) (hε : 0 < ε) :
    ∃ t η : ℝ, 0 < t ∧ 0 < η ∧ η < 1/4 ∧
      (1+4*exp (-t))*exp (3*t*η) < (2:ℝ)^ε := by
  have lim : Tendsto (fun t : ℝ => 1+4*exp (-t)) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds.add (tendsto_const_nhds.mul tendsto_exp_neg_atTop_nhds_zero) :
      Tendsto (fun t : ℝ => 1+4*exp (-t)) atTop (𝓝 (1+4*0)))
  have eps : 1 < (2:ℝ)^ε := Real.one_lt_rpow (by norm_num) hε
  obtain ⟨t,ht,ht'⟩ := ((eventually_gt_atTop (0 : ℝ)).and (lim.eventually_lt_const eps)).exists
  obtain ⟨η,hη,hη',h⟩ := positive_near_zero (f := fun x => (1+4*exp (-t))*exp (3*t*x))
    (by fun_prop) (B := (2:ℝ)^ε) (by simpa using ht')
  exact ⟨t,η,ht,hη,hη',h⟩

theorem combine_tails {u v : ℝ} (hu : 0 < u) (hv : 0 < v) (hu' : u < 4) (hv' : v < 4) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ L : ℕ in atTop, u^L+v^L ≤ ((2:ℝ)^(2-δ))^L := by
  let b := max u v
  have hb : 0 < b := lt_of_lt_of_le hu (le_max_left _ _)
  have hbc : b < 4 := max_lt hu' hv'
  obtain ⟨δ,hδ,_,h⟩ := positive_near_zero (f := fun x : ℝ => -((2:ℝ)^(2-x))) (B := -b)
    (by simp_rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2)]; fun_prop) (by norm_num; linarith)
  let B := (2:ℝ)^(2-δ)
  have hB : 0 < B := by dsimp [B]; positivity
  have hlt : b < B := by dsimp [B]; linarith
  have lim := tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hb.le hB.le) ((div_lt_one hB).mpr hlt)
  refine ⟨δ,hδ,?_⟩
  filter_upwards [lim.eventually_lt_const (by norm_num : (0:ℝ) < 1/2)] with L hL
  rw [div_pow, div_lt_iff₀ (pow_pos hB L)] at hL
  have h1 := pow_le_pow_left₀ hu.le (le_max_left u v) L
  have h2 := pow_le_pow_left₀ hv.le (le_max_right u v) L
  change u^L + v^L ≤ B^L
  dsimp [b] at hL
  linarith

theorem pow_comm (L : ℕ) (p : ℝ) : ((2:ℝ)^L)^p = ((2:ℝ)^p)^L := by
  rw [← Real.rpow_natCast_mul (by norm_num), mul_comm, Real.rpow_mul_natCast (by norm_num)]

end VWZClique.RankSwap

end

/- RankEstimates -/
section

open VWZClique Real Filter Topology
namespace VWZClique.RankSwap

theorem sparse_bound (L d : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (Fintype.card (Terms L d) : ℝ) ≤ (1 + 4*exp (-t))^L * exp (t*d) := by
  classical
  rw [terms_card, Nat.cast_sum]
  push_cast
  have gen : ∑ S : Finset (Fin L), (4*exp (-t))^S.card = (1+4*exp (-t))^L := by
    simpa only [one_pow, mul_one, Fintype.card_fin, add_comm (4*exp (-t)) 1]
      using Fintype.sum_pow_mul_eq_add_pow (Fin L) (4*exp (-t)) 1
  rw [← gen, Finset.sum_mul]
  calc
    _ ≤ ∑ S ∈ smallSets L d, (4*exp (-t))^S.card * exp (t*d) := by
      apply Finset.sum_le_sum
      intro S hS
      have hs : S.card ≤ d := (Finset.mem_filter.mp hS).2
      have hs' : (0:ℝ) ≤ (S.card : ℝ)*(-t) + t*d := by
        have := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hs : (S.card : ℝ) ≤ d) ht
        linarith
      rw [mul_pow, mul_assoc, ← exp_nat_mul, ← exp_add]
      exact le_mul_of_one_le_right (by positivity) (one_le_exp hs')
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ => by positivity)

theorem type_generating (L : ℕ) (v : ℝ) :
    ∑ j : BasisLabel L, (exp v)^(antisymmetric j).card = (3+exp v)^L := by
  have coord (j : BasisLabel L) : (exp v)^(antisymmetric j).card =
      ∏ i, if j i = 3 then exp v else 1 := by simp [antisymmetric, ← Finset.prod_filter]
  simp_rw [coord]
  rw [← Fintype.prod_sum (fun (_ : Fin L) (k : Fin 4) => if k = 3 then exp v else 1)]
  have bit : (∑ k : Fin 4, if k = 3 then exp v else 1) = 3 + exp v := by
    rw [Fin.sum_univ_four]
    norm_num [show (0 : Fin 4) ≠ 3 by decide, show (1 : Fin 4) ≠ 3 by decide,
      show (2 : Fin 4) ≠ 3 by decide]
  simp [bit]

noncomputable def tilted {L : ℕ} (s p t : ℝ) (j : BasisLabel L) :=
  exp (s*t * ((antisymmetric j).card - p*L))

theorem sum_tilted (L : ℕ) (s p t : ℝ) : ∑ j : BasisLabel L, tilted s p t j = (moment s p t)^L := by
  have term (j : BasisLabel L) : tilted s p t j =
      (exp (s*t))^(antisymmetric j).card * (exp (-(p*s)*t))^L := by
    unfold tilted
    rw [← exp_nat_mul, ← exp_nat_mul, ← exp_add]
    congr 1
    ring
  simp_rw [term]
  rw [← Finset.sum_mul, type_generating, ← mul_pow, moment]

/-- Bound both tails by their tilted generating functions. -/
theorem both_tails (L : ℕ) (p q u v : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q)
    (hu : 0 < u) (hv : 0 < v) :
    let a := ⌊p*L⌋₊
    let b := ⌊q*L⌋₊
    ((outside L a (b-a)).card : ℝ) ≤ (moment (-1) p u)^L + (moment 1 q v)^L := by
  classical
  intro a b
  have hab : a ≤ b := Nat.floor_mono (mul_le_mul_of_nonneg_right hpq (by positivity))
  let T := outside L a (b-a)
  change (T.card : ℝ) ≤ _
  rw [← sum_tilted, ← sum_tilted, ← Finset.sum_add_distrib]
  calc
    (T.card : ℝ) = ∑ _ ∈ T, (1 : ℝ) := by simp
    _ ≤ ∑ j ∈ T, (tilted (-1) p u j + tilted 1 q v j) := by
      apply Finset.sum_le_sum
      intro j hj
      have hout : ¬ (a ≤ (antisymmetric j).card ∧ (antisymmetric j).card ≤ b) := by
        simpa [T, outside, Nat.add_sub_of_le hab, Nat.add_comm a (b-a)] using hj
      by_cases hj' : a ≤ (antisymmetric j).card
      · have hj'' : b < (antisymmetric j).card := by omega
        have hqL : 0 ≤ q*(L:ℝ) := mul_nonneg (hp.trans hpq) (by positivity)
        have hz := (Nat.floor_lt hqL).mp hj''
        have ht : 1 ≤ tilted 1 q v j := one_le_exp (by rw [one_mul]; exact mul_nonneg hv.le (sub_nonneg.mpr hz.le))
        exact ht.trans (le_add_of_nonneg_left (exp_pos _).le)
      · have hz : ((antisymmetric j).card : ℝ) ≤ p*L :=
          (Nat.cast_le.mpr (by omega : (antisymmetric j).card ≤ a)).trans
            (Nat.floor_le (mul_nonneg hp (by positivity)))
        have ht : 1 ≤ tilted (-1) p u j := one_le_exp (mul_nonneg_of_nonpos_of_nonpos
          (by linarith) (sub_nonpos.mpr hz))
        exact ht.trans (le_add_of_nonneg_right (exp_pos _).le)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ => add_nonneg (exp_pos _).le (exp_pos _).le)

end VWZClique.RankSwap

end

/- IntegerWindow -/
section

open VWZClique VWZClique.RankSwap Filter Real
namespace VWZClique.UniformFolds

def lower (K L : ℕ) : ℕ := ((K-4)*L)/(4*K)
def upper (K L : ℕ) : ℕ := ((K+4)*L)/(4*K)
def width (K L : ℕ) : ℕ := upper K L - lower K L

theorem lower_floor {K : ℕ} (hK : 4<K) (L : ℕ) :
    lower K L = ⌊(1/4 - 1/(K:ℝ))*(L:ℝ)⌋₊ := by
  unfold lower
  rw [← Nat.floor_div_eq_div (K:=ℝ)]
  congr 1
  rw [Nat.cast_mul,Nat.cast_sub hK.le,Nat.cast_mul]
  push_cast
  have hk : (K:ℝ) ≠ 0 := by exact_mod_cast (by omega : K ≠ 0)
  field_simp

theorem upper_floor {K : ℕ} (hK : 4<K) (L : ℕ) :
    upper K L = ⌊(1/4 + 1/(K:ℝ))*(L:ℝ)⌋₊ := by
  unfold upper
  rw [← Nat.floor_div_eq_div (K:=ℝ)]
  congr 1
  push_cast
  have hk : (K:ℝ) ≠ 0 := by exact_mod_cast (by omega : K ≠ 0)
  field_simp

/-- Choose one fixed integer window parameter for every length. The two
    dimensions of the interpolation window then require only integer division. -/
theorem integer_rates (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, 4<K ∧ ∃ δ : ℝ, 0<δ ∧ ∃ N : ℕ, ∀ L ≥ N,
      (Fintype.card (Terms L (width K L)) : ℝ) ≤ ((2:ℝ)^L)^ε ∧
      ((outside L (lower K L) (width K L)).card : ℝ) ≤ ((2:ℝ)^L)^(2-δ) := by
  obtain ⟨t,η,ht,hη,hη',hs⟩ := sparse_parameters ε hε
  obtain ⟨K,hlarge⟩ := exists_nat_gt (max (4:ℝ) (1/η))
  have hKr : (4:ℝ) < K := (le_max_left _ _).trans_lt hlarge
  have hK : 4<K := by exact_mod_cast hKr
  have hk0 : (0:ℝ) < K := by linarith
  let ξ := 1/(K:ℝ)
  have hξ : 0<ξ := by dsimp [ξ]; positivity
  have hξη : ξ ≤ η := by
    apply (div_le_iff₀ hk0).mpr
    have hh := (div_lt_iff₀ hη).mp ((le_max_right _ _).trans_lt hlarge)
    linarith only [hh, mul_comm (K:ℝ) η]
  have hξ' : ξ<1/4 := hξη.trans_lt hη'
  let p := 1/4 - ξ
  let q := 1/4 + ξ
  have hp : 0 ≤ p := by dsimp [p]; linarith
  have hpq : p ≤ q := by dsimp [p,q]; linarith
  obtain ⟨u,hu,hu'⟩ := improving_tilt (-1) p (by dsimp [p]; linarith)
  obtain ⟨v,hv,hv'⟩ := improving_tilt 1 q (by dsimp [q]; linarith)
  obtain ⟨δ,hδ,hL⟩ := combine_tails (moment_pos _ _ _) (moment_pos _ _ _) hu' hv'
  obtain ⟨N,hN⟩ := eventually_atTop.1 hL
  refine ⟨K,hK,δ,hδ,max N K,?_⟩
  intro L hL
  have ha : lower K L = ⌊p*(L:ℝ)⌋₊ := lower_floor hK L
  have hb : upper K L = ⌊q*(L:ℝ)⌋₊ := upper_floor hK L
  have hab : lower K L ≤ upper K L := by
    rw [ha,hb]
    exact Nat.floor_mono (mul_le_mul_of_nonneg_right hpq (Nat.cast_nonneg L))
  have hw : (width K L : ℝ) ≤ 3*ξ*L := by
    have big : (K:ℝ) ≤ L := by exact_mod_cast ((le_max_right _ _).trans hL)
    have large' : 1 ≤ ξ*(L:ℝ) := by
      calc
        1 = ξ*(K:ℝ) := by dsimp [ξ]; field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left big hξ.le
    have lo := Nat.lt_floor_add_one (p*L)
    have hi := Nat.floor_le (mul_nonneg (hp.trans hpq) (Nat.cast_nonneg L))
    rw [← ha] at lo
    rw [← hb] at hi
    dsimp only [p,q] at lo hi
    rw [width,Nat.cast_sub hab]
    nlinarith
  constructor
  · rw [RankSwap.pow_comm]
    calc
      _ ≤ (1+4*exp (-t))^L * exp (t*(width K L)) := sparse_bound L _ t ht.le
      _ ≤ (1+4*exp (-t))^L * exp ((L:ℝ)*(3*t*ξ)) := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
        calc t*(width K L) ≤ t*(3*ξ*L) := mul_le_mul_of_nonneg_left hw ht.le
             _ = _ := by ring
      _ = ((1+4*exp (-t))*exp (3*t*ξ))^L := by rw [exp_nat_mul,mul_pow]
      _ ≤ _ := by
        apply pow_le_pow_left₀ (by positivity) _ _
        apply le_trans _ hs.le
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
        exact mul_le_mul_of_nonneg_left hξη (by positivity)
  · rw [RankSwap.pow_comm,width,ha,hb]
    exact (both_tails L p q u v hp hpq hu hv).trans (hN L ((le_max_left _ _).trans hL))

end VWZClique.UniformFolds

end

/- DyadicBounds -/
section

open VWZClique
namespace VWZClique.RankSwap

/-- The weighted coefficient bound makes each backward translation cost a factor of two. -/
def coeffBound (c : ℕ → ℤ) (K : ℝ) : Prop := ∀ h, (4:ℝ)^h * |(c h : ℝ)| ≤ K

theorem inverse_bound {d : ℕ} {b c : ℕ → ℤ} {K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ h > d, b h = 0) (he : shift b = c) (hc : coeffBound c K) : coeffBound b (2*K) := by
  have step (h : ℕ) (ih : (4:ℝ)^(h+1) * |(b (h+1) : ℝ)| ≤ 2*K) :
      (4:ℝ)^h * |(b h : ℝ)| ≤ 2*K := by
    have hb' := congrFun he h
    change b h - 2*b (h+1) = c h at hb'
    have hr : (b h : ℝ) = (c h : ℝ) + 2*(b (h+1) : ℝ) := by exact_mod_cast (by omega : b h = c h + 2*b (h+1))
    rw [hr]
    have habs := abs_add_le (c h : ℝ) (2*(b (h+1) : ℝ))
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2)] at habs
    rw [pow_succ] at ih
    calc
      _ ≤ 4^h * (|(c h : ℝ)| + 2*|(b (h+1) : ℝ)|) := mul_le_mul_of_nonneg_left habs (by positivity)
      _ ≤ _ := by linarith only [hc h,ih]
  have aux (n : ℕ) : ∀ h, d+1-h ≤ n → (4:ℝ)^h * |(b h : ℝ)| ≤ 2*K := by
    induction n with
    | zero =>
      intro h hh
      rw [hb h (by omega)]
      simpa using (by linarith : (0:ℝ) ≤ 2*K)
    | succ n ih =>
      intro h hh
      exact step _ (ih (h+1) (by omega))
  exact fun h => aux (d+1-h) h le_rfl


theorem eval_bound {c : ℕ → ℤ} {K : ℝ} (hK : 0 ≤ K) (hc : coeffBound c K) (j : ℕ) :
    |(((shift^[j] c) 0 : ℤ) : ℝ)| ≤ 3^j * K := by
  have one (h : ℕ) : |(c h : ℝ)| ≤ K :=
    (le_mul_of_one_le_left (abs_nonneg _) (one_le_pow₀ (by norm_num) (n := h))).trans (hc h)
  have iter (n : ℕ) : ∀ h, |(((shift^[n] c) h : ℤ) : ℝ)| ≤ 3^n*K := by
    induction n with
    | zero => simpa using one
    | succ n ih =>
      intro h
      rw [Function.iterate_succ_apply',shift,Int.cast_sub,Int.cast_mul,Int.cast_ofNat]
      have ht := abs_sub ((((shift^[n]) c) h : ℤ) : ℝ) (2*((((shift^[n]) c) (h+1) : ℤ) : ℝ))
      rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at ht
      rw [pow_succ]
      linarith [ih h,ih (h+1)]
  exact iter j 0

def denominatorExponent {L : ℕ} (j : BasisLabel L) :=
  (Finset.univ.filter (fun i => ¬ j i < 2)).card

theorem norm_dyadic {L : ℕ} (j : BasisLabel L) :
    normWeight j = 1 / (2 : ℚ)^(denominatorExponent j) := by
  calc
    normWeight j = ∏ i, (if ¬ j i < 2 then (1/2 : ℚ) else 1) := by
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : j i < 2 <;> simp [inverseNormSq,hi]
    _ = (1/2 : ℚ)^(denominatorExponent j) := by
      rw [← Finset.prod_filter,Finset.prod_const]
      rfl
    _ = _ := one_div_pow _ _


end VWZClique.RankSwap

end

/- BoundedDecomposition -/
section

open VWZClique
namespace VWZClique.RankSwap

def residualNum (c : ℕ → ℤ) (k : ℕ) : ℤ := 1 - (-1)^k * (shift^[k] c) 0

theorem residual_bound {L : ℕ} {c : ℕ → ℤ} {K : ℝ} (hK : 0 ≤ K) (hc : coeffBound c K)
    (j : BasisLabel L) : |((residualNum c (antisymmetric j).card : ℤ) : ℝ)| ≤ 1 + 3^L*K := by
  have hj : (antisymmetric j).card ≤ L := by
    simpa [antisymmetric] using Finset.card_le_univ (antisymmetric j)
  have he := eval_bound hK hc (antisymmetric j).card
  have hb := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤3) hj) hK
  unfold residualNum
  push_cast
  calc
    _ ≤ |(1:ℝ)| + |(-1:ℝ)^(antisymmetric j).card * ((shift^[(antisymmetric j).card] c) 0 : ℤ)| := abs_sub _ _
    _ ≤ _ := by simpa [abs_mul,abs_pow] using add_le_add_left (he.trans hb) 1

theorem term_bound {L d : ℕ} {c : ℕ → ℤ} {K : ℝ} (hc : coeffBound c K) (t : Terms L d) :
    |((termCoeff c t : ℤ) : ℝ)| ≤ K := by
  have hsg (b : Bool) (i : ℕ) : |((signBit b i : ℤ) : ℝ)| = 1 := by
    unfold signBit
    split <;> norm_num
  simp only [termCoeff,Int.cast_mul, Int.cast_prod,abs_mul,Finset.abs_prod,hsg,Finset.prod_const_one,mul_one]
  exact (le_mul_of_one_le_left (abs_nonneg _) (one_le_pow₀ (by norm_num) (n := t.1.val.card))).trans (hc _)

theorem decomposition_for {L a d : ℕ} (c : ℕ → ℤ) (hc : ∀ h > d, c h = 0)
    (hval : ∀ t ≤ d, (shift^[a+t] c) 0 = (-1)^(a+t)) :
    ∀ x y : PairBits L, (if x=y then (1:ℚ) else 0) =
      (∑ j ∈ outside L a d, ((residualNum c (antisymmetric j).card : ℚ)/2^(denominatorExponent j)) *
        basisEntry j x * basisEntry j y) +
      ∑ t : Terms L d, (termCoeff c t : ℚ) * swapEntry (termMask t) x y := by
  classical
  intro x y
  let r := fun j : BasisLabel L => (residualNum c (antisymmetric j).card : ℚ) / 2^(denominatorExponent j)
  have small : ∑ j ∈ outside L a d, r j * basisEntry j x * basisEntry j y =
      ∑ j, r j * basisEntry j x * basisEntry j y := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    have range : a ≤ (antisymmetric j).card ∧ (antisymmetric j).card ≤ a+d := by simpa [outside] using hj
    obtain ⟨t,ht⟩ := Nat.exists_eq_add_of_le range.1
    simp [r,residualNum,ht,hval t (by omega),← mul_pow]
  change _ = (∑ j ∈ outside L a d, r j * _ * _) + _
  rw [small,← two_expansions,identity_resolution,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  change normWeight j * _ * _ = _ + _
  rw [aggregate_eigenvalue j c hc,norm_dyadic]
  simp only [r,residualNum,Int.cast_sub,Int.cast_one]
  ring


end VWZClique.RankSwap

end

/- WindowAlgorithm -/
section

open VWZClique
namespace VWZClique.RankSwap.Window

/-- Coefficients past the end of the finite table are zero. -/
def entry : List ℤ → ℕ → ℤ
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, h+1 => entry xs h

/-- One backward sweep. The first component caches the new boundary value. -/
def sweep : List ℤ → ℤ × List ℤ
  | [] => (0,[])
  | x :: xs =>
    let tail := sweep xs
    let y := x + 2 * tail.1
    (y, y :: tail.2)

theorem boundary (xs : List ℤ) : entry (sweep xs).2 0 = (sweep xs).1 := by
  cases xs <;> rfl

theorem sweep_length (xs : List ℤ) : (sweep xs).2.length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa only [sweep,List.length_cons,Nat.add_left_cancel_iff] using congrArg Nat.succ ih

theorem undo (xs : List ℤ) : shift (entry (sweep xs).2) = entry xs := by
  funext h
  induction xs generalizing h with
  | nil => simp [sweep,shift,entry]
  | cons x xs ih =>
    cases h with
    | zero => simp [shift,sweep,entry,boundary]
    | succ h => exact ih h

theorem tail_zero (xs : List ℤ) (h : ℕ) (hh : xs.length ≤ h) : entry xs h = 0 := by
  induction xs generalizing h with
  | nil => rfl
  | cons x xs ih =>
    cases h with
    | zero => simp at hh
    | succ h => exact ih h (by simp at hh; omega)

theorem entry_constant (x : ℤ) (n h : ℕ) (hh : h<n) :
    entry (List.replicate n x) h = x := by
  induction n generalizing h with
  | zero => omega
  | succ n ih =>
    rw [List.replicate_succ]
    cases h with
    | zero => rfl
    | succ h => exact ih h (by omega)

/-- Repeat the backward sweep. The loop has no field operations or divisions. -/
def generate : ℕ → List ℤ → List ℤ
  | 0, xs => xs
  | k+1, xs => (sweep (generate k xs)).2

theorem gen_length (xs : List ℤ) (k : ℕ) : (generate k xs).length=xs.length := by
  induction k with
  | zero => rfl
  | succ k ih => exact (sweep_length _).trans ih

theorem gen_correct (xs : List ℤ) (k : ℕ) : (shift^[k]) (entry (generate k xs)) = entry xs := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [Function.iterate_succ_apply,generate,undo] using ih

def coefficients (a d : ℕ) : List ℤ := generate a (List.replicate (d+1) ((-1:ℤ)^a))

theorem correct (a d : ℕ) :
    let c := entry (coefficients a d)
    (∀ h > d, c h = 0) ∧ coeffBound c ((2:ℝ)^a * 4^d) ∧
    ∀ t ≤ d, (shift^[a+t] c) 0 = (-1)^(a+t) := by
  let xs := List.replicate (d+1) ((-1:ℤ)^a)
  have len (k : ℕ) : (generate k xs).length = d+1 := (gen_length xs k).trans (by simp [xs])
  have zero (k h : ℕ) (hh : h>d) : entry (generate k xs) h=0 := tail_zero _ _ (by rw [len]; omega)
  have bound (k : ℕ) : coeffBound (entry (generate k xs)) ((2:ℝ)^k * 4^d) := by
    induction k with
    | zero =>
      intro h
      by_cases hd : h ≤ d
      · change (4:ℝ)^h * |(entry (List.replicate (d+1) ((-1:ℤ)^a)) h : ℝ)| ≤ _
        rw [entry_constant _ _ _ (by omega)]
        simpa [abs_pow] using (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 4) hd)
      · simp [zero 0 h (by omega)]
    | succ k ih =>
      have eq : shift (entry (generate (k+1) xs)) = entry (generate k xs) := undo _
      convert! inverse_bound (by positivity) (zero (k+1)) eq ih using 1 <;> ring
  refine ⟨zero a,bound a,?_⟩
  intro t ht
  change (shift^[a+t]) (entry (generate a xs)) 0 = _
  rw [Nat.add_comm a t,Function.iterate_add_apply,gen_correct,shift_constant t ((-1)^a),pow_add]
  exact fun i hi => entry_constant _ _ _ (by omega)

/-- The finite coefficient table generated by the sweeps gives the exact
decomposition, together with bounds on the integers used in it. -/
theorem exact_decomposition (L a d : ℕ) :
    let c := entry (coefficients a d)
    (∀ t : Terms L d, |((termCoeff c t : ℤ) : ℝ)| ≤ 2^a*4^d) ∧
    (∀ j : BasisLabel L, |((residualNum c (antisymmetric j).card : ℤ) : ℝ)| ≤ 1 + 3^L*(2^a*4^d)) ∧
    ∀ x y : PairBits L, (if x=y then (1:ℚ) else 0) =
      (∑ j ∈ outside L a d, ((residualNum c (antisymmetric j).card : ℚ)/2^(denominatorExponent j)) *
        basisEntry j x * basisEntry j y) +
      ∑ t : Terms L d, (termCoeff c t : ℚ) * swapEntry (termMask t) x y := by
  obtain ⟨hc,hb,hv⟩ := correct a d
  exact ⟨term_bound hb,residual_bound (by positivity) hb,decomposition_for _ hc hv⟩

end VWZClique.RankSwap.Window

end

/- UniformExpansion -/
section

open VWZClique VWZClique.RankSwap 
namespace VWZClique.UniformFolds

/-- The recursive evaluator can enumerate the terms by their natural finite type.
    No arbitrary bijection of sparse sets of masks with integer indices is needed in the data. -/
structure Expansion (L : ℕ) where
  Index : Type
  [finite : Fintype Index]
  masks : Index → Mask L
  coefficients : Index → ℤ
  labels : Finset (BasisLabel L)
  diagonal : BasisLabel L → ℚ
  identity : ∀ x y : PairBits L, (if x=y then (1:ℚ) else 0) =
    (∑ j ∈ labels, diagonal j * basisEntry j x * basisEntry j y) +
      ∑ i, (coefficients i : ℚ)*swapEntry (masks i) x y

attribute [instance] Expansion.finite

def windowCoeff (K L : ℕ) := Window.entry (Window.coefficients (lower K L) (width K L))

def windowDiagonal (K L : ℕ) (j : BasisLabel L) : ℚ :=
  (residualNum (windowCoeff K L) (antisymmetric j).card : ℚ) / 2^(denominatorExponent j)

/-- All mask and coefficient functions are explicit finite data computed from the
    integer parameter and length. The argument of the summation is the sparse-set
    index together with its four choices at each active coordinate. -/
def windowExpansion (K L : ℕ) : Expansion L where
  Index := Terms L (width K L)
  masks := termMask
  coefficients := termCoeff (windowCoeff K L)
  labels := outside L (lower K L) (width K L)
  diagonal := windowDiagonal K L
  identity := (Window.exact_decomposition L (lower K L) (width K L)).2.2

/-- The exact integer generator simultaneously has the rank and swap savings. -/
theorem windowExpansion_rates (ε : ℝ) (hε : 0<ε) :
    ∃ K : ℕ, 4<K ∧ ∃ δ : ℝ, 0<δ ∧ ∃ N : ℕ, ∀ L ≥ N,
      (Fintype.card (windowExpansion K L).Index : ℝ) ≤ ((2:ℝ)^L)^ε ∧
      ((windowExpansion K L).labels.card : ℝ) ≤ ((2:ℝ)^L)^(2-δ) :=
  integer_rates ε hε



end VWZClique.UniformFolds

end

/- MaskEnumeration -/
section

open VWZClique
namespace VWZClique.RankSwap.MaskEnumeration

abbrev Digits (L : ℕ) := Fin L → Fin 5
def support {L : ℕ} (w : Digits L) : Finset (Fin L) := Finset.univ.filter fun i => w i ≠ 0

def symbol (b : Bool) (x : Fin (choices b)) : Fin 5 :=
  if h : b=true then ⟨x.val+1,by have := x.isLt; simp [choices,h] at this; omega⟩ else 0

def code {L d : ℕ} (t : Terms L d) : Digits L := fun i => symbol (active t.1.val i) (t.2 i)

theorem support_code {L d : ℕ} (t : Terms L d) : support (code t) = t.1.val := by
  ext i
  simp only [support,Finset.mem_filter,Finset.mem_univ,true_and]
  by_cases h : i∈t.1.val
  · simp only [h,iff_true]
    intro he
    have hv := congrArg Fin.val he
    simp [code,symbol,active,h] at hv
  · simp [code,symbol,active,h]

theorem symbol_inj {b : Bool} {x y : Fin (choices b)} (hh : symbol b x = symbol b y) : x=y := by
  apply Fin.ext
  cases b
  · have hx : x.val < 1 := x.isLt; have hy : y.val < 1 := y.isLt; omega
  · simpa [symbol,Fin.ext_iff] using (congrArg Fin.val hh)

theorem code_injective {L d : ℕ} : Function.Injective (@code L d) := by
  rintro ⟨S,f⟩ ⟨T,g⟩ he
  have hs : S.val=T.val := (support_code ⟨S,f⟩).symm.trans ((congrArg support he).trans (support_code ⟨T,g⟩))
  obtain rfl : S=T := Subtype.ext hs
  congr 1
  funext i
  exact symbol_inj (congrFun he i)

def unpack {L d : ℕ} (w : Digits L) (h : (support w).card ≤ d) : Terms L d :=
  ⟨⟨support w,by simpa [smallSets] using h⟩,
    fun i => if hi : w i=0 then ⟨0,by simp [choices,active,support,hi]⟩ else
      ⟨(w i).val-1,by have hw := (w i).isLt; simp [choices,active,support,hi]; omega⟩⟩

theorem code_unpack {L d : ℕ} (w : Digits L) (h : (support w).card≤d) : code (unpack w h)=w := by
  funext i
  apply Fin.ext
  by_cases hi : w i=0
  · simp [unpack,code,symbol,support,active,hi]
  · have pos : 0<(w i).val := Fin.pos_iff_ne_zero.mpr hi
    simp [unpack,code,symbol,support,active,hi]
    omega

/-- The sparse choices are exactly the integers below 5^L with at most d
nonzero base-five digits. Zero denotes swap and the four other digits pin the local entries. -/
def allowed (L d : ℕ) :=
  (Finset.univ : Finset (Fin (5^L))).filter fun x =>
    (support (finFunctionFinEquiv.symm x : Digits L)).card ≤ d

def enumerate (L d : ℕ) : Terms L d ≃ ↥(allowed L d) where
  toFun t := ⟨finFunctionFinEquiv (code t),by
    simpa [allowed,support_code,smallSets] using (show t.1.val.card ≤ d from (Finset.mem_filter.mp t.1.property).2)⟩
  invFun x := unpack (finFunctionFinEquiv.symm x.val) ((Finset.mem_filter.mp x.property).2)
  left_inv t := code_injective (by simp [code_unpack])
  right_inv x := Subtype.ext (by simp [code_unpack])



def integerWeight {L : ℕ} (c : ℕ → ℤ) (w : Digits L) : ℤ :=
  c (support w).card * ∏ i, if 3 ≤ (w i).val then -1 else 1






end VWZClique.RankSwap.MaskEnumeration

end

/- NativeMaskScanSpectral -/
section

namespace VWZClique.IntegerRAM.MaskScan
open RankSwap RankSwap.MaskEnumeration Graph






def maskKey (L d j : ℕ) := selected d ((L:ℤ)+1) (totalN 5 1 j L)
def labelKey (L a d j : ℕ) := selected ((a:ℤ)-1) ((a:ℤ)+d+1) (totalN 4 3 j L)









end VWZClique.IntegerRAM.MaskScan

end

/- NativeMaskScanOffsets -/
section

namespace VWZClique.IntegerRAM.MaskScan.Arena
def origin (q N : ℕ) := q+9*N+81*N^2
def span (N : ℕ) := N^3
def slot (q N j : ℕ) := origin q N + j*span N

end VWZClique.IntegerRAM.MaskScan.Arena

end

/- FoldRouting -/
section

open VWZClique
namespace VWZClique.FoldProof

def site (g i : Fin 3) : V := finProdFinEquiv (g,i)
def next (h : Fin 3) : Fin 3 := ![1,2,0] h















end VWZClique.FoldProof

end

/- WeightedPlacement -/
section

open VWZClique VWZClique.FoldProof OAI.MatrixMultiplication.Arithmetic
namespace VWZClique.WeightedProof

def endpoint (h : Fin 3) : Slot → V
  | .inl i => site h i
  | .inr i => site (next h) i

def locate (u v : V) : EdgeSlot :=
  let a := (finProdFinEquiv (m := 3) (n := 3)).symm u
  let b := (finProdFinEquiv (m := 3) (n := 3)).symm v
  if a.1 = b.1 then
    if a.2 = 1 ∧ b.2 = 2 then (![2,0,1] a.1,.inr a.2,.inr b.2)
    else (a.1,.inl a.2,.inl b.2)
  else if next a.1 = b.1 then (a.1,.inl a.2,.inr b.2)
  else (b.1,.inr a.2,.inl b.2)



def chosen (π : Equiv.Perm V) (p : V × V) : EdgeSlot :=
  locate (min (π.symm p.1) (π.symm p.2)) (max (π.symm p.1) (π.symm p.2))


open Classical in
noncomputable def pairs (H : SimpleGraph V) : Finset (V × V) :=
  Finset.univ.filter fun p => p.1 < p.2 ∧ H.Adj p.1 p.2



noncomputable def slots (π : Equiv.Perm V) (H : SimpleGraph V) : Finset EdgeSlot :=
  (pairs H).image (chosen π)




end VWZClique.WeightedProof

end

/- WeightedPadding -/
section

open VWZClique OAI.MatrixMultiplication.Arithmetic
namespace VWZClique.WeightedProof

variable {F I J : Type*} [Field F]

def literal (w : I → F) : I ⊕ F → F := Sum.elim w id











end VWZClique.WeightedProof

end

/- WeightedChannels -/
section

open VWZClique VWZClique.FoldProof
namespace VWZClique.WeightedProof


def edgeKey {n : ℕ} (i j : V) (x y : Fin n) : WeightKey n :=
  if i<j then .inr (i,j,x,y) else .inr (j,i,y,x)





end VWZClique.WeightedProof

end

/- UniformFoldWeights -/
section

open VWZClique VWZClique.FoldProof VWZClique.WeightedProof
namespace VWZClique.UniformFolds

/-- A recursive binary index, independent of any enumeration of a finite function type. -/
def wordIndex : (L : ℕ) → Bits L ≃ Fin (2^L)
  | 0 => by
    change Bits 0 ≃ Fin 1
    exact ⟨fun _ => 0, fun _ i => i.elim0, fun _ => funext fun i => i.elim0,
      fun _ => Subsingleton.elim _ _⟩
  | L+1 => (Fin.consEquiv (fun _ : Fin (L+1) => Bool)).symm.trans <|
      (finTwoEquiv.symm.prodCongr (wordIndex L)).trans <|
      finProdFinEquiv.trans (finCongr (by rw [pow_succ,Nat.mul_comm]))



def inputKey {F : Type*} [Field F] {L : ℕ}
    (π : Equiv.Perm V) (E : Finset EdgeSlot) : ChannelKey L → WeightKey (2^L) ⊕ F
  | (h,.inl (.inl i,x)) => .inl (.inl (π (site h i),wordIndex L x))
  | (_,.inl (.inr _,_)) => .inr 1
  | (h,.inr (s,t,x,y)) => if (h,s,t) ∈ E then
      .inl (edgeKey (π (endpoint h s)) (π (endpoint h t)) (wordIndex L x) (wordIndex L y))
    else .inr 1








def Binary (x : ℚ) : Prop := x=0 ∨ x=1









end VWZClique.UniformFolds

end

/- DoubleIdentity -/
section

open VWZClique

namespace VWZClique.Double

abbrev Node {L : ℕ} (S : Finset (BasisLabel L)) := S × Bits L

variable {F : Type*} [Field F] [CharZero F] {L : ℕ}










end VWZClique.Double

end

/- TraceDyadicData -/
section

namespace VWZClique.TraceDyadic
open RankSwap UniformFolds Double



def digit (j : Fin 4) (s u : Bool) : ℤ := (oneBit j s u).num



def basisInt {L : ℕ} (j : BasisLabel L) (x : PairBits L) : ℤ :=
  ∏ i, digit (j i) (x.1 i) (x.2 i)




def bitInt (x : ℚ) : ℤ := if x=1 then 1 else 0



def channelInt {L : ℕ} (w : ChannelKey L → ℚ) (h : Fin 3) (a b : Block L) : ℤ :=
  let x : Slot → Bits L := Sum.elim a b
  (∏ i : Slot, bitInt (w (h, .inl (i, x i)))) *
    ∏ i : Slot, ∏ j : Slot, bitInt (w (h, .inr (i,j,x i,x j)))








/-- Integer obtained by widening the actual evaluator's residual coefficient to denominator 2^L. -/
def residualInt (K L : ℕ) (j : BasisLabel L) : ℤ :=
  residualNum (windowCoeff K L) (antisymmetric j).card * 2^(L - denominatorExponent j)




end VWZClique.TraceDyadic

end

/- NativeMaskScanPrepared -/
section

namespace VWZClique.IntegerRAM.MaskScan.Arena
open Structured RankSwap RankSwap.MaskEnumeration UniformFolds

structure CompactTables (K L u v t s e : ℕ) (m : Memory) : Prop where
  maskCount : m e=Fintype.card (Terms L (width K L))
  labelCount : m (e+1:ℕ)=(outside L (lower K L) (width K L)).card
  mask : ∀ z : Fin (5^L), z∈allowed L (width K L) →
    m (u+rank (maskKey L (width K L)) z.val:ℕ)=z.val ∧ m (v+rank (maskKey L (width K L)) z.val:ℕ)=
      integerWeight (windowCoeff K L) (finFunctionFinEquiv.symm z)
  labels : ∀ z : Fin (4^L), (finFunctionFinEquiv.symm z : BasisLabel L)∈outside L (lower K L) (width K L) →
    m (t+rank (labelKey L (lower K L) (width K L)) z.val:ℕ)=z.val ∧
      m (s+rank (labelKey L (lower K L) (width K L)) z.val:ℕ)=TraceDyadic.residualInt K L (finFunctionFinEquiv.symm z)

/-- The retained masks and projected-label diagonal owned by this stack frame. -/
def Prepared (L K q : ℕ) (m : Memory) : Prop := CompactTables K L
  (slot q (2^L) 3) (slot q (2^L) 4) (slot q (2^L) 5) (slot q (2^L) 6) (slot q (2^L) 7) m

theorem scan_lengths (L : ℕ) : 5^L≤ span (2^L) ∧ 4^L≤ span (2^L) := by
  rw [span,←pow_mul,Nat.mul_comm L 3,pow_mul]
  exact ⟨Nat.pow_le_pow_left (by decide) L,Nat.pow_le_pow_left (by decide) L⟩

theorem Prepared.congr {L K q : ℕ} {m o : Memory} (h : Prepared L K q m)
    (same : ∀ z : ℕ, q≤ z → z< slot q (2^L) 7+2 → o z=m z) : Prepared L K q o := by
  have base : q≤ origin q (2^L) := by unfold origin; omega
  obtain ⟨five,four⟩ := scan_lengths L
  have use (i : ℕ) (lo : q≤ i) (hi : i< origin q (2^L)+7*span (2^L)+2) := same i lo hi
  obtain ⟨mm,ll,ms,labels⟩ := h
  constructor
  · exact (use _ (by dsimp [slot];omega) (by dsimp [slot];omega)).trans mm
  · exact (use _ (by dsimp [slot];omega) (by dsimp [slot];omega)).trans ll
  · intro z hz
    have a := rank_le (maskKey L (width K L)) z.val
    have b := z.isLt
    obtain ⟨c,v⟩ := ms z hz
    exact ⟨(use _ (by dsimp [slot];omega) (by dsimp [slot];omega)).trans c,
      (use _ (by dsimp [slot];omega) (by dsimp [slot];omega)).trans v⟩
  · intro z hz
    have a := rank_le (labelKey L (lower K L) (width K L)) z.val
    have b := z.isLt
    obtain ⟨c,v⟩ := labels z hz
    exact ⟨(use _ (by dsimp [slot];omega) (by dsimp [slot];omega)).trans c,
      (use _ (by dsimp [slot];omega) (by dsimp [slot];omega)).trans v⟩

end VWZClique.IntegerRAM.MaskScan.Arena

end

/- NativeFrame -/
section

namespace VWZClique.IntegerRAM.NativeFrame
open Structured

/-- Fixed immediate-address registers inside the first 297 words. The original
graph has already been grouped when these cells are used. -/
inductive Field where
  | value | index | coefficient | flag | leftLength | rightLength | bothLength | weights
  deriving DecidableEq

def Field.offset : Field → ℕ
  | .value => 0 | .index => 1 | .coefficient => 2 | .flag => 3
  | .leftLength => 4 | .rightLength => 5 | .bothLength => 6 | .weights => 7

def reg (d : ℕ) (f : Field) : ℤ := 1 + 8*(d:ℤ) + (f.offset:ℤ)












end VWZClique.IntegerRAM.NativeFrame

end

/- UniformFolds -/
section

open VWZClique VWZClique.FoldProof VWZClique.WeightedProof
namespace VWZClique.UniformFolds

/-- The three graph branches of the signed identity. -/
inductive Branch where
  | left | right | both
  deriving DecidableEq

















end VWZClique.UniformFolds

end

/- UniformFoldPaths -/
section

open VWZClique VWZClique.FoldProof VWZClique.WeightedProof
namespace VWZClique.UniformFolds

/-- One actual recursive call, selecting concrete masks on a precomputed graph branch. -/
structure Round (L : ℕ) where
  H : SimpleGraph V
  π : Equiv.Perm V
  a : Option (Mask L)
  b : Option (Mask L)

noncomputable def Round.inputs {L : ℕ} (r : Round L) (w : WeightKey (2^L) → ℚ) : ChannelKey L → ℚ :=
  fun j => literal w (inputKey r.π (slots r.π r.H) j)












end VWZClique.UniformFolds

end

/- DoubleCost -/
section

open Real

namespace VWZClique.Double

def budget (a g n p T q t : ℕ) : ℕ :=
  (a*n^2*(p+129*n^2) + a*n^2*T + (a*n)*(g*n)) +
  (g*n^2*(p+129*n^2) + a*n^2*(p+129*n^2)) +
  (t*(q + (a*n)*(g*n)) + 2*((a*n)*(g*n)))





end VWZClique.Double

end

/- IntegerTiling -/
section

namespace VWZClique.Double.IntegerTiling

/-- Drop one binary index bit per full group of q bits. -/
def side (L q : ℕ) := 2^(3*L-L/q)
def blocks (L q : ℕ) := 2^(L/q)

theorem positive_rate {δ : ℝ} (hd : 0 < δ) : ∃ q : ℕ, 0<q ∧ (1:ℝ)/(q:ℝ) ≤ δ := by
  obtain ⟨n,hn⟩ := exists_nat_ge (δ⁻¹)
  refine ⟨n+1,by omega,?_⟩
  have h : δ⁻¹ ≤ ((n+1:ℕ):ℝ) := by push_cast; linarith
  apply (div_le_iff₀ (by positivity : (0:ℝ) < (n+1:ℕ))).2
  calc
    1 = δ * δ⁻¹ := (mul_inv_cancel₀ hd.ne').symm
    _ ≤ _ := mul_le_mul_of_nonneg_left h hd.le




end VWZClique.Double.IntegerTiling

end

/- UniformProjectionBudget -/
section

namespace VWZClique.UniformFolds

/-- A zero tile parameter makes one full-size tile. It supplies a concrete
fallback at the finitely many lengths below the rank estimate's threshold. -/
def effectiveTile (q L a : ℕ) : ℕ :=
  if a*2^L ≤ Double.IntegerTiling.side L q then q else 0

/-- The block size and block count use integer division at every input length.
The square multiplication and basis-transform charges are supplied by the caller. -/
def projectionWork (mm : ℕ → ℕ) (T q L a : ℕ) : ℕ :=
  let t := effectiveTile q L a
  Double.budget a a (2^L) (mm (2^L)) (T*(L+1)*4^L)
    (mm (Double.IntegerTiling.side L t)) (Double.IntegerTiling.blocks L t)




end VWZClique.UniformFolds

end

/- UniformFoldBudget -/
section

namespace VWZClique.UniformFolds

/-- A single set of integer parameters works at every sufficiently large length. -/
structure Cut (α : ℝ) where
  window : ℕ
  window_large : 4 < window
  tile : ℕ
  tile_pos : 0 < tile
  threshold : ℕ
  rates : ∀ L ≥ threshold,
    (Fintype.card (windowExpansion window L).Index : ℝ) ≤ ((2:ℝ)^L)^(α/8) ∧
    ((windowExpansion window L).labels.card : ℝ) ≤ ((2:ℝ)^L)^(2-(1:ℝ)/tile)

private theorem cut_exists (α : ℝ) (hα : 0 < α) : Nonempty (Cut α) := by
  obtain ⟨K,hK,δ,hδ,N,rates⟩ := windowExpansion_rates (α/8) (by positivity)
  obtain ⟨q,hq,hqδ⟩ := Double.IntegerTiling.positive_rate hδ
  refine ⟨⟨K,hK,q,hq,N,?_⟩⟩
  intro L hL
  obtain ⟨hm,hr⟩ := rates L hL
  exact ⟨hm,hr.trans (Real.rpow_le_rpow_of_exponent_le
    (one_le_pow₀ (by norm_num : (1:ℝ)≤2)) (by linarith))⟩

structure Saving where
  val : ℝ
  pos : 0 < val
  le_one : val ≤ 1

noncomputable def selectCut (a : Saving) : Cut a.val := Classical.choice (cut_exists a.val a.pos)

noncomputable def nextSaving (a : Saving) : Saving :=
  let q := (selectCut a).tile
  have hq : 0 < q := (selectCut a).tile_pos
  { val := min (a.val/2) ((1:ℝ)/q)
    pos := lt_min (by linarith [a.pos]) (by positivity)
    le_one := (min_le_left _ _).trans (by linarith [a.le_one]) }

noncomputable def levelSaving : ℕ → Saving
  | 0 => ⟨1,by norm_num,le_rfl⟩
  | k+1 => nextSaving (levelSaving k)

/-- The two lookups are indexed only by the number of edges, bounded by 36.
Neither lookup uses the assignment-domain length. -/
noncomputable def windowAt (e : ℕ) : ℕ := (selectCut (levelSaving (e-1))).window
noncomputable def tileAt (e : ℕ) : ℕ := (selectCut (levelSaving (e-1))).tile













end VWZClique.UniformFolds

end

/- TraceDyadic -/
section

namespace VWZClique.TraceDyadic
open UniformFolds Double

variable {L : ℕ}

/-- An integral basis transform applied to one pair of bit strings. -/
def transform (j : BasisLabel L) (f : PairBits L → ℤ) : ℤ :=
  ∑ x, basisInt j x * f x


def rawLeft (S T : Finset (BasisLabel L)) (w : ChannelKey L → ℚ) (u : Node S) (v : Node T) : ℤ :=
  transform v.1 fun y => transform u.1 fun x => channelInt w 0 (block x u.2) (block y v.2)

def leftTable (S T : Finset (BasisLabel L)) (K J : ℕ) (w : ChannelKey L → ℚ) : Matrix (Node S) (Node T) ℤ :=
  fun u v => (residualInt K L u.1 * residualInt J L v.1) * rawLeft S T w u v

def midTable (T : Finset (BasisLabel L)) (w : ChannelKey L → ℚ) : Matrix (Node T) (Block L) ℤ :=
  fun v c => transform v.1 fun y => channelInt w 1 (block y v.2) c

def rightTable (S : Finset (BasisLabel L)) (w : ChannelKey L → ℚ) : Matrix (Block L) (Node S) ℤ :=
  fun c u => transform u.1 fun x => channelInt w 2 c (block x u.2)











/-- Both matrix multiplications and the trace take place in the integers. -/
def numerator (S T : Finset (BasisLabel L)) (K J : ℕ) (w : ChannelKey L → ℚ) : ℤ :=
  Matrix.trace (leftTable S T K J w * (midTable T w * rightTable S w))






end VWZClique.TraceDyadic

end

/- CliqueQuotient -/
section

/-! Exact integer division by repeated addition, comparison and subtraction, for
    recovering scaled matrix-product entries on a RAM without a divide instruction.
    This is the arithmetic schedule; the cost below counts its scalar iterations. -/

namespace VWZClique.Quotient

/-- Compute `2^j * x` using only repeated addition. -/
def twice : ℕ → ℕ → ℕ
  | 0, x => x
  | j+1, x => twice j (x+x)


/-- The largest candidate scales first. Both scales can be recomputed from the
    depth with addition, so no division, shift, or bitwise operator is needed. -/
def scan : ℕ → ℕ → ℕ → ℕ × ℕ
  | 0, a, _ => (0,a)
  | j+1, a, d =>
    let p := twice j d
    if p ≤ a then
      let qr := scan j (a-p) d
      (twice j 1 + qr.1, qr.2)
    else scan j a d



/-- Count the positive powers of two up to `a`, starting from `p+1`. -/
def height (a p : ℕ) : ℕ :=
  if p+1 ≤ a then 1+height a (p+p+1) else 0
termination_by a-p
decreasing_by omega




/-- Integer quotient and remainder, determined by one addition-only height loop
    and the scan. -/
def quotient (a d : ℕ) := scan (height a 0) a d


/-- Restore the sign after operating on a nonnegative magnitude. -/
def signed (z : ℤ) (d : ℕ) : ℤ := z.sign * ((quotient z.natAbs d).1 : ℕ)





end VWZClique.Quotient

end

/- IntegerFoldEvaluation -/
section

open VWZClique 
namespace VWZClique.UniformFolds







/-- Compute the projected summand with integer matrix products and signed
exact division. -/
noncomputable def integerTrace (K L : ℕ) (H : SimpleGraph V) (π : Equiv.Perm V)
    (w : WeightKey (2^L) → ℚ) : ℤ :=
  let q := windowExpansion K L
  let u := (Round.mk H π (none : Option (Mask L)) none).inputs w
  Quotient.signed (TraceDyadic.numerator q.labels q.labels K K u) ((2^L)^2)







end VWZClique.UniformFolds

end

/- NativeFoldTraversal -/
section

namespace VWZClique.NativeTraversal
open UniformFolds IntegerRAM IntegerRAM.Structured

/-- Indices are ordered by the actual retained base-five codes. -/
noncomputable def indexOrder (K L : ℕ) : Fin (Fintype.card (windowExpansion K L).Index) ≃
    (windowExpansion K L).Index :=
  let s := RankSwap.MaskEnumeration.allowed L (width K L)
  let e : (windowExpansion K L).Index ≃ ↥s := RankSwap.MaskEnumeration.enumerate L (width K L)
  (finCongr (by simpa only [Fintype.card_coe] using Fintype.card_congr e)).trans
    ((s.orderIsoOfFin rfl).toEquiv.trans e.symm)

def phaseIndex (I : Type) : Branch → Type
  | .left | .right => I
  | .both => I × I


structure Call (L : ℕ) where
  a : Option (Mask L)
  b : Option (Mask L)
  coeff : ℤ

def callSpec {L : ℕ} (q : Expansion L) : (d : Branch) → phaseIndex q.Index d → Call L
  | .left,i => ⟨some (q.masks i),none,q.coefficients i⟩
  | .right,i => ⟨none,some (q.masks i),q.coefficients i⟩
  | .both,(i,j) => ⟨some (q.masks i),some (q.masks j),-(q.coefficients i*q.coefficients j)⟩

noncomputable def qOf (H : SimpleGraph V) (L : ℕ) := windowExpansion (windowAt (Nat.card H.edgeSet)) L

def visits (m : ℕ) : Branch → ℕ
  | .left | .right => m
  | .both => m*m

noncomputable def phaseOrder {L : ℕ} (H : SimpleGraph V) (d : Branch) :
    Fin (visits (Fintype.card (qOf H L).Index) d) ≃ phaseIndex (qOf H L).Index d := by
  let e := indexOrder (windowAt (Nat.card H.edgeSet)) L
  cases d with
  | left => exact e
  | right => exact e
  | both => exact finProdFinEquiv.symm.trans (e.prodCongr e)

noncomputable def numbered {L : ℕ} (H : SimpleGraph V) (d : Branch)
    (i : Fin (visits (Fintype.card (qOf H L).Index) d)) : Call L :=
  callSpec _ d (phaseOrder H d i)




/-- One stack slot of the shared physical calling convention. A suspended parent
retains its table, cursor, and running sum while its child uses its own workspace. -/
inductive Slot (L : ℕ) where
  | input (depth : ℕ) (w : WeightKey (2^L) → ℚ)
  | value (depth : ℕ) (z : ℤ)
  | cursor (depth : ℕ) (H : SimpleGraph V) (π : Equiv.Perm V) (d : Branch) (w : WeightKey (2^L) → ℚ) (i : ℕ) (z : ℤ)




/-- A bounded run between two abstract machine states. -/
def Transition {L} (W : ℕ) (repr : List (Slot L) → Memory → Prop) (c : Command)
    (src dst : List (Slot L)) (limit : ℕ) : Prop :=
  ∀ m, repr src m → ∃ fuel ≤ limit, ∃ out, Runs W c m fuel out ∧ repr dst out



end VWZClique.NativeTraversal

end

/- NativeFoldProgram -/
section

namespace VWZClique.NativeTraversal
open UniformFolds IntegerRAM IntegerRAM.Structured
open WeightedProof


noncomputable def number (L : ℕ) (H : SimpleGraph V) := Fintype.card (qOf H L).Index






end VWZClique.NativeTraversal

end

/- WordGraphTable -/
section

/-! A native tabulator, on the graph alone, for every blocked zero-one weight.
It writes its 9N+81N² results immediately after the adjacency input. -/

namespace VWZClique.IntegerRAM.Graph.Table
open Structured 
open TrulySubcubicAPSP

/-- The first output word has index zero. Pair labels are row-major, with the
group pair preceding the packed-vertex pair. -/
def wordIndex {N : ℕ} : WeightKey N → ℕ
  | .inl (i,x) => i.val*N+x.val
  | .inr (i,j,x,y) => 9*N+(i.val*9+j.val)*(N*N)+x.val*N+y.val






end VWZClique.IntegerRAM.Graph.Table

end

/- NativeFrameStack -/
section

namespace VWZClique.IntegerRAM.NativeFrame
open Structured UniformFolds NativeTraversal

def lengthField : Branch → Field
  | .left => .leftLength | .right => .rightLength | .both => .bothLength

/-- Frame headers occupy positive cells 1 through 296. The larger positive
cells starting at 512 hold the weight arrays and projection metadata.
Cells 320 and 321 store the dyadic length and output address. The
fixed pointer block in cells 400 through 511 is available to the kernels. -/
structure StackLayout where
  outputAddress : ℕ
  base : ℕ → ℕ
  large : ∀ d, 512 ≤ base d
  prepared : ℕ → SimpleGraph V → Memory → Prop
  transfer : ∀ d H m o, (∀ a : ℕ, base d ≤ a → a < base (d+1) → o a=m a) → prepared d H m → prepared d H o


def Weights {L : ℕ} (lay : StackLayout) (depth : ℕ) (w : WeightKey (2^L) → ℚ) (m : Memory) :=
  m (reg depth .weights)=lay.base depth ∧
  ∀ a, (m ((lay.base depth+Graph.Table.wordIndex a:ℕ):ℤ):ℚ) = w a

def depthOf {L} : NativeTraversal.Slot L → ℕ
  | .input d _ | .value d _ | .cursor d _ _ _ _ _ _ => d

def Valid {L} (lay : StackLayout) : NativeTraversal.Slot L → Memory → Prop
  | .input d w,m => Weights lay d w m
  | .value d z,m => m (reg d .value)=z
  | .cursor d H _ _ w i z,m =>
    Weights lay d w m ∧ lay.prepared d H m ∧
    (∀ b, m (reg d (lengthField b))=visits (number L H) b) ∧
    m (reg d .index)=i ∧ m (reg d .value)=z

/-- push writes the multiplier before suspending its parent. -/
def Armed {L} : NativeTraversal.Slot L → Memory → Prop
  | .cursor d H _ b _ i _,m => ∃ h : i<visits (number L H) b,
      m (reg d .coefficient) = (numbered H b (⟨i,h⟩ : Fin (visits (number L H) b))).coeff
  | _,_ => False

def Saved {L} (lay : StackLayout) : ℕ → List (NativeTraversal.Slot L) → Memory → Prop
  | _,[],_ => True
  | d,s::q,m => depthOf s < d ∧ Valid lay s m ∧ Armed s m ∧ Saved lay (depthOf s) q m

/-- Caller-owned globals survive every branch and the whole compiled recursion. -/
structure Globals (L : ℕ) (lay : StackLayout) (m : Memory) : Prop where
  dim : m 0=((2^L:ℕ):ℤ)
  length : m 320=(L:ℤ)
  output : m 321=(lay.outputAddress:ℤ)


def Repr {L} (lay : StackLayout) (q : List (NativeTraversal.Slot L)) (m : Memory) : Prop :=
  Globals L lay m ∧ match q with
  | [] => True
  | s::anc => Valid lay s m ∧ Saved lay (depthOf s) anc m

















end VWZClique.IntegerRAM.NativeFrame

end

/- NativeArena -/
section

namespace VWZClique.IntegerRAM.NativeArena
open Structured  NativeFrame

def tableWords (n : ℕ) := 9*n+81*(n*n)
def metaBase (base n : ℕ) := base+tableWords n
def maps (base n : ℕ) := metaBase base n+7*n^3+2
def rows (base n : ℕ) := maps base n+22*n
def child (base n : ℕ) := rows base n+4*n












end VWZClique.IntegerRAM.NativeArena

end

/- NativeWidth -/
section

namespace VWZClique.IntegerRAM.NativeArena
open  WeightedProof

/-- The recursive frames have stride independent of the pattern and depth.
Each frame preserves its ancestors by leaving their whole interval untouched. -/
def atDepth (root n : ℕ) : ℕ → ℕ
  | 0 => root
  | d+1 => child (atDepth root n d) n


theorem atDepth_increasing (root n : ℕ) : StrictMono (atDepth root n) := by
  apply strictMono_nat_of_lt_succ
  intro d
  change atDepth root n d < child (atDepth root n d) n
  dsimp only [child,rows,maps,metaBase]
  omega



end VWZClique.IntegerRAM.NativeArena

end

/- NativeArenaLayout -/
section

namespace VWZClique.IntegerRAM.NativeArena
open NativeFrame NativeTraversal UniformFolds  MaskScan.Arena

theorem maps_eq (base N : ℕ) : maps base N=MaskScan.Arena.slot base N 7+2 := by
  dsimp [maps,metaBase,tableWords,MaskScan.Arena.slot,MaskScan.Arena.origin,span]
  ring

noncomputable def layout (L root output : ℕ) (start : 512≤root) : StackLayout where
  outputAddress := output
  base := atDepth root (2^L)
  large d := start.trans ((atDepth_increasing root (2^L)).monotone (Nat.zero_le d))
  prepared d H := Prepared L (windowAt (Nat.card H.edgeSet)) (atDepth root (2^L) d)
  transfer d H m o eq old := by
    apply old.congr
    intro z lo hi
    apply eq z lo
    change z<child (atDepth root (2^L) d) (2^L)
    rw [←maps_eq] at hi
    unfold child rows
    omega



end VWZClique.IntegerRAM.NativeArena

end

/- NativeFoldTime -/
section

namespace VWZClique.NativeTraversal
open UniformFolds
open OAI.MatrixMultiplication.Arithmetic


noncomputable def projected (mm : ℕ → ℕ) (T U L : ℕ) (H : SimpleGraph V) :=
  projectionWork mm T (tileAt (Nat.card H.edgeSet)) L (qOf H L).labels.card + U*(2^L)^5


end VWZClique.NativeTraversal

end

/- NativeEndgame -/
section

namespace VWZClique.IntegerRAM.NativeArena
open Structured UniformFolds NativeTraversal NativeFrame 
open OAI.MatrixMultiplication.Arithmetic

/-- Fixed projected-contraction bytecode, including setup of the parent's compact metadata.
The domain dimension is read from memory. -/
structure ProjectionKernel (mm : ℕ→ℕ) (T : ℕ) where
  command : ℕ → SimpleGraph V → Equiv.Perm V → Command
  workspaceCoefficient : ℕ
  workspacePower : ℕ
  timeCoefficient : ℕ
  logPower : ℕ
  run : ∀ {W L root output d : ℕ} (large : 512≤root) (hL : 0<L) (H : SimpleGraph V) (π : Equiv.Perm V)
      (w : WeightKey (2^L) → ℚ) (q : List (NativeTraversal.Slot L)), d+Nat.card H.edgeSet≤36 →
    (∀ i, Binary (w i)) →
    Graph.Division.Room W (atDepth root (2^L) d+workspaceCoefficient*(2^L)^workspacePower) →
    let lay := layout L root output large
    Transition W (Repr lay) (command d H π) (.input d w::q)
      (.cursor d H π .left w 0 (integerTrace (windowAt (Nat.card H.edgeSet)) L H π w)::q)
      (timeCoefficient*(L+1)^logPower*(NativeTraversal.projected mm T 1 L H+1))



end VWZClique.IntegerRAM.NativeArena

end


