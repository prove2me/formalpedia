-- Prove2me | Definitions.Def_OAI_QuantumFactoring_Part09
-- name    : OAI_QuantumFactoring_Part09
-- status  : Definition
-- author  : @SamenHossain
-- created : 2026-10-12T07:17:06.332982+00:00
-- url     : https://prove2.me/theorems/c1848a9c-5d1e-4633-ade8-d1872130823c
-- title:
--   Exact quantum factoring, part 9 of 38 (port of OpenAI's formalization)
-- statement:
--   Part 9 of 38 of a port of OpenAI's Lean formalization of the manuscript *Exact quantum factoring over a fixed finite gate set* (OpenAI, September 25, 2026). This part contains the modules `RetentionDenominators`, `NaturalExpressions`, `IntegerExpressions`, `RationalExpressions`, `RationalRounding`, `PolynomialExpressions`, `FilterExpressionSyntax`, `ThresholdRetention`, `FairLabelMass`, `TrialRetentionBounds`, `TrialGuessLaw`, `OrderTrialLaw`, `OrderSamplerMass`, `TrialRawPreparation`, `TensorPreparation`.
--
--   **Attribution.** The code is adapted from the OpenAI "math" repository, commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, directory `lean/OAI/Computability/QuantumFactoring`. It is © OpenAI and licensed under the Apache License 2.0; the adapted code is redistributed under the same license.
--
--   **Modifications.** Modules are concatenated in dependency order, with their imports replaced by the previous part. The model definitions come from the platform definition `ExactQuantumFactoring`, which is identical to upstream `Basic.lean`.
--
--   The development is split into 38 parts only so that each compiles within the platform's time limit. Together the parts supply the circuit family `PhysicalTree.finalCircuit` and its specification, used to prove `OAI.ExactQuantumFactoring.zero_amplitude_core`.
-- source:
--   OpenAI, openai/math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, lean/OAI/Computability/QuantumFactoring: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/RetentionDenominators.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/NaturalExpressions.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/IntegerExpressions.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/RationalExpressions.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/RationalRounding.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/PolynomialExpressions.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/FilterExpressionSyntax.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/ThresholdRetention.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/FairLabelMass.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/TrialRetentionBounds.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/TrialGuessLaw.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/OrderTrialLaw.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/OrderSamplerMass.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/TrialRawPreparation.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/TensorPreparation.lean (Apache License 2.0); manuscript https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Exact-quantum-factoring-over-a-fixed-finite-gate-set-September-25-2026/main.pdf

/-
Exact quantum factoring development (port of OpenAI's formalization), part 9 of 38.

Adapted from the OpenAI "math" repository (https://github.com/openai/math, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a), lean/OAI/Computability/QuantumFactoring/: RetentionDenominators.lean, NaturalExpressions.lean, IntegerExpressions.lean, RationalExpressions.lean, RationalRounding.lean, PolynomialExpressions.lean, FilterExpressionSyntax.lean, ThresholdRetention.lean, FairLabelMass.lean, TrialRetentionBounds.lean, TrialGuessLaw.lean, OrderTrialLaw.lean, OrderSamplerMass.lean, TrialRawPreparation.lean, TensorPreparation.lean
These files formalize the manuscript "Exact quantum factoring over a fixed finite gate set"
(OpenAI, September 25, 2026). Copyright OpenAI. Licensed under the Apache License, Version 2.0
(http://www.apache.org/licenses/LICENSE-2.0); the adapted code is distributed under the same license,
on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND.

Modifications: modules concatenated in dependency order with their import lines removed; the model
definitions (Basic.lean) come from the platform definition `ExactQuantumFactoring`, to which upstream
Basic.lean is identical; the final assembly (Main.lean) is omitted.
-/
import Mathlib
import Definitions.Def_OAI_QuantumFactoring_Part08

set_option autoImplicit false

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/RetentionDenominators.lean =====
namespace OAI

section
open scoped BigOperators


/-! Explicit, uniform O(n) fair-bit lengths for every order-trial retention.
Mere dyadicity would not bound the worst-case circuit cost. -/
namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators

def DyadicAt (k : ℕ) (x : ℚ) : Prop := ∃ z : ℤ, x=(z:ℚ)/2^k
namespace DyadicAt
lemma integer (k : ℕ) (z : ℤ) : DyadicAt k (z:ℚ) := by
  refine ⟨z*2^k,?_⟩
  push_cast
  field_simp
lemma mono {k l : ℕ} {x : ℚ} (h : DyadicAt k x) (hkl : k≤l) : DyadicAt l x := by
  obtain ⟨z,rfl⟩ := h
  obtain ⟨c,rfl⟩ := Nat.exists_eq_add_of_le hkl
  refine ⟨z*2^c,?_⟩
  push_cast
  rw [pow_add]
  field_simp
lemma add {k : ℕ} {x y : ℚ} (hx : DyadicAt k x) (hy : DyadicAt k y) : DyadicAt k (x+y) := by
  obtain ⟨a,rfl⟩ := hx
  obtain ⟨b,rfl⟩ := hy
  exact ⟨a+b,by push_cast; ring⟩
lemma sub {k : ℕ} {x y : ℚ} (hx : DyadicAt k x) (hy : DyadicAt k y) : DyadicAt k (x-y) := by
  obtain ⟨a,rfl⟩ := hx
  obtain ⟨b,rfl⟩ := hy
  exact ⟨a-b,by push_cast; ring⟩
lemma mul {k l : ℕ} {x y : ℚ} (hx : DyadicAt k x) (hy : DyadicAt l y) : DyadicAt (k+l) (x*y) := by
  obtain ⟨a,rfl⟩ := hx
  obtain ⟨b,rfl⟩ := hy
  refine ⟨a*b,?_⟩
  push_cast
  rw [pow_add]
  ring
lemma int_mul {k : ℕ} {x : ℚ} (z : ℤ) (hx : DyadicAt k x) : DyadicAt k ((z:ℚ)*x) := by
  obtain ⟨a,rfl⟩ := hx
  exact ⟨z*a,by push_cast; ring⟩
end DyadicAt

lemma majorant_at (n d j u : ℕ) : DyadicAt (24*n) (majorant ((2^n)^16) (2^n) d j u) := by
  refine ⟨majorantNumerator ((2^n)^16) (2^n) d j u,?_⟩
  rw [majorant_numerator (by positivity) (by positivity)]
  congr 1
  push_cast
  rw [← pow_mul,← pow_mul,← pow_add]
  congr 1
  omega
lemma majorantSum_at (n d j : ℕ) : DyadicAt (24*n+1) (majorantSum ((2^n)^16) (2^n) d j) := by
  refine ⟨∑ u ∈ Finset.range d, majorantNumerator ((2^n)^16) (2^n) d j u,?_⟩
  rw [majorantSum_numerator (by positivity) (by positivity)]
  congr 1
  push_cast
  rw [← pow_mul,← pow_mul,← pow_add,pow_succ]
  ring_nf
lemma probability_at (n d j t : ℕ) : DyadicAt (64*n) (residueProbabilityRat ((2^n)^16) d j t) := by
  refine ⟨(residueGaussianNumerator ((2^n)^16) d j t).norm,?_⟩
  rw [residueProbabilityRat]
  congr 1
  push_cast
  rw [← pow_mul,← pow_mul]
  congr 1
  omega
lemma coefficient_at (n : ℕ) (lam S : ℚ) : DyadicAt (10*n) (modeCoeff n lam S) := ⟨_,rfl⟩
lemma lambda_at {n d : ℕ} (hd : d≤2^n) : DyadicAt (n+10) (prescribedMass d) := by
  have h : DyadicAt (Nat.clog 2 d+10) (prescribedMass d) := ⟨1,by simp [prescribedMass]⟩
  exact h.mono (Nat.add_le_add_right (Nat.clog_le_of_le_pow hd) 10)
lemma remainder_at {n d : ℕ} (hn : 1≤n) (hd : d≤2^n) (j : ℕ) :
    DyadicAt (34*n+1) (modeRemainder n (prescribedMass d) (majorantSum ((2^n)^16) (2^n) d j)) := by
  unfold modeRemainder
  apply DyadicAt.sub
  · exact (lambda_at hd).mono (by omega)
  · have h := (coefficient_at n (prescribedMass d) (majorantSum ((2^n)^16) (2^n) d j)).mul
      (majorantSum_at n d j)
    convert h using 1; omega

noncomputable def discrepancyRetention (n d j t : ℕ) : ℚ :=
  2*((2:ℚ)^n)^3*(majorant ((2^n)^16) (2^n) d j ((j*t)%d)-
    residueProbabilityRat ((2^n)^16) d j t)*modeCoeff n (prescribedMass d) (majorantSum ((2^n)^16) (2^n) d j)
noncomputable def remainderRetention (n d j : ℕ) : ℚ :=
  4*((2:ℚ)^n)^2*modeRemainder n (prescribedMass d) (majorantSum ((2^n)^16) (2^n) d j)

lemma discrepancy_at (n d j t : ℕ) : DyadicAt (74*n) (discrepancyRetention n d j t) := by
  have h := ((majorant_at n d j ((j*t)%d)).mono (show 24*n≤64*n by omega)).sub (probability_at n d j t)
  have h' := (h.int_mul (2*(2^n)^3)).mul
    (coefficient_at n (prescribedMass d) (majorantSum ((2^n)^16) (2^n) d j))
  push_cast at h'
  convert h' using 1 <;> first | rfl | omega
lemma remainderRetention_at {n d : ℕ} (hn : 1≤n) (hd : d≤2^n) (j : ℕ) :
    DyadicAt (34*n+1) (remainderRetention n d j) := by
  have h := (remainder_at hn hd j).int_mul (4*(2^n)^2)
  simpa only [Int.cast_mul,Int.cast_ofNat,Int.cast_pow,remainderRetention] using h

/-- One clock-independent number of bits works for all three modes, on every
valid label, including d=1,j=0. -/
def retentionBits (n : ℕ) := 80*n+20
lemma retentions_fixedDenominator {n d : ℕ} (hn : 1≤n) (hd : d≤2^n) (j t : ℕ) :
    DyadicAt (retentionBits n) (modeCoeff n (prescribedMass d) (majorantSum ((2^n)^16) (2^n) d j)) ∧
    DyadicAt (retentionBits n) (discrepancyRetention n d j t) ∧
    DyadicAt (retentionBits n) (remainderRetention n d j) := by
  exact ⟨(coefficient_at n _ _).mono (by unfold retentionBits; omega),
    (discrepancy_at n d j t).mono (by unfold retentionBits; omega),
    (remainderRetention_at hn hd j).mono (by unfold retentionBits; omega)⟩

lemma retained_numerator {T : ℕ} {x : ℚ} (hx : DyadicAt T x) (h₀ : 0≤x) (h₁ : x≤1) :
    ∃ z : ℕ, z≤2^T ∧ x=(z:ℚ)/2^T ∧ (Int.floor (x*2^T)).toNat=z := by
  obtain ⟨a,ha⟩ := hx
  have hp : (0:ℚ)<2^T := by positivity
  have ha₀ : 0≤a := by
    rw [ha,div_nonneg_iff] at h₀
    rcases h₀ with h | h
    · exact_mod_cast h.1
    · exact False.elim ((not_le_of_gt hp) h.2)
  have ha₁ : a≤(2:ℤ)^T := by
    rw [ha,div_le_one hp] at h₁
    exact_mod_cast h₁
  refine ⟨a.toNat,?_,?_,?_⟩
  · simpa using Int.toNat_le_toNat ha₁
  · have he : (a.toNat:ℚ)=(a:ℚ) := by exact_mod_cast (Int.toNat_of_nonneg ha₀)
    rw [he]; exact ha
  · rw [ha,div_mul_cancel₀ _ hp.ne',Int.floor_intCast]

end ExactQuantumFactoring.OrderTrial


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NaturalExpressions.lean =====
namespace OAI

section
open scoped BigOperators


/-! A finite straight-line expression language for the exact rational formulas
in the manuscript. All values are natural numbers, not unit-cost hidden gates.
The following compiler will realize these operations with actual bit networks. -/
namespace ExactQuantumFactoring

inductive NatExpr (v : Type*) where
  | var : v → NatExpr v
  | const : ℕ → NatExpr v
  | add : NatExpr v → NatExpr v → NatExpr v
  | mul : NatExpr v → NatExpr v → NatExpr v
  | sub : NatExpr v → NatExpr v → NatExpr v
  | div : NatExpr v → NatExpr v → NatExpr v
  | mod : NatExpr v → NatExpr v → NatExpr v
  | iteLe : NatExpr v → NatExpr v → NatExpr v → NatExpr v → NatExpr v
  deriving Inhabited

namespace NatExpr
variable {v : Type*}

def eval (x : v → ℕ) : NatExpr v → ℕ
  | .var i => x i
  | .const c => c
  | .add a b => eval x a+eval x b
  | .mul a b => eval x a*eval x b
  | .sub a b => eval x a-eval x b
  | .div a b => eval x a/eval x b
  | .mod a b => eval x a%eval x b
  | .iteLe a b c d => if eval x a ≤ eval x b then eval x c else eval x d

def size : NatExpr v → ℕ
  | .var _ | .const _ => 1
  | .add a b | .mul a b | .sub a b | .div a b | .mod a b => size a+size b+1
  | .iteLe a b c d => size a+size b+size c+size d+1

def constOK (B : ℕ) : NatExpr v → Prop
  | .var _ => True
  | .const c => c < B
  | .add a b | .mul a b | .sub a b | .div a b | .mod a b => constOK B a ∧ constOK B b
  | .iteLe a b c d => constOK B a ∧ constOK B b ∧ constOK B c ∧ constOK B d

lemma size_pos (e : NatExpr v) : 0 < e.size := by cases e <;> simp [size]

lemma value_bound (B : ℕ) (hB : 2 ≤ B) (x : v → ℕ) (hx : ∀ i, x i < B)
    (e : NatExpr v) (hc : e.constOK B) : e.eval x < B^e.size := by
  induction e with
  | var i => simpa [eval,size] using hx i
  | const c => simpa [eval,size,constOK] using hc
  | add a b ia ib =>
    have ha := ia hc.1
    have hb := ib hc.2
    have h₁ : a.eval x+b.eval x+1 ≤ (a.eval x+1)*(b.eval x+1) := by nlinarith
    have h₂ := Nat.mul_le_mul (Nat.succ_le_of_lt ha) (Nat.succ_le_of_lt hb)
    have h₃ : B^(a.size+b.size) ≤ B^(a.size+b.size+1) := Nat.pow_le_pow_right (by omega) (by omega)
    simp only [eval,size]
    rw [← pow_add] at h₂
    simp only [Nat.succ_eq_add_one] at h₂
    omega
  | mul a b ia ib =>
    have ha := ia hc.1
    have hb := ib hc.2
    have h₁ : a.eval x*b.eval x+1 ≤ (a.eval x+1)*(b.eval x+1) := by nlinarith
    have h₂ := Nat.mul_le_mul (Nat.succ_le_of_lt ha) (Nat.succ_le_of_lt hb)
    have h₃ : B^(a.size+b.size) ≤ B^(a.size+b.size+1) := Nat.pow_le_pow_right (by omega) (by omega)
    simp only [eval,size]
    rw [← pow_add] at h₂
    simp only [Nat.succ_eq_add_one] at h₂
    omega
  | sub a b ia _ =>
    exact (Nat.sub_le _ _).trans_lt ((ia hc.1).trans_le
      (Nat.pow_le_pow_right (by omega) (by simp [size]; omega)))
  | div a b ia _ =>
    exact (Nat.div_le_self _ _).trans_lt ((ia hc.1).trans_le
      (Nat.pow_le_pow_right (by omega) (by simp [size]; omega)))
  | mod a b ia _ =>
    exact (Nat.mod_le _ _).trans_lt ((ia hc.1).trans_le
      (Nat.pow_le_pow_right (by omega) (by simp [size]; omega)))
  | iteLe a b c d _ _ ic id =>
    simp only [eval]
    split_ifs
    · exact (ic hc.2.2.1).trans_le (Nat.pow_le_pow_right (by omega) (by simp [size]; omega))
    · exact (id hc.2.2.2).trans_le (Nat.pow_le_pow_right (by omega) (by simp [size]; omega))

/-- Every intermediate value fits, not merely the eventual answer. -/
def Fits (B : ℕ) (x : v → ℕ) (e : NatExpr v) : Prop :=
  e.eval x < B ∧ match e with
    | .var _ | .const _ => True
    | .add a b | .mul a b | .sub a b | .div a b | .mod a b => Fits B x a ∧ Fits B x b
    | .iteLe a b c d => Fits B x a ∧ Fits B x b ∧ Fits B x c ∧ Fits B x d

lemma Fits.mono {B C : ℕ} (hBC : B ≤ C) {x : v → ℕ} {e : NatExpr v}
    (h : Fits B x e) : Fits C x e := by
  induction e with
  | var _ | const _ => exact ⟨h.1.trans_le hBC,trivial⟩
  | add a b ia ib | mul a b ia ib | sub a b ia ib | div a b ia ib | mod a b ia ib =>
    exact ⟨h.1.trans_le hBC,ia h.2.1,ib h.2.2⟩
  | iteLe a b c d ia ib ic id =>
    exact ⟨h.1.trans_le hBC,ia h.2.1,ib h.2.2.1,ic h.2.2.2.1,id h.2.2.2.2⟩

lemma fits_bound (B : ℕ) (hB : 2 ≤ B) (x : v → ℕ) (hx : ∀ i, x i < B)
    (e : NatExpr v) (hc : e.constOK B) : Fits (B^e.size) x e := by
  induction e with
  | var i | const i => exact ⟨value_bound B hB x hx _ hc,trivial⟩
  | add a b ia ib | mul a b ia ib | sub a b ia ib | div a b ia ib | mod a b ia ib =>
    refine ⟨value_bound B hB x hx _ hc,?_,?_⟩
    · exact (ia hc.1).mono (Nat.pow_le_pow_right (by omega) (by simp [size]; omega))
    · exact (ib hc.2).mono (Nat.pow_le_pow_right (by omega) (by simp [size]; omega))
  | iteLe a b c d ia ib ic id =>
    refine ⟨value_bound B hB x hx _ hc,?_,?_,?_,?_⟩
    · exact (ia hc.1).mono (Nat.pow_le_pow_right (by omega) (by simp [size]; omega))
    · exact (ib hc.2.1).mono (Nat.pow_le_pow_right (by omega) (by simp [size]; omega))
    · exact (ic hc.2.2.1).mono (Nat.pow_le_pow_right (by omega) (by simp [size]; omega))
    · exact (id hc.2.2.2).mono (Nat.pow_le_pow_right (by omega) (by simp [size]; omega))

lemma fits_bits {b : ℕ} (hb : 1 ≤ b) (x : v → ℕ) (hx : ∀ i, x i < 2^b)
    (e : NatExpr v) (hc : e.constOK (2^b)) : Fits (2^(b*e.size)) x e := by
  rw [pow_mul]
  exact fits_bound (2^b) (Nat.one_lt_two_pow (by omega)) x hx e hc

end NatExpr
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/IntegerExpressions.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring

/-- Balanced integers avoid a word-size-dependent signed representation. -/
structure IntExpr (v : Type*) where
  pos : NatExpr v
  neg : NatExpr v

namespace IntExpr
variable {v : Type*}

def eval (x : v → ℕ) (e : IntExpr v) : ℤ := (e.pos.eval x : ℤ)-e.neg.eval x

def ofNat (e : NatExpr v) : IntExpr v := ⟨e,.const 0⟩
def ofInt (z : ℤ) : IntExpr v := ⟨.const z.toNat,.const (-z).toNat⟩
def add (a b : IntExpr v) : IntExpr v := ⟨.add a.pos b.pos,.add a.neg b.neg⟩
def negation (a : IntExpr v) : IntExpr v := ⟨a.neg,a.pos⟩
def sub (a b : IntExpr v) : IntExpr v := add a (negation b)
def mul (a b : IntExpr v) : IntExpr v :=
  ⟨.add (.mul a.pos b.pos) (.mul a.neg b.neg),
   .add (.mul a.neg b.pos) (.mul a.pos b.neg)⟩
def scale (a : IntExpr v) (b : NatExpr v) : IntExpr v := mul a (ofNat b)
def toNat (a : IntExpr v) : NatExpr v := .sub a.pos a.neg
def natAbs (a : IntExpr v) : NatExpr v := .add (.sub a.pos a.neg) (.sub a.neg a.pos)
def iteLe (a b : NatExpr v) (c d : IntExpr v) : IntExpr v :=
  ⟨.iteLe a b c.pos d.pos,.iteLe a b c.neg d.neg⟩

@[simp] lemma eval_ofNat (x : v → ℕ) (e : NatExpr v) : (ofNat e).eval x=(e.eval x : ℤ) := by
  simp [ofNat,eval,NatExpr.eval]
@[simp] lemma eval_ofInt (x : v → ℕ) (z : ℤ) : (ofInt z : IntExpr v).eval x=z := by
  simp [ofInt,eval,NatExpr.eval]
@[simp] lemma eval_add (x : v → ℕ) (a b : IntExpr v) : (add a b).eval x=a.eval x+b.eval x := by
  simp [add,eval,NatExpr.eval]
  ring
@[simp] lemma eval_negation (x : v → ℕ) (a : IntExpr v) : (negation a).eval x= -a.eval x := by
  simp [negation,eval]
@[simp] lemma eval_sub (x : v → ℕ) (a b : IntExpr v) : (sub a b).eval x=a.eval x-b.eval x := by
  simp [sub,sub_eq_add_neg]
@[simp] lemma eval_mul (x : v → ℕ) (a b : IntExpr v) : (mul a b).eval x=a.eval x*b.eval x := by
  simp [mul,eval,NatExpr.eval]
  ring
@[simp] lemma eval_scale (x : v → ℕ) (a : IntExpr v) (b : NatExpr v) :
    (scale a b).eval x=a.eval x*b.eval x := by simp [scale]
@[simp] lemma eval_toNat (x : v → ℕ) (a : IntExpr v) : (toNat a).eval x=(a.eval x).toNat := by
  simp [toNat,NatExpr.eval,eval]
@[simp] lemma eval_natAbs (x : v → ℕ) (a : IntExpr v) : (natAbs a).eval x=(a.eval x).natAbs := by
  simp only [natAbs,NatExpr.eval,eval]
  omega
@[simp] lemma eval_iteLe (x : v → ℕ) (a b : NatExpr v) (c d : IntExpr v) :
    (iteLe a b c d).eval x = if a.eval x ≤ b.eval x then c.eval x else d.eval x := by
  simp only [iteLe,eval,NatExpr.eval]
  split_ifs <;> rfl

end IntExpr
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/RationalExpressions.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring

/-- Rational arithmetic as fixed finite syntax over nonnegative registers. No
canonical-fraction reduction or unit-cost large-integer operation is required. -/
structure RatExpr (v : Type*) where
  num : IntExpr v
  den : NatExpr v

namespace RatExpr
variable {v : Type*}

def eval (x : v → ℕ) (a : RatExpr v) : ℚ := (a.num.eval x : ℚ)/(a.den.eval x : ℚ)
def ofNat (a : NatExpr v) : RatExpr v := ⟨IntExpr.ofNat a,.const 1⟩
def ofInt (a : IntExpr v) : RatExpr v := ⟨a,.const 1⟩
def const (a : ℚ) : RatExpr v := ⟨IntExpr.ofInt a.num,.const a.den⟩
def normalize (a : RatExpr v) : RatExpr v :=
  ⟨IntExpr.iteLe a.den (.const 0) (IntExpr.ofInt 0) a.num,
   .iteLe a.den (.const 0) (.const 1) a.den⟩
def add (a b : RatExpr v) : RatExpr v :=
  let a := normalize a
  let b := normalize b
  ⟨IntExpr.add (a.num.scale b.den) (b.num.scale a.den),.mul a.den b.den⟩
def negation (a : RatExpr v) : RatExpr v := ⟨a.num.negation,a.den⟩
def sub (a b : RatExpr v) : RatExpr v := add a b.negation
def mul (a b : RatExpr v) : RatExpr v := ⟨a.num.mul b.num,.mul a.den b.den⟩
def inverse (a : RatExpr v) : RatExpr v :=
  ⟨a.num.scale a.den,.mul a.num.natAbs a.num.natAbs⟩
def div (a b : RatExpr v) : RatExpr v := mul a b.inverse
def pow (a : RatExpr v) : ℕ → RatExpr v
  | 0 => const 1
  | n+1 => mul (pow a n) a

@[simp] lemma eval_ofNat (x : v → ℕ) (a : NatExpr v) : (ofNat a).eval x=a.eval x := by
  simp [ofNat,eval,NatExpr.eval]
@[simp] lemma eval_ofInt (x : v → ℕ) (a : IntExpr v) : (ofInt a).eval x=a.eval x := by
  simp [ofInt,eval,NatExpr.eval]
@[simp] lemma eval_const (x : v → ℕ) (a : ℚ) : (const a : RatExpr v).eval x=a := by
  simp [const,eval,NatExpr.eval,Rat.num_div_den]
@[simp] lemma eval_normalize (x : v → ℕ) (a : RatExpr v) : a.normalize.eval x=a.eval x := by
  by_cases h : a.den.eval x=0
  · simp [normalize,eval,NatExpr.eval,h]
  · have hp : ¬a.den.eval x ≤ 0 := by omega
    simp [normalize,eval,NatExpr.eval,hp]
lemma normalize_den_pos (x : v → ℕ) (a : RatExpr v) : 0 < a.normalize.den.eval x := by
  change 0 < if a.den.eval x ≤ 0 then 1 else a.den.eval x
  split_ifs <;> omega
@[simp] lemma eval_add (x : v → ℕ) (a b : RatExpr v) : (add a b).eval x=a.eval x+b.eval x := by
  have ha : (a.normalize.den.eval x : ℚ) ≠ 0 := by exact_mod_cast (normalize_den_pos x a).ne'
  have hb : (b.normalize.den.eval x : ℚ) ≠ 0 := by exact_mod_cast (normalize_den_pos x b).ne'
  rw [← eval_normalize x a,← eval_normalize x b]
  simp only [add,eval,IntExpr.eval_add,IntExpr.eval_scale,NatExpr.eval,Int.cast_add,
    Int.cast_mul,Int.cast_natCast,Nat.cast_mul]
  field_simp
@[simp] lemma eval_negation (x : v → ℕ) (a : RatExpr v) : a.negation.eval x= -a.eval x := by
  simp [negation,eval,neg_div]
@[simp] lemma eval_sub (x : v → ℕ) (a b : RatExpr v) : (sub a b).eval x=a.eval x-b.eval x := by
  simp [sub,sub_eq_add_neg]
@[simp] lemma eval_mul (x : v → ℕ) (a b : RatExpr v) : (mul a b).eval x=a.eval x*b.eval x := by
  simp [mul,eval,NatExpr.eval,div_mul_div_comm]
@[simp] lemma eval_inverse (x : v → ℕ) (a : RatExpr v) : a.inverse.eval x=(a.eval x)⁻¹ := by
  simp only [inverse,eval,IntExpr.eval_scale,IntExpr.eval_natAbs,NatExpr.eval,
    Int.cast_mul,Int.cast_natCast,Nat.cast_mul,inv_div]
  have hsq : ((a.num.eval x).natAbs : ℚ)*((a.num.eval x).natAbs : ℚ) =
      (a.num.eval x : ℚ)*(a.num.eval x : ℚ) := by
    rw [← sq,← sq]
    have h : ((a.num.eval x).natAbs : ℤ)^2=(a.num.eval x)^2 := by
      rw [Int.natCast_natAbs,sq_abs]
    simpa only [Int.cast_pow,Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℚ)) h
  rw [hsq]
  by_cases hz : (a.num.eval x : ℚ)=0
  · simp [hz]
  · field_simp
@[simp] lemma eval_div (x : v → ℕ) (a b : RatExpr v) : (div a b).eval x=a.eval x/b.eval x := by
  simp [div,div_eq_mul_inv]
@[simp] lemma eval_pow (x : v → ℕ) (a : RatExpr v) (n : ℕ) : (pow a n).eval x=(a.eval x)^n := by
  induction n with
  | zero => simp [pow]
  | succ n ih => simp [pow,ih,pow_succ]

end RatExpr
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/RationalRounding.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
namespace IntExpr
variable {v : Type*}

def ceilRatioNat (a : IntExpr v) (b : NatExpr v) : NatExpr v :=
  .div (.sub (.add a.toNat b) (.const 1)) b

def floorRatio (a : IntExpr v) (b : NatExpr v) : IntExpr v :=
  sub (ofNat (.div a.toNat b)) (ofNat (ceilRatioNat a.negation b))

lemma ceil_ratio_nat (z : ℤ) (d : ℕ) :
    (Int.ceil ((z:ℚ)/d)).toNat=(z.toNat+d-1)/d := by
  by_cases hd : d=0
  · simp [hd]
  have hd' : (0:ℚ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
  apply eq_of_forall_ge_iff
  intro k
  rw [Int.toNat_le,Int.ceil_le,Int.cast_natCast,div_le_iff₀ hd',
    ← Nat.ceilDiv_eq_add_pred_div,ceilDiv_le_iff_le_mul (Nat.pos_of_ne_zero hd),
    Int.toNat_le]
  push_cast
  rw [mul_comm]
  norm_cast

@[simp] lemma eval_ceilRatioNat (x : v → ℕ) (a : IntExpr v) (b : NatExpr v) :
    (ceilRatioNat a b).eval x=(Int.ceil ((a.eval x:ℚ)/(b.eval x:ℚ))).toNat := by
  simp only [ceilRatioNat,NatExpr.eval,eval_toNat,ceil_ratio_nat]

@[simp] lemma eval_floorRatio (x : v → ℕ) (a : IntExpr v) (b : NatExpr v) :
    (floorRatio a b).eval x=Int.floor ((a.eval x:ℚ)/(b.eval x:ℚ)) := by
  simp only [floorRatio,eval_sub,eval_ofNat,NatExpr.eval,eval_toNat,eval_ceilRatioNat,
    eval_negation]
  by_cases hz : 0 ≤ a.eval x
  · have hc : Int.ceil (((-a.eval x:ℤ):ℚ)/(b.eval x:ℚ)) ≤ 0 := by
      rw [Int.ceil_le,Int.cast_zero]
      exact div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast neg_nonpos.mpr hz) (by positivity)
    rw [Int.toNat_of_nonpos hc,Int.natCast_zero,sub_zero]
    rw [Int.natCast_ediv,← Rat.floor_natCast_div_natCast]
    congr 2
    exact_mod_cast Int.toNat_of_nonneg hz
  · have hp : (a.eval x).toNat=0 := by omega
    rw [hp,Nat.zero_div,Int.natCast_zero,zero_sub]
    have hc : 0 ≤ Int.ceil (((-a.eval x:ℤ):ℚ)/(b.eval x:ℚ)) :=
      Int.ceil_nonneg (div_nonneg (by exact_mod_cast (show 0 ≤ -a.eval x by omega)) (by positivity))
    rw [Int.toNat_of_nonneg hc,Int.cast_neg,neg_div,Int.ceil_neg,neg_neg]

end IntExpr

namespace RatExpr
variable {v : Type*}
def ceilNat (a : RatExpr v) : NatExpr v := a.num.ceilRatioNat a.den
def floor (a : RatExpr v) : IntExpr v := a.num.floorRatio a.den
def ceil (a : RatExpr v) : IntExpr v := a.negation.floor.negation
@[simp] lemma eval_ceilNat (x : v → ℕ) (a : RatExpr v) :
    a.ceilNat.eval x=(Int.ceil (a.eval x)).toNat := by
  simp [ceilNat,eval]
@[simp] lemma eval_floor (x : v → ℕ) (a : RatExpr v) : a.floor.eval x=Int.floor (a.eval x) := by
  simp [floor,eval]
@[simp] lemma eval_ceil (x : v → ℕ) (a : RatExpr v) : a.ceil.eval x=Int.ceil (a.eval x) := by
  simp [ceil,Int.floor_neg]
end RatExpr
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/PolynomialExpressions.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
namespace RatExpr
variable {v : Type*}
def sum (f : ℕ → RatExpr v) : ℕ → RatExpr v
  | 0 => const 0
  | n+1 => add (sum f n) (f n)
@[simp] lemma eval_sum (x : v → ℕ) (f : ℕ → RatExpr v) (n : ℕ) :
    (sum f n).eval x=∑ i ∈ Finset.range n, (f i).eval x := by
  induction n with
  | zero => simp [sum]
  | succ n ih => simp [sum,ih,Finset.sum_range_succ]
end RatExpr

/-- Bounded polynomial arithmetic is itself finite rational syntax. -/
inductive PolyExpr (v : Type*) where
  | C : RatExpr v → PolyExpr v
  | X : PolyExpr v
  | add : PolyExpr v → PolyExpr v → PolyExpr v
  | negation : PolyExpr v → PolyExpr v
  | mul : PolyExpr v → PolyExpr v → PolyExpr v

namespace PolyExpr
variable {v : Type*}
open Polynomial
noncomputable def eval (x : v → ℕ) : PolyExpr v → ℚ[X]
  | .C c => Polynomial.C (c.eval x)
  | .X => Polynomial.X
  | .add a b => a.eval x+b.eval x
  | .negation a => -a.eval x
  | .mul a b => a.eval x*b.eval x

def coeff : PolyExpr v → ℕ → RatExpr v
  | .C c,k => if k=0 then c else RatExpr.const 0
  | .X,k => if k=1 then RatExpr.const 1 else RatExpr.const 0
  | .add a b,k => RatExpr.add (a.coeff k) (b.coeff k)
  | .negation a,k => (a.coeff k).negation
  | .mul a b,k => RatExpr.sum (fun i => RatExpr.mul (a.coeff i) (b.coeff (k-i))) (k+1)

lemma coeff_correct (x : v → ℕ) (p : PolyExpr v) (k : ℕ) :
    (p.coeff k).eval x=(p.eval x).coeff k := by
  induction p generalizing k with
  | C c =>
    by_cases h : k=0 <;> simp [coeff,eval,Polynomial.coeff_C,h]
  | X =>
    by_cases h : k=1 <;> simp [coeff,eval,Polynomial.coeff_X,h,eq_comm]
  | add a b ia ib => simp [coeff,eval,ia,ib]
  | negation a ia => simp [coeff,eval,ia]
  | mul a b ia ib =>
    simp only [coeff,RatExpr.eval_sum,RatExpr.eval_mul,ia,ib,eval,Polynomial.coeff_mul]
    exact (Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => (a.eval x).coeff i*(b.eval x).coeff j) k).symm

def sub (a b : PolyExpr v) : PolyExpr v := add a b.negation
def const (r : ℚ) : PolyExpr v := .C (RatExpr.const r)
def pow (a : PolyExpr v) : ℕ → PolyExpr v
  | 0 => const 1
  | n+1 => mul (pow a n) a

def comp : PolyExpr v → PolyExpr v → PolyExpr v
  | .C c,_ => .C c
  | .X,b => b
  | .add a c,b => .add (comp a b) (comp c b)
  | .negation a,b => .negation (comp a b)
  | .mul a c,b => .mul (comp a b) (comp c b)

@[simp] lemma eval_const (x : v → ℕ) (r : ℚ) : (const r : PolyExpr v).eval x=Polynomial.C r := by
  simp [const,eval]
@[simp] lemma eval_sub (x : v → ℕ) (a b : PolyExpr v) : (sub a b).eval x=a.eval x-b.eval x := by
  simp [sub,eval,sub_eq_add_neg]
@[simp] lemma eval_pow (x : v → ℕ) (a : PolyExpr v) (n : ℕ) : (pow a n).eval x=(a.eval x)^n := by
  induction n with
  | zero => simp [pow]
  | succ n ih => simp [pow,eval,ih,pow_succ]
@[simp] lemma eval_comp (x : v → ℕ) (a b : PolyExpr v) : (comp a b).eval x=(a.eval x).comp (b.eval x) := by
  induction a with
  | C c => simp [comp,eval]
  | X => simp [comp,eval]
  | add a c ia ic => simp [comp,eval,ia,ic,Polynomial.add_comp]
  | negation a ia => simp [comp,eval,ia,Polynomial.neg_comp]
  | mul a c ia ic => simp [comp,eval,ia,ic,Polynomial.mul_comp]
end PolyExpr
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/FilterExpressionSyntax.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
namespace RatExpr
variable {v : Type*}
instance (n : ℕ) : OfNat (RatExpr v) n := ⟨const n⟩
instance : Add (RatExpr v) := ⟨add⟩
instance : Mul (RatExpr v) := ⟨mul⟩
instance : Sub (RatExpr v) := ⟨sub⟩
instance : Div (RatExpr v) := ⟨div⟩
instance : Neg (RatExpr v) := ⟨negation⟩
instance : Inv (RatExpr v) := ⟨inverse⟩
instance : Pow (RatExpr v) ℕ := ⟨pow⟩
@[simp] lemma eval_num (x : v → ℕ) (n : ℕ) : (no_index (OfNat.ofNat n : RatExpr v)).eval x=n := eval_const x n
@[simp] lemma eval_plus (x : v → ℕ) (a b : RatExpr v) : (a+b).eval x=a.eval x+b.eval x := eval_add x a b
@[simp] lemma eval_times (x : v → ℕ) (a b : RatExpr v) : (a*b).eval x=a.eval x*b.eval x := eval_mul x a b
@[simp] lemma eval_minus (x : v → ℕ) (a b : RatExpr v) : (a-b).eval x=a.eval x-b.eval x := eval_sub x a b
@[simp] lemma eval_over (x : v → ℕ) (a b : RatExpr v) : (a/b).eval x=a.eval x/b.eval x := eval_div x a b
@[simp] lemma eval_neg (x : v → ℕ) (a : RatExpr v) : (-a).eval x= -a.eval x := eval_negation x a
@[simp] lemma eval_inv (x : v → ℕ) (a : RatExpr v) : (a⁻¹).eval x=(a.eval x)⁻¹ := eval_inverse x a
@[simp] lemma eval_power (x : v → ℕ) (a : RatExpr v) (n : ℕ) : (a^n).eval x=(a.eval x)^n := eval_pow x a n
end RatExpr
namespace PolyExpr
variable {v : Type*}
instance (n : ℕ) : OfNat (PolyExpr v) n := ⟨const n⟩
instance : Add (PolyExpr v) := ⟨add⟩
instance : Mul (PolyExpr v) := ⟨mul⟩
instance : Sub (PolyExpr v) := ⟨sub⟩
instance : Neg (PolyExpr v) := ⟨negation⟩
instance : Pow (PolyExpr v) ℕ := ⟨pow⟩
@[simp] lemma eval_num (x : v → ℕ) (n : ℕ) : (no_index (OfNat.ofNat n : PolyExpr v)).eval x=Polynomial.C (n : ℚ) := eval_const x n
@[simp] lemma eval_plus (x : v → ℕ) (a b : PolyExpr v) : (a+b).eval x=a.eval x+b.eval x := rfl
@[simp] lemma eval_times (x : v → ℕ) (a b : PolyExpr v) : (a*b).eval x=a.eval x*b.eval x := rfl
@[simp] lemma eval_minus (x : v → ℕ) (a b : PolyExpr v) : (a-b).eval x=a.eval x-b.eval x := eval_sub x a b
@[simp] lemma eval_neg (x : v → ℕ) (a : PolyExpr v) : (-a).eval x= -a.eval x := rfl
@[simp] lemma eval_power (x : v → ℕ) (a : PolyExpr v) (n : ℕ) : (a^n).eval x=(a.eval x)^n := eval_pow x a n
end PolyExpr
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/ThresholdRetention.lean =====
namespace OAI

section
open scoped BigOperators


/-! Exact threshold thinning by a FIXED (not rejection-sampled) block of fair
bits. The complete block is retained in the physical history. -/
namespace ExactQuantumFactoring
open scoped BigOperators
open Exactness BooleanNetwork BitArithmetic

def bitsNatEquiv (b : ℕ) : Basis b ≃ Fin (2^b) :=
  (bitsEquiv b).trans BitVec.equivFin.toEquiv

lemma bitsNatEquiv_val (b : ℕ) (x : Basis b) :
    (bitsNatEquiv b x).val=(bitsValue x).toNat := rfl

lemma fair_threshold_mass {b z : ℕ} (hz : z≤2^b) :
    outcomeMass (fun x : Basis b => (bitsValue x).toNat<z) (fairState b)=
      (z:ℝ)/2^b := by
  classical
  unfold outcomeMass
  simp only [fairState_mass]
  rw [Fintype.sum_equiv (bitsNatEquiv b)
    (fun x => if (bitsValue x).toNat<z then (2:ℝ)⁻¹^b else 0)
    (fun i => if i.val<z then (2:ℝ)⁻¹^b else 0) (fun _ => rfl)]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => if i<z then (2:ℝ)⁻¹^b else 0) (2^b)]
  have he : (∑ i ∈ Finset.range (2^b), if i<z then (2:ℝ)⁻¹^b else 0)=
      ∑ i ∈ Finset.range z, (2:ℝ)⁻¹^b := by
    rw [← Finset.sum_subset (Finset.range_mono hz)]
    · apply Finset.sum_congr rfl
      intro i hi
      rw [ite_eq_left (Finset.mem_range.mp hi)]
    · intro i _ hi
      rw [ite_eq_right (by simpa using hi)]
  rw [he]
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,inv_pow,div_eq_mul_inv]

/-- The natural floor implementation of the exact dyadic acceptance threshold. -/
def thresholdExpr {v : Type*} (T : ℕ) (p : RatExpr v) (coin : NatExpr v) : NatExpr v :=
  .iteLe (.add coin (.const 1)) ((p*RatExpr.ofNat (.const (2^T))).floor.toNat)
    (.const 1) (.const 0)

lemma thresholdExpr_eval {v : Type*} (x : v→ℕ) (T : ℕ) (p : RatExpr v) (coin : NatExpr v) :
    (thresholdExpr T p coin).eval x=1 ↔
      coin.eval x<(Int.floor (p.eval x*(2:ℚ)^T)).toNat := by
  simp only [thresholdExpr,NatExpr.eval,IntExpr.eval_toNat,RatExpr.eval_floor,RatExpr.eval_times,
    RatExpr.eval_ofNat,Nat.cast_pow,Nat.cast_ofNat]
  split_ifs with h
  · exact ⟨fun _ => Nat.lt_of_succ_le h,fun _ => rfl⟩
  · exact ⟨False.elim,fun hh => h (Nat.succ_le_of_lt hh)⟩

lemma dyadic_fair_threshold {b : ℕ} {p : ℚ} (h : OrderTrial.DyadicAt b p)
    (h₀ : 0≤p) (h₁ : p≤1) :
    outcomeMass (fun x : Basis b => (bitsValue x).toNat<(Int.floor (p*(2:ℚ)^b)).toNat)
      (fairState b)=(p:ℝ) := by
  obtain ⟨z,hz,hp,hfloor⟩ := OrderTrial.retained_numerator h h₀ h₁
  rw [hfloor,fair_threshold_mass hz,hp]
  push_cast
  rfl

end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/FairLabelMass.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open Exactness

lemma fair_value_mass {b k : ℕ} (hk : k<2^b) :
    outcomeMass (fun x : Basis b => (bitsValue x).toNat=k) (fairState b)=1/(2:ℝ)^b := by
  classical
  unfold outcomeMass
  simp only [fairState_mass]
  rw [Fintype.sum_equiv (bitsNatEquiv b)
    (fun x => if (bitsValue x).toNat=k then (2:ℝ)⁻¹^b else 0)
    (fun i => if i.val=k then (2:ℝ)⁻¹^b else 0) (fun _ => rfl)]
  have he : ∀ i : Fin (2^b), i.val=k ↔ i=⟨k,hk⟩ := by
    intro i
    exact ⟨fun h => Fin.ext h,fun h => congrArg Fin.val h⟩
  simp only [he,Finset.sum_ite_eq',Finset.mem_univ,ite_true,one_div,inv_pow]

lemma fair_fixed_append {b k : ℕ} {α : Type*} [Fintype α]
    (hk : k<2^b) (χ : α→ℂ) (P : ℕ→α→Prop) :
    outcomeMass (fun xu : Basis b × α => (bitsValue xu.1).toNat=k ∧ P (bitsValue xu.1).toNat xu.2)
      (independentState (fairState b) χ)= (1/(2:ℝ)^b)*outcomeMass (P k) χ := by
  have he : (fun xu : Basis b × α => (bitsValue xu.1).toNat=k ∧ P (bitsValue xu.1).toNat xu.2)=
      (fun xu => (bitsValue xu.1).toNat=k ∧ P k xu.2) := by
    funext xu
    apply propext
    constructor
    · rintro ⟨h,hp⟩; exact ⟨h,h ▸ hp⟩
    · rintro ⟨h,hp⟩; exact ⟨h,h.symm ▸ hp⟩
  rw [he,independent_mass (fairState b) χ (fun x => (bitsValue x).toNat=k) (P k),
    fair_value_mass hk]

lemma fair_variable_append {b d : ℕ} {α : Type*} [Fintype α]
    (hd : d≤2^b) (χ : α→ℂ) (P : ℕ→α→Prop) :
    outcomeMass (fun xu : Basis b × α => (bitsValue xu.1).toNat<d ∧ P (bitsValue xu.1).toNat xu.2)
      (independentState (fairState b) χ)=
      (1/(2:ℝ)^b)*∑ t ∈ Finset.range d, outcomeMass (P t) χ := by
  classical
  change outcomeMass (fun xu : Basis b × α => (bitsValue xu.1).toNat<d ∧ P (bitsValue xu.1).toNat xu.2)
    (RecordedHistory.appendState (fairState b) (fun _ => χ))=_
  rw [RecordedHistory.append_mass (fairState b) (fun _ => χ)
    (fun x => (bitsValue x).toNat<d) (fun x => P (bitsValue x).toNat)]
  simp only [fairState_mass]
  rw [Fintype.sum_equiv (bitsNatEquiv b)
    (fun x => if (bitsValue x).toNat<d then (2:ℝ)⁻¹^b*outcomeMass (P (bitsValue x).toNat) χ else 0)
    (fun i => if i.val<d then (2:ℝ)⁻¹^b*outcomeMass (P i.val) χ else 0) (fun _ => rfl)]
  rw [Fin.sum_univ_eq_sum_range
    (fun i : ℕ => if i<d then (2:ℝ)⁻¹^b*outcomeMass (P i) χ else 0) (2^b)]
  have he : (∑ i ∈ Finset.range (2^b), if i<d then (2:ℝ)⁻¹^b*outcomeMass (P i) χ else 0)=
      ∑ i ∈ Finset.range d, (2:ℝ)⁻¹^b*outcomeMass (P i) χ := by
    rw [← Finset.sum_subset (Finset.range_mono hd)]
    · apply Finset.sum_congr rfl
      intro i hi
      rw [ite_eq_left (Finset.mem_range.mp hi)]
    · intro i _ hi
      rw [ite_eq_right (by simpa using hi)]
  rw [he,← Finset.mul_sum]
  simp only [one_div,inv_pow]

lemma outcomeMass_disjoint_or {α : Type*} [Fintype α] (ψ : α→ℂ) (P R : α→Prop)
    (h : ∀ x, ¬(P x ∧ R x)) :
    outcomeMass (fun x => P x ∨ R x) ψ=outcomeMass P ψ+outcomeMass R ψ := by
  classical
  unfold outcomeMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hp : P x <;> by_cases hr : R x
  · exact False.elim (h x ⟨hp,hr⟩)
  all_goals simp [hp,hr]

end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/TrialRetentionBounds.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.OrderTrial

noncomputable def firstRetention (n d j : ℕ) : ℚ :=
  modeCoeff n (prescribedMass d) (majorantSum ((2^n)^16) (2^n) d j)

lemma first_remainder_bounds {n d : ℕ} (hn : 1≤n) (hd : 0<d) (hdB : d<2^n) (j : ℕ) :
    0≤firstRetention n d j ∧ firstRetention n d j≤1 ∧
      0≤ modeRemainder n (prescribedMass d) (majorantSum ((2^n)^16) (2^n) d j) ∧
      modeRemainder n (prescribedMass d) (majorantSum ((2^n)^16) (2^n) d j)≤2/(2:ℚ)^(10*n) := by
  have hB : 2≤2^n := by simpa using Nat.pow_le_pow_right (show 0<2 by decide) hn
  have hs := majorantSum_bounds hB hd hdB j
  have hsl : 1/(128*(d:ℚ))≤ majorantSum ((2^n)^16) (2^n) d j := by
    apply (Rat.cast_le (K:=ℝ)).mp
    simpa only [Rat.cast_div,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_natCast,Rat.cast_one] using hs.1
  have hsu : majorantSum ((2^n)^16) (2^n) d j≤2 := by exact_mod_cast hs.2
  have hc := modeCoeff_bounds n hd hsl hsu
  exact ⟨hc.1,by change modeCoeff n _ _≤1; linarith [hc.2.1],hc.2.2⟩

lemma all_retention_bounds {n d : ℕ} (hn : 1≤n) (hd : 0<d) (hdB : d<2^n) (j : ℕ)
    {t : ℕ} (ht : t<d) :
    (0≤firstRetention n d j ∧ firstRetention n d j≤1) ∧
      (0≤discrepancyRetention n d j t ∧ discrepancyRetention n d j t≤1) ∧
      (0≤remainderRetention n d j ∧ remainderRetention n d j≤1) := by
  have hc := first_remainder_bounds hn hd hdB j
  have hB : 2≤2^n := by simpa using Nat.pow_le_pow_right (show 0<2 by decide) hn
  have hc₀ : (0:ℝ)≤(firstRetention n d j:ℝ) := by exact_mod_cast hc.1
  have hc₁ : (firstRetention n d j:ℝ)≤1 := by exact_mod_cast hc.2.1
  have hdisc := discrepancy_retention_bounds hB hd hdB ht j hc₀ hc₁
  have hdc : (discrepancyRetention n d j t:ℝ)=
      2*((2^n:ℕ):ℝ)^3*((majorant ((2^n)^16) (2^n) d j ((j*t)%d):ℝ)-
        residueProbability ((2^n)^16) d j t)*(firstRetention n d j:ℝ) := by
    simp only [discrepancyRetention,firstRetention,Rat.cast_mul,Rat.cast_pow,Rat.cast_ofNat,
      Rat.cast_sub,residueProbabilityRat_cast (by positivity : 0<(2^n)^16),Nat.cast_pow,Nat.cast_ofNat]
  rw [← hdc] at hdisc
  have hr₀ : (0:ℝ)≤(modeRemainder n (prescribedMass d) (majorantSum ((2^n)^16) (2^n) d j):ℝ) := by
    exact_mod_cast hc.2.2.1
  have hr₁ : (modeRemainder n (prescribedMass d) (majorantSum ((2^n)^16) (2^n) d j):ℝ)≤
      2/(2:ℝ)^(10*n) := by
    have hh := (Rat.cast_le (K:=ℝ)).mpr hc.2.2.2
    simpa only [Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat] using hh
  have hrem := remainder_retention_bounds hn hr₀ hr₁
  have hrc : (remainderRetention n d j:ℝ)=
      4*((2:ℝ)^n)^2*(modeRemainder n (prescribedMass d) (majorantSum ((2^n)^16) (2^n) d j):ℝ) := by
    simp only [remainderRetention,Rat.cast_mul,Rat.cast_pow,Rat.cast_ofNat]
  rw [← hrc] at hrem
  exact ⟨⟨hc.1,hc.2.1⟩,by exact_mod_cast hdisc,by exact_mod_cast hrem⟩

end ExactQuantumFactoring.OrderTrial


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/TrialGuessLaw.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators
open Exactness

abbrev Guesses (n : ℕ) := Basis n × (Basis n × (Basis n × Basis (retentionBits n)))

noncomputable def guessState (n : ℕ) : Guesses n→ℂ :=
  independentState (fairState n) (independentState (fairState n)
    (independentState (fairState n) (fairState (retentionBits n))))

def Retains {n : ℕ} (p : ℚ) (c : Basis (retentionBits n)) : Prop :=
  (bitsValue c).toNat<(Int.floor (p*(2:ℚ)^(retentionBits n))).toNat

noncomputable def firstPass (n d j : ℕ) (x : Guesses n) : Prop :=
  Retains (firstRetention n d j) x.2.2.2
noncomputable def secondPass (n d j : ℕ) (x : Guesses n) : Prop :=
  (bitsValue x.1).toNat=d ∧ (bitsValue x.2.1).toNat=j ∧
    (bitsValue x.2.2.1).toNat<d ∧
      Retains (discrepancyRetention n d j (bitsValue x.2.2.1).toNat) x.2.2.2
noncomputable def thirdPass (n d j : ℕ) (x : Guesses n) : Prop :=
  (bitsValue x.1).toNat=d ∧ (bitsValue x.2.1).toNat=j ∧
    Retains (remainderRetention n d j) x.2.2.2

lemma guess_normalized (n : ℕ) : ∑ x : Guesses n, Complex.normSq (guessState n x)=1 := by
  have h₁ := RecordedHistory.append_normalized (fairState n) (fun _ => fairState (retentionBits n))
    (fair_normalized n) (fun _ => fair_normalized _)
  have h₂ := RecordedHistory.append_normalized (fairState n)
    (fun _ => independentState (fairState n) (fairState (retentionBits n)))
    (fair_normalized n) (fun _ => h₁)
  exact RecordedHistory.append_normalized (fairState n)
    (fun _ => independentState (fairState n) (independentState (fairState n) (fairState (retentionBits n))))
    (fair_normalized n) (fun _ => h₂)

lemma firstPass_mass {n d : ℕ} (hn : 1≤n) (hd : 0<d) (hdB : d<2^n) (j : ℕ) :
    outcomeMass (firstPass n d j) (guessState n)=(firstRetention n d j:ℝ) := by
  unfold firstPass guessState
  rw [independent_mass_right (fairState n) (independentState (fairState n)
      (independentState (fairState n) (fairState (retentionBits n))))
      (fun x => Retains (firstRetention n d j) x.2.2) (fair_normalized n),
    independent_mass_right (fairState n) (independentState (fairState n) (fairState (retentionBits n)))
      (fun x => Retains (firstRetention n d j) x.2) (fair_normalized n),
    independent_mass_right (fairState n) (fairState (retentionBits n)) (Retains (n:=n) (firstRetention n d j)) (fair_normalized n)]
  exact dyadic_fair_threshold (retentions_fixedDenominator hn hdB.le j 0).1
    (first_remainder_bounds hn hd hdB j).1 (first_remainder_bounds hn hd hdB j).2.1

lemma secondPass_mass {n d : ℕ} (hn : 1≤n) (hd : 0<d) (hdB : d<2^n)
    (j : ℕ) (hj : j<d) :
    outcomeMass (secondPass n d j) (guessState n)=
      (1/((2:ℝ)^n)^3)*∑ t ∈ Finset.range d, (discrepancyRetention n d j t:ℝ) := by
  unfold secondPass guessState
  rw [
    independent_mass (fairState n) (independentState (fairState n)
      (independentState (fairState n) (fairState (retentionBits n))))
      (fun x => (bitsValue x).toNat=d)
      (fun x => (bitsValue x.1).toNat=j ∧ (bitsValue x.2.1).toNat<d ∧
        Retains (discrepancyRetention n d j (bitsValue x.2.1).toNat) x.2.2),fair_value_mass hdB,
    independent_mass (fairState n) (independentState (fairState n) (fairState (retentionBits n)))
      (fun x => (bitsValue x).toNat=j)
      (fun x => (bitsValue x.1).toNat<d ∧ Retains (discrepancyRetention n d j (bitsValue x.1).toNat) x.2),
    fair_value_mass (hj.trans hdB),
    fair_variable_append hdB.le (fairState (retentionBits n))
      (fun t => Retains (n:=n) (discrepancyRetention n d j t))]
  have he : (∑ t ∈ Finset.range d,
      outcomeMass (Retains (n:=n) (discrepancyRetention n d j t)) (fairState (retentionBits n)))=
      ∑ t ∈ Finset.range d, (discrepancyRetention n d j t:ℝ) := by
    apply Finset.sum_congr rfl
    intro t ht
    exact dyadic_fair_threshold (retentions_fixedDenominator hn hdB.le j t).2.1
      (all_retention_bounds hn hd hdB j (Finset.mem_range.mp ht)).2.1.1
      (all_retention_bounds hn hd hdB j (Finset.mem_range.mp ht)).2.1.2
  rw [he]
  ring

lemma thirdPass_mass {n d : ℕ} (hn : 1≤n) (hd : 0<d) (hdB : d<2^n)
    (j : ℕ) (hj : j<d) :
    outcomeMass (thirdPass n d j) (guessState n)=
      (1/((2:ℝ)^n)^2)*(remainderRetention n d j:ℝ) := by
  unfold thirdPass guessState
  rw [
    independent_mass (fairState n) (independentState (fairState n)
      (independentState (fairState n) (fairState (retentionBits n))))
      (fun x => (bitsValue x).toNat=d)
      (fun x => (bitsValue x.1).toNat=j ∧ Retains (remainderRetention n d j) x.2.2),fair_value_mass hdB,
    independent_mass (fairState n) (independentState (fairState n) (fairState (retentionBits n)))
      (fun x => (bitsValue x).toNat=j)
      (fun x => Retains (remainderRetention n d j) x.2),fair_value_mass (hj.trans hdB),
    independent_mass_right (fairState n) (fairState (retentionBits n)) (Retains (n:=n) (remainderRetention n d j)) (fair_normalized n)]
  have he : outcomeMass (Retains (n:=n) (remainderRetention n d j)) (fairState (retentionBits n))=
      (remainderRetention n d j:ℝ) :=
    dyadic_fair_threshold (retentions_fixedDenominator hn hdB.le j 0).2.2
      (all_retention_bounds hn hd hdB j hd).2.2.1
      (all_retention_bounds hn hd hdB j hd).2.2.2
  rw [he]
  ring

end ExactQuantumFactoring.OrderTrial


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/OrderTrialLaw.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators

/-- Unnormalized joint amplitude after modular powering and the selected
phase-transform block. The modular-power register is NOT copied before this
interference sum. -/
noncomputable def selectedSampleAmplitude {G : Type*} [Group G]
    (Q k : ℕ) (a u : G) : ℂ := by
  classical
  exact (Q : ℂ)⁻¹ * ∑ x ∈ Finset.range Q,
    if a^x = u then phase ((k : ℝ)*x/Q) else 0

lemma selectedSampleAmplitude_residue {G : Type*} [Group G]
    (Q j : ℕ) (a : G) {t : ℕ} (ht : t < orderOf a) :
    selectedSampleAmplitude Q (bin Q (orderOf a) j) a (a^t) =
      residueAmplitude Q (orderOf a) j t := by
  classical
  unfold selectedSampleAmplitude residueAmplitude
  congr 1
  simp_rw [pow_inj_mod, Nat.mod_eq_of_lt ht]
  exact (Finset.sum_filter _ _).symm

lemma selectedSampleProbability_residue {G : Type*} [Group G]
    (Q j : ℕ) (a : G) {t : ℕ} (ht : t < orderOf a) :
    Complex.normSq (selectedSampleAmplitude Q (bin Q (orderOf a) j) a (a^t)) =
      residueProbability Q (orderOf a) j t := by
  rw [selectedSampleAmplitude_residue Q j a ht]
  exact Complex.normSq_eq_norm_sq _

/-- The literal modular-power verification in all three trial modes. -/
def ValidCandidate {G : Type*} [Group G] (B : ℕ) (a : G) (d : ℕ) : Prop :=
  1 ≤ d ∧ d < B ∧ a^d = 1

lemma ValidCandidate.order_dvd {G : Type*} [Group G] {B : ℕ} {a : G} {d : ℕ}
    (h : ValidCandidate B a d) : orderOf a ∣ d :=
  orderOf_dvd_of_pow_eq_one h.2.2

lemma trueOrder_valid {G : Type*} [Group G] [Finite G] {B : ℕ}
    (a : G) (hB : orderOf a < B) : ValidCandidate B a (orderOf a) :=
  ⟨orderOf_pos a, hB, pow_orderOf_eq_one a⟩

/-- Summing the exact per-reduced-label mass gives the prescribed true-order
probability phi(r) lambda(r), including r=1 and its label j=0. -/
lemma reduced_mass_sum {n Q B d : ℕ} (hB : 0 < B) (hd : 0 < d) :
    (∑ j ∈ (Finset.range d).filter (fun j => Nat.Coprime j d),
      (firstModeMass n Q B d j + secondModeMass n Q B d j +
        thirdModeMass n Q B d j)) =
      (Nat.totient d : ℝ) * (prescribedMass d : ℝ) := by
  classical
  have hm : ∀ j ∈ (Finset.range d).filter (fun j => Nat.Coprime j d),
      firstModeMass n Q B d j + secondModeMass n Q B d j + thirdModeMass n Q B d j =
        (prescribedMass d : ℝ) := by
    intro j hj
    exact three_mode_mass hB hd (Finset.mem_filter.mp hj).2
  rw [Finset.sum_congr rfl hm, Finset.sum_const, nsmul_eq_mul]
  congr 1
  norm_cast
  simp [Nat.totient, Nat.coprime_comm]

end ExactQuantumFactoring.OrderTrial


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/OrderSamplerMass.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open BooleanNetwork Exactness
namespace OrderTrial

/-- Distinct powers in one period; this is an embedding, not an oracle for r. -/
def powerOrbit {G : Type*} [Group G] (a : G) : Fin (orderOf a)→G := fun t => a^t.val
lemma powerOrbit_injective {G : Type*} [Group G] (a : G) : Function.Injective (powerOrbit a) := by
  intro s t h
  apply Fin.ext
  exact pow_injOn_Iio_orderOf s.isLt t.isLt h

lemma selectedSampleAmplitude_outside {G : Type*} [Group G] [Finite G]
    (Q k : ℕ) (a u : G) (hu : u ∉ Set.range (powerOrbit a)) :
    selectedSampleAmplitude Q k a u=0 := by
  have h : ∀ x : ℕ, a^x≠u := by
    intro x hx
    apply hu
    refine ⟨⟨x%orderOf a,Nat.mod_lt _ (orderOf_pos a)⟩,?_⟩
    exact (pow_mod_orderOf a x).trans hx
  simp [selectedSampleAmplitude,h]

lemma selectedSampleProbability_sum {G : Type*} [Group G] [Fintype G]
    (Q j : ℕ) (a : G) :
    (∑ u : G, Complex.normSq (selectedSampleAmplitude Q (bin Q (orderOf a) j) a u))=
      ∑ t : Fin (orderOf a), residueProbability Q (orderOf a) j t.val := by
  classical
  let e := powerOrbit a
  have he : Function.Injective e := powerOrbit_injective a
  have hz : ∀ u ∈ (Finset.univ : Finset G), u∉Finset.univ.image e →
      Complex.normSq (selectedSampleAmplitude Q (bin Q (orderOf a) j) a u)=0 := by
    intro u _ hu
    rw [selectedSampleAmplitude_outside Q _ a u]
    · exact map_zero _
    · rintro ⟨t,rfl⟩
      exact hu (Finset.mem_image.mpr ⟨t,Finset.mem_univ _,rfl⟩)
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image e)) hz,
    Finset.sum_image (fun _ _ _ _ h => he h)]
  apply Finset.sum_congr rfl
  intro t _
  exact selectedSampleProbability_residue Q j a t.isLt

/-- Exact bit representation used for modular-power values. -/
def natBasis (w z : ℕ) : Basis w := fun i => (BitVec.ofNat w z).getLsbD i.val
lemma natBasis_value (w z : ℕ) : (bitsValue (natBasis w z)).toNat=z%2^w := by
  change (bitsValue (fun i : Fin w => (BitVec.ofNat w z).getLsbD i.val)).toNat=z%2^w
  exact congrArg BitVec.toNat (bitsValue_bits (BitVec.ofNat w z))
lemma natBasis_injectiveOn (w : ℕ) : Set.InjOn (natBasis w) (Set.Iio (2^w)) := by
  intro x hx y hy h
  have hh := congrArg (fun z : Basis w => (bitsValue z).toNat) h
  simpa only [natBasis_value,Nat.mod_eq_of_lt hx,Nat.mod_eq_of_lt hy] using hh

/-- Embed all units into the physical modular-power register, when m<2^w. -/
def unitWord {m w : ℕ} (u : (ZMod m)ˣ) : Basis w := natBasis w (u : ZMod m).val
lemma unitWord_value {m w : ℕ} [NeZero m] (hm : m<2^w) (u : (ZMod m)ˣ) :
    (bitsValue (unitWord (w:=w) u)).toNat=(u : ZMod m).val := by
  rw [unitWord,natBasis_value,Nat.mod_eq_of_lt ((ZMod.val_lt _).trans hm)]
lemma unitWord_injective {m w : ℕ} [NeZero m] (hm : m<2^w) :
    Function.Injective (unitWord (m:=m) (w:=w)) := by
  intro u v h
  apply Units.ext
  apply ZMod.val_injective
  have hh := congrArg (fun x : Basis w => (bitsValue x).toNat) h
  simpa only [unitWord_value hm] using hh

lemma nat_pow_eq_unit {m a : ℕ} [NeZero m] (u : (ZMod m)ˣ)
    (ha : (a : ZMod m)=(u : ZMod m)) (x : ℕ) :
    a^x%m=((u^x : (ZMod m)ˣ) : ZMod m).val := by
  rw [Units.val_pow_eq_pow_val,← ha,← Nat.cast_pow,ZMod.val_natCast]

lemma nat_pow_eq_word_iff {m w a : ℕ} [NeZero m] (hm : m<2^w)
    (u v : (ZMod m)ˣ) (ha : (a : ZMod m)=(u : ZMod m)) (x : ℕ) :
    a^x%m=(bitsValue (unitWord (w:=w) v)).toNat ↔ u^x=v := by
  rw [unitWord_value hm,nat_pow_eq_unit u ha]
  exact ⟨fun h => Units.ext (ZMod.val_injective _ h),fun h => by rw [h]⟩

/-- The physical amplitude, at any encoded unit, equals the group-theoretic
coherent residue sum. No early classical measurement is used here. -/
theorem sampler_unit_amplitude {w s : ℕ} (a m : Basis w) (y : Basis (s+2))
    (hm : 2≤(bitsValue m).toNat) (u v : (ZMod (bitsValue m).toNat)ˣ)
    (ha : ((bitsValue a).toNat : ZMod (bitsValue m).toNat)=(u : ZMod (bitsValue m).toNat)) :
    (programMatrix (OrderSample.completeSampler w s)).mulVec
      (basisVector (OrderSample.word a m (fun _=>false) (fun _=>false)))
      (OrderSample.word a m y (unitWord (w:=w) v))=
      selectedSampleAmplitude (2^(s+2)) (Triangular.outputNumber y) u v := by
  let : NeZero (bitsValue m).toNat := ⟨by omega⟩
  rw [OrderSample.completeSampler_amplitude _ _ _ _ hm]
  simp only [selectedSampleAmplitude,nat_pow_eq_word_iff (bitsValue m).isLt u v ha]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> rfl


lemma outcomeMass_range {α β : Type*} [Fintype α] [Fintype β]
    (e : α→β) (he : Function.Injective e) (ψ : β→ℂ) :
    outcomeMass (fun y => y∈Set.range e) ψ=∑ a, Complex.normSq (ψ (e a)) := by
  classical
  let f : β→ℝ := fun y => if y∈Set.range e then Complex.normSq (ψ y) else 0
  have hh : outcomeMass (fun y => y∈Set.range e) ψ=Finset.univ.sum f := by
    unfold outcomeMass
    apply Finset.sum_congr rfl
    intro y _
    dsimp only [f]
    split_ifs <;> rfl
  rw [hh]
  have hz : ∀ y∈(Finset.univ : Finset β), y∉Finset.univ.image e → f y=0 := by
    intro y _ hy
    dsimp only [f]
    rw [ite_eq_right]
    rintro ⟨a,rfl⟩
    exact hy (Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩)
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image e)) hz,
    Finset.sum_image (fun _ _ _ _ h => he h)]
  apply Finset.sum_congr rfl
  intro t _
  exact ite_eq_left ⟨t,rfl⟩

lemma sampler_word_injective {w b : ℕ} (a m : Basis w) (y : Basis b) :
    Function.Injective (OrderSample.word a m y) := by
  intro u v h
  have hh := BooleanNetwork.packed_injective
    (a₁:=(OrderSample.inputWord a m y,u)) (a₂:=(OrderSample.inputWord a m y,v)) h
  exact congrArg Prod.snd hh

noncomputable def samplerState {w s : ℕ} (a m : Basis w) : State (OrderSample.width w (s+2)) :=
  (programMatrix (OrderSample.completeSampler w s)).mulVec
    (basisVector (OrderSample.word a m (fun _=>false) (fun _=>false)))

lemma sampler_outside_units {w s : ℕ} (a m : Basis w) (y : Basis (s+2))
    (hm : 2≤(bitsValue m).toNat) (u : (ZMod (bitsValue m).toNat)ˣ)
    (ha : ((bitsValue a).toNat : ZMod (bitsValue m).toNat)=(u : ZMod (bitsValue m).toNat))
    (z : Basis w) (hz : z∉Set.range (unitWord (m:=(bitsValue m).toNat) (w:=w))) :
    samplerState a m (OrderSample.word a m y z)=0 := by
  let : NeZero (bitsValue m).toNat := ⟨by omega⟩
  have hh : ∀ x : ℕ, (bitsValue a).toNat^x%(bitsValue m).toNat≠(bitsValue z).toNat := by
    intro x hx
    apply hz
    refine ⟨u^x,?_⟩
    apply (bitsEquiv w).injective
    apply BitVec.eq_of_toNat_eq
    change (bitsValue (unitWord (w:=w) (u^x))).toNat=(bitsValue z).toNat
    rw [unitWord_value (bitsValue m).isLt,← nat_pow_eq_unit u ha]
    exact hx
  rw [samplerState,OrderSample.completeSampler_amplitude _ _ _ _ hm]
  simp only [hh,ite_false,Finset.sum_const_zero,mul_zero]

/-- The complete physical selected-bin probability is the sum of the literal
residue probabilities at the TRUE order. False labels are not identified with
artificial probabilities. -/
theorem sampler_selected_bin_mass {w s : ℕ} (a m : Basis w) (y : Basis (s+2))
    (hm : 2≤(bitsValue m).toNat) (u : (ZMod (bitsValue m).toNat)ˣ)
    (ha : ((bitsValue a).toNat : ZMod (bitsValue m).toNat)=(u : ZMod (bitsValue m).toNat))
    (j : ℕ) (hy : Triangular.outputNumber y=bin (2^(s+2)) (orderOf u) j) :
    outcomeMass (fun z => z∈Set.range (OrderSample.word a m y)) (samplerState a m)=
      ∑ t : Fin (orderOf u), residueProbability (2^(s+2)) (orderOf u) j t.val := by
  classical
  let : NeZero (bitsValue m).toNat := ⟨by omega⟩
  rw [outcomeMass_range _ (sampler_word_injective a m y)]
  let e := unitWord (m:=(bitsValue m).toNat) (w:=w)
  have he : Function.Injective e := unitWord_injective (bitsValue m).isLt
  have hz : ∀ z∈(Finset.univ : Finset (Basis w)), z∉Finset.univ.image e →
      Complex.normSq (samplerState a m (OrderSample.word a m y z))=0 := by
    intro z _ hz
    rw [sampler_outside_units a m y hm u ha z]
    · exact map_zero _
    · rintro ⟨v,rfl⟩
      exact hz (Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩)
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image e)) hz,
    Finset.sum_image (fun _ _ _ _ h => he h)]
  simp only [e,samplerState,sampler_unit_amplitude a m y hm u _ ha,hy]
  exact selectedSampleProbability_sum _ j u

end OrderTrial
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/TrialRawPreparation.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open Exactness

lemma parallelProgram_entry {p q : ℕ} (A : List (Instruction p)) (B : List (Instruction q))
    (x z : Basis p) (y u : Basis q) :
    (programMatrix (parallelProgram A B)).mulVec (basisVector (Fin.append x y)) (Fin.append z u)=
      ((programMatrix A).mulVec (basisVector x) z)*((programMatrix B).mulVec (basisVector y) u) := by
  rw [parallelProgram_basis]
  exact encodeState_at (appendEquiv p q) (appendEquiv p q).injective _ (z,u)

def productLayout {α β : Type*} {p q : ℕ} (e : α≃Basis p) (f : β≃Basis q) :
    α×β≃Basis (p+q) := (Equiv.prodCongr e f).trans (appendEquiv p q)
lemma productLayout_apply {α β : Type*} {p q : ℕ} (e : α≃Basis p) (f : β≃Basis q) (xy : α×β) :
    productLayout e f xy=Fin.append (e xy.1) (f xy.2) := rfl

namespace OrderTrial

abbrev guessWidth (n : ℕ) := n+(n+(n+retentionBits n))
def guessLayout (n : ℕ) : Guesses n≃Basis (guessWidth n) :=
  productLayout (Equiv.refl _) (productLayout (Equiv.refl _)
    (productLayout (Equiv.refl _) (Equiv.refl _)))
def guessProgram (n : ℕ) : List (Instruction (guessWidth n)) :=
  parallelProgram (hadamardPrefix n n le_rfl) (parallelProgram (hadamardPrefix n n le_rfl)
    (parallelProgram (hadamardPrefix n n le_rfl) (hadamardPrefix (retentionBits n) (retentionBits n) le_rfl)))
def guessZero (n : ℕ) : Guesses n := ((fun _ => false),(fun _ => false),(fun _ => false),(fun _ => false))

lemma guessProgram_entry (n : ℕ) (x : Guesses n) :
    (programMatrix (guessProgram n)).mulVec (basisVector (guessLayout n (guessZero n)))
      (guessLayout n x)=guessState n x := by
  simp only [guessProgram,guessLayout,productLayout_apply,guessZero,Equiv.refl_apply,
    parallelProgram_entry,hadamards_zero]
  rfl
lemma guessProgram_length (n : ℕ) : (guessProgram n).length=3*n+retentionBits n := by
  simp only [guessProgram,parallelProgram_length,hadamardPrefix_length]
  omega

abbrev Raw (w s n : ℕ) := Basis 2 × (Basis (OrderSample.width w (s+2)) × Guesses n)
abbrev rawWidth (w s n : ℕ) := 2+(OrderSample.width w (s+2)+guessWidth n)
def rawLayout (w s n : ℕ) : Raw w s n≃Basis (rawWidth w s n) :=
  productLayout (Equiv.refl _) (productLayout (Equiv.refl _) (guessLayout n))
def rawProgram (w s n : ℕ) : List (Instruction (rawWidth w s n)) :=
  parallelProgram (hadamardPrefix 2 2 le_rfl)
    (parallelProgram (OrderSample.completeSampler w s) (guessProgram n))
noncomputable def rawZero {w : ℕ} (s n : ℕ) (a m : Basis w) : Raw w s n :=
  ((fun _ => false),OrderSample.word a m (fun _ => false) (fun _ => false),guessZero n)
noncomputable def rawState {w : ℕ} (s n : ℕ) (a m : Basis w) : Raw w s n→ℂ :=
  independentState (fairState 2) (independentState (samplerState (s:=s) a m) (guessState n))

lemma rawProgram_entry {w : ℕ} (s n : ℕ) (a m : Basis w) (x : Raw w s n) :
    (programMatrix (rawProgram w s n)).mulVec (basisVector (rawLayout w s n (rawZero s n a m)))
      (rawLayout w s n x)=rawState s n a m x := by
  simp only [rawProgram,rawLayout,productLayout_apply,rawZero,Equiv.refl_apply,
    parallelProgram_entry,hadamards_zero,guessProgram_entry]
  rfl

lemma rawProgram_state {w : ℕ} (s n : ℕ) (a m : Basis w) :
    (programMatrix (rawProgram w s n)).mulVec (basisVector (rawLayout w s n (rawZero s n a m)))=
      encodeState (rawLayout w s n) (rawState s n a m) := by
  funext x
  obtain ⟨y,rfl⟩ := (rawLayout w s n).surjective x
  rw [rawProgram_entry,encodeState_at _ (rawLayout w s n).injective]

lemma raw_normalized {w : ℕ} (s n : ℕ) (a m : Basis w) :
    ∑ x, Complex.normSq (rawState s n a m x)=1 := by
  have h := RecordedHistory.append_normalized (samplerState (s:=s) a m) (fun _ => guessState n)
    (basis_preparation_normalized (OrderSample.completeSampler w s) _) (fun _ => guess_normalized n)
  exact RecordedHistory.append_normalized (fairState 2)
    (fun _ => independentState (samplerState (s:=s) a m) (guessState n))
    (fair_normalized 2) (fun _ => h)

/-- A physical Born event equals the corresponding retained-history event.
This layout is bijective; no outcome amplitudes are discarded. -/
lemma rawProgram_mass {w : ℕ} (s n : ℕ) (a m : Basis w) (P : Raw w s n→Prop) :
    outcomeMass (P ∘ (rawLayout w s n).symm)
      ((programMatrix (rawProgram w s n)).mulVec (basisVector (rawLayout w s n (rawZero s n a m))))=
      outcomeMass P (rawState s n a m) := by
  rw [rawProgram_state,outcomeMass_encode _ (rawLayout w s n).injective]
  congr 1
  funext x
  simp

end OrderTrial
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/TensorPreparation.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open Exactness RepeatedTrials

abbrev tensorWidth (q : ℕ) : ℕ→ℕ
  | 0 => 0
  | K+1 => q+tensorWidth q K

lemma tensorWidth_eq (q K : ℕ) : tensorWidth q K=K*q := by
  induction K with
  | zero => simp [tensorWidth]
  | succ K ih => simp [tensorWidth,ih,Nat.add_mul,Nat.add_comm]

def tensorLayout (q : ℕ) : (K : ℕ)→(Fin K→Basis q)≃Basis (tensorWidth q K)
  | 0 => Equiv.ofUnique _ _
  | K+1 => (Fin.consEquiv (fun _ : Fin (K+1) => Basis q)).symm.trans
      (productLayout (Equiv.refl _) (tensorLayout q K))

lemma tensorLayout_succ (q K : ℕ) (x : Fin (K+1)→Basis q) :
    tensorLayout q (K+1) x=Fin.append (x 0) (tensorLayout q K (Fin.tail x)) := rfl

def tensorProgram {q : ℕ} (ops : List (Instruction q)) : (K : ℕ)→List (Instruction (tensorWidth q K))
  | 0 => []
  | K+1 => parallelProgram ops (tensorProgram ops K)

lemma tensorProgram_length {q : ℕ} (ops : List (Instruction q)) (K : ℕ) :
    (tensorProgram ops K).length=K*ops.length := by
  induction K with
  | zero => simp [tensorProgram]
  | succ K ih => rw [tensorProgram,parallelProgram_length,ih]; ring

lemma tensorProgram_entry {q : ℕ} (ops : List (Instruction q)) (K : ℕ)
    (x y : Fin K→Basis q) :
    (programMatrix (tensorProgram ops K)).mulVec (basisVector (tensorLayout q K x)) (tensorLayout q K y)=
      ∏ i, (programMatrix ops).mulVec (basisVector (x i)) (y i) := by
  induction K with
  | zero =>
    have he : x=y := Subsingleton.elim _ _
    subst y
    simp [tensorProgram,programMatrix,basisVector]
  | succ K ih =>
    rw [tensorProgram,tensorLayout_succ,tensorLayout_succ,parallelProgram_entry,ih,Fin.prod_univ_succ]
    rfl

/-- A literal repeated finite-gate program, not just a tensor-state idealization. -/
lemma tensorProgram_state {q : ℕ} (ops : List (Instruction q)) (K : ℕ) (x : Basis q) :
    (programMatrix (tensorProgram ops K)).mulVec (basisVector (tensorLayout q K (fun _ => x)))=
      encodeState (tensorLayout q K) (tensorState ((programMatrix ops).mulVec (basisVector x)) K) := by
  funext y
  obtain ⟨z,rfl⟩ := (tensorLayout q K).surjective y
  rw [tensorProgram_entry,encodeState_at _ (tensorLayout q K).injective]
  rfl

lemma tensorProgram_event {q : ℕ} (ops : List (Instruction q)) (K : ℕ) (x : Basis q)
    (P : (Fin K→Basis q)→Prop) :
    outcomeMass (P ∘ (tensorLayout q K).symm)
      ((programMatrix (tensorProgram ops K)).mulVec (basisVector (tensorLayout q K (fun _ => x))))=
      outcomeMass P (tensorState ((programMatrix ops).mulVec (basisVector x)) K) := by
  rw [tensorProgram_state,outcomeMass_encode _ (tensorLayout q K).injective]
  congr 1
  funext y
  simp

end ExactQuantumFactoring


end

end OAI


