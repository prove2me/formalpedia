-- Prove2me | Definitions.Def_OAI_QuantumFactoring_Part15
-- name    : OAI_QuantumFactoring_Part15
-- status  : Definition
-- author  : @SamenHossain
-- created : 2026-10-12T07:54:27.628672+00:00
-- url     : https://prove2.me/theorems/8ba1d8a8-097e-4e38-8920-3ab826f2e2d5
-- title:
--   Exact quantum factoring, part 15 of 38 (port of OpenAI's formalization)
-- statement:
--   Part 15 of 38 of a port of OpenAI's Lean formalization of the manuscript *Exact quantum factoring over a fixed finite gate set* (OpenAI, September 25, 2026). This part contains the modules `ExpressionSharing`, `RetentionCircuit`, `TrialControlCircuit`, `RawTrialDecoder`, `MinimumCandidateCircuit`, `PhysicalOrderDecoder`, `BoundedStack`, `NodeControlCircuit`, `SuppliedDivisorCircuit`, `WideSplitCircuit`, `PhysicalSplitDecoder`, `PhysicalSplitLaunch`.
--
--   **Attribution.** The code is adapted from the OpenAI "math" repository, commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, directory `lean/OAI/Computability/QuantumFactoring`. It is © OpenAI and licensed under the Apache License 2.0; the adapted code is redistributed under the same license.
--
--   **Modifications.** Modules are concatenated in dependency order, with their imports replaced by the previous part. The model definitions come from the platform definition `ExactQuantumFactoring`, which is identical to upstream `Basic.lean`.
--
--   The development is split into 38 parts only so that each compiles within the platform's time limit. Together the parts supply the circuit family `PhysicalTree.finalCircuit` and its specification, used to prove `OAI.ExactQuantumFactoring.zero_amplitude_core`.
-- source:
--   OpenAI, openai/math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, lean/OAI/Computability/QuantumFactoring: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/ExpressionSharing.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/RetentionCircuit.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/TrialControlCircuit.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/RawTrialDecoder.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/MinimumCandidateCircuit.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/PhysicalOrderDecoder.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/BoundedStack.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/NodeControlCircuit.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/SuppliedDivisorCircuit.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/WideSplitCircuit.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/PhysicalSplitDecoder.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/PhysicalSplitLaunch.lean (Apache License 2.0); manuscript https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Exact-quantum-factoring-over-a-fixed-finite-gate-set-September-25-2026/main.pdf

/-
Exact quantum factoring development (port of OpenAI's formalization), part 15 of 38.

Adapted from the OpenAI "math" repository (https://github.com/openai/math, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a), lean/OAI/Computability/QuantumFactoring/: ExpressionSharing.lean, RetentionCircuit.lean, TrialControlCircuit.lean, RawTrialDecoder.lean, MinimumCandidateCircuit.lean, PhysicalOrderDecoder.lean, BoundedStack.lean, NodeControlCircuit.lean, SuppliedDivisorCircuit.lean, WideSplitCircuit.lean, PhysicalSplitDecoder.lean, PhysicalSplitLaunch.lean
These files formalize the manuscript "Exact quantum factoring over a fixed finite gate set"
(OpenAI, September 25, 2026). Copyright OpenAI. Licensed under the Apache License, Version 2.0
(http://www.apache.org/licenses/LICENSE-2.0); the adapted code is distributed under the same license,
on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND.

Modifications: modules concatenated in dependency order with their import lines removed; the model
definitions (Basic.lean) come from the platform definition `ExactQuantumFactoring`, to which upstream
Basic.lean is identical; the final assembly (Main.lean) is omitted.
-/
import Mathlib
import Definitions.Def_OAI_QuantumFactoring_Part14

set_option autoImplicit false

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/ExpressionSharing.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace NatExpr
variable {v : Type*}

/-- Only truncated subtraction duplicates its operands in the actual compiler.
In particular a priority-search tail in an ite is compiled ONCE, not twice. -/
def sharedCost : NatExpr v → ℕ
  | .var _ | .const _ => 1
  | .add a b | .mul a b | .div a b | .mod a b => a.sharedCost+b.sharedCost+1
  | .sub a b => 2*(a.sharedCost+b.sharedCost)+1
  | .iteLe a b c d => a.sharedCost+b.sharedCost+c.sharedCost+d.sharedCost+1

lemma compile_shared_count {k w c : ℕ} (vars : v → BooleanNetwork k w)
    (hc : ∀ i, (vars i).net.count ≤ c) (e : NatExpr v) :
    (e.compile vars).net.count ≤ e.sharedCost*(operationBound w+c) := by
  induction e with
  | var i => simpa only [compile,sharedCost,one_mul] using (hc i).trans (Nat.le_add_left c _)
  | const d => simp only [compile,sharedCost,one_mul,wordConstant_count,operationBound]; omega
  | add a b ia ib =>
    have hh := add_count w
    simp only [compile,count_comp,count_pair,sharedCost]
    dsimp [operationBound] at *
    nlinarith
  | mul a b ia ib =>
    have hh := mul_count w
    simp only [compile,count_comp,count_pair,sharedCost]
    dsimp [operationBound] at *
    nlinarith
  | sub a b ia ib =>
    have hh := natSubOn_count (a.compile vars) (b.compile vars)
    change (natSubOn (a.compile vars) (b.compile vars)).net.count ≤ _
    simp only [sharedCost]
    dsimp [operationBound] at *
    nlinarith
  | div a b ia ib =>
    have hh := div_count w
    simp only [compile,count_comp,count_pair,sharedCost]
    dsimp [operationBound] at *
    nlinarith
  | mod a b ia ib =>
    have hh := mod_count w
    simp only [compile,count_comp,count_pair,sharedCost]
    dsimp [operationBound] at *
    nlinarith
  | iteLe a b d e ia ib id ie =>
    have hh := wordLe_count (a.compile vars) (b.compile vars)
    simp only [compile,wordMux_count,sharedCost]
    dsimp [operationBound] at *
    nlinarith

lemma template_shared_count {k b c : ℕ} (e : NatExpr v) (vars : v → BooleanNetwork k b)
    (hc : ∀ i, (vars i).net.count ≤ c) :
    (e.template vars).net.count ≤
      e.sharedCost*(operationBound (e.templateWidth b)+c+e.templateWidth b) := by
  unfold template
  have hh := e.compile_shared_count (fun i => (vars i).comp (resizeWord b (e.templateWidth b)))
    (c:=c+e.templateWidth b) (by
      intro i
      rw [count_comp]
      exact Nat.add_le_add (hc i) (resizeWord_count _ _))
  simpa only [Nat.add_assoc] using hh

end NatExpr
namespace OrderTrial.Expressions
variable {v : Type*}

lemma coveringPow_sharedCost (d : NatExpr v) (n : ℕ) :
    (coveringPow d n).sharedCost=n*(d.sharedCost+3)+1 := by
  induction n with
  | zero => simp [coveringPow,NatExpr.sharedCost]
  | succ n ih => simp only [coveringPow,NatExpr.sharedCost,ih]; ring

lemma coveringPow_size (d : NatExpr v) (n : ℕ) :
    (coveringPow d n).size=n*(d.size+3)+1 := by
  induction n with
  | zero => simp [coveringPow,NatExpr.size]
  | succ n ih => simp only [coveringPow,NatExpr.size,ih]; ring

end OrderTrial.Expressions
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/RetentionCircuit.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace NatExpr
variable {v : Type*}
lemma isOne_shared_count {k b c : ℕ} (e : NatExpr v) (vars : v → BooleanNetwork k b)
    (hc : ∀ i, (vars i).net.count ≤ c) :
    (e.isOne vars).net.count ≤
      e.sharedCost*(operationBound (e.templateWidth b)+c+e.templateWidth b)+
        100*(e.templateWidth b)+21 := by
  have he := e.template_shared_count vars hc
  have hh := equalOn_count (e.template vars) (wordConstant (n:=k) (BitVec.ofNat (e.templateWidth b) 1))
  simp only [wordConstant_count] at hh
  exact hh.trans (by omega)
end NatExpr

/-- Compile the dyadic threshold to a finite Boolean network. All arithmetic,
including signed rational division and floor, is reduced to bounded word gates. -/
def retentionNet {v : Type*} {k b : ℕ} (T : ℕ) (p : RatExpr v) (coin : NatExpr v)
    (vars : v → BooleanNetwork k b) : BooleanNetwork k 1 :=
  (thresholdExpr T p coin).isOne vars
lemma retentionNet_value {v : Type*} {k b : ℕ} (T : ℕ) (p : RatExpr v) (coin : NatExpr v)
    (vars : v → BooleanNetwork k b) (x : Basis k) :
    (retentionNet T p coin vars).eval x 0=true ↔
      coin.eval (fun i => (bitsValue ((vars i).eval x)).toNat)<
        (Int.floor (p.eval (fun i => (bitsValue ((vars i).eval x)).toNat)*(2:ℚ)^T)).toNat := by
  rw [retentionNet,NatExpr.isOne_eval,thresholdExpr_eval]
lemma retentionNet_count {v : Type*} {k b c : ℕ} (T : ℕ) (p : RatExpr v) (coin : NatExpr v)
    (vars : v → BooleanNetwork k b) (hc : ∀ i, (vars i).net.count ≤ c) :
    (retentionNet T p coin vars).net.count ≤
      (thresholdExpr T p coin).sharedCost*
        (NatExpr.operationBound ((thresholdExpr T p coin).templateWidth b)+c+
          (thresholdExpr T p coin).templateWidth b)+
        100*((thresholdExpr T p coin).templateWidth b)+21 :=
  NatExpr.isOne_shared_count _ _ hc

namespace OrderTrial.Expressions
variable {v : Type*}

def firstE (n : ℕ) (d j : NatExpr v) : RatExpr v :=
  coefficientE n (.const ((2^n)^16)) (.const (2^n)) d j
def secondE (n : ℕ) (d j t : NatExpr v) : RatExpr v :=
  discrepancyE n (.const ((2^n)^16)) (.const (2^n)) d j t
def lastE (n : ℕ) (d j : NatExpr v) : RatExpr v :=
  thirdRetentionE n (.const ((2^n)^16)) (.const (2^n)) d j

lemma firstE_value (x : v→ℕ) (n : ℕ) (d j : NatExpr v)
    (hd : d.eval x≤2^n) (hpos : 0<d.eval x) :
    (firstE n d j).eval x=firstRetention n (d.eval x) (j.eval x) := by
  exact coefficientE_correct x n _ _ d j hd hpos
lemma secondE_value (x : v→ℕ) (n : ℕ) (d j t : NatExpr v)
    (hd : d.eval x≤2^n) (hpos : 0<d.eval x) (ht : t.eval x<d.eval x) :
    (secondE n d j t).eval x=discrepancyRetention n (d.eval x) (j.eval x) (t.eval x) := by
  have hQ : d.eval x≤((2^n)^16) := hd.trans
    (Nat.le_self_pow (by decide : 16≠0) (2^n))
  have h := discrepancyE_correct x n (.const ((2^n)^16)) (.const (2^n)) d j t hd hpos ht hQ
  simpa only [NatExpr.eval,Nat.cast_pow,Nat.cast_ofNat,secondE,discrepancyRetention] using h
lemma lastE_value (x : v→ℕ) (n : ℕ) (d j : NatExpr v)
    (hd : d.eval x≤2^n) (hpos : 0<d.eval x) :
    (lastE n d j).eval x=remainderRetention n (d.eval x) (j.eval x) := by
  have h := thirdRetentionE_correct x n (.const ((2^n)^16)) (.const (2^n)) d j hd hpos
  simpa only [NatExpr.eval,Nat.cast_pow,Nat.cast_ofNat,lastE,remainderRetention] using h

/-- The three actual source retentions. Each net is total also at malformed
labels; the separately compiled label guard suppresses those outputs. -/
def modeRetentionNet {k b : ℕ} (n : ℕ) (mode : Fin 3) (d j t coin : NatExpr v)
    (vars : v → BooleanNetwork k b) : BooleanNetwork k 1 :=
  retentionNet (retentionBits n)
    (if mode=0 then firstE n d j else if mode=1 then secondE n d j t else lastE n d j) coin vars

lemma modeRetentionNet_value {k b : ℕ} (n : ℕ) (mode : Fin 3) (d j t coin : NatExpr v)
    (vars : v → BooleanNetwork k b) (x : Basis k)
    (hd : d.eval (fun i => (bitsValue ((vars i).eval x)).toNat)≤2^n)
    (hpos : 0<d.eval (fun i => (bitsValue ((vars i).eval x)).toNat))
    (ht : t.eval (fun i => (bitsValue ((vars i).eval x)).toNat)<
      d.eval (fun i => (bitsValue ((vars i).eval x)).toNat)) :
    let dx := d.eval (fun i => (bitsValue ((vars i).eval x)).toNat)
    let jx := j.eval (fun i => (bitsValue ((vars i).eval x)).toNat)
    let tx := t.eval (fun i => (bitsValue ((vars i).eval x)).toNat)
    (modeRetentionNet n mode d j t coin vars).eval x 0=true ↔
      coin.eval (fun i => (bitsValue ((vars i).eval x)).toNat)<
        (Int.floor ((if mode=0 then firstRetention n dx jx else
          if mode=1 then discrepancyRetention n dx jx tx else remainderRetention n dx jx)*
            (2:ℚ)^(retentionBits n))).toNat := by
  dsimp only
  rw [modeRetentionNet,retentionNet_value]
  split_ifs <;> simp only [firstE_value _ n d j hd hpos,
    secondE_value _ n d j t hd hpos ht,lastE_value _ n d j hd hpos]
end OrderTrial.Expressions
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/TrialControlCircuit.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.OrderTrial
open BooleanNetwork BitArithmetic

inductive DecodeVar | den | num | residue | coin

private def decodeVars {k w : ℕ} (d j t c : BooleanNetwork k w) : DecodeVar → BooleanNetwork k w
  | .den => d | .num => j | .residue => t | .coin => c

def firstRetNet {k w : ℕ} (n : ℕ) (d j t c : BooleanNetwork k w) : BooleanNetwork k 1 :=
  retentionNet (retentionBits n) (Expressions.firstE n (.var .den) (.var .num))
    (.var .coin) (decodeVars d j t c)
def secondRetNet {k w : ℕ} (n : ℕ) (d j t c : BooleanNetwork k w) : BooleanNetwork k 1 :=
  retentionNet (retentionBits n) (Expressions.secondE n (.var .den) (.var .num) (.var .residue))
    (.var .coin) (decodeVars d j t c)
def thirdRetNet {k w : ℕ} (n : ℕ) (d j t c : BooleanNetwork k w) : BooleanNetwork k 1 :=
  retentionNet (retentionBits n) (Expressions.lastE n (.var .den) (.var .num))
    (.var .coin) (decodeVars d j t c)

lemma firstRetNet_value {k w : ℕ} (n : ℕ) (d j t c : BooleanNetwork k w) (x : Basis k)
    (hd : (bitsValue (d.eval x)).toNat≤2^n) (hp : 0<(bitsValue (d.eval x)).toNat) :
    (firstRetNet n d j t c).eval x 0=true ↔
      (bitsValue (c.eval x)).toNat<(Int.floor (firstRetention n
        (bitsValue (d.eval x)).toNat (bitsValue (j.eval x)).toNat*(2:ℚ)^(retentionBits n))).toNat := by
  rw [firstRetNet,retentionNet_value,Expressions.firstE_value (fun i => (bitsValue ((decodeVars d j t c i).eval x)).toNat) n (.var .den) (.var .num) hd hp]
  rfl
lemma secondRetNet_value {k w : ℕ} (n : ℕ) (d j t c : BooleanNetwork k w) (x : Basis k)
    (hd : (bitsValue (d.eval x)).toNat≤2^n) (hp : 0<(bitsValue (d.eval x)).toNat)
    (ht : (bitsValue (t.eval x)).toNat<(bitsValue (d.eval x)).toNat) :
    (secondRetNet n d j t c).eval x 0=true ↔
      (bitsValue (c.eval x)).toNat<(Int.floor (discrepancyRetention n
        (bitsValue (d.eval x)).toNat (bitsValue (j.eval x)).toNat
          (bitsValue (t.eval x)).toNat*(2:ℚ)^(retentionBits n))).toNat := by
  rw [secondRetNet,retentionNet_value,Expressions.secondE_value (fun i => (bitsValue ((decodeVars d j t c i).eval x)).toNat) n (.var .den) (.var .num) (.var .residue) hd hp ht]
  rfl
lemma thirdRetNet_value {k w : ℕ} (n : ℕ) (d j t c : BooleanNetwork k w) (x : Basis k)
    (hd : (bitsValue (d.eval x)).toNat≤2^n) (hp : 0<(bitsValue (d.eval x)).toNat) :
    (thirdRetNet n d j t c).eval x 0=true ↔
      (bitsValue (c.eval x)).toNat<(Int.floor (remainderRetention n
        (bitsValue (d.eval x)).toNat (bitsValue (j.eval x)).toNat*(2:ℚ)^(retentionBits n))).toNat := by
  rw [thirdRetNet,retentionNet_value,Expressions.lastE_value (fun i => (bitsValue ((decodeVars d j t c i).eval x)).toNat) n (.var .den) (.var .num) hd hp]
  rfl

/-- Mode guards are outside the rational computations. In particular malformed
labels and residue guesses cannot turn an irrelevant retention into acceptance. -/
def trialAcceptOn {k w : ℕ} (n : ℕ) (a m mode d j t c : BooleanNetwork k w)
    (selected : BooleanNetwork k 1) : BooleanNetwork k 1 :=
  (labelValidNet n a m d j).band
    (((wordLt mode (wordConstant (BitVec.ofNat w 2))).band
      (selected.band (firstRetNet n d j t c))).bor
    (((equalOn mode (wordConstant (BitVec.ofNat w 2))).band
      ((wordLt t d).band (secondRetNet n d j t c))).bor
     ((equalOn mode (wordConstant (BitVec.ofNat w 3))).band (thirdRetNet n d j t c))))

lemma trialAcceptOn_value {k w : ℕ} (n : ℕ) (a m mode d j t c : BooleanNetwork k w)
    (selected : BooleanNetwork k 1) (hn : n<w) (hw : 2≤w) (x : Basis k)
    (hm : 2≤(bitsValue (m.eval x)).toNat) :
    (trialAcceptOn n a m mode d j t c selected).eval x 0=true ↔
      ValidLabel n (bitsValue (a.eval x)).toNat (bitsValue (m.eval x)).toNat
        (bitsValue (d.eval x)).toNat (bitsValue (j.eval x)).toNat ∧
      (((bitsValue (mode.eval x)).toNat<2 ∧ selected.eval x 0=true ∧
        (bitsValue (c.eval x)).toNat<(Int.floor (firstRetention n
          (bitsValue (d.eval x)).toNat (bitsValue (j.eval x)).toNat*(2:ℚ)^(retentionBits n))).toNat) ∨
       ((bitsValue (mode.eval x)).toNat=2 ∧ (bitsValue (t.eval x)).toNat<(bitsValue (d.eval x)).toNat ∧
        (bitsValue (c.eval x)).toNat<(Int.floor (discrepancyRetention n
          (bitsValue (d.eval x)).toNat (bitsValue (j.eval x)).toNat
            (bitsValue (t.eval x)).toNat*(2:ℚ)^(retentionBits n))).toNat) ∨
       ((bitsValue (mode.eval x)).toNat=3 ∧
        (bitsValue (c.eval x)).toNat<(Int.floor (remainderRetention n
          (bitsValue (d.eval x)).toNat (bitsValue (j.eval x)).toNat*(2:ℚ)^(retentionBits n))).toNat)) := by
  have h2 : 2<2^w := lt_of_lt_of_le (by decide : 2<2^2) (Nat.pow_le_pow_right (by decide) hw)
  have h3 : 3<2^w := lt_of_lt_of_le (by decide : 3<2^2) (Nat.pow_le_pow_right (by decide) hw)
  simp only [trialAcceptOn,eval_band,eval_bor,Bool.and_eq_true,Bool.or_eq_true,
    labelValidNet_value n a m d j hn x hm,wordLt_eval,decide_eq_true_eq,equalOn_value,
    wordConstant_eval,BitVec.toNat_ofNat,Nat.mod_eq_of_lt h2,Nat.mod_eq_of_lt h3]
  apply and_congr_right
  intro hv
  rw [firstRetNet_value n d j t c x hv.2.1.le hv.1,
    thirdRetNet_value n d j t c x hv.2.1.le hv.1]
  by_cases ht : (bitsValue (t.eval x)).toNat<(bitsValue (d.eval x)).toNat
  · rw [secondRetNet_value n d j t c x hv.2.1.le hv.1 ht]
  · simp only [ht,false_and,and_false]

/-- At the actually recovered/guessed pair, pair equality checks simplify but
sampler scratch selection and the actual recorded retention coin do not. -/
lemma labelEvent_self {u s n : ℕ} (a m : Basis u) (r : Raw u s n) :
    labelEvent s n a m (labelPair s n r).1 (labelPair s n r).2 r ↔
      (((bitsValue r.1).toNat<2 ∧ SampleSelected a m r.2.1 ∧
        Retains (firstRetention n (labelPair s n r).1 (labelPair s n r).2) r.2.2.2.2.2) ∨
       ((bitsValue r.1).toNat=2 ∧ (bitsValue r.2.2.2.2.1).toNat<(labelPair s n r).1 ∧
        Retains (discrepancyRetention n (labelPair s n r).1 (labelPair s n r).2
          (bitsValue r.2.2.2.2.1).toNat) r.2.2.2.2.2) ∨
       ((bitsValue r.1).toNat=3 ∧
        Retains (remainderRetention n (labelPair s n r).1 (labelPair s n r).2) r.2.2.2.2.2)) := by
  by_cases h : (bitsValue r.1).toNat<2
  · have h2 : (bitsValue r.1).toNat≠2 := by omega
    have h3 : (bitsValue r.1).toNat≠3 := by omega
    simp only [labelEvent,modeFirst,modeSecond,modeThird,h,h2,h3,true_and,false_and,
      or_false,firstPass,recovered,labelPair,ite_true,Prod.mk.eta,and_true]
  · simp only [labelEvent,modeFirst,modeSecond,modeThird,h,false_and,false_or,
      labelPair,ite_false,secondPass,thirdPass,true_and]

end ExactQuantumFactoring.OrderTrial


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/RawTrialDecoder.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.OrderTrial
open BooleanNetwork BitArithmetic

/-- Exact ordinary trial decoder, including the sampler's full workspace test,
continued-fraction reconstruction, arithmetic validation, and all three retained
coin tests. Its inputs are actual retained raw bits. -/
def rawAcceptNet {k u s n : ℕ} (a m : BooleanNetwork k u)
    (r : BooleanNetwork k (rawWidth u s n)) : BooleanNetwork k 1 :=
  trialAcceptOn n (toWidth (decodeWidth u s n) a) (toWidth (decodeWidth u s n) m)
    (toWidth (decodeWidth u s n) (rawMode r)) (trialDenNet r) (trialNumNet r)
    (toWidth (decodeWidth u s n) (rawResidue r)) (toWidth (decodeWidth u s n) (rawCoin r))
    (samplerSelectedNet a m (rawSample r))

lemma rawAcceptNet_value {k u s n : ℕ} (a m : BooleanNetwork k u)
    (r : BooleanNetwork k (rawWidth u s n)) (x : Basis k) (y : Raw u s n)
    (h : r.eval x=rawLayout u s n y) (hm : 2≤(bitsValue (m.eval x)).toNat) :
    (rawAcceptNet a m r).eval x 0=true ↔
      ValidLabel n (bitsValue (a.eval x)).toNat (bitsValue (m.eval x)).toNat
        (labelPair s n y).1 (labelPair s n y).2 ∧
      labelEvent s n (a.eval x) (m.eval x) (labelPair s n y).1 (labelPair s n y).2 y := by
  have hu : u≤decodeWidth u s n := by unfold decodeWidth; omega
  have hn : n<decodeWidth u s n := by unfold decodeWidth; omega
  have hw : 2≤decodeWidth u s n := by unfold decodeWidth; omega
  have hc : retentionBits n≤decodeWidth u s n := by unfold decodeWidth; omega
  have hm' : 2≤(bitsValue ((toWidth (decodeWidth u s n) m).eval x)).toNat := by
    rw [toWidth_value m hu]; exact hm
  rw [rawAcceptNet,trialAcceptOn_value _ _ _ _ _ _ _ _ _ hn hw x hm']
  simp only [toWidth_value a hu,toWidth_value m hu,toWidth_value (rawMode r) hw,
    toWidth_value (rawResidue r) hn.le,toWidth_value (rawCoin r) hc,
    trialDenNet_value r x y h,trialNumNet_value r x y h,
    rawMode_eval r x y h,rawResidue_eval r x y h,rawCoin_eval r x y h,
    samplerSelectedNet_eval,rawSample_eval r x y h]
  rw [labelEvent_self]
  rfl

def trialValueNet {k u s n : ℕ} (a m : BooleanNetwork k u)
    (r : BooleanNetwork k (rawWidth u s n)) : BooleanNetwork k (decodeWidth u s n) :=
  wordMux (rawAcceptNet a m r) (trialDenNet r) (wordConstant (BitVec.ofNat (decodeWidth u s n) 0))

lemma trialValueNet_value {k u s n : ℕ} (a m : BooleanNetwork k u)
    (r : BooleanNetwork k (rawWidth u s n)) (x : Basis k) (y : Raw u s n)
    (h : r.eval x=rawLayout u s n y) (hm : 2≤(bitsValue (m.eval x)).toNat) :
    (bitsValue ((trialValueNet a m r).eval x)).toNat=(trialResult s n (a.eval x) (m.eval x) y).getD 0 := by
  classical
  rw [trialValueNet,wordMux_eval]
  by_cases ht : (rawAcceptNet a m r).eval x 0=true
  · rw [ite_eq_left ht,trialDenNet_value r x y h]
    have hh := (rawAcceptNet_value a m r x y h hm).mp ht
    simp only [trialResult,ite_eq_left hh,Option.getD_some]
  · rw [ite_eq_right ht,wordConstant_eval,BitVec.toNat_ofNat,Nat.zero_mod]
    have hh := mt (rawAcceptNet_value a m r x y h hm).mpr ht
    simp only [trialResult,ite_eq_right hh,Option.getD_none]

lemma trialResult_getD_lt {u s n : ℕ} (a m : Basis u) (y : Raw u s n) :
    (trialResult s n a m y).getD 0<2^n := by
  classical
  unfold trialResult
  dsimp only
  split_ifs with h
  · exact h.1.2.1
  · change 0<2^n
    positivity

/-- Only VALID ordinary candidates are narrowed to n bits. This does not apply
to the separately completed rare guess, whose whole transition word is kept. -/
def trialSmallValueNet {k u s n : ℕ} (a m : BooleanNetwork k u)
    (r : BooleanNetwork k (rawWidth u s n)) : BooleanNetwork k n :=
  (trialValueNet a m r).comp (resizeWord (decodeWidth u s n) n)
lemma trialSmallValueNet_value {k u s n : ℕ} (a m : BooleanNetwork k u)
    (r : BooleanNetwork k (rawWidth u s n)) (x : Basis k) (y : Raw u s n)
    (h : r.eval x=rawLayout u s n y) (hm : 2≤(bitsValue (m.eval x)).toNat) :
    (bitsValue ((trialSmallValueNet a m r).eval x)).toNat=(trialResult s n (a.eval x) (m.eval x) y).getD 0 := by
  rw [trialSmallValueNet,eval_comp,resizeWord_value,BitVec.toNat_setWidth,
    trialValueNet_value a m r x y h hm,Nat.mod_eq_of_lt (trialResult_getD_lt _ _ _)]

end ExactQuantumFactoring.OrderTrial


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/MinimumCandidateCircuit.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.OrderTrial
open BooleanNetwork BitArithmetic

def minNonzero (a b : ℕ) : ℕ := if a=0 then b else if b=0 then a else min a b
lemma minNonzero_options (a b : Option ℕ)
    (ha : ∀ d, a=some d → 0<d) (hb : ∀ d, b=some d → 0<d) :
    minNonzero (a.getD 0) (b.getD 0)=(minOption a b).getD 0 := by
  cases a with
  | none => simp only [Option.getD_none,minNonzero,ite_true,minOption]
  | some a =>
    have hapos : a≠0 := (ha a rfl).ne'
    cases b with
    | none => simp only [Option.getD_none,Option.getD_some,minNonzero,ite_eq_right hapos,ite_true,minOption]
    | some b =>
      have hbpos : b≠0 := (hb b rfl).ne'
      simp only [Option.getD_some,minNonzero,ite_eq_right hapos,ite_eq_right hbpos,minOption]

def minimumChoice (w : ℕ) : BooleanNetwork (w+w) w :=
  let a := leftNet w w
  let b := rightNet w w
  wordMux (equalOn a (wordConstant (BitVec.ofNat w 0))) b
    (wordMux (equalOn b (wordConstant (BitVec.ofNat w 0))) a (wordMux (wordLt a b) a b))
lemma minimumChoice_value {w : ℕ} (a b : Basis w) :
    (bitsValue ((minimumChoice w).eval (Fin.append a b))).toNat=
      minNonzero (bitsValue a).toNat (bitsValue b).toNat := by
  have h₁ := equalOn_value (leftNet w w) (wordConstant (BitVec.ofNat w 0)) (Fin.append a b)
  have h₂ := equalOn_value (rightNet w w) (wordConstant (BitVec.ofNat w 0)) (Fin.append a b)
  simp only [leftNet_eval,rightNet_eval,wordConstant_eval,BitVec.toNat_ofNat,Nat.zero_mod] at h₁ h₂
  simp only [minimumChoice,wordMux_eval,leftNet_eval,rightNet_eval]
  simp only [h₁,h₂,wordLt_eval,leftNet_eval,rightNet_eval,decide_eq_true_eq]
  split_ifs with ha hb hab
  · simp only [minNonzero,ite_eq_left ha]
  · simp only [minNonzero,ite_eq_right ha,ite_eq_left hb]
  · simp only [minNonzero,ite_eq_right ha,ite_eq_right hb,min_eq_left hab.le]
  · simp only [minNonzero,ite_eq_right ha,ite_eq_right hb,min_eq_right (by omega : (bitsValue b).toNat≤(bitsValue a).toNat)]
lemma minimumChoice_count (w : ℕ) : (minimumChoice w).net.count≤300*w+60 := by
  have h₁ := equalOn_count (leftNet w w) (wordConstant (n:=w+w) (BitVec.ofNat w 0))
  have h₂ := equalOn_count (rightNet w w) (wordConstant (n:=w+w) (BitVec.ofNat w 0))
  have h₃ := wordLt_count (leftNet w w) (rightNet w w)
  simp only [leftNet,rightNet,count_select,wordConstant_count] at h₁ h₂ h₃
  simp only [minimumChoice,wordMux_count,leftNet,rightNet,count_select]
  omega

/-- Pair costly subnets ONCE before comparing; the recursive minimum is not
copied into each arm of the mux. This gives a linear, not exponential, scan. -/
def minimumNet {k w : ℕ} : {K : ℕ} → (Fin K → BooleanNetwork k w) → BooleanNetwork k w
  | 0,_ => wordConstant (BitVec.ofNat w 0)
  | _+1,f => ((f 0).pair (minimumNet (fun i => f i.succ))).comp (minimumChoice w)
lemma minimumNet_value {k w K : ℕ} (f : Fin K → BooleanNetwork k w) (x : Basis k)
    (g : Fin K → Option ℕ) (h : ∀ i,(bitsValue ((f i).eval x)).toNat=(g i).getD 0)
    (hp : ∀ i d,g i=some d→0<d) :
    (bitsValue ((minimumNet f).eval x)).toNat=(minimumCandidate (List.ofFn g)).getD 0 := by
  induction K with
  | zero => simp only [minimumNet,wordConstant_eval,BitVec.toNat_ofNat,Nat.zero_mod,
      List.ofFn_zero,minimumCandidate,Option.getD_none]
  | succ K ih =>
    rw [minimumNet,eval_comp,eval_pair,minimumChoice_value,h 0,
      ih (fun i=>f i.succ) (fun i=>g i.succ) (fun i=>h i.succ) (fun i=>hp i.succ),
      List.ofFn_succ,minimumCandidate]
    apply minNonzero_options _ _ (hp 0)
    intro d hd
    have hh := minimumCandidate_mem hd
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp hh
    exact hp i.succ d hi
lemma minimumNet_count {k w K c : ℕ} (f : Fin K → BooleanNetwork k w)
    (h : ∀ i,(f i).net.count≤c) : (minimumNet f).net.count≤w+K*(c+300*w+60) := by
  induction K with
  | zero => simp only [minimumNet,wordConstant_count,zero_mul,add_zero,le_refl]
  | succ K ih =>
    have hh := ih (fun i=>f i.succ) (fun i=>h i.succ)
    have hc := minimumChoice_count w
    rw [minimumNet,count_comp,count_pair]
    have h0 := h 0
    nlinarith

end ExactQuantumFactoring.OrderTrial


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/PhysicalOrderDecoder.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic OrderTrial

lemma resizeWord_eq_natBasis {u w : ℕ} (x : Basis u) :
    (resizeWord u w).eval x=natBasis w (bitsValue x).toNat := by
  apply (bitsEquiv w).injective
  apply BitVec.eq_of_toNat_eq
  change (bitsValue ((resizeWord u w).eval x)).toNat = (bitsValue (natBasis w (bitsValue x).toNat)).toNat
  rw [resizeWord_value,BitVec.toNat_setWidth,natBasis_value]

namespace OrderSlots

def usableOn {k n : ℕ} (a m : BooleanNetwork k n) : BooleanNetwork k 1 :=
  (wordLt a m).band (equalOn ((a.pair m).comp (gcdNet n)) (wordConstant (BitVec.ofNat n 1)))
lemma usableOn_value {k n : ℕ} (a m : BooleanNetwork k n) (x : Basis k) (hn : 1≤n) :
    (usableOn a m).eval x 0=true ↔ Usable (a.eval x) (m.eval x) := by
  have h1 : 1<2^n := Nat.one_lt_two_pow (by omega)
  simp only [usableOn,eval_band,Bool.and_eq_true,wordLt_eval,decide_eq_true_eq,equalOn_value,
    eval_comp,eval_pair,gcdNet_value,wordConstant_eval,BitVec.toNat_ofNat,Nat.mod_eq_of_lt h1,
    Usable,ZMod.isUnit_iff_coprime,Nat.Coprime]
lemma usableOn_count {k n : ℕ} (a m : BooleanNetwork k n) :
    (usableOn a m).net.count≤2*a.net.count+2*m.net.count+
      2*n*(216*n*n+300*n+100)+145*n+30 := by
  have he := equalOn_count ((a.pair m).comp (gcdNet n)) (wordConstant (n:=k) (BitVec.ofNat n 1))
  have hl := wordLt_count a m
  have hg := gcdNet_count n
  simp only [count_comp,count_pair,wordConstant_count] at he
  rw [usableOn,count_band]
  omega

/-- Every ordinary raw trial uses its actual tensor block. Nonempty candidates
are validated before a shared, linear-size least-positive-candidate fold. -/
def orderResultNet {k n : ℕ} (a m : BooleanNetwork k n)
    (raw : BooleanNetwork k (ordinaryWidth n)) : BooleanNetwork k n :=
  minimumNet (fun i : Fin (n^5) => trialSmallValueNet a m
    (raw.comp (tensorSelect (rawWidth n (sampleExponent n) n) (n^5) i)))
lemma orderResultNet_value {k n : ℕ} (a m : BooleanNetwork k n)
    (raw : BooleanNetwork k (ordinaryWidth n)) (x : Basis k)
    (y : Fin (n^5)→Raw n (sampleExponent n) n) (h : raw.eval x=ordinaryLayout n y)
    (hm : 2≤(bitsValue (m.eval x)).toNat) :
    (bitsValue ((orderResultNet a m raw).eval x)).toNat=
      orderResult (sampleExponent n) n (a.eval x) (m.eval x) (n^5) y := by
  apply minimumNet_value _ x (fun i=>trialResult (sampleExponent n) n (a.eval x) (m.eval x) (y i))
  · intro i
    apply trialSmallValueNet_value _ _ _ x (y i) _ hm
    rw [eval_comp,h]
    exact tensorSelect_eval _ i
  · intro i d hd
    exact ((trialResult_some _ _ _).mp hd).choose_spec.1.1

def ordinaryOn {k n : ℕ} (a m : BooleanNetwork k n)
    (raw : BooleanNetwork k (ordinaryWidth n)) : BooleanNetwork k (Completion.transitionWidth n) :=
  (wordMux (usableOn a m) (orderResultNet a m raw) (wordConstant (BitVec.ofNat n 0))).comp
    (resizeWord n (Completion.transitionWidth n))
lemma ordinaryOn_eval {k n : ℕ} (a m : BooleanNetwork k n)
    (raw : BooleanNetwork k (ordinaryWidth n)) (x : Basis k)
    (y : Fin (n^5)→Raw n (sampleExponent n) n) (h : raw.eval x=ordinaryLayout n y)
    (hn : 1≤n) (hm : 2≤(bitsValue (m.eval x)).toNat) :
    (ordinaryOn a m raw).eval x=ordinary (a.eval x) (m.eval x) y := by
  classical
  rw [ordinaryOn,eval_comp,resizeWord_eq_natBasis,wordMux_eval]
  simp only [usableOn_value a m x hn]
  by_cases hu : Usable (a.eval x) (m.eval x)
  · rw [ite_eq_left hu,orderResultNet_value a m raw x y h hm,ordinary,ite_eq_left hu]
  · rw [ite_eq_right hu,wordConstant_eval,BitVec.toNat_ofNat,Nat.zero_mod,ordinary,ite_eq_right hu]

/-- Completed output decoding keeps the FULL rare guessed transition word. No
truncation, success flag, or later true-order certificate enters this decoder. -/
def outputOn {k n : ℕ} (a m : BooleanNetwork k n) (raw : BooleanNetwork k (width n)) :
    BooleanNetwork k (Completion.transitionWidth n) :=
  wordMux (raw.comp (Completion.rareNet (ordinaryWidth n) (Completion.transitionWidth n) (2*n) ((n+10)*n^5)))
    (raw.comp (Completion.guessWires (ordinaryWidth n) (Completion.transitionWidth n) (2*n) ((n+10)*n^5)))
    (ordinaryOn a m (raw.comp (Completion.ordinaryWires (ordinaryWidth n) (Completion.transitionWidth n) (2*n) ((n+10)*n^5))))
lemma outputOn_eval {k n : ℕ} (a m : BooleanNetwork k n) (raw : BooleanNetwork k (width n))
    (x : Basis k) (y : Result n) (h : raw.eval x=layout n y) (hn : 1≤n)
    (hm : 2≤(bitsValue (m.eval x)).toNat) :
    (outputOn a m raw).eval x=output (a.eval x) (m.eval x) y := by
  let z : Completion.Raw (Basis (ordinaryWidth n)) (Completion.transitionWidth n) (2*n) ((n+10)*n^5) :=
    (y.1,ordinaryLayout n y.2.1,y.2.2)
  have hz : layout n y=Completion.layout (ordinaryWidth n) (Completion.transitionWidth n) (2*n) ((n+10)*n^5) z := rfl
  have ho : (raw.comp (Completion.ordinaryWires (ordinaryWidth n) (Completion.transitionWidth n) (2*n) ((n+10)*n^5))).eval x=
      ordinaryLayout n y.2.1 := by
    rw [eval_comp,h,hz,Completion.ordinaryWires_eval]
  rw [outputOn,wordMux_eval,ordinaryOn_eval a m _ x y.2.1 ho hn hm]
  simp only [eval_comp,h,hz,Completion.guessWires_eval,Completion.rareNet_eval,output,Completion.output,z]

end OrderSlots
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/BoundedStack.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork

/-- A fixed-capacity little-endian word stack. No dynamic address or unbounded
list is part of the corresponding Boolean network. -/
def stackEncoding (s w : ℕ) (xs : List (Basis w)) : Basis (s*w) := fun j =>
  let ij := finProdFinEquiv.symm j
  (xs[ij.1.val]?.getD (fun _ => false)) ij.2

lemma block_stackEncoding (s w : ℕ) (xs : List (Basis w)) (i : Fin s) :
    block (stackEncoding s w xs) i = xs[i.val]?.getD (fun _ => false) := by
  funext j
  simp [block,stackEncoding]

/-- Pop the top, padding the empty end with zero. -/
def stackPop (s w : ℕ) : BooleanNetwork (s*w) (s*w) :=
  wordBlocks (fun i : Fin s => if h : i.val+1<s then blockNet s w ⟨i.val+1,h⟩
    else wordConstant 0)

/-- Push a word; the last slot is dropped. Capacity is verified separately in
controller invariants, rather than silently growing the physical width. -/
def stackPush {k s w : ℕ} (a : BooleanNetwork k w) (v : BooleanNetwork k (s*w)) :
    BooleanNetwork k (s*w) :=
  wordBlocks (fun i : Fin s => if h : i.val=0 then a
    else v.comp (blockNet s w ⟨i.val-1,by omega⟩))

lemma stackPop_value {s w : ℕ} (x : Basis (s*w)) (i : Fin s) :
    block ((stackPop s w).eval x) i =
      if h : i.val+1<s then block x ⟨i.val+1,h⟩ else (fun _ => false) := by
  rw [stackPop,wordBlocks_eval]
  split_ifs
  · rfl
  · funext j
    simp [wordConstant]

lemma stackPush_value {k s w : ℕ} (a : BooleanNetwork k w) (v : BooleanNetwork k (s*w))
    (x : Basis k) (i : Fin s) :
    block ((stackPush a v).eval x) i =
      if _h : i.val=0 then a.eval x else block (v.eval x) ⟨i.val-1,by omega⟩ := by
  rw [stackPush,wordBlocks_eval]
  split_ifs <;> rfl

lemma block_ext {s w : ℕ} {x y : Basis (s*w)}
    (h : ∀ i : Fin s, block x i=block y i) : x=y := by
  funext j
  obtain ⟨⟨i,k⟩,rfl⟩ := finProdFinEquiv.surjective j
  exact congrFun (h i) k

lemma stackPop_encoding {s w : ℕ} (xs : List (Basis w)) (h : xs.length ≤ s) :
    (stackPop s w).eval (stackEncoding s w xs)=stackEncoding s w xs.tail := by
  apply block_ext
  intro i
  rw [stackPop_value,block_stackEncoding]
  split_ifs with hi
  · rw [block_stackEncoding]
    cases xs <;> simp
  · have hh : xs.tail[i.val]?=none := by
      apply List.getElem?_eq_none
      simp only [List.length_tail]
      omega
    rw [hh]
    rfl

lemma stackPush_encoding {k s w : ℕ} (a : BooleanNetwork k w) (v : BooleanNetwork k (s*w))
    (x : Basis k) (xs : List (Basis w)) (hv : v.eval x=stackEncoding s w xs) :
    (stackPush a v).eval x=stackEncoding s w (a.eval x::xs) := by
  apply block_ext
  intro i
  rw [stackPush_value,block_stackEncoding]
  split_ifs with hi
  · simp [hi]
  · rw [hv,block_stackEncoding]
    obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero hi
    simp [hj]

lemma stackPop_count (s w : ℕ) : (stackPop s w).net.count ≤ s*w*w := by
  apply wordBlocks_count
  intro i
  by_cases hi : i.val+1<s
  · have he : (if h : i.val+1<s then blockNet s w ⟨i.val+1,h⟩ else wordConstant 0) =
        blockNet s w ⟨i.val+1,hi⟩ := dite_eq_left hi
    have hh := congrArg (fun c : BooleanNetwork (s*w) w => c.net.count) he
    rw [hh,blockNet_count]
    omega
  · have he : (if h : i.val+1<s then blockNet s w ⟨i.val+1,h⟩ else wordConstant 0) =
        wordConstant 0 := dite_eq_right hi
    have hh := congrArg (fun c : BooleanNetwork (s*w) w => c.net.count) he
    rw [hh,wordConstant_count]

lemma stackPush_count {k s w : ℕ} (a : BooleanNetwork k w) (v : BooleanNetwork k (s*w)) :
    (stackPush a v).net.count ≤ s*w*(a.net.count+v.net.count) := by
  apply wordBlocks_count
  intro i
  by_cases hi : i.val=0
  · have he : (if h : i.val=0 then a else v.comp (blockNet s w ⟨i.val-1,by omega⟩))=a := dite_eq_left hi
    have hh := congrArg (fun c : BooleanNetwork k w => c.net.count) he
    rw [hh]
    omega
  · have he : (if h : i.val=0 then a else v.comp (blockNet s w ⟨i.val-1,by omega⟩))=
        v.comp (blockNet s w ⟨i.val-1,by omega⟩) := dite_eq_right hi
    have hh := congrArg (fun c : BooleanNetwork k w => c.net.count) he
    rw [hh,count_comp,blockNet_count]
    omega

end ExactQuantumFactoring.BitArithmetic


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/NodeControlCircuit.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork FactorController

def properOn {k w : ℕ} (m d : BooleanNetwork k w) : BooleanNetwork k 1 :=
  ((wordLt (wordConstant (BitVec.ofNat w 1)) d).band (wordLt d m)).band
    (zeroWord ((m.pair d).comp (mod w)))

lemma properOn_value {k w : ℕ} (hw : 0<w) (m d : BooleanNetwork k w) (x : Basis k) :
    (properOn m d).eval x 0=true ↔ ProperDivisor (bitsValue (m.eval x)).toNat
      (bitsValue (d.eval x)).toNat := by
  have h1 : 1<2^w := Nat.one_lt_pow (by omega) (by decide)
  rw [properOn,eval_band,Bool.and_eq_true,eval_band,Bool.and_eq_true,
    wordLt_eval,wordLt_eval,decide_eq_true_eq,decide_eq_true_eq,wordConstant_eval,
    BitVec.toNat_ofNat,Nat.mod_eq_of_lt h1,zeroWord_value,eval_comp,eval_pair,
    mod_word,BitVec.toNat_umod,←Nat.dvd_iff_mod_eq_zero]
  exact and_assoc

namespace NodeCircuit

abbrev width (s w : ℕ) := (s+1)*w+w

def pending (s w : ℕ) : BooleanNetwork (width s w) ((s+1)*w) := select (Fin.castAdd w)
def divisor (s w : ℕ) : BooleanNetwork (width s w) w := select (Fin.natAdd ((s+1)*w))
def top (s w : ℕ) : BooleanNetwork (width s w) w :=
  (pending s w).comp (blockNet (s+1) w 0)
def popped (s w : ℕ) : BooleanNetwork (width s w) ((s+1)*w) :=
  (pending s w).comp (stackPop (s+1) w)
def quotient (s w : ℕ) : BooleanNetwork (width s w) w :=
  ((top s w).pair (divisor s w)).comp (div w)
def isPrime (s w : ℕ) : BooleanNetwork (width s w) 1 := (top s w).comp (primeWord w)
def isDone (s w : ℕ) : BooleanNetwork (width s w) 1 := zeroWord (top s w)
def isProper (s w : ℕ) : BooleanNetwork (width s w) 1 := properOn (top s w) (divisor s w)
def split (s w : ℕ) : BooleanNetwork (width s w) ((s+1)*w) :=
  stackPush (divisor s w) (stackPush (quotient s w) (popped s w))

def next (s w : ℕ) : BooleanNetwork (width s w) ((s+1)*w) :=
  wordMux (isDone s w) (pending s w)
    (wordMux (isPrime s w) (popped s w) (wordMux (isProper s w) (split s w) (pending s w)))
def emitted (s w : ℕ) : BooleanNetwork (width s w) w :=
  wordMux (isPrime s w) (top s w) (wordConstant 0)
def failed (s w : ℕ) : BooleanNetwork (width s w) 1 :=
  ((isDone s w).bnot.band (isPrime s w).bnot).band (isProper s w).bnot

def step (s w : ℕ) : BooleanNetwork (width s w) (width s w+1) :=
  ((next s w).pair (emitted s w)).pair (failed s w)

def pack {s w : ℕ} (xs : List (Basis w)) (d : Basis w) : Basis (width s w) :=
  Fin.append (stackEncoding (s+1) w xs) d

@[simp] lemma pending_pack {s w : ℕ} (xs : List (Basis w)) (d : Basis w) :
    (pending s w).eval (pack xs d)=stackEncoding (s+1) w xs := by
  funext i
  exact Fin.append_left _ _ i
@[simp] lemma divisor_pack {s w : ℕ} (xs : List (Basis w)) (d : Basis w) :
    (divisor s w).eval (pack xs d)=d := by
  funext i
  exact Fin.append_right _ _ i
@[simp] lemma top_pack {s w : ℕ} (xs : List (Basis w)) (d : Basis w) :
    (top s w).eval (pack xs d)=xs.head?.getD (fun _=>false) := by
  rw [top,eval_comp,pending_pack,blockNet_eval,block_stackEncoding]
  cases xs <;> rfl

lemma popped_pack {s w : ℕ} (xs : List (Basis w)) (d : Basis w) (h : xs.length ≤ s+1) :
    (popped s w).eval (pack xs d)=stackEncoding (s+1) w xs.tail := by
  rw [popped,eval_comp,pending_pack,stackPop_encoding xs h]

lemma quotient_pack {s w : ℕ} (a d : Basis w) (xs : List (Basis w)) :
    (bitsValue ((quotient s w).eval (pack (a::xs) d))).toNat =
      (bitsValue a).toNat/(bitsValue d).toNat := by
  rw [quotient,eval_comp,eval_pair,div_word,top_pack,divisor_pack]
  rfl

lemma split_pack {s w : ℕ} (a d : Basis w) (xs : List (Basis w)) (h : xs.length ≤ s) :
    (split s w).eval (pack (a::xs) d)=stackEncoding (s+1) w
      (d::(quotient s w).eval (pack (a::xs) d)::xs) := by
  rw [split,stackPush_encoding _ _ _ _
    (stackPush_encoding _ _ _ _ (popped_pack (a::xs) d (by simp;omega))),divisor_pack]
  rfl

lemma isPrime_pack {s w : ℕ} (hw : 128 ≤ w) (a d : Basis w) (xs : List (Basis w)) :
    (isPrime s w).eval (pack (a::xs) d) 0=true ↔ (bitsValue a).toNat.Prime := by
  rw [isPrime,eval_comp,top_pack]
  exact primeWord_value hw _

lemma isProper_pack {s w : ℕ} (hw : 0<w) (a d : Basis w) (xs : List (Basis w)) :
    (isProper s w).eval (pack (a::xs) d) 0=true ↔
      ProperDivisor (bitsValue a).toNat (bitsValue d).toNat := by
  rw [isProper,properOn_value hw,top_pack,divisor_pack]
  rfl

lemma isDone_pack {s w : ℕ} (xs : List (Basis w)) (d : Basis w) :
    (isDone s w).eval (pack xs d) 0=true ↔
      (bitsValue (xs.head?.getD (fun _=>false))).toNat=0 := by
  rw [isDone,zeroWord_value,top_pack]

/-- Literal guarded stack update for one node of the recursive producer.
The source primality test is the Boolean AKS circuit, and division is a full
word division circuit. No semantic factorization operation is used here. -/
lemma next_pack_cons {s w : ℕ} (hw : 128 ≤ w) (a d : Basis w) (xs : List (Basis w))
    (h : xs.length ≤ s) (ha : 2 ≤ (bitsValue a).toNat) :
    (next s w).eval (pack (a::xs) d)=
      if (bitsValue a).toNat.Prime then stackEncoding (s+1) w xs
      else if ProperDivisor (bitsValue a).toNat (bitsValue d).toNat then
        stackEncoding (s+1) w (d::(quotient s w).eval (pack (a::xs) d)::xs)
      else stackEncoding (s+1) w (a::xs) := by
  rw [next,wordMux_eval,ite_eq_right (by
    rw [isDone_pack]
    simp only [List.head?_cons,Option.getD_some]
    omega),wordMux_eval,wordMux_eval,pending_pack,
    popped_pack (a::xs) d (by simp;omega),split_pack a d xs h]
  simp only [List.tail_cons]
  simp only [isPrime_pack hw,isProper_pack (by omega : 0<w)]

lemma emitted_pack_cons {s w : ℕ} (hw : 128 ≤ w) (a d : Basis w) (xs : List (Basis w)) :
    (emitted s w).eval (pack (a::xs) d)=
      if (bitsValue a).toNat.Prime then a else (fun _=>false) := by
  rw [emitted,wordMux_eval,top_pack]
  simp only [List.head?_cons,Option.getD_some,isPrime_pack hw]
  split_ifs
  · rfl
  · funext i
    simp [wordConstant]

lemma failed_pack_cons {s w : ℕ} (hw : 128 ≤ w) (a d : Basis w) (xs : List (Basis w))
    (ha : 2 ≤ (bitsValue a).toNat) :
    (failed s w).eval (pack (a::xs) d) 0=true ↔
      ¬(bitsValue a).toNat.Prime ∧ ¬ProperDivisor (bitsValue a).toNat (bitsValue d).toNat := by
  rw [failed,eval_band,Bool.and_eq_true,eval_band,Bool.and_eq_true,bnot_value,bnot_value,
    bnot_value,isDone_pack,isPrime_pack hw,isProper_pack (by omega : 0<w)]
  simp only [List.head?_cons,Option.getD_some]
  have h0 : (bitsValue a).toNat≠0 := by omega
  simp only [h0,not_false_eq_true,true_and]

end NodeCircuit
end ExactQuantumFactoring.BitArithmetic


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/SuppliedDivisorCircuit.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
namespace Primality
lemma rootSearch_lt (m e k g : ℕ) : rootSearch m e k g < g+2^k := by
  induction k generalizing g with
  | zero => simp [rootSearch]
  | succ k ih =>
    simp only [rootSearch]
    split_ifs with h
    · have hh := ih (g+2^k)
      rw [pow_succ]
      omega
    · have hh := ih g
      rw [pow_succ]
      omega
lemma boundedRoot_lt (m e n : ℕ) : boundedRoot m e n < 2^n := by
  simpa only [boundedRoot,zero_add] using rootSearch_lt m e n 0
end Primality

namespace BitArithmetic
open BooleanNetwork FactorController

def firstProperNet {k w : ℕ} (m : BooleanNetwork k w) :
    List (BooleanNetwork k w) → BooleanNetwork k w
  | [] => wordConstant 0
  | d::ds => wordMux (properOn m d) d (firstProperNet m ds)

lemma firstProperNet_value {k w : ℕ} (hw : 0<w) (m : BooleanNetwork k w)
    (ds : List (BooleanNetwork k w)) (x : Basis k) :
    (bitsValue ((firstProperNet m ds).eval x)).toNat =
      firstProper (bitsValue (m.eval x)).toNat (ds.map (fun d => (bitsValue (d.eval x)).toNat)) := by
  induction ds with
  | nil => simp [firstProperNet,firstProper,wordConstant_eval]
  | cons d ds ih =>
    rw [firstProperNet,wordMux_eval]
    simp only [properOn_value hw,List.map_cons,firstProper]
    split_ifs <;> simp_all

def evenOn {k w : ℕ} (m : BooleanNetwork k w) : BooleanNetwork k 1 :=
  zeroWord ((m.pair (wordConstant (BitVec.ofNat w 2))).comp (mod w))
lemma evenOn_value {k w : ℕ} (hw : 2≤w) (m : BooleanNetwork k w) (x : Basis k) :
    (evenOn m).eval x 0=true ↔ 2∣(bitsValue (m.eval x)).toNat := by
  have h2 : 2<2^w := (by norm_num : 2<2^2).trans_le (Nat.pow_le_pow_right (by decide) hw)
  rw [evenOn,zeroWord_value,eval_comp,eval_pair,mod_word,BitVec.toNat_umod,
    wordConstant_eval,BitVec.toNat_ofNat,Nat.mod_eq_of_lt h2,Nat.dvd_iff_mod_eq_zero]

def candidateOn {k w : ℕ} (a m d : BooleanNetwork k w) : BooleanNetwork k w :=
  wordMux ((zeroWord d).bnot.band (evenOn d)) (splitRawOn a m d) (wordConstant 0)
lemma candidateOn_value {k w n : ℕ} (hwn : w=n+1) (hw : 2≤w)
    (a m d : BooleanNetwork k w) (x : Basis k)
    (hm : 2≤(bitsValue (m.eval x)).toNat) (hb : (bitsValue (m.eval x)).toNat<2^n) :
    (bitsValue ((candidateOn a m d).eval x)).toNat = candidateDivisor
      (bitsValue (m.eval x)).toNat (bitsValue (a.eval x)).toNat (bitsValue (d.eval x)).toNat := by
  rw [candidateOn,wordMux_eval]
  simp only [eval_band,Bool.and_eq_true,bnot_value,zeroWord_value,evenOn_value hw]
  have hpos : ¬(bitsValue (d.eval x)).toNat=0 ↔ 0<(bitsValue (d.eval x)).toNat := by omega
  simp only [hpos,candidateDivisor]
  split_ifs
  · exact splitRawOn_value hwn hw a m d x hm hb
  · simp [wordConstant_eval]

def rootOn {k : ℕ} (n e : ℕ) (m : BooleanNetwork k (n+1)) : BooleanNetwork k (n+1) :=
  ((m.comp (resizeWord (n+1) (rootWidth n))).comp (boundedRootNet n e)).comp
    (resizeWord (rootWidth n) (n+1))
lemma rootOn_value {k n e : ℕ} (hn : 0<n) (he : e≤n)
    (m : BooleanNetwork k (n+1)) (x : Basis k) :
    (bitsValue ((rootOn n e m).eval x)).toNat=Primality.boundedRoot (bitsValue (m.eval x)).toNat e n := by
  have hw : n+1≤rootWidth n := by dsimp [rootWidth]; nlinarith
  rw [rootOn,eval_comp,resizeWord_value,BitVec.toNat_setWidth,eval_comp,
    boundedRootNet_value n e he,eval_comp,resizeWord_toNat hw]
  exact Nat.mod_eq_of_lt ((Primality.boundedRoot_lt _ _ _).trans
    (Nat.pow_lt_pow_right (by decide) (by omega)))

def rootsOn {k : ℕ} (n : ℕ) (m : BooleanNetwork k (n+1)) : BooleanNetwork k (n+1) :=
  firstProperNet m ((List.range (n+1)).map (fun e => rootOn n e m))
lemma rootsOn_value {k n : ℕ} (hn : 0<n) (m : BooleanNetwork k (n+1)) (x : Basis k) :
    (bitsValue ((rootsOn n m).eval x)).toNat=rootSplit (bitsValue (m.eval x)).toNat n := by
  rw [rootsOn,firstProperNet_value (by omega),rootSplit,rootProposals,List.map_map]
  congr 1
  apply List.map_congr_left
  intro e he
  exact rootOn_value hn (by have hh := List.mem_range.mp he; omega) m x

def ordersOn {k w : ℕ} (m : BooleanNetwork k w)
    (ars : List (BooleanNetwork k w × BooleanNetwork k w)) : BooleanNetwork k w :=
  firstProperNet m (ars.map (fun ar => candidateOn ar.1 m ar.2))
lemma ordersOn_value {k n : ℕ} (hn : 0<n) (m : BooleanNetwork k (n+1))
    (ars : List (BooleanNetwork k (n+1) × BooleanNetwork k (n+1))) (x : Basis k)
    (hm : 2≤(bitsValue (m.eval x)).toNat) (hb : (bitsValue (m.eval x)).toNat<2^n) :
    (bitsValue ((ordersOn m ars).eval x)).toNat=orderSplit (bitsValue (m.eval x)).toNat
      (ars.map (fun ar => ((bitsValue (ar.1.eval x)).toNat,(bitsValue (ar.2.eval x)).toNat))) := by
  rw [ordersOn,firstProperNet_value (by omega),orderSplit,List.map_map,List.map_map]
  congr 1
  apply List.map_congr_left
  intro ar _
  exact candidateOn_value rfl (by omega) ar.1 m ar.2 x hm hb

def suppliedOn {k : ℕ} (n : ℕ) (m : BooleanNetwork k (n+1))
    (ars : List (BooleanNetwork k (n+1) × BooleanNetwork k (n+1))) : BooleanNetwork k (n+1) :=
  wordMux (evenOn m) (wordConstant (BitVec.ofNat (n+1) 2))
    (wordMux (properOn m (rootsOn n m)) (rootsOn n m) (ordersOn m ars))

/-- The actual even/root/order implementation. No factorization information is
used in this decoder, and all loops are fixed by n and the number of slots. -/
theorem suppliedOn_value {k n : ℕ} (hn : 0<n) (m : BooleanNetwork k (n+1))
    (ars : List (BooleanNetwork k (n+1) × BooleanNetwork k (n+1))) (x : Basis k)
    (hm : 2≤(bitsValue (m.eval x)).toNat) (hb : (bitsValue (m.eval x)).toNat<2^n) :
    (bitsValue ((suppliedOn n m ars).eval x)).toNat=suppliedDivisor (bitsValue (m.eval x)).toNat n
      (ars.map (fun ar => ((bitsValue (ar.1.eval x)).toNat,(bitsValue (ar.2.eval x)).toNat))) := by
  simp only [suppliedOn,wordMux_eval,evenOn_value (by omega : 2≤n+1),
    properOn_value (by omega : 0<n+1),rootsOn_value hn,suppliedDivisor]
  split_ifs
  · rw [wordConstant_eval,BitVec.toNat_ofNat,Nat.mod_eq_of_lt]
    exact (by norm_num : 2<2^2).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  · exact rootsOn_value hn m x
  · exact ordersOn_value hn m ars x hm hb

end BitArithmetic
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/WideSplitCircuit.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork FactorController

/-- The exponent word may be the entire completion-guess width. In particular
an arbitrary rare-branch guess is NOT silently truncated to n bits. -/
def halfPowerBits {k w e : ℕ} (a m : BooleanNetwork k w) (d : BooleanNetwork k e) : BooleanNetwork k w :=
  ((a.pair m).pair ((halfWord d).rewire Fin.rev)).comp (modularPower w e)
lemma halfPowerBits_value {k w e : ℕ} (he : 2≤e) (a m : BooleanNetwork k w)
    (d : BooleanNetwork k e) (x : Basis k) (hm : 2≤(bitsValue (m.eval x)).toNat) :
    (bitsValue ((halfPowerBits a m d).eval x)).toNat=
      (bitsValue (a.eval x)).toNat^((bitsValue (d.eval x)).toNat/2)%(bitsValue (m.eval x)).toNat := by
  have hh : horner (((halfWord d).rewire Fin.rev).eval x) e le_rfl=(bitsValue (d.eval x)).toNat/2 := by
    rw [horner_full,Triangular.inputNumber_reverse]
    have hr : reverseBits e (((halfWord d).rewire Fin.rev).eval x)=(halfWord d).eval x := by
      funext i
      simp [reverseBits,eval_rewire]
    rw [hr,halfWord_value he]
  rw [halfPowerBits,eval_comp,eval_pair,eval_pair,modularPower_value _ _ _ hm,hh]

def shiftedHalfBits {k w e : ℕ} (a m : BooleanNetwork k w) (d : BooleanNetwork k e) : BooleanNetwork k w :=
  ((((halfPowerBits a m d).pair m).comp (add w)).pair
    (wordConstant (BitVec.ofNat w 1))).comp (sub w)
lemma shiftedHalfBits_value {k n e : ℕ} (he : 2≤e) (a m : BooleanNetwork k (n+1))
    (d : BooleanNetwork k e) (x : Basis k) (hm : 2≤(bitsValue (m.eval x)).toNat)
    (hb : (bitsValue (m.eval x)).toNat<2^n) :
    (bitsValue ((shiftedHalfBits a m d).eval x)).toNat=
      (bitsValue (a.eval x)).toNat^((bitsValue (d.eval x)).toNat/2)%
        (bitsValue (m.eval x)).toNat+(bitsValue (m.eval x)).toNat-1 := by
  have hp := Nat.mod_lt ((bitsValue (a.eval x)).toNat^((bitsValue (d.eval x)).toNat/2))
    (by omega : 0<(bitsValue (m.eval x)).toNat)
  have hsum : (bitsValue (a.eval x)).toNat^((bitsValue (d.eval x)).toNat/2)%
      (bitsValue (m.eval x)).toNat+(bitsValue (m.eval x)).toNat<2^(n+1) := by
    rw [pow_succ]; omega
  have h1 : 1<2^(n+1) := Nat.one_lt_two_pow (by omega)
  rw [shiftedHalfBits,eval_comp,eval_pair,sub_word,eval_comp,eval_pair,add_word,
    wordConstant_eval,BitVec.toNat_sub,BitVec.toNat_add,halfPowerBits_value he _ _ _ _ hm,
    Nat.mod_eq_of_lt hsum,BitVec.toNat_ofNat,Nat.mod_eq_of_lt h1]
  let v := (bitsValue (a.eval x)).toNat^((bitsValue (d.eval x)).toNat/2)%
    (bitsValue (m.eval x)).toNat
  let M := (bitsValue (m.eval x)).toNat
  change (2^(n+1)-1+(v+M))%2^(n+1)=v+M-1
  have hh : 2^(n+1)-1+(v+M)=2^(n+1)+(v+M-1) := by dsimp [v,M];omega
  rw [hh,Nat.add_mod,Nat.mod_self,zero_add,Nat.mod_mod,Nat.mod_eq_of_lt (by dsimp [v,M];omega)]

def candidateBits {k w e : ℕ} (a m : BooleanNetwork k w) (d : BooleanNetwork k e) : BooleanNetwork k w :=
  wordMux ((zeroWord d).bnot.band (evenOn d))
    (((shiftedHalfBits a m d).pair m).comp (gcdNet w)) (wordConstant 0)
lemma candidateBits_value {k n e : ℕ} (he : 2≤e) (a m : BooleanNetwork k (n+1))
    (d : BooleanNetwork k e) (x : Basis k) (hm : 2≤(bitsValue (m.eval x)).toNat)
    (hb : (bitsValue (m.eval x)).toNat<2^n) :
    (bitsValue ((candidateBits a m d).eval x)).toNat=candidateDivisor
      (bitsValue (m.eval x)).toNat (bitsValue (a.eval x)).toNat (bitsValue (d.eval x)).toNat := by
  have hpos : ¬(bitsValue (d.eval x)).toNat=0 ↔ 0<(bitsValue (d.eval x)).toNat := by omega
  simp only [candidateBits,wordMux_eval,eval_band,Bool.and_eq_true,bnot_value,
    zeroWord_value,evenOn_value he,hpos,candidateDivisor]
  split_ifs
  · rw [eval_comp,eval_pair,gcdNet_value,shiftedHalfBits_value he _ _ _ _ hm hb]
  · simp [wordConstant_eval]

def ordersBits {k w e : ℕ} (m : BooleanNetwork k w)
    (ars : List (BooleanNetwork k w × BooleanNetwork k e)) : BooleanNetwork k w :=
  firstProperNet m (ars.map (fun ar => candidateBits ar.1 m ar.2))
lemma ordersBits_value {k n e : ℕ} (he : 2≤e) (m : BooleanNetwork k (n+1))
    (ars : List (BooleanNetwork k (n+1) × BooleanNetwork k e)) (x : Basis k)
    (hm : 2≤(bitsValue (m.eval x)).toNat) (hb : (bitsValue (m.eval x)).toNat<2^n) :
    (bitsValue ((ordersBits m ars).eval x)).toNat=orderSplit (bitsValue (m.eval x)).toNat
      (ars.map (fun ar => ((bitsValue (ar.1.eval x)).toNat,(bitsValue (ar.2.eval x)).toNat))) := by
  rw [ordersBits,firstProperNet_value (by omega),orderSplit,List.map_map,List.map_map]
  congr 1
  apply List.map_congr_left
  intro ar _
  exact candidateBits_value he ar.1 m ar.2 x hm hb

def suppliedBits {k e : ℕ} (n : ℕ) (m : BooleanNetwork k (n+1))
    (ars : List (BooleanNetwork k (n+1) × BooleanNetwork k e)) : BooleanNetwork k (n+1) :=
  wordMux (evenOn m) (wordConstant (BitVec.ofNat (n+1) 2))
    (wordMux (properOn m (rootsOn n m)) (rootsOn n m) (ordersBits m ars))
theorem suppliedBits_value {k n e : ℕ} (hn : 0<n) (he : 2≤e) (m : BooleanNetwork k (n+1))
    (ars : List (BooleanNetwork k (n+1) × BooleanNetwork k e)) (x : Basis k)
    (hm : 2≤(bitsValue (m.eval x)).toNat) (hb : (bitsValue (m.eval x)).toNat<2^n) :
    (bitsValue ((suppliedBits n m ars).eval x)).toNat=suppliedDivisor (bitsValue (m.eval x)).toNat n
      (ars.map (fun ar => ((bitsValue (ar.1.eval x)).toNat,(bitsValue (ar.2.eval x)).toNat))) := by
  simp only [suppliedBits,wordMux_eval,evenOn_value (by omega : 2≤n+1),
    properOn_value (by omega : 0<n+1),rootsOn_value hn,suppliedDivisor]
  split_ifs
  · rw [wordConstant_eval,BitVec.toNat_ofNat,Nat.mod_eq_of_lt]
    exact (by norm_num : 2<2^2).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  · exact rootsOn_value hn m x
  · exact ordersBits_value he m ars x hm hb

end ExactQuantumFactoring.BitArithmetic


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/PhysicalSplitDecoder.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace FixedSplit

def launchWires (n : ℕ) : BooleanNetwork (width n) (PhysicalListSlots.launchWidth n) :=
  select (firstRegister (PhysicalListSlots.launchWidth n) (ordersWidth n) (work n))
def allOrderWires (n : ℕ) : BooleanNetwork (width n) (ordersWidth n) :=
  select (targetRegister (PhysicalListSlots.launchWidth n) (ordersWidth n) (work n))
def modulusNet (n : ℕ) : BooleanNetwork (width n) n := (launchWires n).comp (modulusWires n)
def actualBaseNet {n : ℕ} (i : Fin (n^5)) : BooleanNetwork (width n) n :=
  (launchWires n).comp (baseNet i)
def actualOrderRawNet {n : ℕ} (i : Fin (n^5)) : BooleanNetwork (width n) (OrderSlots.width n) :=
  (allOrderWires n).comp (tensorSelect (OrderSlots.width n) (n^5) i)
def actualOrderNet {n : ℕ} (i : Fin (n^5)) : BooleanNetwork (width n) (Completion.transitionWidth n) :=
  OrderSlots.outputOn (actualBaseNet i) (modulusNet n) (actualOrderRawNet i)

lemma launchWires_eval {n : ℕ} (m : Basis n) (r : Raw n) :
    (launchWires n).eval (encoding m r)=listEncoding m r.1 := packed_first _ _
lemma allOrderWires_eval {n : ℕ} (m : Basis n) (r : Raw n) :
    (allOrderWires n).eval (encoding m r)=ordersLayout n r.2 := packed_targetRegister _ _
lemma modulusNet_eval {n : ℕ} (m : Basis n) (r : Raw n) :
    (modulusNet n).eval (encoding m r)=m := by
  rw [modulusNet,eval_comp,launchWires_eval,modulusWires_eval]
lemma actualBaseNet_eval {n : ℕ} (i : Fin (n^5)) (m : Basis n) (r : Raw n) :
    (actualBaseNet i).eval (encoding m r)=bases r.1 i := by
  rw [actualBaseNet,eval_comp,launchWires_eval,baseNet_eval]
lemma actualOrderRawNet_eval {n : ℕ} (i : Fin (n^5)) (m : Basis n) (r : Raw n) :
    (actualOrderRawNet i).eval (encoding m r)=OrderSlots.layout n (r.2 i) := by
  rw [actualOrderRawNet,eval_comp,allOrderWires_eval]
  exact tensorSelect_eval _ i
lemma actualOrderNet_eval {n : ℕ} (hn : 1≤n) (i : Fin (n^5)) (m : Basis n) (r : Raw n)
    (hm : 2≤(bitsValue m).toNat) :
    (actualOrderNet i).eval (encoding m r)=OrderSlots.output (bases r.1 i) m (r.2 i) := by
  rw [actualOrderNet,OrderSlots.outputOn_eval _ _ _ _ (r.2 i)
    (actualOrderRawNet_eval i m r) hn (by rw [modulusNet_eval];exact hm),
    actualBaseNet_eval,modulusNet_eval]

def liftedModulus (n : ℕ) : BooleanNetwork (width n) (n+1) :=
  (modulusNet n).comp (resizeWord n (n+1))
def actualPairs (n : ℕ) : List (BooleanNetwork (width n) (n+1) ×
    BooleanNetwork (width n) (Completion.transitionWidth n)) :=
  List.ofFn (fun i : Fin (n^5) => ((actualBaseNet i).comp (resizeWord n (n+1)),actualOrderNet i))

/-- Supplied divisor computed from exactly this run's retained quantum bits.
All guarded arithmetic is explicit, including full rare-branch order guesses. -/
def divisorNet (n : ℕ) : BooleanNetwork (width n) (n+1) :=
  suppliedBits n (liftedModulus n) (actualPairs n)

theorem divisorNet_value {n : ℕ} (hn : 2≤n) (m : Basis n) (r : Raw n)
    (hm : 2≤(bitsValue m).toNat) :
    (bitsValue ((divisorNet n).eval (encoding m r))).toNat=divisor m r := by
  have hm' : (bitsValue ((liftedModulus n).eval (encoding m r))).toNat=(bitsValue m).toNat := by
    rw [liftedModulus,eval_comp,resizeWord_toNat (by omega),modulusNet_eval]
  have he : 2≤Completion.transitionWidth n := by
    unfold Completion.transitionWidth
    calc 2≤n := hn
         _ ≤ n*(n^5+1) := Nat.le_mul_of_pos_right n (by omega)
  rw [divisorNet,suppliedBits_value (by omega) he _ _ _ (by rw [hm'];exact hm)
    (by rw [hm'];exact (bitsValue m).isLt),hm',divisor]
  congr 1
  rw [actualPairs,List.map_ofFn]
  unfold pairs
  congr 1
  funext i
  simp only [Function.comp_apply,eval_comp,resizeWord_toNat (Nat.le_succ n),
    actualBaseNet_eval,actualOrderNet_eval (by omega : 1≤n) i m r hm]

end FixedSplit
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/PhysicalSplitLaunch.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open BooleanNetwork

lemma preparedOracle_encode_dependent {α β : Type*} [Fintype α] [Fintype β] {p q r : ℕ}
    (e : α→Basis p) (f : α→β→Basis q) (ψ : α→ℂ) (F : α→β→ℂ)
    (c : BooleanNetwork p q) (hc : c.net.count≤r) (ops : List (Instruction q))
    (hlocal : ∀ a,(programMatrix ops).mulVec (basisVector (c.eval (e a)))=
      encodeState (f a) (F a)) :
    (programMatrix (preparedOracle c hc ops)).mulVec
      (encodeState (fun a=>packed r (e a) (fun _=>false)) ψ)=
    encodeState (fun ab : α×β=>packed r (e ab.1) (f ab.1 ab.2))
      (RecordedHistory.appendState ψ F) := by
  rw [encodeState,Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul,preparedOracle_basis,hlocal,encodeState_comp]
  unfold encodeState RecordedHistory.appendState
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [smul_smul]
  rfl

namespace FixedSplit

def initialNet (n : ℕ) : BooleanNetwork n (width n) :=
  packNet (work n)
    (packNet (PhysicalListSlots.work n) (select id) (Completion.zeros n (PhysicalListSlots.width n)))
    (Completion.zeros n (ordersWidth n))
lemma initialNet_eval {n : ℕ} (m : Basis n) : (initialNet n).eval m=zero m := by
  simp only [initialNet,packNet_eval,eval_select,Function.comp_id,Completion.zeros_eval,zero]
lemma initialNet_count (n : ℕ) : (initialNet n).net.count=
    PhysicalListSlots.width n+PhysicalListSlots.work n+ordersWidth n+work n := by
  simp only [initialNet,packNet_count,count_select,Completion.zeros_count,zero_add]

/-- Runtime-modulus launch of the entire raw split. The circuit description
contains n only, never the input integer, its prime factors, or true orders. -/
abbrev launchWork (n : ℕ) := (initialNet n).net.count
abbrev launchWidth (n : ℕ) := n+width n+launchWork n
def launch (n : ℕ) : List (Instruction (launchWidth n)) :=
  preparedOracle (initialNet n) le_rfl (program n)
def launchEncoding {n : ℕ} (m : Basis n) (r : Raw n) : Basis (launchWidth n) :=
  packed (launchWork n) m (encoding m r)

theorem launch_state {n : ℕ} (m : Basis n) :
    (programMatrix (launch n)).mulVec (basisVector (packed (launchWork n) m (fun _=>false)))=
      encodeState (launchEncoding m) (fresh m) := by
  rw [launch,preparedOracle_basis,initialNet_eval,program_state,encodeState_comp]
  rfl

/-- Coherent correctness on an arbitrary retained history. A parameter-dependent
encoder keeps this run's actual modulus and all of its actual scratch registers. -/
theorem launch_on_history {α : Type*} [Fintype α] {p n r : ℕ}
    (e : α→Basis p) (ψ : α→ℂ) (m : BooleanNetwork p n)
    (hc : (m.comp (initialNet n)).net.count≤r) :
    (programMatrix (preparedOracle (m.comp (initialNet n)) hc (program n))).mulVec
      (encodeState (fun a=>packed r (e a) (fun _=>false)) ψ)=
      encodeState (fun ar : α×Raw n=>packed r (e ar.1) (encoding (m.eval (e ar.1)) ar.2))
        (RecordedHistory.appendState ψ (fun a=>fresh (m.eval (e a)))) := by
  apply preparedOracle_encode_dependent e (fun a=>encoding (m.eval (e a))) ψ
    (fun a=>fresh (m.eval (e a))) (m.comp (initialNet n)) hc (program n)
  intro a
  rw [eval_comp,initialNet_eval,program_state]

lemma launch_length (n : ℕ) : (launch n).length≤
    4*launchWork n+2*width n+(program n).length :=
  preparedOracle_length _ _ _

end FixedSplit
end ExactQuantumFactoring


end

end OAI


