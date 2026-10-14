-- Prove2me | Definitions.Def_OAI_QuantumFactoring_Part12
-- name    : OAI_QuantumFactoring_Part12
-- status  : Definition
-- author  : @SamenHossain
-- created : 2026-10-12T07:31:04.670981+00:00
-- url     : https://prove2.me/theorems/86aa70f1-32f5-42a2-b873-288adf1c0d6d
-- title:
--   Exact quantum factoring, part 12 of 38 (port of OpenAI's formalization)
-- statement:
--   Part 12 of 38 of a port of OpenAI's Lean formalization of the manuscript *Exact quantum factoring over a fixed finite gate set* (OpenAI, September 25, 2026). This part contains the modules `TransitionEqualization`, `ProductStates`, `CompletedOrderSlots`, `PhysicalOrderSlots`, `PhysicalCompletionOutput`, `TensorWiring`, `PreparedOracle`, `PhysicalOrderNetworks`, `FactorController`, `FavorableSplit`, `CanonicalTransition`, `PhaseOracle`, `PhysicalAmplification`.
--
--   **Attribution.** The code is adapted from the OpenAI "math" repository, commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, directory `lean/OAI/Computability/QuantumFactoring`. It is © OpenAI and licensed under the Apache License 2.0; the adapted code is redistributed under the same license.
--
--   **Modifications.** Modules are concatenated in dependency order, with their imports replaced by the previous part. The model definitions come from the platform definition `ExactQuantumFactoring`, which is identical to upstream `Basic.lean`. This part also makes small compatibility edits for Lean 4.33.1 / Mathlib 0df444a: in CompletedOrderSlots.lean, use the `↓reduceIte` simproc instead of `ite_true` (the classical decidability instance no longer matches `ite_true`).
--
--   The development is split into 38 parts only so that each compiles within the platform's time limit. Together the parts supply the circuit family `PhysicalTree.finalCircuit` and its specification, used to prove `OAI.ExactQuantumFactoring.zero_amplitude_core`.
-- source:
--   OpenAI, openai/math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, lean/OAI/Computability/QuantumFactoring: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/TransitionEqualization.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/ProductStates.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/CompletedOrderSlots.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/PhysicalOrderSlots.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/PhysicalCompletionOutput.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/TensorWiring.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/PreparedOracle.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/PhysicalOrderNetworks.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/FactorController.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/FavorableSplit.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/CanonicalTransition.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/PhaseOracle.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/PhysicalAmplification.lean (Apache License 2.0); manuscript https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Exact-quantum-factoring-over-a-fixed-finite-gate-set-September-25-2026/main.pdf

/-
Exact quantum factoring development (port of OpenAI's formalization), part 12 of 38.

Adapted from the OpenAI "math" repository (https://github.com/openai/math, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a), lean/OAI/Computability/QuantumFactoring/: TransitionEqualization.lean, ProductStates.lean, CompletedOrderSlots.lean, PhysicalOrderSlots.lean, PhysicalCompletionOutput.lean, TensorWiring.lean, PreparedOracle.lean, PhysicalOrderNetworks.lean, FactorController.lean, FavorableSplit.lean, CanonicalTransition.lean, PhaseOracle.lean, PhysicalAmplification.lean
These files formalize the manuscript "Exact quantum factoring over a fixed finite gate set"
(OpenAI, September 25, 2026). Copyright OpenAI. Licensed under the Apache License, Version 2.0
(http://www.apache.org/licenses/LICENSE-2.0); the adapted code is distributed under the same license,
on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND.

Modifications: modules concatenated in dependency order with their import lines removed; the model
definitions (Basic.lean) come from the platform definition `ExactQuantumFactoring`, to which upstream
Basic.lean is identical; the final assembly (Main.lean) is omitted; compatibility edits for the platform Lean/Mathlib versions: in CompletedOrderSlots.lean, use the `↓reduceIte` simproc instead of `ite_true` (the classical decidability instance no longer matches `ite_true`).
-/
import Mathlib
import Definitions.Def_OAI_QuantumFactoring_Part11

set_option autoImplicit false

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/TransitionEqualization.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open Exactness RepeatedTrials OrderTrial

lemma OrderTrial.DyadicAt.pow {d : ℕ} {x : ℚ} (h : DyadicAt d x) (k : ℕ) :
    DyadicAt (d*k) (x^k) := by
  induction k with
  | zero => simpa using DyadicAt.integer 0 1
  | succ k ih =>
    simpa only [pow_succ,Nat.mul_succ] using ih.mul h

namespace Completion

def target (n : ℕ) : ℚ := 1-1/(2:ℚ)^n
def transitionWidth (n : ℕ) : ℕ := n*(n^5+1)
def listSuccess (m n K : ℕ) : ℚ :=
  1-(1-(favorableCount m n : ℚ)/(2:ℚ)^(Nat.clog 2 m))^K
def orderSuccess (d K : ℕ) : ℚ :=
  1-(1-(Nat.totient d:ℚ)*prescribedMass d)^K

lemma target_at (n : ℕ) : DyadicAt n (target n) :=
  (DyadicAt.integer n 1).sub ⟨1,by simp⟩

lemma listSuccess_at {m n : ℕ} (hb : m ≤ 2^n) (K : ℕ) :
    DyadicAt (n*K) (listSuccess m n K) := by
  have hx : DyadicAt n ((favorableCount m n:ℚ)/(2:ℚ)^(Nat.clog 2 m)) :=
    (show DyadicAt (Nat.clog 2 m) _ from ⟨favorableCount m n,by simp⟩).mono
      (Nat.clog_le_of_le_pow hb)
  exact (DyadicAt.integer (n*K) 1).sub (((DyadicAt.integer n 1).sub hx).pow K)

lemma orderSuccess_at {n d : ℕ} (hd : d ≤ 2^n) (K : ℕ) :
    DyadicAt ((n+10)*K) (orderSuccess d K) := by
  have hx : DyadicAt (n+10) ((Nat.totient d:ℚ)*prescribedMass d) := by
    exact_mod_cast (lambda_at hd).int_mul (Nat.totient d)
  exact (DyadicAt.integer ((n+10)*K) 1).sub (((DyadicAt.integer (n+10) 1).sub hx).pow K)

lemma target_pos {n : ℕ} (hn : 1 ≤ n) : 0<target n := by
  have hp : (1:ℚ)<2^n := one_lt_pow₀ (by norm_num) (by omega)
  unfold target
  have hh := (div_lt_one (by positivity : (0:ℚ)<2^n)).mpr hp
  linarith

/-- The source repetition bound suffices for the unchanged equalization target.
No high-probability event is being declared to have probability one. -/
lemma target_le_ordinary {n : ℕ} (hn : 1 ≤ n) {s : ℚ}
    (hs : 1-1/(2:ℚ)^(2*n) ≤ s) :
    target n ≤ (1-1/(2:ℚ)^(2*n))*s := by
  have hp : (2:ℚ) ≤ 2^n := by
    simpa using (pow_le_pow_right₀ (by norm_num : (1:ℚ) ≤ 2) hn)
  have hpp : (0:ℚ)<2^n := by positivity
  have he : (2:ℚ)^(2*n)=(2^n)^2 := by rw [Nat.mul_comm 2 n,pow_mul]
  have hu : 0 ≤ 1/(2:ℚ)^n := by positivity
  have hl : 1/(2:ℚ)^n ≤ 1/2 := by exact one_div_le_one_div_of_le (by norm_num) hp
  have hδ : 1/(2:ℚ)^(2*n)=(1/(2:ℚ)^n)^2 := by rw [he,div_pow,one_pow]
  have hfactor : 0 ≤ 1-1/(2:ℚ)^(2*n) := by rw [hδ]; nlinarith
  have hh := mul_le_mul_of_nonneg_left hs hfactor
  unfold target
  rw [hδ] at hh ⊢
  nlinarith [sq_nonneg ((1/(2:ℚ)^n)^2)]

lemma listSuccess_lower {m n : ℕ} (hn : 128 ≤ n) (hm : 2 ≤ m) (hb : m<2^n)
    (hodd : Odd m) (p₀ p₁ : Component m) (hne : p₁≠p₀) :
    1-1/(2:ℚ)^(2*n) ≤ listSuccess m n (n^5) := by
  have hh := list_good_lower hn hm hb hodd p₀ p₁ hne
  rw [list_good_mass _ hb hodd p₀] at hh
  apply (Rat.cast_le (K := ℝ)).mp
  simpa only [listSuccess,Rat.cast_sub,Rat.cast_one,Rat.cast_div,Rat.cast_pow,
    Rat.cast_ofNat,Rat.cast_natCast] using hh

lemma listSuccess_le_one {m n : ℕ} (hm : m≠0) (hb : m<2^n)
    (hodd : Odd m) (p₀ : Component m) (K : ℕ) : listSuccess m n K ≤ 1 := by
  have hh := (mass_bounds (tensorState (fairState (Nat.clog 2 m)) K)
    (GoodList hm hb p₀ K) (tensor_normalized _ K (fairState_normalized _))).2
  rw [list_good_mass hm hb hodd p₀] at hh
  apply (Rat.cast_le (K := ℝ)).mp
  simpa only [listSuccess,Rat.cast_sub,Rat.cast_one,Rat.cast_div,Rat.cast_pow,
    Rat.cast_ofNat,Rat.cast_natCast] using hh

lemma orderSuccess_lower {w n s : ℕ} (hn : 128 ≤ n) (hs : 2^(s+2)=(2^n)^16)
    (a m : Basis w) (hm : 2 ≤ (bitsValue m).toNat) (u : (ZMod (bitsValue m).toNat)ˣ)
    (ha : ((bitsValue a).toNat : ZMod (bitsValue m).toNat)=(u : ZMod (bitsValue m).toNat))
    (hdB : orderOf u<2^n) : 1-1/(2:ℚ)^(2*n) ≤ orderSuccess (orderOf u) (n^5) := by
  have hh := orderResult_lower hn hs a m hm u ha hdB
  rw [orderResult_mass (by omega) hs a m hm u ha hdB] at hh
  apply (Rat.cast_le (K := ℝ)).mp
  simpa only [orderSuccess,Rat.cast_sub,Rat.cast_one,Rat.cast_div,Rat.cast_pow,
    Rat.cast_ofNat,Rat.cast_mul,Rat.cast_natCast] using hh

lemma orderSuccess_le_one {w n s : ℕ} (hn : 1 ≤ n) (hs : 2^(s+2)=(2^n)^16)
    (a m : Basis w) (hm : 2 ≤ (bitsValue m).toNat) (u : (ZMod (bitsValue m).toNat)ˣ)
    (ha : ((bitsValue a).toNat : ZMod (bitsValue m).toNat)=(u : ZMod (bitsValue m).toNat))
    (hdB : orderOf u<2^n) (K : ℕ) : orderSuccess (orderOf u) K ≤ 1 := by
  have hh := (mass_bounds (tensorState (rawState s n a m) K)
    (fun x => orderResult s n a m K x=orderOf u)
    (tensor_normalized _ K (raw_normalized s n a m))).2
  rw [orderResult_mass hn hs a m hm u ha hdB] at hh
  apply (Rat.cast_le (K := ℝ)).mp
  simpa only [orderSuccess,Rat.cast_sub,Rat.cast_one,Rat.cast_div,Rat.cast_pow,
    Rat.cast_ofNat,Rat.cast_mul,Rat.cast_natCast] using hh

/-- Local same-record equalization, now specialized to the actual list law and
actual source constants. The guess is tested for a single fixed padded list. -/
theorem list_passed_mass {m n : ℕ} (hn : 128 ≤ n) (hm : 2 ≤ m) (hb : m<2^n)
    (hodd : Odd m) (p₀ p₁ : Component m) (hne : p₁≠p₀)
    (y₀ : Basis (transitionWidth n)) :
    outcomeMass (passed (GoodList (by omega : m≠0) hb p₀ (n^5)) y₀
      (listSuccess m n (n^5)) (target n))
      (fresh (tensorState (fairState (Nat.clog 2 m)) (n^5))
        (transitionWidth n) (2*n) (n*n^5))=(target n:ℝ) := by
  have hlow := listSuccess_lower hn hm hb hodd p₀ p₁ hne
  have hp := target_pos (by omega : 1 ≤ 2*n)
  apply passed_mass _ _ _ _ _ (tensor_normalized _ _ (fairState_normalized _))
    (by rw [list_good_mass _ hb hodd p₀]; simp [listSuccess])
    (listSuccess_at hb.le _) (target_at n) (by unfold coinBits; omega)
    (by exact hp.trans_le hlow) (listSuccess_le_one (by omega) hb hodd p₀ _)
    (by omega) (target_pos (by omega)) (target_le_ordinary (by omega) hlow)

/-- Local same-record equalization for the literal n^5 repeated order trial. -/
theorem order_passed_mass {w n s : ℕ} (hn : 128 ≤ n) (hs : 2^(s+2)=(2^n)^16)
    (a m : Basis w) (hm : 2 ≤ (bitsValue m).toNat) (u : (ZMod (bitsValue m).toNat)ˣ)
    (ha : ((bitsValue a).toNat : ZMod (bitsValue m).toNat)=(u : ZMod (bitsValue m).toNat))
    (hdB : orderOf u<2^n) (y₀ : Basis (transitionWidth n)) :
    outcomeMass (passed (fun x => orderResult s n a m (n^5) x=orderOf u) y₀
      (orderSuccess (orderOf u) (n^5)) (target n))
      (fresh (tensorState (rawState s n a m) (n^5))
        (transitionWidth n) (2*n) ((n+10)*n^5))=(target n:ℝ) := by
  have hlow := orderSuccess_lower hn hs a m hm u ha hdB
  have hp := target_pos (by omega : 1 ≤ 2*n)
  apply passed_mass _ _ _ _ _ (tensor_normalized _ _ (raw_normalized s n a m))
    (by rw [orderResult_mass (by omega) hs a m hm u ha hdB]; simp [orderSuccess])
    (orderSuccess_at hdB.le _) (target_at n) (by unfold coinBits; omega)
    (by exact hp.trans_le hlow) (orderSuccess_le_one (by omega) hs a m hm u ha hdB _)
    (by omega) (target_pos (by omega)) (target_le_ordinary (by omega) hlow)

end Completion
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/ProductStates.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open Exactness

/-- Independent, not necessarily identically distributed, retained registers. -/
noncomputable def productState {ι : Type*} [Fintype ι] {α : ι → Type*}
    (ψ : ∀ i, α i → ℂ) (x : ∀ i, α i) : ℂ := ∏ i, ψ i (x i)

lemma productState_normalized {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)] (ψ : ∀ i, α i → ℂ)
    (hψ : ∀ i, ∑ x, Complex.normSq (ψ i x)=1) :
    ∑ x, Complex.normSq (productState ψ x)=1 := by
  simp only [productState,map_prod]
  rw [←Fintype.prod_sum (fun i a => Complex.normSq (ψ i a))]
  simp only [hψ,Finset.prod_const_one]

lemma productState_all_mass {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)] (ψ : ∀ i, α i → ℂ)
    (P : ∀ i, α i → Prop) :
    outcomeMass (fun x => ∀ i, P i (x i)) (productState ψ)=
      ∏ i, outcomeMass (P i) (ψ i) := by
  classical
  unfold outcomeMass productState
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : ∀ i, P i (x i)
  · simp [hx,map_prod]
  · rw [ite_eq_right hx]
    obtain ⟨i,hi⟩ := not_forall.mp hx
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)).symm

lemma productState_constant_mass {α : Type*} [Fintype α] {K : ℕ}
    (ψ : Fin K → α → ℂ) (P : Fin K → α → Prop) (z : ℝ)
    (hz : ∀ i, outcomeMass (P i) (ψ i)=z) :
    outcomeMass (fun x => ∀ i, P i (x i)) (productState ψ)=z^K := by
  rw [productState_all_mass]
  simp only [hz,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/CompletedOrderSlots.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open Exactness RepeatedTrials OrderTrial

namespace Completion

/-- Dummy slots retain their internal preparation too. Only the constant output
is visible to the controller; no branch-local normalization is performed. -/
lemma dummy_passed_mass {α : Type*} [Fintype α] (ψ : α→ℂ) (n d : ℕ)
    (hn : 128 ≤ n) (hψ : ∑ x,Complex.normSq (ψ x)=1) (y₀ : Basis (transitionWidth n)) :
    outcomeMass (passed (fun _ => True) y₀ 1 (target n))
      (fresh ψ (transitionWidth n) (2*n) d)=(target n:ℝ) := by
  apply passed_mass ψ _ y₀ 1 (target n) hψ
  · simpa only [outcomeMass,↓reduceIte,Rat.cast_one] using hψ
  · exact DyadicAt.integer d 1
  · exact target_at n
  · unfold coinBits; omega
  · norm_num
  · norm_num
  · omega
  · exact target_pos (by omega)
  · apply target_le_ordinary (by omega : 1 ≤ n)
    have hp : (0:ℚ) ≤ 1/(2:ℚ)^(2*n) := by positivity
    linarith

end Completion

namespace OrderSlots

abbrev sampleExponent (n : ℕ) := 16*n-2
lemma sampleExponent_spec {n : ℕ} (hn : 128 ≤ n) :
    2^(sampleExponent n+2)=(2^n)^16 := by
  rw [←pow_mul]
  congr 1
  unfold sampleExponent
  omega

abbrev Result (n : ℕ) := Completion.Raw (Fin (n^5)→OrderTrial.Raw n (sampleExponent n) n)
  (Completion.transitionWidth n) (2*n) ((n+10)*n^5)

noncomputable instance resultFintype (n : ℕ) : Fintype (Result n) := inferInstance

noncomputable def fresh (n : ℕ) (a m : Basis n) : Result n→ℂ :=
  Completion.fresh (tensorState (rawState (sampleExponent n) n a m) (n^5))
    (Completion.transitionWidth n) (2*n) ((n+10)*n^5)

def Usable {n : ℕ} (a m : Basis n) : Prop :=
  (bitsValue a).toNat < (bitsValue m).toNat ∧
    IsUnit ((bitsValue a).toNat : ZMod (bitsValue m).toNat)

noncomputable def unitOrder {n : ℕ} (a m : Basis n) : ℕ := by
  classical
  exact if h : Usable a m then orderOf h.2.unit else 0

noncomputable def canonical {n : ℕ} (a m : Basis n) : Basis (Completion.transitionWidth n) :=
  natBasis _ (unitOrder a m)

noncomputable def ordinary {n : ℕ} (a m : Basis n)
    (r : Fin (n^5)→OrderTrial.Raw n (sampleExponent n) n) : Basis (Completion.transitionWidth n) := by
  classical
  exact if Usable a m then
    natBasis _ (orderResult (sampleExponent n) n a m (n^5) r) else natBasis _ 0

noncomputable def passed {n : ℕ} (a m : Basis n) : Result n→Prop := by
  classical
  exact if h : Usable a m then
    Completion.passed (fun r => orderResult (sampleExponent n) n a m (n^5) r=orderOf h.2.unit)
      (canonical a m) (Completion.orderSuccess (orderOf h.2.unit) (n^5)) (Completion.target n)
  else Completion.passed (fun _ => True) (canonical a m) 1 (Completion.target n)

noncomputable def output {n : ℕ} (a m : Basis n) : Result n→Basis (Completion.transitionWidth n) :=
  Completion.output (ordinary a m)

lemma fresh_normalized (n : ℕ) (a m : Basis n) :
    ∑ r,Complex.normSq (fresh n a m r)=1 :=
  Completion.fresh_normalized _ _ _ _ (tensor_normalized _ _ (raw_normalized _ _ a m))

lemma unitOrder_lt {n : ℕ} (a m : Basis n) (hm : 2 ≤ (bitsValue m).toNat) :
    unitOrder a m < 2^n := by
  classical
  let : NeZero (bitsValue m).toNat := ⟨by omega⟩
  unfold unitOrder
  split_ifs with h
  · have hh := orderOf_le_card (x:=h.2.unit)
    rw [Nat.card_eq_fintype_card,ZMod.card_units_eq_totient] at hh
    exact (hh.trans (Nat.totient_le _)).trans_lt (bitsValue m).isLt
  · positivity

lemma passed_mass {n : ℕ} (hn : 128 ≤ n) (a m : Basis n) (hm : 2 ≤ (bitsValue m).toNat) :
    outcomeMass (passed a m) (fresh n a m)=(Completion.target n:ℝ) := by
  classical
  unfold passed
  split_ifs with h
  · have hlt := unitOrder_lt a m hm
    simp only [unitOrder,dite_eq_left h] at hlt
    exact Completion.order_passed_mass hn (sampleExponent_spec hn) a m hm h.2.unit
      h.2.unit_spec.symm hlt (canonical a m)
  · exact Completion.dummy_passed_mass _ n _ hn
      (tensor_normalized _ _ (raw_normalized _ _ a m)) (canonical a m)

lemma passed_output {n : ℕ} (a m : Basis n) (r : Result n) (hp : passed a m r) :
    output a m r=canonical a m := by
  classical
  unfold passed at hp
  split_ifs at hp with h
  · rcases hp with hp | hp
    · simp only [output,Completion.output,ite_eq_right hp.1,ordinary,ite_eq_left h,canonical,
        unitOrder,dite_eq_left h,hp.2.1]
    · simp only [output,Completion.output,ite_eq_left hp.1,hp.2.1]
  · rcases hp with hp | hp
    · simp only [output,Completion.output,ite_eq_right hp.1,ordinary,ite_eq_right h,canonical,
        unitOrder,dite_eq_right h]
    · simp only [output,Completion.output,ite_eq_left hp.1,hp.2.1]

/-- Every supplied base has exactly z retained mass. Out-of-range entries and nonunits are dummy slots,
not an assumption that a random list consists only of units. -/
theorem all_passed_mass {n : ℕ} (hn : 128 ≤ n) (m : Basis n) (hm : 2 ≤ (bitsValue m).toNat)
    (as : Fin (n^5)→Basis n) :
    outcomeMass (fun r : Fin (n^5)→Result n => ∀ i,passed (as i) m (r i))
      (productState (fun i => fresh n (as i) m))=(Completion.target n:ℝ)^(n^5) := by
  exact productState_constant_mass _ _ _ (fun _ => passed_mass hn _ _ hm)

end OrderSlots
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/PhysicalOrderSlots.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open Exactness RepeatedTrials OrderTrial
namespace OrderSlots

abbrev ordinaryWidth (n : ℕ) := tensorWidth (rawWidth n (sampleExponent n) n) (n^5)
abbrev coinWidth (n : ℕ) := Completion.coinBits (Completion.transitionWidth n) (2*n) ((n+10)*n^5)
abbrev width (n : ℕ) := 2*n+(ordinaryWidth n+(Completion.transitionWidth n+coinWidth n))

def ordinaryLayout (n : ℕ) : (Fin (n^5)→OrderTrial.Raw n (sampleExponent n) n)≃Basis (ordinaryWidth n) :=
  (Equiv.piCongrRight (fun _ => rawLayout n (sampleExponent n) n)).trans
    (tensorLayout (rawWidth n (sampleExponent n) n) (n^5))
def layout (n : ℕ) : Result n≃Basis (width n) :=
  productLayout (Equiv.refl _) (productLayout (ordinaryLayout n)
    (productLayout (Equiv.refl _) (Equiv.refl _)))

def program (n : ℕ) : List (Instruction (width n)) :=
  Completion.program (tensorProgram (rawProgram n (sampleExponent n) n) (n^5))
    (Completion.transitionWidth n) (2*n) ((n+10)*n^5)

noncomputable def zero {n : ℕ} (a m : Basis n) : Result n :=
  ((fun _ => false),(fun _ => rawZero (sampleExponent n) n a m),(fun _ => false),(fun _ => false))

lemma ordinary_entry (n : ℕ) (a m : Basis n) (r : Fin (n^5)→OrderTrial.Raw n (sampleExponent n) n) :
    (programMatrix (tensorProgram (rawProgram n (sampleExponent n) n) (n^5))).mulVec
      (basisVector (ordinaryLayout n (fun _ => rawZero (sampleExponent n) n a m)))
      (ordinaryLayout n r)=tensorState (rawState (sampleExponent n) n a m) (n^5) r := by
  change (programMatrix (tensorProgram (rawProgram n (sampleExponent n) n) (n^5))).mulVec
    (basisVector (tensorLayout _ _ (fun _ => rawLayout _ _ _ (rawZero _ _ a m))))
    (tensorLayout _ _ (fun i => rawLayout _ _ _ (r i)))=_
  rw [tensorProgram_entry]
  simp only [rawProgram_entry,tensorState]

/-- The completed order slot is a literal finite gate program on fresh qubits.
Neither the true order nor retrospective factor data occur in its preparation. -/
lemma program_entry (n : ℕ) (a m : Basis n) (r : Result n) :
    (programMatrix (program n)).mulVec (basisVector (layout n (zero a m))) (layout n r)=fresh n a m r := by
  change (programMatrix (Completion.program _ _ _ _)).mulVec
    (basisVector (Completion.layout _ _ _ _
      ((fun _ => false),ordinaryLayout n (fun _ => rawZero (sampleExponent n) n a m),
        (fun _ => false),(fun _ => false))))
    (Completion.layout _ _ _ _ (r.1,ordinaryLayout n r.2.1,r.2.2))=_
  rw [Completion.program_entry]
  simp only [fresh,Completion.fresh,independentState]
  rw [ordinary_entry]

lemma program_state (n : ℕ) (a m : Basis n) :
    (programMatrix (program n)).mulVec (basisVector (layout n (zero a m)))=
      encodeState (layout n) (fresh n a m) := by
  funext x
  obtain ⟨r,rfl⟩ := (layout n).surjective x
  rw [program_entry,encodeState_at _ (layout n).injective]

lemma program_mass (n : ℕ) (a m : Basis n) (P : Result n→Prop) :
    outcomeMass (P ∘ (layout n).symm)
      ((programMatrix (program n)).mulVec (basisVector (layout n (zero a m))))=
      outcomeMass P (fresh n a m) := by
  rw [program_state,outcomeMass_encode _ (layout n).injective]
  congr 1
  funext r
  simp

lemma program_passed_mass {n : ℕ} (hn : 128 ≤ n) (a m : Basis n) (hm : 2 ≤ (bitsValue m).toNat) :
    outcomeMass (passed a m ∘ (layout n).symm)
      ((programMatrix (program n)).mulVec (basisVector (layout n (zero a m))))=(Completion.target n:ℝ) := by
  rw [program_mass]
  exact passed_mass hn a m hm

lemma program_length (n : ℕ) :
    (program n).length ≤ n^5*(2+((sampleExponent n+2)+4*OrderSample.scratch n (sampleExponent n+2)+
      2*n+(sampleExponent n+2)*(998*(sampleExponent n+2)+49)+2*(sampleExponent n+5))+
      3*n+retentionBits n)+2*n+Completion.transitionWidth n+coinWidth n := by
  have hh := OrderSample.completeSampler_length n (sampleExponent n)
  have hr : (rawProgram n (sampleExponent n) n).length ≤
      2+((sampleExponent n+2)+4*OrderSample.scratch n (sampleExponent n+2)+
      2*n+(sampleExponent n+2)*(998*(sampleExponent n+2)+49)+2*(sampleExponent n+5))+
      3*n+retentionBits n := by
    simp only [rawProgram,parallelProgram_length,hadamardPrefix_length,guessProgram_length]
    omega
  unfold program
  rw [Completion.program_length,tensorProgram_length]
  exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.mul_le_mul_left _ hr) _) _) _

end OrderSlots
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/PhysicalCompletionOutput.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace Completion

abbrev totalWidth (q W t d : ℕ) := t+(q+(W+coinBits W t d))

def rareWires (q W t d : ℕ) : BooleanNetwork (totalWidth q W t d) t :=
  select (Fin.castAdd (q+(W+coinBits W t d)))
def ordinaryWires (q W t d : ℕ) : BooleanNetwork (totalWidth q W t d) q :=
  select (fun i => Fin.natAdd t (i.castAdd (W+coinBits W t d)))
def guessWires (q W t d : ℕ) : BooleanNetwork (totalWidth q W t d) W :=
  select (fun i => Fin.natAdd t (Fin.natAdd q (i.castAdd (coinBits W t d))))
def retentionWires (q W t d : ℕ) : BooleanNetwork (totalWidth q W t d) (coinBits W t d) :=
  select (fun i => Fin.natAdd t (Fin.natAdd q (Fin.natAdd W i)))

lemma rareWires_eval {q W t d : ℕ} (r : Raw (Basis q) W t d) :
    (rareWires q W t d).eval (layout q W t d r)=r.1 := by
  funext i
  simp only [rareWires,eval_select,Function.comp_apply,layout,productLayout_apply,
    Equiv.refl_apply,Fin.append_left]
lemma ordinaryWires_eval {q W t d : ℕ} (r : Raw (Basis q) W t d) :
    (ordinaryWires q W t d).eval (layout q W t d r)=r.2.1 := by
  funext i
  simp only [ordinaryWires,eval_select,Function.comp_apply,layout,productLayout_apply,
    Equiv.refl_apply,Fin.append_left,Fin.append_right]
lemma guessWires_eval {q W t d : ℕ} (r : Raw (Basis q) W t d) :
    (guessWires q W t d).eval (layout q W t d r)=r.2.2.1 := by
  funext i
  simp only [guessWires,eval_select,Function.comp_apply,layout,productLayout_apply,
    Equiv.refl_apply,Fin.append_left,Fin.append_right]
lemma retentionWires_eval {q W t d : ℕ} (r : Raw (Basis q) W t d) :
    (retentionWires q W t d).eval (layout q W t d r)=r.2.2.2 := by
  funext i
  simp only [retentionWires,eval_select,Function.comp_apply,layout,productLayout_apply,
    Equiv.refl_apply,Fin.append_right]

def rareNet (q W t d : ℕ) : BooleanNetwork (totalWidth q W t d) 1 :=
  equalOn (rareWires q W t d) (wordConstant (BitVec.ofNat t 0))
lemma rareNet_eval {q W t d : ℕ} (r : Raw (Basis q) W t d) :
    (rareNet q W t d).eval (layout q W t d r) 0=true ↔ rare r.1 := by
  rw [rareNet,equalOn_value,rareWires_eval,wordConstant_eval]
  simp only [BitVec.toNat_ofNat,Nat.zero_mod,rare]
lemma rareNet_count (q W t d : ℕ) : (rareNet q W t d).net.count ≤ 97*t+21 := by
  have h := equalOn_count (rareWires q W t d) (wordConstant (BitVec.ofNat t 0))
  apply h.trans
  simp only [rareWires,count_select,wordConstant_count]
  omega

/-- Runtime output selection retains the entire unused ordinary computation even
on the rare branch. Neither success statistics nor future auxiliary data enter
this network. -/
def outputNet {q W : ℕ} (ordinary : BooleanNetwork q W) (t d : ℕ) :
    BooleanNetwork (totalWidth q W t d) W :=
  wordMux (rareNet q W t d) (guessWires q W t d)
    ((ordinaryWires q W t d).comp ordinary)
lemma outputNet_eval {q W t d : ℕ} (ordinary : BooleanNetwork q W)
    (r : Raw (Basis q) W t d) :
    (outputNet ordinary t d).eval (layout q W t d r)=output ordinary.eval r := by
  rw [outputNet,wordMux_eval,guessWires_eval,eval_comp,ordinaryWires_eval,output]
  simp only [rareNet_eval r]
lemma outputNet_count {q W : ℕ} (ordinary : BooleanNetwork q W) (t d : ℕ) :
    (outputNet ordinary t d).net.count ≤ ordinary.net.count+97*t+7*W+21 := by
  rw [outputNet,wordMux_count,count_comp]
  have h := rareNet_count q W t d
  simp only [guessWires,ordinaryWires,count_select] at *
  omega

/-- Constant-zero fresh blocks are explicit gates, rather than analytical
initialization assumptions about the raw sampler layout. -/
def zeros (k m : ℕ) : BooleanNetwork k m := vector (fun _ => constant false)
lemma zeros_eval (k m : ℕ) (x : Basis k) : (zeros k m).eval x=fun _ => false := by
  funext i
  simp only [zeros,eval_vector,eval_constant]
lemma zeros_count (k m : ℕ) : (zeros k m).net.count=m := by
  simp [zeros]

def initialNet {k q : ℕ} (ordinary : BooleanNetwork k q) (W t d : ℕ) :
    BooleanNetwork k (totalWidth q W t d) :=
  (zeros k t).pair (ordinary.pair ((zeros k W).pair (zeros k (coinBits W t d))))
lemma initialNet_eval {k q W t d : ℕ} (ordinary : BooleanNetwork k q) (x : Basis k) :
    (initialNet ordinary W t d).eval x=
      layout q W t d ((fun _ => false),ordinary.eval x,(fun _ => false),(fun _ => false)) := by
  simp only [initialNet,eval_pair,zeros_eval,layout,productLayout_apply,Equiv.refl_apply]
lemma initialNet_count {k q : ℕ} (ordinary : BooleanNetwork k q) (W t d : ℕ) :
    (initialNet ordinary W t d).net.count=ordinary.net.count+t+W+coinBits W t d := by
  simp only [initialNet,count_pair,zeros_count]
  omega

end Completion
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/TensorWiring.lean =====
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

def tensorWire (q : ℕ) : (K : ℕ) → Fin K → Fin q → Fin (tensorWidth q K)
  | 0, i => Fin.elim0 i
  | K+1, i => Fin.cases (fun j => j.castAdd (tensorWidth q K))
      (fun i j => Fin.natAdd q (tensorWire q K i j)) i

lemma tensorLayout_wire {q K : ℕ} (x : Fin K → Basis q) (i : Fin K) (j : Fin q) :
    tensorLayout q K x (tensorWire q K i j)=x i j := by
  induction K with
  | zero => exact Fin.elim0 i
  | succ K ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · change Fin.append (x 0) (tensorLayout q K (Fin.tail x)) (j.castAdd _) = _
      exact Fin.append_left _ _ _
    · change Fin.append (x 0) (tensorLayout q K (Fin.tail x))
        (Fin.natAdd q (tensorWire q K i j)) = _
      rw [Fin.append_right]
      exact ih (Fin.tail x) i

def tensorSelect (q K : ℕ) (i : Fin K) : BooleanNetwork (tensorWidth q K) q :=
  select (tensorWire q K i)
lemma tensorSelect_eval {q K : ℕ} (x : Fin K → Basis q) (i : Fin K) :
    (tensorSelect q K i).eval (tensorLayout q K x)=x i := by
  funext j
  exact tensorLayout_wire x i j
lemma tensorSelect_inverse {q K : ℕ} (x : Basis (tensorWidth q K)) (i : Fin K) :
    (tensorSelect q K i).eval x=(tensorLayout q K).symm x i := by
  obtain ⟨y,rfl⟩ := (tensorLayout q K).surjective x
  rw [tensorSelect_eval,Equiv.symm_apply_apply]

/-- Direct concatenation prepares K fixed blocks. No branch-indexed truth table
is allocated; the count is the sum of the supplied K finite networks. -/
def tensorNetwork {n q : ℕ} : {K : ℕ} → (Fin K → BooleanNetwork n q) →
    BooleanNetwork n (tensorWidth q K)
  | 0,_ => select Fin.elim0
  | _K+1,f => (f 0).pair (tensorNetwork (fun i => f i.succ))
lemma tensorNetwork_eval {n q K : ℕ} (f : Fin K → BooleanNetwork n q) (x : Basis n) :
    (tensorNetwork f).eval x=tensorLayout q K (fun i => (f i).eval x) := by
  induction K with
  | zero => exact Subsingleton.elim _ _
  | succ K ih => rw [tensorNetwork,eval_pair,ih,tensorLayout_succ]; rfl
lemma tensorNetwork_count {n q K : ℕ} (f : Fin K → BooleanNetwork n q) :
    (tensorNetwork f).net.count=∑ i,(f i).net.count := by
  induction K with
  | zero => simp [tensorNetwork]
  | succ K ih => simp only [tensorNetwork,count_pair,ih,Fin.sum_univ_succ]
lemma tensorNetwork_count_le {n q K c : ℕ} (f : Fin K → BooleanNetwork n q)
    (hf : ∀ i,(f i).net.count ≤ c) : (tensorNetwork f).net.count ≤ K*c := by
  rw [tensorNetwork_count]
  calc
    _ ≤ ∑ _ : Fin K,c := Finset.sum_le_sum (fun i _ => hf i)
    _ = _ := by simp

end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/PreparedOracle.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open BooleanNetwork Exactness

def targetRegister (n m r : ℕ) : Register m (n+m+r) where
  toFun i := ⟨n+i.val,by omega⟩
  inj' := by
    intro i j hh
    apply Fin.ext
    have h := congrArg Fin.val hh
    change n+i.val=n+j.val at h
    omega

lemma targetRegister_val (n m r : ℕ) (i : Fin m) :
    (targetRegister n m r i).val=n+i.val := rfl

lemma packed_targetRegister {n m r : ℕ} (x : Basis n) (y : Basis m) :
    packed r x y ∘ targetRegister n m r=y := by
  funext i
  exact packed_target x y i

lemma packed_replace_target {n m r : ℕ} (x : Basis n) (y z : Basis m) :
    (targetRegister n m r).replace (packed r x y) z=packed r x z := by
  funext i
  by_cases hin : n ≤ i.val
  · by_cases hi : i.val<n+m
    · let j : Fin m := ⟨i.val-n,by omega⟩
      have he : targetRegister n m r j=i := Fin.ext (by rw [targetRegister_val]; dsimp [j]; omega)
      rw [←he,Register.replace_inside]
      exact (packed_target x z j).symm
    · have ho : ∀ j,targetRegister n m r j≠i := by
        intro j hh
        have he := congrArg Fin.val hh
        rw [targetRegister_val] at he
        have := j.isLt
        omega
      rw [Register.replace_outside _ _ _ ⟨i,ho⟩]
      change packed r x y i=packed r x z i
      rw [packed_work _ _ _ (by omega),packed_work _ _ _ (by omega)]
  · have ho : ∀ j,targetRegister n m r j≠i := by
      intro j hh
      have he := congrArg Fin.val hh
      rw [targetRegister_val] at he
      omega
    rw [Register.replace_outside _ _ _ ⟨i,ho⟩]
    simp only [packed,dite_eq_left (show i.val<n by omega)]

def targetProgram {m : ℕ} (n r : ℕ) (ops : List (Instruction m)) :
    List (Instruction (n+m+r)) := ops.map (Instruction.place (targetRegister n m r))

lemma targetProgram_basis {n m r : ℕ} (ops : List (Instruction m)) (x : Basis n) (y : Basis m) :
    (programMatrix (targetProgram n r ops)).mulVec (basisVector (packed r x y))=
      encodeState (fun z => packed r x z) ((programMatrix ops).mulVec (basisVector y)) := by
  rw [targetProgram,Register.placed_basis_state,packed_targetRegister]
  congr 1
  funext z
  exact packed_replace_target x y z

/-- Prepare a runtime-dependent input with a genuine clean Boolean oracle,
then run the same fixed quantum program on that fresh input. All old bits x
survive, and c is a network, not a large table of counterfactual outputs. -/
def preparedOracle {n m r : ℕ} (c : BooleanNetwork n m) (hr : c.net.count ≤ r)
    (ops : List (Instruction m)) : List (Instruction (n+m+r)) :=
  oracleOn c hr++targetProgram n r ops

lemma preparedOracle_length {n m r : ℕ} (c : BooleanNetwork n m) (hr : c.net.count ≤ r)
    (ops : List (Instruction m)) :
    (preparedOracle c hr ops).length ≤ 4*c.net.count+2*m+ops.length := by
  have hh := oracleOn_length c hr
  simp only [preparedOracle,List.length_append,targetProgram,List.length_map]
  omega

lemma preparedOracle_basis {n m r : ℕ} (c : BooleanNetwork n m) (hr : c.net.count ≤ r)
    (ops : List (Instruction m)) (x : Basis n) :
    (programMatrix (preparedOracle c hr ops)).mulVec (basisVector (packed r x (fun _ => false)))=
      encodeState (fun z => packed r x z) ((programMatrix ops).mulVec (basisVector (c.eval x))) := by
  rw [preparedOracle,programMatrix_append,←Matrix.mulVec_mulVec,oracleOn_basis]
  simp only [Bool.false_xor]
  exact targetProgram_basis ops x _

/-- Coherent launch on an arbitrary already-entangled classical history. This
identity is valid on the actual amplitudes, prior to any later validation. -/
lemma preparedOracle_state {n m r : ℕ} (c : BooleanNetwork n m) (hr : c.net.count ≤ r)
    (ops : List (Instruction m)) (ψ : State n) :
    (programMatrix (preparedOracle c hr ops)).mulVec
      (encodeState (fun x => packed r x (fun _ => false)) ψ)=
    encodeState (fun xy : Basis n×Basis m => packed r xy.1 xy.2)
      (RecordedHistory.appendState ψ (fun x => (programMatrix ops).mulVec (basisVector (c.eval x)))) := by
  rw [encodeState,Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul,preparedOracle_basis]
  unfold encodeState RecordedHistory.appendState
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [smul_smul]

lemma packed_pair_injective (n m r : ℕ) :
    Function.Injective (fun xy : Basis n×Basis m => packed r xy.1 xy.2) := by
  intro x y h
  apply Prod.ext
  · have he := congrArg (fun a => a ∘ firstRegister n m r) h
    simpa only [packed_first] using he
  · have he := congrArg (fun a => a ∘ targetRegister n m r) h
    simpa only [packed_targetRegister] using he

end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/PhysicalOrderNetworks.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork

lemma packed_append {n m r : ℕ} (x : Basis n) (y : Basis m) :
    packed r x y=Fin.append (Fin.append x y) (fun _=>false) := by
  funext i
  refine Fin.addCases (fun j=>?_) (fun j=>?_) i
  · refine Fin.addCases (fun j=>?_) (fun j=>?_) j
    · exact (packed_input x y j).trans (by simp)
    · exact (packed_target x y j).trans (by simp)
  · rw [packed_work x y _ (by simp),Fin.append_right]

namespace BooleanNetwork

def packNet {k n m : ℕ} (r : ℕ) (a : BooleanNetwork k n) (b : BooleanNetwork k m) :
    BooleanNetwork k (n+m+r) := (a.pair b).pair (Completion.zeros k r)
lemma packNet_eval {k n m r : ℕ} (a : BooleanNetwork k n) (b : BooleanNetwork k m)
    (x : Basis k) : (packNet r a b).eval x=packed r (a.eval x) (b.eval x) := by
  rw [packNet,eval_pair,eval_pair,Completion.zeros_eval,packed_append]
lemma packNet_count {k n m : ℕ} (r : ℕ) (a : BooleanNetwork k n) (b : BooleanNetwork k m) :
    (packNet r a b).net.count=a.net.count+b.net.count+r := by
  simp only [packNet,count_pair,Completion.zeros_count]

end BooleanNetwork
lemma append_false (n m : ℕ) : Fin.append (fun _ : Fin n=>false) (fun _ : Fin m=>false)=fun _=>false := by
  funext i
  refine Fin.addCases (fun j=>?_) (fun j=>?_) i <;> simp only [Fin.append_left,Fin.append_right]

namespace OrderSlots

lemma triangular_zero (b : ℕ) : Triangular.encode b ((fun _=>false),0)=fun _=>false := by
  have h := (basisResidue b).symm_apply_eq.mpr (basisResidue_zero b).symm
  dsimp [Triangular.encode]
  rw [h,packed_append]
  simp only [append_false]

def samplerZeroNet (w b : ℕ) : BooleanNetwork (w+w) (OrderSample.width w b) :=
  packNet (OrderSample.scratch w b)
    ((select id).pair (Completion.zeros (w+w) (Triangular.width b))) (Completion.zeros (w+w) w)
lemma samplerZeroNet_eval {w b : ℕ} (a m : Basis w) :
    (samplerZeroNet w b).eval (Fin.append a m)=OrderSample.word a m (fun _=>false) (fun _=>false) := by
  rw [samplerZeroNet,packNet_eval,eval_pair,eval_select,Completion.zeros_eval,Completion.zeros_eval]
  simp only [Function.comp_id,OrderSample.word,OrderSample.inputWord,triangular_zero]
lemma samplerZeroNet_count (w b : ℕ) :
    (samplerZeroNet w b).net.count=Triangular.width b+w+OrderSample.scratch w b := by
  simp only [samplerZeroNet,packNet_count,count_pair,count_select,Completion.zeros_count,zero_add]

def rawZeroNet (n : ℕ) : BooleanNetwork (n+n) (OrderTrial.rawWidth n (sampleExponent n) n) :=
  (Completion.zeros (n+n) 2).pair
    ((samplerZeroNet n (sampleExponent n+2)).pair (Completion.zeros (n+n) (OrderTrial.guessWidth n)))
lemma rawZeroNet_eval {n : ℕ} (a m : Basis n) :
    (rawZeroNet n).eval (Fin.append a m)=
      OrderTrial.rawLayout n (sampleExponent n) n (OrderTrial.rawZero (sampleExponent n) n a m) := by
  rw [rawZeroNet,eval_pair,eval_pair,Completion.zeros_eval,Completion.zeros_eval,samplerZeroNet_eval]
  simp only [OrderTrial.rawLayout,productLayout_apply,Equiv.refl_apply,OrderTrial.rawZero,
    OrderTrial.guessLayout,OrderTrial.guessZero]
  simp only [append_false]
lemma rawZeroNet_count (n : ℕ) :
    (rawZeroNet n).net.count ≤ OrderTrial.rawWidth n (sampleExponent n) n := by
  simp only [rawZeroNet,count_pair,Completion.zeros_count,samplerZeroNet_count]
  dsimp [OrderTrial.rawWidth,OrderSample.width,OrderSample.inputWidth]
  omega

def ordinaryZeroNet (n : ℕ) : BooleanNetwork (n+n) (ordinaryWidth n) :=
  tensorNetwork (fun _ : Fin (n^5)=>rawZeroNet n)
lemma ordinaryZeroNet_eval {n : ℕ} (a m : Basis n) :
    (ordinaryZeroNet n).eval (Fin.append a m)=ordinaryLayout n (fun _=>OrderTrial.rawZero (sampleExponent n) n a m) := by
  rw [ordinaryZeroNet,tensorNetwork_eval]
  simp only [rawZeroNet_eval,ordinaryLayout,Equiv.trans_apply]
  rfl
lemma ordinaryZeroNet_count (n : ℕ) :
    (ordinaryZeroNet n).net.count ≤ n^5*OrderTrial.rawWidth n (sampleExponent n) n :=
  tensorNetwork_count_le _ (fun _=>rawZeroNet_count n)

def initialNet (n : ℕ) : BooleanNetwork (n+n) (width n) :=
  Completion.initialNet (ordinaryZeroNet n) (Completion.transitionWidth n) (2*n) ((n+10)*n^5)
lemma initialNet_eval {n : ℕ} (a m : Basis n) :
    (initialNet n).eval (Fin.append a m)=layout n (zero a m) := by
  rw [initialNet,Completion.initialNet_eval,ordinaryZeroNet_eval]
  rfl
lemma initialNet_count (n : ℕ) : (initialNet n).net.count ≤
    n^5*OrderTrial.rawWidth n (sampleExponent n) n+2*n+Completion.transitionWidth n+coinWidth n := by
  rw [initialNet,Completion.initialNet_count]
  have h := ordinaryZeroNet_count n
  dsimp only [coinWidth]
  omega

abbrev work (n : ℕ) := (initialNet n).net.count
abbrev launchWidth (n : ℕ) := (n+n)+width n+work n
def launch (n : ℕ) : List (Instruction (launchWidth n)) :=
  preparedOracle (initialNet n) le_rfl (program n)
lemma launch_state {n : ℕ} (a m : Basis n) :
    (programMatrix (launch n)).mulVec (basisVector (packed (work n) (Fin.append a m) (fun _=>false)))=
      encodeState (fun r : Result n=>packed (work n) (Fin.append a m) (layout n r)) (fresh n a m) := by
  rw [launch,preparedOracle_basis,initialNet_eval,program_state,encodeState_comp]
  rfl
lemma launch_length (n : ℕ) : (launch n).length ≤4*work n+2*width n+(program n).length :=
  preparedOracle_length _ _ _

end OrderSlots
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/FactorController.lean =====
namespace OAI

section
open scoped BigOperators


/-! Bounded, guarded binary factor controller for a single auxiliary-tree node.
Only proper divisors are accepted and primality is tested, never assumed.  The
mathematical prime-factor count is used solely in its termination proof. -/
namespace ExactQuantumFactoring.FactorController
open AuxiliaryTree

def ProperDivisor (m d : ℕ) : Prop := 1 < d ∧ d < m ∧ d ∣ m
instance (m d : ℕ) : Decidable (ProperDivisor m d) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

lemma ProperDivisor.quotient {m d : ℕ} (h : ProperDivisor m d) :
    2 ≤ m/d ∧ m/d < m ∧ d*(m/d)=m := by
  rcases h with ⟨hd,hdm,hdiv⟩
  have he := Nat.mul_div_cancel' hdiv
  have hp : 0 < m/d := Nat.div_pos (by omega) (by omega)
  have hl : m/d < m := Nat.div_lt_self (by omega) hd
  refine ⟨?_,hl,he⟩
  by_contra hh
  have : m/d=1 := by omega
  rw [this,mul_one] at he
  omega

lemma splitWeight_pos {m : ℕ} (hm : 2 ≤ m) : 0 < splitWeight m := by
  by_contra h
  have hl : m.primeFactorsList=[] := List.length_eq_zero_iff.mp (by
    change splitWeight m=0
    omega)
  have he := Nat.prod_primeFactorsList (by omega : m≠0)
  rw [hl,List.prod_nil] at he
  omega

lemma splitWeight_mul {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    splitWeight (a*b)=splitWeight a+splitWeight b := by
  have hh := (Nat.perm_primeFactorsList_mul ha.ne' hb.ne').length_eq
  simpa only [splitWeight,List.length_append] using hh

lemma splitWeight_split {m d : ℕ} (h : ProperDivisor m d) :
    splitWeight m=splitWeight d+splitWeight (m/d) := by
  have hq := h.quotient
  conv_lhs =>  rw [← hq.2.2]
  exact splitWeight_mul (by have := h.1; omega) (by omega)

def weight (ms : List ℕ) : ℕ := (ms.map (fun m =>  2*splitWeight m-1)).sum

lemma weight_prime (m : ℕ) (ms : List ℕ) (hm : m.Prime) :
    weight (m::ms)=weight ms+1 := by
  simp [weight,splitWeight,Nat.primeFactorsList_prime hm,Nat.add_comm]

lemma weight_split {m d : ℕ} (h : ProperDivisor m d) (ms : List ℕ) :
    weight (m::ms)=weight (d::m/d::ms)+1 := by
  have hd := splitWeight_pos (by have := h.1; omega : 2 ≤ d)
  have hq := splitWeight_pos h.quotient.1
  have he := splitWeight_split h
  simp only [weight,List.map_cons,List.sum_cons]
  omega

/-- `choose i m` is the prospective divisor obtained at the i-th guarded
controller step from its recorded classical transition outputs. -/
def run (choose : ℕ→ℕ→ℕ) : ℕ→ℕ→List ℕ→Option (List ℕ)
  | _, _, [] =>  some []
  | 0, _, _::_ =>  none
  | fuel+1, i, m::ms => 
    if m.Prime then (run choose fuel (i+1) ms).map (m::·)
    else let d := choose i m
         if ProperDivisor m d then run choose fuel (i+1) (d::m/d::ms) else none

/-- On every output sequence, a successful result is a genuine complete
factorization. Bad divisors cause an abort, not a false prime leaf. -/
theorem run_sound (choose : ℕ→ℕ→ℕ) {fuel i : ℕ} {ms ps : List ℕ}
    (h : run choose fuel i ms=some ps) :
    (∀ p∈ps, p.Prime) ∧ ps.prod=ms.prod := by
  induction fuel generalizing i ms ps with
  | zero => 
    cases ms with
    | nil =>  simp only [run,Option.some.injEq] at h; subst ps; simp
    | cons m ms =>  simp [run] at h
  | succ fuel ih => 
    cases ms with
    | nil =>  simp only [run,Option.some.injEq] at h; subst ps; simp
    | cons m ms => 
      simp only [run] at h
      split_ifs at h with hp hd
      · obtain ⟨qs,hq,hps⟩ := Option.map_eq_some_iff.mp h
        subst ps
        obtain ⟨hprime,hprod⟩ := ih hq
        exact ⟨by simpa only [List.mem_cons,forall_eq_or_imp] using And.intro hp hprime,
          by simp only [List.prod_cons,hprod]⟩
      · obtain ⟨hprime,hprod⟩ := ih h
        refine ⟨hprime,?_⟩
        rw [List.prod_cons,List.prod_cons,← Nat.mul_assoc,hd.quotient.2.2] at hprod
        exact hprod

/-- All-good divisors cannot exhaust the linear (in logarithmic input size)
controller clock. This theorem controls arbitrary supplied good outputs. -/
theorem run_complete (choose : ℕ→ℕ→ℕ) {N fuel i : ℕ} {ms : List ℕ}
    (hgood : ∀ i m, 2 ≤ m → m ≤ N → ¬m.Prime → ProperDivisor m (choose i m))
    (hms : ∀ m∈ms, 2 ≤ m ∧ m ≤ N) (hw : weight ms ≤ fuel) :
    ∃ ps, run choose fuel i ms=some ps := by
  induction fuel generalizing i ms with
  | zero => 
    cases ms with
    | nil =>  exact ⟨[],rfl⟩
    | cons m ms => 
      have hm := hms m (by simp)
      have hp := splitWeight_pos hm.1
      simp only [weight,List.map_cons,List.sum_cons] at hw
      omega
  | succ fuel ih => 
    cases ms with
    | nil =>  exact ⟨[],rfl⟩
    | cons m ms => 
      have hm := hms m (by simp)
      have htail : ∀ a∈ms, 2 ≤ a ∧ a ≤ N := fun a ha =>  hms a (by simp [ha])
      by_cases hp : m.Prime
      · have hw' : weight ms ≤ fuel := by rw [weight_prime m ms hp] at hw; omega
        obtain ⟨ps,hps⟩ := ih htail hw' (i:=i+1)
        refine ⟨m::ps,?_⟩
        simp only [run,ite_eq_left hp,hps,Option.map_some]
      · have hd := hgood i m hm.1 hm.2 hp
        have hq := hd.quotient
        have hms' : ∀ a∈choose i m::m/choose i m::ms, 2 ≤ a ∧ a ≤ N := by
          intro a ha
          rcases List.mem_cons.mp ha with rfl | ha
          · exact ⟨by have := hd.1; omega,hd.2.1.le.trans hm.2⟩
          · rcases List.mem_cons.mp ha with rfl | ha
            · exact ⟨hq.1,hq.2.1.le.trans hm.2⟩
            · exact htail a ha
        have hw' : weight (choose i m::m/choose i m::ms) ≤ fuel := by
          rw [weight_split hd ms] at hw
          omega
        obtain ⟨ps,hps⟩ := ih hms' hw' (i:=i+1)
        exact ⟨ps,by simpa only [run,ite_eq_right hp,ite_eq_left hd] using hps⟩

/-- A 2n-step clock suffices for every bounded node. Its successful list is
then sorted, padded and passed to the concrete verifier. -/
theorem bounded_node_complete {N n : ℕ} (hN : 2 ≤ N) (hb : N < 2^n)
    (choose : ℕ→ℕ→ℕ)
    (hgood : ∀ i m, 2 ≤ m → m ≤ N → ¬m.Prime → ProperDivisor m (choose i m)) :
    ∃ ps, run choose (2*n) 0 [N]=some ps ∧
      (∀ p∈ps, p.Prime) ∧ ps.prod=N ∧ ps.length < n := by
  have hw : weight [N] ≤ 2*n := by
    have h := splitWeight_bound (by omega) hb
    simp only [weight,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
    omega
  obtain ⟨ps,hps⟩ := run_complete choose hgood (by simpa using And.intro hN (le_rfl : N ≤ N)) hw (i:=0)
  have hs := run_sound choose hps
  have hprod : ps.prod=N := by simpa using hs.2
  have hlen : ps.length=splitWeight N := (Nat.primeFactorsList_unique hprod hs.1).length_eq
  exact ⟨ps,hps,hs.1,hprod,hlen.trans_lt (splitWeight_bound (by omega) hb)⟩

end ExactQuantumFactoring.FactorController


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/FavorableSplit.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring

lemma component_modulus_two_lt {m : ℕ} (hm : m≠0) (hodd : Odd m) (p : Component m) :
    2 < p.val^m.factorization p.val := by
  have hp := Nat.mem_primeFactors.mp p.property
  have hp2 : p.val≠2 := by
    intro he
    have hdiv : 2∣m := he ▸ hp.2.1
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdiv)
  exact (lt_of_le_of_ne hp.1.two_le (Ne.symm hp2)).trans_le
    (Nat.le_pow (hp.1.factorization_pos_of_dvd hm hp.2.1))

lemma unitCRT_apply {m : ℕ} (hm : m≠0) (a : (ZMod m)ˣ) (p : Component m) :
    unitCRT m hm a p=Units.map (ZMod.castHom (Nat.ordProj_dvd m p.val)
      (ZMod (p.val^m.factorization p.val))).toMonoidHom a := by
  apply Units.ext
  change ZMod.equivPi m hm (a : ZMod m) p = _
  exact RingHom.congr_fun (Subsingleton.elim
    ((Pi.evalRingHom (fun p : Component m => ZMod (p.val^m.factorization p.val)) p).comp
      (ZMod.equivPi m hm).toRingHom)
    (ZMod.castHom (Nat.ordProj_dvd m p.val) (ZMod (p.val^m.factorization p.val)))) (a : ZMod m)

/-- A favorable CRT event supplies a proper split from the actual true order. -/
theorem favorable_split {m n : ℕ} (hm : 2 ≤ m) (hb : m < 2^n) (hodd : Odd m)
    (p₀ : Component m) (a : (ZMod m)ˣ) (hf : FavorableUnit (by omega : m≠0) hb p₀ a) :
    2 ∣ orderOf a ∧ FactorController.ProperDivisor m (splitGcd a) := by
  classical
  obtain ⟨p,hp⟩ := not_forall.mp hf
  have hneq : padicValNat 2 (orderOf (unitCRT m (by omega) a p)) ≠
      padicValNat 2 (orderOf (unitCRT m (by omega) a p₀)) := by
    exact fun he => hp (Fin.ext he)
  simp only [unitCRT_apply] at hneq
  have hproper := splitGcd_proper_of_unequal_components hm
    (component_modulus_two_lt (by omega) hodd p).le
    (component_modulus_two_lt (by omega) hodd p₀).le
    (Nat.ordProj_dvd m p.val) (Nat.ordProj_dvd m p₀.val) a hneq
  let f := Units.map (ZMod.castHom (Nat.ordProj_dvd m p.val)
    (ZMod (p.val^m.factorization p.val))).toMonoidHom
  let g := Units.map (ZMod.castHom (Nat.ordProj_dvd m p₀.val)
    (ZMod (p₀.val^m.factorization p₀.val))).toMonoidHom
  have hr : orderOf a≠0 := (orderOf_pos a).ne'
  have hp' := level_le_of_dvd hr (orderOf_map_dvd f a)
  have h₀ := level_le_of_dvd hr (orderOf_map_dvd g a)
  have heven : 2∣orderOf a := dvd_of_one_le_padicValNat (by
    change padicValNat 2 (orderOf (f a)) ≠ padicValNat 2 (orderOf (g a)) at hneq
    omega)
  exact ⟨heven,hproper⟩

/-- The distinguished CRT residue used in the list-completion branch. The
parameter p₀ is subsequently chosen as the least prime component. -/
noncomputable def canonicalUnit {m : ℕ} (hm : m≠0) (p₀ : Component m) : (ZMod m)ˣ :=
  (unitCRT m hm).symm (fun p => if p=p₀ then 1 else -1)

lemma canonicalUnit_component {m : ℕ} (hm : m≠0) (p₀ p : Component m) :
    unitCRT m hm (canonicalUnit hm p₀) p=if p=p₀ then 1 else -1 := by
  rw [canonicalUnit,MulEquiv.apply_symm_apply]

lemma component_neg_one_order {m : ℕ} (hm : m≠0) (hodd : Odd m) (p : Component m) :
    orderOf (-1 : ComponentUnits m p)=2 := by
  have hd := component_modulus_two_lt hm hodd p
  let : Fact (1 < p.val^m.factorization p.val) := ⟨by omega⟩
  rw [← orderOf_units]
  change orderOf (-1 : ZMod (p.val^m.factorization p.val))=2
  rw [orderOf_neg_one,ringChar.eq _ (p.val^m.factorization p.val),ite_eq_right (by omega)]

lemma canonicalUnit_favorable {m n : ℕ} (hm : m≠0) (hb : m < 2^n) (hodd : Odd m)
    (p₀ p₁ : Component m) (hne : p₁≠p₀) :
    FavorableUnit hm hb p₀ (canonicalUnit hm p₀) := by
  intro h
  have he := congrArg Fin.val (h p₁)
  simp only [componentLevel,canonicalUnit_component,ite_eq_right hne,
    component_neg_one_order hm hodd p₁] at he
  norm_num at he

end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/CanonicalTransition.lean =====
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

noncomputable def canonicalList {m : ℕ} (hm : m≠0) (p₀ : Component m) (K : ℕ) :
    Fin K→Basis (Nat.clog 2 m) := fun i =>
  (bitsEquiv _).symm (BitVec.ofNat (Nat.clog 2 m) (if i.val=0 then (canonicalUnit hm p₀ : ZMod m).val else 0))

lemma canonicalList_good {m n K : ℕ} (hm : m≠0) (hb : m<2^n) (hodd : Odd m)
    (p₀ p₁ : Component m) (hne : p₁≠p₀) (hK : 0<K) :
    GoodList hm hb p₀ K (canonicalList hm p₀ K) := by
  let : NeZero m := ⟨hm⟩
  refine ⟨⟨0,hK⟩,canonicalUnit hm p₀,?_,canonicalUnit_favorable hm hb hodd p₀ p₁ hne⟩
  simp only [canonicalList,bitsEquiv,Equiv.coe_fn_symm_mk,bitsValue_bits,
    BitVec.toNat_ofNat]
  exact (Nat.mod_eq_of_lt ((ZMod.val_lt _).trans_le (Nat.le_pow_clog (by decide : 1<2) m))).symm

end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/PhaseOracle.lean =====
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

lemma phase_twice_basis {q : ℕ} (t : Fin q) (x : Basis q) :
    (programMatrix [phaseAt t,phaseAt t]).mulVec (basisVector x) =
      (if x t then (-1:ℂ) else 1) • basisVector x := by
  classical
  rw [programMatrix_cons, programMatrix_singleton, ← Matrix.mulVec_mulVec]
  funext y
  rw [phaseAt_apply, phaseAt_apply]
  simp only [Pi.smul_apply, smul_eq_mul, basisVector]
  by_cases h : y=x
  · subst y
    cases x t <;> simp [Complex.I_mul_I]
  · simp [h]

namespace BooleanNetwork

def phaseTarget {n r : ℕ} : Fin (n+1+r) := ⟨n,by omega⟩

/-- Predicate phase kickback is a clean oracle, two S gates, and the same
clean XOR oracle again, all over the fixed gate alphabet. -/
def phaseOracle {n r : ℕ} (c : BooleanNetwork n 1) (hr : c.net.count ≤ r) :
    List (Instruction (n+1+r)) :=
  oracleOn c hr ++ [phaseAt phaseTarget,phaseAt phaseTarget] ++ oracleOn c hr

lemma phaseOracle_length {n r : ℕ} (c : BooleanNetwork n 1) (hr : c.net.count ≤ r) :
    (phaseOracle c hr).length ≤ 8*c.net.count+6 := by
  have h := oracleOn_length c hr
  simp only [phaseOracle, List.length_append, List.length_cons, List.length_nil]
  omega

lemma phaseOracle_basis {n r : ℕ} (c : BooleanNetwork n 1) (hr : c.net.count ≤ r)
    (x : Basis n) :
    (programMatrix (phaseOracle c hr)).mulVec (basisVector (packed r x (fun _ => false))) =
      (if c.eval x 0 then (-1:ℂ) else 1) • basisVector (packed r x (fun _ => false)) := by
  rw [phaseOracle, programMatrix_append, programMatrix_append,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, oracleOn_basis]
  simp only [Bool.false_xor]
  rw [phase_twice_basis, Matrix.mulVec_smul, oracleOn_basis]
  have ht : packed r x (c.eval x) phaseTarget = c.eval x 0 := by
    exact packed_target x (c.eval x) 0
  rw [ht]
  congr 1
  funext i
  simp

/-- The same actual program applies its diagonal predicate phase coherently,
not just on classical basis inputs. -/
lemma phaseOracle_state {n r : ℕ} (c : BooleanNetwork n 1) (hr : c.net.count ≤ r)
    (ψ : Basis n → ℂ) :
    (programMatrix (phaseOracle c hr)).mulVec
      (encodeState (fun x => packed r x (fun _ : Fin 1 => false)) ψ) =
      encodeState (fun x => packed r x (fun _ : Fin 1 => false))
        (fun x => (if c.eval x 0 then (-1:ℂ) else 1)*ψ x) := by
  classical
  rw [encodeState, Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul, phaseOracle_basis, smul_smul]
  unfold encodeState
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  ring

/-- Bounded fan-in conjunction, built incrementally, not an unbounded gate. -/
def allZero (n : ℕ) : (k : ℕ) → k ≤ n → BooleanNetwork n 1
  | 0, _ => constant true
  | k+1, h => (allZero n k (by omega)).band (bit ⟨k,by omega⟩).bnot

lemma allZero_count (n k : ℕ) (hk : k ≤ n) :
    (allZero n k hk).net.count = 2*k+1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [allZero, ih]; omega

lemma allZero_eval (n k : ℕ) (hk : k ≤ n) (x : Basis n) :
    (allZero n k hk).eval x 0 = true ↔ ∀ i : Fin n, i.val < k → x i = false := by
  induction k with
  | zero => simp [allZero]
  | succ k ih =>
    simp only [allZero, eval_band, eval_bnot, eval_bit, Bool.and_eq_true,
      Bool.not_eq_true', ih (by omega)]
    constructor
    · rintro ⟨h₁,h₂⟩ i hi
      by_cases he : i.val=k
      · have hh : i = (⟨k,by omega⟩ : Fin n) := Fin.ext he
        simpa only [hh] using h₂
      · exact h₁ i (by omega)
    · intro h
      exact ⟨fun i hi => h i (by omega), h ⟨k,by omega⟩ (by simp)⟩

lemma allZero_full (n : ℕ) (x : Basis n) :
    (allZero n n le_rfl).eval x 0 = true ↔ x = (fun _ => false) := by
  rw [allZero_eval]
  constructor
  · intro h; funext i; exact h i i.isLt
  · rintro rfl; simp

end BooleanNetwork
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/PhysicalAmplification.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open BooleanNetwork Exactness

/-- A support invariant for a read-only classical input sector. -/
def Supported {ι : Type*} (S : ι → Prop) (v : ι → ℂ) : Prop :=
  ∀ x, ¬ S x → v x = 0

/-- Matrix entries cannot change the read-only input. -/
def RespectsSector {ι : Type*} (S : ι → Prop) (U : Matrix ι ι ℂ) : Prop :=
  ∀ x y, ¬ (S x ↔ S y) → U x y = 0

lemma RespectsSector.adjoint {ι : Type*} (S : ι → Prop) (U : Matrix ι ι ℂ)
    (h : RespectsSector S U) : RespectsSector S U.conjTranspose := by
  intro x y hxy
  change star (U y x) = 0
  rw [h y x (fun hyx => hxy hyx.symm),star_zero]

lemma RespectsSector.supported {ι : Type*} [Fintype ι] (S : ι → Prop)
    (U : Matrix ι ι ℂ) (h : RespectsSector S U) (v : ι → ℂ)
    (hv : Supported S v) : Supported S (U.mulVec v) := by
  classical
  intro x hx
  apply Finset.sum_eq_zero
  intro y _
  by_cases hy : S y
  · exact mul_eq_zero.mpr (Or.inl (h x y (by tauto)))
  · rw [hv y hy,mul_zero]

noncomputable def signState {ι : Type*} (p : ι → Bool) (v : ι → ℂ) : ι → ℂ :=
  fun x => (if p x then (-1:ℂ) else 1)*v x

lemma signState_supported {ι : Type*} (S : ι → Prop) (p : ι → Bool)
    (v : ι → ℂ) (hv : Supported S v) : Supported S (signState p v) := by
  intro x hx
  simp only [signState,hv x hx,mul_zero]

lemma signState_eq {ι : Type*} (p : ι → Bool) (v : ι → ℂ) :
    signState p v = fun x => v x-2*goodPart (fun y => p y=true) v x := by
  classical
  funext x
  simp only [signState,goodPart]
  split_ifs <;> ring

lemma sector_zero_sign {ι : Type*} [DecidableEq ι] (S : ι → Prop)
    (z : ι) (p : ι → Bool) (hp : ∀ x, S x → (p x=true ↔ x=z))
    (v : ι → ℂ) (hv : Supported S v) :
    signState p v = v - ((2*v z) • basisVector z) := by
  classical
  funext x
  simp only [signState,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,basisVector]
  by_cases hx : S x
  · by_cases he : x=z
    · subst x
      simp [hp z hx]
      ring
    · simp [he, show p x ≠ true from fun h => he ((hp x hx).mp h)]
  · have hvx := hv x hx
    by_cases he : x=z
    · subst x
      simp [hvx]
    · simp [he,hvx]

lemma adjoint_coordinate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) (z : ι) (v : ι → ℂ) :
    U.conjTranspose.mulVec v z = finiteInner (U.mulVec (basisVector z)) v := by
  rw [matrix_basisVector]
  rfl

/-- The physical sign on zero work, conjugated by a reversible preparation,
is minus the reflection about its output, within the invariant input fiber. -/
lemma conjugated_zero_sign {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) (hu : U ∈ Matrix.unitaryGroup ι ℂ)
    (S : ι → Prop) (hS : RespectsSector S U) (z : ι)
    (p : ι → Bool) (hp : ∀ x, S x → (p x=true ↔ x=z))
    (v : ι → ℂ) (hv : Supported S v) :
    U.mulVec (signState p (U.conjTranspose.mulVec v)) =
      -stateReflection (U.mulVec (basisVector z)) v := by
  rw [sector_zero_sign S z p hp _
    ((hS.adjoint S U).supported S U.conjTranspose _ hv)]
  have huu : U * U.conjTranspose = 1 := Matrix.mem_unitaryGroup_iff.mp hu
  rw [Matrix.mulVec_sub,Matrix.mulVec_smul,Matrix.mulVec_mulVec,
    huu,Matrix.one_mulVec,adjoint_coordinate]
  funext x
  simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.neg_apply,stateReflection]
  ring

/-- Five actual programs: prepare, mark good, unprepare, mark zero work,
prepare. The two phase predicates share a clean flag and scratch area. -/
def amplificationProgram {n r : ℕ} (ops : List (Instruction n))
    (good zero : BooleanNetwork n 1) (hg : good.net.count ≤ r) (hz : zero.net.count ≤ r) :
    List (Instruction (n+1+r)) :=
  firstProgram 1 r ops ++ phaseOracle good hg ++
    firstProgram 1 r (ops.reverse.map Instruction.reverse) ++ phaseOracle zero hz ++
      firstProgram 1 r ops

lemma amplificationProgram_length {n r : ℕ} (ops : List (Instruction n))
    (good zero : BooleanNetwork n 1) (hg : good.net.count ≤ r) (hz : zero.net.count ≤ r) :
    (amplificationProgram ops good zero hg hz).length ≤
      3*ops.length+8*good.net.count+8*zero.net.count+12 := by
  have h₁ := phaseOracle_length good hg
  have h₂ := phaseOracle_length zero hz
  simp only [amplificationProgram,List.length_append,firstProgram_length,
    List.length_map,List.length_reverse]
  omega

lemma amplificationProgram_state {n r : ℕ} (ops : List (Instruction n))
    (good zero : BooleanNetwork n 1) (hg : good.net.count ≤ r) (hz : zero.net.count ≤ r)
    (z : Basis n) :
    (programMatrix (amplificationProgram ops good zero hg hz)).mulVec
      (basisVector (packed r z (fun _ : Fin 1 => false))) =
    encodeState (fun x => packed r x (fun _ : Fin 1 => false))
      ((programMatrix ops).mulVec (signState (fun x => zero.eval x 0)
        ((programMatrix ops).conjTranspose.mulVec
          (signState (fun x => good.eval x 0)
            ((programMatrix ops).mulVec (basisVector z)))))) := by
  rw [amplificationProgram]
  simp only [programMatrix_append,← Matrix.mulVec_mulVec]
  rw [firstProgram_basis,phaseOracle_state,firstProgram_state,programMatrix_reverse]
  rw [phaseOracle_state,firstProgram_state]
  rfl

/-- Exact amplitude amplification implemented over the fixed named gates.
The semantic premises are preparation mass and the unchanged-input invariant,
not a gate oracle or an assumed reflection. -/
theorem physical_quarter_amplification {n r : ℕ} (ops : List (Instruction n))
    (good zero : BooleanNetwork n 1) (hg : good.net.count ≤ r) (hz : zero.net.count ≤ r)
    (S : Basis n → Prop) (hS : RespectsSector S (programMatrix ops))
    (z : Basis n) (hstart : S z)
    (hzero : ∀ x, S x → (zero.eval x 0=true ↔ x=z))
    (hquarter : outcomeMass (fun x => good.eval x 0=true)
      ((programMatrix ops).mulVec (basisVector z)) = 1/4) :
    (programMatrix (amplificationProgram ops good zero hg hz)).mulVec
      (basisVector (packed r z (fun _ : Fin 1 => false))) =
      encodeState (fun x => packed r x (fun _ : Fin 1 => false))
        (fun x => -2*goodPart (fun y => good.eval y 0=true)
          ((programMatrix ops).mulVec (basisVector z)) x) := by
  classical
  have hs : Supported S (basisVector z) := by
    intro x hx
    simp [basisVector,show x ≠ z from fun h => hx (h ▸ hstart)]
  have hv := hS.supported S (programMatrix ops) (basisVector z) hs
  have hn : (∑ x, Complex.normSq ((programMatrix ops).mulVec (basisVector z) x)) = 1 := by
    rw [unitary_mass _ (programMatrix_unitary ops)]
    simp [basisVector]
  rw [amplificationProgram_state,
    conjugated_zero_sign _ (programMatrix_unitary ops) S hS z _ hzero _
      (signState_supported S _ _ hv),signState_eq,
    one_reflection _ _ hn hquarter]
  congr 1
  funext x
  simp only [Pi.neg_apply]
  ring

end ExactQuantumFactoring


end

end OAI


