-- Prove2me | Definitions.Def_OAI_QuantumFactoring_Part01
-- name    : OAI_QuantumFactoring_Part01
-- status  : Definition
-- author  : @SamenHossain
-- created : 2026-10-12T06:54:07.943753+00:00
-- url     : https://prove2.me/theorems/f13c397f-e8f2-4d10-b863-4c1be9c46758
-- title:
--   Exact quantum factoring, part 1 of 38 (port of OpenAI's formalization)
-- statement:
--   Part 1 of 38 of a port of OpenAI's Lean formalization of the manuscript *Exact quantum factoring over a fixed finite gate set* (OpenAI, September 25, 2026). This part contains the modules `ExactnessFurther`, `RepeatedTrials`, `GateSemantics`, `CircuitSemantics`, `BooleanCircuit`, `BooleanProgram`, `BooleanNetwork`, `BooleanNetworkFurther`, `BooleanAlgebra`, `BooleanVector`.
--
--   **Attribution.** The code is adapted from the OpenAI "math" repository, commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, directory `lean/OAI/Computability/QuantumFactoring`. It is © OpenAI and licensed under the Apache License 2.0; the adapted code is redistributed under the same license.
--
--   **Modifications.** Modules are concatenated in dependency order, with their imports replaced by the previous part. The model definitions come from the platform definition `ExactQuantumFactoring`, which is identical to upstream `Basic.lean`. Part 1 also adds compatibility shims restating four core lemmas (`ite_eq_left`, `ite_eq_right`, `dite_eq_left`, `dite_eq_right`) absent from Lean 4.33.1.
--
--   The development is split into 38 parts only so that each compiles within the platform's time limit. Together the parts supply the circuit family `PhysicalTree.finalCircuit` and its specification, used to prove `OAI.ExactQuantumFactoring.zero_amplitude_core`.
-- source:
--   OpenAI, openai/math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, lean/OAI/Computability/QuantumFactoring: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/ExactnessFurther.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/RepeatedTrials.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/GateSemantics.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/CircuitSemantics.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/BooleanCircuit.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/BooleanProgram.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/BooleanNetwork.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/BooleanNetworkFurther.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/BooleanAlgebra.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/BooleanVector.lean (Apache License 2.0); manuscript https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Exact-quantum-factoring-over-a-fixed-finite-gate-set-September-25-2026/main.pdf

/-
Exact quantum factoring development (port of OpenAI's formalization), part 1 of 38.

Adapted from the OpenAI "math" repository (https://github.com/openai/math, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a), lean/OAI/Computability/QuantumFactoring/: ExactnessFurther.lean, RepeatedTrials.lean, GateSemantics.lean, CircuitSemantics.lean, BooleanCircuit.lean, BooleanProgram.lean, BooleanNetwork.lean, BooleanNetworkFurther.lean, BooleanAlgebra.lean, BooleanVector.lean
These files formalize the manuscript "Exact quantum factoring over a fixed finite gate set"
(OpenAI, September 25, 2026). Copyright OpenAI. Licensed under the Apache License, Version 2.0
(http://www.apache.org/licenses/LICENSE-2.0); the adapted code is distributed under the same license,
on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND.

Modifications: modules concatenated in dependency order with their import lines removed; the model
definitions (Basic.lean) come from the platform definition `ExactQuantumFactoring`, to which upstream
Basic.lean is identical; the final assembly (Main.lean) is omitted; compatibility shims restating four core lemmas absent from Lean 4.33.1 are added.
-/
import Mathlib
import Definitions.Def_ExactQuantumFactoring

set_option autoImplicit false

-- Compatibility shims: core lemmas present in newer Lean versions used upstream but not in
-- Lean 4.33.1, restated from `if_pos`, `if_neg`, `dif_pos` and `dif_neg`.
namespace OAI

theorem ite_eq_left {c : Prop} {_ : Decidable c} {α : Sort*} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h

theorem ite_eq_right {c : Prop} {_ : Decidable c} {α : Sort*} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h

theorem dite_eq_left {c : Prop} {_ : Decidable c} {α : Sort*} {t : c → α} {e : ¬c → α}
    (h : c) : dite c t e = t h := dif_pos h

theorem dite_eq_right {c : Prop} {_ : Decidable c} {α : Sort*} {t : c → α} {e : ¬c → α}
    (h : ¬c) : dite c t e = e h := dif_neg h

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/ExactnessFurther.lean =====
namespace OAI

section

namespace ExactQuantumFactoring.Exactness
open scoped BigOperators

noncomputable def finiteInner {ι : Type*} [Fintype ι] (v w : ι → ℂ) : ℂ :=
  ∑ x, star (v x)*w x

noncomputable def outcomeMass {ι : Type*} [Fintype ι] (good : ι → Prop) (v : ι → ℂ) : ℝ := by
  classical
  exact ∑ x, if good x then Complex.normSq (v x) else 0

noncomputable def goodPart {ι : Type*} (good : ι → Prop) (v : ι → ℂ) : ι → ℂ := by
  classical
  exact fun x => if good x then v x else 0

noncomputable def stateReflection {ι : Type*} [Fintype ι] (ψ v : ι → ℂ) : ι → ℂ :=
  fun x => 2*finiteInner ψ v*ψ x-v x

lemma finiteInner_self {ι : Type*} [Fintype ι] (v : ι → ℂ) :
    finiteInner v v = ((∑ x, Complex.normSq (v x):ℝ):ℂ) := by
  simp only [finiteInner, Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self,
    Complex.star_def]

lemma finiteInner_goodPart {ι : Type*} [Fintype ι] (good : ι → Prop) (v : ι → ℂ) :
    finiteInner v (goodPart good v) = (outcomeMass good v:ℂ) := by
  classical
  unfold finiteInner goodPart outcomeMass
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp [Complex.normSq_eq_conj_mul_self]

lemma finiteInner_sub {ι : Type*} [Fintype ι] (u v w : ι → ℂ) :
    finiteInner u (fun x => v x-w x) = finiteInner u v-finiteInner u w := by
  simp only [finiteInner, mul_sub, Finset.sum_sub_distrib]

lemma finiteInner_mul {ι : Type*} [Fintype ι] (u v : ι → ℂ) (c : ℂ) :
    finiteInner u (fun x => c*v x) = c*finiteInner u v := by
  simp only [finiteInner]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- Literal one-reflection identity (6.9). The amplitude is not renormalized by fiat. -/
lemma one_reflection {ι : Type*} [Fintype ι] (good : ι → Prop) (ψ : ι → ℂ)
    (hψ : (∑ x, Complex.normSq (ψ x))=1) (hg : outcomeMass good ψ=1/4) :
    stateReflection ψ (fun x => ψ x-2*goodPart good ψ x) = fun x => 2*goodPart good ψ x := by
  have h := finiteInner_goodPart good ψ
  rw [hg] at h
  have hn := finiteInner_self ψ
  rw [hψ] at hn
  ext x
  simp only [stateReflection, finiteInner_sub, finiteInner_mul, h, hn]
  norm_num

lemma amplified_mass {ι : Type*} [Fintype ι] (good : ι → Prop) (ψ : ι → ℂ)
    (hg : outcomeMass good ψ=1/4) :
    outcomeMass good (fun x => 2*goodPart good ψ x)=1 := by
  classical
  have he : outcomeMass good (fun x => 2*goodPart good ψ x)=4*outcomeMass good ψ := by
    unfold outcomeMass goodPart
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : good x
    · simp [hx, Complex.normSq_mul]
      norm_num
    · simp [hx]
  rw [he,hg]
  norm_num

/-- Exact success also applies to the externally requested correct-output predicate. -/
lemma one_reflection_correct {ι : Type*} [Fintype ι]
    (good correct : ι → Prop) (ψ : ι → ℂ)
    (hψ : (∑ x, Complex.normSq (ψ x))=1)
    (hg : outcomeMass good ψ=1/4) (hc : ∀ x, good x → correct x) :
    outcomeMass correct (stateReflection ψ (fun x => ψ x-2*goodPart good ψ x))=1 := by
  classical
  rw [one_reflection good ψ hψ hg]
  have he : outcomeMass correct (fun x => 2*goodPart good ψ x)=
      outcomeMass good (fun x => 2*goodPart good ψ x) := by
    unfold outcomeMass goodPart
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : good x
    · simp [hx,hc x hx]
    · simp [hx]
  rw [he]
  exact amplified_mass good ψ hg

end ExactQuantumFactoring.Exactness


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/RepeatedTrials.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators


/-! Exact independent-trial laws and the source's K=n^5 success guarantee. -/
namespace ExactQuantumFactoring.RepeatedTrials
open scoped BigOperators
open ExactQuantumFactoring.Exactness

noncomputable def tensorState {α : Type*} (ψ : α→ℂ) (K : ℕ) (x : Fin K→α) : ℂ :=
  ∏ i, ψ (x i)

lemma tensor_normalized {α : Type*} [Fintype α] (ψ : α→ℂ) (K : ℕ)
    (hψ : ∑ x, Complex.normSq (ψ x)=1) :
    ∑ x : Fin K→α, Complex.normSq (tensorState ψ K x)=1 := by
  classical
  simp only [tensorState,map_prod]
  calc
    _ = (∑ x, Complex.normSq (ψ x))^K := (Fintype.sum_pow (fun x => Complex.normSq (ψ x)) K).symm
    _ = 1 := by rw [hψ,one_pow]

lemma tensor_all_mass {α : Type*} [Fintype α] (ψ : α→ℂ) (K : ℕ) (P : α→Prop) :
    outcomeMass (fun x : Fin K→α => ∀ i, P (x i)) (tensorState ψ K) = (outcomeMass P ψ)^K := by
  classical
  unfold outcomeMass tensorState
  calc
    _ = ∑ x : Fin K→α, ∏ i, if P (x i) then Complex.normSq (ψ (x i)) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : ∀ i, P (x i)
      · simp [hx,map_prod]
      · obtain ⟨i,hi⟩ := not_forall.mp hx
        rw [ite_eq_right hx]
        symm
        exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)
    _ = _ := (Fintype.sum_pow (fun x => if P x then Complex.normSq (ψ x) else 0) K).symm

lemma mass_compl {α : Type*} [Fintype α] (ψ : α→ℂ) (P : α→Prop)
    (hψ : ∑ x, Complex.normSq (ψ x)=1) :
    outcomeMass (fun x => ¬P x) ψ=1-outcomeMass P ψ := by
  classical
  have he : outcomeMass (fun x => ¬P x) ψ + outcomeMass P ψ = 1 := by
    unfold outcomeMass
    rw [← Finset.sum_add_distrib,← hψ]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : P x <;> simp [hx]
  linarith

lemma tensor_some_mass {α : Type*} [Fintype α] (ψ : α→ℂ) (K : ℕ) (P : α→Prop)
    (hψ : ∑ x, Complex.normSq (ψ x)=1) :
    outcomeMass (fun x : Fin K→α => ∃ i, P (x i)) (tensorState ψ K) =
      1-(1-outcomeMass P ψ)^K := by
  classical
  have he : (fun x : Fin K→α => ∃ i, P (x i)) =
      (fun x => ¬∀ i, ¬P (x i)) := by funext x; simp
  rw [he,mass_compl _ _ (tensor_normalized ψ K hψ)]
  rw [tensor_all_mass ψ K (fun x => ¬P x),mass_compl ψ P hψ]

lemma mass_bounds {α : Type*} [Fintype α] (ψ : α→ℂ) (P : α→Prop)
    (hψ : ∑ x, Complex.normSq (ψ x)=1) : 0≤outcomeMass P ψ ∧ outcomeMass P ψ≤1 := by
  classical
  unfold outcomeMass
  constructor
  · apply Finset.sum_nonneg
    intro x _
    have hh := Complex.normSq_nonneg (ψ x)
    split_ifs <;> linarith
  · rw [← hψ]
    apply Finset.sum_le_sum
    intro x _
    have hh := Complex.normSq_nonneg (ψ x)
    split_ifs <;> linarith

/-- Deliberately uses the original cutoff128 and repetition exponent5. -/
lemma repetition_failure_bound {n : ℕ} (hn : 128≤n) {x : ℝ}
    (hx₀ : 1/(2048*(n+1):ℝ)≤x) (hx₁ : x≤1) :
    (1-x)^(n^5)≤1/(2:ℝ)^(2*n) := by
  have hnR : (128:ℝ)≤n := by exact_mod_cast hn
  have hxpos : 0<x := lt_of_lt_of_le (by positivity) hx₀
  have hmul : ((n:ℝ)^5)*x ≥ 2*n := by
    have hden : (0:ℝ)<2048*(n+1) := by positivity
    have hlow := (div_le_iff₀ hden).mp hx₀
    have hnpos : (0:ℝ)<n := by positivity
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤128) hnR 3
    norm_num at hh
    have hc : (8192:ℝ)≤(n:ℝ)^3 := by linarith
    have hp : 8192*(n:ℝ)^2≤(n:ℝ)^5 := by
      simpa only [← pow_add] using mul_le_mul_of_nonneg_right hc (sq_nonneg (n:ℝ))
    have hfirst : 2*n*(2048*(n+1))≤(n:ℝ)^5 := by nlinarith
    have hscaled := mul_le_mul_of_nonneg_left hlow (by positivity : (0:ℝ)≤(n:ℝ)^5)
    nlinarith
  have hpow := pow_le_pow_left₀ (sub_nonneg.mpr hx₁) (Real.one_sub_le_exp_neg x) (n^5)
  calc
    (1-x)^(n^5) ≤ Real.exp (-x)^(n^5) := hpow
    _ = Real.exp (-(2*n:ℝ)) * Real.exp (2*n-(n:ℝ)^5*x) := by
      rw [← Real.exp_nat_mul,← Real.exp_add]
      congr 1
      push_cast
      ring
    _ ≤ Real.exp (-(2*n:ℝ)) := by
      have he : Real.exp (2*n-(n:ℝ)^5*x)≤1 := Real.exp_le_one_iff.mpr (by linarith)
      exact (mul_le_mul_of_nonneg_left he (Real.exp_pos _).le).trans_eq (mul_one _)
    _ = 1/(Real.exp 1)^(2*n) := by
      rw [Real.exp_neg,← Real.exp_nat_mul]
      simp
    _ ≤ 1/(2:ℝ)^(2*n) := by
      apply one_div_le_one_div_of_le (by positivity)
      apply pow_le_pow_left₀ (by norm_num)
      have he := Real.exp_one_gt_d9
      linarith

lemma repeated_success_lower {n : ℕ} (hn : 128≤n) {x : ℝ}
    (hx₀ : 1/(2048*(n+1):ℝ)≤x) (hx₁ : x≤1) :
    1-1/(2:ℝ)^(2*n) ≤ 1-(1-x)^(n^5) := by
  have hh := repetition_failure_bound hn hx₀ hx₁
  linarith

end ExactQuantumFactoring.RepeatedTrials


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/GateSemantics.lean =====
namespace OAI

section


namespace ExactQuantumFactoring
open scoped BigOperators

lemma sum_boolFin_succ {α : Type*} [AddCommMonoid α] {n : ℕ}
    (f : (Fin (n+1) → Bool) → α) :
    ∑ x, f x = (∑ x : Fin n → Bool, f (Fin.cons false x)) +
      ∑ x : Fin n → Bool, f (Fin.cons true x) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => Bool)).sum_comp]
  simpa [Fintype.sum_prod_type, Fin.consEquiv] using
    (add_comm (∑ x : Fin n → Bool, f (Fin.cons true x))
      (∑ x : Fin n → Bool, f (Fin.cons false x)))

lemma sum_boolFin_zero {α : Type*} [AddCommMonoid α]
    (f : (Fin 0 → Bool) → α) : ∑ x, f x = f Fin.elim0 := by
  exact Fintype.sum_unique _

noncomputable def Primitive.localMatrix (p : Primitive) :
    Matrix (Basis p.arity) (Basis p.arity) ℂ :=
  fun x y => p.matrix (List.ofFn x) (List.ofFn y)

/-- A reversible Boolean operation, viewed as an exact permutation matrix. -/
noncomputable def permutationMatrix {ι : Type*} [DecidableEq ι] (e : Equiv.Perm ι) :
    Matrix ι ι ℂ := Matrix.of (fun a b => if a = e b then 1 else 0)

lemma permutationMatrix_unitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Equiv.Perm ι) : permutationMatrix e ∈ Matrix.unitaryGroup ι ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext a b
  simp only [Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
    permutationMatrix, Matrix.of_apply]
  simp [Finset.sum_ite_eq', e.injective.eq_iff, Matrix.one_apply, eq_comm]

def notPerm : Equiv.Perm (Basis 1) where
  toFun x := ![!x 0]
  invFun x := ![!x 0]
  left_inv x := by ext i; fin_cases i; simp
  right_inv x := by ext i; fin_cases i; simp

def cnotPerm : Equiv.Perm (Basis 2) where
  toFun x := ![x 0, Bool.xor (x 0) (x 1)]
  invFun x := ![x 0, Bool.xor (x 0) (x 1)]
  left_inv x := by ext i; fin_cases i <;> simp
  right_inv x := by ext i; fin_cases i <;> simp

def toffoliPerm : Equiv.Perm (Basis 3) where
  toFun x := ![x 0, x 1, Bool.xor (x 2) (x 0 && x 1)]
  invFun x := ![x 0, x 1, Bool.xor (x 2) (x 0 && x 1)]
  left_inv x := by ext i; fin_cases i <;> simp
  right_inv x := by ext i; fin_cases i <;> simp

lemma not_localMatrix : Primitive.not.localMatrix = permutationMatrix notPerm := by
  change Matrix.of (fun x y : Basis 1 => Primitive.not.matrix (List.ofFn x) (List.ofFn y)) =
    permutationMatrix notPerm
  ext x y
  simp [Primitive.matrix, List.ofFn_succ, Matrix.of_apply,
    permutationMatrix, notPerm, funext_iff, Fin.forall_fin_succ]

lemma cnot_localMatrix : Primitive.cnot.localMatrix = permutationMatrix cnotPerm := by
  change Matrix.of (fun x y : Basis 2 => Primitive.cnot.matrix (List.ofFn x) (List.ofFn y)) =
    permutationMatrix cnotPerm
  ext x y
  simp [Primitive.matrix, List.ofFn_succ, Matrix.of_apply,
    permutationMatrix, cnotPerm, funext_iff, Fin.forall_fin_succ]

lemma toffoli_localMatrix : Primitive.toffoli.localMatrix = permutationMatrix toffoliPerm := by
  change Matrix.of (fun x y : Basis 3 => Primitive.toffoli.matrix (List.ofFn x) (List.ofFn y)) =
    permutationMatrix toffoliPerm
  ext x y
  simp [Primitive.matrix, List.ofFn_succ, Matrix.of_apply,
    permutationMatrix, toffoliPerm, funext_iff, Fin.forall_fin_succ]

lemma hadamard_local_unitary : Primitive.hadamard.localMatrix ∈
    Matrix.unitaryGroup (Basis Primitive.hadamard.arity) ℂ := by
  change Matrix.of (fun x y : Fin 1 → Bool =>
    Primitive.hadamard.matrix (List.ofFn x) (List.ofFn y)) ∈
    Matrix.unitaryGroup (Fin 1 → Bool) ℂ
  rw [Matrix.mem_unitaryGroup_iff']
  ext x y
  simp only [Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, Matrix.of_apply]
  rw [sum_boolFin_succ]
  simp only [sum_boolFin_zero]
  have hx : x = Fin.cons (x 0) Fin.elim0 := by ext i; fin_cases i; rfl
  have hy : y = Fin.cons (y 0) Fin.elim0 := by ext i; fin_cases i; rfl
  rw [hx, hy]
  have hs : (Real.sqrt 2 : ℂ)^2 = 2 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  cases x 0 <;> cases y 0 <;>
    simp [Primitive.matrix, List.ofFn_succ] <;> ring_nf <;>
      simp [inv_pow, hs]

lemma phase_local_unitary : Primitive.phase.localMatrix ∈
    Matrix.unitaryGroup (Basis Primitive.phase.arity) ℂ := by
  change Matrix.of (fun x y : Fin 1 → Bool =>
    Primitive.phase.matrix (List.ofFn x) (List.ofFn y)) ∈
    Matrix.unitaryGroup (Fin 1 → Bool) ℂ
  rw [Matrix.mem_unitaryGroup_iff']
  ext x y
  simp only [Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, Matrix.of_apply]
  rw [sum_boolFin_succ]
  simp only [sum_boolFin_zero]
  have hx : x = Fin.cons (x 0) Fin.elim0 := by ext i; fin_cases i; rfl
  have hy : y = Fin.cons (y 0) Fin.elim0 := by ext i; fin_cases i; rfl
  rw [hx, hy]
  cases x 0 <;> cases y 0 <;> simp [Primitive.matrix, List.ofFn_succ]

lemma Primitive.local_unitary (p : Primitive) :
    p.localMatrix ∈ Matrix.unitaryGroup (Basis p.arity) ℂ := by
  cases p with
  | not => rw [not_localMatrix]; exact permutationMatrix_unitary _
  | cnot => rw [cnot_localMatrix]; exact permutationMatrix_unitary _
  | toffoli => rw [toffoli_localMatrix]; exact permutationMatrix_unitary _
  | hadamard => exact hadamard_local_unitary
  | phase => exact phase_local_unitary

lemma unitary_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) (A : Matrix ι ι ℂ)
    (hA : A ∈ Matrix.unitaryGroup ι ℂ) :
    Matrix.reindex e e A ∈ Matrix.unitaryGroup κ ℂ := by
  rw [Matrix.mem_unitaryGroup_iff'] at hA ⊢
  have hs : star (Matrix.reindex e e A) = Matrix.reindex e e (star A) :=
    Matrix.conjTranspose_reindex e e A
  rw [hs]
  change Matrix.reindexAlgEquiv ℂ ℂ e (star A) * Matrix.reindexAlgEquiv ℂ ℂ e A = 1
  rw [← map_mul, hA, map_one]

noncomputable def controlledMatrix {ι : Type*} [DecidableEq ι] (A : Matrix ι ι ℂ) :
    Matrix (Bool × ι) (Bool × ι) ℂ :=
  Matrix.of (fun x y => if x.1 = y.1 then
    if x.1 then A x.2 y.2 else if x.2 = y.2 then 1 else 0
    else 0)

lemma controlledMatrix_unitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A ∈ Matrix.unitaryGroup ι ℂ) :
    controlledMatrix A ∈ Matrix.unitaryGroup (Bool × ι) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff'] at hA ⊢
  ext ⟨a,x⟩ ⟨b,y⟩
  simp only [Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  cases a <;> cases b <;>
    simp [controlledMatrix, Matrix.one_apply]
  · by_cases h : x = y
    · subst y; simp
    · simp [h, Ne.symm h]
  · simpa [Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
      Matrix.one_apply] using congrFun (congrFun hA x) y

noncomputable def Gate.baseLocalMatrix (g : Gate) :
    Matrix (Basis g.primitive.arity) (Basis g.primitive.arity) ℂ :=
  Matrix.of (fun x y => g.baseMatrix (List.ofFn x) (List.ofFn y))

lemma Gate.baseLocalMatrix_eq (g : Gate) : g.baseLocalMatrix =
    if g.inverse then star g.primitive.localMatrix else g.primitive.localMatrix := by
  ext x y
  cases hi : g.inverse <;>
    simp [Gate.baseLocalMatrix, Gate.baseMatrix, Primitive.localMatrix, hi]

lemma Gate.baseLocal_unitary (g : Gate) :
    g.baseLocalMatrix ∈ Matrix.unitaryGroup (Basis g.primitive.arity) ℂ := by
  rw [g.baseLocalMatrix_eq]
  split_ifs
  · exact Unitary.star_mem g.primitive.local_unitary
  · exact g.primitive.local_unitary

noncomputable def Gate.localMatrix (g : Gate) : Matrix (Basis g.arity) (Basis g.arity) ℂ :=
  Matrix.of (fun x y => g.matrix (List.ofFn x) (List.ofFn y))

lemma Gate.controlled_localMatrix (p : Primitive) (inv : Bool) :
    (Gate.mk p inv true).localMatrix =
    Matrix.reindex (Fin.consEquiv (fun _ : Fin (p.arity+1) => Bool))
      (Fin.consEquiv (fun _ : Fin (p.arity+1) => Bool))
      (controlledMatrix (Gate.mk p inv true).baseLocalMatrix) := by
  change Matrix.of (fun x y : Basis (p.arity+1) =>
    (Gate.mk p inv true).matrix (List.ofFn x) (List.ofFn y)) = _
  ext x y
  simp only [Gate.matrix, ↓reduceIte, List.ofFn_succ, Matrix.of_apply,
    Matrix.reindex_apply, Fin.consEquiv, controlledMatrix,
    Gate.baseLocalMatrix]
  cases hx : x 0 <;> cases hy : y 0 <;> simp [hx, hy, Fin.tail_def]

lemma Gate.local_unitary (g : Gate) : g.localMatrix ∈ Matrix.unitaryGroup (Basis g.arity) ℂ := by
  rcases g with ⟨p, inv, ctrl⟩
  cases ctrl
  · exact Gate.baseLocal_unitary ⟨p, inv, false⟩
  · rw [Gate.controlled_localMatrix]
    exact unitary_reindex _ _ (controlledMatrix_unitary _ (Gate.baseLocal_unitary _))

end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/CircuitSemantics.lean =====
namespace OAI

section


namespace ExactQuantumFactoring
open scoped BigOperators Kronecker

abbrev Instruction.Unused {q : ℕ} (o : Instruction q) :=
  {i : Fin q // ∀ j, o.wire j ≠ i}

/-- Reindex a full computational basis by the gate wires and all other wires.
This is only a proof equivalence; it introduces no new gate in the model. -/
noncomputable def Instruction.splitBasis {q : ℕ} (o : Instruction q) :
    Basis q ≃ Basis o.gate.arity × (o.Unused → Bool) := by
  classical
  refine {
    toFun := fun x => (x ∘ o.wire, fun i => x i.val)
    invFun := fun x i => if h : ∃ j, o.wire j = i then x.1 h.choose
      else x.2 ⟨i, by simpa only [not_exists] using h⟩
    left_inv := ?_
    right_inv := ?_ }
  · intro x
    funext i
    dsimp
    split_ifs with h
    · simp only [h.choose_spec]
    · rfl
  · intro x
    apply Prod.ext
    · funext j
      dsimp
      have h : ∃ j', o.wire j' = o.wire j := ⟨j, rfl⟩
      rw [dite_eq_left h]
      exact congrArg x.1 (o.distinct h.choose_spec)
    · funext i
      dsimp
      rw [dite_eq_right (by simpa only [not_exists] using i.property)]

lemma tensor_unitary {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ)
    (hA : A ∈ Matrix.unitaryGroup ι ℂ) (hB : B ∈ Matrix.unitaryGroup κ ℂ) :
    A ⊗ₖ B ∈ Matrix.unitaryGroup (ι × κ) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff'] at hA hB ⊢
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker]
  rw [← Matrix.mul_kronecker_mul]
  change (star A * A) ⊗ₖ (star B * B) = 1
  rw [hA, hB, Matrix.one_kronecker_one]

lemma Instruction.matrix_eq_reindex {q : ℕ} (o : Instruction q) :
    o.matrix = Matrix.reindex o.splitBasis.symm o.splitBasis.symm
      (o.gate.localMatrix ⊗ₖ (1 : Matrix (o.Unused → Bool) (o.Unused → Bool) ℂ)) := by
  classical
  ext x y
  change (if ∀ i : Fin q, (∀ j, o.wire j ≠ i) → x i = y i then
      o.gate.matrix (List.ofFn (x ∘ o.wire)) (List.ofFn (y ∘ o.wire)) else 0) =
    o.gate.matrix (List.ofFn (x ∘ o.wire)) (List.ofFn (y ∘ o.wire)) *
      if (fun i : o.Unused => x i.val) = (fun i : o.Unused => y i.val) then 1 else 0
  by_cases h : ∀ i : Fin q, (∀ j, o.wire j ≠ i) → x i = y i
  · have he : (fun i : o.Unused => x i.val) = (fun i : o.Unused => y i.val) :=
      funext (fun i => h i.val i.property)
    rw [ite_eq_left h, ite_eq_left he, mul_one]
  · have he : (fun i : o.Unused => x i.val) ≠ (fun i : o.Unused => y i.val) := by
      intro hh
      apply h
      intro i hi
      exact congrFun hh ⟨i,hi⟩
    rw [ite_eq_right h, ite_eq_right he, mul_zero]

lemma Instruction.unitary {q : ℕ} (o : Instruction q) :
    o.matrix ∈ Matrix.unitaryGroup (Basis q) ℂ := by
  classical
  rw [o.matrix_eq_reindex]
  exact unitary_reindex _ _ (tensor_unitary _ _ o.gate.local_unitary (one_mem _))

/-- Matrix of executing a list of instructions, in chronological order. -/
noncomputable def programMatrix {q : ℕ} (ops : List (Instruction q)) :
    Matrix (Basis q) (Basis q) ℂ :=
  ops.foldl (fun A (o : Instruction _) => o.matrix * A) 1

lemma programMatrix_fold {q : ℕ} (ops : List (Instruction q))
    (A : Matrix (Basis q) (Basis q) ℂ) :
    ops.foldl (fun A (o : Instruction _) => o.matrix * A) A = programMatrix ops * A := by
  induction ops generalizing A with
  | nil => simp [programMatrix]
  | cons o ops ih =>
    change ops.foldl (fun A (o : Instruction q) => o.matrix * A) (o.matrix * A) =
      ops.foldl (fun A (o : Instruction q) => o.matrix * A) (o.matrix * 1) * A
    rw [ih, ih, Matrix.mul_one, Matrix.mul_assoc]

lemma programMatrix_unitary {q : ℕ} (ops : List (Instruction q)) :
    programMatrix ops ∈ Matrix.unitaryGroup (Basis q) ℂ := by
  classical
  induction ops with
  | nil => exact one_mem _
  | cons o ops ih =>
    change ops.foldl (fun A (o : Instruction _) => o.matrix * A) (o.matrix * 1) ∈ _
    rw [programMatrix_fold, Matrix.mul_one]
    exact mul_mem ih o.unitary

lemma Circuit.apply_eq_matrix (c : Circuit) (ψ : State c.qubits) :
    c.apply ψ = (programMatrix c.instructions).mulVec ψ := by
  suffices ∀ (ops : List (Instruction c.qubits)) (ψ : State c.qubits),
      ops.foldl (fun v o => o.matrix.mulVec v) ψ = (programMatrix ops).mulVec ψ from
    this c.instructions ψ
  intro ops
  induction ops with
  | nil => intro ψ; simp [programMatrix]
  | cons o ops ih =>
    intro ψ
    rw [List.foldl_cons, ih]
    change _ = (ops.foldl (fun A (o : Instruction _) => o.matrix * A) (o.matrix * 1)).mulVec ψ
    rw [programMatrix_fold, Matrix.mul_one, Matrix.mulVec_mulVec]

/-- Reversing a listed gate stays inside the same twenty gate names. -/
def Gate.reverse (g : Gate) : Gate := {g with inverse := !g.inverse}

lemma Gate.reverse_arity (g : Gate) : g.reverse.arity = g.arity := rfl

lemma Gate.reverse_baseMatrix (g : Gate) (x y : List Bool) :
    g.reverse.baseMatrix x y = star (g.baseMatrix y x) := by
  cases h : g.inverse <;> simp [Gate.reverse, Gate.baseMatrix, h]

lemma Gate.reverse_matrix (g : Gate) (x y : List Bool) :
    g.reverse.matrix x y = star (g.matrix y x) := by
  by_cases h : g.controlled = true
  · cases x with
    | nil => cases y <;> simp [Gate.matrix, Gate.reverse, h]
    | cons a x =>
      cases y with
      | nil => simp [Gate.matrix, Gate.reverse, h]
      | cons b y =>
        cases a <;> cases b <;> simp [Gate.matrix, h, Gate.reverse]
        · by_cases hh : x = y
          · subst y; simp
          · simp [hh, Ne.symm hh]
        · simpa [Gate.reverse, h] using g.reverse_baseMatrix x y
  · have hf : g.controlled = false := Bool.eq_false_iff.mpr h
    simpa [Gate.matrix, hf, Gate.reverse] using g.reverse_baseMatrix x y

def Instruction.reverse {q : ℕ} (o : Instruction q) : Instruction q :=
  ⟨o.gate.reverse, o.wire, o.distinct⟩

lemma Instruction.reverse_matrix {q : ℕ} (o : Instruction q) :
    o.reverse.matrix = star o.matrix := by
  classical
  ext x y
  change (if ∀ i : Fin q, (∀ j, o.wire j ≠ i) → x i = y i then
      o.gate.reverse.matrix (List.ofFn (x ∘ o.wire)) (List.ofFn (y ∘ o.wire)) else 0) =
    star (if ∀ i : Fin q, (∀ j, o.wire j ≠ i) → y i = x i then
      o.gate.matrix (List.ofFn (y ∘ o.wire)) (List.ofFn (x ∘ o.wire)) else 0)
  rw [Gate.reverse_matrix]
  have he : (∀ i : Fin q, (∀ j, o.wire j ≠ i) → y i = x i) ↔
      (∀ i : Fin q, (∀ j, o.wire j ≠ i) → x i = y i) := by
    apply forall_congr'
    intro i
    exact imp_congr_right (fun _ => eq_comm)
  simp only [he]
  split_ifs <;> simp

lemma programMatrix_append {q : ℕ} (a b : List (Instruction q)) :
    programMatrix (a ++ b) = programMatrix b * programMatrix a := by
  unfold programMatrix
  rw [List.foldl_append, programMatrix_fold]
  rfl

lemma programMatrix_reverse {q : ℕ} (ops : List (Instruction q)) :
    programMatrix (ops.reverse.map Instruction.reverse) = star (programMatrix ops) := by
  induction ops with
  | nil => simp [programMatrix]
  | cons o ops ih =>
    rw [List.reverse_cons, List.map_append, programMatrix_append, ih]
    change programMatrix [o.reverse] * star (programMatrix ops) =
      star (ops.foldl (fun A (o : Instruction q) => o.matrix * A) (o.matrix * 1))
    rw [programMatrix_fold]
    simp [programMatrix, Instruction.reverse_matrix]

def Circuit.reverse (c : Circuit) : Circuit :=
  ⟨c.qubits, c.instructions.reverse.map Instruction.reverse⟩

lemma unitary_finiteInner {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A ∈ Matrix.unitaryGroup ι ℂ) (v w : ι → ℂ) :
    Exactness.finiteInner (A.mulVec v) (A.mulVec w) = Exactness.finiteInner v w := by
  change star (A.mulVec v) ⬝ᵥ A.mulVec w = star v ⬝ᵥ w
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
  rw [← Matrix.star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff'.mp hA,
    Matrix.one_mulVec]

lemma unitary_mass {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A ∈ Matrix.unitaryGroup ι ℂ) (v : ι → ℂ) :
    (∑ x, Complex.normSq (A.mulVec v x)) = ∑ x, Complex.normSq (v x) := by
  apply Complex.ofReal_injective
  simpa [Exactness.finiteInner_self] using unitary_finiteInner A hA v v

lemma Circuit.mass (c : Circuit) (ψ : State c.qubits) :
    (∑ x, Complex.normSq (c.apply ψ x)) = ∑ x, Complex.normSq (ψ x) := by
  rw [c.apply_eq_matrix]
  exact unitary_mass _ (programMatrix_unitary _) _

lemma Circuit.output_normalized (c : Circuit) (ℓ N : ℕ) :
    (∑ x, Complex.normSq (c.outputState ℓ N x)) = 1 := by
  classical
  unfold Circuit.outputState
  rw [c.mass]
  simp

lemma Circuit.reverse_apply (c : Circuit) (ψ : State c.qubits) :
    c.reverse.apply (c.apply ψ) = ψ := by
  unfold Circuit.reverse
  rw [Circuit.apply_eq_matrix, c.apply_eq_matrix]
  change (programMatrix (c.instructions.reverse.map Instruction.reverse)).mulVec
    ((programMatrix c.instructions).mulVec ψ) = ψ
  rw [programMatrix_reverse, Matrix.mulVec_mulVec,
    Matrix.mem_unitaryGroup_iff'.mp (programMatrix_unitary _), Matrix.one_mulVec]

end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/BooleanCircuit.lean =====
namespace OAI

section


namespace ExactQuantumFactoring
open scoped BigOperators Kronecker

noncomputable def basisVector {ι : Type*} [DecidableEq ι] (x : ι) : ι → ℂ :=
  fun y => if y = x then 1 else 0

lemma matrix_basisVector {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix κ ι ℂ) (x : ι) : A.mulVec (basisVector x) = fun y => A y x := by
  funext y
  simp [Matrix.mulVec, dotProduct, basisVector]

lemma permutationMatrix_basisVector {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Equiv.Perm ι) (x : ι) :
    (permutationMatrix e).mulVec (basisVector x) = basisVector (e x) := by
  rw [matrix_basisVector]
  rfl

/-- Lift a local classical reversible gate to the actual wires; this is not an
additional circuit instruction, just its classical semantics. -/
noncomputable def Instruction.liftPerm {q : ℕ} (o : Instruction q)
    (e : Equiv.Perm (Basis o.gate.arity)) : Equiv.Perm (Basis q) :=
  (o.splitBasis.trans (Equiv.prodCongr e (Equiv.refl _))).trans o.splitBasis.symm

lemma Instruction.liftPerm_matrix {q : ℕ} (o : Instruction q)
    (e : Equiv.Perm (Basis o.gate.arity))
    (he : o.gate.localMatrix = permutationMatrix e) :
    o.matrix = permutationMatrix (o.liftPerm e) := by
  classical
  rw [o.matrix_eq_reindex, he]
  ext x y
  change ((if (o.splitBasis x).1 = e (o.splitBasis y).1 then (1:ℂ) else 0) *
      if (o.splitBasis x).2 = (o.splitBasis y).2 then 1 else 0) =
    if x = o.liftPerm e y then 1 else 0
  have hh : x = o.liftPerm e y ↔
      (o.splitBasis x).1 = e (o.splitBasis y).1 ∧
      (o.splitBasis x).2 = (o.splitBasis y).2 := by
    rw [← o.splitBasis.injective.eq_iff]
    simp [Instruction.liftPerm, Prod.ext_iff]
  simp only [hh]
  split_ifs <;> simp_all

lemma Instruction.liftPerm_wire {q : ℕ} (o : Instruction q)
    (e : Equiv.Perm (Basis o.gate.arity)) (x : Basis q) (i : Fin o.gate.arity) :
    o.liftPerm e x (o.wire i) = e (x ∘ o.wire) i := by
  have h := congrArg (fun z => z.1 i) (o.splitBasis.apply_symm_apply
    ((Equiv.prodCongr e (Equiv.refl (o.Unused → Bool))) (o.splitBasis x)))
  exact h

lemma Instruction.liftPerm_unused {q : ℕ} (o : Instruction q)
    (e : Equiv.Perm (Basis o.gate.arity)) (x : Basis q) (i : Fin q)
    (hi : ∀ j, o.wire j ≠ i) : o.liftPerm e x i = x i := by
  have h := congrArg (fun z => z.2 ⟨i,hi⟩) (o.splitBasis.apply_symm_apply
    ((Equiv.prodCongr e (Equiv.refl (o.Unused → Bool))) (o.splitBasis x)))
  exact h

lemma Instruction.liftPerm_basisVector {q : ℕ} (o : Instruction q)
    (e : Equiv.Perm (Basis o.gate.arity))
    (he : o.gate.localMatrix = permutationMatrix e) (x : Basis q) :
    o.matrix.mulVec (basisVector x) = basisVector (o.liftPerm e x) := by
  rw [o.liftPerm_matrix e he, permutationMatrix_basisVector]

/-- No inverse/control flag is used in these elementary fresh-bit operations. -/
abbrev plainGate (p : Primitive) : Gate := ⟨p,false,false⟩

lemma plainGate_arity (p : Primitive) : (plainGate p).arity = p.arity := by
  simp [Gate.arity]

lemma plainGate_localMatrix (p : Primitive) :
    (plainGate p).localMatrix = p.localMatrix := rfl

abbrev notAt {q : ℕ} (t : Fin q) : Instruction q :=
  ⟨plainGate .not, fun _ => t, by
    change Function.Injective (fun _ : Fin 1 => t)
    intro a b _
    exact Subsingleton.elim a b⟩

abbrev cnotAt {q : ℕ} (c t : Fin q) (hct : c ≠ t) : Instruction q :=
  ⟨plainGate .cnot, ![c,t], by
    change Function.Injective (![c,t] : Fin 2 → Fin q)
    intro i j he
    fin_cases i <;> fin_cases j <;> simp_all⟩

abbrev toffoliAt {q : ℕ} (a b t : Fin q) (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) :
    Instruction q :=
  ⟨plainGate .toffoli, ![a,b,t], by
    change Function.Injective (![a,b,t] : Fin 3 → Fin q)
    intro i j he
    fin_cases i <;> fin_cases j <;> simp_all⟩

lemma notAt_lift {q : ℕ} (t : Fin q) (x : Basis q) :
    (notAt t).liftPerm notPerm x = Function.update x t (!x t) := by
  classical
  funext i
  by_cases hi : t = i
  · subst i
    rw [Function.update_self]
    exact (notAt t).liftPerm_wire notPerm x ⟨0,by change 0<1; decide⟩
  · rw [(notAt t).liftPerm_unused notPerm x i (by intro j; exact hi)]
    simp [Function.update, Ne.symm hi]

lemma cnotAt_lift {q : ℕ} (c t : Fin q) (hct : c ≠ t) (x : Basis q) :
    (cnotAt c t hct).liftPerm cnotPerm x =
      Function.update x t (Bool.xor (x c) (x t)) := by
  classical
  funext i
  by_cases hi : t = i
  · subst i
    rw [Function.update_self]
    exact (cnotAt c t hct).liftPerm_wire cnotPerm x ⟨1,by change 1<2; decide⟩
  · by_cases hc : c = i
    · subst i
      rw [Function.update_of_ne (Ne.symm hi)]
      exact (cnotAt c t hct).liftPerm_wire cnotPerm x ⟨0,by change 0<2; decide⟩
    · rw [(cnotAt c t hct).liftPerm_unused cnotPerm x i (by
        intro j; fin_cases j <;> simpa [cnotAt] using (by assumption : _))]
      simp [Function.update, Ne.symm hi]

lemma toffoliAt_lift {q : ℕ} (a b t : Fin q)
    (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) (x : Basis q) :
    (toffoliAt a b t hab hat hbt).liftPerm toffoliPerm x =
      Function.update x t (Bool.xor (x t) (x a && x b)) := by
  classical
  funext i
  by_cases hi : t = i
  · subst i
    rw [Function.update_self]
    exact (toffoliAt a b t hab hat hbt).liftPerm_wire toffoliPerm x ⟨2,by change 2<3; decide⟩
  · by_cases ha : a = i
    · subst i
      rw [Function.update_of_ne (Ne.symm hi)]
      exact (toffoliAt a b t hab hat hbt).liftPerm_wire toffoliPerm x ⟨0,by change 0<3; decide⟩
    · by_cases hb : b = i
      · subst i
        rw [Function.update_of_ne (Ne.symm hi)]
        exact (toffoliAt a b t hab hat hbt).liftPerm_wire toffoliPerm x ⟨1,by change 1<3; decide⟩
      · rw [(toffoliAt a b t hab hat hbt).liftPerm_unused toffoliPerm x i (by
          intro j; fin_cases j <;> simpa [toffoliAt] using (by assumption : _))]
        simp [Function.update, Ne.symm hi]

lemma notAt_basis {q : ℕ} (t : Fin q) (x : Basis q) :
    (notAt t).matrix.mulVec (basisVector x) = basisVector (Function.update x t (!x t)) := by
  rw [Instruction.liftPerm_basisVector (notAt t) notPerm (by exact not_localMatrix), notAt_lift]

lemma cnotAt_basis {q : ℕ} (c t : Fin q) (hct : c ≠ t) (x : Basis q) :
    (cnotAt c t hct).matrix.mulVec (basisVector x) =
      basisVector (Function.update x t (Bool.xor (x c) (x t))) := by
  rw [Instruction.liftPerm_basisVector (cnotAt c t hct) cnotPerm (by exact cnot_localMatrix), cnotAt_lift]

lemma toffoliAt_basis {q : ℕ} (a b t : Fin q) (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t)
    (x : Basis q) :
    (toffoliAt a b t hab hat hbt).matrix.mulVec (basisVector x) =
      basisVector (Function.update x t (Bool.xor (x t) (x a && x b))) := by
  rw [Instruction.liftPerm_basisVector (toffoliAt a b t hab hat hbt) toffoliPerm (by exact toffoli_localMatrix), toffoliAt_lift]

end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/BooleanProgram.lean =====
namespace OAI

section


namespace ExactQuantumFactoring
open scoped BigOperators

lemma programMatrix_nil {q : ℕ} : programMatrix ([] : List (Instruction q)) = 1 := rfl

lemma programMatrix_cons {q : ℕ} (o : Instruction q) (ops : List (Instruction q)) :
    programMatrix (o :: ops) = programMatrix ops * o.matrix := by
  change ops.foldl (fun A (o : Instruction q) => o.matrix * A) (o.matrix * 1) = _
  rw [programMatrix_fold, Matrix.mul_one]

lemma programMatrix_singleton {q : ℕ} (o : Instruction q) :
    programMatrix [o] = o.matrix := by
  rw [programMatrix_cons, programMatrix_nil, Matrix.one_mul]

/-- A Boolean node is implemented by at most two of the named fixed gates.
The target is excluded from the sources, but repeated sources are permitted.
Its action toggles the target, so the semantics are reversible on all states. -/
inductive BooleanOp (q : ℕ) (t : Fin q) where
  | constant (b : Bool)
  | copy (a : Fin q) (ha : a ≠ t)
  | neg (a : Fin q) (ha : a ≠ t)
  | conj (a b : Fin q) (ha : a ≠ t) (hb : b ≠ t)

namespace BooleanOp

def value {q : ℕ} {t : Fin q} : BooleanOp q t → Basis q → Bool
  | .constant b, _ => b
  | .copy a _, x => x a
  | .neg a _, x => !x a
  | .conj a b _ _, x => x a && x b

def eval {q : ℕ} {t : Fin q} (o : BooleanOp q t) (x : Basis q) : Basis q :=
  Function.update x t (Bool.xor (x t) (o.value x))

def compile {q : ℕ} {t : Fin q} : BooleanOp q t → List (Instruction q)
  | .constant false => []
  | .constant true => [notAt t]
  | .copy a ha => [cnotAt a t ha]
  | .neg a ha => [cnotAt a t ha, notAt t]
  | .conj a b ha hb => if h : a = b then [cnotAt a t ha]
      else [toffoliAt a b t h ha hb]

lemma compile_length {q : ℕ} {t : Fin q} (o : BooleanOp q t) :
    o.compile.length ≤ 2 := by
  cases o with
  | constant b => cases b <;> simp [compile]
  | copy => simp [compile]
  | neg => simp [compile]
  | conj a b ha hb => simp only [compile]; split <;> simp

lemma eval_at {q : ℕ} {t : Fin q} (o : BooleanOp q t) (x : Basis q) :
    o.eval x t = Bool.xor (x t) (o.value x) := Function.update_self _ _ _

lemma eval_away {q : ℕ} {t i : Fin q} (o : BooleanOp q t) (x : Basis q) (hi : i ≠ t) :
    o.eval x i = x i := Function.update_of_ne hi _ _

lemma eval_fresh {q : ℕ} {t : Fin q} (o : BooleanOp q t) (x : Basis q) (ht : x t = false) :
    o.eval x = Function.update x t (o.value x) := by
  simp [eval, ht]

lemma compile_basis {q : ℕ} {t : Fin q} (o : BooleanOp q t) (x : Basis q) :
    (programMatrix o.compile).mulVec (basisVector x) = basisVector (o.eval x) := by
  cases o with
  | constant b =>
    cases b
    · simp [compile, programMatrix_nil, eval, value]
    · rw [compile, programMatrix_singleton, notAt_basis]
      simp [eval, value]
  | copy a ha =>
    rw [compile, programMatrix_singleton, cnotAt_basis]
    simp [eval, value, Bool.xor_comm]
  | neg a ha =>
    rw [compile, programMatrix_cons, programMatrix_singleton, ← Matrix.mulVec_mulVec,
      cnotAt_basis, notAt_basis]
    congr 1
    simp only [Function.update_self, Function.update_idem, eval, value]
    congr 1
    cases x a <;> cases x t <;> rfl
  | conj a b ha hb =>
    simp only [compile]
    split_ifs with hab
    · rw [programMatrix_singleton, cnotAt_basis]
      subst b
      simp [eval, value, Bool.xor_comm]
    · rw [programMatrix_singleton, toffoliAt_basis]
      rfl

end BooleanOp

/-- The classical network explicitly retains all values already computed.
In a fresh-output DAG each node's target is a previously zero ancilla. -/
abbrev BooleanProgram (q : ℕ) := List ((t : Fin q) × BooleanOp q t)

def BooleanProgram.eval {q : ℕ} (p : BooleanProgram q) (x : Basis q) : Basis q :=
  p.foldl (fun x o => o.2.eval x) x

def BooleanProgram.compile {q : ℕ} (p : BooleanProgram q) : List (Instruction q) :=
  p.flatMap (fun o => o.2.compile)

lemma BooleanProgram.compile_basis {q : ℕ} (p : BooleanProgram q) (x : Basis q) :
    (programMatrix p.compile).mulVec (basisVector x) = basisVector (p.eval x) := by
  induction p generalizing x with
  | nil => simp [compile, eval, programMatrix_nil]
  | cons o p ih =>
    change (programMatrix (o.2.compile ++ BooleanProgram.compile p)).mulVec (basisVector x) = _
    rw [programMatrix_append, ← Matrix.mulVec_mulVec, BooleanOp.compile_basis, ih]
    rfl

lemma BooleanProgram.compile_length {q : ℕ} (p : BooleanProgram q) :
    p.compile.length ≤ 2 * p.length := by
  induction p with
  | nil => simp [compile]
  | cons o p ih =>
    change (o.2.compile ++ BooleanProgram.compile p).length ≤ 2 * (o :: p).length
    rw [List.length_append, List.length_cons]
    have h := o.2.compile_length
    omega

/-- Reversing the actual compiled gate list erases the complete retained trace,
not only its output. No irreversible erasure is used. -/
lemma BooleanProgram.uncompute {q : ℕ} (p : BooleanProgram q) (x : Basis q) :
    (programMatrix (p.compile.reverse.map Instruction.reverse)).mulVec
      (basisVector (p.eval x)) = basisVector x := by
  rw [← p.compile_basis x, programMatrix_reverse, Matrix.mulVec_mulVec,
    Matrix.mem_unitaryGroup_iff'.mp (programMatrix_unitary _), Matrix.one_mulVec]

end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/BooleanNetwork.lean =====
namespace OAI

section


namespace ExactQuantumFactoring

/-- A bounded-fan-in Boolean node, with no hidden arithmetic operation. -/
inductive BoolNode (n : ℕ) where
  | constant (b : Bool)
  | copy (i : Fin n)
  | neg (i : Fin n)
  | conj (i j : Fin n)

namespace BoolNode

def eval {n : ℕ} : BoolNode n → (Fin n → Bool) → Bool
  | .constant b, _ => b
  | .copy i, x => x i
  | .neg i, x => !x i
  | .conj i j, x => x i && x j

def map {n m : ℕ} (f : Fin n → Fin m) : BoolNode n → BoolNode m
  | .constant b => .constant b
  | .copy i => .copy (f i)
  | .neg i => .neg (f i)
  | .conj i j => .conj (f i) (f j)

lemma eval_map {n m : ℕ} (f : Fin n → Fin m) (o : BoolNode n) (x : Fin m → Bool) :
    (o.map f).eval x = o.eval (x ∘ f) := by cases o <;> rfl

/-- The new wire is distinct from every preexisting wire. -/
def compileOp {n q : ℕ} (h : n + 1 ≤ q) (o : BoolNode n) :
    BooleanOp q ⟨n, by omega⟩ :=
  match o with
  | .constant b => .constant b
  | .copy i => .copy (i.castLE (by omega)) (by intro he; have hh := congrArg Fin.val he; simp only [Fin.val_castLE] at hh; omega)
  | .neg i => .neg (i.castLE (by omega)) (by intro he; have hh := congrArg Fin.val he; simp only [Fin.val_castLE] at hh; omega)
  | .conj i j => .conj (i.castLE (by omega)) (j.castLE (by omega))
      (by intro he; have hh := congrArg Fin.val he; simp only [Fin.val_castLE] at hh; omega)
      (by intro he; have hh := congrArg Fin.val he; simp only [Fin.val_castLE] at hh; omega)

lemma compileOp_value {n q : ℕ} (h : n + 1 ≤ q) (o : BoolNode n) (x : Basis q) :
    (o.compileOp h).value x = o.eval (fun i => x (i.castLE (by omega))) := by
  cases o <;> rfl

end BoolNode

/-- Straight-line Boolean computation retaining its whole trace. Width increases
by exactly one per node, so there is no truth-table synthesis overhead. -/
inductive BoolNet (n : ℕ) : ℕ → Type
  | input : BoolNet n n
  | add {k : ℕ} (p : BoolNet n k) (o : BoolNode k) : BoolNet n (k+1)

namespace BoolNet

def count {n k : ℕ} : BoolNet n k → ℕ
  | .input => 0
  | .add p _ => p.count + 1

lemma width_eq {n k : ℕ} (p : BoolNet n k) : k = n + p.count := by
  induction p with
  | input => simp [count]
  | add p o ih => simp only [count]; omega

lemma input_le {n k : ℕ} (p : BoolNet n k) : n ≤ k := by rw [p.width_eq]; omega

def eval {n k : ℕ} : BoolNet n k → (Fin n → Bool) → (Fin k → Bool)
  | .input, x => x
  | .add p o, x => Fin.snoc (p.eval x) (o.eval (p.eval x))

@[simp] lemma eval_add_castSucc {n k : ℕ} (p : BoolNet n k) (o : BoolNode k)
    (x : Fin n → Bool) (i : Fin k) : (p.add o).eval x i.castSucc = p.eval x i := by
  simp [eval]

@[simp] lemma eval_add_last {n k : ℕ} (p : BoolNet n k) (o : BoolNode k)
    (x : Fin n → Bool) : (p.add o).eval x (Fin.last k) = o.eval (p.eval x) := by
  simp [eval]

lemma eval_input {n k : ℕ} (p : BoolNet n k) (x : Fin n → Bool) (i : Fin n) :
    p.eval x (i.castLE p.input_le) = x i := by
  induction p with
  | input => rfl
  | add p o ih =>
    have he : i.castLE (p.add o).input_le = (i.castLE p.input_le).castSucc := rfl
    rw [he, eval_add_castSucc, ih]

def program {n k : ℕ} (p : BoolNet n k) {q : ℕ} (h : k ≤ q) : BooleanProgram q :=
  match p with
  | .input => []
  | .add p o => p.program (by omega) ++ [⟨⟨_, by omega⟩, o.compileOp h⟩]

lemma program_length {n k q : ℕ} (p : BoolNet n k) (h : k ≤ q) :
    (p.program h).length = p.count := by
  induction p with
  | input => rfl
  | add p o ih => simp [program, count, ih]

lemma compile_length {n k q : ℕ} (p : BoolNet n k) (h : k ≤ q) :
    (BooleanProgram.compile (p.program h)).length ≤ 2 * p.count := by
  simpa only [program_length] using BooleanProgram.compile_length (p.program h)

/-- Append a network whose inputs are arbitrary already-computed wires.
Repeated input sources are permitted and do not cause duplicated computation. -/
def attach {n k m l : ℕ} (a : BoolNet n k) (ρ : Fin m → Fin k) (b : BoolNet m l) :
    (j : ℕ) × BoolNet n j × (Fin l → Fin j) :=
  match b with
  | .input => ⟨k, a, ρ⟩
  | .add b o =>
    let c := a.attach ρ b
    ⟨c.1 + 1, c.2.1.add (o.map c.2.2), Fin.snoc (fun i => (c.2.2 i).castSucc) (Fin.last c.1)⟩

lemma attach_count {n k m l : ℕ} (a : BoolNet n k) (ρ : Fin m → Fin k) (b : BoolNet m l) :
    (a.attach ρ b).2.1.count = a.count + b.count := by
  induction b with
  | input => simp [attach, count]
  | add b o ih => simp only [attach, count, ih, Nat.add_assoc]

lemma attach_eval {n k m l : ℕ} (a : BoolNet n k) (ρ : Fin m → Fin k) (b : BoolNet m l)
    (x : Fin n → Bool) :
    (a.attach ρ b).2.1.eval x ∘ (a.attach ρ b).2.2 = b.eval (a.eval x ∘ ρ) := by
  induction b with
  | input => rfl
  | @add l b o ih =>
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [attach, Function.comp_apply, Fin.snoc_last, eval_add_last, BoolNode.eval_map]
      rw [ih]
    · simp only [attach, Function.comp_apply, Fin.snoc_castSucc, eval_add_castSucc]
      exact congrFun ih j

lemma attach_width {n k m l : ℕ} (a : BoolNet n k) (ρ : Fin m → Fin k) (b : BoolNet m l) :
    (a.attach ρ b).1 = k + b.count := by
  have hw := (a.attach ρ b).2.1.width_eq
  rw [attach_count, ← Nat.add_assoc, ← a.width_eq] at hw
  exact hw

lemma attach_le {n k m l : ℕ} (a : BoolNet n k) (ρ : Fin m → Fin k) (b : BoolNet m l) :
    k ≤ (a.attach ρ b).1 := by rw [attach_width]; omega

lemma attach_preserve {n k m l : ℕ} (a : BoolNet n k) (ρ : Fin m → Fin k) (b : BoolNet m l)
    (x : Fin n → Bool) (i : Fin k) :
    (a.attach ρ b).2.1.eval x (i.castLE (a.attach_le ρ b)) = a.eval x i := by
  induction b with
  | input => rfl
  | add b o ih =>
    change ((a.attach ρ b).2.1.add (o.map (a.attach ρ b).2.2)).eval x
      (i.castLE (a.attach_le ρ b)).castSucc = _
    rw [eval_add_castSucc, ih]

/-- On fresh ancillas the compiled program realizes the network exactly,
including preservation of all unused wires. -/
lemma program_eval {n k q : ℕ} (p : BoolNet n k) (h : k ≤ q) (x : Basis q)
    (hfresh : ∀ i : Fin q, n ≤ i.val → x i = false) :
    (∀ i : Fin k, (BooleanProgram.eval (p.program h) x) (i.castLE h) =
      p.eval (fun j => x (j.castLE (p.input_le.trans h))) i) ∧
    (∀ i : Fin q, k ≤ i.val → (BooleanProgram.eval (p.program h) x) i = false) := by
  induction p with
  | input => exact ⟨fun _ => rfl, hfresh⟩
  | @add k p o ih =>
    have hk : k ≤ q := by omega
    obtain ⟨hpre, hrest⟩ := ih hk
    have hy : (BooleanProgram.eval (p.program hk) x) ⟨k, by omega⟩ = false :=
      hrest _ (by simp)
    have hv : (o.compileOp h).value (BooleanProgram.eval (p.program hk) x) =
        o.eval (p.eval (fun j => x (j.castLE (p.input_le.trans hk)))) := by
      rw [BoolNode.compileOp_value]
      congr 1
      funext i
      exact hpre i
    have heval : BooleanProgram.eval ((p.add o).program h) x =
        Function.update (BooleanProgram.eval (p.program hk) x) ⟨k, by omega⟩
          (o.eval (p.eval (fun j => x (j.castLE (p.input_le.trans hk))))) := by
      simp only [program, BooleanProgram.eval, List.foldl_append, List.foldl_cons, List.foldl_nil]
      change (o.compileOp h).eval (BooleanProgram.eval (p.program hk) x) = _
      rw [BooleanOp.eval_fresh _ _ hy, hv]
      rfl
    rw [heval]
    constructor
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [eval_add_last]
        exact Function.update_self _ _ _
      · rw [eval_add_castSucc]
        rw [Function.update_of_ne (by intro he; have hh := congrArg Fin.val he; change j.val = k at hh; omega)]
        exact hpre j
    · intro i hi
      rw [Function.update_of_ne (by intro he; have hh := congrArg Fin.val he; change i.val = k at hh; omega)]
      exact hrest i (by omega)

end BoolNet

/-- Typed interfaces for network composition, with explicitly retained workspace. -/
structure BooleanNetwork (n m : ℕ) where
  width : ℕ
  net : BoolNet n width
  output : Fin m → Fin width


end ExactQuantumFactoring
end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/BooleanNetworkFurther.lean =====
namespace OAI

section
namespace ExactQuantumFactoring

namespace BooleanNetwork

def eval {n m : ℕ} (c : BooleanNetwork n m) (x : Fin n → Bool) : Fin m → Bool :=
  c.net.eval x ∘ c.output

def select {n m : ℕ} (f : Fin m → Fin n) : BooleanNetwork n m := ⟨n, .input, f⟩

def node {n : ℕ} (o : BoolNode n) : BooleanNetwork n 1 :=
  ⟨n+1, .add .input o, fun _ => Fin.last n⟩

def comp {n m l : ℕ} (a : BooleanNetwork n m) (b : BooleanNetwork m l) : BooleanNetwork n l :=
  let c := a.net.attach a.output b.net
  ⟨c.1, c.2.1, c.2.2 ∘ b.output⟩

lemma eval_comp {n m l : ℕ} (a : BooleanNetwork n m) (b : BooleanNetwork m l)
    (x : Fin n → Bool) : (a.comp b).eval x = b.eval (a.eval x) := by
  change ((a.net.attach a.output b.net).2.1.eval x ∘ (a.net.attach a.output b.net).2.2) ∘
    b.output = _
  rw [BoolNet.attach_eval]
  rfl

lemma count_comp {n m l : ℕ} (a : BooleanNetwork n m) (b : BooleanNetwork m l) :
    (a.comp b).net.count = a.net.count + b.net.count := BoolNet.attach_count _ _ _

/-- Parallel computations share the input but retain disjoint new traces. -/
def pair {n m l : ℕ} (a : BooleanNetwork n m) (b : BooleanNetwork n l) : BooleanNetwork n (m+l) :=
  let ρ : Fin n → Fin a.width := fun i => i.castLE a.net.input_le
  let c := a.net.attach ρ b.net
  ⟨c.1, c.2.1, Fin.append (fun i => (a.output i).castLE (a.net.attach_le ρ b.net))
    (c.2.2 ∘ b.output)⟩

lemma eval_pair {n m l : ℕ} (a : BooleanNetwork n m) (b : BooleanNetwork n l)
    (x : Fin n → Bool) : (a.pair b).eval x = Fin.append (a.eval x) (b.eval x) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [pair, eval, Function.comp_apply, Fin.append_left]
    exact BoolNet.attach_preserve _ _ _ _ _
  · simp only [pair, eval, Function.comp_apply, Fin.append_right]
    have he := congrFun (BoolNet.attach_eval a.net (fun i => i.castLE a.net.input_le) b.net x) (b.output j)
    have hi : a.net.eval x ∘ (fun i : Fin n => i.castLE a.net.input_le) = x := by
      funext j
      exact BoolNet.eval_input _ _ _
    rw [hi] at he
    exact he

lemma count_pair {n m l : ℕ} (a : BooleanNetwork n m) (b : BooleanNetwork n l) :
    (a.pair b).net.count = a.net.count + b.net.count := BoolNet.attach_count _ _ _

@[simp] lemma eval_select {n m : ℕ} (f : Fin m → Fin n) (x : Fin n → Bool) :
    (select f).eval x = x ∘ f := rfl

@[simp] lemma count_select {n m : ℕ} (f : Fin m → Fin n) :
    (select f).net.count = 0 := rfl

@[simp] lemma eval_node {n : ℕ} (o : BoolNode n) (x : Fin n → Bool) (i : Fin 1) :
    (node o).eval x i = o.eval x := by
  exact BoolNet.eval_add_last _ _ _

@[simp] lemma count_node {n : ℕ} (o : BoolNode n) : (node o).net.count = 1 := rfl

end BooleanNetwork
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/BooleanAlgebra.lean =====
namespace OAI

section


namespace ExactQuantumFactoring.BooleanNetwork

/-- Wire routing is free: it refers to values already physically present. -/
def rewire {n m l : ℕ} (c : BooleanNetwork n m) (f : Fin l → Fin m) : BooleanNetwork n l :=
  ⟨c.width, c.net, c.output ∘ f⟩

@[simp] lemma eval_rewire {n m l : ℕ} (c : BooleanNetwork n m) (f : Fin l → Fin m)
    (x : Fin n → Bool) : (c.rewire f).eval x = c.eval x ∘ f := rfl

@[simp] lemma count_rewire {n m l : ℕ} (c : BooleanNetwork n m) (f : Fin l → Fin m) :
    (c.rewire f).net.count = c.net.count := rfl

def bit {n : ℕ} (i : Fin n) : BooleanNetwork n 1 := select (fun _ => i)
def constant {n : ℕ} (b : Bool) : BooleanNetwork n 1 := node (.constant b)
def bnot {n : ℕ} (a : BooleanNetwork n 1) : BooleanNetwork n 1 := a.comp (node (.neg 0))
def band {n : ℕ} (a b : BooleanNetwork n 1) : BooleanNetwork n 1 :=
  (a.pair b).comp (node (.conj 0 1))
def bor {n : ℕ} (a b : BooleanNetwork n 1) : BooleanNetwork n 1 := (a.bnot.band b.bnot).bnot
def bxor {n : ℕ} (a b : BooleanNetwork n 1) : BooleanNetwork n 1 :=
  (a.band b.bnot).bor (a.bnot.band b)
def mux {n : ℕ} (c a b : BooleanNetwork n 1) : BooleanNetwork n 1 :=
  (c.band a).bor (c.bnot.band b)
def majority {n : ℕ} (a b c : BooleanNetwork n 1) : BooleanNetwork n 1 :=
  (a.band b).bor (c.band (a.bor b))

@[simp] lemma eval_bit {n : ℕ} (i : Fin n) (x : Fin n → Bool) (j : Fin 1) :
    (bit i).eval x j = x i := rfl

@[simp] lemma eval_constant {n : ℕ} (b : Bool) (x : Fin n → Bool) (j : Fin 1) :
    (constant b).eval x j = b := eval_node _ _ _

@[simp] lemma eval_bnot {n : ℕ} (a : BooleanNetwork n 1) (x : Fin n → Bool) (j : Fin 1) :
    a.bnot.eval x j = !(a.eval x 0) := by simp [bnot, eval_comp, BoolNode.eval]

@[simp] lemma eval_band {n : ℕ} (a b : BooleanNetwork n 1) (x : Fin n → Bool) (j : Fin 1) :
    (a.band b).eval x j = (a.eval x 0 && b.eval x 0) := by
  simp only [band, eval_comp, eval_node, BoolNode.eval, eval_pair]
  rfl

@[simp] lemma eval_bor {n : ℕ} (a b : BooleanNetwork n 1) (x : Fin n → Bool) (j : Fin 1) :
    (a.bor b).eval x j = (a.eval x 0 || b.eval x 0) := by
  simp [bor]

@[simp] lemma eval_bxor {n : ℕ} (a b : BooleanNetwork n 1) (x : Fin n → Bool) (j : Fin 1) :
    (a.bxor b).eval x j = Bool.xor (a.eval x 0) (b.eval x 0) := by
  simp only [bxor, eval_bor, eval_band, eval_bnot]
  cases a.eval x 0 <;> cases b.eval x 0 <;> rfl

@[simp] lemma eval_mux {n : ℕ} (c a b : BooleanNetwork n 1) (x : Fin n → Bool) (j : Fin 1) :
    (mux c a b).eval x j = if c.eval x 0 then a.eval x 0 else b.eval x 0 := by
  simp only [mux, eval_bor, eval_band, eval_bnot]
  cases c.eval x 0 <;> simp

@[simp] lemma eval_majority {n : ℕ} (a b c : BooleanNetwork n 1) (x : Fin n → Bool) (j : Fin 1) :
    (majority a b c).eval x j = Bool.atLeastTwo (a.eval x 0) (b.eval x 0) (c.eval x 0) := by
  simp only [majority, eval_bor, eval_band]
  cases a.eval x 0 <;> cases b.eval x 0 <;> cases c.eval x 0 <;> rfl

@[simp] lemma count_bit {n : ℕ} (i : Fin n) : (bit i).net.count = 0 := rfl
@[simp] lemma count_constant {n : ℕ} (b : Bool) : (constant (n := n) b).net.count = 1 := rfl
@[simp] lemma count_bnot {n : ℕ} (a : BooleanNetwork n 1) : a.bnot.net.count = a.net.count + 1 := by
  simp [bnot, count_comp]
@[simp] lemma count_band {n : ℕ} (a b : BooleanNetwork n 1) :
    (a.band b).net.count = a.net.count + b.net.count + 1 := by simp [band, count_comp, count_pair]
@[simp] lemma count_bor {n : ℕ} (a b : BooleanNetwork n 1) :
    (a.bor b).net.count = a.net.count + b.net.count + 4 := by simp [bor]; omega
@[simp] lemma count_bxor {n : ℕ} (a b : BooleanNetwork n 1) :
    (a.bxor b).net.count = 2 * a.net.count + 2 * b.net.count + 8 := by simp [bxor]; omega
@[simp] lemma count_mux {n : ℕ} (c a b : BooleanNetwork n 1) :
    (mux c a b).net.count = 2 * c.net.count + a.net.count + b.net.count + 7 := by simp [mux]; omega
@[simp] lemma count_majority {n : ℕ} (a b c : BooleanNetwork n 1) :
    (majority a b c).net.count = 2 * a.net.count + 2 * b.net.count + c.net.count + 10 := by
  simp [majority]; omega

/-- Logical assignment preserves the input values in the physical trace, but
provides the standard overwritten-state interface to the next computation. -/
def assign {n : ℕ} (i : Fin n) (v : BooleanNetwork n 1) : BooleanNetwork n n :=
  ((select id).pair v).rewire (fun j => if j = i then Fin.natAdd n 0 else j.castAdd 1)

lemma eval_assign {n : ℕ} (i : Fin n) (v : BooleanNetwork n 1) (x : Fin n → Bool) :
    (assign i v).eval x = Function.update x i (v.eval x 0) := by
  funext j
  simp only [assign, eval_rewire, Function.comp_apply, eval_pair, eval_select]
  by_cases hj : j = i
  · subst j
    simp
  · simp [hj]

@[simp] lemma count_assign {n : ℕ} (i : Fin n) (v : BooleanNetwork n 1) :
    (assign i v).net.count = v.net.count := by simp [assign, count_pair]

/-- Sequentially composed bounded logical updates compile by retained history. -/
def sequence {n : ℕ} : List (BooleanNetwork n n) → BooleanNetwork n n
  | [] => select id
  | c :: cs => c.comp (sequence cs)

lemma eval_sequence {n : ℕ} (cs : List (BooleanNetwork n n)) (x : Fin n → Bool) :
    (sequence cs).eval x = cs.foldl (fun x c => c.eval x) x := by
  induction cs generalizing x with
  | nil => rfl
  | cons c cs ih => rw [sequence, eval_comp, ih]; rfl

lemma count_sequence {n : ℕ} (cs : List (BooleanNetwork n n)) :
    (sequence cs).net.count = (cs.map (fun c => c.net.count)).sum := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [sequence, count_comp, ih]

def iterate {n : ℕ} (c : BooleanNetwork n n) (k : ℕ) : BooleanNetwork n n :=
  sequence (List.replicate k c)

lemma eval_iterate {n : ℕ} (c : BooleanNetwork n n) (k : ℕ) (x : Fin n → Bool) :
    (iterate c k).eval x = (c.eval^[k]) x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    change (c.comp (iterate c k)).eval x = _
    rw [eval_comp, ih, Function.iterate_succ_apply]

lemma count_iterate {n : ℕ} (c : BooleanNetwork n n) (k : ℕ) :
    (iterate c k).net.count = k * c.net.count := by
  simp [iterate, count_sequence, List.sum_replicate]

end ExactQuantumFactoring.BooleanNetwork


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/BooleanVector.lean =====
namespace OAI

section


open scoped BigOperators
namespace ExactQuantumFactoring.BooleanNetwork

/-- Assemble an arbitrary vector of single-bit combinational outputs, retaining
separate traces. This is a finite circuit construction, not a truth table. -/
def vector {n : ℕ} : {m : ℕ} → (Fin m → BooleanNetwork n 1) → BooleanNetwork n m
  | 0, _ => select Fin.elim0
  | m+1, f => (vector (fun i => f i.castSucc)).pair (f (Fin.last m))

@[simp] lemma eval_vector {n m : ℕ} (f : Fin m → BooleanNetwork n 1)
    (x : Fin n → Bool) (i : Fin m) : (vector f).eval x i = (f i).eval x 0 := by
  induction m with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    rw [vector, eval_pair, Fin.append_right_eq_snoc]
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [Fin.snoc_last]
    · rw [Fin.snoc_castSucc]
      exact ih _ j

@[simp] lemma count_vector {n m : ℕ} (f : Fin m → BooleanNetwork n 1) :
    (vector f).net.count = ∑ i, (f i).net.count := by
  induction m with
  | zero => simp [vector]
  | succ m ih => simp [vector, count_pair, ih, Fin.sum_univ_castSucc]

lemma count_vector_le {n m c : ℕ} (f : Fin m → BooleanNetwork n 1)
    (h : ∀ i, (f i).net.count ≤ c) : (vector f).net.count ≤ m*c := by
  rw [count_vector]
  calc
    _ ≤ ∑ _ : Fin m, c := Finset.sum_le_sum (fun i _ => h i)
    _ = _ := by simp

/-- Add explicit zero slots, with <=m nodes. Duplicate outputs may share zero,
but the simple linear upper bound is sufficient for the compiler. -/
def padRight (n m : ℕ) : BooleanNetwork n (n+m) :=
  vector (fun i => if h : i.val < n then bit ⟨i.val,h⟩ else constant false)

lemma eval_padRight (n m : ℕ) (x : Fin n → Bool) :
    (padRight n m).eval x = Fin.append x (fun _ => false) := by
  funext i
  rw [padRight, eval_vector]
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [j.isLt]
  · simp

lemma count_padRight (n m : ℕ) : (padRight n m).net.count = m := by
  rw [padRight, count_vector, Fin.sum_univ_add]
  have h₁ : (∑ x : Fin n, (if h : x.val < n then bit (n := n) ⟨x.val,h⟩
      else constant false).net.count) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    rw [dite_eq_left x.isLt]
    rfl
  have h₂ : (∑ x : Fin m, (if h : n+x.val < n then bit (n := n) ⟨n+x.val,h⟩
      else constant false).net.count) = m := by
    trans ∑ _ : Fin m, 1
    · apply Finset.sum_congr rfl
      intro x _
      rw [dite_eq_right (by omega : ¬ n+x.val < n)]
      rfl
    · simp
  exact (congrArg₂ (· + ·) h₁ h₂).trans (Nat.zero_add _)

end ExactQuantumFactoring.BooleanNetwork


end

end OAI


