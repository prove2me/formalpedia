-- Prove2me | Definitions.Def_OAI_QuantumFactoring_Part10
-- name    : OAI_QuantumFactoring_Part10
-- status  : Definition
-- author  : @SamenHossain
-- created : 2026-10-12T07:20:17.529026+00:00
-- url     : https://prove2.me/theorems/07807055-85cc-4277-a056-c578cb528ad4
-- title:
--   Exact quantum factoring, part 10 of 38 (port of OpenAI's formalization)
-- statement:
--   Part 10 of 38 of a port of OpenAI's Lean formalization of the manuscript *Exact quantum factoring over a fixed finite gate set* (OpenAI, September 25, 2026). This part contains the modules `DyadicCompletion`, `LevelIndependence`, `FactorSplitting`, `LevelCounts`, `LevelBounds`, `PrimePowerLevels`, `CRTLevels`, `ArithmeticBounds`, `ContinuedFractionRecovery`, `GcdCircuit`, `SplitCandidate`.
--
--   **Attribution.** The code is adapted from the OpenAI "math" repository, commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, directory `lean/OAI/Computability/QuantumFactoring`. It is © OpenAI and licensed under the Apache License 2.0; the adapted code is redistributed under the same license.
--
--   **Modifications.** Modules are concatenated in dependency order, with their imports replaced by the previous part. The model definitions come from the platform definition `ExactQuantumFactoring`, which is identical to upstream `Basic.lean`. This part also makes small compatibility edits for Lean 4.33.1 / Mathlib 0df444a: in ArithmeticBounds.lean, `Finset.prod_le_prod` → `Finset.prod_le_prod'`.
--
--   The development is split into 38 parts only so that each compiles within the platform's time limit. Together the parts supply the circuit family `PhysicalTree.finalCircuit` and its specification, used to prove `OAI.ExactQuantumFactoring.zero_amplitude_core`.
-- source:
--   OpenAI, openai/math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, lean/OAI/Computability/QuantumFactoring: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/DyadicCompletion.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/LevelIndependence.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/FactorSplitting.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/LevelCounts.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/LevelBounds.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/PrimePowerLevels.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/CRTLevels.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/ArithmeticBounds.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/ContinuedFractionRecovery.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/GcdCircuit.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/SplitCandidate.lean (Apache License 2.0); manuscript https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Exact-quantum-factoring-over-a-fixed-finite-gate-set-September-25-2026/main.pdf

/-
Exact quantum factoring development (port of OpenAI's formalization), part 10 of 38.

Adapted from the OpenAI "math" repository (https://github.com/openai/math, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a), lean/OAI/Computability/QuantumFactoring/: DyadicCompletion.lean, LevelIndependence.lean, FactorSplitting.lean, LevelCounts.lean, LevelBounds.lean, PrimePowerLevels.lean, CRTLevels.lean, ArithmeticBounds.lean, ContinuedFractionRecovery.lean, GcdCircuit.lean, SplitCandidate.lean
These files formalize the manuscript "Exact quantum factoring over a fixed finite gate set"
(OpenAI, September 25, 2026). Copyright OpenAI. Licensed under the Apache License, Version 2.0
(http://www.apache.org/licenses/LICENSE-2.0); the adapted code is distributed under the same license,
on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND.

Modifications: modules concatenated in dependency order with their import lines removed; the model
definitions (Basic.lean) come from the platform definition `ExactQuantumFactoring`, to which upstream
Basic.lean is identical; the final assembly (Main.lean) is omitted; compatibility edits for the platform Lean/Mathlib versions: in ArithmeticBounds.lean, `Finset.prod_le_prod` → `Finset.prod_le_prod'`.
-/
import Mathlib
import Definitions.Def_OAI_QuantumFactoring_Part09

set_option autoImplicit false

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/DyadicCompletion.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open Exactness OrderTrial

namespace Completion

def coeff (W t : ℕ) (s z : ℚ) : ℚ := completionCoeff (W+t+2) z ((1-1/(2:ℚ)^t)*s)
def guessRetention (W t : ℕ) (s z : ℚ) : ℚ :=
  completionRemainder (W+t+2) z ((1-1/(2:ℚ)^t)*s)*(2:ℚ)^W/(1/(2:ℚ)^t)
def coinBits (W t d : ℕ) : ℕ := (W+t+2)+t+d

lemma coeff_at (W t d : ℕ) (s z : ℚ) : DyadicAt (coinBits W t d) (coeff W t s z) := by
  apply (show DyadicAt (W+t+2) (coeff W t s z) from ⟨_,rfl⟩).mono
  unfold coinBits
  omega

lemma guess_at {W t d j : ℕ} {s z : ℚ} (hs : DyadicAt d s) (hz : DyadicAt j z)
    (hj : j≤coinBits W t d) : DyadicAt (coinBits W t d) (guessRetention W t s z) := by
  have hδ : DyadicAt t (1/(2:ℚ)^t) := ⟨1,by simp⟩
  have hA : DyadicAt (t+d) ((1-1/(2:ℚ)^t)*s) := by
    simpa using ((DyadicAt.integer t 1).sub hδ).mul hs
  have hC : DyadicAt (W+t+2) (coeff W t s z) := ⟨_,rfl⟩
  have hCA : DyadicAt (coinBits W t d) (coeff W t s z*((1-1/(2:ℚ)^t)*s)) := by
    simpa only [coinBits,Nat.add_assoc] using hC.mul hA
  have hR := (hz.mono hj).sub hCA
  have hG := hR.int_mul (2^(W+t))
  convert hG using 1
  push_cast
  unfold guessRetention completionRemainder coeff
  rw [pow_add]
  field_simp

abbrev Raw (α : Type*) (W t d : ℕ) := Basis t × (α × (Basis W × Basis (coinBits W t d)))
noncomputable def fresh {α : Type*} (ψ : α→ℂ) (W t d : ℕ) : Raw α W t d→ℂ :=
  independentState (fairState t) (independentState ψ
    (independentState (fairState W) (fairState (coinBits W t d))))

def rare {t : ℕ} (b : Basis t) : Prop := (bitsValue b).toNat=0
instance {t : ℕ} (b : Basis t) : Decidable (rare b) :=
  inferInstanceAs (Decidable ((bitsValue b).toNat=0))

def threshold {D : ℕ} (p : ℚ) (b : Basis D) : Prop :=
  (bitsValue b).toNat<(Int.floor (p*(2:ℚ)^D)).toNat

def output {α : Type*} {W t d : ℕ} (ordinary : α→Basis W) (r : Raw α W t d) : Basis W :=
  if rare r.1 then r.2.2.1 else ordinary r.2.1

def ordinaryPass {α : Type*} {W t d : ℕ} (good : α→Prop) (s z : ℚ) (r : Raw α W t d) : Prop :=
  ¬rare r.1 ∧ (good r.2.1 ∧ threshold (coeff W t s z) r.2.2.2)
def guessPass {α : Type*} {W t d : ℕ} (y₀ : Basis W) (s z : ℚ) (r : Raw α W t d) : Prop :=
  rare r.1 ∧ (r.2.2.1=y₀ ∧ threshold (guessRetention W t s z) r.2.2.2)
def passed {α : Type*} {W t d : ℕ} (good : α→Prop) (y₀ : Basis W) (s z : ℚ) (r : Raw α W t d) : Prop :=
  ordinaryPass good s z r ∨ guessPass y₀ s z r

lemma fair_eq_mass (W : ℕ) (y₀ : Basis W) :
    outcomeMass (fun y => y=y₀) (fairState W)=1/(2:ℝ)^W := by
  classical
  simp only [outcomeMass,Finset.sum_ite_eq',Finset.mem_univ,ite_true,fairState_mass,one_div,inv_pow]

lemma fresh_normalized {α : Type*} [Fintype α] (ψ : α→ℂ) (W t d : ℕ)
    (hψ : ∑ x,Complex.normSq (ψ x)=1) : ∑ x,Complex.normSq (fresh ψ W t d x)=1 := by
  have h₁ := RecordedHistory.append_normalized (fairState W)
    (fun _ => fairState (coinBits W t d)) (fair_normalized W) (fun _ => fair_normalized _)
  have h₂ := RecordedHistory.append_normalized ψ
    (fun _ => independentState (fairState W) (fairState (coinBits W t d))) hψ (fun _ => h₁)
  exact RecordedHistory.append_normalized (fairState t)
    (fun _ => independentState ψ (independentState (fairState W) (fairState (coinBits W t d))))
    (fair_normalized t) (fun _ => h₂)

/-- Actual fresh registers do NOT depend on s, goodness or the canonical output.
Those values are used only by the later classical test on the retained record. -/
theorem passed_mass {α : Type*} [Fintype α] {W t d j : ℕ}
    (ψ : α→ℂ) (good : α→Prop) (y₀ : Basis W) (s z : ℚ)
    (hψ : ∑ x,Complex.normSq (ψ x)=1) (hgood : outcomeMass good ψ=(s:ℝ))
    (hsd : DyadicAt d s) (hzd : DyadicAt j z) (hj : j≤coinBits W t d)
    (hs₀ : 0<s) (hs₁ : s≤1) (ht : 0<t) (hz : 0<z)
    (hzA : z≤(1-1/(2:ℚ)^t)*s) :
    outcomeMass (passed good y₀ s z) (fresh ψ W t d)=(z:ℝ) := by
  have hb := completion_retention_bounds W t hs₀ hs₁ ht hz hzA
  have hC := dyadic_fair_threshold (coeff_at W t d s z) hb.1 hb.2.1
  have hG := dyadic_fair_threshold (guess_at hsd hzd hj) hb.2.2.1 (hb.2.2.2.le.trans (by norm_num))
  have hr : outcomeMass (rare (t:=t)) (fairState t)=1/(2:ℝ)^t :=
    fair_value_mass (by positivity : 0<2^t)
  have hnr : outcomeMass (fun b : Basis t => ¬rare b) (fairState t)=1-1/(2:ℝ)^t := by
    rw [RepeatedTrials.mass_compl _ _ (fair_normalized t),hr]
  have ho : outcomeMass (ordinaryPass (W:=W) (t:=t) (d:=d) good s z) (fresh ψ W t d)=
      (1-1/(2:ℝ)^t)*(s:ℝ)*(coeff W t s z:ℝ) := by
    rw [show ordinaryPass (W:=W) (t:=t) (d:=d) good s z =
      (fun r : Raw α W t d => ¬rare r.1 ∧ (good r.2.1 ∧ threshold (coeff W t s z) r.2.2.2)) from rfl]
    rw [fresh,independent_mass (fairState t)
      (independentState ψ (independentState (fairState W) (fairState (coinBits W t d))))
      (fun b => ¬rare b) (fun r => good r.1 ∧ threshold (coeff W t s z) r.2.2),
      independent_mass ψ (independentState (fairState W) (fairState (coinBits W t d)))
      good (fun r => threshold (coeff W t s z) r.2),
      independent_mass_right _ _ _ (fair_normalized W)]
    rw [hnr,hgood]
    rw [show outcomeMass (threshold (D:=coinBits W t d) (coeff W t s z))
      (fairState _)= (coeff W t s z:ℝ) from hC]
    ring
  have hg : outcomeMass (guessPass (t:=t) (d:=d) y₀ s z) (fresh ψ W t d)=
      (1/(2:ℝ)^t)*(1/(2:ℝ)^W)*(guessRetention W t s z:ℝ) := by
    rw [show guessPass (t:=t) (d:=d) y₀ s z =
      (fun r : Raw α W t d => rare r.1 ∧ (r.2.2.1=y₀ ∧ threshold (guessRetention W t s z) r.2.2.2)) from rfl]
    rw [fresh,independent_mass (fairState t)
      (independentState ψ (independentState (fairState W) (fairState (coinBits W t d))))
      rare (fun r => r.2.1=y₀ ∧ threshold (guessRetention W t s z) r.2.2),
      independent_mass_right ψ (independentState (fairState W) (fairState (coinBits W t d)))
        (fun r => r.1=y₀ ∧ threshold (guessRetention W t s z) r.2) hψ,
      independent_mass (fairState W) (fairState (coinBits W t d)) (fun y => y=y₀)
        (threshold (guessRetention W t s z)),fair_eq_mass,hr]
    rw [show outcomeMass (threshold (D:=coinBits W t d) (guessRetention W t s z))
      (fairState _)= (guessRetention W t s z:ℝ) from hG]
    ring
  change outcomeMass (fun r => ordinaryPass good s z r ∨ guessPass y₀ s z r)
    (fresh ψ W t d)=(z:ℝ)
  rw [outcomeMass_disjoint_or _ _ _ (by intro r h; exact h.1.1 h.2.1),ho,hg]
  have he := congrArg (fun q : ℚ => (q:ℝ)) (completion_mass W t s z)
  push_cast at he
  simpa [coeff,guessRetention] using he

lemma passed_good {α : Type*} {W t d : ℕ} (ordinary : α→Basis W) (P : Basis W→Prop)
    (y₀ : Basis W) (s z : ℚ) (hy : P y₀) (r : Raw α W t d)
    (h : passed (P∘ordinary) y₀ s z r) : P (output ordinary r) := by
  rcases h with h | h
  · simpa only [output,ite_eq_right h.1,Function.comp_def] using h.2.1
  · simpa only [output,ite_eq_left h.1,h.2.1] using hy

/-- Literal fixed-gate program for the raw extended record; no oracle for the
future data, success probability, or distinguished guess occurs in its code. -/
def program {q : ℕ} (P : List (Instruction q)) (W t d : ℕ) :
    List (Instruction (t+(q+(W+coinBits W t d)))) :=
  parallelProgram (hadamardPrefix t t le_rfl) (parallelProgram P
    (parallelProgram (hadamardPrefix W W le_rfl) (hadamardPrefix (coinBits W t d) (coinBits W t d) le_rfl)))
def layout (q W t d : ℕ) : Raw (Basis q) W t d ≃ Basis (t+(q+(W+coinBits W t d))) :=
  productLayout (Equiv.refl _) (productLayout (Equiv.refl _) (productLayout (Equiv.refl _) (Equiv.refl _)))
lemma program_entry {q : ℕ} (P : List (Instruction q)) (W t d : ℕ) (a : Basis q)
    (r : Raw (Basis q) W t d) :
    (programMatrix (program P W t d)).mulVec
      (basisVector (layout q W t d ((fun _ => false),a,(fun _ => false),(fun _ => false))))
      (layout q W t d r)=fresh ((programMatrix P).mulVec (basisVector a)) W t d r := by
  simp only [program,layout,productLayout_apply,Equiv.refl_apply,parallelProgram_entry,hadamards_zero]
  rfl
lemma program_length {q : ℕ} (P : List (Instruction q)) (W t d : ℕ) :
    (program P W t d).length=P.length+t+W+coinBits W t d := by
  simp only [program,parallelProgram_length,hadamardPrefix_length]
  omega

end Completion
end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/LevelIndependence.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


open scoped BigOperators
namespace ExactQuantumFactoring

noncomputable def equalLevelEquiv {A B T : Type*} (f : A → T) (g : B → T) :
    {x : A × B // f x.1 = g x.2} ≃ Σ b : B, {a : A // f a = g b} where
  toFun x := ⟨x.1.2, x.1.1, x.2⟩
  invFun x := ⟨(x.2.1,x.1),x.2.2⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl

/-- Counting the equality of two independent levels by fibers, with no
assumption about an approximately uniform distribution. -/
theorem equalLevel_card {A B T : Type*} [Fintype A] [Fintype B]
    (f : A → T) (g : B → T) [DecidableEq T] :
    Fintype.card {x : A × B // f x.1 = g x.2} = ∑ b : B, Fintype.card {a : A // f a = g b} := by
  classical
  rw [Fintype.card_congr (equalLevelEquiv f g), Fintype.card_sigma]

theorem twice_equalLevel_card_le {A B T : Type*} [Fintype A] [Fintype B]
    (f : A → T) (g : B → T) [DecidableEq T]
    (hf : ∀ t, 2 * Fintype.card {a : A // f a = t} ≤ Fintype.card A) :
    2 * Fintype.card {x : A × B // f x.1 = g x.2} ≤ Fintype.card A * Fintype.card B := by
  classical
  rw [equalLevel_card, Finset.mul_sum]
  calc
    _ ≤ ∑ _ : B, Fintype.card A := Finset.sum_le_sum (fun b _ => hf (g b))
    _ = _ := by simp [mul_comm]

noncomputable def allEqualLevelEquiv {ι T : Type*} {G : ι → Type*} (i₀ : ι)
    (f : ∀ i, G i → T) :
    {x : ∀ i, G i // ∀ i, f i (x i) = f i₀ (x i₀)} ≃
      Σ t : T, ∀ i, {x : G i // f i x = t} where
  toFun x := ⟨f i₀ (x.1 i₀), fun i => ⟨x.1 i,x.2 i⟩⟩
  invFun x := ⟨fun i => (x.2 i).1, fun i => (x.2 i).2.trans (x.2 i₀).2.symm⟩
  left_inv x := rfl
  right_inv x := by
    rcases x with ⟨t,x⟩
    dsimp
    have he : f i₀ (x i₀).1 = t := (x i₀).2
    apply Sigma.ext he
    have hh : ∀ (s t : T) (a : ∀ i, {z : G i // f i z = s})
        (b : ∀ i, {z : G i // f i z = t}), s = t →
        (∀ i, (a i).val = (b i).val) → HEq a b := by
      rintro s t a b rfl hab
      apply heq_of_eq
      funext i
      exact Subtype.ext (hab i)
    exact hh _ _ _ _ he (fun _ => rfl)

/-- Exact product formula used in the source's retrospective F computation. -/
theorem allEqualLevel_card {ι T : Type*} {G : ι → Type*} [Fintype ι] [Fintype T]
    [∀ i, Fintype (G i)] [DecidableEq T] [DecidableEq ι] (i₀ : ι) (f : ∀ i, G i → T) :
    Fintype.card {x : ∀ i, G i // ∀ i, f i (x i) = f i₀ (x i₀)} =
      ∑ t : T, ∏ i : ι, Fintype.card {x : G i // f i x = t} := by
  classical
  rw [Fintype.card_congr (allEqualLevelEquiv i₀ f), Fintype.card_sigma]
  congr 1
  funext t
  exact Fintype.card_pi

/-- Extra components can only decrease the all-equal event. -/
theorem twice_constrained_card_le {A B C T : Type*} [Fintype A] [Fintype B] [Fintype C]
    (f : A → T) (g : B → T) [DecidableEq T]
    (P : A × B × C → Prop) [DecidablePred P]
    (hp : ∀ x, P x → f x.1 = g x.2.1)
    (hf : ∀ t, 2 * Fintype.card {a : A // f a = t} ≤ Fintype.card A) :
    2 * Fintype.card {x : A × B × C // P x} ≤
      Fintype.card A * Fintype.card B * Fintype.card C := by
  classical
  let emb : {x : A × B × C // P x} → ({x : A × B // f x.1 = g x.2} × C) :=
    fun x => (⟨(x.1.1,x.1.2.1),hp x.1 x.2⟩,x.1.2.2)
  have hinj : Function.Injective emb := by
    intro x y h
    apply Subtype.ext
    have h₁ := congrArg (fun z => z.1.1.1) h
    have h₂ := congrArg (fun z => z.1.1.2) h
    have h₃ := congrArg Prod.snd h
    exact Prod.ext h₁ (Prod.ext h₂ h₃)
  have hc := Fintype.card_le_of_injective emb hinj
  rw [Fintype.card_prod] at hc
  calc
    _ ≤ 2 * (Fintype.card {x : A × B // f x.1 = g x.2} * Fintype.card C) :=
      Nat.mul_le_mul_left 2 hc
    _ = (2 * Fintype.card {x : A × B // f x.1 = g x.2}) * Fintype.card C := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (twice_equalLevel_card_le f g hf)

/-- Two distinct independent components suffice for the exact half bound. -/
theorem twice_allEqualLevel_card_le {ι T : Type*} {G : ι → Type*}
    [Fintype ι] [∀ i, Fintype (G i)] [DecidableEq T] [DecidableEq ι]
    (i₀ i₁ : ι) (hi : i₁ ≠ i₀) (f : ∀ i, G i → T)
    (hf : ∀ t, 2 * Fintype.card {a : G i₀ // f i₀ a = t} ≤ Fintype.card (G i₀)) :
    2 * Fintype.card {x : ∀ i, G i // ∀ i, f i (x i) = f i₀ (x i₀)} ≤
      Fintype.card (∀ i, G i) := by
  classical
  let R := ∀ j : {j : ι // j ≠ i₀}, G j.val
  let g : R → T := fun x => f i₁ (x ⟨i₁,hi⟩)
  let emb : {x : ∀ i, G i // ∀ i, f i (x i) = f i₀ (x i₀)} →
      {x : G i₀ × R // f i₀ x.1 = g x.2} :=
    fun x => ⟨(Equiv.piSplitAt i₀ G) x.val, (x.property i₁).symm⟩
  have hinj : Function.Injective emb := by
    intro x y h
    apply Subtype.ext
    apply (Equiv.piSplitAt i₀ G).injective
    exact congrArg Subtype.val h
  have hc := Fintype.card_le_of_injective emb hinj
  calc
    _ ≤ 2 * Fintype.card {x : G i₀ × R // f i₀ x.1 = g x.2} :=
      Nat.mul_le_mul_left 2 hc
    _ ≤ Fintype.card (G i₀) * Fintype.card R := twice_equalLevel_card_le _ _ hf
    _ = Fintype.card (∀ i, G i) := by
      rw [← Fintype.card_prod]
      exact (Fintype.card_congr (Equiv.piSplitAt i₀ G)).symm

end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/FactorSplitting.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring

/-- Strictly smaller 2-adic level makes a divisor divide the half-order. -/
theorem dvd_half_of_level_lt {d r : ℕ} (hr : r ≠ 0) (hdr : d ∣ r)
    (hlevel : padicValNat 2 d < padicValNat 2 r) : d ∣ r / 2 := by
  rcases hdr with ⟨k, rfl⟩
  have hd : d ≠ 0 := left_ne_zero_of_mul hr
  have hk : k ≠ 0 := right_ne_zero_of_mul hr
  rw [padicValNat.mul hd hk] at hlevel
  have htwo : 2 ∣ k := dvd_of_one_le_padicValNat (by omega : 1 ≤ padicValNat 2 k)
  rcases htwo with ⟨t, rfl⟩
  use t
  rw [show d * (2 * t) = (d * t) * 2 by ring, Nat.mul_div_cancel _ (by decide)]

/-- Divisibility cannot increase the 2-adic valuation. -/
theorem level_le_of_dvd {d r : ℕ} (hr : r ≠ 0) (hdr : d ∣ r) :
    padicValNat 2 d ≤ padicValNat 2 r := by
  rcases hdr with ⟨k, rfl⟩
  rw [padicValNat.mul (left_ne_zero_of_mul hr) (right_ne_zero_of_mul hr)]
  omega

/-- The actual representative used by bounded modular gcd arithmetic. -/
noncomputable def halfOrderResidue {m : ℕ} (a : (ZMod m)ˣ) : ℕ :=
  ((a ^ (orderOf a / 2) : (ZMod m)ˣ) : ZMod m).val

noncomputable def splitGcd {m : ℕ} (a : (ZMod m)ˣ) : ℕ :=
  Nat.gcd (halfOrderResidue a + m - 1) m

/-- A single lower-level component suffices for a proper nontrivial split.
The largest-level component is not assumed to have a chosen generator. -/
theorem splitGcd_proper_of_lower_component {m d : ℕ} (hm : 2 ≤ m) (hd : 2 ≤ d)
    (hdm : d ∣ m) (a : (ZMod m)ˣ)
    (hlevel : padicValNat 2 (orderOf (Units.map (ZMod.castHom hdm (ZMod d)).toMonoidHom a))
      < padicValNat 2 (orderOf a)) :
    1 < splitGcd a ∧ splitGcd a < m ∧ splitGcd a ∣ m := by
  let : NeZero m := ⟨by omega⟩
  let : NeZero d := ⟨by omega⟩
  let f : (ZMod m)ˣ →* (ZMod d)ˣ := Units.map (ZMod.castHom hdm (ZMod d)).toMonoidHom
  have hr : 0 < orderOf a := orderOf_pos a
  have hhalf : orderOf (f a) ∣ orderOf a / 2 :=
    dvd_half_of_level_lt hr.ne' (orderOf_map_dvd f a) hlevel
  have hreduce : f a ^ (orderOf a / 2) = 1 := orderOf_dvd_iff_pow_eq_one.mp hhalf
  have htwo : 2 ∣ orderOf a := dvd_of_one_le_padicValNat (by omega)
  have hhalfnz : orderOf a / 2 ≠ 0 := by
    have : 2 ≤ orderOf a := Nat.le_of_dvd hr htwo
    omega
  have hglobal : a ^ (orderOf a / 2) ≠ 1 :=
    pow_ne_one_of_lt_orderOf hhalfnz (Nat.div_lt_self hr (by decide))
  have hle : 1 ≤ halfOrderResidue a + m := by omega
  have hcastm : ((halfOrderResidue a + m - 1 : ℕ) : ZMod m) =
      ((a ^ (orderOf a / 2) : (ZMod m)ˣ) : ZMod m) - 1 := by
    rw [Nat.cast_sub hle, Nat.cast_add, Nat.cast_one, ZMod.natCast_self, add_zero]
    exact congrArg (fun x : ZMod m => x - 1) (ZMod.natCast_zmod_val _)
  have hcastd : ((halfOrderResidue a + m - 1 : ℕ) : ZMod d) = 0 := by
    have heq : (ZMod.castHom hdm (ZMod d))
        ((a ^ (orderOf a / 2) : (ZMod m)ˣ) : ZMod m) = 1 := by
      have hv := congrArg (fun x : (ZMod d)ˣ => (x : ZMod d)) hreduce
      change (((f a) ^ (orderOf a / 2) : (ZMod d)ˣ) : ZMod d) = 1 at hv
      rw [← map_pow] at hv
      exact hv
    have hz : (m : ZMod d) = 0 := (ZMod.natCast_eq_zero_iff m d).mpr hdm
    rw [Nat.cast_sub hle, Nat.cast_add, Nat.cast_one, hz, add_zero]
    rw [ZMod.castHom_apply, ZMod.cast_eq_val] at heq
    exact sub_eq_zero.mpr heq
  have hdiv : d ∣ halfOrderResidue a + m - 1 :=
    (ZMod.natCast_eq_zero_iff _ _).mp hcastd
  have hnond : ¬ m ∣ halfOrderResidue a + m - 1 := by
    intro h
    have hz := (ZMod.natCast_eq_zero_iff _ m).mpr h
    rw [hcastm] at hz
    exact hglobal (Units.ext (sub_eq_zero.mp hz))
  have hgpos : 0 < splitGcd a := Nat.gcd_pos_of_pos_right _ (by omega)
  have hglower : d ≤ splitGcd a := Nat.le_of_dvd hgpos (Nat.dvd_gcd hdiv hdm)
  have hgupper : splitGcd a ≤ m := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right _ _)
  have hgneq : splitGcd a ≠ m := by
    intro h
    exact hnond (Nat.gcd_eq_right_iff_dvd.mp h)
  exact ⟨by omega, by omega, Nat.gcd_dvd_right _ _⟩

/-- Two unequal local levels guarantee that one of them is below the global
level, so the verified order always supplies a nontrivial gcd. -/
theorem splitGcd_proper_of_unequal_components {m d e : ℕ} (hm : 2 ≤ m)
    (hd : 2 ≤ d) (he : 2 ≤ e) (hdm : d ∣ m) (hem : e ∣ m) (a : (ZMod m)ˣ)
    (hne : padicValNat 2 (orderOf (Units.map (ZMod.castHom hdm (ZMod d)).toMonoidHom a)) ≠
      padicValNat 2 (orderOf (Units.map (ZMod.castHom hem (ZMod e)).toMonoidHom a))) :
    1 < splitGcd a ∧ splitGcd a < m ∧ splitGcd a ∣ m := by
  let : NeZero m := ⟨by omega⟩
  have hr : orderOf a ≠ 0 := (orderOf_pos a).ne'
  have hdle := level_le_of_dvd hr
    (orderOf_map_dvd (Units.map (ZMod.castHom hdm (ZMod d)).toMonoidHom) a)
  have hele := level_le_of_dvd hr
    (orderOf_map_dvd (Units.map (ZMod.castHom hem (ZMod e)).toMonoidHom) a)
  rcases lt_or_gt_of_ne hne with h | h
  · exact splitGcd_proper_of_lower_component hm hd hdm a (h.trans_le hele)
  · exact splitGcd_proper_of_lower_component hm he hem a (h.trans_le hdle)

end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/LevelCounts.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators


open scoped BigOperators
namespace ExactQuantumFactoring

/-- Dividing a positive multiple by a power of two preserves exactly the
order divisors with enough 2-adic slack. -/
theorem dvd_div_pow_two_iff {d r k : ℕ} (hr : r ≠ 0) (hdr : d ∣ r) (hk : 2 ^ k ∣ r) :
    d ∣ r / 2 ^ k ↔ padicValNat 2 d + k ≤ padicValNat 2 r := by
  have hkle : k ≤ padicValNat 2 r := (padicValNat_dvd_iff_le hr).mp hk
  constructor
  · intro h
    have hquot : r / 2 ^ k ≠ 0 := by
      have : 2 ^ k ≤ r := Nat.le_of_dvd (Nat.pos_of_ne_zero hr) hk
      have : 0 < r / 2 ^ k := Nat.div_pos this (by positivity)
      omega
    have hh := level_le_of_dvd hquot h
    rw [padicValNat.div_pow hk] at hh
    omega
  · intro h
    rcases hdr with ⟨a, rfl⟩
    have hd : d ≠ 0 := left_ne_zero_of_mul hr
    have ha : a ≠ 0 := right_ne_zero_of_mul hr
    rw [padicValNat.mul hd ha] at h
    have hp : 2 ^ k ∣ a := (padicValNat_dvd_iff_le ha).mpr (by omega)
    apply (Nat.dvd_div_iff_mul_dvd hk).mpr
    simpa only [Nat.mul_comm (2 ^ k) d] using Nat.mul_dvd_mul_left d hp

/-- For a divisor, an exact valuation cutoff is a single ordinary divisibility
test; hence its size is a cyclic-group root count, not residue enumeration. -/
theorem level_le_iff_dvd_cutoff {d r t : ℕ} (hr : r ≠ 0) (hdr : d ∣ r) :
    padicValNat 2 d ≤ t ↔ d ∣ r / 2 ^ (padicValNat 2 r - t) := by
  have hle := level_le_of_dvd hr hdr
  have hp : 2 ^ (padicValNat 2 r - t) ∣ r :=
    (padicValNat_dvd_iff_le hr).mpr (Nat.sub_le _ _)
  rw [dvd_div_pow_two_iff hr hdr hp]
  omega

noncomputable def cumulativeLevelCount (G : Type*) [Group G] [Fintype G] (t : ℕ) : ℕ := by
  classical
  exact Fintype.card {x : G // padicValNat 2 (orderOf x) ≤ t}

noncomputable def levelCount (G : Type*) [Group G] [Fintype G] (t : ℕ) : ℕ := by
  classical
  exact Fintype.card {x : G // padicValNat 2 (orderOf x) = t}

/-- The cumulative law of levels in every finite cyclic group. -/
theorem cumulativeLevelCount_eq (G : Type*) [CommGroup G] [Fintype G] [IsCyclic G] (t : ℕ) :
    cumulativeLevelCount G t = Fintype.card G / 2 ^ (padicValNat 2 (Fintype.card G) - t) := by
  classical
  let r := Fintype.card G
  have hr : r ≠ 0 := Fintype.card_ne_zero
  let e := r / 2 ^ (padicValNat 2 r - t)
  have hediv : e ∣ r := Nat.div_dvd_of_dvd
    ((padicValNat_dvd_iff_le hr).mpr (Nat.sub_le _ _))
  have heq : ∀ x : G, padicValNat 2 (orderOf x) ≤ t ↔ x ∈ (powMonoidHom e : G →* G).ker := by
    intro x
    rw [level_le_iff_dvd_cutoff hr (show orderOf x ∣ r from orderOf_dvd_card)]
    exact orderOf_dvd_iff_pow_eq_one
  let E : {x : G // padicValNat 2 (orderOf x) ≤ t} ≃ (powMonoidHom e : G →* G).ker :=
    Equiv.subtypeEquivRight heq
  change Fintype.card _ = e
  rw [Fintype.card_congr E, ← Nat.card_eq_fintype_card, IsCyclic.card_powMonoidHom_ker]
  rw [Nat.card_eq_fintype_card]
  exact Nat.gcd_eq_right hediv

/-- Fibers are obtained by differencing two consecutive cumulative counts. -/
theorem levelCount_eq_cumulative (G : Type*) [Group G] [Fintype G] (t : ℕ) :
    levelCount G t = if t = 0 then cumulativeLevelCount G 0
      else cumulativeLevelCount G t - cumulativeLevelCount G (t - 1) := by
  classical
  by_cases ht : t = 0
  · subst t
    simp [levelCount, cumulativeLevelCount]
  · have hpartition : (Finset.univ.filter (fun x : G => padicValNat 2 (orderOf x) ≤ t)) =
        (Finset.univ.filter (fun x : G => padicValNat 2 (orderOf x) = t)) ∪
        (Finset.univ.filter (fun x : G => padicValNat 2 (orderOf x) ≤ t - 1)) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      omega
    have hdis : Disjoint (Finset.univ.filter (fun x : G => padicValNat 2 (orderOf x) = t))
        (Finset.univ.filter (fun x : G => padicValNat 2 (orderOf x) ≤ t - 1)) := by
      rw [Finset.disjoint_left]
      intro x hx hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
      omega
    simp only [levelCount, cumulativeLevelCount, ht, ↓reduceIte, Fintype.card_subtype]
    rw [hpartition, Finset.card_union_of_disjoint hdis]
    omega

/-- Exact level counts use only cardinal arithmetic, powers of two and division. -/
theorem levelCount_cyclic (G : Type*) [CommGroup G] [Fintype G] [IsCyclic G] (t : ℕ) :
    levelCount G t = if t = 0 then
      Fintype.card G / 2 ^ padicValNat 2 (Fintype.card G)
    else Fintype.card G / 2 ^ (padicValNat 2 (Fintype.card G) - t) -
      Fintype.card G / 2 ^ (padicValNat 2 (Fintype.card G) - (t - 1)) := by
  rw [levelCount_eq_cumulative]
  simp only [cumulativeLevelCount_eq, Nat.sub_zero]

end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/LevelBounds.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring

lemma div_lower_power_two {r v t : ℕ} (hdiv : 2^v ∣ r) (ht : t ≤ v) :
    r / 2^(v-t) = 2^t * (r / 2^v) := by
  have hpow : 2^(v-t) * 2^t = 2^v := by rw [← pow_add, Nat.sub_add_cancel ht]
  calc
    r / 2^(v-t) = (2^(v-t) * (2^t * (r / 2^v))) / 2^(v-t) := by
      rw [← mul_assoc, hpow, Nat.mul_div_cancel' hdiv]
    _ = 2^t * (r / 2^v) := Nat.mul_div_right _ (by positivity)

/-- The traditional cyclic-group level law u, u, 2u, 4u, ... . -/
theorem levelCount_closed (G : Type*) [CommGroup G] [Fintype G] [IsCyclic G] (t : ℕ) :
    levelCount G t = if t = 0 then Fintype.card G / 2^padicValNat 2 (Fintype.card G)
      else if t ≤ padicValNat 2 (Fintype.card G) then
        2^(t-1) * (Fintype.card G / 2^padicValNat 2 (Fintype.card G)) else 0 := by
  have hr : Fintype.card G ≠ 0 := Fintype.card_ne_zero
  have hd : 2^padicValNat 2 (Fintype.card G) ∣ Fintype.card G :=
    (padicValNat_dvd_iff_le hr).mpr le_rfl
  rw [levelCount_cyclic]
  by_cases ht : t = 0
  · simp [ht]
  · simp only [ht, ↓reduceIte]
    by_cases htv : t ≤ padicValNat 2 (Fintype.card G)
    · rw [ite_eq_left htv, div_lower_power_two hd htv,
        div_lower_power_two hd (by omega : t-1 ≤ padicValNat 2 (Fintype.card G))]
      have he : t = (t-1)+1 := by omega
      nth_rw 1 [he]
      rw [pow_succ]
      have heq : 2 ^ (t-1) * 2 * (Fintype.card G / 2^padicValNat 2 (Fintype.card G)) =
          2 * (2^(t-1) * (Fintype.card G / 2^padicValNat 2 (Fintype.card G))) := by ring
      rw [heq]
      omega
    · have hv : padicValNat 2 (Fintype.card G) ≤ t-1 := by omega
      simp [htv, Nat.sub_eq_zero_of_le hv, Nat.sub_eq_zero_of_le (by omega :
        padicValNat 2 (Fintype.card G) ≤ t)]

/-- No particular level has more than half the elements of a cyclic group of
even order, including the lowest level and the unique top level. -/
theorem two_mul_levelCount_le (G : Type*) [CommGroup G] [Fintype G] [IsCyclic G]
    (heven : 2 ∣ Fintype.card G) (t : ℕ) : 2 * levelCount G t ≤ Fintype.card G := by
  have hr : Fintype.card G ≠ 0 := Fintype.card_ne_zero
  have hv : 1 ≤ padicValNat 2 (Fintype.card G) := by
    apply (padicValNat_dvd_iff_le hr).mp
    simpa using heven
  have hd : 2^padicValNat 2 (Fintype.card G) ∣ Fintype.card G :=
    (padicValNat_dvd_iff_le hr).mpr le_rfl
  have hrw : 2^padicValNat 2 (Fintype.card G) *
      (Fintype.card G / 2^padicValNat 2 (Fintype.card G)) = Fintype.card G :=
    Nat.mul_div_cancel' hd
  rw [levelCount_closed]
  by_cases ht : t = 0
  · rw [ite_eq_left ht]
    calc
      _ ≤ 2^padicValNat 2 (Fintype.card G) *
          (Fintype.card G / 2^padicValNat 2 (Fintype.card G)) :=
        Nat.mul_le_mul_right _ (by simpa using Nat.pow_le_pow_right (by omega : 0 < 2) hv)
      _ = _ := hrw
  · rw [ite_eq_right ht]
    by_cases htv : t ≤ padicValNat 2 (Fintype.card G)
    · rw [ite_eq_left htv, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ t)]
      calc
        _ ≤ 2^padicValNat 2 (Fintype.card G) *
            (Fintype.card G / 2^padicValNat 2 (Fintype.card G)) :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega : 0 < 2) htv)
        _ = _ := hrw
    · simp [htv]

end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/PrimePowerLevels.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring

/-- A closed integer expression; no enumeration of residue classes. -/
def primePowerUnitCount (p e : ℕ) : ℕ := (p-1) * p^(e-1)

def closedLevelCount (R t : ℕ) : ℕ :=
  if t = 0 then R / 2^padicValNat 2 R
  else if t ≤ padicValNat 2 R then 2^(t-1) * (R / 2^padicValNat 2 R) else 0

noncomputable def primePowerLevelCard (p e t : ℕ) : ℕ :=
  Nat.card {x : (ZMod (p^e))ˣ // padicValNat 2 (orderOf x) = t}

/-- Exact prime-power level counts from the already fully proved cyclicity of
odd prime-power unit groups in Mathlib. -/
theorem primePowerLevelCard_eq {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (he : 0 < e) (t : ℕ) :
    primePowerLevelCard p e t = closedLevelCount (primePowerUnitCount p e) t := by
  let : NeZero p := ⟨hp.ne_zero⟩
  let : IsCyclic (ZMod (p^e))ˣ := ZMod.isCyclic_units_of_prime_pow p hp hp2 e
  have hc : Fintype.card (ZMod (p^e))ˣ = primePowerUnitCount p e := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime_pow hp he]
    simp [primePowerUnitCount, mul_comm]
  classical
  change Nat.card {x : (ZMod (p^e))ˣ // padicValNat 2 (orderOf x) = t} = _
  rw [Nat.card_eq_fintype_card]
  change levelCount (ZMod (p^e))ˣ t = _
  rw [levelCount_closed, hc]
  rfl

theorem primePowerLevelCard_half {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (he : 0 < e) (t : ℕ) :
    2 * primePowerLevelCard p e t ≤ primePowerUnitCount p e := by
  let : NeZero p := ⟨hp.ne_zero⟩
  let : IsCyclic (ZMod (p^e))ˣ := ZMod.isCyclic_units_of_prime_pow p hp hp2 e
  have hc : Fintype.card (ZMod (p^e))ˣ = primePowerUnitCount p e := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime_pow hp he]
    simp [primePowerUnitCount, mul_comm]
  have hpe : 2 < p^e := by
    have hp3 : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp2)
    exact hp3.trans_le (Nat.le_pow he)
  have heven : 2 ∣ Fintype.card (ZMod (p^e))ˣ := by
    rw [ZMod.card_units_eq_totient]
    exact even_iff_two_dvd.mp (Nat.totient_even hpe)
  classical
  have hh := two_mul_levelCount_le (ZMod (p^e))ˣ heven t
  rw [hc] at hh
  simpa only [primePowerLevelCard, Nat.card_eq_fintype_card, levelCount] using hh

end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/CRTLevels.lean =====
namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


open scoped BigOperators
namespace ExactQuantumFactoring

abbrev Component (m : ℕ) := {p : ℕ // p ∈ m.primeFactors}

instance componentNeZero (m : ℕ) (p : Component m) :
    NeZero (p.val ^ m.factorization p.val) :=
  ⟨pow_ne_zero _ (Nat.mem_primeFactors.mp p.property).1.ne_zero⟩

abbrev ComponentUnits (m : ℕ) (p : Component m) :=
  (ZMod (p.val ^ m.factorization p.val))ˣ

noncomputable def unitCRT (m : ℕ) (hm : m ≠ 0) :
    (ZMod m)ˣ ≃* (∀ p : Component m, ComponentUnits m p) :=
  (Units.mapEquiv (ZMod.equivPi m hm).toMulEquiv).trans MulEquiv.piUnits

lemma component_order_level_lt {m n : ℕ} (hm : m ≠ 0) (hmn : m < 2^n)
    (p : Component m) (a : ComponentUnits m p) : padicValNat 2 (orderOf a) < n := by
  have ho : 0 < orderOf a := orderOf_pos a
  have hpow : 2^padicValNat 2 (orderOf a) ≤ orderOf a := Nat.le_of_dvd ho pow_padicValNat_dvd
  have hcard : Nat.card (ComponentUnits m p) = (p.val ^ m.factorization p.val).totient := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  apply (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp
  calc
    _ ≤ orderOf a := hpow
    _ ≤ Nat.card (ComponentUnits m p) := orderOf_le_card
    _ = _ := hcard
    _ ≤ p.val ^ m.factorization p.val := Nat.totient_le _
    _ ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm) (Nat.ordProj_dvd _ _)
    _ < 2^n := hmn

noncomputable def componentLevel {m n : ℕ} (hm : m ≠ 0) (hmn : m < 2^n)
    (p : Component m) (a : ComponentUnits m p) : Fin (n+1) :=
  ⟨padicValNat 2 (orderOf a), by have := component_order_level_lt hm hmn p a; omega⟩

lemma componentLevel_card {m n : ℕ} (hm : m ≠ 0) (hmn : m < 2^n)
    (p : Component m) (t : Fin (n+1)) :
    Fintype.card {a : ComponentUnits m p // componentLevel hm hmn p a = t} =
      primePowerLevelCard p.val (m.factorization p.val) t.val := by
  classical
  rw [primePowerLevelCard, Nat.card_eq_fintype_card]
  apply Fintype.card_congr
  exact Equiv.subtypeEquivRight (fun a => Fin.ext_iff)

/-- Closed form for the number of favorable unit residues. Only n+1 levels
and the prime-power factors occur; there is no modulo-m residue enumeration. -/
def favorableCount (m n : ℕ) : ℕ :=
  m.totient - ∑ t : Fin (n+1), ∏ p : Component m,
    closedLevelCount (primePowerUnitCount p.val (m.factorization p.val)) t.val

noncomputable def FavorableUnit {m n : ℕ} (hm : m ≠ 0) (hmn : m < 2^n)
    (p₀ : Component m) (a : (ZMod m)ˣ) : Prop :=
  ¬ ∀ p, componentLevel hm hmn p (unitCRT m hm a p) =
    componentLevel hm hmn p₀ (unitCRT m hm a p₀)

lemma equal_component_card {m n : ℕ} (hm : m ≠ 0) (hmn : m < 2^n)
    (hodd : Odd m) (p₀ : Component m) :
    Fintype.card {a : ∀ p : Component m, ComponentUnits m p //
      ∀ p, componentLevel hm hmn p (a p) = componentLevel hm hmn p₀ (a p₀)} =
    ∑ t : Fin (n+1), ∏ p : Component m,
      closedLevelCount (primePowerUnitCount p.val (m.factorization p.val)) t.val := by
  classical
  rw [allEqualLevel_card p₀]
  apply Finset.sum_congr rfl
  intro t ht
  apply Finset.prod_congr rfl
  intro p hp
  rw [componentLevel_card]
  have pp := Nat.mem_primeFactors.mp p.property
  exact primePowerLevelCard_eq pp.1 (by
    intro h
    apply (Nat.not_even_iff_odd.mpr hodd)
    exact even_iff_two_dvd.mpr (h ▸ pp.2.1))
    (pp.1.factorization_pos_of_dvd hm pp.2.1) _

/-- The exact source F is the cardinality of the actual CRT favorable event. -/
theorem favorableCount_eq_card {m n : ℕ} (hm : m ≠ 0) (hmn : m < 2^n)
    (hodd : Odd m) (p₀ : Component m) :
    favorableCount m n = Nat.card {a : (ZMod m)ˣ // FavorableUnit hm hmn p₀ a} := by
  classical
  let : NeZero m := ⟨hm⟩
  rw [Nat.card_eq_fintype_card]
  unfold FavorableUnit
  rw [Fintype.card_subtype_compl, ZMod.card_units_eq_totient]
  unfold favorableCount
  congr 1
  rw [← equal_component_card hm hmn hodd p₀]
  exact (Fintype.card_congr ((unitCRT m hm).toEquiv.subtypeEquiv (fun _ => Iff.rfl))).symm

/-- At least half the units are favorable whenever there are two distinct
odd prime-power components, exactly as in Section 5. -/
theorem totient_le_twice_favorableCount {m n : ℕ} (hm : m ≠ 0) (hmn : m < 2^n)
    (hodd : Odd m) (p₀ p₁ : Component m) (hne : p₁ ≠ p₀) :
    m.totient ≤ 2 * favorableCount m n := by
  classical
  let : NeZero m := ⟨hm⟩
  have hhalf := twice_allEqualLevel_card_le p₀ p₁ hne (componentLevel hm hmn) (by
    intro t
    rw [componentLevel_card]
    have pp := Nat.mem_primeFactors.mp p₀.property
    have hpp := primePowerLevelCard_half pp.1 (by
      intro h
      apply (Nat.not_even_iff_odd.mpr hodd)
      exact even_iff_two_dvd.mpr (h ▸ pp.2.1))
      (pp.1.factorization_pos_of_dvd hm pp.2.1) t.val
    rw [ZMod.card_units_eq_totient, Nat.totient_prime_pow pp.1
      (pp.1.factorization_pos_of_dvd hm pp.2.1)]
    simpa only [primePowerUnitCount, mul_comm] using hpp)
  rw [equal_component_card hm hmn hodd p₀] at hhalf
  have hc : Fintype.card (∀ p : Component m, ComponentUnits m p) = m.totient := by
    rw [← Fintype.card_congr (unitCRT m hm).toEquiv, ZMod.card_units_eq_totient]
  rw [hc] at hhalf
  unfold favorableCount
  omega

end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/ArithmeticBounds.lean =====
namespace OAI

section
open scoped BigOperators


open scoped BigOperators
namespace ExactQuantumFactoring

/-- The telescoping estimate for any distinct integers at least two. -/
theorem prod_le_card_mul_pred_prod (s : Finset ℕ) (hs : ∀ p ∈ s, 2 ≤ p) :
    (∏ p ∈ s, p) ≤ (s.card + 1) * ∏ p ∈ s, (p - 1) := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a s hmax ih =>
    have ha : a ∉ s := fun h => (lt_irrefl a) (hmax a h)
    have ha2 : 2 ≤ a := hs a (Finset.mem_insert_self _ _)
    have hs2 : ∀ p ∈ s, 2 ≤ p := fun p hp => hs p (Finset.mem_insert_of_mem hp)
    have hc : s.card + 2 ≤ a := by
      have hass : s ⊆ Finset.Ico 2 a := fun p hp => Finset.mem_Ico.mpr ⟨hs2 p hp, hmax p hp⟩
      have := Finset.card_le_card hass
      rw [Nat.card_Ico] at this
      omega
    have hstep : a * (s.card + 1) ≤ (s.card + 2) * (a - 1) := by
      have : a - 1 + 1 = a := by omega
      nlinarith
    simp only [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    calc
      a * ∏ p ∈ s, p ≤ a * ((s.card + 1) * ∏ p ∈ s, (p - 1)) :=
        Nat.mul_le_mul_left _ (ih hs2)
      _ ≤ (s.card + 1 + 1) * (a - 1) * ∏ p ∈ s, (p - 1) := by
        simpa [Nat.mul_assoc] using Nat.mul_le_mul_right (∏ p ∈ s, (p - 1)) hstep
      _ = (s.card + 1 + 1) * ((a - 1) * ∏ p ∈ s, (p - 1)) := by ring

/-- The number of distinct prime factors is less than a strict binary cutoff. -/
theorem primeFactors_card_lt {d n : ℕ} (hd : 0 < d) (hb : d < 2 ^ n) :
    d.primeFactors.card < n := by
  have hp : 2 ^ d.primeFactors.card ≤ ∏ p ∈ d.primeFactors, p := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod'
      (fun prime hprime => (Nat.prime_of_mem_primeFactors hprime).two_le)
  have hp' : (∏ p ∈ d.primeFactors, p) ≤ d :=
    Nat.le_of_dvd hd (Nat.prod_primeFactors_dvd d)
  exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp (hp.trans_lt (hp'.trans_lt hb))

/-- Integer form of (5.2), retaining the original global binary cutoff. -/
theorem le_succ_mul_totient {d n : ℕ} (hd : 0 < d) (hb : d < 2 ^ n) :
    d ≤ (n + 1) * Nat.totient d := by
  have hp := prod_le_card_mul_pred_prod d.primeFactors
    (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
  have hprodpos : 0 < ∏ p ∈ d.primeFactors, (p - 1) := by
    apply Finset.prod_pos
    intro p hp
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    omega
  have hx := Nat.mul_le_mul_left (Nat.totient d) hp
  rw [Nat.totient_mul_prod_primeFactors] at hx
  have hbase : d ≤ (d.primeFactors.card + 1) * Nat.totient d := by
    apply Nat.le_of_mul_le_mul_right (c := ∏ p ∈ d.primeFactors, (p - 1)) _ hprodpos
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hx
  exact hbase.trans (Nat.mul_le_mul_right _ (by have := primeFactors_card_lt hd hb; omega))

/-- Real ratio version, ready for the exact transition-probability bound. -/
theorem totient_ratio_lower {d n : ℕ} (hd : 0 < d) (hb : d < 2 ^ n) :
    1 / ((n : ℝ) + 1) ≤ (Nat.totient d : ℝ) / d := by
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hd' : 0 < (d : ℝ) := by exact_mod_cast hd
  rw [div_le_div_iff₀ hn hd']
  norm_num only [one_mul]
  exact_mod_cast (le_succ_mul_totient hd hb).trans_eq (Nat.mul_comm _ _)

end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/ContinuedFractionRecovery.lean =====
namespace OAI

section
open scoped BigOperators


/-! Bounded Euclidean recovery of the manuscript's nearest-bin labels.
The denominator bound is logarithmic, never a search through B labels. -/
namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators

/-- Euclid's finite convergent recurrence, entirely natural/rational arithmetic. -/
def euclidConvergent (a b : ℕ) : ℕ → ℚ
  | 0 => (a/b:ℕ)
  | k+1 => (a/b:ℕ)+(euclidConvergent b (a%b) k)⁻¹

lemma euclidConvergent_zero_pair (k : ℕ) : ∀ b,
    euclidConvergent 0 b k=0 ∧ euclidConvergent b 0 k=0 := by
  induction k with
  | zero => intro b; simp [euclidConvergent]
  | succ k ih =>
    intro b
    constructor <;> simp [euclidConvergent,(ih b).1,(ih b).2]

lemma euclidConvergent_zero_left (b k : ℕ) : euclidConvergent 0 b k=0 :=
  (euclidConvergent_zero_pair k b).1

lemma euclidConvergent_zero_right (a k : ℕ) : euclidConvergent a 0 k=0 :=
  (euclidConvergent_zero_pair k a).2

lemma real_floor_ratio (a b : ℕ) : ⌊(a:ℝ)/b⌋ = ((a/b:ℕ):ℤ) := by
  have hf := Rat.floor_cast (α:=ℝ) ((a:ℚ)/b)
  simp only [Rat.cast_div,Rat.cast_natCast] at hf
  rw [hf,Rat.floor_natCast_div_natCast]
  norm_cast

lemma euclidConvergent_real (a b k : ℕ) :
    euclidConvergent a b k = Real.convergent ((a:ℝ)/b) k := by
  induction k generalizing a b with
  | zero =>
    simp only [euclidConvergent,Real.convergent_zero,real_floor_ratio]
    norm_cast
  | succ k ih =>
    rw [euclidConvergent,Real.convergent_succ,real_floor_ratio,
      Int.fract_div_natCast_eq_div_natCast_mod,inv_div,← ih]
    congr 1

lemma ratio_euclid (a b : ℕ) :
    (a:ℚ)/b = (a/b:ℕ)+((b:ℚ)/((a%b:ℕ):ℚ))⁻¹ := by
  have h := Int.floor_add_fract ((a:ℚ)/b)
  rw [Rat.floor_natCast_div_natCast,Int.fract_div_natCast_eq_div_natCast_mod] at h
  simpa only [Int.cast_natCast,← Int.natCast_ediv,inv_div] using h.symm

/-- Two Euclidean steps halve the denominator; the zero remainder is treated
separately, since natural remainder by zero is not zero. -/
lemma euclid_two_halving {b r : ℕ} (hr : 0<r) (hrb : r<b) : 2*(b%r)<b := by
  by_cases h : 2*r ≤ b
  · have hm := Nat.mod_lt b hr
    omega
  · have hb : b<2*r := by omega
    have hmod : b%r=b-r := by
      apply Nat.mod_eq_sub_mod hrb.le |>.trans
      exact Nat.mod_eq_of_lt (by omega)
    rw [hmod]
    omega

/-- At most twice the denominator bit bound suffices, including rational
termination and all later convergents. -/
lemma euclidConvergent_terminal (s a b h : ℕ) (hb : b<2^s) :
    euclidConvergent a b (2*s+h) = (a:ℚ)/b := by
  induction s generalizing a b h with
  | zero =>
    have : b=0 := by simpa using hb
    subst b
    simp [euclidConvergent_zero_right]
  | succ s ih =>
    by_cases hb0 : b=0
    · subst b
      simp [euclidConvergent_zero_right]
    have hbpos : 0<b := Nat.pos_of_ne_zero hb0
    by_cases h0 : a%b=0
    · have he : 2*(s+1)+h = (2*s+h+1)+1 := by omega
      rw [he,euclidConvergent,h0,euclidConvergent_zero_right,inv_zero,add_zero]
      simpa [h0] using (ratio_euclid a b).symm
    · have hr : 0<a%b := Nat.pos_of_ne_zero h0
      have hh := euclid_two_halving hr (Nat.mod_lt a hbpos)
      have hb' : b%(a%b)<2^s := by
        rw [pow_succ] at hb
        omega
      have he : 2*(s+1)+h = (2*s+h+1)+1 := by omega
      rw [he,euclidConvergent,euclidConvergent,ih _ _ h hb']
      rw [← ratio_euclid b (a%b),← ratio_euclid a b]

/-- Every possible convergent is already in this polynomial-size list. -/
lemma euclidConvergent_bounded {s a b k : ℕ} (hb : b<2^s) :
    ∃ i ≤ 2*s, euclidConvergent a b k = euclidConvergent a b i := by
  by_cases hk : k≤2*s
  · exact ⟨k,hk,rfl⟩
  · refine ⟨2*s,le_rfl,?_⟩
    obtain ⟨h,rfl⟩ := Nat.exists_eq_add_of_le (le_of_not_ge hk)
    rw [euclidConvergent_terminal s a b h hb]
    simpa using (euclidConvergent_terminal s a b 0 hb).symm

lemma bin_error_div {Q d j : ℕ} (hd : 0<d) (hQ : 0<Q) :
    |(bin Q d j:ℝ)/Q-(j:ℝ)/d| ≤ 1/(2*(Q:ℝ)) := by
  have hQ' : (0:ℝ)<Q := by exact_mod_cast hQ
  have he : (bin Q d j:ℝ)/Q-(j:ℝ)/d = binError Q d j/(Q:ℝ) := by
    unfold binError
    field_simp
  rw [he,abs_div,abs_of_pos hQ',div_le_iff₀ hQ']
  have hh : 1/(2*(Q:ℝ))*(Q:ℝ)=1/2 := by field_simp
  rw [hh]
  exact binError_bound hd

/-- Legendre recovery with an explicit O(log Q) search bound. -/
lemma bin_has_bounded_convergent {Q d j s : ℕ}
    (hd : 0<d) (hQ : d^2<Q) (hsize : Q<2^s) (hcop : Nat.Coprime j d) :
    ∃ i ≤ 2*s, euclidConvergent (bin Q d j) Q i = (j:ℚ)/d := by
  have hdq : ((j:ℚ)/d).den=d := by
    have hh := Rat.den_div_eq_of_coprime (a:=(j:ℤ)) (b:=(d:ℤ))
      (by exact_mod_cast hd) (by simpa using hcop)
    apply Int.ofNat_inj.mp
    simpa only [Int.cast_natCast] using hh
  have hQ0 : 0<Q := lt_of_le_of_lt (Nat.zero_le _) hQ
  have ha := bin_error_div (j:=j) hd hQ0
  have hs : 1/(2*(Q:ℝ)) < 1/(2*(d:ℝ)^2) := by
    apply one_div_lt_one_div_of_lt
    · positivity
    · have hh : (d:ℝ)^2<(Q:ℝ) := by exact_mod_cast hQ
      linarith
  obtain ⟨k,hk⟩ := Real.exists_rat_eq_convergent
    (ξ:=(bin Q d j:ℝ)/Q) (q:=(j:ℚ)/d) (by
      simpa only [hdq,Rat.cast_div,Rat.cast_natCast] using ha.trans_lt hs)
  rw [← euclidConvergent_real] at hk
  obtain ⟨i,hi,hei⟩ := euclidConvergent_bounded (k:=k) hsize
  exact ⟨i,hi,hei.symm.trans hk.symm⟩


lemma bin_mul_bounds {Q d j : ℕ} (hd : 0<d) :
    2*bin Q d j*d ≤ 2*j*Q+d ∧ 2*j*Q ≤ 2*bin Q d j*d+d := by
  have h₁ : bin Q d j*(2*d) ≤ 2*j*Q+d := Nat.div_mul_le_self _ _
  have h₂ : 2*j*Q+d < (bin Q d j+1)*(2*d) := by
    have hr := Nat.mod_lt (2*j*Q+d) (by omega : 0<2*d)
    have he := Nat.mod_add_div (2*j*Q+d) (2*d)
    change (2*j*Q+d)%(2*d)+(2*d)*bin Q d j=2*j*Q+d at he
    nlinarith
  constructor <;> nlinarith

lemma bin_lt {Q d j : ℕ} (hd : 0<d) (hdQ : d≤Q) (hj : j<d) : bin Q d j<Q := by
  unfold bin
  apply (Nat.div_lt_iff_lt_mul (by omega : 0<2*d)).2
  have hh := Nat.mul_le_mul_right (2*Q) (show j+1≤d by omega)
  nlinarith

lemma same_bin_cross {Q d e j i : ℕ} (hd : 0<d) (he : 0<e)
    (hQ : d*e<Q) (hbin : bin Q d j=bin Q e i) : j*e=i*d := by
  obtain ⟨hd₁,hd₂⟩ := bin_mul_bounds (Q:=Q) (j:=j) hd
  obtain ⟨he₁,he₂⟩ := bin_mul_bounds (Q:=Q) (j:=i) he
  rw [← hbin] at he₁ he₂
  have hde₁ := Nat.mul_le_mul_right e hd₁
  have hde₂ := Nat.mul_le_mul_right e hd₂
  have hed₁ := Nat.mul_le_mul_right d he₁
  have hed₂ := Nat.mul_le_mul_right d he₂
  apply le_antisymm
  · by_contra hh
    have hh' : i*d+1≤j*e := by omega
    have hh'' := Nat.mul_le_mul_right (2*Q) hh'
    nlinarith
  · by_contra hh
    have hh' : j*e+1 ≤ i*d := by omega
    have hh'' := Nat.mul_le_mul_right (2*Q) hh'
    nlinarith

lemma same_bin_unique {Q d e j i : ℕ} (hd : 0<d) (he : 0<e)
    (hQ : d*e<Q) (hj : Nat.Coprime j d) (hi : Nat.Coprime i e)
    (hbin : bin Q d j=bin Q e i) : d=e ∧ j=i := by
  have hc := same_bin_cross hd he hQ hbin
  have heq : (j:ℚ)/d=(i:ℚ)/e := by
    apply (div_eq_div_iff (by positivity : (d:ℚ)≠0) (by positivity : (e:ℚ)≠0)).2
    exact_mod_cast hc
  have hh := Rat.div_int_inj (a:=(j:ℤ)) (b:=(d:ℤ)) (c:=(i:ℤ)) (d:=(e:ℤ))
    (by exact_mod_cast hd) (by exact_mod_cast he)
    (by simpa using hj) (by simpa using hi) (by simpa only [Int.cast_natCast] using heq)
  exact ⟨Int.ofNat_inj.mp hh.2,Int.ofNat_inj.mp hh.1⟩

/-- All label checks precede evaluation of any retention expression. -/
def IsBinLabel (Q B k : ℕ) (l : ℕ×ℕ) : Prop :=
  0<l.1 ∧ l.1<B ∧ l.2<l.1 ∧ Nat.Coprime l.2 l.1 ∧ bin Q l.1 l.2=k

instance (Q B k : ℕ) (l : ℕ×ℕ) : Decidable (IsBinLabel Q B k l) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

def rationalLabel (q : ℚ) : ℕ×ℕ := (q.den,q.num.toNat)

lemma rationalLabel_reduced {d j : ℕ} (hd : 0<d) (hcop : Nat.Coprime j d) :
    rationalLabel ((j:ℚ)/d)=(d,j) := by
  have hn := Rat.num_div_eq_of_coprime (a:=(j:ℤ)) (b:=(d:ℤ))
    (by exact_mod_cast hd) (by simpa using hcop)
  have hd' := Rat.den_div_eq_of_coprime (a:=(j:ℤ)) (b:=(d:ℤ))
    (by exact_mod_cast hd) (by simpa using hcop)
  apply Prod.ext
  · apply Int.ofNat_inj.mp
    simpa only [rationalLabel,Int.cast_natCast] using hd'
  · simp only [rationalLabel,Int.cast_natCast] at hn ⊢
    rw [hn,Int.toNat_natCast]

/-- Search only the polynomially many Euclidean convergents. Rational labels
not satisfying the exact bin rule are rejected, not rounded into a candidate. -/
def recoveredLabels (s Q B k : ℕ) : List (ℕ×ℕ) :=
  ((List.range (2*s+1)).map (fun i => rationalLabel (euclidConvergent k Q i))).filter
    (fun l => decide (IsBinLabel Q B k l))

lemma mem_recoveredLabels {s Q B k : ℕ} {l : ℕ×ℕ} :
    l ∈ recoveredLabels s Q B k ↔
      IsBinLabel Q B k l ∧ ∃ i≤2*s, rationalLabel (euclidConvergent k Q i)=l := by
  simp only [recoveredLabels,List.mem_filter,List.mem_map,List.mem_range,decide_eq_true_eq]
  constructor
  · rintro ⟨⟨i,hi,he⟩,hl⟩
    exact ⟨hl,i,by omega,he⟩
  · rintro ⟨hl,i,hi,he⟩
    exact ⟨⟨i,by omega,he⟩,hl⟩

lemma recoveredLabels_complete {s Q B k d j : ℕ}
    (hQ : B^2≤Q) (hsize : Q<2^s) (hl : IsBinLabel Q B k (d,j)) :
    (d,j) ∈ recoveredLabels s Q B k := by
  obtain ⟨hd,hdB,hjd,hcop,hbin⟩ := hl
  have hdQ : d^2<Q := by nlinarith
  obtain ⟨i,hi,he⟩ := bin_has_bounded_convergent hd hdQ hsize hcop
  apply mem_recoveredLabels.mpr
  refine ⟨⟨hd,hdB,hjd,hcop,hbin⟩,i,hi,?_⟩
  rw [← hbin,he,rationalLabel_reduced hd hcop]

lemma IsBinLabel.unique {Q B k : ℕ} {l r : ℕ×ℕ} (hQ : B^2≤Q)
    (hl : IsBinLabel Q B k l) (hr : IsBinLabel Q B k r) : l=r := by
  have hp : l.1*r.1<Q := by
    have h₁ := hl.2.1
    have h₂ := hr.2.1
    nlinarith [hl.1,hr.1]
  exact Prod.ext
    (same_bin_unique hl.1 hr.1 hp hl.2.2.2.1 hr.2.2.2.1
      (hl.2.2.2.2.trans hr.2.2.2.2.symm)).1
    (same_bin_unique hl.1 hr.1 hp hl.2.2.2.1 hr.2.2.2.1
      (hl.2.2.2.2.trans hr.2.2.2.2.symm)).2

/-- The operational decoder either returns the unique exact bin label or rejects. -/
def recoverLabel (s Q B k : ℕ) : Option (ℕ×ℕ) :=
  (recoveredLabels s Q B k).head?

lemma recoveredLabels_length (s Q B k : ℕ) :
    (recoveredLabels s Q B k).length ≤ 2*s+1 := by
  exact (List.length_filter_le _ _).trans_eq (by simp)

lemma recoverLabel_sound {s Q B k : ℕ} {l : ℕ×ℕ}
    (h : recoverLabel s Q B k=some l) : IsBinLabel Q B k l := by
  obtain ⟨ys,hy⟩ := List.head?_eq_some_iff.mp h
  have hm : l ∈ recoveredLabels s Q B k := by rw [hy]; simp
  exact (mem_recoveredLabels.mp hm).1

lemma recoverLabel_complete {s Q B k : ℕ} {l : ℕ×ℕ}
    (hQ : B^2≤Q) (hsize : Q<2^s) (hl : IsBinLabel Q B k l) :
    recoverLabel s Q B k=some l := by
  have hm := recoveredLabels_complete hQ hsize hl
  unfold recoverLabel
  cases he : recoveredLabels s Q B k with
  | nil => simp [he] at hm
  | cons r rs =>
    have hr : IsBinLabel Q B k r := (mem_recoveredLabels.mp (by rw [he]; simp)).1
    simpa only [List.head?_cons] using congrArg some (hr.unique hQ hl)

lemma recoverLabel_iff {s Q B k : ℕ} {l : ℕ×ℕ}
    (hQ : B^2≤Q) (hsize : Q<2^s) :
    recoverLabel s Q B k=some l ↔ IsBinLabel Q B k l :=
  ⟨recoverLabel_sound,recoverLabel_complete hQ hsize⟩

end ExactQuantumFactoring.OrderTrial


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/GcdCircuit.lean =====
namespace OAI

section
open scoped BigOperators


/-! Clocked Euclidean arithmetic, including zero operands.  The clock is
linear in bit width, and every step is an actual Boolean modular divider. -/
namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork

def euclidRun : ℕ → ℕ → ℕ → ℕ × ℕ
  | 0,a,b => (a,b)
  | k+1,a,b => if b=0 then (a,0) else euclidRun k b (a%b)

lemma euclidRun_zero (k a : ℕ) : euclidRun k a 0=(a,0) := by
  cases k <;> simp [euclidRun]

lemma euclidRun_terminal (s a b h : ℕ) (hb : b < 2^s) :
    euclidRun (2*s+h) a b=(Nat.gcd a b,0) := by
  induction s generalizing a b h with
  | zero =>
    have : b=0 := by simpa using hb
    subst b
    simp [euclidRun_zero]
  | succ s ih =>
    by_cases hb0 : b=0
    · subst b; simp [euclidRun_zero]
    have hbpos : 0 < b := Nat.pos_of_ne_zero hb0
    have he : 2*(s+1)+h=(2*s+h+1)+1 := by omega
    by_cases hr0 : a%b=0
    · rw [he,euclidRun,ite_eq_right hb0,hr0,euclidRun_zero]
      rw [Nat.gcd_comm a b,Nat.gcd_rec b a,hr0,Nat.gcd_zero_left]
    · have hr := Nat.pos_of_ne_zero hr0
      have hh := OrderTrial.euclid_two_halving hr (Nat.mod_lt a hbpos)
      have hb' : b%(a%b) < 2^s := by rw [pow_succ] at hb; omega
      rw [he,euclidRun,ite_eq_right hb0,euclidRun,ite_eq_right hr0,ih _ _ h hb']
      congr 1
      calc
        Nat.gcd (a%b) (b%(a%b)) = Nat.gcd b (a%b) := by
          rw [Nat.gcd_comm (a%b) (b%(a%b)),← Nat.gcd_rec (a%b) b,Nat.gcd_comm]
        _ = Nat.gcd a b := by rw [Nat.gcd_comm b (a%b),← Nat.gcd_rec b a,Nat.gcd_comm]

def euclidStep (w : ℕ) : BooleanNetwork (w+w) (w+w) :=
  let z := wordConstant (BitVec.ofNat w 0)
  let done := equalOn (rootGuess w) z
  (wordMux done (rootModulus w) (rootGuess w)).pair
    (wordMux done z (mod w))

def euclidPrefix (w : ℕ) : ℕ → BooleanNetwork (w+w) (w+w)
  | 0 => select id
  | k+1 => (euclidStep w).comp (euclidPrefix w k)

def gcdNet (w : ℕ) : BooleanNetwork (w+w) w :=
  (euclidPrefix w (2*w)).comp (rootModulus w)

lemma euclidStep_semantics (w : ℕ) (a b : Basis w) :
    ∃ a' b' : Basis w,
      (euclidStep w).eval (Fin.append a b)=Fin.append a' b' ∧
      (bitsValue a').toNat=(if (bitsValue b).toNat=0 then (bitsValue a).toNat else (bitsValue b).toNat) ∧
      (bitsValue b').toNat=(if (bitsValue b).toNat=0 then 0 else (bitsValue a).toNat%(bitsValue b).toNat) := by
  let z := (wordConstant (n:=w+w) (BitVec.ofNat w 0)).eval (Fin.append a b)
  have hz : (bitsValue z).toNat=0 := by simp [z,wordConstant_eval]
  have hc : (equalOn (rootGuess w) (wordConstant (BitVec.ofNat w 0))).eval (Fin.append a b) 0=true ↔
      (bitsValue b).toNat=0 := by
    rw [equalOn_value,rootGuess_eval,wordConstant_eval]
    simp
  by_cases hb : (bitsValue b).toNat=0
  · refine ⟨a,z,?_,by simp [hb],by simpa [hb] using hz⟩
    rw [euclidStep,eval_pair,wordMux_eval,wordMux_eval,ite_eq_left (hc.mpr hb),ite_eq_left (hc.mpr hb),rootModulus_eval]
  · refine ⟨b,(mod w).eval (Fin.append a b),?_,by simp [hb],?_⟩
    · rw [euclidStep,eval_pair,wordMux_eval,wordMux_eval,ite_eq_right (fun condition => hb (hc.mp condition)),ite_eq_right (fun condition => hb (hc.mp condition)),rootGuess_eval]
    · rw [mod_word,BitVec.toNat_umod,ite_eq_right hb]

lemma euclidPrefix_semantics (w k : ℕ) (a b : Basis w) :
    ∃ a' b' : Basis w,
      (euclidPrefix w k).eval (Fin.append a b)=Fin.append a' b' ∧
      ((bitsValue a').toNat,(bitsValue b').toNat)=euclidRun k (bitsValue a).toNat (bitsValue b).toNat := by
  induction k generalizing a b with
  | zero => exact ⟨a,b,rfl,rfl⟩
  | succ k ih =>
    obtain ⟨a₁,b₁,he,ha,hb⟩ := euclidStep_semantics w a b
    obtain ⟨a',b',he',hv⟩ := ih a₁ b₁
    refine ⟨a',b',by rw [euclidPrefix,eval_comp,he,he'],?_⟩
    rw [hv,ha,hb,euclidRun]
    split_ifs with hb0
    · exact euclidRun_zero k _
    · rfl

lemma gcdNet_value (w : ℕ) (a b : Basis w) :
    (bitsValue ((gcdNet w).eval (Fin.append a b))).toNat=
      Nat.gcd (bitsValue a).toNat (bitsValue b).toNat := by
  obtain ⟨a',b',he,hv⟩ := euclidPrefix_semantics w (2*w) a b
  have ht := euclidRun_terminal w (bitsValue a).toNat (bitsValue b).toNat 0 (bitsValue b).isLt
  rw [Nat.add_zero] at ht
  rw [ht] at hv
  rw [gcdNet,eval_comp,he,rootModulus_eval]
  exact congrArg Prod.fst hv

lemma euclidStep_count (w : ℕ) : (euclidStep w).net.count ≤ 216*w*w+300*w+100 := by
  have hc := equalOn_count (rootGuess w) (wordConstant (n:=w+w) (BitVec.ofNat w 0))
  simp only [rootGuess,count_select,wordConstant_count,zero_add] at hc
  have hm := mod_count w
  simp only [euclidStep,count_pair,wordMux_count,rootModulus,rootGuess,count_select,wordConstant_count]
  omega

lemma euclidPrefix_count (w k : ℕ) :
    (euclidPrefix w k).net.count ≤ k*(216*w*w+300*w+100) := by
  induction k with
  | zero => simp [euclidPrefix]
  | succ k ih =>
    rw [euclidPrefix,count_comp]
    have := euclidStep_count w
    rw [Nat.succ_mul]
    omega

lemma gcdNet_count (w : ℕ) : (gcdNet w).net.count ≤ 2*w*(216*w*w+300*w+100) := by
  simpa only [gcdNet,count_comp,rootModulus,count_select,add_zero] using euclidPrefix_count w (2*w)

end ExactQuantumFactoring.BitArithmetic


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/SplitCandidate.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic

def candidateDivisor (m a d : ℕ) : ℕ :=
  if 0 < d ∧ 2 ∣ d then Nat.gcd (a^(d/2)%m+m-1) m else 0

lemma halfOrderResidue_nat {m a : ℕ} (hm : 2 ≤ m) (u : (ZMod m)ˣ)
    (ha : (a : ZMod m)=(u : ZMod m)) :
    halfOrderResidue u=a^(orderOf u/2)%m := by
  let : NeZero m := ⟨by omega⟩
  simp only [halfOrderResidue,Units.val_pow_eq_pow_val,← ha,← Nat.cast_pow,ZMod.val_natCast]

lemma candidateDivisor_trueOrder {m a : ℕ} (hm : 2 ≤ m) (u : (ZMod m)ˣ)
    (ha : (a : ZMod m)=(u : ZMod m)) (heven : 2 ∣ orderOf u) :
    candidateDivisor m a (orderOf u)=splitGcd u := by
  let : NeZero m := ⟨by omega⟩
  rw [candidateDivisor,ite_eq_left ⟨orderOf_pos u,heven⟩,splitGcd,halfOrderResidue_nat hm u ha]

namespace BitArithmetic

def halfWord {k w : ℕ} (d : BooleanNetwork k w) : BooleanNetwork k w :=
  (d.pair (wordConstant (BitVec.ofNat w 2))).comp (div w)

lemma div_word (w : ℕ) (a b : Basis w) :
    bitsValue ((div w).eval (Fin.append a b))=bitsValue a/bitsValue b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [show (bitsValue ((div w).eval (Fin.append a b))).getLsbD i =
    (div w).eval (Fin.append a b) ⟨i,hi⟩ from bitsValue_bit _ ⟨i,hi⟩,
    div_correct,leftWord_append,rightWord_append]

lemma sub_word (w : ℕ) (a b : Basis w) :
    bitsValue ((sub w).eval (Fin.append a b))=bitsValue a-bitsValue b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [show (bitsValue ((sub w).eval (Fin.append a b))).getLsbD i =
    (sub w).eval (Fin.append a b) ⟨i,hi⟩ from bitsValue_bit _ ⟨i,hi⟩,
    sub_correct,leftWord_append,rightWord_append]

lemma halfWord_value {k w : ℕ} (hw : 2 ≤ w) (d : BooleanNetwork k w) (x : Basis k) :
    (bitsValue ((halfWord d).eval x)).toNat=(bitsValue (d.eval x)).toNat/2 := by
  have h2 : 2 < 2^w := (by norm_num : 2 < 2^2).trans_le (Nat.pow_le_pow_right (by decide) hw)
  rw [halfWord,eval_comp,eval_pair,div_word,wordConstant_eval,BitVec.toNat_udiv,
    BitVec.toNat_ofNat,Nat.mod_eq_of_lt h2]

/-- The repeated-squaring exponent is wired most-significant bit first. -/
def halfPower {k w : ℕ} (a m d : BooleanNetwork k w) : BooleanNetwork k w :=
  ((a.pair m).pair ((halfWord d).rewire Fin.rev)).comp (modularPower w w)

lemma halfPower_value {k w : ℕ} (hw : 2 ≤ w) (a m d : BooleanNetwork k w)
    (x : Basis k) (hm : 2 ≤ (bitsValue (m.eval x)).toNat) :
    (bitsValue ((halfPower a m d).eval x)).toNat=
      (bitsValue (a.eval x)).toNat^((bitsValue (d.eval x)).toNat/2)%(bitsValue (m.eval x)).toNat := by
  let eb := ((halfWord d).rewire Fin.rev).eval x
  have he : horner eb w le_rfl=(bitsValue (d.eval x)).toNat/2 := by
    rw [horner_full,Triangular.inputNumber_reverse]
    have hh : reverseBits w eb=(halfWord d).eval x := by
      funext i
      simp [reverseBits,eb,eval_rewire]
    rw [hh,halfWord_value hw]
  rw [halfPower,eval_comp,eval_pair,eval_pair,modularPower_value _ _ _ hm,he]

def shiftedHalfPower {k w : ℕ} (a m d : BooleanNetwork k w) : BooleanNetwork k w :=
  ((((halfPower a m d).pair m).comp (add w)).pair
    (wordConstant (BitVec.ofNat w 1))).comp (sub w)

lemma shiftedHalfPower_value {k w n : ℕ} (hwn : w=n+1) (hw : 2 ≤ w)
    (a m d : BooleanNetwork k w) (x : Basis k)
    (hm : 2 ≤ (bitsValue (m.eval x)).toNat) (hmb : (bitsValue (m.eval x)).toNat < 2^n) :
    (bitsValue ((shiftedHalfPower a m d).eval x)).toNat=
      (bitsValue (a.eval x)).toNat^((bitsValue (d.eval x)).toNat/2)%
        (bitsValue (m.eval x)).toNat+(bitsValue (m.eval x)).toNat-1 := by
  have hp := Nat.mod_lt ((bitsValue (a.eval x)).toNat^((bitsValue (d.eval x)).toNat/2)) (by omega : 0 < (bitsValue (m.eval x)).toNat)
  have hsum : (bitsValue (a.eval x)).toNat^((bitsValue (d.eval x)).toNat/2)%
      (bitsValue (m.eval x)).toNat+(bitsValue (m.eval x)).toNat < 2^w := by
    have he : 2^w=2^n*2 := by rw [hwn,pow_succ]
    rw [he]
    omega
  have h1 : 1 < 2^w := Nat.one_lt_two_pow (by omega)
  rw [shiftedHalfPower,eval_comp,eval_pair,sub_word,eval_comp,eval_pair,add_word,
    wordConstant_eval,BitVec.toNat_sub,BitVec.toNat_add,halfPower_value hw _ _ _ _ hm,
    Nat.mod_eq_of_lt hsum,BitVec.toNat_ofNat,Nat.mod_eq_of_lt h1]
  let v := (bitsValue (a.eval x)).toNat^((bitsValue (d.eval x)).toNat/2)%
    (bitsValue (m.eval x)).toNat
  let M := (bitsValue (m.eval x)).toNat
  change (2^w-1+(v+M))%2^w=v+M-1
  have he : 2^w-1+(v+M)=2^w+(v+M-1) := by dsimp [v,M]; omega
  rw [he,Nat.add_mod,Nat.mod_self,zero_add,Nat.mod_mod,Nat.mod_eq_of_lt (by dsimp [v,M]; omega)]

def splitRawOn {k w : ℕ} (a m d : BooleanNetwork k w) : BooleanNetwork k w :=
  ((shiftedHalfPower a m d).pair m).comp (gcdNet w)

lemma splitRawOn_value {k w n : ℕ} (hwn : w=n+1) (hw : 2 ≤ w)
    (a m d : BooleanNetwork k w) (x : Basis k)
    (hm : 2 ≤ (bitsValue (m.eval x)).toNat) (hmb : (bitsValue (m.eval x)).toNat < 2^n) :
    (bitsValue ((splitRawOn a m d).eval x)).toNat=
      Nat.gcd ((bitsValue (a.eval x)).toNat^((bitsValue (d.eval x)).toNat/2)%
        (bitsValue (m.eval x)).toNat+(bitsValue (m.eval x)).toNat-1) (bitsValue (m.eval x)).toNat := by
  rw [splitRawOn,eval_comp,eval_pair,gcdNet_value,shiftedHalfPower_value hwn hw _ _ _ _ hm hmb]

end BitArithmetic
end ExactQuantumFactoring


end

end OAI


