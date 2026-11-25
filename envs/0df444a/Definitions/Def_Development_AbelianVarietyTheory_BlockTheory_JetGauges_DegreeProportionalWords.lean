-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_DegreeProportionalWords
-- name    : Development_AbelianVarietyTheory_BlockTheory_JetGauges_DegreeProportionalWords
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T02:38:24.60999+00:00
-- url     : https://prove2.me/theorems/3e0ffa00-a401-48ea-8d7d-bce6a4da60ce
-- title:
--   Degree Proportional Words
-- statement:
--   Definitions and structural lemmas for Degree Proportional Words, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/DegreeProportionalWords.lean

import Mathlib
import Definitions.Def_Formalism_FormalDegreeBessel_StatementDS
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped ENNReal
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.DegreeProportionalWords
open Formalism.QuantumDeterminants
def gam (n : ℕ) (H H' : ℝ) : ℝ := 2 * (n : ℝ) ^ ((3 : ℝ) / 2) * H * H'
def TermCount : Prop :=
  ∀ (n l : ℕ) (H H' : ℝ) (τ : Finset (Fin n) → ℂ) (ρ : Finset (Fin n) → ℝ),
    0 ≤ H → 0 ≤ H' →
    (∀ I : Finset (Fin n), I.card = l → ‖τ I‖ ≤ (H * H') ^ l) →
    (∀ I : Finset (Fin n), I.card = l → 0 < ρ I ∧ ρ I ≤ (Real.exp 1 * n) ^ l) →
    ∑ I ∈ powersetCard l (univ : Finset (Fin n)), ‖τ I * ((Real.sqrt (ρ I) : ℝ) : ℂ)‖ ≤ gam n H H' ^ l
def TermCountNorm : Prop :=
  ∀ (V : Type) [SeminormedAddCommGroup V] [NormedSpace ℂ V]
    (n l : ℕ) (H H' : ℝ) (τ : Finset (Fin n) → ℂ) (ρ : Finset (Fin n) → ℝ) (v : V) (w : Finset (Fin n) → V),
    0 ≤ H → 0 ≤ H' →
    (∀ I : Finset (Fin n), I.card = l → ‖τ I‖ ≤ (H * H') ^ l) →
    (∀ I : Finset (Fin n), I.card = l → 0 < ρ I ∧ ρ I ≤ (Real.exp 1 * n) ^ l) →
    (∀ I : Finset (Fin n), I.card = l → ‖w I‖ ≤ Real.sqrt (ρ I) * ‖v‖) →
    ‖∑ I ∈ powersetCard l (univ : Finset (Fin n)), τ I • w I‖ ≤ gam n H H' ^ l * ‖v‖
def IsGauge {A : Type} [AddCommGroup A] (N : A → ℝ) : Prop :=
  N 0 = 0 ∧ ∀ x y, N (x + y) ≤ N x + N y
def l1 {A : Type} (a : A →₀ ℂ) : ℝ := ∑ ν ∈ a.support, ‖a ν‖
def comb {A V : Type} [AddCommGroup A] [AddCommGroup V] [Module ℂ V] (j : A → V) (μ : A) (a : A →₀ ℂ) : V :=
  ∑ ν ∈ a.support, a ν • j (μ + ν)
def Expands {A V : Type} [AddCommGroup A] [AddCommGroup V] [Module ℂ V] (N M : A → ℝ) (j : A → V) (μ : A)
    (x : V) (s t B : ℝ) : Prop :=
  ∃ a : A →₀ ℂ, x = comb j μ a ∧ (∀ ν ∈ a.support, N ν ≤ s ∧ M ν ≤ t) ∧ l1 a ≤ B
def OneStep {A V ι : Type} [AddCommGroup A] [AddCommGroup V] [Module ℂ V] (N M : A → ℝ) (j : A → V)
    (D : ι → Module.End ℂ V) (w : ι → ℕ) (lam : A) (R Γ : ℝ) : Prop :=
  ∀ (i : ι) (μ : A), N (μ - lam) ≤ R → Expands N M j μ (D i (j μ)) (w i) 1 (Γ ^ w i)
def wordOp {V ι : Type} [AddCommGroup V] [Module ℂ V] (D : ι → Module.End ℂ V) (L : List ι) : Module.End ℂ V :=
  (L.map D).prod
def wordWt {ι : Type} (w : ι → ℕ) (L : List ι) : ℕ := (L.map w).sum
def Iteration : Prop :=
  ∀ (A V ι : Type) [AddCommGroup A] [AddCommGroup V] [Module ℂ V] (N M : A → ℝ) (j : A → V)
    (D : ι → Module.End ℂ V) (w : ι → ℕ) (lam : A) (R Γ : ℝ),
    IsGauge N → IsGauge M → 0 ≤ Γ → OneStep N M j D w lam R Γ →
    ∀ (L : List ι) (μ : A), N (μ - lam) + (wordWt w L : ℝ) ≤ R →
      Expands N M j μ (wordOp D L (j μ)) (wordWt w L) L.length (Γ ^ wordWt w L)
def IterationSum : Prop :=
  ∀ (A V ι : Type) [AddCommGroup A] [AddCommGroup V] [Module ℂ V] (N M : A → ℝ) (j : A → V)
    (D : ι → Module.End ℂ V) (w : ι → ℕ) (lam : A) (R Γ : ℝ),
    IsGauge N → IsGauge M → 0 ≤ Γ → OneStep N M j D w lam R Γ →
    ∀ (L : List ι) (μ : A) (c : A →₀ ℂ), (∀ ν ∈ c.support, N (μ + ν - lam) + (wordWt w L : ℝ) ≤ R) →
      ∃ c' : A →₀ ℂ, wordOp D L (comb j μ c) = comb j μ c' ∧
        (∀ ν' ∈ c'.support, ∃ ν ∈ c.support, N (ν' - ν) ≤ (wordWt w L : ℝ) ∧ M (ν' - ν) ≤ (L.length : ℝ)) ∧
        l1 c' ≤ Γ ^ wordWt w L * l1 c
def IterationGauge : Prop :=
  ∀ (A V ι : Type) [AddCommGroup A] [AddCommGroup V] [Module ℂ V] (N M : A → ℝ) (j : A → V)
    (D : ι → Module.End ℂ V) (w : ι → ℕ) (lam : A) (R Γ : ℝ) (p : V → ℝ≥0∞) (K : ℝ≥0∞),
    IsGauge N → IsGauge M → 0 ≤ Γ → OneStep N M j D w lam R Γ →
    (∀ x y, p (x + y) ≤ p x + p y) → (∀ (c : ℂ) (x : V), p (c • x) = ‖c‖ₑ * p x) →
    (∀ κ : A, N (κ - lam) ≤ R → p (j κ) ≤ K) →
    ∀ (L : List ι) (μ : A), N (μ - lam) + (wordWt w L : ℝ) ≤ R →
      p (wordOp D L (j μ)) ≤ ENNReal.ofReal (Γ ^ wordWt w L) * K
def RegInt {n : ℕ} (μ : Fin n → ℝ) : Prop :=
  Function.Injective μ ∧ ∀ a b, ∃ m : ℤ, μ a - μ b = (m : ℝ)
def GapTwo {n : ℕ} (μ : Fin n → ℝ) : Prop := ∀ a b, a ≠ b → 2 ≤ |μ a - μ b|
def eSet {n : ℕ} (I : Finset (Fin n)) : Fin n → ℝ := fun a => if a ∈ I then 1 else 0
def StepSize : Prop :=
  ∀ (n : ℕ) (μ : Fin n → ℝ) (s : Fin n), RegInt μ →
    (Function.Injective (μ + Pi.single s 1) →
      1 / (n : ℝ) ≤ fdegHC (μ + Pi.single s 1) / fdegHC μ ∧ fdegHC (μ + Pi.single s 1) / fdegHC μ ≤ n) ∧
    (Function.Injective (μ - Pi.single s 1) →
      1 / (n : ℝ) ≤ fdegHC (μ - Pi.single s 1) / fdegHC μ ∧ fdegHC (μ - Pi.single s 1) / fdegHC μ ≤ n)
def GapStepSize : Prop :=
  ∀ (n : ℕ) (μ : Fin n → ℝ) (s : Fin n), GapTwo μ →
    (GapTwo (μ + Pi.single s 1) →
      1 / (4 * (n : ℝ) ^ 2) ≤ fdegHC (μ + Pi.single s 1) / fdegHC μ ∧
        fdegHC (μ + Pi.single s 1) / fdegHC μ ≤ Real.exp 1 * n) ∧
    (GapTwo (μ - Pi.single s 1) →
      1 / (4 * (n : ℝ) ^ 2) ≤ fdegHC (μ - Pi.single s 1) / fdegHC μ ∧
        fdegHC (μ - Pi.single s 1) / fdegHC μ ≤ Real.exp 1 * n)
def GapSubsetSize : Prop :=
  ∀ (n : ℕ) (μ : Fin n → ℝ) (I : Finset (Fin n)),
    ((∀ J ⊆ I, GapTwo (μ + eSet J)) →
      (1 / (4 * (n : ℝ) ^ 2)) ^ I.card ≤ fdegHC (μ + eSet I) / fdegHC μ ∧
        fdegHC (μ + eSet I) / fdegHC μ ≤ (Real.exp 1 * n) ^ I.card) ∧
    ((∀ J ⊆ I, GapTwo (μ - eSet J)) →
      (1 / (4 * (n : ℝ) ^ 2)) ^ I.card ≤ fdegHC (μ - eSet I) / fdegHC μ ∧
        fdegHC (μ - eSet I) / fdegHC μ ≤ (Real.exp 1 * n) ^ I.card)
def StepIn {n : ℕ} (Q : Set (Fin n → ℝ)) (μ ν : Fin n → ℝ) : Prop :=
  μ ∈ Q ∧ ν ∈ Q ∧ ∃ s : Fin n, ν = μ + Pi.single s 1 ∨ ν = μ - Pi.single s 1
def DegreeProportional : Prop :=
  ∀ (n : ℕ) (P Q : Set (Fin n → ℝ)) (d : (Fin n → ℝ) → ℝ),
    (∀ μ ∈ Q, RegInt μ) → (∀ μ ∈ Q, 0 < d μ) →
    (∀ μ ∈ Q, ∀ s : Fin n, μ + Pi.single s 1 ∈ Q →
      d (μ + Pi.single s 1) / d μ = ∏ t ∈ univ.erase s, (μ s + 1 - μ t) / (μ s - μ t)) →
    P ⊆ Q → (∀ μ ∈ P, ∀ ν ∈ P, Relation.ReflTransGen (StepIn Q) μ ν) →
    ∃ c : ℝ, 0 < c ∧ ∀ μ ∈ P, d μ = c * fdegHC μ
def Statement : Prop :=
  TermCount ∧ TermCountNorm ∧ Iteration ∧ IterationSum ∧ IterationGauge ∧
    StepSize ∧ GapStepSize ∧ GapSubsetSize ∧ DegreeProportional
example {n : ℕ} (s : Fin n) : eSet {s} = Pi.single s 1 := by
  funext a
  by_cases h : a = s <;> simp [eSet, h]
example : OneStep (A := ℤ) (V := ℂˣ → ℂ) (ι := Unit) (fun k => |(k : ℝ)|) (fun k => |(k : ℝ)|)
    (fun k x => ((x ^ k : ℂˣ) : ℂ)) (fun _ => LinearMap.mulLeft ℂ (fun x : ℂˣ => (x : ℂ))) (fun _ => 1) 0 5 1 := by
  intro i μ _
  refine ⟨Finsupp.single 1 1, ?_, ?_, ?_⟩
  · funext x
    simp [comb, Finsupp.support_single_ne_zero, zpow_add₀, mul_comm]
  · intro ν hν
    rw [Finsupp.support_single_ne_zero _ one_ne_zero, mem_singleton] at hν
    simp [hν]
  · simp [l1, Finsupp.support_single_ne_zero]
end GlobalTheory.IndefiniteRowSideFullHecke.DegreeProportionalWords


