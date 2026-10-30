-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P04
-- name    : QAlgorithms_Papers_Independent_Advance50_P04
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T08:18:23.23344+00:00
-- url     : https://prove2.me/theorems/368aec93-812b-4262-bec5-752ebea6fee3
-- title:
--   Definitions for Private and Quantum Capacities of More Capable and Less Noisy Quantum Channels
-- statement:
--   The objects the formalized statements of *Private and Quantum Capacities of More Capable and Less Noisy Quantum Channels* (arXiv:1110.5746) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `MixedEnsemble`: Section II, PDF p.2: a finite mixed ensemble, allowing zero probabilities. The normalization also rules out m=0; states remain normalized at zero weights.
--   - `privateValue`: Section II, PDF p.2: the SAME ensemble is used for receiver and complement.
--   - `coherentValue`: Section II, PDF p.2: coherent information on an unrestricted input density.
--   - `swapDilation`: Section II, PDF p.2: interchange B and E in the SAME dilation.
--   - `MoreCapable`: Definition 1, PDF p.3: zero quantum capacity of the complementary channel. This is not defined by a one-use or tensor ensemble inequality.
--   - `LessNoisy`: Definition 2, PDF p.3: zero PRIVATE capacity of the complementary channel.
--   - `PureDominance`: Equation (6), PDF p.3, for ONE channel: all normalized pure ensembles of length dim A. No orthogonality condition is imposed; zero weights allow padding.
--   - `MixedDominance`: Equation (7), PDF p.3, for ONE channel: arbitrary finite mixed ensembles.
--   - `CoherentConcave`: Proposition 3, PDF p.5: concavity on every finite density mixture, including zero weights. The average is computed, rather than supplied as an unrelated state.
--   - `DivergenceDominance`: Equation (8), PDF p.3, for ONE channel, including singular input/output states and infinite relative entropies. No subtraction of infinities occurs.
-- source:
--   Private and Quantum Capacities of More Capable and Less Noisy Quantum Channels, arXiv:1110.5746v3, https://arxiv.org/abs/1110.5746v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_ExtendedQuantumEntropy
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P13
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P48
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P01

/-!
Watanabe, arXiv:1110.5746v3. All locators are PDF pages.
Finite nonzero complex registers are arbitrary positive dimensions, not just qubits.
The accepted isometry and tensor-power definitions act on every operator.
Private capacity is the limit in (1), written directly on lengths n+1.
Quantum capacity reuses the accepted positive-block coherent-information
regularization; superadditivity makes its supremum equal the limit in (2).
Both allow arbitrary mixed joint inputs on finite memoryless channels.
Compilation and independent moderation are pending the batch handoff.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P04

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal
open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel dilationPower
    maximumCoherentInformation IsDegradable)
open QAlgorithms.Papers.Independent.Support50.P01 (ConjugateDegradable)
open QAlgorithms.Papers.Independent.Information100.P56 (average)
open QAlgorithms.Papers.Independent.Dependency50.P48
  (holevoInformation privateMaximum regularizedCoherentInformation)
open QAlgorithms.Papers.Independent.Dependency50.P13 (finiteRelativeEntropy)

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

variable {A B E : Type*}
variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
variable [Fintype E] [DecidableEq E]

/-- Section II, PDF p.2: a finite mixed ensemble, allowing zero probabilities.
The normalization also rules out m=0; states remain normalized at zero weights. -/
structure MixedEnsemble (I : Type*) [Fintype I] (m : ℕ) where
  weight : Fin m → ℝ
  nonnegative : ∀ i, 0 ≤ weight i
  total : ∑ i, weight i = 1
  state : Fin m → Matrix I I ℂ
  density : ∀ i, IsDensityMatrix (state i)

/-- Section II, PDF p.2: the SAME ensemble is used for receiver and complement. -/
def privateValue (U : Matrix (B × E) A ℂ) {m : ℕ}
    (ens : MixedEnsemble A m) : ℝ :=
  holevoInformation ens.weight (fun i => receiverChannel U (ens.state i)) -
    holevoInformation ens.weight (fun i => complementaryChannel U (ens.state i))

/-- Section II, PDF p.2: coherent information on an unrestricted input density. -/
def coherentValue (U : Matrix (B × E) A ℂ) (rho : Matrix A A ℂ) : ℝ :=
  vnEntropy (receiverChannel U rho) - vnEntropy (complementaryChannel U rho)

/-- Section II, PDF p.2: interchange B and E in the SAME dilation. -/
def swapDilation (U : Matrix (B × E) A ℂ) : Matrix (E × B) A ℂ :=
  fun eb a => U (eb.2, eb.1) a

/-- Definition 1, PDF p.3: zero quantum capacity of the complementary channel.
This is not defined by a one-use or tensor ensemble inequality. -/
def MoreCapable (U : Matrix (B × E) A ℂ) : Prop :=
  regularizedCoherentInformation (swapDilation U) = 0

/-- Definition 2, PDF p.3: zero PRIVATE capacity of the complementary channel. -/
def LessNoisy (U : Matrix (B × E) A ℂ) : Prop :=
  (Filter.limUnder Filter.atTop (fun n : ℕ =>
      privateMaximum (dilationPower (swapDilation U) (n + 1)) / ((n + 1 : ℕ) : ℝ))) = 0

/-- Equation (6), PDF p.3, for ONE channel: all normalized pure ensembles of
length dim A. No orthogonality condition is imposed; zero weights allow padding. -/
def PureDominance (U : Matrix (B × E) A ℂ) : Prop :=
  ∀ p : Fin (Fintype.card A) → ℝ,
    ∀ psi : Fin (Fintype.card A) → EuclideanSpace ℂ A,
      (∀ i, 0 ≤ p i) → (∑ i, p i = 1) → (∀ i, ‖psi i‖ = 1) →
        holevoInformation p (fun i => complementaryChannel U (pureDensity (psi i))) ≤
        holevoInformation p (fun i => receiverChannel U (pureDensity (psi i)))

/-- Equation (7), PDF p.3, for ONE channel: arbitrary finite mixed ensembles. -/
def MixedDominance (U : Matrix (B × E) A ℂ) : Prop :=
  ∀ m : ℕ, ∀ ens : MixedEnsemble A m,
    holevoInformation ens.weight (fun i => complementaryChannel U (ens.state i)) ≤
      holevoInformation ens.weight (fun i => receiverChannel U (ens.state i))

/-- Proposition 3, PDF p.5: concavity on every finite density mixture, including
zero weights. The average is computed, rather than supplied as an unrelated state. -/
def CoherentConcave (U : Matrix (B × E) A ℂ) : Prop :=
  ∀ m : ℕ, ∀ ens : MixedEnsemble A m,
    (∑ i, ens.weight i * coherentValue U (ens.state i)) ≤
      coherentValue U (average ens.state ens.weight)

/-- Equation (8), PDF p.3, for ONE channel, including singular input/output
states and infinite relative entropies. No subtraction of infinities occurs. -/
def DivergenceDominance (U : Matrix (B × E) A ℂ) : Prop :=
  ∀ rho sigma : Matrix A A ℂ,
    IsDensityMatrix rho → IsDensityMatrix sigma →
      finiteRelativeEntropy (complementaryChannel U rho) (complementaryChannel U sigma) ≤
        finiteRelativeEntropy (receiverChannel U rho) (receiverChannel U sigma)

/-! Sanity checks for the local definitions; no paper theorem is proved here. -/

/-- A singleton ensemble is its component, and its private information is zero. -/
example (rho : Matrix A A ℂ) (hr : IsDensityMatrix rho)
    (U : Matrix (B × E) A ℂ) :
    let ens : MixedEnsemble A 1 :=
      ⟨fun _ => 1, fun _ => zero_le_one, by simp, fun _ => rho, fun _ => hr⟩
    average ens.state ens.weight = rho ∧ privateValue U ens = 0 := by
  simp [average, privateValue, holevoInformation]

/-- A normalized empty ensemble cannot exist. -/
example (ens : MixedEnsemble A 0) : False := by
  have h := ens.total
  simp at h

/-- Swapping twice restores every coefficient, so the complement is fixed. -/
example (U : Matrix (B × E) A ℂ) : swapDilation (swapDilation U) = U := rfl

/-- Both class predicates use capacities of exactly the swapped dilation. -/
example (U : Matrix (B × E) A ℂ) :
    (MoreCapable U ↔ regularizedCoherentInformation (swapDilation U) = 0) ∧
    (LessNoisy U ↔ (Filter.limUnder Filter.atTop (fun n : ℕ =>
      privateMaximum (dilationPower (swapDilation U) (n + 1)) / ((n + 1 : ℕ) : ℝ))) = 0) := ⟨Iff.rfl, Iff.rfl⟩

/-- Coherent information uses receiver entropy minus complement entropy. -/
example (U : Matrix (B × E) A ℂ) (rho : Matrix A A ℂ) :
    coherentValue U rho = vnEntropy (receiverChannel U rho) -
      vnEntropy (complementaryChannel U rho) := rfl

/-- The frozen maximum optimizes this coherent value over all density matrices. -/
example (U : Matrix (B × E) A ℂ) :
    maximumCoherentInformation U =
      sSup {r | ∃ rho : Matrix A A ℂ, IsDensityMatrix rho ∧ r = coherentValue U rho} := rfl

/-- Pure-dominance hypotheses constrain norms, weights and cardinality explicitly. -/
example (U : Matrix (B × E) A ℂ) (h : PureDominance U)
    (p : Fin (Fintype.card A) → ℝ)
    (psi : Fin (Fintype.card A) → EuclideanSpace ℂ A)
    (hp : ∀ i, 0 ≤ p i) (ht : ∑ i, p i = 1) (hn : ∀ i, ‖psi i‖ = 1) :
    holevoInformation p (fun i => complementaryChannel U (pureDensity (psi i))) ≤
      holevoInformation p (fun i => receiverChannel U (pureDensity (psi i))) := h p psi hp ht hn

/-- The n=0 tensor is scalar one, and is excluded from capacity regularization. -/
example (U : Matrix (B × E) A ℂ) (be : (Fin 0 → B) × (Fin 0 → E))
    (x : Fin 0 → A) : dilationPower U 0 be x = 1 := by simp [dilationPower]

/-- The imported extended divergence retains infinity on support failure. -/
example (rho sigma : Matrix A A ℂ)
    (h : ¬ LinearMap.ker sigma.mulVecLin ≤ LinearMap.ker rho.mulVecLin) :
    finiteRelativeEntropy rho sigma = ⊤ := by
  simp [finiteRelativeEntropy, h]

/-- The one-dimensional normalized identity has zero relative entropy with itself. -/
example : finiteRelativeEntropy (1 : Matrix (Fin 1) (Fin 1) ℂ) 1 = 0 := by
  simp [finiteRelativeEntropy, qRelEntropy, cfc_one]

/-- Mixed dominance uses exactly the same ensemble for both output systems. -/
example (U : Matrix (B × E) A ℂ) (h : MixedDominance U)
    (m : ℕ) (ens : MixedEnsemble A m) :
    holevoInformation ens.weight (fun i => complementaryChannel U (ens.state i)) ≤
      holevoInformation ens.weight (fun i => receiverChannel U (ens.state i)) := h m ens

/-- Finite concavity evaluates the constructed average input. -/
example (U : Matrix (B × E) A ℂ) (h : CoherentConcave U)
    (m : ℕ) (ens : MixedEnsemble A m) :
    (∑ i, ens.weight i * coherentValue U (ens.state i)) ≤
      coherentValue U (average ens.state ens.weight) := h m ens

/-- Divergence dominance is an order comparison of extended values on states. -/
example (U : Matrix (B × E) A ℂ) (h : DivergenceDominance U)
    (rho sigma : Matrix A A ℂ) (hr : IsDensityMatrix rho) (hs : IsDensityMatrix sigma) :
    finiteRelativeEntropy (complementaryChannel U rho) (complementaryChannel U sigma) ≤
      finiteRelativeEntropy (receiverChannel U rho) (receiverChannel U sigma) := h rho sigma hr hs

/-- The imported quantum regularization uses all positive block lengths.
Its coherentMaximum is the purification expression for the same mixed-input
coherent information; no restriction to pure input matrices is imposed. -/
example (U : Matrix (B × E) A ℂ) :
    regularizedCoherentInformation U =
      sSup {r | ∃ n : ℕ, 0 < n ∧
        r = QAlgorithms.Papers.Independent.Dependency50.P48.coherentRate U n} := rfl

variable {a b e : ℕ}

end QAlgorithms.Papers.Independent.Advance50.P04


