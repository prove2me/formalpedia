-- Prove2me | Definitions.Def_KelsoCrawford_CompStatics_Process
-- name    : KelsoCrawford_CompStatics_Process
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:19:12.053385+00:00
-- url     : https://prove2.me/theorems/2db0da79-f1e1-4a52-93b9-1b54e6350023
-- title:
--   Section 3 and Section 5 — salary-adjustment runs and new-firm starting state
-- statement:
--   A salary-adjustment run records every round's permitted salary for each worker–firm pair, each firm's offers, and the offer tentatively chosen by each worker. A rejected offer raises that pair's permitted salary by the positive unit $\delta$ in the next round. The other offers keep their salaries, firms choose profit-maximizing sets while repeating unrejected offers, and workers tentatively choose a best available offer.
--
--   $$s_{ij}(t+1)=\begin{cases}s_{ij}(t)+\delta,&\text{if worker }i\text{ rejects firm }j\text{ at }t,\\s_{ij}(t),&\text{otherwise.}\end{cases}$$
--
--   A run stops at a round with no rejection, and its outcome assigns each worker to the firm whose offer the worker holds. For the new-firm-on-the-block process, existing firms begin with the original run's final salaries and offers; the entrant begins at its starting salaries and offers to every worker.
--
--   These definitions support comparisons across all legal runs and stopping rounds.
--
--   **Formalization Note** The entrant's initial offers are made explicit because NFB1 specifies initial salaries but leaves the first offer set implicit. The choice function also has a value when a worker has no offers; the run rule constrains it whenever there is at least one offer.
-- source:
--   Kelso and Crawford, Job matching, coalition formation, and gross substitutes, Econometrica 50 (1982), pp. 1488–1489, R1–R5; p. 1498, NFB1–NFB5. https://doi.org/10.2307/1913392

import Mathlib
import Definitions.Def_KelsoCrawford_CompStatics_Model

namespace KelsoCrawford.CompStatics

structure Run (W F : Type) where
  sal : ℕ → W → F → ℝ
  offers : ℕ → F → Finset W
  choice : ℕ → W → F

def Run.Rejects {W F : Type} [DecidableEq W] (ρ : Run W F)
    (t : ℕ) (i : W) (j : F) : Prop :=
  i ∈ ρ.offers t j ∧ ρ.choice t i ≠ j

def Market.IsRunFrom {W F : Type} [Fintype W] [DecidableEq W]
    (M : Market W F) (δ : ℝ) (sal₀ : W → F → ℝ)
    (offers₀ : F → Finset W) (ρ : Run W F) : Prop := by
  classical
  exact ρ.sal 0 = sal₀ ∧ ρ.offers 0 = offers₀ ∧
  (∀ t j,
    KelsoCrawford.OneSided.IsDemanded (M.y j) (fun i => ρ.sal (t + 1) i j) (ρ.offers (t + 1) j) ∧
    (ρ.offers t j).filter (fun i => ¬ ρ.Rejects t i j) ⊆ ρ.offers (t + 1) j) ∧
  (∀ t i, (∃ j, i ∈ ρ.offers t j) →
    i ∈ ρ.offers t (ρ.choice t i) ∧
    ∀ k, i ∈ ρ.offers t k →
      M.u i k (ρ.sal t i k) ≤
        M.u i (ρ.choice t i) (ρ.sal t i (ρ.choice t i))) ∧
  ∀ t i j,
    ρ.sal (t + 1) i j =
      if ρ.Rejects t i j then ρ.sal t i j + δ else ρ.sal t i j

def Market.IsRun {W F : Type} [Fintype W] [DecidableEq W]
    (M : Market W F) (δ : ℝ) (ρ : Run W F) : Prop :=
  M.IsRunFrom δ M.σ (fun _ => Finset.univ) ρ

def Run.Stopped {W F : Type} [DecidableEq W]
    (ρ : Run W F) (t : ℕ) : Prop :=
  ∀ i j, ¬ ρ.Rejects t i j

def Run.outcome {W F : Type} (ρ : Run W F) (t : ℕ) : Allocation W F :=
  ⟨ρ.choice t, fun i => ρ.sal t i (ρ.choice t i)⟩

def nfbInitialSalaries {W F : Type} (Mplus : Market W (Option F))
    (ρ : Run W F) (T : ℕ) : W → Option F → ℝ :=
  fun i j => match j with
    | some k => ρ.sal T i k
    | none => Mplus.σ i none

def nfbInitialOffers {W F : Type} [Fintype W]
    (ρ : Run W F) (T : ℕ) : Option F → Finset W :=
  fun j => match j with
    | some k => ρ.offers T k
    | none => Finset.univ

end KelsoCrawford.CompStatics


