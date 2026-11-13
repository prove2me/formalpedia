-- Prove2me | Definitions.Def_KSATSingleFlip_Connect_Shattering
-- name    : KSATSingleFlip_Connect_Shattering
-- status  : Definition
-- author  : @wcysai
-- created : 2026-11-13T05:08:11.78913+00:00
-- url     : https://prove2.me/theorems/34feaba4-e888-4511-8d33-15cd0c5246f1
-- title:
--   Random k-SAT shattering and energy barriers
-- statement:
--   A formula is shattered at positive rates $a,b,c$ if its nonempty solution set is partitioned into regions of mass at most $e^{-an}$, any two solutions in different regions have Hamming distance at least $bn$, and every single-variable-flip path in the full Boolean cube between different regions contains an assignment violating at least $cn$ clause occurrences. The model counts repeated clauses separately. The definitions also give the lower and upper density endpoints in Theorem 1.4.
-- source:
--   Chunyang Wang, Yitong Yin, Yixiao Yu, Yiyao Zhang, Single-Variable Connectivity in Random k-SAT, STOC 2027 submission #737, Theorem 1.4, printed p. 4 (PDF p. 6), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_Model

noncomputable section
open scoped Classical BigOperators
namespace KSATSingleFlip.Connect

/-! # Shattering and linear energy barriers

Definitions for Theorem 1.4 of Wang, Yin, Yu and Zhang, STOC 2027 submission
#737, printed p. 4. Clause occurrences are counted by their list positions. -/

/-- The number of clause occurrences falsified by an assignment. -/
def violatedCount {n : ℕ} (Φ : GFormula (Fin n)) (σ : Fin n → Bool) : ℕ :=
  (Finset.univ.filter fun c : Fin Φ.length => ¬ ClauseSat σ (Φ.get c)).card

/-- A finite partition of all solutions into exponentially small regions,
with linear pairwise Hamming separation and linear single-flip energy barriers.
The three rates are explicit parameters to allow the source's constants to
depend on k while remaining uniform in n and in the density range. -/
def IsShattered {n : ℕ} (Φ : GFormula (Fin n))
    (massRate separationRate energyRate : ℝ)
    (regions : Finset (Finset (Fin n → Bool))) : Prop :=
  (sols Φ).Nonempty ∧
  (∀ A ∈ regions, A.Nonempty ∧ A ⊆ sols Φ ∧
    mass Φ A ≤ Real.exp (-massRate * n)) ∧
  (∀ σ ∈ sols Φ, ∃ A ∈ regions, σ ∈ A) ∧
  (∀ A ∈ regions, ∀ B ∈ regions, A ≠ B →
    Disjoint A B ∧
    (∀ σ ∈ A, ∀ τ ∈ B, separationRate * n ≤ (hamming σ τ : ℝ)) ∧
    (∀ σ ∈ A, ∀ τ ∈ B, ∀ p : List (Fin n → Bool),
      IsPathIn Finset.univ p σ τ → ∃ z ∈ p, energyRate * n ≤ violatedCount Φ z))

/-- The shattering interval's lower endpoint, as a density α = m/n. -/
def shatteringDensityLower (k : ℕ) : ℝ :=
  (2 : ℝ) ^ k / k * (Real.log k + Real.log (Real.log k) + Real.log (34 / 13))

/-- The satisfiable-regime upper endpoint used in Theorems 1.2–1.4. -/
def shatteringDensityUpper (k : ℕ) : ℝ :=
  (2 : ℝ) ^ k * (Real.log 2 - 1 / Real.log k)

end KSATSingleFlip.Connect


