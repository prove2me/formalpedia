-- Prove2me | Definitions.Def_NonuniformCompetitive_Snoopy_Supplement_taskSystem
-- name    : NonuniformCompetitive_Snoopy_Supplement_taskSystem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T11:52:18.331298+00:00
-- url     : https://prove2.me/theorems/e5b23369-5df6-49a3-bec7-af5cb25ad42a
-- title:
--   Directed finite task systems, work functions and known states
-- statement:
--   A task system has states $S$, requests $R$, finite nonnegative directed transition costs $d(s,t)$ with zero diagonal and the triangle inequality, and processing costs $T(r,s)\in[0,\infty]$. Each request specifies whether its current identity may be used for a move at its moment. Before-request choices depend only on the preceding prefix; moment and after-request choices may use the current request.
--
--   The work function and the known-state criterion are
--   $$w_\sigma(s)=\inf\{\text{schedule cost ending at }s\},\qquad
--   w_\sigma(s_*)+d(s_*,t)\le w_\sigma(t)\quad(t\in S).$$
--   Ties are resolved by a fixed canonical order. A forcing word for $s$ is free while remaining at $s$ and has positive cost for every schedule avoiding $s$. A mixed strategy includes fixed-input cost measurability. Competitiveness retains a real additive constant and is evaluated on finite words with finite offline optimum; all-infinite infeasible words do not become zero through conversion to real numbers.
--
--   This general model is independent of the cache representation. Finite state and request instances are supplied at theorem use, while zero-cost distinct states and both request timings remain available.
-- source:
--   Karlin, Manasse, McGeoch, Owicki, Competitive Randomized Algorithms for Nonuniform Problems, Algorithmica 11 (1994), DOI 10.1007/BF01189993, §2, pp. 544–546

import Mathlib

namespace NonuniformCompetitive.Snoopy.Supplement

open MeasureTheory
open scoped NNReal ENNReal

/-- The general directed task system of §2, separate from any cache model.
Finite state and request types are supplied by the theorems. Distinct states may
have zero transition cost; processing costs may be infinite. -/
structure TaskSystem (S R : Type) where
  distance : S → S → ℝ≥0
  diagonal : ∀ s, distance s s = 0
  triangle : ∀ s t u, distance s u ≤ distance s t + distance t u
  task : R → S → ℝ≥0∞
  lookahead : R → Bool

/-- Before-request moves use the preceding prefix only; moment and after moves
may use the current request. Keeping before separate is essential for Theorem 1. -/
structure TaskOnline {S R : Type} (T : TaskSystem S R) where
  before : List R → S
  moment : List R → S
  after : List R → S
  zero : ∀ (h : List R) (r : R), T.lookahead r = false → moment (h ++ [r]) = before h

noncomputable def taskScheduleCost {S R : Type} (T : TaskSystem S R) (σ : List R)
    (b m s : ℕ → S) : ℝ≥0∞ :=
  ∑ j : Fin σ.length,
    ((T.distance (s j) (b j) : ℝ≥0∞) + (T.distance (b j) (m j) : ℝ≥0∞) +
      T.task σ[j] (m j) + (T.distance (m j) (s (j + 1)) : ℝ≥0∞))

def TaskScheduleOK {S R : Type} (T : TaskSystem S R) (s₀ : S) (σ : List R)
    (b m s : ℕ → S) : Prop :=
  s 0 = s₀ ∧ ∀ j : Fin σ.length, T.lookahead σ[j] = false → m j = b j

/-- Work function with arbitrary terminal moves. In the empty word it is the
transition cost from the initial state. Infima are in the complete lattice
[0,∞], so infeasible inputs have value ∞, never the real sInf default zero. -/
noncomputable def taskWork {S R : Type} (T : TaskSystem S R) (s₀ : S)
    (σ : List R) (t : S) : ℝ≥0∞ :=
  ⨅ (b : ℕ → S) (m : ℕ → S) (s : ℕ → S) (_ : TaskScheduleOK T s₀ σ b m s),
    taskScheduleCost T σ b m s + (T.distance (s σ.length) t : ℝ≥0∞)

noncomputable def taskOpt {S R : Type} (T : TaskSystem S R) (s₀ : S)
    (σ : List R) : ℝ≥0∞ := ⨅ t : S, taskWork T s₀ σ t

noncomputable def TaskOnline.cost {S R : Type} {T : TaskSystem S R}
    (A : TaskOnline T) (σ : List R) : ℝ≥0∞ :=
  ∑ j : Fin σ.length,
    ((T.distance (A.after (σ.take j)) (A.before (σ.take j)) : ℝ≥0∞) +
      (T.distance (A.before (σ.take j)) (A.moment (σ.take (j + 1))) : ℝ≥0∞) +
      T.task σ[j] (A.moment (σ.take (j + 1))) +
      (T.distance (A.moment (σ.take (j + 1))) (A.after (σ.take (j + 1))) : ℝ≥0∞))

structure TaskRandomized {S R : Type} (T : TaskSystem S R) where
  ι : Type
  [ms : MeasurableSpace ι]
  μ : Measure ι
  prob : IsProbabilityMeasure μ
  alg : ι → TaskOnline T
  meas : ∀ σ : List R, Measurable fun i => (alg i).cost σ

noncomputable def TaskRandomized.expCost {S R : Type} {T : TaskSystem S R}
    (A : TaskRandomized T) (σ : List R) : ℝ≥0∞ := ∫⁻ i, (A.alg i).cost σ ∂A.μ

/-- Competitive on every input with finite offline optimum. Entirely infeasible
words are not assigned a spurious zero optimum by conversion to ℝ. No positivity
condition on α or a is added. -/
def TaskRandomized.Competitive {S R : Type} {T : TaskSystem S R}
    (A : TaskRandomized T) (s₀ : S) (α : ℝ) : Prop :=
  (∀ i, (A.alg i).after [] = s₀) ∧ ∃ a : ℝ, ∀ σ : List R,
    taskOpt T s₀ σ ≠ ⊤ → A.expCost σ ≤ ENNReal.ofReal (α * (taskOpt T s₀ σ).toReal + a)

/-- The raw work-function criterion on p.545. A known state must have finite
work value; all-infinite infeasible prefixes do not designate a known state. -/
def TaskRawKnown {S R : Type} (T : TaskSystem S R) (s₀ : S) (σ : List R) (s : S) : Prop :=
  taskWork T s₀ σ s ≠ ⊤ ∧
    ∀ t : S, taskWork T s₀ σ s + (T.distance s t : ℝ≥0∞) ≤ taskWork T s₀ σ t

/-- Resolve zero-distance ties using the fixed canonical order. -/
def TaskKnown {S R : Type} [LinearOrder S] (T : TaskSystem S R)
    (s₀ : S) (σ : List R) (s : S) : Prop :=
  TaskRawKnown T s₀ σ s ∧ ∀ t : S, t < s → ¬TaskRawKnown T s₀ σ t

/-- The two explicit forcing-word conditions of Theorem 1. Avoidance includes
states before, at, and after requests, not only the terminal states. -/
def HasForcingWord {S R : Type} (T : TaskSystem S R) (target : S) : Prop :=
  ∃ ρ : List R,
    (∀ r ∈ ρ, T.task r target = 0) ∧
    ∀ (b m s : ℕ → S),
      (∀ j : Fin ρ.length, T.lookahead ρ[j] = false → m j = b j) →
      (s 0 ≠ target ∧ ∀ j : Fin ρ.length, b j ≠ target ∧ m j ≠ target ∧ s j ≠ target ∧ s (j + 1) ≠ target) →
      0 < taskScheduleCost T ρ b m s

/-- Theorem 1 assumes a witness for every state; the phase framework requires
these witnesses only at the start and end states of its phases (p.547). -/
def HasForcingWords {S R : Type} (T : TaskSystem S R) : Prop :=
  ∀ target : S, HasForcingWord T target

end NonuniformCompetitive.Snoopy.Supplement


