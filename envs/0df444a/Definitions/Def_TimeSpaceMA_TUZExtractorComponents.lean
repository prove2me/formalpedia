-- Prove2me | Definitions.Def_TimeSpaceMA_TUZExtractorComponents
-- name    : TimeSpaceMA_TUZExtractorComponents
-- status  : Definition
-- author  : @bersubs
-- created : 2026-11-14T20:10:03.756898+00:00
-- url     : https://prove2.me/theorems/d5b92bd2-8b0e-4d1b-81a2-b351d3ab35ee
-- title:
--   Finite event interfaces for the condenser and extractor
-- statement:
--   Defines statistical-distance tests on finite events for lossless condensation and weighted seeded extraction. The two component interfaces specify a logarithmic-seed lossless condenser and a polylogarithmic-seed extractor with constant entropy loss, together with uniform polynomial-time evaluation.

import Definitions.Def_TimeSpaceMA_TUZExtractor
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod

open scoped BigOperators

namespace TimeSpaceMA

section Statistics

variable {X Y Seed₁ Seed₂ Out : Type} [Fintype Y] [Fintype Seed₁] [Fintype Seed₂] [Fintype Out]
  [DecidableEq Y] [DecidableEq Out]

/-- Every event of the empirical distribution of the condensed flat source has excess
probability at most δ over its probability under the reference distribution. -/
def CondensesFlatEvents (cond : X → Seed₁ → Y) (S : Finset X)
    (reference : Y → ℝ) (δ : ℝ) : Prop :=
  ∀ U : Finset Y,
    (((S ×ˢ Finset.univ).filter fun p : X × Seed₁ => cond p.1 p.2 ∈ U).card : ℝ) /
      ((S.card : ℝ) * Fintype.card Seed₁) - ∑ y ∈ U, reference y ≤ δ

/-- Probability of an output test under a finite weighted source and a fresh uniform seed. -/
noncomputable def weightedExtractionProbability (ext : Y → Seed₂ → Out)
    (reference : Y → ℝ) (U : Finset Out) : ℝ :=
  ∑ y : Y, reference y *
    (((Finset.univ : Finset Seed₂).filter fun r => ext y r ∈ U).card : ℝ) / Fintype.card Seed₂

/-- The one-sided extractor condition lifted to all events of a finite weighted source. -/
def WeightedExtractorEvents (ext : Y → Seed₂ → Out)
    (reference : Y → ℝ) (ε : ℝ) : Prop :=
  ∀ U : Finset Out,
    weightedExtractionProbability ext reference U - (U.card : ℝ)/Fintype.card Out ≤ ε

end Statistics

end TimeSpaceMA

namespace TimeSpaceMA

open Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableTidilyInPolyTime

/-- Interpret a candidate evaluator in the finite label set of a specified width. -/
def fixedOutput (f : ExtractorInput → ℕ) (n k t m : ℕ)
    (x : Fin (2^n)) (y : Fin (2^t)) : Fin (2^m) :=
  ⟨f (n,k,t,x.val,y.val) % 2^m, Nat.mod_lt _ (Nat.pow_pos (by decide))⟩

/-- GUV's lossless condenser at α=1, in finite event form. Enlarge its seed to
(a,mathrm{size}(n)) by passing the spare bits through and zero-pad the output
to (2(k+a,mathrm{size}(n))) bits. -/
def HasShortLosslessCondenser (ε : ℝ) : Prop :=
  ∃ (a : ℕ) (cond : ExtractorInput → ℕ), 0 < a ∧
    ComputableInPolyTime cond encExtractorInput encNat ∧
    ∀ n k : ℕ, 1 ≤ n → k ≤ n →
      let s := a*n.size
      let m := 2*(k+s)
      ∀ S : Finset (Fin (2^n)), 2^k ≤ S.card →
        ∃ q : Fin (2^m) → ℝ, (∑ y, q y) = 1 ∧
          (∀ y, 0 ≤ q y ∧ q y ≤ 1/(2:ℝ)^(k+s)) ∧
          CondensesFlatEvents (fixedOutput cond n k s m) S q ε

/-- RRV's constant-loss extractor with a cubically polylogarithmic seed schedule.
The additional constant Δ in the seed width makes the output width expression
valid also at very small input entropies. -/
def HasPolylogConstantLossExtractor (ε : ℝ) : Prop :=
  ∃ (b Δ : ℕ) (ext : ExtractorInput → ℕ), 0 < b ∧
    ComputableInPolyTime ext encExtractorInput encNat ∧
    ∀ w K : ℕ, 1 ≤ w → K ≤ w →
      let d := b*w.size^3+Δ
      ∀ q : Fin (2^w) → ℝ, (∑ y, q y) = 1 →
        (∀ y, 0 ≤ q y ∧ q y ≤ 1/(2:ℝ)^K) →
        WeightedExtractorEvents (extractorEdge ext Δ w K d) q ε

end TimeSpaceMA


