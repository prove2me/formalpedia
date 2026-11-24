-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsElem
-- name    : GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsElem
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:10:42.595033+00:00
-- url     : https://prove2.me/theorems/440a6218-78ce-468b-9442-bc18a425512e
-- title:
--   Statements Elem
-- statement:
--   Definitions and structural lemmas for Statements Elem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/StatementsElem.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
namespace RestTerms
open Finset
noncomputable section
def RestInnerTsumBound.Statement : Prop :=
  ∀ (p : ℝ) (k : ℕ) (c : ℕ → ℝ) (M : ℝ), 2 ≤ p → 1 ≤ k → (∀ n, |c n| ≤ M) →
    Summable (fun n : ℕ => (p ^ ((n + 1) * k))⁻¹ * c n) ∧
      |∑' n : ℕ, (p ^ ((n + 1) * k))⁻¹ * c n| ≤ M * (2 * (p ^ k)⁻¹)
def RestKSumBound.Statement : Prop :=
  ∀ (p X : ℝ) (N : ℕ), 0 < p → 0 ≤ X → X ≤ 3 / 8 * p →
    ∑ k ∈ Finset.Icc 2 N, 2 * (p ^ k)⁻¹ * X ^ (k - 1) / (k.factorial : ℝ) ≤ 1.5 * X / p ^ 2
def RestPrimeBoundOfFactor.Statement : Prop :=
  ∀ (f r a : ℕ) (c : SmallBlock) (B₀ : ℝ), 1 ≤ f → 1 ≤ r → 1 ≤ a →
    4 * (f : ℝ) * ((r + a : ℕ) : ℝ) ^ 2 ≤ B₀ →
    ∀ Q : ℕ → Fin f → RootRing f (r + a),
      (∀ k : ℕ, 2 ≤ k → k ≤ r + a → ∀ τ τ' : Fin f,
        |restTerm f (r + a) Q k τ (smallPowerSum f r a c (k - 1) τ')| ≤
          ((f * (r * a) + 1 : ℕ) : ℚ) * |fibreDegree f r a c| * restX r a ^ (k - 1) /
            (k.factorial : ℚ)) →
    ∀ (s : ℕ → ℕ → Fin f → Fin f) (e : ℕ → ℕ → Fin f → ℕ → ℚ),
      (∀ p n τ k, e p n τ k = 1 ∨ e p n τ k = -1) →
    ∀ p : ℕ, p.Prime → B₀ < p →
      |restPrimeModel f r a c Q s e p| ≤
        1.5 * f * (restX r a : ℝ) * (Real.log p / (p : ℝ) ^ 2) *
          ((f * (r * a) + 1 : ℕ) : ℝ) * |(fibreDegree f r a c : ℝ)|
def RestBoundOfPrimeBound.Statement : Prop :=
  ∀ (f r a : ℕ) (c : SmallBlock) (B₀ : ℝ), 1 ≤ f → 1 ≤ r → 1 ≤ a →
    4 * (f : ℝ) * ((r + a : ℕ) : ℝ) ^ 2 ≤ B₀ →
    ∀ (Q : ℕ → Fin f → RootRing f (r + a)) (s : ℕ → ℕ → Fin f → Fin f)
      (e : ℕ → ℕ → Fin f → ℕ → ℚ),
    (∀ p : ℕ, p.Prime → B₀ < p →
      |restPrimeModel f r a c Q s e p| ≤
        1.5 * f * (restX r a : ℝ) * (Real.log p / (p : ℝ) ^ 2) *
          ((f * (r * a) + 1 : ℕ) : ℝ) * |(fibreDegree f r a c : ℝ)|) →
    ∀ P : Set ℕ,
      Summable (fun p : {p : ℕ // p ∈ P ∧ p.Prime ∧ B₀ < p} =>
        |restPrimeModel f r a c Q s e p|) ∧
      |∑' p : {p : ℕ // p ∈ P ∧ p.Prime ∧ B₀ < p}, restPrimeModel f r a c Q s e p| ≤
        1.6 * ((f * (r * a) + 1 : ℕ) : ℝ) * |(fibreDegree f r a c : ℝ)|
end
end RestTerms
end GroundTheory.Heights₂.Heights


