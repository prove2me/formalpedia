-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsTop
-- name    : GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsTop
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:09:48.355001+00:00
-- url     : https://prove2.me/theorems/5ba2ff6d-15cc-495d-b584-80674e0801c2
-- title:
--   Statements Top
-- statement:
--   Definitions and structural lemmas for Statements Top, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/StatementsTop.lean

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
open MvPolynomial Finset
noncomputable section
def OtherFactorFormula.Statement : Prop :=
  ∀ (f r a : ℕ) (c : SmallBlock), 2 ≤ f → 1 ≤ r → 1 ≤ a →
    ∃ C₀ : ℚ, C₀ ≠ 0 ∧
      fibreDegree f r a c =
        C₀ * (f * (r * a)).factorial / ((r * a).factorial : ℚ) ^ f *
          (numStandardTable (rectangle r a) : ℚ) ^ f ∧
      ∀ Q : ℕ → Fin f → RootRing f (r + a),
        IsPowerSumDecomposition f (r + a) (restPolynomial f r a c) Q →
        ∀ (k : ℕ) (hk2 : 2 ≤ k) (hkN : k ≤ r + a) (τ τ' : Fin f), τ' ≠ τ →
          ∃ S : MvPolynomial (Fin (r + a)) ℚ,
            powerSumHom (r + a) S =
              ∑ nu ∈ partitionsOf r k,
                C ((numStandardTable (fun i => a + nu i) : ℕ) : ℚ) *
                  aeval (fun i : Fin (r + a) => C c.sign * X i) (schur (Fin (r + a)) nu) ∧
            restTerm f (r + a) Q k τ (smallPowerSum f r a c (k - 1) τ') =
              C₀ * k * (f * (r * a) + 1).factorial /
                  (((r * a + k).factorial : ℚ) * ((r * a - (k - 1)).factorial : ℚ) *
                    ((r * a).factorial : ℚ) ^ (f - 2)) *
                (numStandardTable (rectangle r a) : ℚ) ^ (f - 2) *
                symmetricGroupCharacter (rectangle r a)
                  ((k - 1) :: List.replicate (r * a - (k - 1)) 1) *
                coeff (Finsupp.single (⟨k - 1, by omega⟩ : Fin (r + a)) 1) S
def SchurSignCoefficient.Statement : Prop :=
  ∀ (N r k : ℕ) (hk1 : 1 ≤ k) (hkN : k ≤ N) (nu : Fin r → ℕ) (s : ℚ), (s = 1 ∨ s = -1) →
    Antitone nu → ∑ i, nu i = k →
    ∃ S : MvPolynomial (Fin N) ℚ,
      powerSumHom N S = aeval (fun i : Fin N => C s * X i) (schur (Fin N) nu) ∧
      coeff (Finsupp.single (⟨k - 1, by omega⟩ : Fin N) 1) S =
        s ^ k * if ∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1 then
          (-1 : ℚ) ^ ((Finset.univ.filter fun i : Fin r => (i : ℕ) ≠ 0 ∧ nu i = 1).card) / k
        else 0
def HookTableauCount.Statement : Prop :=
  ∀ r k l : ℕ, l < k → l < r → numStandardTable (hookShape r k l) = Nat.choose (k - 1) l
def RectangleTablePos.Statement : Prop :=
  ∀ r a : ℕ, 0 < numStandardTable (rectangle r a)
def HookSumBound.Statement : Prop :=
  ∀ (r a k : ℕ) (b : (Fin r → ℕ) → ℚ), 1 ≤ k →
    (∀ nu ∈ partitionsOf r k, |b nu| ≤ numStandardTable (fun i => a + nu i)) →
    ∑ nu ∈ (partitionsOf r k).filter (fun nu => ∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1), |b nu| ≤
      (Nat.choose (r * a + k) k : ℚ) * 2 ^ (k - 1) * numStandardTable (rectangle r a)
def ShiftSumRule.Statement : Prop :=
  ∀ r a : ℕ, 1 ≤ r → 1 ≤ a → ∀ Q : ℕ → Fin 1 → RootRing 1 (r + a),
    IsPowerSumDecomposition 1 (r + a) (restPolynomial 1 r a .last) Q →
      (a : ℚ) * flagIntegral 1 (r + a) (Q 1 0) =
        ∑ k ∈ Finset.Icc 2 (r + a),
          restTerm 1 (r + a) Q k 0 (smallPowerSum 1 r a .last (k - 1) 0)
def LinearTermValue.Statement : Prop :=
  ∀ r a : ℕ, 1 ≤ r → 1 ≤ a → ∀ Q : ℕ → Fin 1 → RootRing 1 (r + a),
    IsPowerSumDecomposition 1 (r + a) (restPolynomial 1 r a .last) Q →
      flagIntegral 1 (r + a) (Q 1 0) * numStandardTable (rectangle r a) =
        fibreDegree 1 r a .last *
          numStandardTable (fun i : Fin r => a + if (i : ℕ) = 0 then 1 else 0)
end
end RestTerms
end GroundTheory.Heights₂.Heights


