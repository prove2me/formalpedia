-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Characterised
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Characterised
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:30:40.022571+00:00
-- url     : https://prove2.me/theorems/de45adf4-9dcd-41d6-a74e-960d099d9207
-- title:
--   Characterised
-- statement:
--   Definitions and structural lemmas for Characterised, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/Characterised.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
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
open MvPolynomial MeasureTheory NumberField
noncomputable section
def ConeIntegralMass.Statement : Prop :=
  ∀ (n e δ : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ),
    IsProjPrime W → IsChowForm W (e + 1) f → IsMultiHomog δ f →
      coneIntegral h W e (fun _ => 1) = δ
def ChowFormBaseChange.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n k : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (f : MvPolynomial (Fin k × Fin n) K) (σ : K →+* ℂ),
    IsProjPrime I → IsChowForm I k f →
      (∀ W ∈ (fundCycle (I.map (MvPolynomial.map σ))).support, IsProjPrime W) ∧
        IsChowFormCycle (fundCycle (I.map (MvPolynomial.map σ))) k (MvPolynomial.map σ f)
def ChowHeightCharacterised.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (H : ArchData K n)
    (J : Ideal (MvPolynomial (Fin n) K) → ℝ),
    (∀ (e δ : ℕ) (I : Ideal (MvPolynomial (Fin n) K)) (f : MvPolynomial (Fin (e + 1) × Fin n) K)
        (u : Fin n → 𝓞 K),
      IsProjPrime I → IsChowForm I (e + 1) f → IsMultiHomog δ f →
      linForm (fun j => (u j : K)) ∉ I →
        J I = (∑ W ∈ (divCycle I fun j => (u j : K)).support,
                ((divCycle I fun j => (u j : K)) W : ℝ) * J W) +
          (1 / Module.finrank ℚ K : ℝ) *
            (vertTerm I (e + 1) u -
              ∑ σ : K →+* ℂ, cycleIntegral (H.normAt σ) (fundCycle (I.map (MvPolynomial.map σ))) e
                (fsLog (H.normAt σ) fun j => σ (u j)))) →
    ∀ (e δ : ℕ) (I : Ideal (MvPolynomial (Fin n) K)) (f : MvPolynomial (Fin (e + 1) × Fin n) K),
      IsProjPrime I → IsChowForm I (e + 1) f → IsMultiHomog δ f → J I = chowHt H (e + 1) δ f
end
end GroundTheory.Heights₂.Heights


