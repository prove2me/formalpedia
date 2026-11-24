-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitiveFormRemainder
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitiveFormRemainder
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:31:25.091831+00:00
-- url     : https://prove2.me/theorems/1c0992ce-67e6-48c5-aaeb-743581bb44e6
-- title:
--   St Primitive Form Remainder
-- statement:
--   Definitions and structural lemmas for St Primitive Form Remainder, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StPrimitiveFormRemainder.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Filter
def PrimitiveFormRemainder.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (w : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (ℓ : (σ → ℂ) →L[ℂ] ℂ)
    (N : ℕ) (δ : (Fin d → ℂ) → ℂ) (q : σ → Fin N → (Fin d → ℂ) → ℂ) (n : σ → ℕ)
    (c : (i : σ) → Fin (n i) → (Fin d → ℂ) → ℂ) (f : (σ → ℂ) → ℂ),
    AnalyticAt ℂ δ (A w) → (∀ i j, AnalyticAt ℂ (q i j) (A w)) → (∀ i j, AnalyticAt ℂ (c i j) (A w)) →
    (∀ i (T : ℂ), T ^ n i + ∑ j, c i j (A w) * T ^ (j : ℕ) = (T - w i) ^ n i) →
    AnalyticAt ℂ f w →
    ∃ (M : ℕ) (R : Polynomial ((Fin d → ℂ) → ℂ)), (∀ k, AnalyticAt ℂ (R.coeff k) (A w)) ∧
      ∀ᶠ z in 𝓝 w, (∀ i, z i ^ n i + ∑ j, c i j (A z) * z i ^ (j : ℕ) = 0) →
        (∀ i, δ (A z) * z i = ∑ j, q i j (A z) * ℓ z ^ (j : ℕ)) →
        δ (A z) ^ M * f z = R.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ => ℂ) (A z)) (ℓ z)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


