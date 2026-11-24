-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermMinimalPolynomialDivides
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermMinimalPolynomialDivides
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:30:32.263265+00:00
-- url     : https://prove2.me/theorems/d12e8367-2660-4076-9769-71ac1127ff43
-- title:
--   St Germ Minimal Polynomial Divides
-- statement:
--   Definitions and structural lemmas for St Germ Minimal Polynomial Divides, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StGermMinimalPolynomialDivides.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_AnalyticGerm
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
def GermMinimalPolynomialDivides.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsAnalyticNear X w → GermIrreducibleAt X w →
    (∃ W ∈ 𝓝 w, ∀ x ∈ X ∩ W, A x = A w → x = w) →
    (∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A w) → (∀ᶠ z in 𝓝 w, z ∈ X → h (A z) = 0) →
        ∀ᶠ y in 𝓝 (A w), h y = 0) →
    ∀ g : (σ → ℂ) → ℂ, AnalyticAt ℂ g w →
      ∃ (n : ℕ) (b : Fin n → (Fin d → ℂ) → ℂ), (∀ j, AnalyticAt ℂ (b j) (A w)) ∧
        (∀ᶠ z in 𝓝 w, z ∈ X → g z ^ n + ∑ j, b j (A z) * g z ^ (j : ℕ) = 0) ∧
        ∀ E : Polynomial ((Fin d → ℂ) → ℂ), (∀ k, AnalyticAt ℂ (E.coeff k) (A w)) →
          (∀ᶠ z in 𝓝 w, z ∈ X → E.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ => ℂ) (A z)) (g z) = 0) →
          ∀ᶠ y in 𝓝 (A w),
            (Polynomial.X ^ n + ∑ j, Polynomial.C (b j y) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ) ∣
              E.map (Pi.evalRingHom (fun _ : Fin d → ℂ => ℂ) y)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


