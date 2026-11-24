-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StWeierstrassFiniteness
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StWeierstrassFiniteness
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:15:48.770913+00:00
-- url     : https://prove2.me/theorems/17272f2f-ae9c-48e3-b0ec-12ef0b330a8b
-- title:
--   St Weierstrass Finiteness
-- statement:
--   Definitions and structural lemmas for St Weierstrass Finiteness, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StWeierstrassFiniteness.lean

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
def WeierstrassFiniteness.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (x : σ → ℂ) (k : ℕ) (f : Fin k → (σ → ℂ) → ℂ) (d : ℕ)
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    (∀ i, AnalyticAt ℂ (f i) x) →
    (∀ l : σ, ∃ (r : ℕ) (h : Fin k → (σ → ℂ) → ℂ) (h' : Fin d → (σ → ℂ) → ℂ),
      (∀ i, AnalyticAt ℂ (h i) x) ∧ (∀ j, AnalyticAt ℂ (h' j) x) ∧
      ∀ᶠ z in 𝓝 x, (z l - x l) ^ r = ∑ i, h i z * f i z + ∑ j, h' j z * (A z j - A x j)) →
    ∀ g : (σ → ℂ) → ℂ, AnalyticAt ℂ g x →
      ∃ (N : ℕ) (a : Fin N → (Fin d → ℂ) → ℂ) (h : Fin k → (σ → ℂ) → ℂ),
        (∀ j, AnalyticAt ℂ (a j) (A x)) ∧ (∀ i, AnalyticAt ℂ (h i) x) ∧
        ∀ᶠ z in 𝓝 x, g z ^ N + ∑ j, a j (A z) * g z ^ (j : ℕ) = ∑ i, h i z * f i z
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


