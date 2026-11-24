-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRootSumHolomorphic
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRootSumHolomorphic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:30:23.051615+00:00
-- url     : https://prove2.me/theorems/b019a30c-dfee-4a11-9e84-1bd031e6abd9
-- title:
--   St Root Sum Holomorphic
-- statement:
--   Definitions and structural lemmas for St Root Sum Holomorphic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StRootSumHolomorphic.lean

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
namespace GroundTheory.Heights₂.Heights.ComplexSets
noncomputable section
def RootSumHolomorphic.Statement : Prop :=
  ∀ (d : ℕ) (m : Polynomial (MvPolynomial (Fin d) ℂ)) (W : Set (Fin d → ℂ)) (Φ : (Fin d → ℂ) → ℂ → ℂ),
    m.Monic → IsOpen W → (∀ y ∈ W, (m.map (MvPolynomial.eval y)).Separable) →
    (∀ y ∈ W, ∀ τ : ℂ, (m.map (MvPolynomial.eval y)).IsRoot τ →
      ∃ O : Set ((Fin d → ℂ) × ℂ), IsOpen O ∧ (y, τ) ∈ O ∧ ∃ Ψ : (Fin d → ℂ) × ℂ → ℂ,
        DifferentiableOn ℂ Ψ O ∧
        ∀ p ∈ O, (m.map (MvPolynomial.eval p.1)).IsRoot p.2 → Φ p.1 p.2 = Ψ p) →
    DifferentiableOn ℂ (fun y => ((m.map (MvPolynomial.eval y)).roots.map (Φ y)).sum) W
end
end GroundTheory.Heights₂.Heights.ComplexSets


