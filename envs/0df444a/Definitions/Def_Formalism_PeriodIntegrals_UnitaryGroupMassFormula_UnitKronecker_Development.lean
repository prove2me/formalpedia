-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitKronecker_Development
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitKronecker_Development
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:10:23.834603+00:00
-- url     : https://prove2.me/theorems/7aa67243-39d7-4592-8a7f-4b6b5ce9550d
-- title:
--   Development
-- statement:
--   Definitions and structural lemmas for Development, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitKronecker/Development.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitKron
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI.UnitKronW
open Matrix Polynomial ComplexOrder
def StepA : Prop := ∀ (k : ℕ) (H G : Matrix (Fin k) (Fin k) ℂ), H.PosDef → Gᴴ * H * G = H →
  ∀ μ : ℂ, G.charpoly.IsRoot μ → ‖μ‖ = 1
def StepB : Prop := ∀ (E : Type) [Field E] [NumberField E] (p : E[X]), p.Monic → (∀ i, IsIntegral ℤ (p.coeff i)) →
  (∀ (φ : E →+* ℂ) (μ : ℂ), (p.map φ).IsRoot μ → ‖μ‖ = 1) →
  ∀ (φ₀ : E →+* ℂ) (μ : ℂ), (p.map φ₀).IsRoot μ → ∃ m : ℕ, 0 < m ∧ μ ^ m = 1
def StepC : Prop := ∀ (k : ℕ) (H G : Matrix (Fin k) (Fin k) ℂ), H.PosDef → Gᴴ * H * G = H →
  ∀ n : ℕ, (∀ μ ∈ G.charpoly.roots, μ ^ n = 1) → G ^ n = 1
end PI.UnitKronW


