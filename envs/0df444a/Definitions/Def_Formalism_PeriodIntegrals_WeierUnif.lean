-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_WeierUnif
-- name    : Formalism_PeriodIntegrals_WeierUnif
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:38:52.175454+00:00
-- url     : https://prove2.me/theorems/b211e47d-4663-40c5-a58c-1f4818e6f45e
-- title:
--   Weier Unif
-- statement:
--   Definitions and structural lemmas for Weier Unif, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/WeierUnif.lean

import Definitions.Def_Formalism_PeriodIntegrals_LatDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI
namespace WeierUnif
def IsLat (Λ : AddSubgroup ℂ) : Prop :=
  DiscreteTopology Λ ∧ Submodule.span ℝ (Λ : Set ℂ) = ⊤
end WeierUnif
open WeierUnif
def WeierUnif : Prop :=
  ∀ a b : ℂ, a ^ 3 - 27 * b ^ 2 ≠ 0 →
    (∃ Λ : AddSubgroup ℂ, IsLat Λ ∧ g2 Λ = a ∧ g3 Λ = b) ∧
    ∀ Λ Λ' : AddSubgroup ℂ, IsLat Λ → IsLat Λ' → g2 Λ = a → g3 Λ = b → g2 Λ' = a → g3 Λ' = b →
      Λ = Λ'
end PI
end


