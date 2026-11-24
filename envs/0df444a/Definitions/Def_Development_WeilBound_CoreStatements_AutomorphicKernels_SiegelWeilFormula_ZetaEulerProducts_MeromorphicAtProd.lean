-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ZetaEulerProducts_MeromorphicAtProd
-- name    : Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ZetaEulerProducts_MeromorphicAtProd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:00:12.254245+00:00
-- url     : https://prove2.me/theorems/ced6cb8a-438f-45c5-870f-431150b94ddb
-- title:
--   Meromorphic At Prod
-- statement:
--   Definitions and structural lemmas for Meromorphic At Prod, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ZetaEulerProducts/MeromorphicAtProd.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
namespace PositivityTheory.Lord
def PO (f : ℂ → ℂ) (x : ℂ) (k : ℕ) : Prop :=
  ∃ H : ℂ → ℂ, AnalyticAt ℂ H x ∧ ∀ᶠ s in 𝓝[≠] x, H s = (s - x) ^ k * f s
def ZO (f : ℂ → ℂ) (x : ℂ) (m : ℕ) : Prop :=
  ∃ u : ℂ → ℂ, AnalyticAt ℂ u x ∧ u x ≠ 0 ∧ ∀ᶠ s in 𝓝[≠] x, f s = (s - x) ^ m * u s
variable {f g : ℂ → ℂ} {x : ℂ} {k l m n : ℕ}
end PositivityTheory.Lord


