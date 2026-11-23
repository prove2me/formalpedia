-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_RsParLamMinus
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_RsParLamMinus
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:35:09.299936+00:00
-- url     : https://prove2.me/theorems/66b2d980-2767-4e5e-9639-4a75b1e4e9bf
-- title:
--   Rs Par Lam Minus
-- statement:
--   Definitions and structural lemmas for Rs Par Lam Minus, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/InterlacingWalks/RsParLamMinus.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_LowerStepStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_AdjGap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.DS.Lap
open ReciprocityTheory.ChartRestriction.DS
def rsExt {N : ℕ} (f : Fin N → ℝ) (x : ℕ) : ℝ := if h : x < N then f ⟨x, h⟩ else 0
def rsG (B : ℕ → ℝ) (t j m q : ℕ) : ℝ :=
  if q < j then -B q else if q = j then -B q - (j : ℝ) * t + m else -B q - (q : ℝ) * t
def rsF (k : ℕ) (U B : ℕ → ℝ) (t j m x : ℕ) : ℝ :=
  if x < k then U x - 1 / 2 else rsG B t j m (x - (k - 1))
def rsPt (k r : ℕ) (u : Fin k → ℝ) (b : Fin (2 * r + 2) → ℝ) (t j m : ℕ) :
    Fin (2 * r + k + 1) → ℝ :=
  fun a => rsF k (rsExt u) (rsExt b) t j m a.val
end ReciprocityTheory.ChartRestriction.DS.Lap


