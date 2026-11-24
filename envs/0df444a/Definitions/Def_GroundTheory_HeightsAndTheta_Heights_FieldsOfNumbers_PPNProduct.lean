-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPNProduct
-- name    : GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPNProduct
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:30:33.26756+00:00
-- url     : https://prove2.me/theorems/bf30a7fc-17d7-4ea1-ac8f-8b7ebd1ef8b4
-- title:
--   PPNProduct
-- statement:
--   Definitions and structural lemmas for PPNProduct, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPNProduct.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsAddBlock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Filter
noncomputable section
universe u
section Product
variable {K : Type}
def prodFn (A : (K → ℤ) → ℤ) (B : ℤ → ℤ) : (Option K → ℤ) → ℤ :=
  fun m => A (fun k => m (some k)) * B (m none)
def diff1 (g : ℤ → ℤ) : ℤ → ℤ := fun t => g t - g (t - 1)
end Product
section Binomial
end Binomial
end
end GroundTheory.Heights₂.Heights.FieldNumbers


