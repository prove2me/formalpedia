-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ChoiceOfTops
-- name    : Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ChoiceOfTops
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:02:24.368277+00:00
-- url     : https://prove2.me/theorems/c290609c-e01f-4862-9281-4d5e9389cb63
-- title:
--   Choice Of Tops
-- statement:
--   Definitions and structural lemmas for Choice Of Tops, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ChoiceOfTops.lean

import Mathlib
import Definitions.Def_Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Formalism.G0
namespace GlobalTheory.RandomTops
def ex (δ : ℝ) (S : Finset ℕ) (f : Finset ℕ → ℝ) : ℝ :=
  ∑ T ∈ S.powerset, δ ^ T.card * (1 - δ) ^ (S.card - T.card) * f T
open Classical in

def ind (p : Prop) : ℝ := if p then 1 else 0
variable {δ : ℝ}
def tile (r u s : ℕ) : Finset ℕ :=
  Finset.Ico (s * ((6 * r + 1) * u)) ((s + 1) * ((6 * r + 1) * u))
end GlobalTheory.RandomTops


