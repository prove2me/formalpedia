-- Prove2me | Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe
-- name    : Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:51:37.80783+00:00
-- url     : https://prove2.me/theorems/e441bbe7-4d06-440a-bec4-628d0fc9549c
-- title:
--   Sub Three Mul Log Two Le
-- statement:
--   Definitions and structural lemmas for Sub Three Mul Log Two Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/SubThreeMulLogTwoLe.lean

import Definitions.Def_Formalism_SizeWindowBrackets_ErrorFormsWeakWindowsFalse
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Real
namespace Formalism.LFunctionChainParameters.LErr
open Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds
set_option linter.unusedVariables false
noncomputable def modelD (η : ℝ) : Data Unit (fun _ => Unit) Unit 1 1 where
  x := 100000
  ε := 1
  a := 100000
  b := 1
  b' := 1
  k := 100000
  L := 1
  La := 1
  B0 := 1
  Nc := 1
  gam := 0
  LpL := 0
  v := 1
  lg := 0
  logGam := 0
  aT := fun _ => 100000
  w := fun _ _ _ => 1
  d := fun _ _ => 1
  T := fun _ _ => 1
  muN := fun _ _ => 0
  muMaxN := fun _ _ => 0
  h := fun _ _ => 0
  muM := fun _ _ => 0
  muMaxM := fun _ _ => 0
  EeJ := fun _ _ _ => 0
  muCC := fun _ => 0
  muMinCC := fun _ => 0
  Fo := fun _ => 0
  Ga := fun _ => 0
  Ta := fun _ => 0
  ASK := fun _ => 0
  IO := fun _ => 0
  HH := fun _ => 1
  del := fun _ => 0
  η := fun _ => 0
  e := fun _ => 0
  delBar := 0
  etaBar := η
  eBar := 0
def modelC (cHH : ℝ) : Consts := ⟨1, 1, 1, 1, 1, 1, 1, 1, 1, cHH⟩
section
open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds
end
end Formalism.LFunctionChainParameters.LErr
section Check
open Formalism.LFunctionChainParameters.LErr
end Check


