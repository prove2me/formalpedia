-- Prove2me | Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PBrDiv
-- name    : Formalism_SizeWindowBrackets_ChainSlopeWindows_PBrDiv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:04:58.984934+00:00
-- url     : https://prove2.me/theorems/a10a642d-7d4d-439a-9ee0-38b0c41e5d89
-- title:
--   PBr Div
-- statement:
--   Definitions and structural lemmas for PBr Div, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PBrDiv.lean

import Definitions.Def_Formalism_SizeWindowBrackets_SBrDiv
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Rerealize
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open Formalism.HN
noncomputable section
namespace Formalism.LFunctionChainParameters.LBrDiv
open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain2
def satD : Data Unit (fun _ => Unit) (Fin 1) 1 1 where
  x := 1
  ε := 1 / 52
  a := Real.exp 1
  b := Real.exp 1
  b' := 1
  k := 1
  L := 1
  La := 1
  B0 := Real.exp 1
  Nc := 0
  gam := 0
  LpL := 0
  v := Real.pi * Real.exp (-1)
  lg := 0
  logGam := 0
  aT := fun _ => 0
  w := fun _ _ _ => 1
  d := fun _ _ => 1
  T := fun _ _ => 1
  muN := fun _ _ => 0
  muMaxN := fun _ _ => 0
  h := fun _ _ => 4
  muM := fun _ _ => 0
  muMaxM := fun _ _ => 0
  EeJ := fun _ _ _ => 0
  muCC := fun _ => 3 + Real.exp 1
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
  etaBar := 0
  eBar := 0
def satC : Consts where
  cDiv := 60
  eDiv := 1
  cE := 0
  cH := 0
  cCount := 0
  cSlope := 0
  cSl1 := 0
  cLoss := 0
  eLoss := 0
  cHH := 0
def satP : ParNums where
  rd := 1
  f := 1
  N := 1
  S := 0
  tt := 0
  η := 0
  w'' := 0
  dC := 1
  lam0 := 1
  C0 := 1
def satSt : StepNums (Fin 1) (Fin 1) where
  mu0 := 1 + Real.exp 1
  FoP := 0
  hP := 2
  mlam := -1
  hK := fun _ => 1
  phν := fun _ _ => 2
  nν := fun _ _ => 4
  fa := fun _ _ => 0
  Lpass := 2
  Eb := Real.exp 1
  e6 := 1
  eP := 2
  eK := fun _ => 3
  pq := fun _ => 1
  w := fun _ _ => 1
  eE := fun _ _ => 2
  δ := fun _ _ => 3
end Formalism.LFunctionChainParameters.LBrDiv


