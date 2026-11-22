-- Prove2me | Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SecondPriceSumWeightsUncovered
-- name    : Formalism_SizeWindowBrackets_ChainSlopeWindows_SecondPriceSumWeightsUncovered
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:57:24.644718+00:00
-- url     : https://prove2.me/theorems/bdf8c971-7f73-4e16-867c-232db16f0706
-- title:
--   Second Price Sum Weights Uncovered
-- statement:
--   Definitions and structural lemmas for Second Price Sum Weights Uncovered, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/SecondPriceSumWeightsUncovered.lean

import Definitions.Def_Formalism_SizeWindowBrackets_TranslateWordBoundHypotheses
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe
import Definitions.Def_Formalism_LogVandermondeBounds_HookGammaAmgmMultinomialBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Real
namespace Formalism.LFunctionChainParameters.SectionsFourToSixTransfer
open Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LatticeToWeightTransfer
section
variable {U0 : Type} {W : U0 → Type} {Top : Type} {m f : ℕ}
end
namespace Model
noncomputable def gv : ℝ := Real.exp 1 ^ (-(2 / (((2 : ℕ) : ℝ) * Real.exp 2)))
noncomputable def Xv : ∀ _ : Unit, Fin 2 → ℝ := fun _ u => Real.exp (13 + ((u : ℕ) : ℝ))
noncomputable def D0 : Data Unit (fun _ => Fin 2) Unit 6 2 where
  x := 6
  ε := 1
  a := Real.exp 40
  b := Real.exp 4
  b' := Real.exp 2
  k := Real.exp 2
  L := 4
  La := 100
  B0 := 2 * 6 * Real.exp 4 * 4
  Nc := 0
  gam := 0
  LpL := 0
  v := π
  lg := 0
  logGam := 1
  aT := fun _ => Real.exp 40
  w := fun _ _ _ => 1
  d := fun _ _ => 1
  T := fun _ u => Xv () u * gv
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
  HH := fun _ => 0
  del := fun _ => 0
  η := fun _ => 0
  e := fun _ => 0
  delBar := 0
  etaBar := 0
  eBar := 0
noncomputable def D1 : Data Unit (fun _ => Fin 2) Unit 6 2 :=
  { D0 with
    muM := fun u0 u => ZiiR D0 1 1 1 (Real.log (D0.T u0 u))
    muMaxM := fun u0 u => ZiiiR D0 1 1 1 (Real.log (D0.T u0 u)) }
end Model
end Formalism.LFunctionChainParameters.SectionsFourToSixTransfer


