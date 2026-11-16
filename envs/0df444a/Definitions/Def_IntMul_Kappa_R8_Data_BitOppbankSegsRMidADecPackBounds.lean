-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSegsRMidADecPackBounds
-- name    : IntMul_Kappa_R8_Data_BitOppbankSegsRMidADecPackBounds
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T18:21:26.30755+00:00
-- url     : https://prove2.me/theorems/bd5a4676-273b-4957-8079-86ee0cc4f385
-- title:
--   SegsR midA pack simple bounds decide
-- statement:
--   # SegsR midA pack simple bounds decide
--
--   Decide-certified simple bounds on densified midAPack: piv and bp-1 < 11099, 1 ≤ bp, nf ≤ 5, tp/tb < 1771, n ≤ 61313. Later-segs midA helper only; not a full-word W1F certificate.
--
--   ## Formalization Note
--
--   Lean definition name: `IntMul_Kappa_R8_Data_BitOppbankSegsRMidADecPackBounds`.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: IntMul_Kappa_R8_Data_BitOppbankSegsRMidADecPackBounds. Later-segs midA helper only; not a full-word W1F certificate. Uses densified MidADataD.

-- Later-segs midA helper only; not a full-word W1F / segsR / preloadHits certificate.
-- Imports densified MidADataD (not raw-n MidAData).
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSegsRMidADataD

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Gen (genF genStepF mvF)
open IntMul.Kappa.R8.Bit.Oppbank.Lab (ValidOn MovesV)
open IntMul.Kappa.R8.Bit.Oppbank.Pnd (nestOK argRel isND)
open IntMul.Kappa.R8.Bit.Oppbank.QHNetRecR

theorem midAPack_simple_bounds :
    ∀ g ∈ midAPack,
      gatePiv g < 11099 ∧
      1 ≤ gateBp g ∧ gateBp g - 1 < 11099 ∧
      gateNf g ≤ 5 ∧
      gateTp g < 1771 ∧ gateTb g < 1771 ∧
      gateN g ≤ 61313 := by
  decide


