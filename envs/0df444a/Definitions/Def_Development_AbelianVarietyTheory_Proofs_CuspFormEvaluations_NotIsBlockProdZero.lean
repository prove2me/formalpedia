-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_NotIsBlockProdZero
-- name    : Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_NotIsBlockProdZero
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T00:51:05.108795+00:00
-- url     : https://prove2.me/theorems/48a4a8c6-a1b3-4aef-93de-afce69830c54
-- title:
--   Not Is Block Prod Zero
-- statement:
--   Definitions and structural lemmas for Not Is Block Prod Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/NotIsBlockProdZero.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_IsBlockProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.BlockThInhab
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.BlockTh
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H) (n : ℕ)
def lead (τ : E →+* ℂ) (i : ℕ) (hi : i ≤ Dw.mult τ) (hn : i ≤ n) (c : ℕ) (hc : 1 ≤ c) : Bk Dw n :=
  ⟨τ, i, hi, c, hc, Fin.castLE hn, Fin.castLE_injective hn⟩
end GlobalTheory.BlockThInhab


