-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_StripDataTensorColumnFamilies
-- name    : Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_StripDataTensorColumnFamilies
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T11:05:55.792621+00:00
-- url     : https://prove2.me/theorems/d7a4b143-4eb9-4ad7-a544-056e1b67d6d9
-- title:
--   Strip Data Tensor Column Families
-- statement:
--   Definitions and structural lemmas for Strip Data Tensor Column Families, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/StripDataTensorColumnFamilies.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QxFstInj
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qx_equiv
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qx_indep
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qx_rank

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
namespace Formalism.InvariantFactorPaths.ColumnFamilies
def qx_colFam {n : ℕ} [NeZero n] {κ : Type} [Fintype κ] [DecidableEq κ] {B : Matrix κ κ (GLCoord ℤ n)}
    {be : κ → Fin n → ℤ} {Str : (Fin n → ℤ) → Finset (Fin n → ℤ)}
    {ps : (mu nu : Fin n → ℤ) → Matrix (TIdx mu × κ) (TIdx nu) ℤ} (hd : IsStripData B be Str ps)
    {M M' : GLMod n} (e : M'.ι ≃ M.ι × κ) (hT : IsTensor M M' B e) (CF : ColFam M) : ColFam M' where
  J := qx_J Str CF
  mu := fun x => (x.2 : Fin n → ℤ)
  dom := fun x => hd.2.2.1 _ (CF.dom x.1) _ x.2.2
  ph := qx_ph ps e CF
  equiv := fun x => by
    ext i I
    exact qx_equiv hd e hT CF x i I
  indepP := fun p hp nu => by
    have := Fact.mk hp
    exact qx_indep hd e CF (ZMod p) nu
  indepQ := fun nu => qx_indep hd e CF ℚ nu
  rank := qx_rank hd e CF
end Formalism.InvariantFactorPaths.ColumnFamilies


