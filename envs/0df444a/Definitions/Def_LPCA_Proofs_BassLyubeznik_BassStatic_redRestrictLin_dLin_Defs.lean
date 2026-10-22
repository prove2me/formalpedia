-- Prove2me | Definitions.Def_LPCA_Proofs_BassLyubeznik_BassStatic_redRestrictLin_dLin_Defs
-- name    : LPCA_Proofs_BassLyubeznik_BassStatic_redRestrictLin_dLin_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:39:16.171483+00:00
-- url     : https://prove2.me/theorems/59a1ce79-de89-4229-84ee-7f8c900803cb
-- title:
--   Restriction commutes with the reduced cochain differential
-- statement:
--   This bundle supplies restriction commutes with the reduced cochain differential. These selected declarations concern field-valued signed cochains on finite vertex types, with integer cardinality offsets and ordinary restriction maps. The signed complex assumes a convex family. Restriction commutes with its differential under the stated relative downward-closure hypothesis, not for an arbitrary subfamily. Offset minus one retains the empty face in degree minus one, and offset changes introduce no categorical-shift sign.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Proofs/BassLyubeznik/BassStatic/redRestrictLin_dLin.lean, selected declarations in lines 47–53; source SHA-256 c482b9e56a59b1fd0c45b48595e125d1450efc36fcc8b6d3d89f4137003434fb; source certificate Sapelo2 job 49172236.

import Mathlib
import Definitions.Def_LPCA_Proofs_BassLyubeznik_BassStatic_Common_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_BassStatic_signed_complex_d_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_BassStatic_signed_dLin_idxCongr_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_BassStatic_signed_restrictLin_dLin_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_Common_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_dd_sum_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_eps_insert_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_eps_mul_self_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_exists_insert_of_inc_ne_zero_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_hc_inc_sum_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_eq_zero_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_inc_sum_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_insert_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_sdiff_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_erase_self_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_insert_of_gt_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_insert_of_lt_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_sdiff_add_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SrFamily_Common_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SrFamily_faceFamily_convex_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SrFamily_faceFamily_mono_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SrFamily_faceFamily_of_subset_Defs

namespace Proofs.BassLyubeznik.BassStatic

open Finset CategoryTheory CategoryTheory.Limits Proofs.BassLyubeznik.SignedCore Proofs.BassLyubeznik.SrFamily

universe u v

variable {V : Type u} [LinearOrder V] [Fintype V] (k : Type v) [Field k]

-- SWARM:HELPERS-BEGIN

-- SWARM:HELPERS-END
-- SWARM:STATEMENT-BEGIN
theorem redRestrictLin_dLin {K' K : SComplex V} (h : K' ≤ K) (m n : ℤ)
    (f : Signed.Idx (faceFamily K) m n → k) :
    redRestrictLin k h m (n + 1) (Signed.dLin k (faceFamily K) m n f) =
      Signed.dLin k (faceFamily K') m n (redRestrictLin k h m n f)
-- SWARM:STATEMENT-END
:= by
  exact signed_restrictLin_dLin k m n (faceFamily_mono h) (fun τ τ' => faceFamily_of_subset h) f
-- SWARM:PROOF-END

end Proofs.BassLyubeznik.BassStatic


