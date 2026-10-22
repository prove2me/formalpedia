-- Prove2me | Definitions.Def_LPCA_Proofs_BassLyubeznik_BassStatic_signed_dLin_idxCongr_Defs
-- name    : LPCA_Proofs_BassLyubeznik_BassStatic_signed_dLin_idxCongr_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:37:35.344171+00:00
-- url     : https://prove2.me/theorems/8d6f2c0c-00e3-45a4-b3c0-5d9f5567690d
-- title:
--   Degree-offset changes commute with the differential
-- statement:
--   This bundle supplies degree-offset changes commute with the differential. These selected declarations concern field-valued signed cochains on finite vertex types, with integer cardinality offsets and ordinary restriction maps. The signed complex assumes a convex family. Restriction commutes with its differential under the stated relative downward-closure hypothesis, not for an arbitrary subfamily. Offset minus one retains the empty face in degree minus one, and offset changes introduce no categorical-shift sign.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Proofs/BassLyubeznik/BassStatic/signed_dLin_idxCongr.lean, selected declarations in lines 41–48; source SHA-256 e6272006030b455811ecd192d5857bce7a036607a73457968c6d6f4980f5ca6f; source certificate Sapelo2 job 49172236.

import Mathlib
import Definitions.Def_LPCA_Proofs_BassLyubeznik_BassStatic_Common_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_BassStatic_signed_complex_d_Defs
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
theorem signed_dLin_idxCongr {𝓕 : Finset V → Prop} [DecidablePred 𝓕] {m m' n n' : ℤ}
    (h : n - m = n' - m') (h' : n + 1 - m = n' + 1 - m') (f : Signed.Idx 𝓕 m' n' → k) :
    Signed.dLin k 𝓕 m n (fun J => f (Signed.idxCongr 𝓕 h J)) =
      fun J' => Signed.dLin k 𝓕 m' n' f (Signed.idxCongr 𝓕 h' J')
-- SWARM:STATEMENT-END
:= by
  funext J'
  exact Equiv.sum_comp (Signed.idxCongr 𝓕 h) (fun J => inc k J.1 J'.1 * f J)
-- SWARM:PROOF-END

end Proofs.BassLyubeznik.BassStatic


