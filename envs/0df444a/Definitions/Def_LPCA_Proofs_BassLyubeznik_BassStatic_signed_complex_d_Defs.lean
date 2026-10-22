-- Prove2me | Definitions.Def_LPCA_Proofs_BassLyubeznik_BassStatic_signed_complex_d_Defs
-- name    : LPCA_Proofs_BassLyubeznik_BassStatic_signed_complex_d_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:36:31.046019+00:00
-- url     : https://prove2.me/theorems/161dea8b-07ea-4434-8541-21b3a2cb7c60
-- title:
--   Component formula for the signed cochain differential
-- statement:
--   This bundle supplies component formula for the signed cochain differential. These selected declarations concern field-valued signed cochains on finite vertex types, with integer cardinality offsets and ordinary restriction maps. The signed complex assumes a convex family. Restriction commutes with its differential under the stated relative downward-closure hypothesis, not for an arbitrary subfamily. Offset minus one retains the empty face in degree minus one, and offset changes introduce no categorical-shift sign.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Proofs/BassLyubeznik/BassStatic/signed_complex_d.lean, selected declarations in lines 40–44; source SHA-256 6f7f587c72c722bca27ed9f684034ee7ebb6ddb20fae56287b75b5fcb468e33b; source certificate Sapelo2 job 49172236.

import Mathlib
import Definitions.Def_LPCA_Proofs_BassLyubeznik_BassStatic_Common_Defs
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
theorem signed_complex_d {𝓕 : Finset V → Prop} [DecidablePred 𝓕] (hconv : IsConvex 𝓕)
    (m n : ℤ) : (Signed.complex k 𝓕 m hconv).d n (n + 1) = ModuleCat.ofHom (Signed.dLin k 𝓕 m n)
-- SWARM:STATEMENT-END
:= by
  simp [Signed.complex]
-- SWARM:PROOF-END

end Proofs.BassLyubeznik.BassStatic


