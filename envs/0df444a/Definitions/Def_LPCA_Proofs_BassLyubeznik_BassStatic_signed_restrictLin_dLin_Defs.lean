-- Prove2me | Definitions.Def_LPCA_Proofs_BassLyubeznik_BassStatic_signed_restrictLin_dLin_Defs
-- name    : LPCA_Proofs_BassLyubeznik_BassStatic_signed_restrictLin_dLin_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:38:14.740215+00:00
-- url     : https://prove2.me/theorems/c462a8a2-b8e0-4889-b7c2-c604f794e98b
-- title:
--   Restriction commutes with incidence under relative downward closure
-- statement:
--   This bundle supplies restriction commutes with incidence under relative downward closure. These selected declarations concern field-valued signed cochains on finite vertex types, with integer cardinality offsets and ordinary restriction maps. The signed complex assumes a convex family. Restriction commutes with its differential under the stated relative downward-closure hypothesis, not for an arbitrary subfamily. Offset minus one retains the empty face in degree minus one, and offset changes introduce no categorical-shift sign.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Proofs/BassLyubeznik/BassStatic/signed_restrictLin_dLin.lean, selected declarations in lines 43–64; source SHA-256 70561555311b8a6220d4001276796f2d135a0a4f2d91139a8b533f1a479d97da; source certificate Sapelo2 job 49172236.

import Mathlib
import Definitions.Def_LPCA_Proofs_BassLyubeznik_BassStatic_Common_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_BassStatic_signed_complex_d_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_BassStatic_signed_dLin_idxCongr_Defs
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
theorem signed_restrictLin_dLin {𝓕 𝓕' : Finset V → Prop} [DecidablePred 𝓕] [DecidablePred 𝓕']
    (m n : ℤ) (h𝓕 : ∀ J, 𝓕' J → 𝓕 J)
    (hrel : ∀ ⦃J J' : Finset V⦄, J ⊆ J' → 𝓕' J' → 𝓕 J → 𝓕' J)
    (f : Signed.Idx 𝓕 m n → k) :
    Signed.restrictLin k 𝓕 m h𝓕 (n + 1) (Signed.dLin k 𝓕 m n f) =
      Signed.dLin k 𝓕' m n (Signed.restrictLin k 𝓕 m h𝓕 n f)
-- SWARM:STATEMENT-END
:= by
  funext J'
  change ∑ J : Signed.Idx 𝓕 m n, inc k J.1 J'.1 * f J =
    ∑ J : Signed.Idx 𝓕' m n, inc k J.1 J'.1 * f ⟨J.1, h𝓕 J.1 J.2.1, J.2.2⟩
  symm
  refine Fintype.sum_of_injective (fun J : Signed.Idx 𝓕' m n => (⟨J.1, h𝓕 J.1 J.2.1, J.2.2⟩ :
    Signed.Idx 𝓕 m n)) ?_ _ _ ?_ (fun _ => rfl)
  · intro a b hab
    exact Subtype.ext (congrArg Subtype.val hab :)
  · intro J hJ
    by_contra hne
    have hinc := left_ne_zero_of_mul hne
    obtain ⟨j, -, hj⟩ := exists_insert_of_inc_ne_zero hinc
    have hsub : J.1 ⊆ J'.1 := hj ▸ Finset.subset_insert j J.1
    exact hJ ⟨⟨J.1, hrel hsub J'.2.1 J.2.1, J.2.2⟩, rfl⟩
-- SWARM:PROOF-END

end Proofs.BassLyubeznik.BassStatic


