-- Prove2me | Definitions.Def_LPCA_Proofs_BassLyubeznik_SrFamily_faceFamily_of_subset_Defs
-- name    : LPCA_Proofs_BassLyubeznik_SrFamily_faceFamily_of_subset_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:33:26.970299+00:00
-- url     : https://prove2.me/theorems/0e3fc0b7-2ee5-459b-8767-b3ba80b53b6e
-- title:
--   Face-family membership under inclusion
-- statement:
--   This bundle supplies face-family membership under inclusion. These are declarations about finite downward-closed face families and their selected index predicates, including the distinct void and {empty face} complexes. The Koszul-family predicate is combinatorial support data; it does not itself construct a polynomial resolution or assert exactness.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Proofs/BassLyubeznik/SrFamily/faceFamily_of_subset.lean, selected declarations in lines 20–24; source SHA-256 658c69dc7fd369bf340579b6c2bba63aeb09371c891aaef9eb847a37a6b85c2e; source certificate Sapelo2 job 49172236.

import Mathlib
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_Common_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_eps_insert_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_eps_mul_self_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_exists_insert_of_inc_ne_zero_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_hc_inc_sum_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_eq_zero_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_inc_sum_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_insert_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_erase_self_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_insert_of_gt_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_insert_of_lt_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_sdiff_add_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SrFamily_Common_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SrFamily_faceFamily_convex_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SrFamily_faceFamily_mono_Defs

namespace Proofs.BassLyubeznik.SrFamily

open Finset Proofs.BassLyubeznik.SignedCore

universe u

variable {V : Type u} [LinearOrder V] [Fintype V]

-- SWARM:HELPERS-BEGIN

-- SWARM:HELPERS-END
-- SWARM:STATEMENT-BEGIN
theorem faceFamily_of_subset {K' K : SComplex V} (h : K' ≤ K) {τ τ' : Finset V}
    (hττ' : τ ⊆ τ') (hτ' : faceFamily K' τ') (hτ : faceFamily K τ) : faceFamily K' τ
-- SWARM:STATEMENT-END
:= by
  exact K'.down_closed hτ' hττ'
-- SWARM:PROOF-END

end Proofs.BassLyubeznik.SrFamily


