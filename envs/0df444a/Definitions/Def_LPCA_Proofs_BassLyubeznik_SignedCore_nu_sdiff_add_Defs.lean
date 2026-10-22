-- Prove2me | Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_sdiff_add_Defs
-- name    : LPCA_Proofs_BassLyubeznik_SignedCore_nu_sdiff_add_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:22:17.766719+00:00
-- url     : https://prove2.me/theorems/68730877-1092-4aff-a07c-5ef3c86585e5
-- title:
--   Predecessor counts for a set difference
-- statement:
--   This bundle supplies predecessor counts for a set difference. The declarations concern finite subsets of linearly ordered vertex types, with field-valued signs where used. Cancellation and square-zero statements retain their convex-family hypotheses; the contraction identity requires family membership to be invariant under insertion of the chosen vertex. No contraction of an arbitrary subset family is asserted.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Proofs/BassLyubeznik/SignedCore/nu_sdiff_add.lean, selected declarations in lines 21–28; source SHA-256 55cb0e7b6c8465f826ff141c6e239de2c90526d12c5ab7c9285b532808d7e442; source certificate Sapelo2 job 49172236.

import Mathlib
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_Common_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_eps_insert_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_eps_mul_self_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_eq_zero_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_insert_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_erase_self_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_insert_of_gt_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_insert_of_lt_Defs

namespace Proofs.BassLyubeznik.SignedCore

open Finset

variable {V : Type*} [LinearOrder V] {k : Type*} [Field k]

-- SWARM:HELPERS-BEGIN

-- SWARM:HELPERS-END
-- SWARM:STATEMENT-BEGIN
theorem nu_sdiff_add {G J : Finset V} (hG : G ⊆ J) (j : V) :
    nu J j = nu G j + nu (J \ G) j
-- SWARM:STATEMENT-END
:= by
  have hd : Disjoint (G.filter (· < j)) ((J \ G).filter (· < j)) :=
    Finset.disjoint_filter_filter Finset.disjoint_sdiff
  rw [nu, nu, nu, ← Finset.card_union_of_disjoint hd, ← Finset.filter_union,
    Finset.union_sdiff_of_subset hG]
-- SWARM:PROOF-END

end Proofs.BassLyubeznik.SignedCore


