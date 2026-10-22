-- Prove2me | Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_insert_Defs
-- name    : LPCA_Proofs_BassLyubeznik_SignedCore_inc_insert_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:14:16.184208+00:00
-- url     : https://prove2.me/theorems/86e46ce7-b5a8-4112-98bc-1bc7b04fd4f6
-- title:
--   Signed incidence for insertion of one vertex
-- statement:
--   This bundle supplies signed incidence for insertion of one vertex. The declarations concern finite subsets of linearly ordered vertex types, with field-valued signs where used. Cancellation and square-zero statements retain their convex-family hypotheses; the contraction identity requires family membership to be invariant under insertion of the chosen vertex. No contraction of an arbitrary subset family is asserted.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Proofs/BassLyubeznik/SignedCore/inc_insert.lean, selected declarations in lines 17–23; source SHA-256 60dc7cf439563f4be7e2bbe355af3d0eb15b39aedf3e5e71ab31e2f7d165216f; source certificate Sapelo2 job 49172236.

import Mathlib
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_Common_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_eps_insert_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_eps_mul_self_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_eq_zero_Defs

namespace Proofs.BassLyubeznik.SignedCore

open Finset

variable {V : Type*} [LinearOrder V] {k : Type*} [Field k]

-- SWARM:HELPERS-BEGIN

-- SWARM:HELPERS-END
-- SWARM:STATEMENT-BEGIN
theorem inc_insert {J : Finset V} {j : V} (hj : j ∉ J) :
    inc k J (insert j J) = (-1 : k) ^ nu J j
-- SWARM:STATEMENT-END
:= by
  have hsub : J ⊆ insert j J := Finset.subset_insert j J
  have hcard : (insert j J).card = J.card + 1 := Finset.card_insert_of_notMem hj
  rw [inc, if_pos ⟨hsub, hcard⟩, Finset.insert_sdiff_cancel hj, Finset.sum_singleton]
-- SWARM:PROOF-END

end Proofs.BassLyubeznik.SignedCore


