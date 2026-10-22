-- Prove2me | Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_exists_insert_of_inc_ne_zero_Defs
-- name    : LPCA_Proofs_BassLyubeznik_SignedCore_exists_insert_of_inc_ne_zero_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:23:47.688174+00:00
-- url     : https://prove2.me/theorems/bdd266be-ab5a-45e8-86cf-4bb0055f1f7a
-- title:
--   Insertion pattern forced by nonzero incidence
-- statement:
--   This bundle supplies insertion pattern forced by nonzero incidence. The declarations concern finite subsets of linearly ordered vertex types, with field-valued signs where used. Cancellation and square-zero statements retain their convex-family hypotheses; the contraction identity requires family membership to be invariant under insertion of the chosen vertex. No contraction of an arbitrary subset family is asserted.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Proofs/BassLyubeznik/SignedCore/exists_insert_of_inc_ne_zero.lean, selected declarations in lines 22–27; source SHA-256 09dceac0bc104cfb35d829254d661ee039c7ecaebc28119388b6432e37eac46a; source certificate Sapelo2 job 49172236.

import Mathlib
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_Common_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_eps_insert_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_eps_mul_self_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_eq_zero_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_insert_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_erase_self_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_insert_of_gt_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_insert_of_lt_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_sdiff_add_Defs

namespace Proofs.BassLyubeznik.SignedCore

open Finset

variable {V : Type*} [LinearOrder V] {k : Type*} [Field k]

-- SWARM:HELPERS-BEGIN

-- SWARM:HELPERS-END
-- SWARM:STATEMENT-BEGIN
theorem exists_insert_of_inc_ne_zero {J J' : Finset V} (h : inc k J J' ≠ 0) :
    ∃ j, j ∉ J ∧ J' = insert j J
-- SWARM:STATEMENT-END
:= by
  by_contra hcon
  exact h (inc_eq_zero hcon)
-- SWARM:PROOF-END

end Proofs.BassLyubeznik.SignedCore


