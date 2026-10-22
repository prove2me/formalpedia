-- Prove2me | Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_insert_of_gt_Defs
-- name    : LPCA_Proofs_BassLyubeznik_SignedCore_nu_insert_of_gt_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:19:27.320341+00:00
-- url     : https://prove2.me/theorems/3e4c8c05-f063-45e7-a24d-a6077a48615a
-- title:
--   Predecessor counts under insertion above a vertex
-- statement:
--   This bundle supplies predecessor counts under insertion above a vertex. The declarations concern finite subsets of linearly ordered vertex types, with field-valued signs where used. Cancellation and square-zero statements retain their convex-family hypotheses; the contraction identity requires family membership to be invariant under insertion of the chosen vertex. No contraction of an arbitrary subset family is asserted.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Proofs/BassLyubeznik/SignedCore/nu_insert_of_gt.lean, selected declarations in lines 19–23; source SHA-256 8269a07c2a3aeff257db00679d9b22f8a12281b1f1c3e266033ddc1050e4439b; source certificate Sapelo2 job 49172236.

import Mathlib
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_Common_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_eps_insert_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_eps_mul_self_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_eq_zero_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_insert_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_erase_self_Defs

namespace Proofs.BassLyubeznik.SignedCore

open Finset

variable {V : Type*} [LinearOrder V] {k : Type*} [Field k]

-- SWARM:HELPERS-BEGIN

-- SWARM:HELPERS-END
-- SWARM:STATEMENT-BEGIN
theorem nu_insert_of_gt {J : Finset V} {a b : V} (hab : b < a) :
    nu (insert a J) b = nu J b
-- SWARM:STATEMENT-END
:= by
  rw [nu, nu, Finset.filter_insert, if_neg (not_lt.mpr hab.le)]
-- SWARM:PROOF-END

end Proofs.BassLyubeznik.SignedCore


