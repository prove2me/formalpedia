-- Prove2me | Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_insert_of_lt_Defs
-- name    : LPCA_Proofs_BassLyubeznik_SignedCore_nu_insert_of_lt_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:20:58.110879+00:00
-- url     : https://prove2.me/theorems/3ca2b7c4-4abb-41ce-b6c0-2c230683cb14
-- title:
--   Predecessor counts under insertion below a vertex
-- statement:
--   This bundle supplies predecessor counts under insertion below a vertex. The declarations concern finite subsets of linearly ordered vertex types, with field-valued signs where used. Cancellation and square-zero statements retain their convex-family hypotheses; the contraction identity requires family membership to be invariant under insertion of the chosen vertex. No contraction of an arbitrary subset family is asserted.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Proofs/BassLyubeznik/SignedCore/nu_insert_of_lt.lean, selected declarations in lines 20–25; source SHA-256 d2b566c1c84d9a82877b3956b6926dea9158730e783e9eeb5ae943c2d1e99b35; source certificate Sapelo2 job 49172236.

import Mathlib
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_Common_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_eps_insert_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_eps_mul_self_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_eq_zero_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_insert_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_erase_self_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_insert_of_gt_Defs

namespace Proofs.BassLyubeznik.SignedCore

open Finset

variable {V : Type*} [LinearOrder V] {k : Type*} [Field k]

-- SWARM:HELPERS-BEGIN

-- SWARM:HELPERS-END
-- SWARM:STATEMENT-BEGIN
theorem nu_insert_of_lt {J : Finset V} {a b : V} (ha : a ∉ J) (hab : a < b) :
    nu (insert a J) b = nu J b + 1
-- SWARM:STATEMENT-END
:= by
  have h : a ∉ J.filter (· < b) := fun h => ha (Finset.mem_filter.mp h).1
  rw [nu, nu, Finset.filter_insert, if_pos hab, Finset.card_insert_of_notMem h]
-- SWARM:PROOF-END

end Proofs.BassLyubeznik.SignedCore


