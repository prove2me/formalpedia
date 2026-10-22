-- Prove2me | Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_erase_self_Defs
-- name    : LPCA_Proofs_BassLyubeznik_SignedCore_nu_erase_self_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:15:02.790009+00:00
-- url     : https://prove2.me/theorems/6249a88e-b53d-4ff5-b94e-17ee7817fd3b
-- title:
--   Predecessor counts after erasing a vertex
-- statement:
--   This bundle supplies predecessor counts after erasing a vertex. The declarations concern finite subsets of linearly ordered vertex types, with field-valued signs where used. Cancellation and square-zero statements retain their convex-family hypotheses; the contraction identity requires family membership to be invariant under insertion of the chosen vertex. No contraction of an arbitrary subset family is asserted.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Proofs/BassLyubeznik/SignedCore/nu_erase_self.lean, selected declarations in lines 18–23; source SHA-256 9379642647c28b8728c05286e08efcf6ae79c98cf65066e8906e490535be16ac; source certificate Sapelo2 job 49172236.

import Mathlib
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_Common_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_eps_insert_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_eps_mul_self_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_eq_zero_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_insert_Defs

namespace Proofs.BassLyubeznik.SignedCore

open Finset

variable {V : Type*} [LinearOrder V] {k : Type*} [Field k]

-- SWARM:HELPERS-BEGIN

-- SWARM:HELPERS-END
-- SWARM:STATEMENT-BEGIN
theorem nu_erase_self {J : Finset V} {j : V} :
    nu (J.erase j) j = nu J j
-- SWARM:STATEMENT-END
:= by
  have hj : j ∉ J.filter (· < j) := by simp
  rw [nu, nu, Finset.filter_erase, Finset.erase_eq_of_notMem hj]
-- SWARM:PROOF-END

end Proofs.BassLyubeznik.SignedCore


