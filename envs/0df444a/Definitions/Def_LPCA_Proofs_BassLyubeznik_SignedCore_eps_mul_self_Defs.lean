-- Prove2me | Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_eps_mul_self_Defs
-- name    : LPCA_Proofs_BassLyubeznik_SignedCore_eps_mul_self_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:12:39.819767+00:00
-- url     : https://prove2.me/theorems/cbd3256a-3957-4772-86ed-c690bbea363b
-- title:
--   Orientation signs square to one
-- statement:
--   This bundle supplies orientation signs square to one. The declarations concern finite subsets of linearly ordered vertex types, with field-valued signs where used. Cancellation and square-zero statements retain their convex-family hypotheses; the contraction identity requires family membership to be invariant under insertion of the chosen vertex. No contraction of an arbitrary subset family is asserted.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Proofs/BassLyubeznik/SignedCore/eps_mul_self.lean, selected declarations in lines 14–17; source SHA-256 6df3f4ca3d3fa27751a66c9d1650a637b5c2022a92198b769f26ef1e00b96cf0; source certificate Sapelo2 job 49172236.

import Mathlib
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_Common_Defs

namespace Proofs.BassLyubeznik.SignedCore

open Finset

variable {V : Type*} [LinearOrder V] {k : Type*} [Field k]

-- SWARM:HELPERS-BEGIN

-- SWARM:HELPERS-END
-- SWARM:STATEMENT-BEGIN
theorem eps_mul_self (G τ : Finset V) : eps k G τ * eps k G τ = 1
-- SWARM:STATEMENT-END
:= by
  rw [eps, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
-- SWARM:PROOF-END

end Proofs.BassLyubeznik.SignedCore


