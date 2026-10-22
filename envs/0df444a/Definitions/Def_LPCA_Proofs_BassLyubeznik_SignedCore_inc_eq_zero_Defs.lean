-- Prove2me | Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_eq_zero_Defs
-- name    : LPCA_Proofs_BassLyubeznik_SignedCore_inc_eq_zero_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:13:15.936903+00:00
-- url     : https://prove2.me/theorems/60238978-201f-4c66-86bc-e2d4e29e404f
-- title:
--   Vanishing patterns of signed incidence coefficients
-- statement:
--   This bundle supplies vanishing patterns of signed incidence coefficients. The declarations concern finite subsets of linearly ordered vertex types, with field-valued signs where used. Cancellation and square-zero statements retain their convex-family hypotheses; the contraction identity requires family membership to be invariant under insertion of the chosen vertex. No contraction of an arbitrary subset family is asserted.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Proofs/BassLyubeznik/SignedCore/inc_eq_zero.lean, selected declarations in lines 16–23; source SHA-256 4456e2e9bd632638c3d14bae9cee9c8073f2c8dde3e3a397c000c908cb2695dc; source certificate Sapelo2 job 49172236.

import Mathlib
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_Common_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_eps_insert_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_eps_mul_self_Defs

namespace Proofs.BassLyubeznik.SignedCore

open Finset

variable {V : Type*} [LinearOrder V] {k : Type*} [Field k]

-- SWARM:HELPERS-BEGIN

-- SWARM:HELPERS-END
-- SWARM:STATEMENT-BEGIN
theorem inc_eq_zero {J J' : Finset V} (h : ¬ ∃ j, j ∉ J ∧ J' = insert j J) :
    inc k J J' = 0
-- SWARM:STATEMENT-END
:= by
  rw [inc, if_neg]
  rintro ⟨hsub, hcard⟩
  obtain ⟨a, ha, hins⟩ := Finset.exists_eq_insert_iff.2 ⟨hsub, hcard.symm⟩
  exact h ⟨a, ha, hins.symm⟩
-- SWARM:PROOF-END

end Proofs.BassLyubeznik.SignedCore


