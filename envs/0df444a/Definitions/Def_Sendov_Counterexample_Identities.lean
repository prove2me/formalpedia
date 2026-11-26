-- Prove2me | Definitions.Def_Sendov_Counterexample_Identities
-- name    : Sendov_Counterexample_Identities
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T18:51:24.838656+00:00
-- url     : https://prove2.me/theorems/8a68718c-6baf-53ed-9cc3-09e43b4bcdf5
-- title:
--   Identities
-- statement:
--   Definitions and structural lemmas for Identities, from Terence Tao (teorth/sendov; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Sendov's conjecture and the Phelps-Rodriguez conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Counterexample/Identities.lean

import Definitions.Def_Sendov_Counterexample_Factor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
set_option autoImplicit false
namespace Sendov
open Polynomial Multiset
open scoped Classical in
/-- `∑ⱼ ∏_{k≠j} sₖ`.  This is `(∏ s) · (∑ⱼ 1/sⱼ)` with the denominators cleared, and unlike
that expression it is well defined when some `sⱼ` vanishes. -/
noncomputable def sumEraseProd (s : Multiset ℂ) : ℂ :=
  (s.map (fun j => (s.erase j).prod)).sum
variable {n : ℕ} {a c : ℂ} {z q : Multiset ℂ} {p : ℂ[X]}
end Sendov


