-- Prove2me | Definitions.Def_Sendov_Analytic_Origin
-- name    : Sendov_Analytic_Origin
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T18:54:36.219355+00:00
-- url     : https://prove2.me/theorems/de6d6d7d-4204-45b8-b671-5ab61acc87be
-- title:
--   Origin
-- statement:
--   Definitions and structural lemmas for Origin, from Terence Tao (teorth/sendov; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Sendov's conjecture and the Phelps-Rodriguez conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/Origin.lean

import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Maclaurin
import Definitions.Def_Sendov_Analytic_Defect
import Definitions.Def_Sendov_Common_Quadratic
import Definitions.Def_Sendov_Analytic_Polar
set_option autoImplicit false
namespace Sendov
open scoped Classical in
/-- `∑ⱼ ∏_{k≠j} f(sₖ)`, as a sum over erasures of `s`. -/
noncomputable def sumEraseProdMap {α : Type*} (s : Multiset α) (f : α → ℝ) : ℝ :=
  (s.map (fun j => ((s.erase j).map f).prod)).sum
open scoped Classical in
/-- `∑ⱼ g(qⱼ) ∏_{k≠j} f(q_k)`, the weighted erasure sum over `ℂ`.  Taking `g = id` gives the
derivative of a product; taking `g = (· ^ 2)` gives the residual left after the main term is
split off. -/
noncomputable def sumEraseProdC (s : Multiset ℂ) (g f : ℂ → ℂ) : ℂ :=
  (s.map (fun j => g j * ((s.erase j).map f).prod)).sum
noncomputable def Fprod (a : ℝ) (q : Multiset ℂ) (t : ℝ) : ℂ :=
  (q.map (fun v => 1 - (a : ℂ) * (t : ℂ) * v)).prod
end Sendov


