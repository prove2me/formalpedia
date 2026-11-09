-- Prove2me | Definitions.Def_NetworkEquilibriumCLS_LinearNash_BooleanSearch
-- name    : NetworkEquilibriumCLS_LinearNash_BooleanSearch
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:18:50.914359+00:00
-- url     : https://prove2.me/theorems/ff0ecfc2-3235-4620-afbe-70a36d5f5db7
-- title:
--   Boolean local minima and the published discrete-local-search interface
-- statement:
--   The encoded Boolean search input is an integer square-free quadratic h in a positive number n of variables. An accepted answer is an n-bit vector b with no improving single-coordinate flip:
--
--   $$h(b)\le h(b\oplus q)\quad\text{for every }q.$$
--
--   The same h is evaluated as a real polynomial in the analytic construction. Its bit answers are only the local-search alternatives and do not discretize any KKT domain. General discrete local search uses the published LocalOpt problem: two well-formed Boolean circuits supply an integer potential and a candidate neighbor, and a solution has nondecreasing potential at that neighbor. The grid construction in Lemma 3.1 is represented by such finite circuits, rather than enumerating its exponentially many points. Neighborhood and objective evaluations must be encoded by the reduction's polynomial-time construction.
--
--   These definitions connect the discrete alternative to the analytic milestones without assuming a decoder or its correctness.
-- source:
--   Ioannis Anagnostides, Ioannis Panageas, Jingming Yan, STOC 2027 submission #653 (October 2026), pp.8–9 (PDF 9–10), §3, Eq. (2), Lemmas 3.1–3.2; published ConstrSOSP.LocalOpt is the standard circuit presentation.

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Encoding
import Definitions.Def_ConstrSOSP_LocalOpt

noncomputable section

namespace NetworkEquilibriumCLS.LinearNash

/-- Single-bit local minima of an integer square-free quadratic, §3 and Eq. (2). -/
def booleanSearch : SearchProblem where
  valid x := ∃ n, 0 < n ∧ ∃ h : BooleanPolynomial n, encBoolean h = x
  answer x y := ∃ n, 0 < n ∧ ∃ h : BooleanPolynomial n, encBoolean h = x ∧
    ∃ b : Fin n → Bool, y = List.ofFn b ∧ BooleanLocalMin h (fun q => if b q then 1 else 0)

end NetworkEquilibriumCLS.LinearNash


