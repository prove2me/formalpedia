-- Prove2me | Definitions.Def_GaleShapley1962_Admissions_Procedure
-- name    : GaleShapley1962_Admissions_Procedure
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T02:41:32.613468+00:00
-- url     : https://prove2.me/theorems/be0891bb-4303-444b-93dd-7424513df4dd
-- title:
--   Simultaneous applicant-proposing deferred acceptance
-- statement:
--   Initially no applicant is held and each applicant's untried list is their permissible application list. In a round, every unheld applicant with a nonempty untried list applies to its first college. A college considers its incumbents and new applicants, orders them by its own list, retains the first quota-many, and rejects the rest. The submitted application is removed from each proposer's untried list, whether retained or rejected.
--
--   The state records the remaining lists and each applicant's current waiting-list college or unassignment. The retained lists are disjoint on the run from the initial state: incumbents do not apply and each unheld applicant makes at most one application. Decoding these lists therefore returns a unique college or unassignment. A round with no applications leaves the entire state unchanged.
--
--   The output is computed by recursion for the total number of permissible applicant-college pairs. Every productive round consumes at least one new pair, so this reaches the stop rule, with stationary padding after an earlier stop. This fuel is an implementation bound, not a rate claim in the source. No output, termination, stability, or rejection-safety assumption is supplied as market data.
-- source:
--   Gale and Shapley (1962), College Admissions and the Stability of Marriage, Section 4, printed pp. 13–14 (PDF pp. 5–6), https://doi.org/10.1080/00029890.1962.11989827

import Definitions.Def_GaleShapley1962_Admissions_Assignments

namespace GaleShapley1962.Admissions

/-- Between rounds: untried permissible lists and current waiting-list placement. -/
structure DAState (n m : ℕ) where
  remaining : Fin n → List (Fin m)
  held : Assignment n m

def Market.initial {n m : ℕ} (M : Market n m) : DAState n m :=
  ⟨M.permissible, fun _ => none⟩

/-- Only applicants not currently held apply, to their next untried college. -/
def DAState.proposal {n m : ℕ} (s : DAState n m) (a : Fin n) : Option (Fin m) :=
  if s.held a = none then (s.remaining a).head? else none

/-- The college's best `quota` candidates among incumbents and new applications. -/
def Market.retained {n m : ℕ} (M : Market n m) (s : DAState n m)
    (c : Fin m) : List (Fin n) :=
  ((M.collegeList c).filter fun a =>
    s.held a = some c ∨ s.proposal a = some c).take (M.quota c)

/-- One simultaneous round. On reachable states the retained lists are disjoint:
an incumbent cannot apply and each free applicant applies to at most one college.
Thus `find?` decodes the unique waiting-list placement, returning `none` if absent. -/
def Market.round {n m : ℕ} (M : Market n m) (s : DAState n m) : DAState n m :=
  if ∀ a, s.proposal a = none then s else
    { remaining := fun a => if (s.proposal a).isSome then (s.remaining a).tail
        else s.remaining a
      held := fun a => (List.finRange m).find? fun c => a ∈ M.retained s c }

/-- Explicit recursion from empty waiting lists. Completed runs are padded stationarily. -/
def Market.run {n m : ℕ} (M : Market n m) : ℕ → DAState n m
  | 0 => M.initial
  | k + 1 => M.round (M.run k)

/-- At most this many productive rounds: each consumes at least one previously
untried permissible pair. This is implementation fuel, not a source rate constant. -/
def Market.fuel {n m : ℕ} (M : Market n m) : ℕ :=
  ∑ a : Fin n, (M.permissible a).length

/-- Section 4's actual applicant-proposing waiting-list output. -/
def Market.deferredAcceptance {n m : ℕ} (M : Market n m) : Assignment n m :=
  (M.run M.fuel).held

end GaleShapley1962.Admissions


