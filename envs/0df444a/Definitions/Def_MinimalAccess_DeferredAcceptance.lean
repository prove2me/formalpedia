-- Prove2me | Definitions.Def_MinimalAccess_DeferredAcceptance
-- name    : MinimalAccess_DeferredAcceptance
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:43:19.535209+00:00
-- url     : https://prove2.me/theorems/cb6ad5f1-7cec-4dc5-90a8-20d935af5313
-- title:
--   The deferred acceptance mechanism $\gamma$ based on adjusted priorities
-- statement:
--   Let $(P,\succ,r)$ be a problem. The (student-proposing) **deferred acceptance algorithm based on adjusted priorities** runs as follows. *Step 0.* Compute $\succ^r$. *Step 1.* Each student proposes to her most preferred acceptable school (or to $\emptyset$). Each school $s$ tentatively accepts, up to its capacity $q_s$, the proposers with highest $\succ^r_s$-priority and rejects the others; $\emptyset$ accepts every proposal. *Steps 2, ….* Each student rejected at the previous step proposes to her next most preferred acceptable school (or $\emptyset$); each school considers its tentatively accepted students together with its new proposers, keeps the best $q_s$ of them according to $\succ^r_s$ and rejects the rest. The algorithm stops when every student is tentatively matched or has been rejected by all her acceptable schools. The resulting matching is $\gamma(P,\succ,r)=\gamma(P,\succ^r)$, and the mechanism $\gamma$ that always selects it is the **(minimal-access adjusted) deferred acceptance mechanism**.
--
--   This is the mechanism that Theorem 1 characterizes.
--
--   **Formalization Note** The algorithm is the published simultaneous applicant-proposing deferred acceptance `GaleShapley1962.Admissions.Market.deferredAcceptance` (a fuel-bounded run of rounds), applied to the market whose applicant lists are the students' acceptable schools sorted best first, whose college lists contain **all** students sorted by the priority keys (schools find all students acceptable, Remark 2), and whose quotas are $q$. `daKey q P key` is the classical outcome $\gamma(P,\text{key})$ and `gamma q P pri r = daKey q P (adjKey pri r)`.
-- source:
--   Klaus–Klijn, Minimal-Access Rights in School Choice and the Deferred Acceptance Mechanism, BSE Working Paper 1264 (rev. July 2023), §2, pp.6–7 (Steps 0, 1, 2, … of the algorithm) and p.11 (the mechanism γ)

import Mathlib
import Definitions.Def_GaleShapley1962_Admissions_Procedure
import Definitions.Def_MinimalAccess_AdjustedPriorities

namespace MinimalAccess

/-!
Klaus–Klijn, *Minimal-Access Rights in School Choice and the Deferred Acceptance Mechanism*,
BSE Working Paper 1264 (rev. July 2023), pp.6–7 and p.11: the (student-proposing) deferred
acceptance algorithm based on adjusted priorities. "Step 0. Using ≻ and r, compute ≻^r.
Step 1. Each student i proposes to the acceptable school she most prefers or the no-school
option (according to P_i). Among all proposers, up to its capacity, each school s tentatively
assigns its seats to students who have highest priority according to ≻^r_s and rejects all
other proposers. The no-school option accepts all proposals it receives. Steps 2, …. Each
student i who was rejected at the previous step proposes to her next most preferred acceptable
school or the no-school option (according to P_i). Each school s considers the proposers she
tentatively accepted (if any) and all current proposers. Among these students, up to its
capacity, school s tentatively assigns its seats to the students who have highest priority
according to ≻^r_s and rejects all other proposers. The no-school option accepts all proposals
it receives. The algorithm stops when each student is either tentatively matched or has been
rejected by all her acceptable schools; we denote the resulting matching by γ(P, ≻, r)." (p.11:
"The mechanism that always assigns the matching obtained by the (student-proposing) deferred
acceptance algorithm based on adjusted priorities is called (minimal-access adjusted) deferred
acceptance mechanism and denoted by γ.")

**Formalization Note.** The algorithm is the published simultaneous applicant-proposing
deferred acceptance `GaleShapley1962.Admissions.Market.deferredAcceptance` (a fuel-bounded run
of rounds, each round exactly Steps 1/2 above), applied to the market whose applicant lists are
the students' acceptable schools, best first, whose college lists are **all** students ordered
by the priority keys (schools find all students acceptable, Remark 2, p.6), and whose quotas
are `q`. `daKey q P key` is the classical deferred acceptance outcome `γ(P, key)`, and
`gamma q P pri r := daKey q P (adjKey pri r)` is `γ(P, ≻, r) = γ(P, ≻^r)`. Students are
`Fin n`, schools `Fin m`, and `none` is the no-school option.
-/

open GaleShapley1962.Admissions

/-- Student `i`'s acceptable schools, most preferred first (ranks of `P i`). -/
def applicantList {n m : ℕ} (P : Fin n → Pref m) (i : Fin n) : List (Fin m) :=
  List.insertionSort (fun a b => P i (some a) ≤ P i (some b))
    ((List.finRange m).filter fun s => decide (Acceptable P i s))

/-- All students, ordered by school `s`'s keys (smallest key, i.e. highest priority, first). -/
def collegeList {n m : ℕ} (key : Fin m → Fin n → ℕ) (s : Fin m) : List (Fin n) :=
  List.insertionSort (fun a b => key s a ≤ key s b) (List.finRange n)

/-- The admissions market of the classical school choice problem `(P, key)` with capacities
`q`. -/
def toMarket {n m : ℕ} (q : Fin m → ℕ) (P : Fin n → Pref m) (key : Fin m → Fin n → ℕ) :
    Market n m where
  applicantList := applicantList P
  collegeList := collegeList key
  applicant_nodup := fun _ =>
    (List.perm_insertionSort _ _).nodup_iff.mpr ((List.nodup_finRange m).filter _)
  college_nodup := fun _ => (List.perm_insertionSort _ _).nodup_iff.mpr (List.nodup_finRange n)
  quota := q

/-- The classical (student-proposing) deferred acceptance outcome `γ(P, key)` with capacities
`q` and priority keys `key`. -/
def daKey {n m : ℕ} (q : Fin m → ℕ) (P : Fin n → Pref m) (key : Fin m → Fin n → ℕ) :
    Assignment n m :=
  (toMarket q P key).deferredAcceptance

/-- The (minimal-access adjusted) deferred acceptance mechanism `γ` (p.11):
`γ(P, ≻, r) = γ(P, ≻^r)`. -/
def gamma {n m : ℕ} (q : Fin m → ℕ) (P : Fin n → Pref m) (pri : Fin m → Prio n)
    (r : Fin n → Finset (Fin m)) : Assignment n m :=
  daKey q P (adjKey pri r)

end MinimalAccess


