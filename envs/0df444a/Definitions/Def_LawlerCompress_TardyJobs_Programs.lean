-- Prove2me | Definitions.Def_LawlerCompress_TardyJobs_Programs
-- name    : LawlerCompress_TardyJobs_Programs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T16:27:12.173174+00:00
-- url     : https://prove2.me/theorems/a0ff0fb5-7a91-4770-94d5-a0ef8882a116
-- title:
--   Concrete finite programs for Algorithm 2 and sparse reconstruction
-- statement:
--   Three fixed finite programs specify the implementation. The endpoint program stable-sorts only observed processing-time groups, traverses each in reverse EDD index, and maintains a binary min-heap with the paper's priority rule. Parent addresses are initialized in linear time. Heap size divided by m is maintained by quotient and remainder counters, so the capacity comparison never scans up to d_max.
--
--   Algorithm 2 uses a table indexed in base d_max+1, with a reachability flag, weight and optional pointer per vector. Explicit digit counters enumerate t,u,r. Every successful candidate is appended before any writes for that job; the reusable update buffer is then applied. The maximum is obtained by scanning the table. With sparse reconstruction enabled, every successful candidate allocates an immutable three-cell record (job, machine, predecessor), copying the predecessor pointer before the batch writes. Equality retains the earlier candidate. Extraction scans the completed table, follows its chosen chain, writes selected jobs in increasing index on each machine, and appends all remaining jobs to machine zero.
--
--   $$\text{table cells}=(d_{\max}+1)^m,\qquad\text{record width}=3.$$
--
--   The literal layout, register conventions, sentinels, scratch arrays and procedure numbers are documented in the declaration. Helper constructors only assemble finite syntax; no host function remains as an instruction.
--
--   This code is the particular Algorithm 2 whose execution resources are asserted by Lemmas 3.4–3.5.
--
--   **Formalization Note** Procedure zero runs the DP, procedure one extracts, and procedure two computes endpoints. The null pointer is zero, unreachable table entries have a zero flag, and selected-job marks initially use −1. All costs and peak cell bounds are claims about Light.Exec.
-- source:
--   Klaus Jansen, Björn Schumacher, Corinna Wambsganz, Compressing the Lawler-Moore Dynamic Program for Weighted Tardy Jobs, STOC 2027 submission #354 (October 2026), pp. 5–8, §3.1 heap procedure, Algorithm 2, Lemmas 3.2, 3.4, 3.5 and their proofs

import Definitions.Def_LawlerCompress_TardyJobs_Interface

set_option autoImplicit false

namespace LawlerCompress.TardyJobs
open Light

/-- Syntactic assembly only. The resulting program contains no Lean callbacks. -/
def statements (ss : List Stmt) : Stmt := ss.foldr Stmt.seq .skip

def jobField (field : ℕ) (j : Expr) : Expr := M (k 2 +' k 3 *' j +' k field)

def increment (r : ℕ) : Stmt := .set r (v r +' k 1)

/-- Compare heap jobs, strictly from lower to higher priority, by weight then index. -/
def ifLower (x y : Expr) (yes no : Stmt) : Stmt :=
  .ite (jobField 2 x <' jobField 2 y) yes
    (.ite (jobField 2 x =' jobField 2 y) (.ite (x <' y) yes no) no)

/-- §3.1 implementation. Registers: 0 return; 1 m; 2 n; 3 header B;
4 endpoints A; 5 permutation; 6 merge scratch; 7 heap; 8 parents;
9 dmax; 10..29 scratch. All arrays after A have at most n+1 cells.
A=B+16. Bottom-up stable mergesort groups observed processing times only.
The binary heap is 1-based, with parents initialized in one linear pass.
The capacity test uses floor(size/m) and size mod m, maintained on insert/delete;
no division, no scan over absent p, and no scan up to dmax occurs. -/
def intervalBody : Stmt := statements [
  .set 1 (M (k 0)), .set 2 (M (k 1)),
  .set 3 (k 2 +' k 3 *' v 2), .set 4 (v 3 +' k 16),
  .set 5 (v 4 +' v 2), .set 6 (v 5 +' v 2),
  .set 7 (v 6 +' v 2), .set 8 (v 7 +' v 2 +' k 1),
  .set 9 (k 0), .set 10 (k 0),
  .while (v 10 <' v 2) (statements [
    .store (v 5 +' v 10) (v 10),
    .store (v 4 +' v 10) (jobField 0 (v 10)),
    .ite (v 9 <' jobField 1 (v 10)) (.set 9 (jobField 1 (v 10))) .skip,
    increment 10]),
  .store (v 3) (v 9), .store (v 3 +' k 1) (v 4),
  -- Parent[i]=floor(i/2), initialized without a division instruction.
  .set 10 (k 1), .set 11 (k 0), .set 12 (k 1),
  .while (v 10 ≤' v 2) (statements [
    .store (v 8 +' v 10) (v 11), increment 10,
    .ite (v 12 =' k 1) (statements [.set 12 (k 0), increment 11]) (.set 12 (k 1))]),
  -- Stable mergesort by processing time; original index order resolves ties.
  .set 10 (k 1),
  .while (v 10 <' v 2) (statements [
    .set 11 (k 0),
    .while (v 11 <' v 2) (statements [
      .set 12 (v 11 +' v 10),
      .ite (v 2 <' v 12) (.set 12 (v 2)) .skip,
      .set 13 (v 11 +' k 2 *' v 10),
      .ite (v 2 <' v 13) (.set 13 (v 2)) .skip,
      .set 14 (v 11), .set 15 (v 12), .set 16 (v 11),
      .while (v 16 <' v 13) (statements [
        .set 17 (k 0),
        .ite (v 14 <' v 12)
          (.ite (v 15 <' v 13)
            (.ite (jobField 0 (M (v 5 +' v 15)) <' jobField 0 (M (v 5 +' v 14)))
              .skip (.set 17 (k 1))) (.set 17 (k 1))) .skip,
        .ite (v 17 =' k 1)
          (statements [.store (v 6 +' v 16) (M (v 5 +' v 14)), increment 14])
          (statements [.store (v 6 +' v 16) (M (v 5 +' v 15)), increment 15]),
        increment 16]),
      .set 11 (v 13)]),
    .set 11 (k 0),
    .while (v 11 <' v 2) (statements [
      .store (v 5 +' v 11) (M (v 6 +' v 11)), increment 11]),
    .set 10 (k 2 *' v 10)]),
  -- Each maximal observed-p block is traversed backwards in original EDD index.
  .set 10 (k 0),
  .while (v 10 <' v 2) (statements [
    .set 11 (jobField 0 (M (v 5 +' v 10))),
    .set 12 (v 10 +' k 1), .set 13 (k 1),
    .while (v 13 =' k 1)
      (.ite (v 12 <' v 2)
        (.ite (jobField 0 (M (v 5 +' v 12)) =' v 11) (increment 12) (.set 13 (k 0)))
        (.set 13 (k 0))),
    .set 13 (k 0), .set 14 (k 0), .set 15 (k 0), -- size, quotient, remainder
    .set 16 (v 12),
    .while (v 10 <' v 16) (statements [
      .set 16 (v 16 -' k 1), .set 17 (M (v 5 +' v 16)),
      increment 13, increment 15,
      .ite (v 15 =' v 1) (statements [increment 14, .set 15 (k 0)]) .skip,
      .store (v 7 +' v 13) (v 17), .set 18 (v 13),
      .set 19 (k 1),
      .while (v 19 =' k 1)
        (.ite (k 1 <' v 18) (statements [
          .set 20 (M (v 8 +' v 18)),
          ifLower (M (v 7 +' v 18)) (M (v 7 +' v 20))
            (statements [.set 21 (M (v 7 +' v 20)),
              .store (v 7 +' v 20) (M (v 7 +' v 18)),
              .store (v 7 +' v 18) (v 21), .set 18 (v 20)])
            (.set 19 (k 0))]) (.set 19 (k 0))),
      .set 18 (v 14),
      .ite (k 0 <' v 15) (increment 18) .skip,
      .ite (v 9 <' v 18 *' v 11) (statements [
        .set 18 (M (v 7 +' k 1)),
        .store (v 4 +' v 18) (jobField 1 (v 17) +' k 1),
        .store (v 7 +' k 1) (M (v 7 +' v 13)),
        .set 13 (v 13 -' k 1),
        .ite (v 15 =' k 0)
          (statements [.set 14 (v 14 -' k 1), .set 15 (v 1 -' k 1)])
          (.set 15 (v 15 -' k 1)),
        .set 18 (k 1), .set 19 (k 1),
        .while (v 19 =' k 1) (statements [
          .set 20 (k 2 *' v 18),
          .ite (v 20 ≤' v 13) (statements [
            .ite (v 20 <' v 13)
              (ifLower (M (v 7 +' v 20 +' k 1)) (M (v 7 +' v 20)) (increment 20) .skip) .skip,
            ifLower (M (v 7 +' v 20)) (M (v 7 +' v 18))
              (statements [.set 21 (M (v 7 +' v 18)),
                .store (v 7 +' v 18) (M (v 7 +' v 20)),
                .store (v 7 +' v 20) (v 21), .set 18 (v 20)])
              (.set 19 (k 0))]) (.set 19 (k 0))])]) .skip]),
    .set 10 (v 12)]),
  .set 0 (v 4)]

/-- Append a successful candidate using the predecessor's pointer before any writes.
Records have three cells (job, machine, predecessor), append-only at register 12. -/
def appendCandidate (backlinks : Bool) : Stmt := statements [
  .set 29 (k 0),
  (if backlinks then statements [
    .set 29 (v 12),
    .store (v 12) (v 13), .store (v 12 +' k 1) (v 19),
    .store (v 12 +' k 2) (M (v 8 +' k 3 *' v 22 +' k 2)),
    .set 12 (v 12 +' k 3)] else .skip),
  .store (v 10 +' k 3 *' v 24) (v 20),
  .store (v 10 +' k 3 *' v 24 +' k 1) (v 23),
  .store (v 10 +' k 3 *' v 24 +' k 2) (v 29), increment 24]

/-- Algorithm 2, lines 1–15, as fixed finite syntax. The Boolean is resolved while
constructing syntax; it is not a free operation during execution.
Memory: input [0,B), header [B,B+16), endpoints and heap scratch as above;
strides Q=B+18+5n, u digits U=Q+m, table F=U+m (3 cells per vector:
reachability, weight, pointer), updates F+3N (3mN reusable cells), then records.
N=(d+1)^m. Header fields 0..5 hold d,A,F,N,records-start,records-end.
All tuple enumeration, flattening, comparisons and updates execute in Light.
The t,u,r loop order is the printed order; equality retains the earlier candidate. -/
def algorithmBody (backlinks : Bool) : Stmt := statements [
  .call 2 [] 4,
  .set 1 (M (k 0)), .set 2 (M (k 1)),
  .set 3 (k 2 +' k 3 *' v 2), .set 5 (M (v 3)),
  .set 6 (v 3 +' k 18 +' k 5 *' v 2),
  .set 7 (v 6 +' v 1), .set 8 (v 7 +' v 1),
  .set 9 (k 1), .set 25 (k 0),
  .while (v 25 <' v 1) (statements [
    .store (v 6 +' v 25) (v 9), .set 9 (v 9 *' (v 5 +' k 1)), increment 25]),
  .set 10 (v 8 +' k 3 *' v 9),
  .set 11 (v 10 +' k 3 *' v 1 *' v 9), .set 12 (v 11),
  .store (v 3 +' k 2) (v 8), .store (v 3 +' k 3) (v 9),
  .store (v 3 +' k 4) (v 11), .set 25 (k 0),
  .while (v 25 <' v 9) (statements [
    .store (v 8 +' k 3 *' v 25) (k 0),
    .store (v 8 +' k 3 *' v 25 +' k 1) (k 0),
    .store (v 8 +' k 3 *' v 25 +' k 2) (k 0), increment 25]),
  .store (v 8) (k 1), .set 13 (k 0),
  .while (v 13 <' v 2) (statements [
    .set 14 (jobField 0 (v 13)), .set 15 (jobField 2 (v 13)),
    .set 16 (jobField 1 (v 13)), .set 24 (k 0),
    .set 17 (M (v 4 +' v 13)),
    .while (v 17 ≤' v 16) (statements [
      .set 25 (k 0),
      .while (v 25 <' v 1) (statements [.store (v 7 +' v 25) (k 0), increment 25]),
      .set 18 (k 0),
      .while (v 18 =' k 0) (statements [
        .set 19 (k 0),
        .while (v 19 <' v 1) (statements [
          -- Insert_r(u,t), flatten in base d+1, remember stride r.
          .set 20 (k 0), .set 25 (k 0), .set 26 (k 0),
          .while (v 25 <' v 1) (statements [
            .ite (v 25 =' v 19)
              (statements [.set 28 (v 17), .set 21 (M (v 6 +' v 25))])
              (statements [.set 28 (M (v 7 +' v 26)), increment 26]),
            .set 20 (v 20 +' v 28 *' M (v 6 +' v 25)), increment 25]),
          .set 22 (v 20 -' v 14 *' v 21),
          .ite (M (v 8 +' k 3 *' v 22) =' k 1) (statements [
            .set 23 (M (v 8 +' k 3 *' v 22 +' k 1) +' v 15),
            .ite (M (v 8 +' k 3 *' v 20) =' k 0)
              (appendCandidate backlinks)
              (.ite (M (v 8 +' k 3 *' v 20 +' k 1) <' v 23)
                (appendCandidate backlinks) .skip)]) .skip,
          increment 19]),
        -- Odometer on exactly m-1 digits; for m=1 there is one empty tuple.
        .set 25 (k 0), .set 27 (k 1),
        .while (v 27 =' k 1)
          (.ite (v 25 <' v 1 -' k 1)
            (statements [
              .ite (M (v 7 +' v 25) <' v 5)
                (statements [.store (v 7 +' v 25) (M (v 7 +' v 25) +' k 1),
                  .set 27 (k 0)])
                (statements [.store (v 7 +' v 25) (k 0), increment 25])])
            (statements [.set 18 (k 1), .set 27 (k 0)]))]),
      increment 17]),
    -- Only now modify f. The entire job's candidate buffer has been collected.
    .set 25 (k 0),
    .while (v 25 <' v 24) (statements [
      .set 20 (M (v 10 +' k 3 *' v 25)),
      .set 23 (M (v 10 +' k 3 *' v 25 +' k 1)),
      .set 28 (k 0),
      .ite (M (v 8 +' k 3 *' v 20) =' k 0) (.set 28 (k 1))
        (.ite (M (v 8 +' k 3 *' v 20 +' k 1) <' v 23) (.set 28 (k 1)) .skip),
      .ite (v 28 =' k 1) (statements [
        .store (v 8 +' k 3 *' v 20) (k 1),
        .store (v 8 +' k 3 *' v 20 +' k 1) (v 23),
        .store (v 8 +' k 3 *' v 20 +' k 2) (M (v 10 +' k 3 *' v 25 +' k 2))]) .skip,
      increment 25]), increment 13]),
  .store (v 3 +' k 5) (v 12),
  .set 0 (k 0), .set 25 (k 0), .set 29 (k 0),
  .while (v 25 <' v 9) (statements [
    .ite (M (v 8 +' k 3 *' v 25) =' k 1)
      (.ite (v 0 <' M (v 8 +' k 3 *' v 25 +' k 1))
        (statements [.set 0 (M (v 8 +' k 3 *' v 25 +' k 1)),
          .set 29 (M (v 8 +' k 3 *' v 25 +' k 2))]) .skip) .skip,
    increment 25]),
  .store (v 3 +' k 6) (v 29)]

/-- Procedure 1: scan the completed table, follow immutable sparse records, mark
chosen jobs, then list chosen jobs in increasing index on each machine and append
all remaining jobs to machine zero. Machine counters reuse strides; marks reuse
mergesort scratch. Output has two cells per input job at records-end. No records
are modified and the dynamic program is not recomputed. -/
def extractionBody : Stmt := statements [
  .set 1 (M (k 0)), .set 2 (M (k 1)),
  .set 3 (k 2 +' k 3 *' v 2), .set 4 (M (v 3 +' k 1)),
  .set 5 (M (v 3 +' k 2)), .set 6 (M (v 3 +' k 3)),
  .set 7 (M (v 3 +' k 5)), -- output address
  .set 8 (v 4 +' v 2), -- selected-job marks
  .set 9 (v 3 +' k 18 +' k 5 *' v 2), -- machine counters
  .set 10 (k 0), .set 11 (k 0), .set 12 (k 0),
  .while (v 10 <' v 6) (statements [
    .ite (M (v 5 +' k 3 *' v 10) =' k 1)
      (.ite (v 11 <' M (v 5 +' k 3 *' v 10 +' k 1))
        (statements [.set 11 (M (v 5 +' k 3 *' v 10 +' k 1)),
          .set 12 (M (v 5 +' k 3 *' v 10 +' k 2))]) .skip) .skip,
    increment 10]),
  .set 10 (k 0),
  .while (v 10 <' v 2) (statements [
    .store (v 8 +' v 10) (k 0 -' k 1), increment 10]),
  .set 10 (k 0),
  .while (v 10 <' v 1) (statements [.store (v 9 +' v 10) (k 0), increment 10]),
  .while (k 0 <' v 12) (statements [
    .store (v 8 +' M (v 12)) (M (v 12 +' k 1)),
    .set 12 (M (v 12 +' k 2))]),
  .set 10 (k 0),
  .while (v 10 <' v 2) (statements [
    .set 12 (M (v 8 +' v 10)),
    .ite (k 0 ≤' v 12) (statements [
      .store (v 7 +' k 2 *' v 10) (v 12),
      .store (v 7 +' k 2 *' v 10 +' k 1) (M (v 9 +' v 12)),
      .store (v 9 +' v 12) (M (v 9 +' v 12) +' k 1)]) .skip,
    increment 10]),
  .set 10 (k 0),
  .while (v 10 <' v 2) (statements [
    .ite (M (v 8 +' v 10) <' k 0) (statements [
      .store (v 7 +' k 2 *' v 10) (k 0),
      .store (v 7 +' k 2 *' v 10 +' k 1) (M (v 9)),
      .store (v 9) (M (v 9) +' k 1)]) .skip,
    increment 10]), .set 0 (v 7)]

def algorithm2Program : Light.Program := [algorithmBody false, .skip, intervalBody]

def algorithm2BacklinkProgram : Light.Program :=
  [algorithmBody true, extractionBody, intervalBody]

def endpointProgram : Light.Program := [intervalBody]

end LawlerCompress.TardyJobs


