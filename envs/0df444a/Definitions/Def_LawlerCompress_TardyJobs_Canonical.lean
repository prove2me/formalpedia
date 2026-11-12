-- Prove2me | Definitions.Def_LawlerCompress_TardyJobs_Canonical
-- name    : LawlerCompress_TardyJobs_Canonical
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T16:24:36.088428+00:00
-- url     : https://prove2.me/theorems/6cdc3054-97b9-4049-a66e-947c31c68fab
-- title:
--   Priorities, canonical intervals, and the reverse heap specification
-- statement:
--   A larger weight has higher priority; equal weights are resolved in favor of the larger input index. For positive processing time p put κ_p=m⌊d_max/p⌋. Let T_{p,t} contain the jobs with processing time p and due date at least t. Its canonical subset T̄_{p,t} contains a job precisely when fewer than κ_p eligible jobs outrank it. Define
--
--   $$\bar C_j=\{t\in\{p_j,\ldots,d_{\max}\}:j\in\bar T_{p_j,t}\}.$$
--
--   The endpoint a_j is the smallest canonical time, defaulting explicitly to d_j+1 if the interval is empty. The pure heap procedure groups jobs by processing time and folds over each group in decreasing index. It inserts a job and removes the lowest-priority job when the heap exceeds κ_p. An evicted job receives the inserted job's due date plus one. Surviving jobs receive endpoint p.
--
--   This layer states the mathematical objects shared by the interval and scheduling lemmas. The finite-set heap specifies contents; it does not assign a constant cost to heap operations.
--
--   **Formalization Note** The heap minimum is selected by an explicitly ordered finite list. Processing time zero is never used by the targets; natural division's value there is irrelevant.
-- source:
--   Klaus Jansen, Björn Schumacher, Corinna Wambsganz, Compressing the Lawler-Moore Dynamic Program for Weighted Tardy Jobs, STOC 2027 submission #354 (October 2026), pp. 4–6, §2 definitions and Equation (1), Lemma 2.1, §3.1 heap procedure

import Definitions.Def_LawlerCompress_TardyJobs_Model

set_option autoImplicit false

namespace LawlerCompress.TardyJobs

/-- Higher priority means larger weight, then larger input index (p.4). -/
def higher {m : ℕ} (I : Instance m) (h j : Fin I.n) : Prop :=
  I.w j < I.w h ∨ (I.w h = I.w j ∧ j < h)

instance {m : ℕ} (I : Instance m) (h j : Fin I.n) : Decidable (higher I h j) :=
  inferInstanceAs (Decidable (_ ∨ _))

def kappa {m : ℕ} (I : Instance m) (p : ℕ) : ℕ := m * (dmax I / p)

def eligible {m : ℕ} (I : Instance m) (p t : ℕ) : Finset (Fin I.n) :=
  Finset.univ.filter (fun j => I.p j = p ∧ t ≤ I.d j)

/-- The first κ jobs in the strict priority order, including all jobs if fewer exist. -/
def tbar {m : ℕ} (I : Instance m) (p t : ℕ) : Finset (Fin I.n) :=
  (eligible I p t).filter fun j =>
    ((eligible I p t).filter (fun h => higher I h j)).card < kappa I p

def cbar {m : ℕ} (I : Instance m) (j : Fin I.n) : Finset ℕ :=
  (Finset.Icc (I.p j) (dmax I)).filter fun t => j ∈ tbar I (I.p j) t

/-- Least canonical time; the explicitly specified empty-interval endpoint is d_j+1. -/
def a {m : ℕ} (I : Instance m) (j : Fin I.n) : ℕ :=
  ((List.range (dmax I + 1)).filter (fun t => t ∈ cbar I j)).headD (I.d j + 1)

/-- A pure finite-set heap step specifies §3.1; it makes no constant-time claim. -/
def heapStep {m : ℕ} (I : Instance m) (p : ℕ)
    (s : Finset (Fin I.n) × (Fin I.n → ℕ)) (j : Fin I.n) :
    Finset (Fin I.n) × (Fin I.n → ℕ) :=
  let h := insert j s.1
  if kappa I p < h.card then
    let low := (((List.finRange I.n).filter (· ∈ h)).mergeSort (fun x y => decide (higher I y x))).headD j
    (h.erase low, Function.update s.2 low (I.d j + 1))
  else (h, s.2)

/-- Reverse EDD-index traversal, with the due date of the inserted job on eviction. -/
def heapGroup {m : ℕ} (I : Instance m) (p : ℕ) : Fin I.n → ℕ :=
  let jobs := (List.finRange I.n).filter (fun j => I.p j = p)
  let s := jobs.reverse.foldl (heapStep I p) (∅, fun j => I.d j + 1)
  fun j => if j ∈ s.1 then p else s.2 j

def heapEndpoints {m : ℕ} (I : Instance m) (j : Fin I.n) : ℕ :=
  heapGroup I (I.p j) j

end LawlerCompress.TardyJobs


