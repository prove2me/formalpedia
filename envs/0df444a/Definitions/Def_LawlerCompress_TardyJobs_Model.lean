-- Prove2me | Definitions.Def_LawlerCompress_TardyJobs_Model
-- name    : LawlerCompress_TardyJobs_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T16:23:52.104934+00:00
-- url     : https://prove2.me/theorems/f1479c5c-de1d-42c8-92f8-4054124ffeff
-- title:
--   Scheduling model, completion times, and attained optimality
-- statement:
--   An instance consists of n input jobs and m identical parallel machines. Job j has integral processing time p_j, due date d_j and weight w_j, with 1 ≤ p_j ≤ d_j and 1 ≤ w_j. A schedule consists of one ordered list per machine, with each job appearing exactly once overall. Every machine starts at time zero and runs without idle time. Write C_j(τ) for the inclusive prefix processing sum at job j. The late and on-time weights are
--
--   $$L_I(τ)=\sum_{j:d_j<C_j(τ)}w_j,\qquad E_I(τ)=\sum_{j:C_j(τ)\le d_j}w_j.$$
--
--   An optimal value is attained by a schedule and is no greater than the late weight of any schedule. An optimal schedule attains the minimum. The maximum due date is d_max, the largest input due date. EDD means input due dates are nondecreasing. An on-time EDD prefix means that on each machine the on-time jobs form a prefix strictly increasing in input index, followed by all late jobs.
--
--   These definitions supply the common model for every target.
--
--   **Formalization Note** Jobs and machines are zero-based finite types. Missing-job completion on malformed lists defaults to zero; objective claims only use actual schedules. The targets assume m,n ≥ 1, excluding the undefined maximum-due-date case.
-- source:
--   Klaus Jansen, Björn Schumacher, Corinna Wambsganz, Compressing the Lawler-Moore Dynamic Program for Weighted Tardy Jobs, STOC 2027 submission #354 (October 2026), p. 2, §1, lines 17–41; p. 4, §2, lines 95–97 and Theorem 2.2

import Mathlib

set_option autoImplicit false

namespace LawlerCompress.TardyJobs

/-- The positive integral model of §1, p.2. Machines and input jobs are zero-based. -/
structure Instance (m : ℕ) where
  n : ℕ
  p : Fin n → ℕ
  d : Fin n → ℕ
  w : Fin n → ℕ
  p_pos : ∀ j, 1 ≤ p j
  w_pos : ∀ j, 1 ≤ w j
  p_le_d : ∀ j, p j ≤ d j

def dmax {m : ℕ} (I : Instance m) : ℕ := Finset.univ.sup I.d

abbrev JobLists {m : ℕ} (I : Instance m) := Fin m → List (Fin I.n)

/-- Every job occurs once in exactly one machine list. All machines start at zero. -/
def Schedule {m : ℕ} (I : Instance m) (τ : JobLists I) : Prop :=
  ∀ j, ∑ r, (τ r).count j = 1

/-- Inclusive prefix completion. Outside schedules a missing job has completion zero. -/
def completion {m : ℕ} (I : Instance m) (τ : JobLists I) (j : Fin I.n) : ℕ :=
  ∑ r, if j ∈ τ r then (((τ r).takeWhile (· ≠ j)).map I.p).sum + I.p j else 0

def lateWeight {m : ℕ} (I : Instance m) (τ : JobLists I) : ℕ :=
  ∑ j, if I.d j < completion I τ j then I.w j else 0

def onTimeWeight {m : ℕ} (I : Instance m) (τ : JobLists I) : ℕ :=
  ∑ j, if completion I τ j ≤ I.d j then I.w j else 0

def totalWeight {m : ℕ} (I : Instance m) : ℕ := ∑ j, I.w j

/-- Attainment is part of the optimal-value specification; no infimum convention. -/
def IsOptValue {m : ℕ} (I : Instance m) (v : ℕ) : Prop :=
  (∃ τ, Schedule I τ ∧ lateWeight I τ = v) ∧
    ∀ τ, Schedule I τ → v ≤ lateWeight I τ

def IsOptSchedule {m : ℕ} (I : Instance m) (τ : JobLists I) : Prop :=
  Schedule I τ ∧ ∀ τ', Schedule I τ' → lateWeight I τ ≤ lateWeight I τ'

def EDD {m : ℕ} (I : Instance m) : Prop := Monotone I.d

/-- On-time jobs form an increasing-index prefix on each machine, including tied due dates. -/
def OnTimeEDDPrefix {m : ℕ} (I : Instance m) (τ : JobLists I) : Prop :=
  ∀ r, ∃ early late : List (Fin I.n), τ r = early ++ late ∧
    early.Pairwise (· < ·) ∧
    (∀ j ∈ early, completion I τ j ≤ I.d j) ∧
    (∀ j ∈ late, I.d j < completion I τ j)

end LawlerCompress.TardyJobs


