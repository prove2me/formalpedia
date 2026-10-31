-- Prove2me | Definitions.Def_FairVaccineReserves_DA_Procedure
-- name    : FairVaccineReserves_DA_Procedure
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T14:53:57.92671+00:00
-- url     : https://prove2.me/theorems/9c49145f-71c6-4a23-a364-c051ded59a67
-- title:
--   Reserve-system adapter to simultaneous deferred acceptance
-- statement:
--   The applicant list of patient $i$ consists of categories above the outside option in $\succ_i$, in preference order. The college list of category $c$ consists of patients above the outside option in $\pi_c$, in priority order. The quota is $r_c$. For compatible profiles the two lists have exactly the same acceptable pairs, so the published admissions procedure's mutual-acceptability filter removes none.
--
--   Starting with empty holds, each free patient applies to her next untried category. Each category retains its highest-priority quota-many patients from its incumbents and new applicants. Submitted applications are removed from the untried lists. The outcome is the assignment returned by the published simultaneous deferred-acceptance recursion. A matching $\mu$ is DA-induced precisely if some compatible full preference profile produces exactly $\mu$, including its category labels.
--
--   **Formalization Note** The lists are obtained by filtering a finite enumeration and sorting by the original ranks; duplicate-freedom is proved structurally. The recursion runs for the number of permissible patient-category pairs, padding stationarily after termination. This gives the same output as stopping at the source's first round with no rejections: after such a round every unheld patient is exhausted. Conversely, when no further application is possible, an additional empty round rejects nobody. No correctness or termination claim is an input hypothesis.
-- source:
--   Pathak, Sönmez, Ünver and Yenmez, arXiv:2008.00374v3 (1 July 2023; draft May 2023), https://arxiv.org/abs/2008.00374v3, §3.5, DA algorithm and DA-induced definition, printed/PDF p. 18

import Definitions.Def_FairVaccineReserves_DA_Preferences
import Definitions.Def_GaleShapley1962_Admissions_Procedure
import Mathlib.Data.List.Nodup

namespace FairVaccineReserves.DA

/-- Eligible patients in the category's full priority order, best first. -/
def ReserveSystem.categoryList {n m : ℕ} (R : ReserveSystem n m)
    (c : Fin m) : List (Fin n) :=
  ((List.finRange n).filter fun i => R.Eligible i c).mergeSort
    (fun i j => decide (R.priority c (some i) ≤ R.priority c (some j)))

/-- Categories above the outside option in the patient's full preference order. -/
def preferenceList {n m : ℕ} (P : PreferenceProfile n m)
    (i : Fin n) : List (Fin m) :=
  ((List.finRange m).filter fun c => P i (some c) < P i none).mergeSort
    (fun c d => decide (P i (some c) ≤ P i (some d)))

/-- Adapter to the published general admissions market; no correctness assumption. -/
def ReserveSystem.toAdmissions {n m : ℕ} (R : ReserveSystem n m)
    (P : PreferenceProfile n m) : GaleShapley1962.Admissions.Market n m where
  applicantList := preferenceList P
  collegeList := R.categoryList
  applicant_nodup := fun i => by
    unfold preferenceList
    exact List.Nodup.mergeSort ((List.nodup_finRange m).filter _)
  college_nodup := fun c => by
    unfold ReserveSystem.categoryList
    exact List.Nodup.mergeSort ((List.nodup_finRange n).filter _)
  quota := R.quota

/-- The actual simultaneous DA output from empty holds with pair-count fuel. -/
def ReserveSystem.outcome {n m : ℕ} (R : ReserveSystem n m)
    (P : PreferenceProfile n m) : GaleShapley1962.Admissions.Assignment n m :=
  (R.toAdmissions P).deferredAcceptance

/-- Section 3.5, p. 18: equality of the entire assignment, including category labels. -/
def ReserveSystem.DAInduced {n m : ℕ} (R : ReserveSystem n m)
    (μ : GaleShapley1962.Admissions.Assignment n m) : Prop :=
  ∃ P : PreferenceProfile n m, R.Compatible P ∧ R.outcome P = μ

end FairVaccineReserves.DA


