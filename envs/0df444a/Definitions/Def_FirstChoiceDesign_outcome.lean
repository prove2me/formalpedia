-- Prove2me | Definitions.Def_FirstChoiceDesign_outcome
-- name    : FirstChoiceDesign_outcome
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:23:40.13951+00:00
-- url     : https://prove2.me/theorems/bef4dad0-aeae-4314-aa1c-4459c6628786
-- title:
--   The assignment $\varphi(\rho,r)$ and the sets $\varphi_s(\rho,r)$
-- statement:
--   Given preferences $\succ_I$, reported priorities $\rho$ and lottery numbers $r$, school $s$ orders students by $i\succ^\varphi_{r_s}i'$ if $\rho^\varphi_{is}+r_{is}<\rho^\varphi_{i's}+r_{i's}$, and $\varphi(\rho,r)$ is the assignment produced by the student-proposing deferred acceptance algorithm on these orders. $\varphi_s(\rho,r)$ is the set of students assigned to $s$.
--
--   **Formalization Note** `market` builds the published `GaleShapley1962.Admissions.Market`, with students' acceptable lists and each school's list of all students, and `outcome` is its published `deferredAcceptance`. Priorities and lottery numbers are arguments, not fields of the problem, so a report can change one school's column. `outcome` is a total function: on tied profiles it returns the junk value of the sort, and no statement evaluates it there except through a null set of `lotteryLaw`. `seats μ s` is $\mu_s$. `GDA.score` is $\rho^\varphi_{is}+r_{is}$.
-- source:
--   Narita, (Non)Randomization: A Theory of Quasi-Experimental Evaluation of School Quality, Cowles Foundation Discussion Paper No. 2056R (rev. Aug. 2017), Definition 1, pp.7–8; DA algorithm, p.7; φ(ρ, r), p.13

import Definitions.Def_FirstChoiceDesign_GDA
import Definitions.Def_FirstChoiceDesign_Lottery
import Definitions.Def_GaleShapley1962_Admissions_Procedure

namespace FirstChoiceDesign

open GaleShapley1962.Admissions

/-- The criterion `ρ^φ_is + r_is` of Definition 1(2), p.7: a smaller value is a better position in
school `s`'s ex post strict order, `i ≻^φ_{r_s} i'` iff `ρ^φ_is + r_is < ρ^φ_i's + r_i's`. -/
noncomputable def GDA.score {n m : ℕ} (φ : GDA) (B : Setting n m) (ρ : Fin n → Fin m → ℕ)
    (r : Lottery n m) (i : Fin n) (s : Fin m) : ℝ :=
  (φ.modified B ρ i s : ℝ) + r i s

open Classical in
/-- The market on which Definition 1(3) runs DA: students list their acceptable schools best first,
each school lists all students by `≻^φ_{r_s}` (every student is acceptable to every school, p.6). -/
noncomputable def market {n m : ℕ} (φ : GDA) (B : Setting n m) (ρ : Fin n → Fin m → ℕ)
    (r : Lottery n m) : Market n m where
  applicantList := B.applicantList
  collegeList s := (List.finRange n).insertionSort fun a b => φ.score B ρ r a s ≤ φ.score B ρ r b s
  applicant_nodup _ :=
    (List.perm_insertionSort _ _).nodup_iff.mpr ((List.nodup_finRange m).filter _)
  college_nodup _ := (List.perm_insertionSort _ _).nodup_iff.mpr (List.nodup_finRange n)
  quota := B.c

/-- The assignment `φ(ρ, r)` produced by a gDA mechanism from reported priorities and lottery
numbers `(ρ, r)`, Definition 1, pp.7–8, and p.13, by the published deferred acceptance procedure.

**Formalization Note** The function is total. The school order is a total preorder on students and
is strict exactly when no two students of the school have the same `ρ^φ + r`, which `Tieless r`
guarantees: `ρ^φ` is an integer and `r` lies in `(0, 1)`. On ties the value is a junk value of the
sort, and those profiles form a null set for `lotteryLaw`. -/
noncomputable def outcome {n m : ℕ} (φ : GDA) (B : Setting n m) (ρ : Fin n → Fin m → ℕ)
    (r : Lottery n m) : Assignment n m :=
  (market φ B ρ r).deferredAcceptance

/-- The set `μ_s` of students a matching `μ` assigns to school `s`, p.41. -/
def seats {n m : ℕ} (μ : Assignment n m) (s : Fin m) : Finset (Fin n) :=
  Finset.univ.filter fun i => μ i = some s

/-- `φ_s(ρ, r)`, the set of students assigned to `s`, p.13. -/
noncomputable def assigned {n m : ℕ} (φ : GDA) (B : Setting n m) (ρ : Fin n → Fin m → ℕ)
    (r : Lottery n m) (s : Fin m) : Finset (Fin n) :=
  seats (outcome φ B ρ r) s

end FirstChoiceDesign


