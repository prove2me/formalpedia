-- Prove2me | Definitions.Def_AssortOpt_HMF_Supplement_Reports
-- name    : AssortOpt_HMF_Supplement_Reports
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T07:13:56.102168+00:00
-- url     : https://prove2.me/theorems/519314ff-344c-4d95-ac66-e3e2094f64d7
-- title:
--   Report domains, prefix-increment mechanisms and attained allocation maxima
-- statement:
--   Let $N$ be a finite item universe. A report is a list of distinct items. The report domain $R$ may contain types of probability zero, independently of the positive support of a buyer distribution. Incentive compatibility on $R$ means, for every $\ell,\ell'\in R$ and $k\le |\ell|$,
--   $$\sum_{j\in\ell_{1:k}\cap\ell'}x_j(\ell')\le\sum_{j\in\ell_{1:k}}x_j(\ell),\qquad \sum_{j\in\ell}x_j(\ell)\le1,\qquad x_j(\ell)\ge0.$$
--   For a set function $f$, the prefix-increment mechanism assigns $\ell_k$ with probability $f(\ell_{1:k})-f(\ell_{1:k-1})$. The maximum-mass function is the attained maximum of $\sum_{j\in S\cap\ell}x_j(\ell)$ over reports. The singleton maximum $f_j$ ranges over reports containing $j$; it is zero when there are none. Zero is adjoined to each finite maximum, which changes no maximum for an IC array on a nonempty report domain.
--
--   This interface extends the published support-only IC predicate to retain probability-zero reports in Proposition 10. Items are `Fin n`, numbered from zero. Values for items absent from a report are never used.
-- source:
--   Ma, When is Assortment Optimization Optimal?, arXiv:2105.10433v5, p. 9, Definition 3, (3)–(5); p. 11, (7); p. 23, Proposition 10; p. 25, Theorem 5

import Mathlib
import Definitions.Def_AssortOpt_HMF_Setting
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular

namespace AssortOpt.HMF.Supplement
open Finset

/-- The finite type of all strictly ordered subsets, including the empty list. -/
abbrev Report (n : ℕ) := {ℓ : List (Fin n) // ℓ.Nodup}

/-- All possible reports, independently of their probabilities. -/
def allReports (n : ℕ) : Finset (List (Fin n)) :=
  Finset.univ.image (fun ℓ : Report n => ℓ.val)

/-- The IC constraints (3)–(5) on a report domain, which may include zero-probability lists.
Every theorem applying this predicate also requires reports to be strictly ordered subsets. -/
def IsICOn {n : ℕ} (R : Finset (List (Fin n)))
    (x : List (Fin n) → Fin n → ℝ) : Prop :=
  (∀ ℓ ∈ R, ∀ k ≤ ℓ.length, ∀ ℓ' ∈ R,
    ∑ j ∈ (ℓ.take k).toFinset ∩ ℓ'.toFinset, x ℓ' j ≤
      ∑ j ∈ (ℓ.take k).toFinset, x ℓ j) ∧
  (∀ ℓ ∈ R, ∑ j ∈ ℓ.toFinset, x ℓ j ≤ 1) ∧
  (∀ ℓ ∈ R, ∀ j ∈ ℓ, 0 ≤ x ℓ j)

/-- Allocation defined by successive prefix increments, evaluated at the position of `j`.
Values at items absent from the reported list are zero and are never used by the IC constraints. -/
def incrementMech {n : ℕ} (f : Finset (Fin n) → ℝ)
    (ℓ : List (Fin n)) (j : Fin n) : ℝ :=
  if j ∈ ℓ then
    f (ℓ.take (ℓ.idxOf j + 1)).toFinset - f (ℓ.take (ℓ.idxOf j)).toFinset
  else 0

/-- Equation (7): maximum allocation mass in a set over the actual report domain.
Adjoining 0 makes the empty-domain convention explicit; for IC arrays every mass is already
nonnegative, so this is the paper's maximum. The finite maximum is attained. -/
noncomputable def maxMass {n : ℕ} (R : Finset (List (Fin n)))
    (x : List (Fin n) → Fin n → ℝ) (S : Finset (Fin n)) : ℝ :=
  (insert 0 (R.image fun ℓ => ∑ j ∈ S ∩ ℓ.toFinset, x ℓ j)).max' (by simp)

/-- Maximum item-allocation probability over reports containing the item. Items absent from
every report have value 0. For IC arrays this is `maxMass R x {j}`. -/
noncomputable def maxAlloc {n : ℕ} (R : Finset (List (Fin n)))
    (x : List (Fin n) → Fin n → ℝ) (j : Fin n) : ℝ :=
  (insert 0 ((R.filter fun ℓ => j ∈ ℓ).image fun ℓ => x ℓ j)).max' (by simp)

end AssortOpt.HMF.Supplement


