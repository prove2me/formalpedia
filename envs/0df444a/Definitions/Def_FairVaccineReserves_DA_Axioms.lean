-- Prove2me | Definitions.Def_FairVaccineReserves_DA_Axioms
-- name    : FairVaccineReserves_DA_Axioms
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T14:53:32.269423+00:00
-- url     : https://prove2.me/theorems/b98b16cb-81ea-4f83-893f-131733cdc20f
-- title:
--   Capacity-feasible matchings and the three reserve axioms
-- statement:
--   An assignment $\mu$ sends each patient to one category or to $\varnothing$. Write $\mu^{-1}(c)$ for the patients assigned to category $c$. It is a matching in $M$ exactly when $|\mu^{-1}(c)|\le r_c$ for every category. Eligibility is not part of this capacity-only condition.
--
--   The three axioms are:
--
--   1. Compliance with eligibility: $\mu(i)=c\Rightarrow i\pi_c\varnothing$.
--   2. Non-wastefulness: $i\pi_c\varnothing$ and $\mu(i)=\varnothing$ imply $|\mu^{-1}(c)|=r_c$.
--   3. Respect for priorities: $\mu(i)=c$ and $\mu(j)=\varnothing$ imply $i\pi_c j$.
--
--   The last comparison includes every unmatched patient, whether eligible or not. It imposes no comparison between two patients assigned to different categories. Non-wastefulness permits unused capacity when there is no eligible unmatched patient. The assignment retains category labels.
--
--   **Formalization Note** The published general `Assignment` type is reused; a filtered finite set represents each fiber. The published admissions feasibility and printed-stability predicates are not used.
-- source:
--   Pathak, Sönmez, Ünver and Yenmez, arXiv:2008.00374v3 (1 July 2023; draft May 2023), https://arxiv.org/abs/2008.00374v3, §§3.2–3.3, Definitions 1–3, printed/PDF pp. 13–15

import Definitions.Def_FairVaccineReserves_DA_Model

namespace FairVaccineReserves.DA

def assignedTo {n m : ℕ} (μ : GaleShapley1962.Admissions.Assignment n m)
    (c : Fin m) : Finset (Fin n) :=
  Finset.univ.filter fun i => μ i = some c

/-- Section 3.2: membership in M imposes capacity only, not eligibility. -/
def ReserveSystem.CapacityFeasible {n m : ℕ} (R : ReserveSystem n m)
    (μ : GaleShapley1962.Admissions.Assignment n m) : Prop :=
  ∀ c, (assignedTo μ c).card ≤ R.quota c

/-- Definition 1. -/
def ReserveSystem.CompliesWithEligibility {n m : ℕ} (R : ReserveSystem n m)
    (μ : GaleShapley1962.Admissions.Assignment n m) : Prop :=
  ∀ i c, μ i = some c → R.Eligible i c

/-- Definition 2: an eligible unmatched patient forces that category to be full. -/
def ReserveSystem.NonWasteful {n m : ℕ} (R : ReserveSystem n m)
    (μ : GaleShapley1962.Admissions.Assignment n m) : Prop :=
  ∀ i c, R.Eligible i c → μ i = none → (assignedTo μ c).card = R.quota c

/-- Definition 3: compare each recipient with every unmatched patient. -/
def ReserveSystem.RespectsPriorities {n m : ℕ} (R : ReserveSystem n m)
    (μ : GaleShapley1962.Admissions.Assignment n m) : Prop :=
  ∀ i j c, μ i = some c → μ j = none → R.Higher c (some i) (some j)

end FairVaccineReserves.DA


