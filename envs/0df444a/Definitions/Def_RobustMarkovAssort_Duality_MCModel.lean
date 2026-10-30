-- Prove2me | Definitions.Def_RobustMarkovAssort_Duality_MCModel
-- name    : RobustMarkovAssort_Duality_MCModel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T23:16:31.438554+00:00
-- url     : https://prove2.me/theorems/1806e28a-68dd-471f-8629-5bd11e0f3c90
-- title:
--   Row-product Markov uncertainty and its constructed general specialization
-- statement:
--   MCUncertainty records nonnegative prices, nonempty arrival and row uncertainty sets, nonnegative transition rows with zero diagonal and row sums at most one. The scenario set is exactly the Cartesian product of the arrival set and the independently chosen rows. MCPositive requires positive arrival weights; Assumption2 also requires each admissible row sum strictly below one, without a uniform gap. specialization constructs lambda(u)=lambda, A(u)=I-rho and b(u)=0. primitiveModel reuses the published MarkovChainChoice.Shared.Model for each admissible scenario, and mcRevenue constructs the continuation balance value and its arrival-weighted revenue. Arrival weights need not be normalized; all probability instances are included. Zero-product instances are also admitted and have zero revenue.
-- source:
--   Désir, Goyal, Jiang, Xie and Zhang, Robust Assortment Optimization Under the Markov Chain Choice Model, Operations Research (2023), DOI 10.1287/opre.2022.2420; canonical artifact pp. 6–8 and 12, equations (1), Rev MC, Assumptions 1–2 and Section 3.3

import Definitions.Def_MarkovChainChoice_Shared_Model
import Definitions.Def_RobustMarkovAssort_Duality_GeneralModel

namespace RobustMarkovAssort.Duality

structure MCUncertainty (n : ℕ) where
  r : Vec n
  r_nonneg : ∀ i, 0 ≤ r i
  arrivals : Set (Vec n)
  arrivals_nonempty : arrivals.Nonempty
  rows : Fin n → Set (Vec n)
  rows_nonempty : ∀ i, (rows i).Nonempty
  rows_nonneg : ∀ i q, q ∈ rows i → ∀ j, 0 ≤ q j
  rows_diag : ∀ i q, q ∈ rows i → q i = 0
  rows_subprob : ∀ i q, q ∈ rows i → ∑ j, q j ≤ 1

def MCPositive {n : ℕ} (M : MCUncertainty n) : Prop :=
  ∀ l ∈ M.arrivals, ∀ i, 0 < l i

def Assumption2 {n : ℕ} (M : MCUncertainty n) : Prop :=
  MCPositive M ∧ ∀ i q, q ∈ M.rows i → ∑ j, q j < 1

def scenarios {n : ℕ} (M : MCUncertainty n) : Set (Vec n × Mat n) :=
  {u | u.1 ∈ M.arrivals ∧ ∀ i, u.2 i ∈ M.rows i}

noncomputable def specialization {n : ℕ} (M : MCUncertainty n) :
    GeneralModel n (Vec n × Mat n) where
  r := M.r
  r_nonneg := M.r_nonneg
  U := scenarios M
  U_nonempty := by
    obtain ⟨l, hl⟩ := M.arrivals_nonempty
    choose q hq using M.rows_nonempty
    exact ⟨(l, q), hl, hq⟩
  lam := fun u => u.1
  A := fun u => 1 - u.2
  b := fun _ => 0

def primitiveModel {n : ℕ} (M : MCUncertainty n) (h2 : Assumption2 M)
    (u : {u // u ∈ scenarios M}) : MarkovChainChoice.Shared.Model n where
  lam := u.val.1
  rho := u.val.2
  lam_pos := h2.1 u.val.1 u.property.1
  rho_nonneg := fun i j => M.rows_nonneg i (u.val.2 i) (u.property.2 i) j
  rho_row_lt_one := fun i => h2.2 i (u.val.2 i) (u.property.2 i)

noncomputable def fixedMCRevenue {n : ℕ} (r : Vec n)
    (P : MarkovChainChoice.Shared.Model n) (S : Assortment n) : ℝ :=
  ∑ i, P.lam i * balanceValue r (1 - Matrix.of P.rho) 0 S i

noncomputable def mcRevenue {n : ℕ} (M : MCUncertainty n) (h2 : Assumption2 M)
    (S : Assortment n) (u : {u // u ∈ scenarios M}) : ℝ :=
  fixedMCRevenue M.r (primitiveModel M h2 u) S

end RobustMarkovAssort.Duality


