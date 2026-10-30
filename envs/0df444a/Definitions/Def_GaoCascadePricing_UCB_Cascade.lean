-- Prove2me | Definitions.Def_GaoCascadePricing_UCB_Cascade
-- name    : GaoCascadePricing_UCB_Cascade
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T08:13:03.845992+00:00
-- url     : https://prove2.me/theorems/f6fdb56f-9685-4d40-b21c-dc0636012667
-- title:
--   General cascade customer law and observed paths
-- statement:
--   A general cascade has $J$ ordered positions and $K$ available action labels at each position. Conditional on examination of product $j$ at action $k$, the click probability is $\beta_{j,k}$, and the conditional purchase probability following a click is $\alpha_{j,k}$. A purchase ends the path. A nonclick continues with probability $\gamma_j$; a click without purchase continues with probability $\zeta_j$. All parameters are in $[0,1]$, including endpoints, and the two continuation probabilities at the last product are zero. The parameter record and its validity predicate are separate so empirical ratios can use the same computational functions.
--
--   The observation records six possibilities at each position: unexamined; nonclick and exit; nonclick and continuation; click and purchase; click without purchase and exit; click without purchase and continuation. The first product is examined. Each later product is examined precisely when the preceding observation continued. A path's weight is the product of these conditional transition probabilities, with inconsistent paths assigned zero. Thus customers may click several products, but purchase at most one. No price or learning assumption is bundled into this object.
--
--   The continuation probability is $\mu_j=(1-\beta_{j,k})\gamma_j+\beta_{j,k}(1-\alpha_{j,k})\zeta_j$. Reach at $j$ is the product of preceding continuation probabilities. Four coordinates expose the selected click, purchase and two continuation parameters for perturbation statements.
--
--   **Formalization Note.** Product and action indices start at zero; the six statuses use the order listed above. The full finite observation carrier includes impossible paths with zero mass. For valid parameters the five outgoing examined-state probabilities sum to one, and exit forces all later positions to be unexamined.
-- source:
--   Gao, Jasin, Najafi and Zhang (2022), Joint Learning and Optimization for Multi-Product Pricing (and Ranking) Under a General Cascade Click Model, DOI https://doi.org/10.1287/mnsc.2021.4246; published basis, supplied manuscript-paginated PDF; §3, pp. 9–11

import Mathlib

open scoped BigOperators

namespace GaoCascadePricing.UCB

/-- General cascade parameters, separate from monetary rewards and learning. -/
structure Cascade (J K : ℕ) where
  beta : Fin J → Fin K → ℝ
  alpha : Fin J → Fin K → ℝ
  gamma : Fin J → ℝ
  zeta : Fin J → ℝ

/-- Endpoints are allowed; continuation at the last product is zero. -/
def Cascade.Valid {J K : ℕ} (θ : Cascade J K) : Prop :=
  (∀ j k, θ.beta j k ∈ Set.Icc (0 : ℝ) 1) ∧
  (∀ j k, θ.alpha j k ∈ Set.Icc (0 : ℝ) 1) ∧
  (∀ j, θ.gamma j ∈ Set.Icc (0 : ℝ) 1) ∧
  (∀ j, θ.zeta j ∈ Set.Icc (0 : ℝ) 1) ∧
  (∀ j, j.val + 1 = J → θ.gamma j = 0 ∧ θ.zeta j = 0)

abbrev Action (J K : ℕ) := Fin J → Fin K

/-- The six observable states: unexamined, nonclick/exit, nonclick/continue,
click/purchase, click/no-purchase/exit, click/no-purchase/continue. -/
abbrev Observation (J : ℕ) := Fin J → Fin 6

def continued (s : Fin 6) : Prop := s = 2 ∨ s = 5

def examined (s : Fin 6) : Prop := s ≠ 0

def clicked (s : Fin 6) : Prop := s = 3 ∨ s = 4 ∨ s = 5

def bought (s : Fin 6) : Prop := s = 3

def nonclick (s : Fin 6) : Prop := s = 1 ∨ s = 2

def declined (s : Fin 6) : Prop := s = 4 ∨ s = 5

noncomputable def localWeight {J K : ℕ} (θ : Cascade J K)
    (j : Fin J) (k : Fin K) (s : Fin 6) : ℝ :=
  if s = 1 then (1 - θ.beta j k) * (1 - θ.gamma j)
  else if s = 2 then (1 - θ.beta j k) * θ.gamma j
  else if s = 3 then θ.beta j k * θ.alpha j k
  else if s = 4 then θ.beta j k * (1 - θ.alpha j k) * (1 - θ.zeta j)
  else if s = 5 then θ.beta j k * (1 - θ.alpha j k) * θ.zeta j
  else 0

/-- Deterministic examination rule, including the first product. -/
def active {J : ℕ} (o : Observation J) (j : Fin J) : Prop :=
  j.val = 0 ∨ ∃ i : Fin J, i.val + 1 = j.val ∧ continued (o i)

/-- Product of the sequential transition probabilities. Impossible paths have mass zero.
After exit all subsequent states must be unexamined. -/
noncomputable def customerWeight {J K : ℕ} (θ : Cascade J K)
    (p : Action J K) (o : Observation J) : ℝ := by
  classical
  exact ∏ j, if active o j then localWeight θ j (p j) (o j)
    else if o j = 0 then 1 else 0

noncomputable def continuation {J K : ℕ} (θ : Cascade J K)
    (p : Action J K) (j : Fin J) : ℝ :=
  (1 - θ.beta j (p j)) * θ.gamma j +
    θ.beta j (p j) * (1 - θ.alpha j (p j)) * θ.zeta j

noncomputable def reach {J K : ℕ} (θ : Cascade J K)
    (p : Action J K) (j : Fin J) : ℝ :=
  ∏ i ∈ Finset.Iio j, continuation θ p i

/-- Four primitive parameters at the chosen product-price pair. -/
def parameter {J K : ℕ} (θ : Cascade J K) (p : Action J K)
    (j : Fin J) (a : Fin 4) : ℝ :=
  if a = 0 then θ.beta j (p j) else if a = 1 then θ.alpha j (p j)
  else if a = 2 then θ.gamma j else θ.zeta j

end GaoCascadePricing.UCB


