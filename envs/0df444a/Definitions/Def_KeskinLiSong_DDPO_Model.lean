-- Prove2me | Definitions.Def_KeskinLiSong_DDPO_Model
-- name    : KeskinLiSong_DDPO_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T14:43:41.396768+00:00
-- url     : https://prove2.me/theorems/f3f53992-26fa-4032-9a05-00306c5a2708
-- title:
--   Continuous pricing and perishable inventory model
-- statement:
--   The model uses continuous compact price and inventory intervals and compact demand and positive beta-parameter rectangles. Demand has the increasing C2 link g and a negative price coefficient. A horizon-specific environment supplies exactly C changes, pairwise separation of distinct parameter values, and an initially feasible stock. H and Q are the actual expectations in equations (4)–(5); stock and joint optimizers are attained-optimum relations. No desired rate or optimizer sensitivity is assumed. Increasing is encoded as nondecreasing, without a strictly positive derivative condition.
-- source:
--   Keskin, Li and Song (2022), Data-Driven Dynamic Pricing and Ordering with Perishable Inventory in a Changing Environment, Management Science, doi:10.1287/mnsc.2021.4011, supplied source.pdf (internally dated January 3, 2021; SSRN 3401188 footers), pp. 7–10, equations (1)–(5)

import Definitions.Def_KeskinLiSong_DDPO_StatisticalObjects

open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section

namespace KeskinLiSong.DDPO

structure Model where
  pmin : ℝ
  pmax : ℝ
  ymin : ℝ
  ymax : ℝ
  alphaMin : ℝ
  alphaMax : ℝ
  betaMin : ℝ
  betaMax : ℝ
  lambdaMin : ℝ
  lambdaMax : ℝ
  nuMin : ℝ
  nuMax : ℝ
  h : ℝ
  b : ℝ
  w : ℝ
  c : ℝ
  g : ℝ → ℝ
  price_bounds : 0 < pmin ∧ pmin < pmax
  stock_bounds : 0 < ymin ∧ ymin < ymax
  demand_bounds : alphaMin ≤ alphaMax ∧ betaMin ≤ betaMax ∧ betaMax < 0
  perish_bounds : 0 < lambdaMin ∧ lambdaMin ≤ lambdaMax ∧ 0 < nuMin ∧ nuMin ≤ nuMax
  costs_nonnegative : 0 ≤ h ∧ 0 ≤ b ∧ 0 ≤ w ∧ 0 ≤ c
  cost_restriction : ∀ p ∈ Set.Icc pmin pmax, |h - c| < b + p
  increasing : Monotone g
  smooth : ContDiff ℝ 2 g
  noise : LocalMGF
  changes : ℕ
  separation : ℝ
  separation_pos : 0 < separation

def Model.P (A : Model) := Set.Icc A.pmin A.pmax

def Model.Y (A : Model) := Set.Icc A.ymin A.ymax

def Model.Theta (A : Model) : Set (Vector 2) :=
  {v | v 0 ∈ Set.Icc A.alphaMin A.alphaMax ∧ v 1 ∈ Set.Icc A.betaMin A.betaMax}

def Model.Xi (A : Model) : Set (Vector 2) :=
  {v | v 0 ∈ Set.Icc A.lambdaMin A.lambdaMax ∧ v 1 ∈ Set.Icc A.nuMin A.nuMax}

structure Environment (A : Model) (T : ℕ) where
  theta : ℕ → Vector 2
  xi : Vector 2
  xinitial : ℝ
  changeTime : ℕ → ℕ
  xi_mem : xi ∈ A.Xi
  initial_feasible : 0 ≤ xinitial ∧ xinitial ≤ A.ymax
  theta_mem : ∀ t ∈ Finset.Icc 1 T, theta t ∈ A.Theta
  first_change : changeTime 0 = 1
  last_change : changeTime (A.changes + 1) = T + 1
  increasing_changes : ∀ j ≤ A.changes, changeTime j < changeTime (j + 1)
  constant_segments : ∀ j ≤ A.changes, ∀ t,
    changeTime j ≤ t → t < changeTime (j + 1) → theta t = theta (changeTime j)
  genuine_changes : ∀ j, 1 ≤ j → j ≤ A.changes →
    theta (changeTime j) ≠ theta (changeTime (j - 1))
  separated_values : ∀ s ∈ Finset.Icc 1 T, ∀ t ∈ Finset.Icc 1 T,
    theta s ≠ theta t → A.separation ≤ dist (theta s) (theta t)

def meanDemand (A : Model) (theta : Vector 2) (p : ℝ) : ℝ :=
  A.g (theta 0 + theta 1 * p)

def perishLaw (xi : Vector 2) : Measure ℝ := betaMeasure (xi 0) (xi 1)

def H (A : Model) (μ : Measure ℝ) (theta xi : Vector 2) (p y : ℝ) : ℝ :=
  (A.h - A.c) * (∫ e, ∫ q, max ((1 - q) * y - meanDemand A theta p - e) 0 ∂perishLaw xi ∂μ) +
  (A.b + p) * (∫ e, ∫ q, max (meanDemand A theta p + e - (1 - q) * y) 0 ∂perishLaw xi ∂μ) +
  (A.w * (∫ q, q ∂perishLaw xi) + A.c) * y

def Q (A : Model) (μ : Measure ℝ) (theta xi : Vector 2) (p y : ℝ) : ℝ :=
  p * meanDemand A theta p - H A μ theta xi p y

/-- Actual maximizers, not an unguarded supremum over an empty set. -/
def StockOptimum (A : Model) (μ : Measure ℝ) (theta xi : Vector 2)
    (p y : ℝ) : Prop := Maximizes A.Y (fun z => -H A μ theta xi p z) y

def JointOptimum (A : Model) (μ : Measure ℝ) (theta xi : Vector 2)
    (a : ℝ × ℝ) : Prop :=
  Maximizes (A.P ×ˢ A.Y) (fun z => Q A μ theta xi z.1 z.2) a

/-- Optimal value as a relation includes attainment. -/
def IsG (A : Model) (μ : Measure ℝ) (theta xi : Vector 2) (p v : ℝ) : Prop :=
  ∃ y, StockOptimum A μ theta xi p y ∧ v = Q A μ theta xi p y

end KeskinLiSong.DDPO


