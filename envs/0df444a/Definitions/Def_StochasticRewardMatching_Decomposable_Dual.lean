-- Prove2me | Definitions.Def_StochasticRewardMatching_Decomposable_Dual
-- name    : StochasticRewardMatching_Decomposable_Dual
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T21:16:55.839311+00:00
-- url     : https://prove2.me/theorems/9b1a498d-dc55-47dd-90fa-926912e7b37b
-- title:
--   The actual pathwise dual accounting of equation (9)
-- statement:
--   For the actual Algorithm 1 history, lambda_t sums r_i(1-g(y_i)) over successful offers at t; theta_i sums r_i g(y_i) over successful offers of resource i. All unset terms are zero. This sum form exactly implements the initialization and increment convention of equation (9), including failed offers with zero increment. lambda and theta average these quantities over the full seed vector. dualTotal averages the sum of the arrival and resource quantities over the independent edge law. It can also be applied to arbitrary dual arrays in Lemma 2.
-- source:
--   Goyal and Udwani, Online Matching with Stochastic Rewards: Optimal Competitive Ratio via Path Based Formulation, supplied PDF marked arXiv:1905.12778v6 (10 May 2022), equations (7)–(9), PDF/printed pp. 13–14; metadata citation_basis: published. https://arxiv.org/abs/1905.12778v6

import Mathlib
import Definitions.Def_StochasticRewardMatching_Decomposable_Algorithm

open scoped BigOperators
open MeasureTheory
noncomputable section

namespace StochasticRewardMatching.Decomposable

def lambdaPath {n m : ℕ} (D : Instance n m) (ω : Outcome D) (Y : Seeds n) (t : Fin m) : ℝ :=
  ((algorithmHistory D Y ω).map fun z =>
    if z.1.1 = t ∧ z.2 = true then
      match z.1.2 with | none => 0 | some i => D.reward i * (1 - g (Y i))
    else 0).sum

def thetaPath {n m : ℕ} (D : Instance n m) (ω : Outcome D) (Y : Seeds n) (i : Fin n) : ℝ :=
  ((algorithmHistory D Y ω).map fun z =>
    if z.1.2 = some i ∧ z.2 = true then D.reward i * g (Y i) else 0).sum

def lambda {n m : ℕ} (D : Instance n m) (ω : Outcome D) (t : Fin m) : ℝ :=
  seedAverage (fun Y => lambdaPath D ω Y t)

def theta {n m : ℕ} (D : Instance n m) (ω : Outcome D) (i : Fin n) : ℝ :=
  seedAverage (fun Y => thetaPath D ω Y i)

def dualTotal {n m : ℕ} (D : Instance n m)
    (l : Outcome D → Fin m → ℝ) (q : Outcome D → Fin n → ℝ) : ℝ :=
  edgeAverage D (fun ω => (∑ t, l ω t) + ∑ i, q ω i)

end StochasticRewardMatching.Decomposable


