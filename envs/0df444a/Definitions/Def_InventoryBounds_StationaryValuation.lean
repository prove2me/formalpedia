-- Prove2me | Definitions.Def_InventoryBounds_StationaryValuation
-- name    : InventoryBounds_StationaryValuation
-- status  : Definition
-- author  : @visuddhi
-- created : 2026-10-08T15:31:05.588979+00:00
-- url     : https://prove2.me/theorems/ad57e5cd-2326-4254-a92e-ec7cfff80db5
-- title:
--   Bernoulli backlog Bellman values and randomized valuation experiments
-- statement:
--   Finite-horizon Bellman recursion and zero-base-stock recursion for unit costs and zero/unit IID demand; a separately defined value polynomial and derivative expression; Bernoulli KL; the two perturbed zero-demand probabilities; IID finite archive weights; and estimator success probability computed from a Markov kernel.
-- source:
--   Hanzhang Qin, David Simchi-Levi, Ruihao Zhu, Information Limits of Multistage Inventory Control: Learning, Valuation, and Censoring, arXiv:2609.37380v1 (29 September 2026), https://arxiv.org/abs/2609.37380v1, Sections 2.1 and 3.3

import Definitions.Def_InventoryBounds_Primitives
import Mathlib.Probability.Kernel.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace InventoryBounds

noncomputable def bernoulliDP : ℕ → ℝ → ℝ → ℝ
  | 0, _, _ => 0
  | n + 1, ρ, x => sInf
      ((fun y : ℝ =>
        ρ * (stageCost 1 1 y 0 + bernoulliDP n ρ y) +
        (1 - ρ) * (stageCost 1 1 y 1 + bernoulliDP n ρ (y - 1))) ''
        Set.Ici (max x 0))

noncomputable def zeroBaseStockValue : ℕ → ℝ → ℝ → ℝ
  | 0, _, _ => 0
  | n + 1, ρ, x =>
      let y := max x 0
      ρ * (stageCost 1 1 y 0 + zeroBaseStockValue n ρ y) +
      (1 - ρ) * (stageCost 1 1 y 1 + zeroBaseStockValue n ρ (y - 1))

noncomputable def valueFormula (T : ℕ) (ρ : ℝ) : ℝ :=
  (T : ℝ) * (1 - ρ) + (2 * ρ - 1) * ∑ k ∈ Finset.range T, ρ ^ k

noncomputable def valueDerivative (T : ℕ) (ρ : ℝ) : ℝ :=
  -(T : ℝ) + 2 * (∑ k ∈ Finset.range T, ρ ^ k) +
    (2 * ρ - 1) * ∑ k ∈ Finset.range T, (k : ℝ) * ρ ^ (k - 1)

noncomputable def binaryKL (p q : ℝ) : ℝ :=
  p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q))

noncomputable def rhoMinus (T : ℕ) (ε : ℝ) : ℝ :=
  1 - 1 / (2 * (T : ℝ)) - 128 * ε / (T : ℝ) ^ 2

noncomputable def rhoPlus (T : ℕ) (ε : ℝ) : ℝ :=
  1 - 1 / (2 * (T : ℝ)) + 128 * ε / (T : ℝ) ^ 2

-- A true bit denotes a zero demand; false denotes a unit demand.
noncomputable def sampleWeight {M : ℕ} (ρ : ℝ) (z : Fin M → Bool) : ℝ :=
  ∏ i : Fin M, if z i then ρ else 1 - ρ

-- A Markov kernel includes every randomized real-valued estimator on this finite archive.
noncomputable def estimatorSuccess {M : ℕ}
    (κ : Kernel (Fin M → Bool) ℝ) (ρ v ε : ℝ) : ℝ :=
  ∑ z : Fin M → Bool,
    sampleWeight ρ z * (κ z (Set.Icc (v - ε) (v + ε))).toReal

end InventoryBounds


