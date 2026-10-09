-- Prove2me | Definitions.Def_ModernOnlineLearning_ParameterFree_Defs
-- name    : ModernOnlineLearning_ParameterFree_Defs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T02:38:29.033914+00:00
-- url     : https://prove2.me/theorems/1ab7fc9d-2f0e-4cac-87bb-f0a32751943f
-- title:
--   Algorithms 13.1–13.3 — KT wealth, potential, subgradients, and online runs
-- statement:
--   The **KT bettor** begins with wealth $\varepsilon>0$. At round $t$, its fraction is $\beta_t=(\sum_{j=1}^{t-1}c_j)/t$, it bets $x_t=\beta_t\operatorname{Wealth}_{t-1}$, and its wealth changes by $\operatorname{Wealth}_t=\operatorname{Wealth}_{t-1}+c_tx_t$. The gamma-function potential used to bound this wealth is
--   $$F_t(z)=\frac{\varepsilon 2^t\Gamma((t+1+z)/2)\Gamma((t+1-z)/2)}{\pi\Gamma(t+1)}.$$
--
--   The one-dimensional and coordinate-wise OCO runs record the explicit KT prediction from past subgradients and past predictions. For each round, the chosen subgradient supports the loss on the entire decision space and has absolute value at most $L$ in each coordinate. The losses are subdifferentiable throughout that space.
--
--   These definitions fix the book's round numbering and the algorithmic state used by the regret bounds. Index zero is unused by the update.
-- source:
--   Orabona, arXiv:1912.13213v10, Algorithm 13.1 p. 208, Theorem 13.4 proof p. 210, Algorithms 13.2–13.3 pp. 213, 215

import Mathlib

namespace ModernOnlineLearning.ParameterFree

/-- Algorithm 13.1: the fraction of current wealth wagered in round `t`. -/
noncomputable def ktFraction (c : ℕ → ℝ) (t : ℕ) : ℝ :=
  (∑ j ∈ Finset.Icc 1 (t - 1), c j) / (t : ℝ)

/-- Algorithm 13.1: initial wealth and the product of the round-by-round returns. -/
noncomputable def ktWealth (ε : ℝ) (c : ℕ → ℝ) (t : ℕ) : ℝ :=
  ε * ∏ j ∈ Finset.Icc 1 t, (1 + c j * ktFraction c j)

/-- Algorithm 13.1: the signed wager in round `t`. -/
noncomputable def ktBet (ε : ℝ) (c : ℕ → ℝ) (t : ℕ) : ℝ :=
  ktFraction c t * ktWealth ε c (t - 1)

/-- The gamma-function potential in Theorem 13.4 and its proof. -/
noncomputable def ktPotential (ε : ℝ) (t : ℕ) (z : ℝ) : ℝ :=
  ε * 2 ^ t *
    Real.Gamma (((t : ℝ) + 1 + z) / 2) *
    Real.Gamma (((t : ℝ) + 1 - z) / 2) /
    (Real.pi * Real.Gamma ((t : ℝ) + 1))

/-- A full-space subgradient of a real-valued loss on `ℝ`. -/
def IsSubgradientReal (f : ℝ → ℝ) (x g : ℝ) : Prop :=
  ∀ y : ℝ, f x + g * (y - x) ≤ f y

/-- A full-space subgradient of a real-valued loss on `ℝ^d`. -/
def IsSubgradientCoord {d : ℕ} (f : (Fin d → ℝ) → ℝ)
    (x g : Fin d → ℝ) : Prop :=
  ∀ y : Fin d → ℝ, f x + (∑ i : Fin d, g i * (y i - x i)) ≤ f y

/-- Algorithm 13.2: the one-dimensional KT update and its admissible oracle answers. -/
def IsOneDKTRun (ε L : ℝ) (T : ℕ) (ℓ : ℕ → ℝ → ℝ)
    (g x : ℕ → ℝ) : Prop :=
  (∀ t ∈ Finset.Icc 1 T,
    x t = -((∑ j ∈ Finset.Icc 1 (t - 1), g j) / (L * (t : ℝ))) *
      (ε - ∑ j ∈ Finset.Icc 1 (t - 1), (g j / L) * x j)) ∧
  (∀ t ∈ Finset.Icc 1 T, IsSubgradientReal (ℓ t) (x t) (g t) ∧ |g t| ≤ L) ∧
  (∀ t ∈ Finset.Icc 1 T, ∀ z : ℝ, ∃ h : ℝ, IsSubgradientReal (ℓ t) z h)

/-- Algorithm 13.3: one KT update in each coordinate, with full-space subgradients. -/
def IsCoordKTRun {d : ℕ} (ε L : ℝ) (T : ℕ)
    (ℓ : ℕ → (Fin d → ℝ) → ℝ) (g x : ℕ → Fin d → ℝ) : Prop :=
  (∀ t ∈ Finset.Icc 1 T, ∀ i : Fin d,
    x t i = -((∑ j ∈ Finset.Icc 1 (t - 1), g j i) / (L * (t : ℝ))) *
      (ε - ∑ j ∈ Finset.Icc 1 (t - 1), (g j i / L) * x j i)) ∧
  (∀ t ∈ Finset.Icc 1 T,
    IsSubgradientCoord (ℓ t) (x t) (g t) ∧ ∀ i : Fin d, |g t i| ≤ L) ∧
  (∀ t ∈ Finset.Icc 1 T, ∀ z : Fin d → ℝ,
    ∃ h : Fin d → ℝ, IsSubgradientCoord (ℓ t) z h)

end ModernOnlineLearning.ParameterFree


