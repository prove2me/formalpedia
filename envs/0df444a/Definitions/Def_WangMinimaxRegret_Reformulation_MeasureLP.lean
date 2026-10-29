-- Prove2me | Definitions.Def_WangMinimaxRegret_Reformulation_MeasureLP
-- name    : WangMinimaxRegret_Reformulation_MeasureLP
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:32:58.216389+00:00
-- url     : https://prove2.me/theorems/7376bf5f-cffc-4dc8-8d27-ecf9256986cc
-- title:
--   Nonnegative measure linear programs
-- statement:
--   A measure linear program has a carrier $S\subseteq\mathbb R$, a nonnegative extended cost $c$, real test functions $f_i$, and real right-hand sides $t_i$, indexed by a type $\iota$. A feasible decision is a nonnegative finite Borel measure $H$ supported on $S$ for which every $f_i$ is integrable and
--   $$\int f_i\,dH=t_i\quad(i\in\iota).$$
--   Its objective is the nonnegative integral $\int c\,dH$, and its value is the infimum over feasible measures, with empty infimum $+\infty$. There is no implicit probability normalization or support finiteness. For arbitrary cost functions the integral is the nonnegative lower integral; the screening instance has a Borel cost. This general object supplies the measure LP used in equation (3), separately from the seller model.
-- source:
--   Wang, Liu and Zhang (2024), Minimax Regret Robust Screening with Moment Information, https://doi.org/10.1287/msom.2023.0072, Section 2, p. 8, equation (3), general measure-program vocabulary

import Mathlib

open MeasureTheory Set
open scoped ENNReal NNReal
set_option autoImplicit false
noncomputable section

namespace WangMinimaxRegret.Reformulation

/-- A nonnegative measure linear program, with finite real constraint integrals
and a possibly infinite nonnegative objective. No probability normalization is implicit. -/
structure MeasureLP (ι : Type) where
  carrier : Set ℝ
  cost : ℝ → ℝ≥0∞
  test : ι → ℝ → ℝ
  target : ι → ℝ

def MeasureLP.Feasible {ι : Type} (L : MeasureLP ι) (H : Measure ℝ) : Prop :=
  IsFiniteMeasure H ∧ H L.carrierᶜ = 0 ∧
    ∀ i, Integrable (L.test i) H ∧ (∫ x, L.test i x ∂H) = L.target i

def MeasureLP.objective {ι : Type} (L : MeasureLP ι) (H : Measure ℝ) : ℝ≥0∞ :=
  ∫⁻ x, L.cost x ∂H

def MeasureLP.value {ι : Type} (L : MeasureLP ι) : ℝ≥0∞ :=
  ⨅ H : Measure ℝ, ⨅ (_ : L.Feasible H), L.objective H

end WangMinimaxRegret.Reformulation


