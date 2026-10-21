-- Prove2me | Definitions.Def_BetaCoskew_ThreeMoment_Market
-- name    : BetaCoskew_ThreeMoment_Market
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:49:08.367001+00:00
-- url     : https://prove2.me/theorems/06e45694-09b5-4f7b-a721-7e8321d3d110
-- title:
--   §2.1 and Assumption 1(i): atomless one-period priced market
-- statement:
--   A one-period market has a probability measure $P$, a finite list of total asset returns $R_i$, a pricing kernel $\tilde m$, and a risk-free total return $1+r_f$. Every $R_i$ is measurable and has a genuine finite kernel-weighted expectation. The kernel is measurable, strictly positive almost surely, and integrable. The pricing equations and risk-free asset are
--
--   $$
--   \mathbb E_P[\tilde mR_i]=1\quad\text{for every asset }i,
--   \qquad R_{i_0}=1+r_f\quad\text{for some }i_0.
--   $$
--
--   An atomless probability space means every measurable event of positive probability contains a measurable subset of strictly intermediate probability. This is the measure-theoretic assumption of the paper, beyond the vanishing of singleton probabilities.
--
--   These objects provide the market side of the equilibrium pricing statement.
-- source:
--   Shi, Cui & Zhou, Beta and coskewness pricing: perspective from probability weighting, SSRN 3579960 (version of June 2, 2020), pp. 8–9, §2.1 and Assumption 1(i)

import Mathlib

namespace BetaCoskew.ThreeMoment

open MeasureTheory

/-- Assumption 1(i): every positive-measure event contains a strictly smaller
positive-measure measurable event. -/
def Atomless {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) : Prop :=
  ∀ A : Set Ω, MeasurableSet A → 0 < P A →
    ∃ B : Set Ω, B ⊆ A ∧ MeasurableSet B ∧ 0 < P B ∧ P B < P A

/-- A one-period market whose total asset returns are priced by a strictly positive
integrable kernel, with one risk-free asset. -/
structure IsPricedMarket {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (mt : Ω → ℝ) (rf : ℝ) {n : ℕ} (R : Fin n → Ω → ℝ) : Prop where
  measurable_mt : Measurable mt
  pos : ∀ᵐ ω ∂P, 0 < mt ω
  integrable_mt : Integrable mt P
  measurable_R : ∀ i, Measurable (R i)
  integrable_price : ∀ i, Integrable (fun ω => mt ω * R i ω) P
  price : ∀ i, ∫ ω, mt ω * R i ω ∂P = 1
  riskfree : ∃ i0, R i0 = fun _ => 1 + rf

end BetaCoskew.ThreeMoment


