-- Prove2me | Definitions.Def_FreeSamples_FullRevenue_Policies
-- name    : FreeSamples_FullRevenue_Policies
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T13:54:08.168523+00:00
-- url     : https://prove2.me/theorems/a6b52970-d398-4563-93ab-7603de01190a
-- title:
--   Unrestricted observed-data stopping policies and extended optimal revenue
-- statement:
--   A free-sample policy consists of an observed-data stopping amount $T$, a terminal additional allocation $k_T\in[0,\infty]$, and a nonnegative terminal price $q_T$. Allocation and price are measurable with respect to $\mathcal F_T$, where $\mathcal F_t=\sigma(Y_s:0\le s\le t)$. Finite stopping amounts sell at the actual accepted payment determined by the Buyer's posterior and utility. $T=\infty$ means never selling, with payment zero.
--   $$R(\pi)=\mathbb E^S[\operatorname{pay}(k_T,q_T;m_T,v_T)\,\mathbf1\{T<\infty\}],\qquad V_{\rm free}=\sup_{\pi\text{ admissible}}R(\pi).$$
--   Both quantities take nonnegative extended real values. The policy class has no deterministic bound, finite-mean condition, revenue-integrability pin or latent-state information before full release. One-round policies are admissible policies with $T=0$ almost surely. A separately defined full-sale offer charges $BR$ at the stopping state; its admissibility up to null-set versions and optimality are conclusions of Lemma 3. A stopping reward is defined separately so arbitrary-offer revenue is never identified with $BR$ by definition.
-- source:
--   Drakopoulos & Makhdoumi, Providing Data Samples for Free, SSRN 3611003, pinned local PDF snapshot (creation metadata 2021-08-30; SHA-256 2e29ad6e37639d93e587e9999f63959d3eb52c66a1fe2ac7e78f3d33976e44c0), p.16, §4 and Lemma 3; pp.17–18, Theorem 1(a) and Seller expectation convention; pp.30–31, comparison proof

import Definitions.Def_FreeSamples_FullRevenue_Offers
import Definitions.Def_FreeSamples_FullRevenue_Learning

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace FreeSamples.FullRevenue

/-- A free-data stopping amount, terminal allocation and terminal price.
∞ stopping means all information is released freely and no sale is made. -/
structure PolicyData (Ω : Type*) where
  stop : Ω → WithTop ℝ≥0
  allocation : Ω → WithTop ℝ≥0
  price : Ω → ℝ≥0

/-- Nonanticipation and terminal information constraints. No boundedness,
finite-mean or expected-revenue integrability condition is imposed. -/
def IsAdmissible {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (ℱ : Filtration ℝ≥0 mΩ) (π : PolicyData Ω) : Prop :=
  ∃ hT : IsStoppingTime ℱ π.stop,
    @Measurable Ω ℝ≥0 hT.measurableSpace inferInstance π.price ∧
    @Measurable Ω (WithTop ℝ≥0) hT.measurableSpace inferInstance π.allocation

/-- Realized accepted price at a finite stopping amount; zero if never selling. -/
noncomputable def realizedRevenue (p : Revenue.Params) (u : ℝ → ℝ → ℝ)
    {Ω : Type*} (θ : Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (π : PolicyData Ω) (ω : Ω) : ℝ :=
  if π.stop ω = ⊤ then 0 else
    let t : ℝ≥0 := (π.stop ω).untopD 0
    payment u p.σsq (posteriorMean p θ B t ω) (p.buyerVar t)
      (π.allocation ω) (π.price ω)

/-- Seller expected revenue, allowing +∞ and avoiding a nonintegrable-real default. -/
noncomputable def expectedRevenue (p : Revenue.Params) (u : ℝ → ℝ → ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (θ : Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (π : PolicyData Ω) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal (realizedRevenue p u θ B π ω) ∂P

/-- Supremum over the entire source class of free-sample policies and terminal offers. -/
noncomputable def optimalRevenue (p : Revenue.Params) (u : ℝ → ℝ → ℝ)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) (θ : Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (ℱ : Filtration ℝ≥0 mΩ) : ℝ≥0∞ :=
  ⨆ (π : PolicyData Ω) (_ : IsAdmissible ℱ π), expectedRevenue p u P θ B π

/-- All one-round offers, allowing any ℱ₀-measurable price/allocation and null-set versions. -/
def IsOneRound {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (ℱ : Filtration ℝ≥0 mΩ) (π : PolicyData Ω) : Prop :=
  IsAdmissible ℱ π ∧ ∀ᵐ ω ∂P, π.stop ω = 0

/-- The actual full-remainder offer at a given stopping amount. Admissibility and
optimality are conclusions of Lemma 3, not fields of this definition. -/
noncomputable def fullSale {Ω : Type*} (p : Revenue.Params) (u : ℝ → ℝ → ℝ)
    (θ : Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (T : Ω → WithTop ℝ≥0) : PolicyData Ω where
  stop := T
  allocation := fun _ => ⊤
  price := fun ω =>
    let t : ℝ≥0 := (T ω).untopD 0
    (BR u (posteriorMean p θ B t ω) (p.buyerVar t)).toNNReal

/-- The reduced stopping reward, defined separately from arbitrary-offer revenue. -/
noncomputable def stoppingReward {Ω : Type*} (p : Revenue.Params) (u : ℝ → ℝ → ℝ)
    (θ : Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (T : Ω → WithTop ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  if T ω = ⊤ then 0 else
    let t : ℝ≥0 := (T ω).untopD 0
    bayesRisk u (posteriorMean p θ B t ω) (p.buyerVar t)

end FreeSamples.FullRevenue


