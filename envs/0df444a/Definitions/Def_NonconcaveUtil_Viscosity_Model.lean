-- Prove2me | Definitions.Def_NonconcaveUtil_Viscosity_Model
-- name    : NonconcaveUtil_Viscosity_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T02:18:28.763982+00:00
-- url     : https://prove2.me/theorems/1d87102d-58f0-4626-a1cb-30b18b201d12
-- title:
--   §3 and Assumption 3.1 — portfolio market, admissible wealth, and value function
-- statement:
--   A portfolio invests a fraction $\pi_s$ of wealth in one risky stock. Its discounted forward wealth starts at $W_t=w$ and satisfies
--
--   $$dW_s=W_s\pi_s(\eta\,ds+\sigma\,d\mathcal B_s),\qquad W_s\ge B,\quad d\le\pi_s\le u.$$
--
--   The market has excess return $\eta$, volatility $\sigma>0$, horizon $T>0$, liquidation floor $B\ge0$, and bounds $d\le0\le u$ that may be infinite. Its value function is the supremum of $\mathbb E[U(W_T)]$ over admissible strategies. Assumption 3.1 makes $U$ nondecreasing, right-continuous, and eventually bounded above by $w^{\hat p}$ for $0<\hat p<1$, with either a finite value at $B$ or the stated CRRA behavior near $B=0$. The definition also records the constrained Merton rate $\Lambda$ and its associated CRRA value.
--
--   These shared objects give the control problem used by every theorem in the mission.
--
--   **Formalization Note** Infinite bounds use extended real endpoints. Controls are progressively measurable and have an Itô integral and integrable terminal reward. The strong solution of the wealth equation is represented by the integral equation. The Brownian motion has independent future increments relative to the filtration. The nonzero portfolio assumption $d<0$ or $u>0$ excludes the degenerate $L=0$ case.
-- source:
--   Dai, Kou, Qian & Wan, Nonconcave utility maximization with portfolio bounds, accepted manuscript (Management Science 68(11), 2022; DOI 10.1287/mnsc.2021.4228), pp. 7–11 (PDF 7–11), §3, Assumption 3.1, (1)–(4), (13), footnote 5

import Mathlib
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace NonconcaveUtil.Viscosity

/-- The one-stock, constant-coefficient market of §3. Infinite portfolio endpoints are EReal. -/
structure Market where
  eta : ℝ
  sigma : ℝ
  T : ℝ
  B : ℝ
  d : EReal
  u : EReal

/-- Standing assumptions of §3 and the nondegeneracy assumptions of EC.1.1. -/
def Market.Standing (mk : Market) : Prop :=
  0 < mk.sigma ∧ 0 < mk.T ∧ 0 ≤ mk.B ∧ mk.d ≤ 0 ∧ 0 ≤ mk.u ∧
    (mk.d < 0 ∨ 0 < mk.u)

def Market.Weights (mk : Market) : Set ℝ :=
  {π | mk.d ≤ (π : EReal) ∧ (π : EReal) ≤ mk.u}

def Market.Bounded (mk : Market) : Prop := mk.d ≠ ⊥ ∧ mk.u ≠ ⊤

/-- Used only under `Bounded`; otherwise `EReal.toReal` loses infinite endpoints. -/
noncomputable def Market.L (mk : Market) : ℝ :=
  mk.sigma * max mk.u.toReal (-mk.d.toReal)

def Market.D (mk : Market) : Set (ℝ × ℝ) := Set.Ico 0 mk.T ×ˢ Set.Ioi mk.B

inductive BdryCase where
  | finite
  | crra (pTilde A1 A2 : ℝ)

noncomputable def crraU (pTilde A1 A2 w : ℝ) : ℝ :=
  if pTilde = 0 then A1 * Real.log w + A2
  else A1 * (w ^ pTilde - 1) / pTilde + A2

/-- Assumption 3.1. In the singular case, the value of `U 0` is unused. -/
structure Assumption31 (mk : Market) (U : ℝ → ℝ) (pHat : ℝ)
    (bc : BdryCase) : Prop where
  pHat_mem : 0 < pHat ∧ pHat < 1
  growth : ∃ W₀ : ℝ, ∀ w ≥ W₀, U w ≤ w ^ pHat
  boundary : match bc with
    | .finite => MonotoneOn U (Set.Ici mk.B) ∧
        ∀ w ≥ mk.B, ContinuousWithinAt U (Set.Ici w) w
    | .crra pTilde A1 A2 => mk.B = 0 ∧ pTilde ≤ 0 ∧ 0 < A1 ∧
        MonotoneOn U (Set.Ioi 0) ∧
        (∀ w > 0, ContinuousWithinAt U (Set.Ici w) w) ∧
        (∃ ε > 0, ∀ w ∈ Set.Ioo 0 ε, U w = crraU pTilde A1 A2 w) ∧
        ∀ w > 0, crraU pTilde A1 A2 w ≤ U w

/-- The bounded-portfolio Merton rate of footnote 5 and EC.24. For `q < 1`, the
quadratic is bounded above even when one portfolio endpoint is infinite. -/
noncomputable def Market.Lam (mk : Market) (q : ℝ) : ℝ :=
  sSup ((fun π : ℝ => mk.eta * π - (1 - q) / 2 * mk.sigma ^ 2 * π ^ 2) '' mk.Weights)

noncomputable def VCRRA (mk : Market) (pTilde A1 A2 t w : ℝ) : ℝ :=
  if pTilde = 0 then A1 * (Real.log w + mk.Lam 0 * (mk.T - t)) + A2
  else A1 * (Real.exp (pTilde * mk.Lam pTilde * (mk.T - t)) * w ^ pTilde - 1) /
    pTilde + A2

/-- A Brownian motion relative to the information filtration: each future increment
is independent of the information available at its starting time. -/
def IsFBrownian {Ω : Type*} [m : MeasurableSpace Ω] (P : Measure Ω)
    (ℱ : Filtration ℝ≥0 m) (𝓑 : ℝ≥0 → Ω → ℝ) : Prop :=
  IsBrownianReal 𝓑 P ∧ Adapted ℱ 𝓑 ∧
    ∀ s t : ℝ≥0, s ≤ t →
      ProbabilityTheory.Indep
        (MeasurableSpace.comap (fun ω => 𝓑 t ω - 𝓑 s ω) inferInstance) (ℱ s) P

/-- A control and the wealth/Itô-integral processes in the strong formulation. -/
structure Control (Ω : Type*) where
  π : ℝ≥0 → Ω → ℝ
  J : ℝ≥0 → Ω → ℝ
  W : ℝ≥0 → Ω → ℝ

/-- Equations (2)–(3): the wealth SDE, admissible weights, and the liquidation floor.
The Itô relation uses the published Brownian-integral construction. -/
def Admissible {Ω : Type*} [MeasurableSpace Ω] (mk : Market) (P : Measure Ω)
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (𝓑 : ℝ≥0 → Ω → ℝ)
    (t w : ℝ) (a : Control Ω) : Prop :=
  IsStronglyProgressive ℱ a.π ∧
  (∀ᵐ ω ∂P, ∀ s : ℝ≥0, t ≤ (s : ℝ) ∧ (s : ℝ) ≤ mk.T → a.π s ω ∈ mk.Weights) ∧
  (∀ ω, IntervalIntegrable (fun r : ℝ => a.π r.toNNReal ω ^ 2) volume t mk.T) ∧
  EthierKurtz.HasBrownianItoIntegral P (fun s => ℱ s) 𝓑
    (fun s ω => if t ≤ (s : ℝ) then mk.sigma * a.W s ω * a.π s ω else 0) a.J ∧
  (∀ ω, ∀ s : ℝ, t ≤ s → s ≤ mk.T →
    IntervalIntegrable (fun r : ℝ => mk.eta * a.W r.toNNReal ω * a.π r.toNNReal ω)
      volume t s) ∧
  (∀ᵐ ω ∂P, ∀ s : ℝ, t ≤ s → s ≤ mk.T →
    a.W s.toNNReal ω = w +
      ∫ r in t..s, mk.eta * a.W r.toNNReal ω * a.π r.toNNReal ω +
      (a.J s.toNNReal ω - a.J t.toNNReal ω)) ∧
  (∀ᵐ ω ∂P, ∀ s : ℝ, t ≤ s → s ≤ mk.T → mk.B ≤ a.W s.toNNReal ω)

/-- The value in (4), as a supremum of genuine, finite expectations. The set of
controls excludes a nonintegrable reward, whose Bochner integral would be zero. -/
noncomputable def valueFn {Ω : Type*} [MeasurableSpace Ω] (mk : Market)
    (U : ℝ → ℝ) (P : Measure Ω) (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (𝓑 : ℝ≥0 → Ω → ℝ) (t w : ℝ) : EReal :=
  sSup {z : EReal | ∃ a : Control Ω,
    Admissible mk P ℱ 𝓑 t w a ∧
      Integrable (fun ω => U (a.W mk.T.toNNReal ω)) P ∧
      z = ((∫ ω, U (a.W mk.T.toNNReal ω) ∂P : ℝ) : EReal)}

end NonconcaveUtil.Viscosity


