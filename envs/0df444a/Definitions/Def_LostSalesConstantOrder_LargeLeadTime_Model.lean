-- Prove2me | Definitions.Def_LostSalesConstantOrder_LargeLeadTime_Model
-- name    : LostSalesConstantOrder_LargeLeadTime_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T18:03:22.287305+00:00
-- url     : https://prove2.me/theorems/247c6d78-4b45-4f46-bc78-75885f0e69d6
-- title:
--   Problem (1), OPT(L, T), the cost of L periods from a given state, problem (4), and the demand constants Q, g, σ, ζ
-- statement:
--   This file sets up the finite-horizon lost-sales problem of Goldberg, Katz-Rogozhnikov, Lu, Sharma and Squillante on top of the published periodic-review lost-sales model `CappedBaseStock_Model`.
--
--   **The system.** The holding cost $h>0$ per unit and the lost-demand penalty $c>0$ per unit, the lead time $L\ge1$, and the demand law $\mathcal D$ on $[0,\infty)$ (with finite positive mean) come from the published model. Demands $D_1,D_2,\dots$ are i.i.d. with law $\mathcal D$. At the start of period $t$ there is inventory $I_t$ and a pipeline $\mathbf x_t=(x_{1,t},\dots,x_{L,t})$; first $x_{1,t}$ arrives, then an order is placed and joins the end of the pipeline, then $D_t$ is realized. The next inventory is $I_{t+1}=(I_t+x_{1,t}-D_t)^+$, the lost demand is $N_t=(I_t+x_{1,t}-D_t)^-$, and the period cost is $C_t=hI_{t+1}+cN_t$. The system starts empty, $I_1=0$, $\mathbf x_1=\mathbf 0$. An admissible policy chooses each order as a measurable function of the past demands and of a private uniform random seed.
--
--   **Problem (1) and OPT(L, T).** For a horizon $T$ and a policy $\pi$,
--   $$
--   \mathrm{cost}_{L,T}(\pi)=\sum_{t=L+1}^{T+L}\mathbb E[C^\pi_t],\qquad \mathrm{OPT}(L,T)=\inf_{\pi}\ \mathrm{cost}_{L,T}(\pi),
--   $$
--   both in $[0,\infty]$. The window cost of $\pi$ from period $\tau$ is $\mathbb E[\sum_{t=\tau}^{\tau+L-1}C^\pi_t]$.
--
--   **The window from a given state.** For a pipeline $\mathbf x\in[0,\infty)^L$ and an inventory $\mathcal I\ge0$, $\mathrm{windowCost}(\mathbf x,\mathcal I)$ is the expected cost of $L$ periods of the system started with inventory $\mathcal I$ and pipeline $\mathbf x$, with fresh i.i.d. demands; this is the paper's $\mathbb E[\sum_{t=\tau}^{\tau+L-1}C^\pi_t\mid \mathbf x^\pi_\tau=\mathbf x, I^\pi_\tau=\mathcal I]$, which does not depend on $\pi$ or $\tau$ because orders placed during the window arrive after it. $I^*_{L+1}$, the end inventory of that window, is `endInventory`. A pair $(\mathbf x^*,\mathcal I^*)$ **solves problem (4)** if $\mathbf 0\le\mathbf x^*\le Q\mathbf 1$ and it minimizes the window cost over all such pipelines and all $\mathcal I\ge0$. A policy has **orders bounded by $Q$** if with probability one it never orders more than $Q$. The average of a pipeline is $r^*=L^{-1}\sum_{i=1}^L x^*_i$.
--
--   **Demand constants (p. 5).** With $D\sim\mathcal D$: $E[D^2]$; the standard deviation $\sigma$; the skewness $\zeta=\mathbb E[|D-\mathbb E[D]|^3]\sigma^{-3}$; the $c/(c+h)$ quantile
--   $$
--   Q=\inf\{s\ge0:\ \mathbb P(D>s)\le h/(c+h)\};
--   $$
--   and the newsvendor cost $g=h\mathbb E[(Q-D)^+]+c\mathbb E[(D-Q)^+]$. The paper's standing assumptions that $\mathcal D$ has a finite third moment and is not deterministic are the predicates `FiniteThirdMoment` and `NonDeterministic`.
--
--   These objects are the vocabulary of every statement of the mission.
--
--   **Formalization Note** Time is zero-based: Lean period $t$ is the paper's period $t+1$, so problem (1) sums Lean periods $L,\dots,T+L-1$. Pipeline slot $i$ is the paper's $x_{i+1}$. The paper's penalty $c$ is the model's `prm.p`; the parameter record is called `prm`. Costs are lower Lebesgue integrals in $[0,\infty]$, so no non-integrable cost reads as $0$. $Q$ is the published `newsvendorLevel` at the one-period demand law ($\mathbb P(D>s)\le h/(c+h)$ iff $c/(c+h)\le\mathbb P(D\le s)$), and $g$ is the published `backorderCost` at $Q$. The infimum OPT is over the model's history-dependent randomized policies, a class that contains the paper's class $\Pi$ (orders that are possibly random functions of $T,t,I_t,\mathbf x_t$ and the primitives). The moments $E[D^2]$, $\sigma$, $\zeta$ are Bochner integrals; they are the true values under the finite-third-moment assumption, which every statement that uses them carries.
-- source:
--   Goldberg, Katz-Rogozhnikov, Lu, Sharma & Squillante, Asymptotic Optimality of Constant-Order Policies for Lost Sales Inventory Models with Large Lead Times, arXiv:1211.4063v2, pp. 4–5 (§2, problem (1)), p. 5 (§3.1, Q, g, σ, ζ), p. 6 (OPT(L, T), Lemma 3), p. 8 (problem (4), r*)

import Definitions.Def_CappedBaseStock_Model
import Definitions.Def_LostSalesOrderUpTo_Asymptotic_Backorder

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

namespace LostSalesConstantOrder.LargeLeadTime

/-!
Goldberg, Katz-Rogozhnikov, Lu, Sharma & Squillante, arXiv:1211.4063v2, §2 (pp. 4–5), §3.1 (p. 5),
§3.2 (p. 6), §4.1 (p. 6), §5 (p. 8): the finite-horizon lost-sales problem (1), OPT(L, T), the cost of
`L` consecutive periods started from a given state, and the demand constants Q, g, σ, ζ.

The lost-sales system itself is the published `CappedBaseStock` model: `prm : Parameters` carries
the lead time `prm.L = L`, the holding cost `prm.h = h` and the lost-demand penalty `prm.p = c` (the
paper's `c`; the Lean variable is called `prm` to avoid the clash), and `P : DemandLaw` is the demand
law 𝒟. Time is zero-based: Lean period `t` is the paper's period `t + 1`. Pipeline slot `i` is the
paper's `x_{i+1}`.
-/

/-- The paper's standing moment assumption (p. 4): 𝒟 has a finite third moment. -/
def FiniteThirdMoment (P : CappedBaseStock.DemandLaw) : Prop :=
  Integrable (fun d : ℝ≥0 => (d : ℝ) ^ 3) P.law

/-- The paper's standing assumption (p. 4): 𝒟 is not deterministic (not a point mass). -/
def NonDeterministic (P : CappedBaseStock.DemandLaw) : Prop :=
  ∀ a : ℝ≥0, P.law ≠ Measure.dirac a

/-- The expected cost of period `t` (Lean, zero-based) under the policy `π`, in `[0, ∞]`. -/
def periodExpectedCost (P : CappedBaseStock.DemandLaw) (prm : CappedBaseStock.Parameters)
    (π : CappedBaseStock.AdmissiblePolicy) (t : ℕ) : ℝ≥0∞ :=
  ∫⁻ ω, CappedBaseStock.periodCost prm (CappedBaseStock.run prm π ω t) (ω.1 t)
    ∂CappedBaseStock.sampleLaw P

/-- The objective of problem (1): `Σ_{t=L+1}^{T+L} E[C_t^π]`. Lean periods `L, …, T + L − 1`
are the paper's periods `L + 1, …, T + L`. -/
def costLT (P : CappedBaseStock.DemandLaw) (prm : CappedBaseStock.Parameters)
    (π : CappedBaseStock.AdmissiblePolicy) (T : ℕ) : ℝ≥0∞ :=
  ∑ t ∈ Finset.Ico prm.L (T + prm.L), periodExpectedCost P prm π t

/-- `OPT(L, T)` (p. 6): the infimum of problem (1) over all admissible policies of the model. -/
def optLT (P : CappedBaseStock.DemandLaw) (prm : CappedBaseStock.Parameters) (T : ℕ) : ℝ≥0∞ :=
  ⨅ π : CappedBaseStock.AdmissiblePolicy, costLT P prm π T

/-- The expected cost of the `L` consecutive periods starting at Lean period `t₀`:
`E[Σ_{t=τ}^{τ+L−1} C_t^π]` with `τ = t₀ + 1`. -/
def costWindow (P : CappedBaseStock.DemandLaw) (prm : CappedBaseStock.Parameters)
    (π : CappedBaseStock.AdmissiblePolicy) (t₀ : ℕ) : ℝ≥0∞ :=
  ∑ t ∈ Finset.Ico t₀ (t₀ + prm.L), periodExpectedCost P prm π t

/-- Pipeline entry with a natural-number index, `0` beyond the lead time. `slot x i` is the
paper's `x_{i+1}`. -/
def slot {L : ℕ} (x : Fin L → ℝ≥0) (i : ℕ) : ℝ≥0 :=
  if h : i < L then x ⟨i, h⟩ else 0

/-- The system started in state `s` (inventory `s.1`, pipeline `s.2`) and run on the demands
`d 0, d 1, …` (`d 0` is the first period's demand) with zero orders. Over the first `L` periods
orders never matter, since an order arrives `L` periods after it is placed. -/
def fromState (prm : CappedBaseStock.Parameters) (s : CappedBaseStock.State prm.L)
    (d : CappedBaseStock.DemandPath) : ℕ → CappedBaseStock.State prm.L
  | 0 => s
  | k + 1 => CappedBaseStock.step prm (fromState prm s d k) 0 (d k)

/-- `E[Σ_{t=τ}^{τ+L−1} C_t | x_τ = x, I_τ = 𝓘]` (Lemma 3, (4)): the expected cost of `L` periods
of the system started with pipeline `x` and inventory `𝓘`, the demands i.i.d. with law 𝒟. -/
def windowCost (P : CappedBaseStock.DemandLaw) (prm : CappedBaseStock.Parameters)
    (x : Fin prm.L → ℝ≥0) (I : ℝ≥0) : ℝ≥0∞ :=
  ∑ k ∈ Finset.range prm.L,
    ∫⁻ d, CappedBaseStock.periodCost prm (fromState prm (I, x) d k) (d k)
      ∂CappedBaseStock.demandPathLaw P

/-- `I_{τ+L}` for the system started at `(x, 𝓘)`: the inventory at the end of the window. -/
def endInventory (prm : CappedBaseStock.Parameters) (x : Fin prm.L → ℝ≥0) (I : ℝ≥0)
    (d : CappedBaseStock.DemandPath) : ℝ≥0 :=
  (fromState prm (I, x) d prm.L).1

/-- The second moment `E[D²]`. -/
def secondMoment (P : CappedBaseStock.DemandLaw) : ℝ :=
  ∫ d : ℝ≥0, (d : ℝ) ^ 2 ∂P.law

/-- σ, the standard deviation of `D` (p. 5). -/
def sigma (P : CappedBaseStock.DemandLaw) : ℝ :=
  Real.sqrt (∫ d : ℝ≥0, ((d : ℝ) - CappedBaseStock.mean P) ^ 2 ∂P.law)

/-- ζ = E[|D − E[D]|³] σ⁻³, the skewness of `D` (p. 5). -/
def skew (P : CappedBaseStock.DemandLaw) : ℝ :=
  (∫ d : ℝ≥0, |(d : ℝ) - CappedBaseStock.mean P| ^ 3 ∂P.law) / sigma P ^ 3

/-- `Q = inf{s ∈ ℝ⁺ : P(D > s) ≤ h/(c+h)}` (p. 5), the `c/(c+h)` quantile of 𝒟; it is the
published `newsvendorLevel` at the law of one period's demand (`P(D > s) ≤ h/(c+h)` iff
`c/(c+h) ≤ P(D ≤ s)`). -/
def Qlevel (P : CappedBaseStock.DemandLaw) (prm : CappedBaseStock.Parameters) : ℝ≥0 :=
  LostSalesOrderUpTo.Asymptotic.newsvendorLevel P.law prm.h prm.p

/-- `g = hE[(Q − D)^+] + cE[(D − Q)^+]` (p. 5), the published single-period newsvendor cost. -/
def gConst (P : CappedBaseStock.DemandLaw) (prm : CappedBaseStock.Parameters) : ℝ :=
  LostSalesOrderUpTo.Asymptotic.backorderCost P.law prm.h prm.p (Qlevel P prm)

/-- Lemma 5's bound: with probability one, the policy never orders more than `Q`. -/
def OrdersBounded (P : CappedBaseStock.DemandLaw) (π : CappedBaseStock.AdmissiblePolicy)
    (Q : ℝ≥0) : Prop :=
  ∀ᵐ ω ∂CappedBaseStock.sampleLaw P, ∀ t, CappedBaseStock.order π t ω ≤ Q

/-- `(x*, 𝓘*)` solves problem (4): it minimizes `windowCost` over pipelines in `[0, Q1]` and
inventories `𝓘 ∈ ℝ⁺`. -/
def IsWindowMinimizer (P : CappedBaseStock.DemandLaw) (prm : CappedBaseStock.Parameters)
    (x : Fin prm.L → ℝ≥0) (I : ℝ≥0) : Prop :=
  (∀ i, x i ≤ Qlevel P prm) ∧
    ∀ (x' : Fin prm.L → ℝ≥0) (I' : ℝ≥0), (∀ i, x' i ≤ Qlevel P prm) →
      windowCost P prm x I ≤ windowCost P prm x' I'

/-- `r* = L⁻¹ Σ_{i=1}^L x*_i` (p. 8), the average of a pipeline vector. -/
def rStar {L : ℕ} (x : Fin L → ℝ≥0) : ℝ≥0 :=
  (∑ i, x i) / L

end LostSalesConstantOrder.LargeLeadTime


