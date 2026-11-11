-- Prove2me | Definitions.Def_IndependentInfoPricing_Main_Menus
-- name    : IndependentInfoPricing_Main_Menus
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:31:35.437311+00:00
-- url     : https://prove2.me/theorems/5ed00fe8-1e9a-4c6c-ade0-2e828f4fd485
-- title:
--   Finite menus, seller-favorable ties and the simple benchmarks
-- statement:
--   For a finite menu $M$ containing both free options, define additive and actual menu values by maximizing respectively $v\cdot x-p$ and $V(v,x)-p$. The payment is the highest price among the maximizing entries. The expected payments, written $\operatorname{Rev}^{\rm rel}(M)$ and $\operatorname{Rev}(M)$, remain separate.
--
--   Activation offers every subset $T$ at allocation $1_T$ and price $\sum_{i\in T}p_i$. Deactivation offers every subset at allocation $1_T$ and price $\sum_{i\notin T}p_i$. Both include $(0,0)$ and $(1,0)$. Symmetrization offers every ordered pair's allocation $(x_a+1-x_b)/2$ at price $(p_a+p_b)/2$.
--
--   $$\widetilde R=\max\{\widetilde{\operatorname{SRev}},\operatorname{FRev}\},\qquad R=\max\{\operatorname{SRev}^{\pm},\operatorname{FRev}\}.$$
--
--   The separate benchmarks optimize one nonnegative finite price vector before any sign or value is observed. Symmetrized revenue uses actual experiment evaluation. Full revelation charges a single price for learning the state and sells exactly when both total positive and total negative magnitudes exceed that price. Finite-menu implementation means a measurable direct selection obeying full information IC, attaining actual menu value and the highest maximizing price. These definitions are reused in both proof branches. Real suprema here occur only for finite menus; empty menus have default value zero and are never used as valid menus.
-- source:
--   Hu Fu, Chenshuo Guo, STOC 2027 submission #1459 (October 2026), §§2–4.5, starting printed p.8 (PDF p.10); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1459.pdf

import Definitions.Def_IndependentInfoPricing_Main_Model

open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section

namespace IndependentInfoPricing.Main

variable {ι : Type} [Fintype ι]

abbrev Menu (ι : Type) := Finset (Values ι × ℝ)

def HasFree (M : Menu ι) : Prop := (0, 0) ∈ M ∧ (1, 0) ∈ M

def ValidMenu (M : Menu ι) : Prop :=
  HasFree M ∧ ∀ e ∈ M, 0 ≤ e.2 ∧ ∀ i, e.1 i ∈ Set.Icc (0 : ℝ) 1

def ReverseClosed (M : Menu ι) : Prop := ∀ e ∈ M, (1 - e.1, e.2) ∈ M

def menuValue (realResponse : Bool) (M : Menu ι) (v : Values ι) : ℝ :=
  sSup {u | ∃ e ∈ M,
    u = (if realResponse then binaryValue v e.1 else dot v e.1) - e.2}

/-- Largest price among the utility maximizers, including ties with either free option. -/
def menuPayment (realResponse : Bool) (M : Menu ι) (v : Values ι) : ℝ :=
  sSup {p | ∃ e ∈ M, p = e.2 ∧
    (if realResponse then binaryValue v e.1 else dot v e.1) - e.2 = menuValue realResponse M v}

def menuRevenue (realResponse : Bool) (F : Measure (Values ι)) (M : Menu ι) : ℝ≥0∞ :=
  ∫⁻ v, ENNReal.ofReal (menuPayment realResponse M v) ∂F

def ImplementsMenu (M : Menu ι) : Prop :=
  ∃ m : DirectMechanism ι, InformationOn Set.univ m ∧
    ∀ v, (m.allocation v, m.price v) ∈ M ∧
      binaryValue v (m.allocation v) - m.price v = menuValue true M v ∧
      m.price v = menuPayment true M v

def symmetrize (M : Menu ι) : Menu ι := by
  classical
  exact (M ×ˢ M).image (fun e => ((fun i => (e.1.1 i + 1 - e.2.1 i) / 2), (e.1.2 + e.2.2) / 2))

def activation (p : Values ι) : Menu ι := by
  classical
  exact (Finset.univ : Finset ι).powerset.image (fun T =>
    ((fun i => if i ∈ T then (1 : ℝ) else 0), ∑ i ∈ T, p i)) ∪ {(0, 0), (1, 0)}

def deactivation (p : Values ι) : Menu ι := by
  classical
  exact (Finset.univ : Finset ι).powerset.image (fun T =>
    ((fun i => if i ∈ T then (1 : ℝ) else 0), ∑ i ∈ Finset.univ \ T, p i)) ∪ {(0, 0), (1, 0)}

def sRevPlus (F : Measure (Values ι)) : ℝ≥0∞ :=
  ⨆ (p : Values ι) (_ : ∀ i, 0 ≤ p i), menuRevenue false F (activation p)

def sRevMinus (F : Measure (Values ι)) : ℝ≥0∞ :=
  ⨆ (p : Values ι) (_ : ∀ i, 0 ≤ p i), menuRevenue false F (deactivation p)

def sRevBoth (F : Measure (Values ι)) : ℝ≥0∞ := max (sRevPlus F) (sRevMinus F)

def sRevSym (F : Measure (Values ι)) : ℝ≥0∞ :=
  ⨆ (p : Values ι) (_ : ∀ i, 0 ≤ p i), menuRevenue true F (symmetrize (activation p))

def positiveTotal (v : Values ι) : ℝ := ∑ i, max (v i) 0

def negativeTotal (v : Values ι) : ℝ := ∑ i, max (-v i) 0

def fullRev (F : Measure (Values ι)) : ℝ≥0∞ :=
  ⨆ (p : ℝ) (_ : 0 ≤ p), ENNReal.ofReal p * F {v | p ≤ positiveTotal v ∧ p ≤ negativeTotal v}

def benchmark (F : Measure (Values ι)) : ℝ≥0∞ := max (sRevBoth F) (fullRev F)

def benchmarkSym (F : Measure (Values ι)) : ℝ≥0∞ := max (sRevSym F) (fullRev F)

end IndependentInfoPricing.Main


