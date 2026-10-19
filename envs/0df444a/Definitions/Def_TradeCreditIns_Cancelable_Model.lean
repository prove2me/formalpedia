-- Prove2me | Definitions.Def_TradeCreditIns_Cancelable_Model
-- name    : TradeCreditIns_Cancelable_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T22:20:03.556565+00:00
-- url     : https://prove2.me/theorems/dade6462-9be8-48e1-aea6-80bc8443f09c
-- title:
--   §3–§6 and Table 1 — three-signal cancelable trade credit insurance model
-- statement:
--   A supplier sells one unit at credit price $r$ to a buyer who may default, or takes an outside payment $r_0$. Monitoring by a competitive insurer costs $c$ and reveals one of three signals with probabilities $\theta_i$ and conditional default probabilities $\beta_i$; the prior default probability is $\bar\beta=\sum_i\theta_i\beta_i$. If end-of-period cash flow is $x$, the supplier's financing cost is
--
--   $$
--   L(x)=l\max\{T-x,0\}.
--   $$
--
--   A cancelable contract $\kappa=(p,\delta,f)$ has premium $p$, deductible $\delta\in[0,r]$, and refund $f\in[0,p]$. After observing a signal, the insurer may cancel coverage and refund $f$; the supplier then chooses whether to ship. The model defines these choices by their payoff comparisons, the supplier's expected payoff, the insurer's monitoring cost and alternatives, and the set of contracts under which the insurer monitors and cancels for at least one signal. The first-best is the maximum payoff of a financially unconstrained planner over the no-monitoring choice and all three-signal shipping policies.
--
--   This common model supports the paper's monitoring and optimal-contract statements.
--
--   **Formalization Note** Signals are indexed by Fin 3, so Lean index 0 denotes the paper's signal 1. The paper's Table 1 supplies $\bar\beta=\sum_i\theta_i\beta_i$, instead of the inconsistent Bayes display on p. 9. The standing assumptions use $c>0$, $l\ge0$, and $\theta_1>0$ as disclosed in the mission scope. For ties, shipping under coverage uses the weak comparison in (1), while cancelation and shipping after cancelation use the strict choices in the proof of Proposition 3, (64)–(66). Decisions use payoff comparisons, so the zero denominator of the paper's covered-shipping threshold at the proposed contract cannot change them.
-- source:
--   Yang, Bakshi & Chen, Trade credit insurance: operational value and contract choice, accepted manuscript (Management Science 67(2), 2021; LBS Research Online eprint 1343), pp. 7–18 (PDF 8–19), §§3–6, Assumptions 1–2, Table 1 p. 30 (PDF 31)

import Mathlib

namespace TradeCreditIns.Cancelable
open scoped Classical

/-! The three-signal trade credit insurance model of Yang, Bakshi and Chen (2021).
`Fin 3` indices 0, 1, 2 correspond to the paper's signals 1, 2, 3. -/

structure Params where
  r : ℝ
  r0 : ℝ
  T : ℝ
  l : ℝ
  c : ℝ
  θ : Fin 3 → ℝ
  β : Fin 3 → ℝ

def Params.βbar (P : Params) : ℝ := ∑ i, P.θ i * P.β i

def Params.Standing (P : Params) : Prop :=
  (∀ i, 0 ≤ P.θ i) ∧ (∑ i, P.θ i) = 1 ∧ 0 < P.θ 0 ∧
  0 ≤ P.β 0 ∧ P.β 0 < P.β 1 ∧ P.β 1 < P.β 2 ∧ P.β 2 ≤ 1 ∧
  P.r0 < P.r ∧ P.r0 < (1 - P.βbar) * P.r ∧ 0 ≤ P.l ∧ 0 < P.c

def Assumption1 (P : Params) : Prop := (1 - P.β 2) * P.r < P.r0
def Assumption2 (P : Params) : Prop := 0 ≤ P.T ∧ P.T < P.r0 - (P.r - P.r0)

def L (P : Params) (x : ℝ) : ℝ := P.l * max (P.T - x) 0
def φ (P : Params) : ℝ :=
  ∑ i, P.θ i * max (P.r0 - (1 - P.β i) * P.r) 0

structure Contract where
  p : ℝ
  δ : ℝ
  f : ℝ

def Contract.IsCancelable (P : Params) (κ : Contract) : Prop :=
  0 ≤ κ.δ ∧ κ.δ ≤ P.r ∧ 0 ≤ κ.f ∧ κ.f ≤ κ.p

def ShipsCovered (P : Params) (κ : Contract) (b : ℝ) : Prop :=
  P.r0 ≤ P.r - b * (κ.δ + L P (P.r - κ.δ - κ.p))

def ShipsUncovered (P : Params) (κ : Contract) (b : ℝ) : Prop :=
  P.r0 < P.r - b * (P.r + L P (κ.f - κ.p))

def Cancels (P : Params) (κ : Contract) (b : ℝ) : Prop :=
  ShipsCovered P κ b ∧ κ.f < b * (P.r - κ.δ)

def Ships (P : Params) (κ : Contract) (b : ℝ) : Prop :=
  if Cancels P κ b then ShipsUncovered P κ b else ShipsCovered P κ b

noncomputable def supplierPayoff (P : Params) (κ : Contract) : ℝ :=
  -κ.p + ∑ i, P.θ i *
    (if Cancels P κ (P.β i) then
       κ.f + (if ShipsUncovered P κ (P.β i) then
         (1 - P.β i) * P.r - P.β i * L P (κ.f - κ.p) else P.r0)
     else if ShipsCovered P κ (P.β i) then
       P.r - P.β i * (κ.δ + L P (P.r - κ.δ - κ.p))
     else P.r0)

noncomputable def insurerCostEffort (P : Params) (κ : Contract) : ℝ :=
  P.c + ∑ i, P.θ i *
    (if Cancels P κ (P.β i) then κ.f
     else if ShipsCovered P κ (P.β i) then P.β i * (P.r - κ.δ) else 0)

noncomputable def insurerCostKeep (P : Params) (κ : Contract) : ℝ :=
  if ShipsCovered P κ P.βbar then P.βbar * (P.r - κ.δ) else 0

def InsurerMonitors (P : Params) (κ : Contract) : Prop :=
  insurerCostEffort P κ ≤ insurerCostKeep P κ ∧
  insurerCostEffort P κ ≤ κ.f ∧
  insurerCostEffort P κ ≤ κ.p

def Admissible (P : Params) (κ : Contract) : Prop :=
  κ.IsCancelable P ∧ InsurerMonitors P κ ∧ ∃ i, Cancels P κ (P.β i)

noncomputable def firstBest (P : Params) : ℝ :=
  max (max ((1 - P.βbar) * P.r) P.r0)
    (Finset.univ.sup' Finset.univ_nonempty
      (fun s : Fin 3 → Bool =>
        (∑ i, P.θ i * (if s i then (1 - P.β i) * P.r else P.r0)) - P.c))

def noInsurance (P : Params) : ℝ :=
  max ((1 - P.βbar) * P.r - P.βbar * L P 0) P.r0

noncomputable def κstar (P : Params) : Contract :=
  ⟨P.c / P.θ 0 + P.β 0 * P.r, 0, P.c / P.θ 0 + P.β 0 * P.r⟩

end TradeCreditIns.Cancelable


