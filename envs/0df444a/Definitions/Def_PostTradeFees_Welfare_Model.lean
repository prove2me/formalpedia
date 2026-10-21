-- Prove2me | Definitions.Def_PostTradeFees_Welfare_Model
-- name    : PostTradeFees_Welfare_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T09:16:31.054246+00:00
-- url     : https://prove2.me/theorems/e04c638c-55cd-40a0-aa3e-06739878fdab
-- title:
--   §3–§5 and Appendix — limit-order market, fee structures, stationary equilibria, and welfare
-- statement:
--   Each period one risk-neutral buyer or seller arrives, with valuations $V_h$ and $V_l$, respectively. One of $N>1$ brokers submits her order. A limit order survives for one period and is taken by the next opposite-side arrival when the gain from a market order is at least her value from posting a fresh limit order. Each trade has two legs. A uniform fee charges $(N-1)c/N$ per leg; a trade-specific fee charges zero for an internalized trade and $c$ for a trade across brokers.
--
--   A stationary equilibrium is a pair of buyer and seller continuation values attained as greatest expected limit-order profits over all possible quotes. An optimal quote may attract counterparties at every broker ("all"), only at the same broker ("own"), or none. The induced three-state transition matrix records a limit order, an internalized market order, or a non-internalized market order. If $\varphi$ is its stationary distribution, expected welfare per period is
--
--   $$
--   W(\varphi)=\varphi_1(V_h-V_l)+\varphi_2(V_h-V_l-2c).
--   $$
--
--   The model also defines the expected fee per leg $E(fee)=\frac1N fee_{\mathrm{in}}+\frac{N-1}{N}fee_{\mathrm{out}}$, the three thresholds $c_1$, $c_2$, and $c_U$ and the closed-form quotes of Equations (2)–(4). It supplies the objects used by the equilibrium and welfare theorems.
--
--   **Formalization Note** $N$ is natural, $N>1$, $V_h>V_l\ge0$, and $c>0$. The hit rule chooses a market order at equality, and "all" wins a strategy tie. The stationary best-response fixed point makes the paper's implicit equilibrium convention explicit. The unreachable third state in (A2) returns to the limit-order state, repairing its printed zero row while preserving (A3). State indices are $0,1,2$ in Lean.
-- source:
--   Degryse, Van Achter & Wuyts, Plumbing of Securities Markets, SSRN 2023597 (version of October 2016), pp. 8–16 (PDF 9–17), §§3–5, Equations (2)–(8); Appendix pp. 1–2 (PDF 29–30), (A1)–(A3)

import Mathlib
import Definitions.Def_MarkovChain

namespace PostTradeFees.Welfare

open Classical

structure Params where
  N : ℕ
  Vh : ℝ
  Vl : ℝ
  c : ℝ

def Params.Standing (P : Params) : Prop :=
  1 < P.N ∧ 0 ≤ P.Vl ∧ P.Vl < P.Vh ∧ 0 < P.c

inductive FeeStructure | uniform | tradeSpecific

/-- Fee paid by each leg; `internal = true` means a common broker. -/
noncomputable def fee (P : Params) : FeeStructure → Bool → ℝ
  | .uniform, _ => (((P.N : ℝ) - 1) / (P.N : ℝ)) * P.c
  | .tradeSpecific, true => 0
  | .tradeSpecific, false => P.c

/-- Expected fee per leg of a trade, E(fee): the counterparty uses the same broker
with probability `1/N` and another broker with probability `(N-1)/N`. -/
noncomputable def expectedFee (P : Params) (k : FeeStructure) : ℝ :=
  (1 / (P.N : ℝ)) * fee P k true + (((P.N : ℝ) - 1) / (P.N : ℝ)) * fee P k false

/-- A seller takes a standing bid when the market order is at least as valuable as a new limit order. -/
noncomputable def SellerHits (P : Params) (k : FeeStructure) (internal : Bool)
    (Vs B : ℝ) : Prop := Vs ≤ B - P.Vl - fee P k internal

noncomputable def BuyerHits (P : Params) (k : FeeStructure) (internal : Bool)
    (Vb A : ℝ) : Prop := Vb ≤ P.Vh - A - fee P k internal

noncomputable def bidProfit (P : Params) (k : FeeStructure) (Vs B : ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    ((1 / (P.N : ℝ)) *
        (if SellerHits P k true Vs B then P.Vh - B - fee P k true else 0) +
     (((P.N : ℝ) - 1) / (P.N : ℝ)) *
        (if SellerHits P k false Vs B then P.Vh - B - fee P k false else 0))

noncomputable def askProfit (P : Params) (k : FeeStructure) (Vb A : ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    ((1 / (P.N : ℝ)) *
        (if BuyerHits P k true Vb A then A - P.Vl - fee P k true else 0) +
     (((P.N : ℝ) - 1) / (P.N : ℝ)) *
        (if BuyerHits P k false Vb A then A - P.Vl - fee P k false else 0))

/-- Stationary continuation values are attained best responses on both sides. -/
noncomputable def IsEquilibrium (P : Params) (k : FeeStructure) (Vb Vs : ℝ) : Prop :=
  IsGreatest (Set.range (bidProfit P k Vs)) Vb ∧
  IsGreatest (Set.range (askProfit P k Vb)) Vs

noncomputable def PlaysAll (P : Params) (k : FeeStructure) (Vb Vs : ℝ) : Prop :=
  (∃ B, bidProfit P k Vs B = Vb ∧ SellerHits P k true Vs B ∧
    SellerHits P k false Vs B) ∧
  (∃ A, askProfit P k Vb A = Vs ∧ BuyerHits P k true Vb A ∧
    BuyerHits P k false Vb A)

noncomputable def PlaysOwn (P : Params) (k : FeeStructure) (Vb Vs : ℝ) : Prop :=
  ¬ PlaysAll P k Vb Vs ∧
  (∃ B, bidProfit P k Vs B = Vb ∧ SellerHits P k true Vs B ∧
    ¬ SellerHits P k false Vs B) ∧
  (∃ A, askProfit P k Vb A = Vs ∧ BuyerHits P k true Vb A ∧
    ¬ BuyerHits P k false Vb A)

noncomputable def RefrainsFromTrading (P : Params) (k : FeeStructure)
    (Vb Vs : ℝ) : Prop :=
  (∀ B, bidProfit P k Vs B = Vb →
    ¬ SellerHits P k true Vs B ∧ ¬ SellerHits P k false Vs B) ∧
  (∀ A, askProfit P k Vb A = Vs →
    ¬ BuyerHits P k true Vb A ∧ ¬ BuyerHits P k false Vb A)

/-- State 0: limit order; state 1: internalized market order; state 2: external market order. -/
noncomputable def chain (N : ℕ) (hitOwn hitOther : Prop) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  let pI : ℝ := if hitOwn then 1 / (2 * (N : ℝ)) else 0
  let pX : ℝ := if hitOther then ((N : ℝ) - 1) / (2 * (N : ℝ)) else 0
  !![1 - pI - pX, pI, pX; 1, 0, 0; 1, 0, 0]

noncomputable def chainAll (N : ℕ) : Matrix (Fin 3) (Fin 3) ℝ :=
  chain N True True

/-- The printed third row of (A2) is zero; the unreachable state returns to LO here. -/
noncomputable def chainOwn (N : ℕ) : Matrix (Fin 3) (Fin 3) ℝ :=
  chain N True False

noncomputable def eqChain (P : Params) (k : FeeStructure) (Vb Vs : ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  chain P.N (PlaysAll P k Vb Vs ∨ PlaysOwn P k Vb Vs)
    (PlaysAll P k Vb Vs)

def tradingRate (φ : Fin 3 → ℝ) : ℝ := φ 1 + φ 2
noncomputable def internalizationRate (φ : Fin 3 → ℝ) : ℝ :=
  φ 1 / (φ 1 + φ 2)
def welfare (P : Params) (φ : Fin 3 → ℝ) : ℝ :=
  φ 1 * (P.Vh - P.Vl) + φ 2 * (P.Vh - P.Vl - 2 * P.c)

noncomputable def c1 (P : Params) : ℝ :=
  2 * (P.N : ℝ) * ((P.N : ℝ) - 1) * (P.Vh - P.Vl) /
    ((2 * (P.N : ℝ) + 1) * (2 * (P.N : ℝ) - 1))
noncomputable def c2 (P : Params) : ℝ :=
  (P.N : ℝ) * (P.Vh - P.Vl) / (2 * (P.N : ℝ) + 1)
noncomputable def cU (P : Params) : ℝ :=
  (P.N : ℝ) * (P.Vh - P.Vl) / (2 * ((P.N : ℝ) - 1))

noncomputable def AstarUall (P : Params) : ℝ :=
  (2 * P.Vh + P.Vl) / 3 - ((P.N : ℝ) - 1) * P.c / (3 * (P.N : ℝ))
noncomputable def BstarUall (P : Params) : ℝ :=
  (P.Vh + 2 * P.Vl) / 3 + ((P.N : ℝ) - 1) * P.c / (3 * (P.N : ℝ))
noncomputable def AstarTSall (P : Params) : ℝ :=
  (2 * P.Vh + P.Vl) / 3 - ((P.N : ℝ) + 1) * P.c / (3 * (P.N : ℝ))
noncomputable def BstarTSall (P : Params) : ℝ :=
  (P.Vh + 2 * P.Vl) / 3 + ((P.N : ℝ) + 1) * P.c / (3 * (P.N : ℝ))
noncomputable def AstarTSown (P : Params) : ℝ :=
  (2 * P.Vh * (P.N : ℝ) + P.Vl) / (2 * (P.N : ℝ) + 1)
noncomputable def BstarTSown (P : Params) : ℝ :=
  (P.Vh + 2 * P.Vl * (P.N : ℝ)) / (2 * (P.N : ℝ) + 1)

def observedSpread (A B : ℝ) : ℝ := A - B
noncomputable def cumSpread (P : Params) (k : FeeStructure) (internal : Bool)
    (A B : ℝ) : ℝ := observedSpread A B + 2 * fee P k internal

noncomputable def averageCumSpread (P : Params) (k : FeeStructure)
    (A B : ℝ) : ℝ :=
  observedSpread A B + 2 * expectedFee P k

end PostTradeFees.Welfare


