-- Prove2me | Definitions.Def_PerishablePricing_Backlog_Supplement_IntegerLostSalesModel
-- name    : PerishablePricing_Backlog_Supplement_IntegerLostSalesModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T07:00:21.424369+00:00
-- url     : https://prove2.me/theorems/99a5febf-e3aa-44b7-9c4b-8df4b94e5187
-- title:
--   Equations (3)–(6) — the integer lost-sales Bellman recursion and largest optimizers
-- statement:
--   This is the zero-lead-time lost-sales model over integer states and actions. Lifetime is $l=L+1\ge1$, the state is $s\in\mathcal V^+_{L,L}\subseteq\mathbb Z^L$, and an order/demand pair satisfies $S\ge s_L$ and $d\in\mathcal D\cap\mathbb Z$. With integer noise $\varepsilon$, depletion ranges over every integer in $[s_1\vee(d+\varepsilon),S\vee(d+\varepsilon)]$. The state transition and modified profit are
--
--   $$\tilde s_i=(s_{i+1}-a)^+,\qquad
--   \varphi_F=\gamma c\tilde s_L-cS-\theta(a-d-\varepsilon)-h^+(S-a)^+-h^-(a-S)^++\gamma F(\tilde s).$$
--
--   The functions $g_F$, $G_F$ and $f_n$ take respectively the depletion supremum, the actual expected one-period objective, and the supremum over every feasible integer order/demand pair, with $f_0=0$. Orders have no upper cap. The cost conditions are exactly those of the real lost-sales model, including $h^++h^-\ge\gamma c$. Largest-optimal predicates require feasibility, attainment of the actual supremum, and domination of every attaining alternative. These objects supply the complete discrete half of Theorem 2.
--
--   **Formalization Note** Monetary values and integrals remain real. The measure is concentrated on integer shocks; `Int.floor` selects that exact integer inside the expectation and changes no positive-probability input. Bounded support therefore gives finitely many shock values, so measurability/integrability follow from finite sums and finite Bellman values. Depletion sets are nonempty finite integer intervals; order sets contain $(s_L,\underline d)$ and their objective images are bounded above at every finite horizon. The lifetime-one boundary has an empty state, zero carried inventory, and depletion $S\vee(d+\varepsilon)$. The same off-state $-\infty$ sign correction, zero-based indices, periods-to-go time, and local largest-maximizer existence convention as the real model apply. No backlog assumption or revenue-concavity premise is imported.
-- source:
--   Chen, Pang, Pan, Coordinating Inventory Control and Pricing Strategies for Perishable Products, Oper. Res. 62(2), 2014, eqs. (3)–(6), pp. 289–290; §5, pp. 292–293

import Mathlib
import Definitions.Def_PerishablePricing_Backlog_LNatConvex
import Definitions.Def_PerishablePricing_Backlog_Supplement_IntegerDemand

namespace PerishablePricing.Backlog.Supplement

open MeasureTheory

/-- Integer zero-lead-time lost-sales data (§§3,5). Unlike the published backlogging Model,
this has neither Assumption 1 nor the backlog-only cost restriction. -/
structure IntegerLostSalesModel (L : ℕ) extends IntegerDemandData where
  c : ℝ
  hp : ℝ
  hm : ℝ
  θ : ℝ
  γ : ℝ
  c_nonneg : 0 ≤ c
  hp_nonneg : 0 ≤ hp
  hm_nonneg : 0 ≤ hm
  θ_nonneg : 0 ≤ θ
  γ_nonneg : 0 ≤ γ
  γ_le_one : γ ≤ 1
  cost_condition : γ * c ≤ hp + hm

namespace IntegerLostSalesModel

variable {L : ℕ} (M : IntegerLostSalesModel L)

def stateSpace (L : ℕ) : Set (Fin L → ℤ) := VplusZ L L

/-- No old inventory when L=0 (l=1, the newsvendor boundary on p. 288). -/
def sLast (s : Fin L → ℤ) : ℤ :=
  if h : 0 < L then s ⟨L - 1, by omega⟩ else 0

/-- For l=1 the only inventory is the new order, which expires this period. -/
def sFirst (s : Fin L → ℤ) (sl : ℤ) : ℤ :=
  if h : 0 < L then s ⟨0, h⟩ else sl

def ext (s : Fin L → ℤ) (sl : ℤ) : Fin (L + 1) → ℤ := Fin.snoc s sl

/-- Equation (3) at k=0: every carried coordinate is a positive part. -/
noncomputable def next (s : Fin L → ℤ) (sl a : ℤ) : Fin L → ℤ :=
  fun i => max (ext s sl i.succ - a) 0

noncomputable def depletionSet (s : Fin L → ℤ) (sl d ε : ℤ) : Set ℤ :=
  Set.Icc (max (sFirst s sl) (d + ε)) (max sl (d + ε))

/-- Equation (6), with monetary values in R and integer stock/action arguments, with precisely the lost-sales dynamics, including at L=0. -/
noncomputable def phi (F : (Fin L → ℤ) → ℝ) (s : Fin L → ℤ) (sl d a ε : ℤ) : ℝ :=
  M.γ * M.c * (sLast (next s sl a) : ℝ) - M.c * (sl : ℝ)
    - M.θ * ((a : ℝ) - ((d : ℝ) + (ε : ℝ)))
    - M.hp * (max (sl - a) 0 : ℤ) - M.hm * (max (a - sl) 0 : ℤ) + M.γ * F (next s sl a)

noncomputable def g (F : (Fin L → ℤ) → ℝ) (s : Fin L → ℤ) (sl d ε : ℤ) : ℝ :=
  sSup ((fun a => M.phi F s sl d a ε) '' depletionSet s sl d ε)

/-- Floor merely selects the integer shock on a full-measure set; no positive-probability
shock is rounded. The distribution, support, and CDF remain those of the original law. -/
noncomputable def G (F : (Fin L → ℤ) → ℝ) (s : Fin L → ℤ) (sl d : ℤ) : ℝ :=
  M.toIntegerDemandData.revenue d sl + ∫ ε : ℝ, M.g F s sl d (Int.floor ε) ∂M.μ

def orderSet (s : Fin L → ℤ) : Set (ℤ × ℤ) :=
  {p | sLast s ≤ p.1 ∧ p.2 ∈ M.toIntegerDemandData.demandSet}

/-- Stationarity permits periods-to-go time. f 0 is the terminal value, and the
continuation in f (n+1), gJoint n and phiJoint n is f n. -/
noncomputable def f : ℕ → (Fin L → ℤ) → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun s => sSup ((fun p : ℤ × ℤ => M.G (f n) s p.1 p.2) '' M.orderSet s)

noncomputable def gJoint (n : ℕ) (ε : ℤ) (w : Fin (L + 2) → ℤ) : ℝ :=
  M.g (M.f n) (fun i => w ⟨i, by omega⟩) (w ⟨L, by omega⟩) (w ⟨L + 1, by omega⟩) ε

noncomputable def phiJoint (n : ℕ) (ε : ℤ) (w : Fin (L + 3) → ℤ) : ℝ :=
  M.phi (M.f n) (fun i => w ⟨i, by omega⟩) (w ⟨L, by omega⟩) (w ⟨L + 1, by omega⟩)
    (w ⟨L + 2, by omega⟩) ε

def IsOptOrder (n : ℕ) (s : Fin L → ℤ) (S D : ℤ) : Prop :=
  (S, D) ∈ M.orderSet s ∧ M.G (M.f n) s S D = M.f (n + 1) s

def IsLargestOptOrder (n : ℕ) (s : Fin L → ℤ) (S D : ℤ) : Prop :=
  M.IsOptOrder n s S D ∧ ∀ S' D', M.IsOptOrder n s S' D' → S' ≤ S ∧ D' ≤ D

noncomputable def IsLargestOptDepletion (n : ℕ) (s : Fin L → ℤ) (sl d ε a : ℤ) : Prop :=
  IsGreatest {a' | a' ∈ depletionSet s sl d ε ∧
    M.phi (M.f n) s sl d a' ε = M.g (M.f n) s sl d ε} a

end IntegerLostSalesModel

end PerishablePricing.Backlog.Supplement


