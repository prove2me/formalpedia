-- Prove2me | Definitions.Def_PerishablePricing_Backlog_Supplement_LostSalesModel
-- name    : PerishablePricing_Backlog_Supplement_LostSalesModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T06:59:10.487527+00:00
-- url     : https://prove2.me/theorems/2c6a4395-d3af-4324-91f9-b46ed4af8dda
-- title:
--   Equations (3)–(6), pp. 290–293 — zero-lead-time lost-sales recursion and largest optima
-- statement:
--   Let $l=L+1\ge1$ be the lifetime and let the lead time be zero. The lost-sales state $s$ is nonnegative and ordered: $\mathcal S_l=\mathcal V^+_{L,L}$. Ordering up to $s_l\ge s_{l-1}$ precedes demand $d+\varepsilon$, with $d\in\mathcal D$. Depletion satisfies $s_1\vee(d+\varepsilon)\le a\le s_l\vee(d+\varepsilon)$ and the next state is $\tilde s=((s_2-a)^+,\ldots,(s_l-a)^+)$. All unit costs $c,h^+,h^-,\theta$ are nonnegative, $0\le\gamma\le1$, and $h^++h^-\ge\gamma c$. With continuation $F_0$, define
--
--   $$\varphi=\gamma c\tilde s_{l-1}-cs_l-\theta(a-d-\varepsilon)-h^+(s_l-a)^+-h^-(a-s_l)^++\gamma F_0(\tilde s),$$
--   $$g=\sup_a\varphi,\quad G(s,s_l,d)=R(d,s_l)+\mathbb E[g],\quad f_0=0,\quad f_{n+1}(s)=\sup_{s_l\ge s_{l-1},\ d\in\mathcal D}G(s,s_l,d),$$
--
--   where $F_0=f_n$ in the last equation. An order pair is largest optimal if it is feasible, attains $f_{n+1}$, and dominates every other attaining pair componentwise. Depletion uses the largest attaining point of its interval. These definitions supply every policy clause of Theorem 2; there is no Assumption 1 or backlog-only cost condition.
--
--   **Formalization Note** The superscript $+$ is a positive part, never a state constraint on $d$ or $a$ in the joint functions. The index set `Fin L` is zero based, and time counts periods to go. Supremums are over the actual feasible sets, not over all reals. On valid inputs they are nonempty and bounded above; the integral is the ordinary Bochner expectation (see MODERATION_NOTES.md for the finite-horizon bounds and integrability argument). Largest-optimum existence is required at compared points by the theorem, rather than asserted globally. The $l=1$ newsvendor boundary mentioned on p. 288 is included: old inventory and carried inventory are zero, the only stock is $s_l$, and $a=s_l\vee(d+\varepsilon)$. Off-state values are unused, implementing the $-\infty$ extension appropriate to maximization; the printed $+\infty$ off-state convention on p. 290 has the wrong sign.
-- source:
--   Chen, Pang, Pan, Coordinating Inventory Control and Pricing Strategies for Perishable Products, Oper. Res. 62(2), 2014, https://doi.org/10.1287/opre.2014.1261, (3)–(6), pp. 289–290 (PDF 7–8); §5 pp. 292–293 (PDF 10–11); l=1 boundary p. 288

import Mathlib
import Definitions.Def_PerishablePricing_Backlog_LNatConvex
import Definitions.Def_PerishablePricing_Backlog_Supplement_Demand

namespace PerishablePricing.Backlog.Supplement

open MeasureTheory

/-- Zero-lead-time lost-sales data (§§3,5). Unlike the published backlogging Model,
this has neither Assumption 1 nor the backlog-only cost restriction. -/
structure LostSalesModel (L : ℕ) extends DemandData where
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

namespace LostSalesModel

variable {L : ℕ} (M : LostSalesModel L)

def stateSpace (L : ℕ) : Set (Fin L → ℝ) := Vplus L L

/-- No old inventory when L=0 (l=1, the newsvendor boundary on p. 288). -/
def sLast (s : Fin L → ℝ) : ℝ :=
  if h : 0 < L then s ⟨L - 1, by omega⟩ else 0

/-- For l=1 the only inventory is the new order, which expires this period. -/
def sFirst (s : Fin L → ℝ) (sl : ℝ) : ℝ :=
  if h : 0 < L then s ⟨0, h⟩ else sl

def ext (s : Fin L → ℝ) (sl : ℝ) : Fin (L + 1) → ℝ := Fin.snoc s sl

/-- Equation (3) at k=0: every carried coordinate is a positive part. -/
noncomputable def next (s : Fin L → ℝ) (sl a : ℝ) : Fin L → ℝ :=
  fun i => max (ext s sl i.succ - a) 0

noncomputable def depletionSet (s : Fin L → ℝ) (sl d ε : ℝ) : Set ℝ :=
  Set.Icc (max (sFirst s sl) (d + ε)) (max sl (d + ε))

/-- Equation (6), with precisely the lost-sales dynamics, including at L=0. -/
noncomputable def phi (F : (Fin L → ℝ) → ℝ) (s : Fin L → ℝ) (sl d a ε : ℝ) : ℝ :=
  M.γ * M.c * sLast (next s sl a) - M.c * sl - M.θ * (a - (d + ε))
    - M.hp * max (sl - a) 0 - M.hm * max (a - sl) 0 + M.γ * F (next s sl a)

noncomputable def g (F : (Fin L → ℝ) → ℝ) (s : Fin L → ℝ) (sl d ε : ℝ) : ℝ :=
  sSup ((fun a => M.phi F s sl d a ε) '' depletionSet s sl d ε)

noncomputable def G (F : (Fin L → ℝ) → ℝ) (s : Fin L → ℝ) (sl d : ℝ) : ℝ :=
  M.toDemandData.revenue d sl + ∫ ε, M.g F s sl d ε ∂M.μ

def orderSet (s : Fin L → ℝ) : Set (ℝ × ℝ) :=
  {p | sLast s ≤ p.1 ∧ p.2 ∈ M.toDemandData.demandSet}

/-- Stationarity permits periods-to-go time. f 0 is the terminal value, and the
continuation in f (n+1), gJoint n and phiJoint n is f n. -/
noncomputable def f : ℕ → (Fin L → ℝ) → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun s => sSup ((fun p : ℝ × ℝ => M.G (f n) s p.1 p.2) '' M.orderSet s)

noncomputable def gJoint (n : ℕ) (ε : ℝ) (w : Fin (L + 2) → ℝ) : ℝ :=
  M.g (M.f n) (fun i => w ⟨i, by omega⟩) (w ⟨L, by omega⟩) (w ⟨L + 1, by omega⟩) ε

noncomputable def phiJoint (n : ℕ) (ε : ℝ) (w : Fin (L + 3) → ℝ) : ℝ :=
  M.phi (M.f n) (fun i => w ⟨i, by omega⟩) (w ⟨L, by omega⟩) (w ⟨L + 1, by omega⟩)
    (w ⟨L + 2, by omega⟩) ε

def IsOptOrder (n : ℕ) (s : Fin L → ℝ) (S D : ℝ) : Prop :=
  (S, D) ∈ M.orderSet s ∧ M.G (M.f n) s S D = M.f (n + 1) s

def IsLargestOptOrder (n : ℕ) (s : Fin L → ℝ) (S D : ℝ) : Prop :=
  M.IsOptOrder n s S D ∧ ∀ S' D', M.IsOptOrder n s S' D' → S' ≤ S ∧ D' ≤ D

noncomputable def IsLargestOptDepletion (n : ℕ) (s : Fin L → ℝ) (sl d ε a : ℝ) : Prop :=
  IsGreatest {a' | a' ∈ depletionSet s sl d ε ∧
    M.phi (M.f n) s sl d a' ε = M.g (M.f n) s sl d ε} a

end LostSalesModel

end PerishablePricing.Backlog.Supplement


