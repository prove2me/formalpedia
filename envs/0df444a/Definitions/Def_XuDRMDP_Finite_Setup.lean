-- Prove2me | Definitions.Def_XuDRMDP_Finite_Setup
-- name    : XuDRMDP_Finite_Setup
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T05:27:13.385969+00:00
-- url     : https://prove2.me/theorems/c0874ffc-9c7b-4074-9d27-741e7a6c2816
-- title:
--   Finite staged MDP parameters
-- statement:
--   A finite decision process has a nonempty state set $S$ and a finite nonempty action set $A_s$ at each state. Its general MDP object is the published `PutermanMDP.Discounted.MDP`: real rewards and nonnegative transition rows summing to one. The extra staging data consist of a positive horizon $T$, a discount $0<\gamma\le1$, a stage map into $\{0,\ldots,T-1\}$, and an initial state which is the unique state at stage zero. A local parameter vector $x_s=(p_s,r_s)$ contains every action's transition row and reward. It is valid if it is the local projection of a general MDP, terminal rewards are zero, and nonterminal transitions vanish outside the next stage. Terminal transitions remain probability rows but are never used.
--
--   States and actions are indexed by finite ordinal types; this changes no finite instance. Different states may have different action counts. The local parameter space is a finite dimensional real vector space with its Borel sigma algebra. Rewards have no sign restriction. The model carries no uncertainty, optimality, mean-set identity or saddle assumption.
-- source:
--   Xu and Mannor (2012), Distributionally Robust Markov Decision Processes, Mathematics of Operations Research 37(2), 288–300, DOI:10.1287/moor.1120.0540. Published basis; printed page = PDF page + 287. Sections 2–3, printed pp. 289–293 (PDF pp. 2–6).

import Definitions.Def_PutermanMDP_Discounted_MDP
open MeasureTheory
open scoped BigOperators

namespace XuDRMDP.Finite

/-- Staging and discount data, separate from the general MDP. Stage zero is source stage one. -/
structure Setup (n : ℕ) (a : Fin n → ℕ) where
  horizon : ℕ
  horizon_pos : 0 < horizon
  discount : ℝ
  discount_pos : 0 < discount
  discount_le_one : discount ≤ 1
  stage : Fin n → ℕ
  stage_lt : ∀ s, stage s < horizon
  initial : Fin n
  initial_stage : stage initial = 0
  first_unique : ∀ s, stage s = 0 → s = initial

/-- Local coordinates in transition/reward order, with all actions in the same vector. -/
abbrev Local (n : ℕ) (a : Fin n → ℕ) (s : Fin n) :=
  (Fin (a s) → Fin n → ℝ) × (Fin (a s) → ℝ)

abbrev Parameters (n : ℕ) (a : Fin n → ℕ) := (s : Fin n) → Local n a s

/-- Projection of the published general MDP onto a state's coordinates. -/
def localCoordinates {n : ℕ} [NeZero n] {a : Fin n → ℕ} [∀ s, NeZero (a s)]
    (M : PutermanMDP.Discounted.MDP (Fin n) (fun s => Fin (a s))) (s : Fin n) :
    Local n a s := (M.trans s, M.reward s)

/-- Valid local MDP coordinates, next-stage transitions and zero terminal rewards.
Terminal transition rows are immaterial, but remain probability rows of a general MDP. -/
def ValidLocal {n : ℕ} [NeZero n] {a : Fin n → ℕ} [∀ s, NeZero (a s)]
    (G : Setup n a) (s : Fin n) (x : Local n a s) : Prop :=
  (∃ M : PutermanMDP.Discounted.MDP (Fin n) (fun s => Fin (a s)),
    localCoordinates M s = x) ∧
  (G.stage s + 1 = G.horizon → ∀ b, x.2 b = 0) ∧
  (G.stage s + 1 < G.horizon → ∀ b j, G.stage j ≠ G.stage s + 1 → x.1 b j = 0)

end XuDRMDP.Finite


