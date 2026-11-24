-- Prove2me | Definitions.Def_RequestProject_TPSSefxMoney
-- name    : RequestProject_TPSSefxMoney
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:17:12.156054+00:00
-- url     : https://prove2.me/theorems/5bc9ad9f-e637-4680-83c6-d7343824144d
-- title:
--   TPSSefx Money
-- statement:
--   Definitions and structural lemmas for TPSSefx Money, from yotam-gafni/FairAllocationWithOptionalSelling contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Fair allocation with optional selling and maximin-share bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxMoney.lean

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSSefx
import Definitions.Def_RequestProject_TPSSefxGeneral
set_option autoImplicit true
open scoped BigOperators
namespace FairSelling
namespace MoneyGoods
open GeneralTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open Classical in
/-- The goods that are sold at the outset: those carrying a positive price. -/
noncomputable def soldGoods (p : G → ℝ) : Finset G := Finset.univ.filter (fun g => p g ≠ 0)
def MoneyClass (v : Fin n → G → ℝ) (p : G → ℝ) : Prop :=
  ∀ g, p g = 0 ∨ ∀ j, trunc (v j) p (TPS n (v j) p) g = p g
noncomputable def guarM (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) (s : Stage G n) (j : Fin n) :
    ℝ :=
  if j ∈ s.served then vbarSum (v j) p (s.bundle j) + s.cash j else thr v p j - eps
def SafeM (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) (s : Stage G n) (i j : Fin n) : Prop :=
  (vbarSum (v j) p (s.bundle i) + s.cash i ≤ guarM v p eps s j + eps) ∨
  (s.cash i = 0 ∧ (∀ g ∈ s.bundle i, p g ≤ v i g) ∧
    ∀ g ∈ s.bundle i, vbarSum (v j) p (s.bundle i \ {g}) + p g ≤ guarM v p eps s j + eps)
def GoodM (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) (s : Stage G n) : Prop :=
  (∀ i, i ∉ s.served → s.bundle i = ∅ ∧ s.cash i = 0) ∧
  (∀ i j, i ≠ j → Disjoint (s.bundle i) (s.bundle j)) ∧
  (∀ i, Disjoint s.soldSet (s.bundle i)) ∧
  (∀ i, 0 ≤ s.cash i) ∧ 0 ≤ s.bank ∧
  ((∑ i, s.cash i) + s.bank = ∑ g ∈ s.soldSet, p g) ∧
  s.soldSet = soldGoods p ∧
  (∀ i ∈ s.served, thr v p i - eps ≤ vbarSum (v i) p (s.bundle i) + s.cash i) ∧
  (∀ i ∈ s.served, ∀ j, SafeM v p eps s i j)
end MoneyGoods
end FairSelling


