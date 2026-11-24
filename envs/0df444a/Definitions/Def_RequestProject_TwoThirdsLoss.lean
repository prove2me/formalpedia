-- Prove2me | Definitions.Def_RequestProject_TwoThirdsLoss
-- name    : RequestProject_TwoThirdsLoss
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:14:45.686653+00:00
-- url     : https://prove2.me/theorems/b8be4933-dee1-42a8-8925-826708d5ce87
-- title:
--   Two Thirds Loss
-- statement:
--   Definitions and structural lemmas for Two Thirds Loss, from yotam-gafni/FairAllocationWithOptionalSelling contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Fair allocation with optional selling and maximin-share bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsLoss.lean

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TwoThirdsCanonical
import Definitions.Def_RequestProject_EquiMMS
set_option autoImplicit true
open scoped BigOperators
namespace FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
noncomputable def rho : ℝ := 2 / 3
noncomputable def thr (v : Fin n → G → ℝ) (p : G → ℝ) (i : Fin n) : ℝ := rho * MMS n (v i) p
def LossL1 (p : G → ℝ) (S : Finset G) (E F : Finset G) (c : ℝ) : Prop :=
  ∃ e, e ∉ S ∧ ((E = {e} ∧ F = ∅ ∧ c = 0) ∨ (E = ∅ ∧ F = {e} ∧ c ≤ p e))
def LossL2 (w p : G → ℝ) (S : Finset G) (t : ℝ) (E F : Finset G) (c : ℝ) : Prop :=
  vbarSum w p E + c ≤ t ∧ (∀ f ∈ F, w f ≤ p f ∨ f ∈ S)
def LossL3 (w p : G → ℝ) (S : Finset G) (μ t : ℝ) (E F : Finset G) (c : ℝ) : Prop :=
  (∃ e, E = {e} ∧ e ∉ S ∧ vbar w p e ≤ t) ∧
  (∃ f, F = {f} ∧ f ∉ S ∧ vbar w p f ≤ t ∧ c ≤ p f ∧ μ - t ≤ p f) ∧ 0 ≤ c ∧
  vbarSum w p E + c ≤ t
def LossL4 (w p : G → ℝ) (S : Finset G) (μ t : ℝ) (E F : Finset G) (c : ℝ) : Prop :=
  (∃ e, E = {e} ∧ e ∈ S ∧ vbar w p e ≤ t) ∧
  (∃ f, F = {f} ∧ f ∉ S ∧ vbar w p f ≤ t ∧ c ≤ p f ∧ μ - t ≤ p f) ∧ 0 ≤ c ∧
  vbarSum w p E + c ≤ t
def LossOK (w p : G → ℝ) (S : Finset G) (μ t : ℝ) (E F : Finset G) (c : ℝ) : Prop :=
  LossL1 p S E F c ∨ LossL2 w p S t E F c ∨ LossL3 w p S μ t E F c ∨ LossL4 w p S μ t E F c
def Losses (v : Fin n → G → ℝ) (p : G → ℝ) (T : Finset (Fin n)) (R : Finset G) (D : ℝ) : Prop :=
  ∃ (alloc sold : Fin n → Finset G) (paid : Fin n → ℝ),
    (∀ b ∈ T, alloc b = ∅ ∧ sold b = ∅ ∧ paid b = 0) ∧
    (∀ b, Disjoint (alloc b) (sold b)) ∧
    (∀ b b', b ≠ b' → Disjoint (alloc b ∪ sold b) (alloc b' ∪ sold b')) ∧
    (∀ b, Disjoint R (alloc b ∪ sold b)) ∧
    (Finset.univ = R ∪ Finset.univ.biUnion (fun b => alloc b ∪ sold b)) ∧
    (∀ b, 0 ≤ paid b) ∧
    ((∑ b, ∑ g ∈ sold b, p g) - ∑ b, paid b ≤ D) ∧
    (∀ i ∈ T, ∃ E : EquiMMS (v i) p (MMS n (v i) p) n,
      ∀ b ∉ T, LossOK (v i) p E.sell (MMS n (v i) p) (thr v p i) (alloc b) (sold b) (paid b))
def Inv (v : Fin n → G → ℝ) (p : G → ℝ) (T : Finset (Fin n)) (R : Finset G) (D : ℝ) : Prop :=
  0 ≤ D ∧ Losses v p T R D ∧ ∀ i ∈ T, ∀ g ∈ R, vbar (v i) p g < thr v p i
end FairSelling


