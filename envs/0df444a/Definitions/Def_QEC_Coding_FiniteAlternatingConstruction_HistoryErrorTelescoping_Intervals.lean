-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_Intervals
-- name    : QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_Intervals
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T06:24:23.984951+00:00
-- url     : https://prove2.me/theorems/470ac1b9-c683-4e58-a9ed-e68ad759a1a1
-- title:
--   Intervals
-- statement:
--   Definitions and structural lemmas for Intervals, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/Intervals.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26HistoryErrorTelescoping
open MultiscaleDecoder
open scoped Classical
universe u v
section LinearIntervals
variable {depth : Nat} {V : LevelIndex depth → Type u}
variable [∀ i, AddCommGroup (V i)] [∀ i, Module BDL26Field (V i)]
def linearUp (edge : ∀ i : StepIndex depth, V i.castSucc →ₗ[BDL26Field] V i.succ)
    (b : Nat) (hb : b ≤ depth) (a : LevelIndex depth) (ha : a.val ≤ b) :
    V a →ₗ[BDL26Field] V ⟨b,Nat.lt_succ_of_le hb⟩ := by
  cases b with
  | zero =>
      have he : a = ⟨0,Nat.lt_succ_of_le hb⟩ := Fin.ext (by change a.val = 0; omega)
      subst a
      exact LinearMap.id
  | succ b =>
      if h : a.val = b+1 then
        have he : a = ⟨b+1,Nat.lt_succ_of_le hb⟩ := Fin.ext h
        subst a
        exact LinearMap.id
      else
        exact (edge ⟨b,by omega⟩).comp
          (linearUp edge b (by omega) a (by omega))
termination_by b
end LinearIntervals
section DecoderIntervals
variable {depth : Nat} {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
def intervalMap0 (D : BDL26DecoderData depth C0 C1 C2)
    (a b : LevelIndex depth) (hab : a.val ≤ b.val) :
    D.family.Cochain0 a →ₗ[BDL26Field] D.family.Cochain0 b :=
  linearUp (fun i => (D.selectedMap i).map0) b.val
    (Nat.le_of_lt_succ b.isLt) a hab
def intervalMap1 (D : BDL26DecoderData depth C0 C1 C2)
    (a b : LevelIndex depth) (hab : a.val ≤ b.val) :
    D.family.Cochain1 a →ₗ[BDL26Field] D.family.Cochain1 b :=
  linearUp (fun i => (D.selectedMap i).map1) b.val
    (Nat.le_of_lt_succ b.isLt) a hab
end DecoderIntervals
end QEC.Coding.BDL26HistoryErrorTelescoping


