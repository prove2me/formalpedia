-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
-- name    : QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T06:20:50.165346+00:00
-- url     : https://prove2.me/theorems/300fdcfe-f292-4cd4-a502-b3c0046b6de3
-- title:
--   Snapshots
-- statement:
--   Definitions and structural lemmas for Snapshots, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity/Snapshots.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Steps
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Snapshots
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open MultiscaleDecoder
open scoped Classical
universe u
section Prefix
variable {depth : Nat} {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
def prefixHistory (D : BDL26DecoderData depth C0 C1 C2)
    (S : AlternatingStepData D) (B : AuditedBaseDecoder D) (n : Nat)
    (hn : n ≤ depth) (sigma : D.family.Syndrome ⟨n,Nat.lt_succ_of_le hn⟩) :
    CorrectionHistory D := by
  cases n with
  | zero =>
      exact [.base {
        input := sigma
        correction := B.decode sigma
        relation := (B.rightInverse sigma).symm }]
  | succ n =>
      have hstep : n < depth := Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hn
      let i : StepIndex depth := ⟨n,hstep⟩
      have hi : i.succ = ⟨n+1,Nat.lt_succ_of_le hn⟩ := Fin.ext rfl
      let sigma' : D.family.Syndrome i.succ := hi ▸ sigma
      let out := S.step i sigma'
      have hnext : n ≤ depth := Nat.le_of_lt hstep
      have hcoarse : i.castSucc = ⟨n,Nat.lt_succ_of_le hnext⟩ := Fin.ext rfl
      exact .step i out :: prefixHistory D S B n hnext (hcoarse ▸ out.coarse)
termination_by n
def prefixInput (D : BDL26DecoderData depth C0 C1 C2)
    (S : AlternatingStepData D) (n : Nat) (hn : n ≤ depth)
    (sigma : D.family.Syndrome ⟨n,Nat.lt_succ_of_le hn⟩)
    (a : LevelIndex depth) (ha : a.val ≤ n) : D.family.Syndrome a := by
  cases n with
  | zero =>
      have he : (⟨0,Nat.lt_succ_of_le hn⟩ : LevelIndex depth) = a :=
        Fin.ext (by change 0 = a.val; omega)
      exact he ▸ sigma
  | succ n =>
      if h : a.val = n+1 then
        exact (show (⟨n+1,Nat.lt_succ_of_le hn⟩ : LevelIndex depth) = a from
          Fin.ext h.symm) ▸ sigma
      else
        have hs : n < depth := by omega
        exact prefixInput D S n (by omega) (S.step ⟨n,hs⟩ sigma).coarse a (by omega)
termination_by n
end Prefix
variable (S : OddScale) (n : Nat)
abbrev SuffixData := LevelTwoHistory.suffixData (indexedDecoderData S (n+2))
abbrev TopInput := (indexedFamily S (n+2)).Syndrome (TopIndex (n+2))
def actualInputs (sigma : TopInput S n) (a : LevelIndex n) :
    (SuffixData S n).family.Syndrome a :=
  prefixInput (SuffixData S n)
    (LevelTwoHistory.suffixSteps _ (actualAboveTwoSteps S n)) n (Nat.le_refl _) sigma a
      (Nat.le_of_lt_succ a.isLt)
def actualReadout (sigma : TopInput S n) (a : LevelIndex n) :=
  LevelTwoHistory.syndromeReadout (indexedDecoderData S (n+2))
    (actualHistory S n sigma) (LevelTwoHistory.physicalLevel a)
end QEC.Coding.BDL26HistorySyndromeSensitivity


