-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual_Words
-- name    : QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual_Words
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T13:37:55.499703+00:00
-- url     : https://prove2.me/theorems/49255d8d-ffb2-47d7-8fca-7af23a21990c
-- title:
--   Words
-- statement:
--   Definitions and structural lemmas for Words, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryLogicalResidual/Words.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual_Intervals
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_descentWord_readout
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_word_add_self
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_suffix_delta1
import Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_actualInputs_readout
import Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_actualReadout_top
import Theorems.Thm_QEC_Coding_BDL26OwnerIncidenceMasks_actualHistory_syndrome
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26HistoryLogicalResidual
open MultiscaleDecoder BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26RZMap1CoordinateBridge
open scoped Classical
variable (S : OddScale) (n : Nat)
def baseCorrection (sigma : TopInput S n) : (SuffixData S n).family.Cochain1 0 :=
  (actualBase S n).decode (actualInputs S n sigma 0)
def fullCorrection (sigma : TopInput S n) : (SuffixData S n).family.Cochain1 (TopIndex n) :=
  historyLiftedCorrection (SuffixData S n) (actualHistory S n sigma)
def lowerWord (sigma : TopInput S n)
    (e u : (SuffixData S n).family.Cochain1 (TopIndex n)) :
    (SuffixData S n).family.Cochain1 0 :=
  descentWord S n (TopIndex n) u 0 (Nat.zero_le _) +
    descentWord S n (TopIndex n) (u+e) 0 (Nat.zero_le _) +
      baseCorrection S n sigma + baseCorrection S n (perturbTop S n sigma e)
def topWord (sigma : TopInput S n)
    (e : (SuffixData S n).family.Cochain1 (TopIndex n)) :
    (SuffixData S n).family.Cochain1 (TopIndex n) :=
  e + fullCorrection S n sigma + fullCorrection S n (perturbTop S n sigma e)
def residualPotential (e u : (SuffixData S n).family.Cochain1 (TopIndex n)) :
    (SuffixData S n).family.Cochain0 (TopIndex n) :=
  accumulatedPotential S n (TopIndex n) u 0 n (Nat.le_refl _) (Nat.zero_le _) +
    accumulatedPotential S n (TopIndex n) (u+e) 0 n (Nat.le_refl _) (Nat.zero_le _)
theorem shared_valid (sigma : TopInput S n)
    (e u : (SuffixData S n).family.Cochain1 (TopIndex n))
    (hu : (SuffixData S n).family.coboundary1 (TopIndex n) u = sigma.val) :
    (SuffixData S n).family.coboundary1 (TopIndex n) (u+e) =
      (perturbTop S n sigma e).val := by
  change (SuffixData S n).family.coboundary1 (TopIndex n) (u+e) =
    sigma.val + (SuffixData S n).family.coboundary1 (TopIndex n) e
  rw [map_add,hu]
theorem lower_closed (sigma : TopInput S n)
    (e u : (SuffixData S n).family.Cochain1 (TopIndex n))
    (hu : (SuffixData S n).family.coboundary1 (TopIndex n) u = sigma.val) :
    (SuffixData S n).family.coboundary1 0 (lowerWord S n sigma e u) = 0 := by
  let tau := perturbTop S n sigma e
  have hue := shared_valid S n sigma e u hu
  have hv := hu.trans (actualReadout_top S n sigma).symm
  have hv' := hue.trans (actualReadout_top S n tau).symm
  have hl := descentWord_readout S n sigma (TopIndex n) u hv 0 (Nat.zero_le _)
  have hl' := descentWord_readout S n tau (TopIndex n) (u+e) hv' 0 (Nat.zero_le _)
  have hb : (SuffixData S n).family.coboundary1 0 (baseCorrection S n sigma) =
      actualReadout S n sigma 0 :=
    ((actualBase S n).rightInverse _).trans (actualInputs_readout S n sigma 0).symm
  have hb' : (SuffixData S n).family.coboundary1 0 (baseCorrection S n tau) =
      actualReadout S n tau 0 :=
    ((actualBase S n).rightInverse _).trans (actualInputs_readout S n tau 0).symm
  unfold lowerWord
  rw [map_add,map_add,map_add,hl,hl',hb,hb']
  calc
    (actualReadout S n sigma 0 + actualReadout S n tau 0) + actualReadout S n sigma 0 +
        actualReadout S n tau 0 =
      (actualReadout S n sigma 0 + actualReadout S n sigma 0) +
        (actualReadout S n tau 0 + actualReadout S n tau 0) := by ac_rfl
    _ = 0 := by rw [word_add_self,word_add_self,add_zero]
theorem top_closed (sigma : TopInput S n)
    (e : (SuffixData S n).family.Cochain1 (TopIndex n)) :
    (SuffixData S n).family.coboundary1 (TopIndex n) (topWord S n sigma e) = 0 := by
  have hs : (SuffixData S n).family.coboundary1 (TopIndex n) (fullCorrection S n sigma) =
      sigma.val := actualHistory_syndrome S n sigma
  have ht : (SuffixData S n).family.coboundary1 (TopIndex n)
      (fullCorrection S n (perturbTop S n sigma e)) = (perturbTop S n sigma e).val :=
    actualHistory_syndrome S n (perturbTop S n sigma e)
  unfold topWord
  rw [map_add,map_add,hs,ht]
  change (SuffixData S n).family.coboundary1 (TopIndex n) e + sigma.val +
    (sigma.val + (SuffixData S n).family.coboundary1 (TopIndex n) e) = 0
  calc
    _ = ((SuffixData S n).family.coboundary1 (TopIndex n) e +
        (SuffixData S n).family.coboundary1 (TopIndex n) e) + (sigma.val+sigma.val) := by ac_rfl
    _ = 0 := by rw [word_add_self,word_add_self,add_zero]
def lowerCocycle (sigma : TopInput S n)
    (e u : (SuffixData S n).family.Cochain1 (TopIndex n))
    (hu : (SuffixData S n).family.coboundary1 (TopIndex n) u = sigma.val) : FC.Cocycle S 2 :=
  ⟨lowerWord S n sigma e u, by
    apply (BDL26RZCohomology.mem_cocycle_iff _ _).mpr
    have h := lower_closed S n sigma e u hu
    rw [suffix_delta1] at h
    exact h⟩
def topCocycle (sigma : TopInput S n)
    (e : (SuffixData S n).family.Cochain1 (TopIndex n)) : FC.Cocycle S (n+2) :=
  ⟨topWord S n sigma e, by
    apply (BDL26RZCohomology.mem_cocycle_iff _ _).mpr
    have h := top_closed S n sigma e
    rw [suffix_delta1] at h
    exact h⟩
end QEC.Coding.BDL26HistoryLogicalResidual


