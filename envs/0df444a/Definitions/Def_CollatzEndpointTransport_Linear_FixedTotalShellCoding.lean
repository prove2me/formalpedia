-- Prove2me | Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalShellCoding
-- name    : CollatzEndpointTransport_Linear_FixedTotalShellCoding
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:55:28.282498+00:00
-- url     : https://prove2.me/theorems/04c69b67-0a89-44a3-855e-edbfd75b9db0
-- title:
--   Fixed Total Shell Coding
-- statement:
--   Definitions and structural lemmas for Fixed Total Shell Coding, from Idris Ali Shaik (shaikidris/CollatzEndpointTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Refined arbitrary-target transport through Collatz endpoints development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalShellCoding.lean

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalGlobalEndpointMoment
import Definitions.Def_CollatzEndpointTransport_Common_AffineCorrectionDensity
import Definitions.Def_CollatzEndpointTransport_Common_QuantitativePullbackDefs
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumerator_prependOne
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_wordCorrectionFrom_nil
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_card_positivePrefix
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_mem_basePullback
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_mem_collatzPullback
import Theorems.Thm_CollatzEndpointTransport_Terras_integerCorrection_zero
attribute [local simp] CollatzEndpointTransport.FixedTotal.encodeBlocks_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.encodeBlocks_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_length
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_length
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumerator_prependOne
attribute [local simp] CollatzEndpointTransport.FixedTotal.wordCorrectionFrom_nil
attribute [local simp] CollatzEndpointTransport.QuantitativeDensity.card_positivePrefix
attribute [local simp] CollatzEndpointTransport.QuantitativeDensity.mem_basePullback
attribute [local simp] CollatzEndpointTransport.QuantitativeDensity.mem_collatzPullback
attribute [local simp] CollatzEndpointTransport.Terras.integerCorrection_zero


set_option autoImplicit false
namespace CollatzEndpointTransport
namespace FixedTotal
open Nat Finset
noncomputable section
noncomputable def residueEquivDyadicShell
    (M : ℕ) :
    Fin (2 ^ M) ≃
      {n // n ∈ QuantitativeDensity.dyadicShell M} where
  toFun r := by
    refine ⟨2 ^ M + (r : ℕ), ?_⟩
    unfold QuantitativeDensity.dyadicShell
    rw [Finset.mem_Ico]
    rw [pow_succ]
    omega
  invFun n := by
    refine ⟨(n : ℕ) - 2 ^ M, ?_⟩
    have hn := n.property
    unfold QuantitativeDensity.dyadicShell at hn
    rw [Finset.mem_Ico] at hn
    have hupper : (n : ℕ) < 2 ^ M * 2 := by
      simpa only [pow_succ] using hn.2
    omega
  left_inv r := by
    apply Fin.ext
    simp
  right_inv n := by
    apply Subtype.ext
    have hn := n.property
    unfold QuantitativeDensity.dyadicShell at hn
    rw [Finset.mem_Ico] at hn
    simp only
    omega
noncomputable def sourceCodeEquivDyadicShell
    (M : ℕ) :
    SourceCode M ≃
      {n // n ∈ QuantitativeDensity.dyadicShell M} :=
  (sourceCodeEquivResidue M).trans (residueEquivDyadicShell M)
def sourceEndpointBad (S : Set ℕ) (M : ℕ) :
    Finset (SourceCode M) := by
  classical
  exact Finset.univ.filter fun x => sourceEndpoint x ∉ S
def endpointShellBad (S : Set ℕ) (M : ℕ) : Finset ℕ := by
  classical
  exact (QuantitativeDensity.dyadicShell M).filter
    fun n => (Terras.T^[M]) n ∉ S
end
end FixedTotal
end CollatzEndpointTransport


