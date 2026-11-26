-- Prove2me | Definitions.Def_FirstPassageLinearTransport_ReciprocalHeightObstruction
-- name    : FirstPassageLinearTransport_ReciprocalHeightObstruction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:18:35.171196+00:00
-- url     : https://prove2.me/theorems/09323b22-7190-4b3e-9983-d4544f1a84fc
-- title:
--   Reciprocal Height Obstruction
-- statement:
--   Definitions and structural lemmas for Reciprocal Height Obstruction, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ReciprocalHeightObstruction.lean

import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_cons
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_scale
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_zero
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_card_boolSupport_cons
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_stageClock_zero
import Theorems.Thm_FirstPassageLinearTransport_stageOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_stoppedBallotValue_cons
attribute [local simp] FirstPassageLinearTransport.ballotWordValue_cons
attribute [local simp] FirstPassageLinearTransport.ballotWordValue_scale
attribute [local simp] FirstPassageLinearTransport.ballotWordValue_zero
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.bootstrapC_zero
attribute [local simp] FirstPassageLinearTransport.bootstrapD_zero
attribute [local simp] FirstPassageLinearTransport.bootstrapSet_zero
attribute [local simp] FirstPassageLinearTransport.card_boolSupport_cons
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.mem_taggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_transportedSources
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.rawOrbit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero
attribute [local simp] FirstPassageLinearTransport.stageClock_zero
attribute [local simp] FirstPassageLinearTransport.stageOrbit_zero
attribute [local simp] FirstPassageLinearTransport.stoppedBallotValue_cons


set_option autoImplicit true
namespace FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
def dyadicShellEquivFin (M : ℕ) :
    {n : ℕ // n ∈ dyadicShell M} ≃ Fin (2 ^ M) where
  toFun n := ⟨n.1 - 2 ^ M, by
    have hn := mem_dyadicShell.mp n.2
    have hpow : 2 ^ (M + 1) = 2 ^ M + 2 ^ M := by
      simp [pow_succ, Nat.mul_comm, Nat.two_mul]
    omega⟩
  invFun x := ⟨2 ^ M + x.1, mem_dyadicShell.mpr ⟨by omega, by
    have hpow : 2 ^ (M + 1) = 2 ^ M + 2 ^ M := by
      simp [pow_succ, Nat.mul_comm, Nat.two_mul]
    omega⟩⟩
  left_inv n := by
    apply Subtype.ext
    have hn := (mem_dyadicShell.mp n.2).1
    simp only
    omega
  right_inv x := by
    apply Fin.ext
    simp only
    omega
def dyadicShellPrefixEquiv (M h : ℕ) (hhM : h ≤ M) :
    {n : ℕ // n ∈ dyadicShell M} ≃
      Fin (2 ^ (M - h)) × Fin (2 ^ h) :=
  (dyadicShellEquivFin M).trans
    ((finCongr (by
      rw [← pow_add]
      congr 1
      omega : 2 ^ M = 2 ^ (M - h) * 2 ^ h)).trans
      finProdFinEquiv.symm)
noncomputable def shellPrefixResidueSet
    (M h : ℕ) (hhM : h ≤ M) (S : Finset (Fin (2 ^ h))) :
    Finset {n : ℕ // n ∈ dyadicShell M} := by
  classical
  exact Finset.univ.filter fun n => (dyadicShellPrefixEquiv M h hhM n).2 ∈ S
noncomputable def shellPrefixMultiplicativeHit
    (M h : ℕ) (hhM : h ≤ M) (u : ℝ) :
    Finset {n : ℕ // n ∈ dyadicShell M} :=
  shellPrefixResidueSet M h hhM (multiplicativeHitResidues h u)
def HasTargetHeightWitness (f : ℕ → ℝ) (u : ℝ) (n : ℕ) : Prop :=
  ∃ k : ℕ,
    (orbit k n : ℝ) ≤ f n ∧
      ∀ j : ℕ, j ≤ k → (orbit j n : ℝ) ≤ u * (n : ℝ)
noncomputable def shellTargetHeightFailure
    (M : ℕ) (f : ℕ → ℝ) (u : ℝ) :
    Finset {n : ℕ // n ∈ dyadicShell M} := by
  classical
  exact Finset.univ.filter fun n => ¬HasTargetHeightWitness f u n.1
def targetHeightFailureSet (f : ℕ → ℝ) (u : ℝ) : Set ℕ :=
  {n | ¬HasTargetHeightWitness f u n}
noncomputable def targetHeightFailureCount
    (f : ℕ → ℝ) (u : ℝ) (X : ℕ) : ℕ := by
  classical
  exact ((Finset.range X).filter fun n => n ∈ targetHeightFailureSet f u).card
noncomputable def targetHeightFailureFinset
    (f : ℕ → ℝ) (u : ℝ) (X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range X).filter fun n => n ∈ targetHeightFailureSet f u
noncomputable def periodicMultiplicativeHitBlock
    (N t h : ℕ) (u : ℝ) : Finset ℕ := by
  classical
  let blocks := (Finset.Ico N t).product (multiplicativeHitResidues h u)
  exact blocks.map (Nat.divModEquiv (2 ^ h)).symm.toEmbedding
noncomputable def lowerDensityCount (E : Set ℕ) (X : ℕ) : ℕ := by
  classical
  exact ((Finset.range X).filter fun n => n ∈ E).card
def LowerNaturalDensityAtLeast (E : Set ℕ) (d : ℝ) : Prop :=
  ∀ d' : ℝ, d' < d →
    ∀ᶠ X : ℕ in Filter.atTop,
      d' ≤ (lowerDensityCount E X : ℝ) / (X : ℝ)
end
end FirstPassageLinearTransport


