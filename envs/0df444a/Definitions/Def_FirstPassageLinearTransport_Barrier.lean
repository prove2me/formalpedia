-- Prove2me | Definitions.Def_FirstPassageLinearTransport_Barrier
-- name    : FirstPassageLinearTransport_Barrier
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T10:59:34.656696+00:00
-- url     : https://prove2.me/theorems/3d1a8572-5e25-4a72-b4cd-f959af494fa4
-- title:
--   Barrier
-- statement:
--   Definitions and structural lemmas for Barrier, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Barrier.lean

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_FirstPassageLinearTransport_Parity
import Definitions.Def_FirstPassageLinearTransport_Density
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero


set_option autoImplicit true
namespace FirstPassageLinearTransport
open scoped BigOperators
def boolWalkStep (b : Bool) : ℤ :=
  if b then 1 else -1
@[simp] theorem boolWalkStep_false : boolWalkStep false = -1 := rfl
@[simp] theorem boolWalkStep_true : boolWalkStep true = 1 := rfl
def hitsBarrierFrom (a : ℝ) :
    (r : ℕ) → ℤ → (Fin r → Bool) → Prop
  | 0, y, _ => a < |(y : ℝ)|
  | r + 1, y, v =>
      a < |(y : ℝ)| ∨
        hitsBarrierFrom a r (y + boolWalkStep (v 0))
          (fun i => v i.succ)
noncomputable def barrierHitCount (a : ℝ) (r : ℕ) (y : ℤ) : ℕ := by
  classical
  exact (Finset.univ.filter (hitsBarrierFrom a r y)).card
noncomputable def safeHitSuccEquiv {a : ℝ} {r : ℕ} {y : ℤ}
    (hy : ¬a < |(y : ℝ)|) :
    {v : Fin (r + 1) → Bool // hitsBarrierFrom a (r + 1) y v} ≃
      Σ b : Bool,
        {w : Fin r → Bool //
          hitsBarrierFrom a r (y + boolWalkStep b) w} :=
  ((Fin.consEquiv (fun _ : Fin (r + 1) => Bool)).symm.subtypeEquiv (fun v => by
      change
        hitsBarrierFrom a (r + 1) y v ↔
          hitsBarrierFrom a r (y + boolWalkStep (v 0))
            (fun i => v i.succ)
      simp [hitsBarrierFrom, hy])).trans
    (Equiv.subtypeProdEquivSigmaSubtype
      (fun b w => hitsBarrierFrom a r (y + boolWalkStep b) w))
def boolParityCode (M : ℕ) (n : Fin (2 ^ M)) : Fin M → Bool :=
  fun i => finTwoEquiv (parityCode M n i)
noncomputable def boolParityEquiv (M : ℕ) :
    Fin (2 ^ M) ≃ (Fin M → Bool) :=
  (parityEquiv M).trans (Equiv.piCongrRight fun _ => finTwoEquiv)
@[simp] theorem boolParityEquiv_apply (M : ℕ) (n : Fin (2 ^ M)) :
    boolParityEquiv M n = boolParityCode M n := rfl
noncomputable def barrierResidues (M : ℕ) (h : ℝ) :
    Finset (Fin (2 ^ M)) := by
  classical
  exact Finset.univ.filter
    (fun x => hitsBarrierFrom (2 * h) M 0 (boolParityCode M x))
noncomputable def barrierResidueEquiv (M : ℕ) (h : ℝ) :
    {x : Fin (2 ^ M) //
      hitsBarrierFrom (2 * h) M 0 (boolParityCode M x)} ≃
      {v : Fin M → Bool // hitsBarrierFrom (2 * h) M 0 v} :=
  (boolParityEquiv M).subtypeEquiv (fun x => by
    rw [boolParityEquiv_apply])
def boolParityWord (M n : ℕ) : Fin M → Bool :=
  fun i => finTwoEquiv (parityBit n i)
noncomputable def shellBarrierHit (M : ℕ) (h : ℝ) : Finset ℕ := by
  classical
  exact (dyadicShell M).filter
    (fun n => hitsBarrierFrom (2 * h) M 0 (boolParityWord M n))
def MaximalParityRegular (n M : ℕ) (h : ℝ) : Prop :=
  ∀ H : ℕ, H ≤ M →
    |(oddCount n H : ℝ) - (H : ℝ) / 2| ≤ h
noncomputable def shellMaximalParityBad (M : ℕ) (h : ℝ) : Finset ℕ := by
  classical
  exact (dyadicShell M).filter (fun n => ¬MaximalParityRegular n M h)
end FirstPassageLinearTransport


