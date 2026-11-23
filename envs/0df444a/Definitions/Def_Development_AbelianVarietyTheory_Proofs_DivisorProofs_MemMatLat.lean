-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLat
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLat
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:00:21.759+00:00
-- url     : https://prove2.me/theorems/ea279f16-c24c-442d-a14a-58c83b256acb
-- title:
--   Mem Mat Lat
-- statement:
--   Definitions and structural lemmas for Mem Mat Lat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemMatLat.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LatOrb
open Polynomial Matrix
variable (O : Type) {K : Type} [CommRing O] [Field K] [Algebra O K]
def stdLat (n : ℕ) : Submodule O (Fin n → K) where
  carrier := {v | ∀ i, v i ∈ (algebraMap O K).range}
  add_mem' := by
    intro a b ha hb i
    exact Subring.add_mem _ (ha i) (hb i)
  zero_mem' := fun i => Subring.zero_mem _
  smul_mem' := by
    intro c v hv i
    obtain ⟨a, ha⟩ := hv i
    exact ⟨c * a, by simp [Algebra.smul_def, ha]⟩
def matLat {n : ℕ} (g : Matrix (Fin n) (Fin n) K) (M : Submodule O (Fin n → K)) :
    Submodule O (Fin n → K) :=
  M.map ((Matrix.mulVecLin g).restrictScalars O)
def IsLatV {n : ℕ} (M : Submodule O (Fin n → K)) : Prop :=
  M.FG ∧ Submodule.span K (M : Set (Fin n → K)) = ⊤
def herm {n : ℕ} (σ : K →+* K) (x y : Fin n → K) : K := ∑ k, x k * σ (y k)
def SelfDual {n : ℕ} (σ : K →+* K) (M : Submodule O (Fin n → K)) : Prop :=
  ∀ y, y ∈ M ↔ ∀ x ∈ M, herm σ y x ∈ (algebraMap O K).range
variable {O}
end GlobalTheory.LatOrb


