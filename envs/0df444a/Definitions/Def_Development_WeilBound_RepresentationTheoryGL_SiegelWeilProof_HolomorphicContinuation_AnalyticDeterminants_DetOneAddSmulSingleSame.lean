-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_DetOneAddSmulSingleSame
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_DetOneAddSmulSingleSame
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:06:16.407246+00:00
-- url     : https://prove2.me/theorems/fea1e052-9140-4bb5-90fb-bbd805134a74
-- title:
--   Det One Add Smul Single Same
-- statement:
--   Definitions and structural lemmas for Det One Add Smul Single Same, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/DetOneAddSmulSingleSame.lean

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_InfInvA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Filter Topology
open scoped ContDiff ComplexConjugate
namespace PositivityTheory.Rg.Sw.LVs.II
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
def rmulL (x : M2 n) : M2 n →L[ℝ] M2 n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M * x
      map_add' := fun _ _ => Matrix.add_mul _ _ _
      map_smul' := fun c M => by simp }
def LawH (Θ : M2 n → ℂ) : Prop :=
  ∀ p x, InG p → p.toBlocks₂₁ = 0 → InG x → Θ (p * x) = ((‖(p.toBlocks₂₂).det‖ ^ (-(2 * (n : ℤ))) : ℝ) : ℂ) * Θ x
def lam (Y : M2 n) : ℂ := (n : ℂ) * (Y.toBlocks₁₁.trace - Y.toBlocks₂₂.trace)
def Pij (c : ℂ) (i j : Fin n) : M2 n := fromBlocks (c • Matrix.single i j 1) 0 0 (-(conj c) • Matrix.single j i 1)
def Gen (n : ℕ) : Set (M2 n) :=
  {Y | (∃ β : Matrix (Fin n) (Fin n) ℂ, βᴴ = β ∧ Y = fromBlocks 0 β 0 0) ∨ ∃ c i j, Y = Pij c i j}
def fb11 (n : ℕ) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] M2 n where
  toFun A := fromBlocks A 0 0 0
  map_add' A B := by rw [Matrix.fromBlocks_add]; simp
  map_smul' c A := by rw [Matrix.fromBlocks_smul]; simp
def fb22 (n : ℕ) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] M2 n where
  toFun A := fromBlocks 0 0 0 A
  map_add' A B := by rw [Matrix.fromBlocks_add]; simp
  map_smul' c A := by rw [Matrix.fromBlocks_smul]; simp
end PositivityTheory.Rg.Sw.LVs.II


