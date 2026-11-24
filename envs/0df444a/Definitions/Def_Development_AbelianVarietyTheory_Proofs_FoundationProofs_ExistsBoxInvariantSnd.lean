-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsBoxInvariantSnd
-- name    : Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsBoxInvariantSnd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:52:50.087161+00:00
-- url     : https://prove2.me/theorems/4856b529-5fe0-4740-9750-f92dd77129ee
-- title:
--   Exists Box Invariant Snd
-- statement:
--   Definitions and structural lemmas for Exists Box Invariant Snd, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsBoxInvariantSnd.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_GL2CharacterZeros
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi GlobalTheory.IndefiniteRowSideFullHecke.GLMatrixJoining
open scoped Topology
noncomputable section
namespace GlobalTheory.SplitDict
section Partial
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type} [Fintype n] [DecidableEq n] {T : Type} [TopologicalSpace T] [T2Space T]
variable {ψ : AddChar k Circle} {c : kˣ}
variable [MeasurableSpace k] [BorelSpace k]
def pf (ψ : AddChar k Circle) (μ : Measure (n → k)) (f : T × (n → k) → ℂ) : T × (n → k) → ℂ :=
  fun z => ∫ x, f (z.1, x) * (ψ (x ⬝ᵥ z.2) : ℂ) ∂μ
end Partial
section Matrices
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
def curryH (k : Type) [TopologicalSpace k] (a b : Type) : (a × b → k) ≃ₜ Matrix a b k where
  toFun y := Matrix.of (Function.curry y)
  invFun x := fun p => x p.1 p.2
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_matrix fun i j => continuous_apply (i, j)
  continuous_invFun := continuous_pi fun p => continuous_id.matrix_elem p.1 p.2
def curryT (k : Type) [TopologicalSpace k] (a b : Type) : Matrix b a k ≃ₜ (a × b → k) where
  toFun x := fun p => x p.2 p.1
  invFun y := Matrix.of fun j i => y (i, j)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_pi fun p => continuous_id.matrix_elem p.2 p.1
  continuous_invFun := continuous_matrix fun j i => continuous_apply (i, j)
variable [MeasurableSpace k] [BorelSpace k]
end Matrices
section Homeos
variable (k : Type) [TopologicalSpace k] (ρ v τ w W : Type)
def colsH : (Matrix W ρ k × Matrix W v k) × Matrix W ρ k ≃ₜ Matrix W (ρ ⊕ v ⊕ ρ) k where
  toFun z := glueCols z.1.1 z.1.2 z.2
  invFun x := ((Matrix.of fun i j => x i (.inl j), Matrix.of fun i j => x i (.inr (.inl j))),
    Matrix.of fun i j => x i (.inr (.inr j)))
  left_inv _ := rfl
  right_inv x := by ext i (j | j | j) <;> rfl
  continuous_toFun := continuous_matrix fun i j => by
    rcases j with j | j | j
    · exact (continuous_fst.comp continuous_fst).matrix_elem i j
    · exact (continuous_snd.comp continuous_fst).matrix_elem i j
    · exact continuous_snd.matrix_elem i j
  continuous_invFun :=
    ((continuous_matrix fun _ _ => continuous_id.matrix_elem _ _).prodMk
      (continuous_matrix fun _ _ => continuous_id.matrix_elem _ _)).prodMk
      (continuous_matrix fun _ _ => continuous_id.matrix_elem _ _)
def mixH₁ : Mix₁ k ρ v W ≃ₜ (Matrix W ρ k × Matrix W v k) × Matrix ρ W k where
  toFun z := ((z.1, z.2.2), z.2.1)
  invFun z := (z.1.1, z.2, z.1.2)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop
abbrev Kept := Matrix (τ ⊕ w ⊕ τ) ρ k × Matrix ρ (τ ⊕ w ⊕ τ) k × Matrix τ v k × Matrix w v k
def rowsH : Kept k ρ v τ w × Matrix τ v k ≃ₜ Mix₁ k ρ v (τ ⊕ w ⊕ τ) where
  toFun z := (z.1.1, z.1.2.1, glueRows z.2 z.1.2.2.2 z.1.2.2.1)
  invFun x := ((x.1, x.2.1, Matrix.of fun i j => x.2.2 (.inr (.inr i)) j,
    Matrix.of fun i j => x.2.2 (.inr (.inl i)) j), Matrix.of fun i j => x.2.2 (.inl i) j)
  left_inv _ := rfl
  right_inv x := by
    refine Prod.ext rfl (Prod.ext rfl ?_)
    ext (i | i | i) j <;> rfl
  continuous_toFun := by
    refine Continuous.prodMk (by fun_prop) (Continuous.prodMk (by fun_prop) ?_)
    refine continuous_matrix fun i j => ?_
    rcases i with i | i | i
    · exact continuous_snd.matrix_elem i j
    · exact (continuous_snd.comp (continuous_snd.comp (continuous_snd.comp continuous_fst))).matrix_elem i j
    · exact (continuous_fst.comp (continuous_snd.comp (continuous_snd.comp continuous_fst))).matrix_elem i j
  continuous_invFun :=
    (continuous_fst.prodMk ((continuous_fst.comp continuous_snd).prodMk
      ((continuous_matrix fun _ _ => (continuous_snd.comp continuous_snd).matrix_elem _ _).prodMk
      (continuous_matrix fun _ _ => (continuous_snd.comp continuous_snd).matrix_elem _ _)))).prodMk
      (continuous_matrix fun _ _ => (continuous_snd.comp continuous_snd).matrix_elem _ _)
def mixH₂ : Mix₂ k ρ v τ w ≃ₜ Kept k ρ v τ w × Matrix v τ k where
  toFun z := ((z.1, z.2.1, z.2.2.1, z.2.2.2.2), z.2.2.2.1)
  invFun z := (z.1.1, z.1.2.1, z.1.2.2.1, z.2, z.1.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop
end Homeos
section Main
variable {k : Type} [Field k]
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]
variable (ψ : AddChar k Circle) (m : Measure k) [m.IsAddHaarMeasure] (μ : kˣ →* ℂˣ) (s₁ s₂ : ℤˣ)
variable {ρ v τ w W : Type} [Fintype ρ] [DecidableEq ρ] [Fintype v] [DecidableEq v]
  [Fintype τ] [DecidableEq τ] [Fintype w] [DecidableEq w] [Fintype W] [DecidableEq W]
end Main
end GlobalTheory.SplitDict


