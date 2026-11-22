-- Prove2me | Definitions.Def_LeanPool_QECCertificates_RowspaceKernel
-- name    : LeanPool_QECCertificates_RowspaceKernel
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:41:14.491361+00:00
-- url     : https://prove2.me/theorems/348b7aef-5730-47de-8580-76b661302daa
-- title:
--   Rowspace Kernel
-- statement:
--   Definitions and structural lemmas for Rowspace Kernel, from Shuoming An; LeanPool contributors's pinned Quantum code certificates and hypergraph-product theory development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/RowspaceKernel.lean

module
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.InformationTheory.Hamming
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Tauto
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace QECCertificates
noncomputable instance submoduleSetFintype
    (C : Submodule (ZMod 2) (Fin n → ZMod 2)) : Fintype ↑(C : Set (Fin n → ZMod 2)) := by
  classical
  infer_instance
def _root_.Matrix.certificateRowSpace {α β γ : Type*} [Semiring γ] (M : Matrix α β γ) :=
    (Submodule.span γ (Set.range M))
noncomputable def minWeightKernelOutsideRowSpace {n k₁ k₂ : ℕ}
  (M₁ : Matrix (Fin k₁) (Fin n) (ZMod 2))
  (M₂ : Matrix (Fin k₂) (Fin n) (ZMod 2)) : ℕ :=
  let undetectable_errors : Set (Fin n → ZMod 2) :=
    (LinearMap.ker M₁.toLin' \ M₂.certificateRowSpace)
  match Finset.min (Finset.image hammingNorm undetectable_errors.toFinset) with
  | ⊤ => n + 1
  | some a => a
def _root_.Matrix.certificateMutuallyOrthogonalRows {α β γ δ : Type*} [Fintype γ] [Mul δ]
    [AddCommMonoid δ]
  (M₁ : Matrix α γ δ) (M₂ : Matrix β γ δ) : Prop := ∀ a b, M₁ a ⬝ᵥ M₂ b = 0
def _root_.Matrix.certificateIsKernelFor {k₁ k₂ n : ℕ} (M₁ : Matrix (Fin k₁) (Fin n) (ZMod 2)) (M₂
    : Matrix (Fin k₂) (Fin n) (ZMod 2))
  : Prop := M₁.certificateRowSpace = LinearMap.ker M₂.toLin'
end QECCertificates


