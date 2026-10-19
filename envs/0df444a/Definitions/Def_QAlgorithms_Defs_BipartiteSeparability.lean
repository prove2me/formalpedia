-- Prove2me | Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
-- name    : QAlgorithms_Defs_BipartiteSeparability
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T18:37:24.561754+00:00
-- url     : https://prove2.me/theorems/e3b0a26b-11db-49c7-93a8-f1c146540cf4
-- title:
--   BipartiteSeparability
-- statement:
--   BipartiteSeparability
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\BipartiteSeparability.lean

import Definitions.Def_QAlgorithms_Defs_Channel
noncomputable section

open scoped Matrix ComplexOrder

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Entanglement

/-- arxiv-quant-ph-9604005v2 PDF p.2; arxiv-quant-ph-0102117v1 PDF p.2. -/
def partialTransposeFirst {I J : Type*} (X : Matrix (I × J) (I × J) ℂ) :
    Matrix (I × J) (I × J) ℂ := Matrix.of fun p q => X (q.1,p.2) (p.1,q.2)

/-- arxiv-quant-ph-9604005v2 PDF p.2; arxiv-quant-ph-0302032v3 PDF p.2; arxiv-quant-ph-0302032v3 PDF p.4. -/
def IsSeparableDensity {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
    (X : Matrix (I × J) (I × J) ℂ) : Prop :=
  ∃ q : ℕ, ∃ w : Fin q → ℝ, ∃ A : Fin q → Matrix I I ℂ, ∃ B : Fin q → Matrix J J ℂ,
    (∀ j, 0 ≤ w j) ∧ (∑ j, w j) = 1 ∧
    (∀ j, IsDensityMatrix (A j) ∧ IsDensityMatrix (B j)) ∧
    X = ∑ j, (w j : ℂ) • Matrix.kronecker (A j) (B j)

/-- arxiv-quant-ph-0302031v2 PDF p.2; arxiv-quant-ph-0302031v2 PDF p.5; arxiv-quant-ph-0302031v2 PDF p.10. -/
def IsSeparablePositive {I J : Type*} [Fintype I] [Fintype J]
    (X : Matrix (I × J) (I × J) ℂ) : Prop :=
  ∃ q : ℕ, ∃ w : Fin q → ℝ, ∃ A : Fin q → Matrix I I ℂ, ∃ B : Fin q → Matrix J J ℂ,
    (∀ j, 0 ≤ w j) ∧ (∀ j, IsDensityMatrix (A j) ∧ IsDensityMatrix (B j)) ∧
    X = ∑ j, (w j : ℂ) • Matrix.kronecker (A j) (B j)

/-- arxiv-quant-ph-0302031v2 PDF p.2; arxiv-quant-ph-0302031v2 PDF p.4; arxiv-quant-ph-0302031v2 PDF p.5. -/
def IsEntanglementBreakingPositive {d : ℕ}
    (Phi : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∀ a : ℕ, 0 < a → ∀ X : Matrix (Fin a × Fin d) (Fin a × Fin d) ℂ,
    IsDensityMatrix X → IsSeparablePositive (idTensorSuperop Phi X)

/-- arxiv-quant-ph-0302032v3 PDF p.1; arxiv-quant-ph-0302032v3 PDF p.2; arxiv-quant-ph-0302032v3 PDF p.3. -/
def IsEntanglementBreaking (Phi : Matrix Bool Bool ℂ →ₗ[ℂ] Matrix Bool Bool ℂ) : Prop :=
  ∀ a : ℕ, ∀ ha : 0 < a,
    letI : Nonempty (Fin a) := ⟨⟨0,ha⟩⟩
    ∀ X : Matrix (Fin a × Bool) (Fin a × Bool) ℂ, IsDensityMatrix X →
      IsSeparableDensity (idTensorSuperop Phi X)

/-- Sanity check for the source model (arxiv-quant-ph-9604005v2 PDF p.2). -/
example {I J : Type*} (X : Matrix (I × J) (I × J) ℂ) :
    partialTransposeFirst (partialTransposeFirst X) = X := rfl

/-- Sanity check for the source model (arxiv-quant-ph-9604005v2 PDF p.2). -/
example {I J : Type*} [Fintype I] [Fintype J] :
    IsSeparablePositive (0 : Matrix (I × J) (I × J) ℂ) := by
  refine ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, ?_, ?_, ?_⟩
  · intro j; exact Fin.elim0 j
  · intro j; exact Fin.elim0 j
  · simp

end QAlgorithms.Entanglement


