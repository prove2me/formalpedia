-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMemMatrixAlgebra
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMemMatrixAlgebra
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T15:05:41.66629+00:00
-- url     : https://prove2.me/theorems/45c9763d-2aea-4412-8b65-08b031901bf0
-- title:
--   Lift Mem Matrix Algebra
-- statement:
--   Definitions and structural lemmas for Lift Mem Matrix Algebra, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LiftMemMatrixAlgebra.lean

import Definitions.Def_Formalism_HermitianCurvature_CompositeFormulaLevelZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
open scoped ComplexConjugate
noncomputable section
namespace Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T
section MatSub
variable {A : Type} [Ring A] [Algebra ℂ A]
def matSub (C : Subalgebra ℂ A) (n : Type) [Fintype n] [DecidableEq n] : Subalgebra ℂ (Matrix n n A) where
  carrier := {M | ∀ i j, M i j ∈ C}
  mul_mem' := by
    intro M N hM hN i j
    rw [Matrix.mul_apply]
    exact Subalgebra.sum_mem _ fun k _ => Subalgebra.mul_mem _ (hM i k) (hN k j)
  add_mem' := by
    intro M N hM hN i j
    exact Subalgebra.add_mem _ (hM i j) (hN i j)
  algebraMap_mem' := by
    intro c i j
    rw [Matrix.algebraMap_matrix_apply]
    split_ifs
    · exact C.algebraMap_mem c
    · exact C.zero_mem
variable {S : Type} [Fintype S] [DecidableEq S] (C : Subalgebra ℂ A)
end MatSub
section Act
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]
end Act
section Wave
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]
end Wave
section StepParts
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]
variable (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
  (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
  (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π')))
  (K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')) (l0 : ℕ)
end StepParts
end Formalism.FourierDecayAlt.P5


