-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixTranspose
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixTranspose
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T14:28:48.790999+00:00
-- url     : https://prove2.me/theorems/d9500bce-b537-4ab9-b560-8c94ff8da0a1
-- title:
--   Symmetric Scalar Block Matrix Transpose
-- statement:
--   Definitions and structural lemmas for Symmetric Scalar Block Matrix Transpose, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixTranspose.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MulDiagOfTriangular
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
noncomputable section
namespace Formalism.FourierDecayAlt.P.Ux2
section blocks3
variable {k j ρ : ℕ}
section blocks
variable (M : B.Mat k (j + ρ))
def b11 : Matrix (Fin j) (Fin j) ℂ := Matrix.of fun a b => M (eB k j ρ (Sum.inl (Sum.inl a))) (eB k j ρ (Sum.inl (Sum.inl b)))
def b12 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ := Matrix.of fun a b => M (eB k j ρ (Sum.inl (Sum.inl a))) (eB k j ρ (Sum.inl (Sum.inr b)))
def b13 : Matrix (Fin j) (Fin j) ℂ := Matrix.of fun a b => M (eB k j ρ (Sum.inl (Sum.inl a))) (eB k j ρ (Sum.inr b))
def b21 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ := Matrix.of fun a b => M (eB k j ρ (Sum.inl (Sum.inr a))) (eB k j ρ (Sum.inl (Sum.inl b)))
def b22 : B.Mat k ρ := Matrix.of fun a b => M (eB k j ρ (Sum.inl (Sum.inr a))) (eB k j ρ (Sum.inl (Sum.inr b)))
def b23 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ := Matrix.of fun a b => M (eB k j ρ (Sum.inl (Sum.inr a))) (eB k j ρ (Sum.inr b))
def b31 : Matrix (Fin j) (Fin j) ℂ := Matrix.of fun a b => M (eB k j ρ (Sum.inr a)) (eB k j ρ (Sum.inl (Sum.inl b)))
def b32 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ := Matrix.of fun a b => M (eB k j ρ (Sum.inr a)) (eB k j ρ (Sum.inl (Sum.inr b)))
def b33 : Matrix (Fin j) (Fin j) ℂ := Matrix.of fun a b => M (eB k j ρ (Sum.inr a)) (eB k j ρ (Sum.inr b))
end blocks
end blocks3
section tri
variable {p : ℕ}
def uniK (κ : Fin p → ℤ) (M : Matrix (Fin p) (Fin p) ℂ) : Prop :=
  (∀ i, M i i = 1) ∧ ∀ a b, κ a < κ b → M a b = 0
def kL (p : ℕ) : Fin p → ℤ := fun a => (a.val : ℤ)
def kU (p : ℕ) : Fin p → ℤ := fun a => -(a.val : ℤ)
def kS (σ : Equiv.Perm (Fin p)) : Fin p → ℤ := fun a => ((σ.symm a).val : ℤ)
end tri
section twoBlocks
variable {p s : ℕ}
end twoBlocks
end Formalism.FourierDecayAlt.P.Ux2
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P


