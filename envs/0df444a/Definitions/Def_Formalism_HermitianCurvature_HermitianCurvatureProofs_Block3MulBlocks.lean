-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T14:28:12.727301+00:00
-- url     : https://prove2.me/theorems/849f2c2e-8d8c-4555-b9b0-879a35edbcd6
-- title:
--   Block3 Mul Blocks
-- statement:
--   Definitions and structural lemmas for Block3 Mul Blocks, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Block3MulBlocks.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DetNormLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
noncomputable section
namespace Formalism.FourierDecayAlt.P.Ux5
def EB {m n : Type*} (A : Matrix m n ℂ) (c : ℝ) : Prop := ∀ i j, ‖A i j‖ ≤ c
section three
variable {k j ρ : ℕ}
def q1 (k ρ : ℕ) {j : ℕ} (a : Fin j) : Ix k j ρ := Sum.inl (Sum.inl a)
def q2 (k j : ℕ) {ρ : ℕ} (i : Fin (2 * ρ + k + 1)) : Ix k j ρ := Sum.inl (Sum.inr i)
def q3 (k ρ : ℕ) {j : ℕ} (a : Fin j) : Ix k j ρ := Sum.inr a
def bk {ι κ : Type*} (M : B.Mat k (j + ρ)) (f : ι → Ix k j ρ) (f' : κ → Ix k j ρ) : Matrix ι κ ℂ :=
  Matrix.of fun a b => M (eB k j ρ (f a)) (eB k j ρ (f' b))
end three
end Formalism.FourierDecayAlt.P.Ux5


