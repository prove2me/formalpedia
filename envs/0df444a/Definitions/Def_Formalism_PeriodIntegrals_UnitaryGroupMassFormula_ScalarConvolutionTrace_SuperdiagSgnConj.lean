-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_SuperdiagSgnConj
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_SuperdiagSgnConj
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:49:38.852281+00:00
-- url     : https://prove2.me/theorems/07cf275c-3269-49f2-9b46-b533c068e61f
-- title:
--   Superdiag Sgn Conj
-- statement:
--   Definitions and structural lemmas for Superdiag Sgn Conj, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ScalarConvolutionTrace/SuperdiagSgnConj.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
noncomputable section
open Classical
namespace PI.GGConvScalarW
open Formalism.L2.SG.GGMirabolic
variable {F : Type} [Field F] [Fintype F] {k : ℕ}
def IsUTm (A : Matrix (Fin k) (Fin k) F) : Prop :=
  (∀ i, A i i = 1) ∧ ∀ i j, j < i → A i j = 0
def sgnM (k : ℕ) : Matrix (Fin k) (Fin k) F := Matrix.diagonal fun i => (-1 : F) ^ (i : ℕ)
theorem sgnM_mul_self : sgnM (F := F) k * sgnM k = 1 := by
  unfold sgnM
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
def sgn (k : ℕ) : GL (Fin k) F := ⟨sgnM k, sgnM k, sgnM_mul_self, sgnM_mul_self⟩
end PI.GGConvScalarW


