-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ListSumSplittings
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_ListSumSplittings
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T16:49:59.810846+00:00
-- url     : https://prove2.me/theorems/4c3243a6-daaa-4361-a4ad-b411e46ae736
-- title:
--   List Sum Splittings
-- statement:
--   Definitions and structural lemmas for List Sum Splittings, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ListSumSplittings.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ExponentWordRecursion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ComplexConjugate
noncomputable section
namespace Formalism.FourierDecayAlt.P.ListSumSplittings
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.Ux10 Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic Formalism.FourierDecayAlt.P.ListSumInequalities
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
def splits {α : Type*} : List α → List (List α × List α)
  | [] => [([], [])]
  | x :: w => (splits w).flatMap fun p => [(x :: p.1, p.2), (p.1, x :: p.2)]
def PolyClass (D : ℕ) (P : Mat k r → ℂ) : Prop :=
  CkOn (⊤ : ℕ∞) (GV k r) P ∧ ∀ a : List (Bool × Mat k r), AllLie a →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g ∈ GV k r, ‖W a P g‖ ≤ C * gN g ^ D
def varIn (p : Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) : Mat k r →ₗ[ℝ] ℂ where
  toFun g := g p.1 p.2
  map_add' _ _ := rfl
  map_smul' c g := by simp
def varCj (p : Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) : Mat k r →ₗ[ℝ] ℂ where
  toFun g := conj (g p.1 p.2)
  map_add' x y := by simp
  map_smul' c g := by simp [Complex.real_smul]
def varL : (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) ⊕ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) →
    (Mat k r →ₗ[ℝ] ℂ) := Sum.elim varIn varCj
end Formalism.FourierDecayAlt.P.ListSumSplittings


