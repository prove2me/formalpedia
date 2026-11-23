-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ProdLeadMinorDiagonal
-- name    : Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ProdLeadMinorDiagonal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:44:15.629081+00:00
-- url     : https://prove2.me/theorems/608e404b-86b5-4809-bef4-13ff4762ce8c
-- title:
--   Prod Lead Minor Diagonal
-- statement:
--   Definitions and structural lemmas for Prod Lead Minor Diagonal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ProdLeadMinorDiagonal.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
namespace GlobalTheory
namespace UnipotentInvariant
variable {K : Type*} [Field K] {p : ℕ}
def rowAdd (a b : Fin p) (t : K) (M : Matrix (Fin p) (Fin p) K) : Matrix (Fin p) (Fin p) K :=
  Matrix.of fun i k => M i k + if i = b then t * M a k else 0
def BiInvariant (f : Matrix (Fin p) (Fin p) K → K) : Prop :=
  (∀ a b : Fin p, a < b → ∀ t M, f (rowAdd a b t M) = f M) ∧
  (∀ a b : Fin p, a < b → ∀ t M, f (rowAdd a b t M)ᵀ = f Mᵀ)
def leadMinor (i : Fin p) (M : Matrix (Fin p) (Fin p) K) : K :=
  (Matrix.of fun a b : Fin (i.val + 1) => M (Fin.castLE i.isLt a) (Fin.castLE i.isLt b)).det
variable {σ : Type*} [DecidableEq σ]
noncomputable def setBlock (z : Fin p × Fin p → σ) (x : σ → K) (M : Matrix (Fin p) (Fin p) K) :
    σ → K :=
  Function.extend z (fun w => M w.1 w.2) x
end UnipotentInvariant
end GlobalTheory


