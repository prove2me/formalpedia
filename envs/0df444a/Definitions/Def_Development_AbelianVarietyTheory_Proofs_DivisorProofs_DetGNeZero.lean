-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DetGNeZero
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_DetGNeZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T08:53:01.979047+00:00
-- url     : https://prove2.me/theorems/82c0f304-f16e-4932-badb-6a0b2caae973
-- title:
--   Det GNe Zero
-- statement:
--   Definitions and structural lemmas for Det GNe Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DetGNeZero.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdMinorsMemInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
namespace GlobalTheory.MinorFrame
def rsub {σ σ' : Type} [Fintype σ'] (M : Matrix σ' σ ℂ) : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ' ℂ :=
  aeval fun v => ∑ w, C (M w v) * X w
variable {ι : Type}
open Classical in

def frameMat {d a : ℕ} (x₀ : Var ι d a → ℂ) : Matrix (ι × Fin a × Fin a) (Var ι d a) ℂ :=
  fun w v => if w.1 = v.1 ∧ w.2.2 = v.2.2 then x₀ (v.1, v.2.1, w.2.1) else 0
def detG [Fintype ι] (a : ℕ) (n : ι → ℕ) : MvPolynomial (ι × Fin a × Fin a) ℂ :=
  ∏ τ, (Matrix.of fun i j : Fin a => (X (τ, i, j) : MvPolynomial (ι × Fin a × Fin a) ℂ)).det ^ n τ
end GlobalTheory.MinorFrame


