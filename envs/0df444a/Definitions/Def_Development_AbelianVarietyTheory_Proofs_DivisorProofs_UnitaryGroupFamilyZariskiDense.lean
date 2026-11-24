-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryGroupFamilyZariskiDense
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryGroupFamilyZariskiDense
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T08:59:23.194251+00:00
-- url     : https://prove2.me/theorems/08b5f091-9344-453a-bde8-1720ad101e29
-- title:
--   Unitary Group Family Zariski Dense
-- statement:
--   Definitions and structural lemmas for Unitary Group Family Zariski Dense, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryGroupFamilyZariskiDense.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DetGNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical MvPolynomial
open scoped Matrix ComplexOrder
noncomputable section
namespace GlobalTheory.UnitaryZariskiDense
variable {ι : Type} {a : ℕ}
def tr (v : ι × Fin a × Fin a) : ι × Fin a × Fin a := (v.1, v.2.2, v.2.1)
def cα : ℂ := ⟨1 / 2, 1 / 2⟩
def cβ : ℂ := ⟨-1 / 2, 1 / 2⟩
def cγ : ℂ := ⟨1 / 2, -1 / 2⟩
def cδ : ℂ := ⟨-1 / 2, -1 / 2⟩
def cay {n : Type} [Fintype n] [DecidableEq n] (B : Matrix n n ℂ) : Matrix n n ℂ := (1 - B) * (1 + B)⁻¹
def varMat (τ : ι) : Matrix (Fin a) (Fin a) (MvPolynomial (ι × Fin a × Fin a) ℂ) :=
  Matrix.of fun i j => X (τ, i, j)
def famOf (x : ι × Fin a × Fin a → ℂ) (τ : ι) : Matrix (Fin a) (Fin a) ℂ := Matrix.of fun i j => x (τ, i, j)
variable [Fintype ι]
def denom : MvPolynomial (ι × Fin a × Fin a) ℂ := ∏ τ, (1 + varMat τ).det
def numer (v : ι × Fin a × Fin a) : MvPolynomial (ι × Fin a × Fin a) ℂ :=
  ((1 - varMat (a := a) v.1) * (1 + varMat v.1).adjugate :
      Matrix (Fin a) (Fin a) (MvPolynomial (ι × Fin a × Fin a) ℂ)) v.2.1 v.2.2 *
    ∏ τ ∈ Finset.univ.erase v.1, (1 + varMat τ).det
def clearQ (Q : MvPolynomial (ι × Fin a × Fin a) ℂ) : MvPolynomial (ι × Fin a × Fin a) ℂ :=
  ∑ d ∈ Q.support, C (coeff d Q) * (∏ v ∈ d.support, numer v ^ d v) *
    denom ^ (Q.totalDegree - d.sum fun _ e => e)
end GlobalTheory.UnitaryZariskiDense


