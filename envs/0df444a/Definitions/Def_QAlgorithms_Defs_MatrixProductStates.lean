-- Prove2me | Definitions.Def_QAlgorithms_Defs_MatrixProductStates
-- name    : QAlgorithms_Defs_MatrixProductStates
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:23:18.900716+00:00
-- url     : https://prove2.me/theorems/bf13ec59-4512-4374-8d32-ab9440cf1835
-- title:
--   MatrixProductStates
-- statement:
--   MatrixProductStates
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\MatrixProductStates.lean

import Definitions.Def_QAlgorithms_Defs_SingleQubitCert
import Definitions.Def_QAlgorithms_Defs_HamiltonianDQI
noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

namespace QAlgorithms

/-- Definition 2: amplitudes v_LᵀA^(1)(y_1)⋯A^(r)(y_r)v_R, local physical dimension q, bond dimension D. Source: arxiv-2601.18773v1 PDF p.5; arxiv-2601.18773v1 PDF p.6; arxiv-2601.18773v1 PDF p.7; arxiv-2601.18773v1 PDF p.8. -/
structure OpenBoundaryMPS (r q D : ℕ) where
  left : Fin D → ℂ
  right : Fin D → ℂ
  localMatrix : Fin r → Fin q → Matrix (Fin D) (Fin D) ℂ

/-- Vector with amplitudes vL^T A_1(y_1)...A_m(y_m) vR on Fin m -> Fin q. Source: arxiv-2601.18773v1 PDF p.5; arxiv-2601.18773v1 PDF p.7. -/
def mpsState {r q D : ℕ} (M : OpenBoundaryMPS r q D) : EuclideanSpace ℂ (Fin r → Fin q) :=
  WithLp.toLp 2 fun y =>
    M.left ⬝ᵥ (((List.ofFn fun i => M.localMatrix i (y i)).prod).mulVec M.right)

/-- Construct q=2,D=l+1,m-site data: vL=e0/N, vR_j=a_j*j!, and A_i(y)_(j,k)=c_i^(k-j)/(k-j)! for j<=k and (k-j) mod 2=y, otherwise zero. Source: arxiv-2601.18773v1 PDF p.6; arxiv-2601.18773v1 PDF p.7. -/
def hdqiReferenceMPS {m : ℕ} (c : Fin m → ℝ) (P : Polynomial ℝ) (l : ℕ) :
    OpenBoundaryMPS m 2 (l + 1) where
  left := fun j => if (j : ℕ) = 0 then (hdqiReferenceNorm c P l : ℂ)⁻¹ else 0
  right := fun j => (P.coeff j : ℂ) * ((j : ℕ).factorial : ℂ)
  localMatrix := fun i y => Matrix.of fun j k =>
    if (j : ℕ) ≤ k ∧ ((k : ℕ) - j) % 2 = (y : ℕ)
    then (c i : ℂ) ^ ((k : ℕ) - j) / (((k : ℕ) - j).factorial : ℂ) else 0

/-- Sanity test. Source: arxiv-2601.18773v1 PDF p.5; arxiv-2601.18773v1 PDF p.6; arxiv-2601.18773v1 PDF p.7; arxiv-2601.18773v1 PDF p.8. -/
example {q D : ℕ} (M : OpenBoundaryMPS 0 q D) (y : Fin 0 → Fin q) :
    mpsState M y = M.left ⬝ᵥ M.right := by simp [mpsState]

/-- Sanity test. Source: arxiv-2601.18773v1 PDF p.5; arxiv-2601.18773v1 PDF p.6; arxiv-2601.18773v1 PDF p.7; arxiv-2601.18773v1 PDF p.8. -/
example {m : ℕ} (c : Fin m → ℝ) (P : Polynomial ℝ) (i : Fin m) :
    (hdqiReferenceMPS c P 0).localMatrix i 0 0 0 = 1 ∧
      (hdqiReferenceMPS c P 0).localMatrix i 1 0 0 = 0 := by simp [hdqiReferenceMPS]

end QAlgorithms


