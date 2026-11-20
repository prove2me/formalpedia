-- Prove2me | Definitions.Def_GaoQuantumUnion_Model
-- name    : GaoQuantumUnion_Model
-- status  : Definition
-- author  : @Mrnaiq
-- created : 2026-11-19T21:44:54.961579+00:00
-- url     : https://prove2.me/theorems/25584cd4-4a6c-46f2-a7a6-40dc2a39c5da
-- title:
--   Ordered projective measurements, outcome probabilities and conditional states
-- statement:
--   Finite complex matrices are used. An orthogonal projector is Hermitian and idempotent. For a family indexed in ascending order, the sequential operator is $K=P_{N-1}\cdots P_0$, defined as the identity for an empty sequence. The unnormalized output is $K\rho K^\dagger$ and its real trace is the joint success probability $q$. Failure terms are $\operatorname{Tr}((I-P_i)\rho)$, summed on the original input. The conditional state is $q^{-1}K\rho K^\dagger$; Lean makes it zero when $q=0$, and every disturbance theorem separately requires $q>0$. Rank-one matrices and unit-vector predicates support the pure-state lemma. Definitions impose no theorem hypotheses; the theorems supply density and projector assumptions.
-- source:
--   Jingliang Gao, Quantum union bounds for sequential projective measurements, arXiv:1410.5688v2, Physical Review A 92, 052331 (2015), https://doi.org/10.1103/PhysRevA.92.052331; PDF pp. 2–5: sequential experiment, Theorem 1, Corollary 1, Remark 1 and pure-state representation

import Definitions.Def_WildeQIT_traceDist
import Definitions.Def_WildeQIT_IsDensityOperator
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.List.OfFn
noncomputable section
open Matrix WildeQIT
open scoped MatrixOrder ComplexOrder ComplexConjugate
set_option autoImplicit false
namespace GaoQuantumUnion
variable {ι : Type} [Fintype ι] [DecidableEq ι]
def IsProjector (P : Matrix ι ι ℂ) : Prop := P.IsHermitian ∧ P*P=P
def seqOp {N : ℕ} (P : Fin N → Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (List.ofFn P).foldl (fun K Q => Q*K) 1
def seqOutput {N : ℕ} (P : Fin N → Matrix ι ι ℂ) (ρ : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  seqOp P*ρ*(seqOp P)ᴴ
def successProb {N : ℕ} (P : Fin N → Matrix ι ι ℂ) (ρ : Matrix ι ι ℂ) : ℝ :=
  (seqOutput P ρ).trace.re
def failureTerm (P ρ : Matrix ι ι ℂ) : ℝ := ((1-P)*ρ).trace.re
def failureSum {N : ℕ} (P : Fin N → Matrix ι ι ℂ) (ρ : Matrix ι ι ℂ) : ℝ :=
  ∑ i, failureTerm (P i) ρ
def postState {N : ℕ} (P : Fin N → Matrix ι ι ℂ) (ρ : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (successProb P ρ : ℂ)⁻¹ • seqOutput P ρ
def pureState (ψ : ι → ℂ) : Matrix ι ι ℂ := vecMulVec ψ (star ψ)
def IsUnitVector (ψ : ι → ℂ) : Prop := ∑ i, ‖ψ i‖^2=1
end GaoQuantumUnion


