-- Prove2me | Definitions.Def_QAlgorithms_Defs_GeneralizedQSP
-- name    : QAlgorithms_Defs_GeneralizedQSP
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:13:44.463078+00:00
-- url     : https://prove2.me/theorems/447426aa-790f-44ea-80ab-44c3e27ae529
-- title:
--   GeneralizedQSP
-- statement:
--   GeneralizedQSP
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\GeneralizedQSP.lean

import Definitions.Def_QAlgorithms_Defs_SingleQubitCert
noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

namespace QAlgorithms

/-- The Bool-indexed single-qubit matrix r(θ,ϕ,λ)=[[exp(i(λ+ϕ))cos θ, exp(iϕ)sin θ],[exp(iλ)sin θ,−cos θ]], for real angles; false,true correspond to source 0,1. Source: arxiv-2308.01501v2 PDF p.3. -/
def gqspRotation (theta phi lam : ℝ) : Matrix Bool Bool ℂ :=
  Matrix.of fun a b => match a, b with
    | false, false => Complex.exp (Complex.I * ((lam + phi : ℝ) : ℂ)) * (Real.cos theta : ℂ)
    | false, true => Complex.exp (Complex.I * (phi : ℂ)) * (Real.sin theta : ℂ)
    | true, false => Complex.exp (Complex.I * (lam : ℂ)) * (Real.sin theta : ℂ)
    | true, true => -(Real.cos theta : ℂ)

/-- For a finite system register ι and matrix U, A(U)=diag(U,I) on Bool × ι: ((a,i),(b,j)) entry is U i j if a=b=false, the identity entry if a=b=true, and 0 if a≠b. Source: arxiv-2308.01501v2 PDF p.3. -/
def gqspSignal {ι : Type*} [DecidableEq ι] (U : Matrix ι ι ℂ) :
    Matrix (Bool × ι) (Bool × ι) ℂ :=
  Matrix.of fun p q => if p.1 = q.1 then
    (if p.1 then (1 : Matrix ι ι ℂ) p.2 q.2 else U p.2 q.2) else 0

/-- For d:ℕ, θ,ϕ:Fin(d+1)→ℝ, λ:ℝ and U, S_d(U)=R(θ_d,ϕ_d,0)A(U)...R(θ_1,ϕ_1,0)A(U)R(θ_0,ϕ_0,λ). Source: arxiv-2308.01501v2 PDF p.4. -/
def gqspSequence {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}
    (theta phi : Fin (d + 1) → ℝ) (lam : ℝ) (U : Matrix ι ι ℂ) :
    Matrix (Bool × ι) (Bool × ι) ℂ :=
  (orderedProd fun j : Fin d =>
    Matrix.kronecker (gqspRotation (theta j.succ) (phi j.succ) 0) 1 * gqspSignal U) *
    Matrix.kronecker (gqspRotation (theta 0) (phi 0) lam) 1

/-- Sanity test. Source: arxiv-2308.01501v2 PDF p.3. -/
example {ι : Type*} [Fintype ι] [DecidableEq ι] (theta phi : Fin 1 → ℝ)
    (lam : ℝ) (U : Matrix ι ι ℂ) : gqspSequence theta phi lam U =
      Matrix.kronecker (gqspRotation (theta 0) (phi 0) lam) 1 := by
  simp [gqspSequence, orderedProd]

/-- Sanity test. Source: arxiv-2308.01501v2 PDF p.3. -/
example : gqspRotation 0 0 0 = pauliZ := by
  ext a b; cases a <;> cases b <;> simp [gqspRotation, pauliZ]

/-- Sanity test. Source: arxiv-2308.01501v2 PDF p.3. -/
example {ι : Type*} [DecidableEq ι] (U : Matrix ι ι ℂ) (i j : ι) :
    gqspSignal U (false, i) (false, j) = U i j := by simp [gqspSignal]

end QAlgorithms


