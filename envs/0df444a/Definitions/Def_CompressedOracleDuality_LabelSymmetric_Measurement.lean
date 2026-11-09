-- Prove2me | Definitions.Def_CompressedOracleDuality_LabelSymmetric_Measurement
-- name    : CompressedOracleDuality_LabelSymmetric_Measurement
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T12:02:37.226206+00:00
-- url     : https://prove2.me/theorems/3c3f5644-2736-431a-8c2c-d903f72d799c
-- title:
--   Canonical polar factor and completed square-root measurement
-- statement:
--   Let $B$ be a coefficient matrix with memory rows and database columns, and put $\rho=BB^\dagger$. The inverse square root $\rho^{-1/2}$ is defined spectrally, inverting positive square roots and sending the eigenvalue zero to zero. Put $U=\rho^{-1/2}B$. For a column $b_D=B|D\rangle$, write $b_Db_D^\dagger$ for its unnormalized pure density matrix.
--
--   The database measurement and its complementary failure effect are
--   $$E_D=U|D\rangle\langle D|U^\dagger,\qquad E_\bot=I-UU^\dagger.$$
--   The column density is exactly $p_D|\psi^D\rangle\langle\psi^D|$; no conditional state has to be selected when $p_D=0$. These definitions describe the measurement algebraically; the POVM property and its distributional meaning are theorem obligations, not assumptions.
-- source:
--   Ding and Zhandry, Compressed Oracle Duality: A simple framework for knowing what quantum adversaries know, October 30, 2026 preprint, arXiv:submit/8306656 [quant-ph], STOC 2027 submission #94, SHA-256 6614c6a707d45eff1e475fa25c9c0d22747adf304a0680ebf79d2bd118122daa, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/94.pdf, p. 12, (13); pp. 14–15, polar decomposition and (25)

import Definitions.Def_CompressedOracleDuality_LabelSymmetric_Database

open QAlgorithms
open scoped BigOperators MatrixOrder ComplexOrder

noncomputable section

namespace CompressedOracleDuality.LabelSymmetric

/-- §3.1, (25): inverse square root is zero on the kernel. -/
def inverseSqrt {ι : Type} [Fintype ι] [DecidableEq ι] (ρ : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  cfc (fun x : ℝ => (Real.sqrt x)⁻¹) ρ

def columnDensity {ι κ : Type} (B : Matrix ι κ ℂ) (d : κ) : Matrix ι ι ℂ :=
  fun i j => B i d * star (B j d)

/-- The canonical polar factor U = ρ^{-1/2} A. -/
def polarFactor {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (B : Matrix ι κ ℂ) : Matrix ι κ ℂ := inverseSqrt (B * B.conjTranspose) * B

/-- (25): database outcomes and the null-support failure outcome. -/
def dualPOVM {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι (Database n) ℂ) : Option (Database n) → Matrix ι ι ℂ
  | some D => columnDensity (polarFactor B) D
  | none => 1 - polarFactor B * (polarFactor B).conjTranspose

end CompressedOracleDuality.LabelSymmetric


