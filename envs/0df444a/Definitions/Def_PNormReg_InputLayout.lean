-- Prove2me | Definitions.Def_PNormReg_InputLayout
-- name    : PNormReg_InputLayout
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:39:43.720779+00:00
-- url     : https://prove2.me/theorems/1ee5b94c-e3fa-408e-8075-2dd004268669
-- title:
--   Input layouts of Theorems 2 and 9
-- statement:
--   How an instance is presented to the machine. For problem (1), integer memory holds $n,d$ and real memory holds $p,\epsilon,\delta$ followed by $A$ in row-major order and then $b$, so that $A_{ij}$ is at cell $3+id+j$ and $b_i$ at cell $3+nd+i$. For Theorem 9, integer memory holds $n,d,m$ and real memory holds $p,\epsilon,\delta,\nu_0$ followed by $a,Q,N,b,C,\ell,x^{(0)}$ consecutively. All other cells are zero.
--
--   The layouts fix what "input" means in the running-time statements.
--
--   **Formalization Note** The paper names no input format, so this is a reading. The format is dense, matching the $nd^{\omega-1}$ bound, which already pays for reading all of $A$. The output is read from cells $-1-j$ for $j<d$.
-- source:
--   Adil, Bullins, O'Carroll, Sidford, Solving p-norm regression in matrix multiplication time, STOC 2027 submission (manuscript sha256 e335b2fa…), problem (1), p.1; Theorem 9, p.20

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_PNormReg_Regression

namespace PNormReg

/-!
# How the inputs of Theorems 2 and 9 sit in the machine's memory

Adil, Bullins, O'Carroll, Sidford, *Solving p-norm regression in matrix multiplication time*,
STOC 2027 submission (manuscript sha256 e335b2fa…), inputs of problem (1), p.1, and of Theorem 9, p.20.

**Formalization Note.** The layouts are a reading: the paper names no input format. Matrices are dense
and row-major, so `A i j` is at offset `i·d + j` of its block. The output is read by
`PNormReg.outputVec`.
-/

/-- A matrix as a row-major list: entry `(i, j)` is at position `i·d + j`. -/
def rowMajor {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) : List ℝ :=
  List.ofFn fun k : Fin (n * d) => A (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2

/-- The input of problem (1). Integer memory: cell `0` is `n`, cell `1` is `d`. Real memory: `p, ϵ, δ`
in cells `0, 1, 2`, then `A` row-major, then `b`. -/
noncomputable def goalInput {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) (b : Fin n → ℝ)
    (p ε δ : ℝ) : State :=
  initState [(n : ℤ), (d : ℤ)] ([p, ε, δ] ++ rowMajor A ++ List.ofFn b)

/-- The input of Theorem 9. Integer memory: `n, d, m`. Real memory: `p, ϵ, δ, ν₀`, then
`a, Q, N, b, C, ℓ, x⁽⁰⁾` consecutively, matrices row-major. -/
noncomputable def theorem9Input {n d m : ℕ} (G : GenRegression n d m) (p ε δ ν₀ : ℝ)
    (x₀ : Fin d → ℝ) : State :=
  initState [(n : ℤ), (d : ℤ), (m : ℤ)]
    ([p, ε, δ, ν₀] ++ List.ofFn G.a ++ rowMajor G.Q ++ rowMajor G.N ++ List.ofFn G.b ++
      rowMajor G.C ++ List.ofFn G.ell ++ List.ofFn x₀)

end PNormReg


