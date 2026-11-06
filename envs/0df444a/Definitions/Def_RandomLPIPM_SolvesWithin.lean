-- Prove2me | Definitions.Def_RandomLPIPM_SolvesWithin
-- name    : RandomLPIPM_SolvesWithin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:09:36.444228+00:00
-- url     : https://prove2.me/theorems/15da596e-bf83-4158-934a-fa4d86a4f511
-- title:
--   The method of Theorem 1.1 solves LP(A) exactly within $N$ iterations
-- statement:
--   For $A\in\mathbb R^{d\times n}$, an exponent $q>0$ and a constant $C_0>0$, the method of the proof of Theorem 1.1 is: run Algorithm 1 on LP(A) ($b=A\mathbf 1$, $c=\mathbf 1$) with
--   $$x^0=\mathbf 1,\quad \mu_{\mathrm{start}}=1,\quad \mu_{\mathrm{end}}=\frac{n^{-2(q+4)}}{2048},\quad \varepsilon=\frac16,\quad C=C_0\,(\log(ed))^{4.5},$$
--   then round the output $\hat x$ by solving the basis system on its $d$ largest coordinates.
--
--   The method **solves $A$ within $N$ iterations** when the run halts after at most $N$ evaluations of the test of line 7 (each one linear system solve in $ADA^\top$ with $D$ positive diagonal), and the rounded triple $(x,y,s)$ is an optimal primal-dual solution of LP(A).
--
--   **Formalization Note** $\log(ed)$ is the natural logarithm of $e\cdot d$; exponents are real powers. The single solve of the rounding step is not counted, as in the paper's proof.
-- source:
--   Dadush–Jiang–Kyng–Ma, Interior Point Methods Solve Random LPs in polylog(n) iterations, STOC 2027 submission (manuscript sha256 a8a320f9…), proof of Theorem 1.1, p.81

import Mathlib
import Definitions.Def_RandomLPIPM_algo1Step
import Definitions.Def_RandomLPIPM_algo1Init
import Definitions.Def_RandomLPIPM_IsHalted
import Definitions.Def_RandomLPIPM_roundBasis
import Definitions.Def_RandomLPIPM_IsPDOptimal

open Matrix

namespace RandomLPIPM

/-- **The method of Theorem 1.1 succeeds on `A` within `N` iterations.** Dadush–Jiang–Kyng–Ma, *Interior Point Methods Solve Random LPs in polylog(n) iterations*, STOC 2027 submission (manuscript sha256 a8a320f9…), proof of Theorem 1.1,
p.81: run Algorithm 1 on LP(A) (`b = A1`, `c = 1`) with `(x⁰, μ_start) = (1, 1)`,
`μ_end = n^{−2(q+4)}/2048`, `ε = 1/6` and `C = C₀ (log(e·d))^{4.5}`, then round the output `x̂` with
the basis identification of Theorem 8.11.

`SolvesWithin A q C₀ N` says: the run halts, it performs at most `N` evaluations of line 7 (each one
linear system solve in `ADAᵀ` with `D = X²` positive diagonal), and the rounded `(x, y, s)` is an
optimal primal-dual solution of LP(A).

**Formalization Note.** `log(e·d)` is the natural logarithm of Euler's number times `d`; the
exponents are real powers. The final rounding solve is outside the count, as in the proof. -/
noncomputable def SolvesWithin {d n : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) (q C₀ N : ℝ) : Prop :=
  ∃ j : ℕ,
    let s := (algo1Step A 1 ((n : ℝ) ^ (-(2 * (q + 4))) / 2048) (1 / 6)
      (C₀ * Real.log (Real.exp 1 * d) ^ (9 / 2 : ℝ)))^[j] (algo1Init 1 1)
    IsHalted s ∧ (s.solves : ℝ) ≤ N ∧
      IsPDOptimal A (A *ᵥ 1) 1 (roundBasis A s.x).1 (roundBasis A s.x).2.1 (roundBasis A s.x).2.2

end RandomLPIPM


