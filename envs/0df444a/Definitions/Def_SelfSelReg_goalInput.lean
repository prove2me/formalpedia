-- Prove2me | Definitions.Def_SelfSelReg_goalInput
-- name    : SelfSelReg_goalInput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:46:14.586206+00:00
-- url     : https://prove2.me/theorems/82c5cf6d-ec52-4aee-a06c-03ebf892baa1
-- title:
--   Input list, output layout and resource bound of the recovery program
-- statement:
--   These are the conventions of the goal theorem for the recovery algorithm (Algorithm 9.1: "Input: Known $B,\Delta,k,\varepsilon,\delta$, and sample access to $(X,Y_{\max})$. Output: $k$ vectors in $\mathbb R^n$").
--
--   1. **Input.** The memory holds $k,\varepsilon,\delta,B,\Delta$ from cell $0$; the machine dimension is $n+1$, held in pointer $0$, so the program learns $n$ as that value minus one.
--   2. **Output.** A halted state is read as $k$ vectors $\hat w_1,\dots,\hat w_k\in\mathbb R^n$: coordinate $j$ of $\hat w_i$ is the memory cell at address $p_1+i\,n+j$, where $p_1$ is pointer register $1$. Every halted state decodes to exactly $k$ vectors.
--   3. **Resource bound.** For a constant $C\in\mathbb N$,
--   $$R_C(n,k,\varepsilon,\delta,B,\Delta)=C\Big(\frac{nk}{\varepsilon}\Big)^{C(B/\Delta)^C}\log\frac1\delta ,$$
--   the reading of $\widetilde O\big((nk/\varepsilon)^{\mathrm{poly}(B/\Delta)}\log(1/\delta)\big)$ with one constant, natural logarithm.
--
--   **Formalization Note** The page fixes no input or output format; these are conventions. The factors suppressed by $\widetilde O$ are logarithms in $n,k,1/\varepsilon$, absorbed by the exponent since $nk/\varepsilon\ge4$.
-- source:
--   Zhou, Linear Regression with Self-Selection Bias in Polynomial Time, STOC 2027 submission (manuscript sha256 5d65f750…), Theorem 1.3, p.2–3 (PDF pp.5–6); Algorithm 9.1, p.66 (PDF p.69); Proposition G.1, p.94 (PDF p.97)

import Mathlib
import Definitions.Def_GaussMixHH_Machine

namespace SelfSelReg

/-- **The input and output conventions of the recovery program** (Theorem 1.3; Algorithm 9.1).

F. Zhou, *Linear Regression with Self-Selection Bias in Polynomial Time*, STOC 2027 submission
(manuscript sha256 5d65f750…), Theorem 1.3, p.2–3 (PDF pp.5–6), and Algorithm 9.1, p.66 (PDF p.69):
"Input: Known B, ∆, k, ε, δ, and sample access to (X, Y_max). Output: k vectors in ℝⁿ".

The input list, in memory from cell `0`: `k, ε, δ, B, ∆`. The machine dimension is `n + 1` (one
observation `(X, Y_max)` per `sample`), held in pointer `0` by `GaussMixHH.initState`.

**Formalization Note.** The page fixes no input format; this one is a convention. -/
noncomputable def goalInput (k : ℕ) (ε δ B Δ : ℝ) : List ℝ := [(k : ℝ), ε, δ, B, Δ]

/-- The output of a halted state: `k` vectors of `ℝⁿ`, coordinate `j` of `ŵ_i` (`i < k`, `j < n`)
being memory cell `p[1] + i·n + j`. Every halted state decodes to exactly `k` vectors.

**Formalization Note.** The page fixes no output format; this one is a convention. -/
noncomputable def decodeOutput (n k : ℕ) (s : GaussMixHH.State) :
    Fin k → EuclideanSpace ℝ (Fin n) :=
  fun i => WithLp.toLp 2 fun j : Fin n =>
    s.core.mem (s.core.ptrs 1 + (i : ℤ) * (n : ℤ) + (j : ℤ))

/-- The resource bound `C · (nk/ε)^{C·(B/∆)^C} · log(1/δ)`, the reading of
`Õ((nk/ε)^{poly(B/∆)} log(1/δ))` (Theorem 1.3, p.3) with one constant `C`. Natural logarithm;
`Real.rpow` for the outer power.

**Formalization Note.** `Õ` suppresses logarithmic factors in `n`, `k`, `1/ε` (Proposition G.1, p.94);
they are absorbed by the exponent since `nk/ε ≥ 4`. No factor `log log(1/δ)` is admitted. -/
noncomputable def resourceBound (C n k : ℕ) (ε δ B Δ : ℝ) : ℝ :=
  (C : ℝ) * ((n : ℝ) * k / ε) ^ ((C : ℝ) * (B / Δ) ^ C) * Real.log (1 / δ)

end SelfSelReg


