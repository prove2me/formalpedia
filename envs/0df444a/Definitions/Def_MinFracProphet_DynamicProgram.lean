-- Prove2me | Definitions.Def_MinFracProphet_DynamicProgram
-- name    : MinFracProphet_DynamicProgram
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:35:32.040377+00:00
-- url     : https://prove2.me/theorems/5cf08965-f37e-42bb-a835-2b65a802631c
-- title:
--   The dynamic program of Appendix B.1: cost-to-go $J_i$ (21), the recursion $b_i$, $\mathbb E[b_i]$ (24)–(25), and the long-shot instance
-- statement:
--   These are the objects of the lower-bound proof of Theorem 2 (Appendix B.1, pp.21–23).
--
--   Let the prices $C_1,\dots,C_n$ be independent, $C_i\sim D_i$, and let $p>1$.
--
--   1. **Cost-to-go functions** (21), p.21. With $s\in[0,1]$ the amount already bought and $c$ the realized price at stage $i$,
--   $$
--   J_n(s,c)=c(1-s)^p,\qquad J_i(s,c)=\min_{0\le x\le 1-s}\ c\,x^p+\mathbb E\bigl[J_{i+1}(s+x,C_{i+1})\bigr],\quad i<n.
--   $$
--   2. **The recursion of Lemma 8** (24)–(25), p.22. $b_n(c)=c$, and for $i<n$
--   $$
--   b_i(c)=\frac{c\,\mathbb E[b_{i+1}]}{\bigl(c^{1/(p-1)}+\mathbb E[b_{i+1}]^{1/(p-1)}\bigr)^{p-1}},
--   $$
--   where $\mathbb E[b_{i+1}]=\mathbb E[b_{i+1}(C_{i+1})]$.
--   3. **Long-shot instance** (p.23). For $0<\varepsilon<1$ and $u>\ell$: the in-house seller has price $1$, and every other seller has price $\ell$ with probability $1-\varepsilon$ and $u$ with probability $\varepsilon$.
--
--   Lemma 8 shows $J_i(s,c)=b_i(c)(1-s)^p$, and the long-shot instance forces every adaptive policy to buy (almost) everything in-house.
--
--   **Formalization Note** Stages are 0-based: Lean stage $i\in\{0,\dots,n-1\}$ is the paper's stage $i+1$, with law `ν ⟨i,_⟩`. `costToGo p ν i s c` is the cost-to-go, written with a real infimum over $y\in[0,1-s]$ and Bochner integrals; only states $s\in[0,1]$ and prices in the supports are meaningful. `dpBeta p ν i` is $\mathbb E[b_i]$ and `dpB p ν i c` is $b_i(c)$. The page prints the exponent of $\mathbb E[b_{i+1}]$ in (25) as `1/p−1`; the definition uses $1/(p-1)$, as the proof of Lemma 8 and (26) do (the literal exponent gives a false Lemma 8: with $n=2$, $p=2$, $C_1\equiv1$, $C_2\equiv4$ the optimal cost is $4/5$, the literal formula gives $8/3$). In (21) the page writes $c_n(1-s_n)$ and $c_i(x_i)$ for the cost functions $c_n(1-s_n)^p$ and $c_ix_i^p$.
-- source:
--   Qin, Vardi, Wierman, Minimization Fractional Prophet Inequalities for Sequential Procurement, author manuscript (INFORMS template, sha256 672fa87c…79125d3), Appendix B.1: (21)–(22), p.21; Lemma 8, (24)–(25), p.22 (exponent corrected); proof of Theorem 2 (lower bound), p.23

import Mathlib
import Definitions.Def_MinFracProphet_Model

open MeasureTheory

namespace MinFracProphet

/-! # The dynamic program and the long-shot instance

J. Qin, S. Vardi, A. Wierman, *Minimization Fractional Prophet Inequalities for Sequential
Procurement*, author manuscript (sha256 672fa87c…79125d3), Appendix B.1, pp.21–23: cost-to-go
functions (21), the recursion (24)–(25) of Lemma 8, and the long-shot instance of the proof of
Theorem 2 (lower bound), p.23.

**Formalization Note** Stages are 0-based: Lean stage `i ∈ {0, …, n-1}` is the paper's stage
`i+1`, with price law `ν ⟨i, _⟩`. The cost-to-go `costToGo p ν i s c` depends on the realized price
`c` of stage `i` and the state `s` (amount bought so far), as on p.21; `c_i(x_i)` in (21) is the
cost function `c_i x_i^p` (R9). The exponent in (25) is `1/(p-1)` (R10: the page prints
`1/p-1`, which is false). -/

/-- The cost-to-go functions (21), p.21 (0-based stages): at the last stage `n-1` the buyer must
take the rest, `J_{n-1}(s, c) = c (1-s)^p`; before it,
`J_i(s, c) = inf_{0 ≤ y ≤ 1-s} c y^p + E[J_{i+1}(s+y, C_{i+1})]` with `C_{i+1} ∼ ν_{i+1}`.
Only states `s ∈ [0,1]` are meaningful. -/
noncomputable def costToGo {n : ℕ} (p : ℝ) (ν : Fin n → Measure ℝ) (i : ℕ) (s c : ℝ) : ℝ :=
  if h : i + 1 < n then
    ⨅ y : Set.Icc (0 : ℝ) (1 - s),
      c * (y : ℝ) ^ p + ∫ c', costToGo p ν (i + 1) (s + y) c' ∂(ν ⟨i + 1, h⟩)
  else c * (1 - s) ^ p
termination_by n - i

/-- One step of the recursion (25), p.22, with the corrected exponent `1/(p-1)`:
`b(c) = c β / (c^{1/(p-1)} + β^{1/(p-1)})^{p-1}`, where `β = E[b_{i+1}]`. -/
noncomputable def bStep (p β c : ℝ) : ℝ :=
  c * β / (c ^ (1 / (p - 1)) + β ^ (1 / (p - 1))) ^ (p - 1)

/-- The means `β_i = E[b_i]` of Lemma 8, p.22 (0-based): `β_{n-1} = E[C_{n-1}]` ((24)), and for
`i + 1 < n`, `β_i = E[b(C_i)]` with `b` the step (25) at `β_{i+1}`. Zero past the horizon. -/
noncomputable def dpBeta {n : ℕ} (p : ℝ) (ν : Fin n → Measure ℝ) (i : ℕ) : ℝ :=
  if h : i + 1 < n then ∫ c, bStep p (dpBeta p ν (i + 1)) c ∂(ν ⟨i, by omega⟩)
  else if h' : i < n then ∫ c, c ∂(ν ⟨i, h'⟩) else 0
termination_by n - i

/-- The coefficients `b_i(c)` of Lemma 8, (24)–(25), p.22 (0-based, corrected exponent):
`b_{n-1}(c) = c`, and `b_i(c) = c β_{i+1} / (c^{1/(p-1)} + β_{i+1}^{1/(p-1)})^{p-1}` for `i + 1 < n`. -/
noncomputable def dpB {n : ℕ} (p : ℝ) (ν : Fin n → Measure ℝ) (i : ℕ) (c : ℝ) : ℝ :=
  if i + 1 < n then bStep p (dpBeta p ν (i + 1)) c else c

/-- The long-shot instance of the proof of Theorem 2 (lower bound), p.23: seller `0` (in-house)
has the point mass at `1`; every other seller's price is `ℓ` with probability `1-ε` and `u` with
probability `ε`. -/
noncomputable def longShot (n : ℕ) (ℓ u ε : ℝ) : Fin n → Measure ℝ :=
  fun i => if i.val = 0 then Measure.dirac 1
    else ENNReal.ofReal (1 - ε) • Measure.dirac ℓ + ENNReal.ofReal ε • Measure.dirac u

end MinFracProphet


