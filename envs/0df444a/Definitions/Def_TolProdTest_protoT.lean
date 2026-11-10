-- Prove2me | Definitions.Def_TolProdTest_protoT
-- name    : TolProdTest_protoT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T03:25:34.237219+00:00
-- url     : https://prove2.me/theorems/a3dde11b-0c96-4c00-8ca0-7e9ace22a3bc
-- title:
--   Parameters $c,\eta,q,R,k,p_Y,p_N,T$ of Protocol 3.1
-- statement:
--   For thresholds $1\ge a>b\ge0$ and $\delta\in(0,1/2)$, with $\Delta=a-b$:
--
--   $$
--   c=b+\tfrac{\Delta}{4},\quad \eta=\tfrac{\Delta}{4},\quad
--   q=\max\Big\{13,\Big\lceil\tfrac{3}{c^2-b^2}\Big\rceil\Big\},\quad
--   R=\Big\lceil\tfrac{4q}{\eta}\Big\rceil,\quad
--   k=\Big\lceil\tfrac{8qRc}{\eta}\log\tfrac{8eqc}{\eta}\Big\rceil,
--   $$
--
--   $$
--   p_Y=a^k,\qquad p_N=\Big(\tfrac{a+b}{2}\Big)^k,\qquad
--   T=\Big\lceil\frac{\min\{2,8p_Y\}}{(p_Y-p_N)^2}\log\frac4\delta\Big\rceil .
--   $$
--
--   $k$ is the number of copies per trial, $T$ the number of trials, and $(p_Y+p_N)/2$ the acceptance threshold of Protocol 3.1.
--
--   **Formalization Note** Ceilings are `Nat.ceil`; `log` is the natural logarithm (p.8). The definitions are total functions of $a,b,\delta$; every statement using them assumes the ranges above.
-- source:
--   Bao, Helsen, Nguyen, Fully tolerant product state testing and closest product state learning, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), eqs. (67)–(70), p.17

import Mathlib

set_option autoImplicit false

namespace TolProdTest

/-- `c := b + Δ/4`, `Δ = a − b`, Bao, Helsen, Nguyen, *Fully tolerant product state testing and closest product state learning*, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), eq. (67), p.17. -/
noncomputable def protoC (a b : ℝ) : ℝ := b + (a - b) / 4

/-- `η := Δ/4`, `Δ = a − b`, Bao, Helsen, Nguyen, *Fully tolerant product state testing and closest product state learning*, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), eq. (67), p.17. -/
noncomputable def protoEta (a b : ℝ) : ℝ := (a - b) / 4

/-- `q := max{13, ⌈3/(c² − b²)⌉}`, Bao, Helsen, Nguyen, *Fully tolerant product state testing and closest product state learning*, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), eq. (68), p.17. -/
noncomputable def protoQ (a b : ℝ) : ℕ := max 13 ⌈3 / (protoC a b ^ 2 - b ^ 2)⌉₊

/-- `R := ⌈4q/η⌉`, Bao, Helsen, Nguyen, *Fully tolerant product state testing and closest product state learning*, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), eq. (68), p.17. -/
noncomputable def protoR (a b : ℝ) : ℕ := ⌈4 * (protoQ a b : ℝ) / protoEta a b⌉₊

/-- `k := ⌈(8qRc/η) log(8eqc/η)⌉` (natural logarithm), Bao, Helsen, Nguyen, *Fully tolerant product state testing and closest product state learning*, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), eq. (68), p.17. -/
noncomputable def protoK (a b : ℝ) : ℕ :=
  ⌈8 * (protoQ a b : ℝ) * (protoR a b : ℝ) * protoC a b / protoEta a b *
      Real.log (8 * Real.exp 1 * (protoQ a b : ℝ) * protoC a b / protoEta a b)⌉₊

/-- `p_Y := a^k`, Bao, Helsen, Nguyen, *Fully tolerant product state testing and closest product state learning*, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), eq. (69), p.17. -/
noncomputable def protoPY (a b : ℝ) : ℝ := a ^ protoK a b

/-- `p_N := ((a + b)/2)^k`, Bao, Helsen, Nguyen, *Fully tolerant product state testing and closest product state learning*, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), eq. (69), p.17. -/
noncomputable def protoPN (a b : ℝ) : ℝ := ((a + b) / 2) ^ protoK a b

/-- **Parameters of Protocol 3.1**, Bao, Helsen, Nguyen, *Fully tolerant product state testing and closest product state learning*, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), "Choice of parameters", eqs. (67)–(70), p.17. This is
`T := ⌈(min{2, 8p_Y}/(p_Y − p_N)²) log(4/δ)⌉` (eq. (70)), the number of independent trials; the module also
defines `c, η` (67), `q, R, k` (68) and `p_Y, p_N` (69).

**Formalization Note** Ceilings are `Nat.ceil` of real numbers (all arguments are positive under the paper's
hypotheses `1 ≥ a > b ≥ 0`, `δ ∈ (0, 1/2)`); `log` is the natural logarithm (p.8). The definitions are total
functions of `a, b, δ`; every statement using them assumes the paper's ranges. -/
noncomputable def protoT (a b δ : ℝ) : ℕ :=
  ⌈min 2 (8 * protoPY a b) / (protoPY a b - protoPN a b) ^ 2 * Real.log (4 / δ)⌉₊

end TolProdTest


