-- Prove2me | Definitions.Def_GrothendieckLB_Pfun
-- name    : GrothendieckLB_Pfun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:46:59.571721+00:00
-- url     : https://prove2.me/theorems/30eedf2b-3905-4765-a3c9-d8b57ed0fd17
-- title:
--   $2\Phi(\sqrt{-2\log x})-1$ with $r_0=\infty$
-- statement:
--   With $\Phi$ the standard normal distribution function and $r_x:=\sqrt{-2\log x}$ for $x\in(0,1]$, this is the bathtub value
--   $$
--   P(x)=\mathbb P(|S|\le r_x)=2\Phi(\sqrt{-2\log x})-1,
--   $$
--   with the convention $r_0=\infty$ of the proof of Theorem 8.5, so that $P(0)=1$.
--
--   **Formalization Note** The case $x=0$ is written out, because Lean's `Real.log 0 = 0` would otherwise give $r_0=0$ and the value $0$. Here $\Phi$ is `cdf (gaussianReal 0 1)`.
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Theorem 8.5 and its proof, p.38

import Mathlib
open MeasureTheory ProbabilityTheory

namespace GrothendieckLB

/-- The bathtub value `P(|S| ≤ r_x) = 2Φ(√(−2 log x)) − 1` with `r_x := √(−2 log x)` for `x ∈ (0, 1]`
and the convention `r₀ = ∞`, so the value at `x = 0` is `1` (Saha et al., *New Lower and Upper Bounds for the Grothendieck Constant*, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Theorem 8.5 and its proof, p.38).

**Formalization Note** `Real.log 0 = 0` in Lean would make `r₀ = 0` and the value `0`, so the case
`x = 0` is written out. `Φ` is `cdf (gaussianReal 0 1)`. -/
noncomputable def Pfun (x : ℝ) : ℝ :=
  if x = 0 then 1
  else 2 * cdf (gaussianReal 0 1) (Real.sqrt (-2 * Real.log x)) - 1

end GrothendieckLB


