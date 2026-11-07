-- Prove2me | Definitions.Def_GrothendieckLB_Delta
-- name    : GrothendieckLB_Delta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:46:38.994582+00:00
-- url     : https://prove2.me/theorems/5eda1e59-1041-4082-a540-81771fa436e6
-- title:
--   $\Delta(x)$
-- statement:
--   For $x\in[0,1]$,
--   $$
--   \Delta(x):=x+2(1+x)\log\frac{1+x}2 .
--   $$
--   By Lemma 8.1, $-\nu\Delta(x)$ is the largest possible cubic coefficient under a linear-mass constraint.
--
--   **Formalization Note** The definition is total, and on $[0,1]$ the logarithm's argument lies in $[1/2,1]$. Note that $\Delta(0)=2\log(1/2)<0$ and $\Delta(1)=1$.
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Section 8.3, p.34

import Mathlib

namespace GrothendieckLB

/-- `Δ(x) := x + 2(1 + x) log((1 + x)/2)` (Saha et al., *New Lower and Upper Bounds for the Grothendieck Constant*, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Section 8.3, p.34). All uses have `x ∈ [0, 1]`, where
`(1 + x)/2 ∈ [1/2, 1]` and the logarithm is the true one. -/
noncomputable def Delta (x : ℝ) : ℝ :=
  x + 2 * (1 + x) * Real.log ((1 + x) / 2)

end GrothendieckLB


