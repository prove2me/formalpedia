-- Prove2me | Definitions.Def_HeilmanMax3Cut_bv
-- name    : HeilmanMax3Cut_bv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:27:25.919645+00:00
-- url     : https://prove2.me/theorems/9cfa01d8-25d4-4a3a-9b8d-b5da6f413ae1
-- title:
--   $b_v(t)=q\cos(\pi v)$
-- statement:
--   With $d=1-\sigma^2$ and $q=q_{\sigma,t}=\sigma\sqrt t/\sqrt d$,
--
--   $$b_v(t)=q\cos(\pi v),\qquad v\in[0,1],\ t\ge0.$$
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), Eqs. (115), (116), p.32

import Mathlib
open Real

namespace HeilmanMax3Cut

/-- **`b_v(t)`.** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), Eqs. (115), (116), p.32: with `d = 1 − σ²` and `q = q_{σ,t} := σ√t/√d`,
`b_v(t) := q cos(πv)` for `v ∈ [0, 1]`, `t ≥ 0`. -/
noncomputable def bv (σ v t : ℝ) : ℝ :=
  σ * Real.sqrt t / Real.sqrt (1 - σ ^ 2) * Real.cos (π * v)

end HeilmanMax3Cut


