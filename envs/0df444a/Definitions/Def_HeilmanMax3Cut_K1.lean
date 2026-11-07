-- Prove2me | Definitions.Def_HeilmanMax3Cut_K1
-- name    : HeilmanMax3Cut_K1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:26:57.679782+00:00
-- url     : https://prove2.me/theorems/0048e128-18fa-4e1b-84ec-0320ec56c7c0
-- title:
--   The first-mode kernel $K^{(1)}(p,q)$
-- statement:
--   For a function $r$ let $K_r(p,q)=\int_0^p\int_0^q\tfrac12[r(u-v)+r(u+v)]\,dv\,du$. With $r^{(1)}(u)=1-\cos(\pi u)$,
--
--   $$K^{(1)}(p,q)=K_{r^{(1)}}(p,q)=\int_0^p\!\!\int_0^q\frac{[1-\cos(\pi(u-v))]+[1-\cos(\pi(u+v))]}{2}\,dv\,du,$$
--
--   which the paper evaluates as $pq-\sin(\pi p)\sin(\pi q)/\pi^2$ (86).
--
--   **Formalization Note** The integral (82) is the definition; the closed form (86) is a consequence.
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), Eqs. (82), (85), (86), pp.26–27

import Mathlib
open Real

namespace HeilmanMax3Cut

/-- **The first-mode arc kernel `K^{(1)}`.** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), Eqs. (82), (85), (86), pp.26–27: for a function
`r`, `K_r(p, q) := ∫₀^p ∫₀^q ½[r(u − v) + r(u + v)] dv du`, and `K^{(1)} := K_{r^{(1)}}` with
`r^{(1)}(u) = 1 − cos(πu)`. The paper computes `K^{(1)}(p, q) = pq − sin(πp) sin(πq)/π²` (86).

**Formalization Note.** The definition is the integral (82) with `r = r^{(1)}` (interval
integrals); the closed form (86) is a consequence, not the definition. The paper uses
`p, q ∈ [0, 1]`; the formula is evaluated for all real `p, q`. -/
noncomputable def K1 (p q : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..p, ∫ v in (0 : ℝ)..q,
    ((1 - Real.cos (π * (u - v))) + (1 - Real.cos (π * (u + v)))) / 2

end HeilmanMax3Cut


