-- Prove2me | Definitions.Def_PertComp_indicator
-- name    : PertComp_indicator
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:12:21.468865+00:00
-- url     : https://prove2.me/theorems/861ed053-19f5-42f9-9a7c-1e6272c66085
-- title:
--   Indicator function $\iota_C$
-- statement:
--   The **indicator function** of a set $C$ is $\iota_C(x)=0$ if $x\in C$ and $\iota_C(x)=+\infty$ otherwise. It appears in (2.8) as $\iota_{\overline{\operatorname{dom} f}}$.
-- source:
--   L. M. Briceño-Arias, P. L. Combettes, A Perturbation Framework for Convex Minimization and Monotone Inclusion Problems with Nonlinear Compositions, arXiv:2111.11421v4, §2, p.5

import Mathlib

namespace PertComp

open Classical in
/-- Briceño-Arias, Combettes, arXiv:2111.11421v4, §2, p.5: the *indicator function* `ι_C` of a
set `C`, equal to `0` on `C` and `+∞` off `C`. -/
noncomputable def indicator {V : Type*} (C : Set V) : V → EReal :=
  fun x => if x ∈ C then 0 else ⊤

end PertComp


