-- Prove2me | Definitions.Def_StochAutoreg_classG
-- name    : StochAutoreg_classG
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:19:27.779728+00:00
-- url     : https://prove2.me/theorems/72ef238f-0765-44d1-a118-40318bec4d28
-- title:
--   The family $G_N$
-- statement:
--   The family $G_N$ has one generator $g_{\omega,\tau}$ for each $\omega\in\{-1,1\}^N$ and $\tau\in\{-1,1\}$: the completion of Lemma 6.1 of the rules of $G_N$, on a placement of the roots $r_1,\dots,r_N,v$.
-- source:
--   Doron-Arad–Mehalel–Mossel, Stochastic Autoregressive Learning, arXiv:2608.07224, §7, "The first family G_N", p.15

import Mathlib
import Definitions.Def_StochAutoreg_isolate
import Definitions.Def_StochAutoreg_gRule

namespace StochAutoreg

/-- The family `G_N`: one generator `g_{ω,τ}` for each `ω ∈ {-1,1}^N` and `τ ∈ {-1,1}`, on a placement of `r₁, …, r_N, v`.
Doron-Arad–Mehalel–Mossel, *Stochastic Autoregressive Learning*, arXiv:2608.07224, §7 "The first family `G_N`", p.15. -/
def classG (J M : ℕ) (ε tG : ℝ) {N : ℕ} (b : Fin N ⊕ Unit → List Bool) : Set Generator :=
  Set.range fun p : (Fin N → ℤˣ) × ℤˣ => isolate M b (gRule J M ε tG p.1 p.2)

end StochAutoreg


