-- Prove2me | Definitions.Def_StochAutoreg_classH
-- name    : StochAutoreg_classH
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:19:33.039295+00:00
-- url     : https://prove2.me/theorems/cbd2bdc6-9194-435a-a434-dbcdf4c47e9c
-- title:
--   The family $H_D$
-- statement:
--   The family $H_D$ contains the inactive generator $h_0$ and the active generators $h_{b,s}$, $b\in\{0,1\}$, $s\in\{-1,1\}^D$: the completions of Lemma 6.1 of the rules of $H_D$, on a placement of the roots $x_0,\dots,x_D$.
-- source:
--   Doron-Arad–Mehalel–Mossel, Stochastic Autoregressive Learning, arXiv:2608.07224, §7, "The second family H_D", p.15

import Mathlib
import Definitions.Def_StochAutoreg_isolate
import Definitions.Def_StochAutoreg_hRuleOff
import Definitions.Def_StochAutoreg_hRuleOn

namespace StochAutoreg

/-- The family `H_D`: the inactive generator `h₀` and the active generators `h_{b,s}`, `b ∈ {0,1}`, `s ∈ {-1,1}^D`, on a
placement of the roots `x₀, …, x_D`. Doron-Arad–Mehalel–Mossel, *Stochastic Autoregressive Learning*, arXiv:2608.07224, §7 "The second family `H_D`", p.15. -/
def classH (J M : ℕ) (tH : ℝ) {D : ℕ} (b : Fin (D + 1) → List Bool) : Set Generator :=
  {isolate M b (hRuleOff D)} ∪
    Set.range fun p : Bool × (Fin D → ℤˣ) => isolate M b (hRuleOn J M tH p.1 p.2)

end StochAutoreg


