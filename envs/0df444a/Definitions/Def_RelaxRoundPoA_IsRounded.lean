-- Prove2me | Definitions.Def_RelaxRoundPoA_IsRounded
-- name    : RelaxRoundPoA_IsRounded
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:49:57.233798+00:00
-- url     : https://prove2.me/theorems/5cee658e-15cb-42d5-99ba-b5e661a8fb47
-- title:
--   Mechanism obtained from a relaxation by rounding
-- statement:
--   A mechanism $M$ for the original problem is **obtained from the relaxed mechanism $M'$ through the rounding scheme $R$** if on every profile $b$ drawn from the weight classes, the outcome of $M$ is produced by first drawing the relaxed outcome $x'$ of $M'$ and then drawing $x\sim R(x')$:
--
--   $$
--   \mathrm{law}_M(b)=\int R(x')\,\mathrm d\,\mathrm{law}_{M'}(b)(x').
--   $$
--
--   Payments are not constrained here; a pay-your-bid $M$ charges $b_i(x)$ on the rounded outcome $x$.
-- source:
--   Dütting, Kesselheim, Tardos, Algorithms as Mechanisms: The Price of Anarchy of Relax-and-Round, arXiv:1511.09208v1, §3, p.8

import Mathlib
import Definitions.Def_RelaxRoundPoA_Mechanism
import Definitions.Def_RelaxRoundPoA_IsProfile

open MeasureTheory ProbabilityTheory NNReal

namespace RelaxRoundPoA

/-- **Mechanism obtained from a relaxation by rounding.**
Dütting, Kesselheim, Tardos, arXiv:1511.09208v1, §3, p.8: "First, one computes an optimal solution
`x'` to a relaxed problem `Π'` ... Afterwards, an α-approximate oblivious rounding scheme is applied
to derive a feasible solution `x` to the original problem `Π`."

`IsRounded Val M' R M` says that on every profile `b` drawn from `Val`, the outcome law of `M` is the
outcome law of `M'` followed by the rounding kernel `R`: `M.outcome b = (M'.outcome b).bind R`.

**Formalization Note** Payments are not constrained here; a pay-your-bid `M` (`IsPayYourBid`)
charges each bidder `b_i(x)` on the *rounded* outcome `x`, as on p.8. -/
def IsRounded {N : Type*} {Ω' : Type*} [MeasurableSpace Ω'] (Val : N → Set (Ω' → ℝ≥0))
    (M' : Mechanism N Ω') (R : Kernel Ω' Ω') (M : Mechanism N Ω') : Prop :=
  ∀ b, IsProfile Val b → M.outcome b = (M'.outcome b).bind R

end RelaxRoundPoA


