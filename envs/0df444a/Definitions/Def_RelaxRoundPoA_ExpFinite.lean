-- Prove2me | Definitions.Def_RelaxRoundPoA_ExpFinite
-- name    : RelaxRoundPoA_ExpFinite
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:49:50.002801+00:00
-- url     : https://prove2.me/theorems/ded74b7e-8a39-4585-8228-d0a7376c3ed5
-- title:
--   Finite expected values of the weights
-- statement:
--   A mechanism $M$ has **finite expected values** on the weight classes if for every profile $b$ drawn from the classes, every agent $i$ and every $w\in\mathcal V_i$, the function $w$ is integrable under the outcome law of $M$ on $b$, i.e. $\mathbf E[w(f(b))]<\infty$.
--
--   The paper's expected utilities are only defined under this condition; it excludes nothing else.
-- source:
--   Dütting, Kesselheim, Tardos, Algorithms as Mechanisms: The Price of Anarchy of Relax-and-Round, arXiv:1511.09208v1, §2, p.7

import Mathlib
import Definitions.Def_RelaxRoundPoA_Mechanism
import Definitions.Def_RelaxRoundPoA_IsProfile

open MeasureTheory NNReal

namespace RelaxRoundPoA

/-- **Finite expected values.**
Dütting, Kesselheim, Tardos, arXiv:1511.09208v1, §2, p.7: the expected utility
`u_i(b, v_i) = E[v_i(f(b))] − E[p_i(b)]` is only defined when the expectations are finite.

`ExpFinite Val M` says: for every profile `b` drawn from `Val`, every agent `i` and every weight
`w ∈ Val i`, the function `w` is integrable under the outcome law of `M` on `b`.

**Formalization Note** This excludes only the cases in which the paper's expectations are
undefined; without it a Bochner integral of a non-integrable weight would silently be `0`. -/
def ExpFinite {N : Type*} {Ω' : Type*} [MeasurableSpace Ω'] (Val : N → Set (Ω' → ℝ≥0))
    (M : Mechanism N Ω') : Prop :=
  ∀ b, IsProfile Val b → ∀ i, ∀ w ∈ Val i, Integrable (fun x => (w x : ℝ)) (M.outcome b)

end RelaxRoundPoA


