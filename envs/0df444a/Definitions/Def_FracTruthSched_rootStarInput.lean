-- Prove2me | Definitions.Def_FracTruthSched_rootStarInput
-- name    : FracTruthSched_rootStarInput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:31:02.975625+00:00
-- url     : https://prove2.me/theorems/78248c2b-1c21-44c8-ad03-676de1f01c26
-- title:
--   Graph input of Lemma 5: root values $a$, opposing values $\lambda$, all else $0$
-- statement:
--   For a root $i$, a common opposing value $\lambda$ and root values $a$, this graph input gives, on every edge incident to $i$, the root value $a_e$ and the other endpoint value $\lambda$; every edge not incident to $i$ has value zero at both endpoints, and every self-loop has owner value zero (the root's own included). The root's disutility at this input, as a function of $a$, is the function $V$ of Lemma 5.
--
--   **Formalization Note.** The values of $a$ off the edges incident to $i$ are ignored.
-- source:
--   Anastasiadis et al., Tight bounds for fractional and randomized truthful scheduling, arXiv:2611.06642v1, Lemma 5 and its proof, p.17

import Mathlib
import Definitions.Def_FracTruthSched_incident

set_option autoImplicit false

namespace FracTruthSched

/-- The **graph input of Lemma 5** with root `i`, root values `a` and common opposing value `lam`
(Anastasiadis et al., arXiv:2611.06642v1, Lemma 5, p.17, and its proof: "Give every core edge not
incident to i value zero at both endpoints, and every self-loop owner value zero … every opposing
endpoint value in these classes equals λ … Its self-loop value remains zero"): on every edge `e`
incident to `i`, the root has value `a e` and the other endpoint value `lam`; every other entry,
including every self-loop value (the root's own included), is `0`.

**Formalization Note.** The values of `a` off the edges incident to `i` are ignored. For `a ≥ 0`
and `lam ≥ 0` this is a graph input. -/
def rootStarInput {n ℓ : ℕ} (i : Fin n) (lam : ℝ) (a : CoreTask n ℓ → ℝ) :
    Fin n → CoreTask n ℓ → ℝ :=
  fun u e => if e.isLeft ∧ incident i e ∧ incident u e then (if u = i then a e else lam) else 0

end FracTruthSched


