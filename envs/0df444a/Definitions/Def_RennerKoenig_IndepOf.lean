-- Prove2me | Definitions.Def_RennerKoenig_IndepOf
-- name    : RennerKoenig_IndepOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:44:48.918477+00:00
-- url     : https://prove2.me/theorems/a1444410-b793-4d28-b9c9-396f0432d8b3
-- title:
--   Independence of two random variables
-- statement:
--   Two random variables $U,V$ on a discrete probability space are independent if
--
--   $$
--   \Pr[U\in A,\ V\in B]=\Pr[U\in A]\,\Pr[V\in B]
--   $$
--
--   for all subsets $A,B$ of their ranges.
--
--   **Formalization Note** On a discrete space every subset is an event, so no measurability enters. A random state is a random variable with values in operators, so the definition applies to it.
-- source:
--   Renner–König, Universally Composable Privacy Amplification Against Quantum Adversaries, arXiv:quant-ph/0403133v2, Theorem 4.1, p.8 and Lemmas 4.3, 4.7, pp.8, 10

import Mathlib
import Definitions.Def_RennerKoenig_prob

namespace RennerKoenig

/-- **Independence** of two random variables on a discrete probability space. Used in
Renner–König, *Universally Composable Privacy Amplification Against Quantum Adversaries*,
arXiv:quant-ph/0403133v2, Theorem 4.1 and Lemmas 4.3, 4.7, pp.8, 10.

**Formalization Note** On a discrete space every subset is an event, so the product rule is asked
of all pairs of subsets of the ranges. -/
def IndepOf {Ω A B : Type*} (P : PMF Ω) (U : Ω → A) (V : Ω → B) : Prop :=
  ∀ (s : Set A) (t : Set B),
    prob P {ω | U ω ∈ s ∧ V ω ∈ t} = prob P {ω | U ω ∈ s} * prob P {ω | V ω ∈ t}

end RennerKoenig


