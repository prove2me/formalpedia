-- Prove2me | Definitions.Def_VehShare_MultiNet_Ropt
-- name    : VehShare_MultiNet_Ropt
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:49:44.13636+00:00
-- url     : https://prove2.me/theorems/0ff136e3-53e3-4f5b-82b4-3ba404e71101
-- title:
--   Optimal dynamic reward $R(q^*)$
-- statement:
--   The **optimal dynamic reward** is
--
--   $$
--   R(q^*)=\sup\{R(q,\pi)\ :\ q\text{ a dynamic policy},\ \pi\text{ a stationary distribution of its chain}\},
--   $$
--
--   the value of "a policy $q^*=\operatorname{argmax}(R(q))$ that maximizes $R(q)$" (p. 5).
--
--   **Formalization Note** The supremum ranges over every policy and every stationary distribution, which makes $R(q^*)$ as large as possible. Lean's real supremum is $0$ on an empty or unbounded set; the set is nonempty (the zero policy with a point mass on a state where all vehicles are parked at one location, when there is a location) and bounded above by $R_s(q^s)$ (Proposition 1), so the value is the paper's wherever the theorems use it.
-- source:
--   Benjaafar, Shen, Pricing in On-Demand (and One-Way) Vehicle Sharing Networks, SSRN 3998297 (version of 2023-01-10), https://ssrn.com/abstract=3998297, p. 5

import Mathlib
import Definitions.Def_VehShare_MultiNet_IsStationary
import Definitions.Def_VehShare_MultiNet_reward

namespace VehShare.MultiNet

/-- **Optimal dynamic reward `R(q*)`.**
Benjaafar, Shen, *Pricing in On-Demand (and One-Way) Vehicle Sharing Networks*, SSRN 3998297
(version of 2023-01-10), p. 5: "Our aim is to identify a policy `q* = argmax(R(q))` that maximizes `R(q)`."

The supremum of `R(q, π)` over every dynamic policy `q` and every stationary distribution `π` of
its chain.

**Formalization Note.** Reading 2: the supremum ranges over every policy and every stationary
law, which makes `R(q*)` as large as possible (the stronger reading of the ratio bounds). The real
`sSup` is 0 on an empty or unbounded set; the set is nonempty (the policy `q ≡ 0` with a point mass
on a state where every vehicle is parked at one location, when there is a location) and bounded above by `R_s(q^s)` (Proposition 1), so the
value is the paper's on every instance where the theorems use it. -/
noncomputable def Ropt (P : Instance) (K : ℕ) : ℝ :=
  sSup {x | ∃ (q : Policy P K) (π : State P K → ℝ), IsStationary q π ∧ x = reward q π}

end VehShare.MultiNet


