-- Prove2me | Definitions.Def_WildeQIT_HSW_classicalCapacity
-- name    : WildeQIT_HSW_classicalCapacity
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T19:14:35.215645+00:00
-- url     : https://prove2.me/theorems/6e34c36e-d2b8-4726-9d21-eb2bad56f6a9
-- title:
--   Classical capacity $C(\mathcal N)$ of a quantum channel
-- statement:
--   The classical capacity of a quantum channel $\mathcal N$ is
--
--   $$
--   C(\mathcal N) \equiv \sup\{C : C \text{ is an achievable rate of classical communication for } \mathcal N\}.
--   $$
--
--   The Holevo–Schumacher–Westmoreland theorem identifies it with the regularized Holevo information $\chi_{\mathrm{reg}}(\mathcal N) = \lim_{k\to\infty}\frac1k\chi(\mathcal N^{\otimes k})$.
--
--   **Formalization Note** The supremum is Lean's `sSup` on $\mathbb R$, which is $0$ for an empty set or a set unbounded above. The rate $0$ is achievable whenever the input space is nonempty, and the classical capacity theorem states boundedness of the set of achievable rates explicitly, so the junk value never enters a stated result.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §20.2.1, p. 562

import Mathlib
import Definitions.Def_WildeQIT_HSW_IsAchievableRate

namespace WildeQIT.HSW

/-- Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §20.2.1, p. 562:
"The classical capacity C(N) of N is equal to the supremum of all achievable rates for classical
communication."

**Formalization Note.** `sSup` of the set of achievable rates
(`WildeQIT.HSW.IsAchievableRate`). In Lean `sSup` of a set that is empty or unbounded above is
`0`; Theorem 20.3.1 (`WildeQIT.HSW.theorem_20_3_1`) therefore states boundedness of the set
explicitly, and the rate `0` is achievable whenever the input space is nonempty. -/
noncomputable def classicalCapacity {A B : Type} [Fintype A] [DecidableEq A] [Fintype B]
    [DecidableEq B] (N : WildeQIT.QChannel A B) : ℝ :=
  sSup {C : ℝ | IsAchievableRate N C}

end WildeQIT.HSW


