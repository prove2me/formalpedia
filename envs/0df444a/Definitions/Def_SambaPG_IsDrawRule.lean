-- Prove2me | Definitions.Def_SambaPG_IsDrawRule
-- name    : SambaPG_IsDrawRule
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:37:01.438871+00:00
-- url     : https://prove2.me/theorems/ad6a757a-d0ac-4d9d-b79b-61ce5b6ff9dc
-- title:
--   Drawing an arm with distribution $p$ from a uniform variable
-- statement:
--   A **draw rule** is a map $(p,u)\mapsto \mathrm{draw}(p,u)\in\mathcal A$ from a probability vector and a number $u\in[0,1]$ to an arm such that
--
--   1. for each arm $a$, the set $\{(p,u):\mathrm{draw}(p,u)=a\}$ is measurable;
--   2. for every probability vector $p$ (entries $\ge0$ summing to $1$) and every arm $a$, the Lebesgue measure of $\{u\in[0,1]:\mathrm{draw}(p,u)=a\}$ equals $p_a$.
--
--   So, for $U$ uniform on $[0,1]$, $\mathrm{draw}(p,U)$ is an arm with distribution $p$. This is how SAMBA plays an arm "with distribution $(p_a:a=1,\dots,N)$".
--
--   **Formalization Note** Any such rule is allowed; the inverse distribution function along an enumeration of the arms is one example.
-- source:
--   Denisov & Walton, Regret Analysis of a Markov Policy Gradient Algorithm for Multi-arm Bandits, arXiv:2007.10229v3, algorithm box, p.4; §3.2, p.7

import Mathlib

open MeasureTheory

namespace SambaPG

/-- **Drawing an arm with distribution `p` from a uniform variable.**
Denisov & Walton, arXiv:2007.10229v3, algorithm box, p.4 ("`a ←` choose with distribution
`(p_a : a = 1, …, N)`"), and §3.2, p.7.

`draw p u` is the arm played when the probability vector is `p` and the uniform randomization is
`u`. The rule is jointly measurable, and for every probability vector `p` (entries `≥ 0`, sum `1`)
a uniform `u ∈ [0, 1]` selects arm `a` with probability exactly `p_a`.

**Formalization Note.** Any such rule is allowed. The inverse-CDF rule along an enumeration of the
arms is one instance; every instance gives the same law of the SAMBA process. -/
def IsDrawRule {A : Type*} [Fintype A] (draw : (A → ℝ) → ℝ → A) : Prop :=
  (∀ a, MeasurableSet {x : (A → ℝ) × ℝ | draw x.1 x.2 = a}) ∧
    ∀ p ∈ stdSimplex ℝ A, ∀ a,
      volume {u ∈ Set.Icc (0 : ℝ) 1 | draw p u = a} = ENNReal.ofReal (p a)

end SambaPG


