-- Prove2me | Definitions.Def_ParamSDPTraj_RightContLossOfUniqueness
-- name    : ParamSDPTraj_RightContLossOfUniqueness
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:15:18.305227+00:00
-- url     : https://prove2.me/theorems/a2d1060a-cb7e-41bc-8960-a933ee9008db
-- title:
--   Right-sided continuous loss of uniqueness
-- statement:
--   A time $s$ is a **right-sided continuous loss of uniqueness** of $F$ if there is $\eta>0$ such that $F$ is continuous at every $t\in(s-\eta,s+\eta)$, $F$ is single-valued at $s$, and $F$ is multi-valued at every $t\in(s,s+\eta)$.
--
--   This is Definition 3.10 of the paper without its left condition. It replaces "continuous bifurcation" in the second bullet of Definition 3.11. It is also how the paper itself uses that phrase in example $(P5_t)$ on p.23, where "each $t_k$ is a continuous bifurcation point" although the optimal set is multi-valued immediately to the left of $t_k$.
--
--   **Formalization Note** This is not a printed definition. It is the minimal correction that makes Theorem 3.15 true.
-- source:
--   Bellon, Henrion, Kungurtsev, Mareček, Parametric Semidefinite Programming: Geometry of the Trajectory of Solutions, arXiv:2104.05445v3, Definition 3.10, p.14, without its left condition; usage in example (P5t), p.23

import Mathlib
import Definitions.Def_ParamSDPTraj_SingleValuedAt
import Definitions.Def_ParamSDPTraj_PKContinuousAt
import Definitions.Def_ParamSDPTraj_MultiValuedAt

namespace ParamSDPTraj

/-- **Right-sided continuous loss of uniqueness (the corrected second bullet of Definition 3.11).**
A time s at which, for some η > 0, the map is continuous at every t ∈ (s − η, s + η), single-valued
at s and multi-valued at every t ∈ (s, s + η). This is Definition 3.10 of Bellon, Henrion, Kungurtsev, Mareček, *Parametric Semidefinite Programming: Geometry of the
Trajectory of Solutions*, arXiv:2104.05445v3, p.14, without
its left condition "single-valued for every t ∈ (t∗ − ε, t∗)".

It is how the paper itself uses "continuous bifurcation point" in example (P5t), p.23: there
"each tk is a continuous bifurcation point", although the optimal set is multi-valued immediately
to the left of tk, so tk does not satisfy Definition 3.10 as printed.

**Formalization Note** Not a printed definition: it is the minimal correction that makes
Theorem 3.15 true. See `IsIrregularAccumulationPoint`. -/
def RightContLossOfUniqueness {E : Type*} [TopologicalSpace E] (T : Set ℝ) (F : ℝ → Set E)
    (s : ℝ) : Prop :=
  ∃ η > 0, Set.Ioo (s - η) (s + η) ⊆ T ∧
    (∀ t ∈ Set.Ioo (s - η) (s + η), PKContinuousAt T F t) ∧
    SingleValuedAt F s ∧
    (∀ t ∈ Set.Ioo s (s + η), MultiValuedAt F t)

end ParamSDPTraj


