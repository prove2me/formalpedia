-- Prove2me | Definitions.Def_DelaunayStretch_IsFeasiblePotential
-- name    : DelaunayStretch_IsFeasiblePotential
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:53:09.127819+00:00
-- url     : https://prove2.me/theorems/2b8b9363-8191-4a19-b570-4bd769203478
-- title:
--   Feasible potentials of level $U$
-- statement:
--   Let $U\in\mathbb R$. A **feasible potential of level $U$** is a function $W$ from gate states to $\mathbb R$ such that, in the notation of the moves,
--
--   1. (I) $\mu_1-U\,(x(c_1)-x(u))\le -W(s_1)$ for every initial pair, where $s_1$ is the gate state it leads to;
--   2. (S) $\Delta\mu-U\,\Delta x\le W(s)-W(s')$ for every gate state $s$ and every next disk for $s$, where $s'$ is the gate state the step leads to;
--   3. (F) $\kappa-U\,(x(w_+(O))-x(c(s)))\le W(s)$ for every gate state $s=(O,G,\delta)$, where $\kappa$ is the cost of the final step at $s$.
--
--   Summing (I), (S) and (F) along a chain telescopes, so a feasible potential certifies the chain inequality (Theorem 3.9).
--
--   **Formalization Note** $W$ is defined on all records; only its values at gate states are constrained.
-- source:
--   Mo, Cheng, Ding, The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined, preprint (arXiv:2609.07979, version not stamped; held file of November 3, 2026, sha256 49ad9397…f824), Definition 3.7, p.19

import Mathlib
import Definitions.Def_DelaunayStretch_IsNextDisk

namespace DelaunayStretch

/-- **Feasible potential of level `U`** (Definition 3.7, p.19): a function `W` from gate states
to `ℝ` such that

* (I) `µ₁ − U(x(c₁) − x(u)) ≤ −W(s₁)` for every initial pair, where `s₁` is the gate state it
  leads to;
* (S) `Δµ − U Δx ≤ W(s) − W(s′)` for every gate state `s` and every next disk for `s`, where
  `s′` is the gate state the step leads to;
* (F) `κ − U(x(w₊(O)) − x(c(s))) ≤ W(s)` for every gate state `s = (O, G, δ)`, where `κ` is the
  cost of the final step at `s`.

Mo, Cheng, Ding, *The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined*,
preprint (arXiv:2609.07979, version not stamped; held file of November 3, 2026),
Definition 3.7, p.19.

**Formalization Note** `W` is a function on all of `GateState`; only its values at gate states
(`GateState.IsGateState`) enter, and every gate state reached by an initial pair or a step is
one. -/
def IsFeasiblePotential (U : ℝ) (W : GateState → ℝ) : Prop :=
  (∀ (O₁ O₂ : Disk) (a₁ b₁ : ℂ), IsInitialPair O₁ O₂ a₁ b₁ →
      initialCost O₁ a₁ b₁ - U * initialProgress O₁ a₁ b₁ ≤ -W (initialState O₁ O₂ a₁ b₁)) ∧
  (∀ s : GateState, s.IsGateState → ∀ (O' : Disk) (a' b' : ℂ), IsNextDisk s O' a' b' →
      stepCost s a' b' - U * stepProgress s a' b' ≤ W s - W (stepState s O' a' b')) ∧
  (∀ s : GateState, s.IsGateState → finalCost s - U * finalProgress s ≤ W s)

end DelaunayStretch


