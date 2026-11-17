-- Prove2me | Definitions.Def_DelaunayStretch_Supplement_valueFunction
-- name    : DelaunayStretch_Supplement_valueFunction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T12:38:46.863643+00:00
-- url     : https://prove2.me/theorems/4943542b-1b42-47d0-a00d-57650d154986
-- title:
--   Continuations, payoff $J_U(\Gamma;s)$ and value function $W^*_U$ (Definition B.1)
-- statement:
--   Let $s$ be a gate state. A **continuation** from $s$ is a finite, possibly empty, sequence $\Gamma=(O^{(1)},\dots,O^{(m)})$, $m\ge0$, of closed disks for which there are gate states $s_0=s,s_1,\dots,s_m$ such that, for $1\le l\le m$, the disk $O^{(l)}$ is a next disk for $s_{l-1}$ and the step from $s_{l-1}$ to $O^{(l)}$ leads to $s_l$. The gate states $s_0,\dots,s_m$ are determined by $s$ and $\Gamma$.
--
--   For $U\in\mathbb R$, the **payoff** $J_U(\Gamma;s)$ is the sum of cost minus $U$ times progress over the $m$ steps of $\Gamma$ and the final step at $s_m$:
--
--   $$
--   J_U(\Gamma;s)=\sum_{l=1}^{m}\bigl(\Delta\mu_l-U\,\Delta x_l\bigr)+\kappa(s_m)-U\bigl(x(w_+(O_m))-x(c(s_m))\bigr),
--   $$
--
--   where $\Delta\mu_l,\Delta x_l$ are the cost and the progress of the $l$-th step, $\kappa(s_m)$ is the cost of the final step at $s_m=(O_m,G_m,\delta_m)$. The **value function of level $U$** is
--
--   $$
--   W^*_U(s)=\sup_{\Gamma}J_U(\Gamma;s)\in(-\infty,+\infty],
--   $$
--
--   the supremum over all continuations $\Gamma$ from $s$. The empty continuation shows that the supremum is over a nonempty set, so $W^*_U(s)>-\infty$.
--
--   $W^*_U(s)$ is the largest total that the remaining moves of a disk chain can contribute to $P(u,v)-U\|u-v\|$ once the chain has reached the gate state $s$; Theorem B.4 shows it is the smallest feasible potential.
--
--   **Formalization Note** A continuation is a list of triples $(O',a',b')$: each disk carries the ends of its new gate $G'=[a',b']$, because the published next-disk predicate takes them as arguments; condition (N1) determines them from the current disk and $O'$, so this is in bijection with the paper's lists of disks. Gate states are complex-coordinate gate states of the base mission. The value function takes values in the extended reals `EReal`, so $+\infty$ is representable; it is defined at every element of the gate-state structure but only meaningful at gate states.
-- source:
--   Mo, Cheng, Ding, The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined, preprint (arXiv:2609.07979, version not stamped; held file of November 3, 2026, sha256 49ad9397…f824), Definition B.1, p.53; Proposition 3.8, pp.19–20

import Mathlib
import Definitions.Def_DelaunayStretch_IsNextDisk

namespace DelaunayStretch.Supplement

/-- A **continuation** from the gate state `s` (Definition B.1, p.53): a finite, possibly empty,
sequence of steps, each to a next disk for the current gate state, the current gate state being
updated to the gate state the step leads to. An entry `(O′, a′, b′)` of the list is the disk `O′`
together with the ends `a′, b′` of its new gate `G′ = [a′, b′]`.

Mo, Cheng, Ding, *The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined*,
preprint (arXiv:2609.07979, version not stamped; held file of November 3, 2026),
Definition B.1, p.53.

**Formalization Note** The paper's continuation is the list of disks `(O⁽¹⁾, …, O⁽ᵐ⁾)`; here
each disk carries its new gate ends, because the published `IsNextDisk` takes them as arguments.
Condition (N1) (`∂O ∩ ∂O′ = {a′, b′}` with `y(a′) > 0 > y(b′)`) determines `a′, b′` from the
current disk and `O′`, so the two encodings are in bijection. The gate states `s₀ = s, s₁, …, sₘ`
of the continuation are `sₗ = stepState sₗ₋₁ O⁽ˡ⁾ a⁽ˡ⁾ b⁽ˡ⁾`. -/
def IsContinuation : GateState → List (Disk × ℂ × ℂ) → Prop
  | _, [] => True
  | s, (O', a', b') :: Γ => IsNextDisk s O' a' b' ∧ IsContinuation (stepState s O' a' b') Γ

/-- The **payoff** `J_U(Γ; s)` (Definition B.1, p.53): the sum of cost − `U` · progress over the
`m` steps of `Γ` from `s` and the final step at the last gate state `sₘ`. For the empty
continuation it is `κ − U (x(w₊(O)) − x(c(s)))`. Defined for every real `U`. -/
noncomputable def payoff (U : ℝ) : GateState → List (Disk × ℂ × ℂ) → ℝ
  | s, [] => finalCost s - U * finalProgress s
  | s, (O', a', b') :: Γ =>
      (stepCost s a' b' - U * stepProgress s a' b') + payoff U (stepState s O' a' b') Γ

/-- The **value function of level `U`** (Definition B.1, p.53; Proposition 3.8, pp.19–20):
`W*_U(s) = sup_Γ J_U(Γ; s) ∈ (−∞, +∞]`, the supremum over all continuations `Γ` from `s`.

**Formalization Note** The value lies in `EReal`, so that `W*_U(s) = +∞` is representable (it is
when the chain inequality fails); the empty continuation makes the supremum range over a nonempty
set, so the value is never `⊥`. The definition is meaningful at gate states
(`GateState.IsGateState`), as in the paper; it is a definition for every element of `GateState`
but nothing is claimed about other ones. -/
noncomputable def valueFunction (U : ℝ) (s : GateState) : EReal :=
  ⨆ Γ : {Γ : List (Disk × ℂ × ℂ) // IsContinuation s Γ}, ((payoff U s Γ.1 : ℝ) : EReal)

end DelaunayStretch.Supplement


