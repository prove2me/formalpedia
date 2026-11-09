-- Prove2me | Definitions.Def_DelaunayStretch_IsNextDisk
-- name    : DelaunayStretch_IsNextDisk
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:51:45.720289+00:00
-- url     : https://prove2.me/theorems/c9170349-f263-4edb-86f8-6abca16d7f69
-- title:
--   Moves: initial pairs, next disks, steps and final steps
-- statement:
--   Let $O$ be a closed disk whose circle meets the $x$-axis in two points, and let $G=[a_G,b_G]$, $G'=[a',b']$ each be a chord of $\partial O$ with its upper end above and its lower end below the $x$-axis, or a point of $\partial O$ on the $x$-axis regarded as a chord of length $0$. Suppose $a_G$ does not come after $a'$ on the upper arc and $b_G$ does not come after $b'$ on the lower arc, and let $\alpha$, $\beta$ be the lengths of the parts of the upper arc from $a_G$ to $a'$ and of the lower arc from $b_G$ to $b'$. For $\delta\in[-|G|,|G|]$, the **move** on $O$ from $G$ to $G'$ with difference $\delta$ has
--
--   $$
--   \delta'=\mathrm{clip}_{|G'|}(\delta+\alpha-\beta),\qquad \Delta\mu=\tfrac12(\alpha+\beta-\omega),\qquad \Delta x=x(c')-x(c),
--   $$
--
--   where $\omega=(|\delta+\alpha-\beta|-|G'|)_+$ and $c$, $c'$ are the crossings of $G$, $G'$ with the $x$-axis.
--
--   1. An **initial pair** is a pair $(O_1,O_2)$ of closed disks whose circles meet in exactly two points $a_1,b_1$ with $y(a_1)>0>y(b_1)$, and $x(o_2)>x(o_1)$. It accounts for $O_1$ by the move from $u=w_-(O_1)$ to $G_1=[a_1,b_1]$ with difference $0$, with new difference $\delta_1$, cost $\mu_1$ and progress $x(c_1)-x(u)$, and leads to $s_1=(O_2,G_1,\delta_1)$.
--   2. A **next disk** for a gate state $s=(O,G,\delta)$ is a closed disk $O'$ with center $o'$ such that (N1) $\partial O$ and $\partial O'$ meet in exactly two points $a',b'$ with $y(a')>0>y(b')$; (N2) $x(o')>x(o)$; (N3) $x(c')>x(c(s))$ for the crossing $c'$ of $G'=[a',b']$; (N4) $a_G$ does not come after $a'$ on the upper arc of $O$ and $b_G$ does not come after $b'$ on the lower arc. The step from $s$ to $O'$ is the move on $O$ from $G$ to $G'$ with difference $\delta$; it leads to $s'=(O',G',\delta')$.
--   3. The **final step** at $s=(O,G,\delta)$ is the move on $O$ from $G$ to $w_+(O)$; its cost is $\kappa=\min(\tfrac12\delta+\alpha_{\mathrm{end}},-\tfrac12\delta+\beta_{\mathrm{end}})$ and its progress $x(w_+(O))-x(c(s))$, where $\alpha_{\mathrm{end}}$, $\beta_{\mathrm{end}}$ are the lengths of the parts of the upper and lower arcs from $a_G$ and $b_G$ to $w_+(O)$.
--
--   Every disk chain is a sequence of these moves (Lemma 3.6), so conditions on single moves control whole chains.
--
--   **Formalization Note** The ends $a',b'$ of a new gate are explicit arguments; (N1) (and, for initial pairs, the set equality $\partial O_1\cap\partial O_2=\{a_1,b_1\}$) determines them. Chords of length $0$ are a point repeated. The final cost is the formula (3.8), which equals the general move cost with $|G'|=0$.
-- source:
--   Mo, Cheng, Ding, The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined, preprint (arXiv:2609.07979, version not stamped; held file of November 3, 2026, sha256 49ad9397…f824), Definition 3.5, pp.17–18

import Mathlib
import Definitions.Def_DelaunayStretch_GateState

namespace DelaunayStretch

/-! Moves (Definition 3.5, pp.17–18). -/

/-- The new difference `δ′ = clip_{|G′|}(δ + α − β)` of the **move** on `O` from
`G = [aG, bG]` to `G′ = [a′, b′]` with difference `δ` (Definition 3.5, equation (3.7), p.17),
where `α` is the length of the part of the upper arc of `O` from `aG` to `a′` and `β` the length
of the part of the lower arc from `bG` to `b′`. A chord of length `0` is a point of `∂O` on the
`x`-axis, given as `a = b`. -/
noncomputable def moveNewDiff (O : Disk) (aG bG a' b' : ℂ) (δ : ℝ) : ℝ :=
  clip (dist a' b') (δ + O.upperArcLength aG a' - O.lowerArcLength bG b')

/-- The cost `Δμ = ½(α + β − ω)`, `ω = (|δ + α − β| − |G′|)₊`, of the move on `O` from `G` to
`G′` with difference `δ` (Definition 3.5, equation (3.7), p.17). -/
noncomputable def moveCost (O : Disk) (aG bG a' b' : ℂ) (δ : ℝ) : ℝ :=
  (O.upperArcLength aG a' + O.lowerArcLength bG b' -
      max (|δ + O.upperArcLength aG a' - O.lowerArcLength bG b'| - dist a' b') 0) / 2

/-- The progress `Δx = x(c′) − x(c)` of the move from `G` to `G′`, where `c`, `c′` are the
points where the `x`-axis crosses `G`, `G′` (Definition 3.5, equation (3.7), p.17). -/
noncomputable def moveProgress (aG bG a' b' : ℂ) : ℝ :=
  (axisCrossing a' b').re - (axisCrossing aG bG).re

/-- **Initial pair** (Definition 3.5(1), p.18): closed disks `O₁, O₂` with centers `o₁, o₂` such
that `∂O₁` and `∂O₂` meet in exactly the two points `a₁, b₁`, `y(a₁) > 0 > y(b₁)`, and
`x(o₂) > x(o₁)`. -/
def IsInitialPair (O₁ O₂ : Disk) (a₁ b₁ : ℂ) : Prop :=
  O₁.boundary ∩ O₂.boundary = {a₁, b₁} ∧ 0 < a₁.im ∧ b₁.im < 0 ∧ O₁.center.re < O₂.center.re

/-- `δ₁`: the new difference of the move on `O₁` from `u = w₋(O₁)` to `G₁ = [a₁, b₁]` with
difference `0`, by which an initial pair accounts for `O₁` (Definition 3.5(1), p.18). -/
noncomputable def initialDiff (O₁ : Disk) (a₁ b₁ : ℂ) : ℝ :=
  moveNewDiff O₁ O₁.wMinus O₁.wMinus a₁ b₁ 0

/-- `µ₁`: the cost of the move of an initial pair (Definition 3.5(1), p.18). -/
noncomputable def initialCost (O₁ : Disk) (a₁ b₁ : ℂ) : ℝ :=
  moveCost O₁ O₁.wMinus O₁.wMinus a₁ b₁ 0

/-- The progress `x(c₁) − x(u)` of an initial pair, `u = w₋(O₁)` (Definition 3.5(1), p.18). -/
noncomputable def initialProgress (O₁ : Disk) (a₁ b₁ : ℂ) : ℝ :=
  (axisCrossing a₁ b₁).re - O₁.wMinus.re

/-- The gate state `s₁ = (O₂, G₁, δ₁)` to which an initial pair leads (Definition 3.5(1),
p.18). -/
noncomputable def initialState (O₁ O₂ : Disk) (a₁ b₁ : ℂ) : GateState :=
  ⟨O₂, a₁, b₁, initialDiff O₁ a₁ b₁⟩

/-- **Next disk** (Definition 3.5(2), p.18). A closed disk `O′` with center `o′` is a next disk
for the gate state `s = (O, G, δ)`, with new gate `G′ = [a′, b′]`, if

* (N1) `∂O` and `∂O′` meet in exactly the two points `a′, b′`, with `y(a′) > 0 > y(b′)`;
* (N2) `x(o′) > x(o)`;
* (N3) the point `c′` where the `x`-axis crosses `G′` satisfies `x(c′) > x(c(s))`;
* (N4) on the upper arc of `O`, `aG` does not come after `a′`, and on the lower arc of `O`,
  `bG` does not come after `b′`.

Mo, Cheng, Ding, *The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined*,
preprint (arXiv:2609.07979, version not stamped; held file of November 3, 2026),
Definition 3.5, pp.17–18.

**Formalization Note** The ends `a′, b′` of the new gate are arguments; (N1) determines them
from `O` and `O′`. Arc order and arc lengths use the angle parameters of `Disk`; the moves of
an initial pair and of a final step start or end at the chord of length `0` given by the point
`w₋(O₁)` or `w₊(O)` repeated. -/
def IsNextDisk (s : GateState) (O' : Disk) (a' b' : ℂ) : Prop :=
  s.O.boundary ∩ O'.boundary = {a', b'} ∧ 0 < a'.im ∧ b'.im < 0 ∧
    s.O.center.re < O'.center.re ∧
    s.crossing.re < (axisCrossing a' b').re ∧
    s.O.UpperNotAfter s.aG a' ∧ s.O.LowerNotAfter s.bG b'

/-- The new difference `δ′` of the step from `s` to a next disk with new gate `[a′, b′]`: the
move on `O` from `G` to `G′` with difference `δ` (Definition 3.5(2), p.18). -/
noncomputable def stepDiff (s : GateState) (a' b' : ℂ) : ℝ :=
  moveNewDiff s.O s.aG s.bG a' b' s.δ

/-- The cost `Δµ` of the step from `s` with new gate `[a′, b′]` (Definition 3.5(2), p.18). -/
noncomputable def stepCost (s : GateState) (a' b' : ℂ) : ℝ :=
  moveCost s.O s.aG s.bG a' b' s.δ

/-- The progress `Δx = x(c′) − x(c(s))` of the step from `s` (Definition 3.5(2), p.18). -/
noncomputable def stepProgress (s : GateState) (a' b' : ℂ) : ℝ :=
  (axisCrossing a' b').re - s.crossing.re

/-- The gate state `s′ = (O′, G′, δ′)` to which the step from `s` to `O′` leads
(Definition 3.5(2), p.18). -/
noncomputable def stepState (s : GateState) (O' : Disk) (a' b' : ℂ) : GateState :=
  ⟨O', a', b', stepDiff s a' b'⟩

/-- The cost `κ = min(½δ + α_end, −½δ + β_end)` of the **final step** at `s = (O, G, δ)`,
where `α_end`, `β_end` are the lengths of the parts of the upper arc of `O` from `aG` to `w₊(O)`
and of the lower arc from `bG` to `w₊(O)` (Definition 3.5(3), equation (3.8), p.18). -/
noncomputable def finalCost (s : GateState) : ℝ :=
  min (s.δ / 2 + s.O.upperArcLength s.aG s.O.wPlus) (-s.δ / 2 + s.O.lowerArcLength s.bG s.O.wPlus)

/-- The progress `x(w₊(O)) − x(c(s))` of the final step at `s` (Definition 3.5(3), p.18). -/
noncomputable def finalProgress (s : GateState) : ℝ := s.O.wPlus.re - s.crossing.re

end DelaunayStretch


