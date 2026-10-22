-- Prove2me | Definitions.Def_StrategyproofMinimax_Circle_lrm
-- name    : StrategyproofMinimax_Circle_lrm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T20:42:29.906494+00:00
-- url     : https://prove2.me/theorems/63026fad-c1e7-4be7-83cf-9d9cfc31b1b0
-- title:
--   Agents on one semicircle, and the LRM mechanism on that semicircle
-- statement:
--   On the circle $G$ of circumference one, the agents of a profile $x\in G^n$ are **on one semicircle** if some closed arc of length $1/2$ contains every $x_i$; equivalently, there is a point $c$ with
--   $$d(x_i,c)\le \tfrac14\quad\text{for all } i\in N .$$
--   The arc is closed, so agents spread over exactly a half circle are on one semicircle.
--
--   On such an arc, identify each point $z$ with its signed coordinate $t_c(z)\in[-1/4,1/4]$ relative to the arc's midpoint $c$. The **left-right-middle (LRM) mechanism** run on this arc returns the leftmost agent $c+\min_i t_c(x_i)$ with probability $1/4$, the rightmost agent $c+\max_i t_c(x_i)$ with probability $1/4$, and the midpoint $c+\tfrac12(\min_i t_c(x_i)+\max_i t_c(x_i))$ between them with probability $1/2$. The outcome $\operatorname{lrm}(x)$ is this distribution for a covering semicircle.
--
--   Different covering semicircles give the same outcome, except when the agents occupy exactly one antipodal pair $\{p,\hat p\}$: then two closed semicircles cover them and their midpoints differ. The definition fixes the choice: $c = x_j - 1/4$ for the least index $j$ for which this $c$ covers all agents; such a $j$ exists whenever the agents are on one semicircle.
--
--   **Formalization Note.** `OnSemicircle x` is `∃ c, ∀ i, ‖x i - c‖ ≤ 1/4`. `offset c z` is the representative of $z-c$ in $[-1/2,1/2)$. `lrmAt c x` is $\tfrac14\delta_{\text{left}}+\tfrac14\delta_{\text{right}}+\tfrac12\delta_{\text{mid}}$ for the arc centred at `c`, and `lrm x = lrmAt (semicircleCenter x) x`. `semicircleCenter` returns the junk value $0$ when the agents are not on one semicircle (where `lrm` is never used in the paper's statements) and when $n=0$.
-- source:
--   Alon, Feldman, Procaccia, Tennenholtz, Strategyproof Approximation of the Minimax on Networks, Math. Oper. Res. 35(3) (2010), p. 516 (LRM mechanism), p. 517, Mechanism 3.1 (i), p. 519 (lrm(x))

import Mathlib

namespace StrategyproofMinimax.Circle

open MeasureTheory

/-- The agents are located on one semicircle (p. 517, Mechanism 3.1 (i)): some closed arc of
length `1/2` contains every location. Such an arc is `{z : ‖z - c‖ ≤ 1/4}` for its midpoint `c`,
so this is: some point `c` is within arc distance `1/4` of every agent. The arc is closed, so
agents spread over exactly a semicircle are on one semicircle. -/
def OnSemicircle {n : ℕ} (x : Fin n → AddCircle (1 : ℝ)) : Prop :=
  ∃ c : AddCircle (1 : ℝ), ∀ i, ‖x i - c‖ ≤ 1 / 4

/-- Signed position of `z` seen from `c`: the representative of `z - c` in `[-1/2, 1/2)`.
On an arc `{z : ‖z - c‖ ≤ 1/4}` it is the coordinate that identifies the arc with the interval
`[-1/4, 1/4] ⊂ ℝ`, with `c` at `0`. -/
noncomputable def offset (c z : AddCircle (1 : ℝ)) : ℝ :=
  (AddCircle.equivIco (1 : ℝ) (-1 / 2) (z - c) : ℝ)

/-- The LRM (left-right-middle) mechanism (p. 516) run on the arc of length `1/2` centred at `c`,
treated as an interval through `offset c`: with probability `1/4` the leftmost agent
`c + min_i offset c (xᵢ)`, with probability `1/4` the rightmost agent
`c + max_i offset c (xᵢ)`, and with probability `1/2` the midpoint `cen` between them. -/
noncomputable def lrmAt {n : ℕ} (c : AddCircle (1 : ℝ)) (x : Fin n → AddCircle (1 : ℝ)) :
    Measure (AddCircle (1 : ℝ)) :=
  let lo : ℝ := ⨅ i, offset c (x i)
  let hi : ℝ := ⨆ i, offset c (x i)
  (1 / 4 : ENNReal) • Measure.dirac (c + ((lo : ℝ) : AddCircle (1 : ℝ))) +
    (1 / 4 : ENNReal) • Measure.dirac (c + ((hi : ℝ) : AddCircle (1 : ℝ))) +
    (1 / 2 : ENNReal) • Measure.dirac (c + (((lo + hi) / 2 : ℝ) : AddCircle (1 : ℝ)))

/-- The centre of the semicircle on which LRM is run. When the agents are on one semicircle,
`x j - 1/4` is the centre of a covering closed semicircle for the agent `j` that is extreme in
the positive direction; we take the least index `j` for which `x j - 1/4` is such a centre.
Any covering semicircle gives the same LRM outcome (p. 517), except when the agents occupy
exactly one antipodal pair `{p, p̂}`; this rule then runs LRM on the semicircle centred at
`x j - 1/4` for the least such `j` (agent `0` in that case). Junk value `0` when no such `j`
exists (then the agents are not on one semicircle, or `n = 0`). -/
noncomputable def semicircleCenter {n : ℕ} (x : Fin n → AddCircle (1 : ℝ)) :
    AddCircle (1 : ℝ) := by
  classical
  exact if h : ∃ j, ∀ i, ‖x i - (x j - ((1 / 4 : ℝ) : AddCircle (1 : ℝ)))‖ ≤ 1 / 4 then
    x (Fin.find _ h) - ((1 / 4 : ℝ) : AddCircle (1 : ℝ))
  else 0

/-- `lrm(x)` (p. 519): the outcome of the LRM mechanism on the semicircle containing the agents,
treated as an interval (Mechanism 3.1 (i)). -/
noncomputable def lrm {n : ℕ} (x : Fin n → AddCircle (1 : ℝ)) : Measure (AddCircle (1 : ℝ)) :=
  lrmAt (semicircleCenter x) x

end StrategyproofMinimax.Circle


