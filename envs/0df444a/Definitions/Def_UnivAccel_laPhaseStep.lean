-- Prove2me | Definitions.Def_UnivAccel_laPhaseStep
-- name    : UnivAccel_laPhaseStep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:18:58.520981+00:00
-- url     : https://prove2.me/theorems/115b685a-7435-4ce3-ac46-b9c29aa5e0c1
-- title:
--   One phase of the restarted lookahead method (§5.4 blocks with (43)–(46))
-- statement:
--   A phase of the lookahead method restarted as in §5.4 runs the method (44) on $\tilde f = f + \frac{\mu}{2}\|\cdot - a\|^2$ from the anchor $a$ with zero velocity, that is $\bar x_0 = a$, $\bar w_0 = \sqrt\mu\, a$ (`laPhaseInit`), using the ball oracle $O(\mu, a, \cdot)$ for $\tilde f$. It runs in blocks $j = 0, 1, \dots$: block $j$ assumes the potential bound
--   $$
--   \mathcal H_j = 2^{-j}\cdot 2\mu R^2 \qquad (`blockBound`),
--   $$
--   uses the duration $h_j$ of (43) with $\mathcal H = \mathcal H_j$ (`blockStep`) and runs $N_j = \lceil 8\log 2/(3h_j\sqrt\mu)\rceil$ steps (46) (`blockLen`). Once $\mathcal H_j \le \mu r^2/2$ the blocks stop and the method keeps the duration $h_j$.
--
--   `laPhaseStep` makes **one ball query**: it predicts $x_p$, asks the oracle for $x_c = O(\mu, a, x_p)$ and reads $g = \nabla\tilde f(x_c) = \nabla f(x_c) + \mu(x_c - a)$. If $g = 0$ the phase is done at $x_c$ (the minimizer of $\tilde f$); otherwise it applies (44) and advances the block bookkeeping. A done state is fixed.
--
--   **Formalization Note** The state records the block index, the steps left in the block, $(\bar x, \bar w)$ in original coordinates and the done flag. After the last block the paper shows that the next query returns the minimizer; the method adds no other stopping rule.
-- source:
--   Adil, Kyng, Universal Acceleration: New Approaches to Heavy Ball Discretization, STOC 2027 submission (manuscript sha256 c7b64bc2…), §5.3 (43)–(46), p.23; §5.4 "One phase" and "Cost of a phase", pp.24–25

import Mathlib
import Definitions.Def_UnivAccel_regObj
import Definitions.Def_UnivAccel_laUpdate

namespace UnivAccel

/-- The state of one restart phase of the lookahead method: the current block `blk`, the number
`left` of steps still to run in that block, the iterate `(x̄, w̄)` (fields `x`, `w`) in original
coordinates, and a flag `done` raised when a ball query returned a point with zero regularized
gradient (then `x` holds that point). -/
structure LAState (E : Type*) where
  /-- the block index `j` -/
  blk : ℕ
  /-- the steps left in block `j` -/
  left : ℕ
  /-- the iterate `x̄` -/
  x : E
  /-- the iterate `w̄` -/
  w : E
  /-- a query returned `∇f̃(x_c) = 0` -/
  done : Bool

/-- The potential bound of block `j`, `𝓗_j = 2^{−j} · 2μR²` (Adil–Kyng, *Universal Acceleration:
New Approaches to Heavy Ball Discretization*, STOC 2027 submission manuscript (sha256
c7b64bc2…980250), §5.4 "Cost of a phase", p.24). -/
noncomputable def blockBound (μ R : ℝ) (j : ℕ) : ℝ :=
  (2 : ℝ)⁻¹ ^ j * (2 * μ * R ^ 2)

/-- The duration of block `j`: (43) with `𝓗 = 𝓗_j` (same source, p.24). -/
noncomputable def blockStep (μ R r : ℝ) (j : ℕ) : ℝ :=
  laStepSize μ r (blockBound μ R j)

/-- The number of steps of a block with duration `h`, `N = ⌈8 log 2 / (3h√μ)⌉` (46) (same source,
p.23). -/
noncomputable def blockLen (μ h : ℝ) : ℕ :=
  ⌈8 * Real.log 2 / (3 * h * Real.sqrt μ)⌉₊

/-- The start of a phase at the anchor `a`: block 0, zero velocity (`x̄ = a`, `w̄ = √μ a`, i.e.
`v = w̄ − √μ x̄ = 0`) (same source, §5.4 "One phase", p.24: "starting at a with zero velocity"). -/
noncomputable def laPhaseInit {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (μ R r : ℝ) (a : E) : LAState E :=
  ⟨0, blockLen μ (blockStep μ R r 0), a, Real.sqrt μ • a, false⟩

open Classical in
/-- One ball query of a phase of the lookahead method, restarted as in §5.4 (Adil–Kyng,
*Universal Acceleration: New Approaches to Heavy Ball Discretization*, STOC 2027 submission
manuscript (sha256 c7b64bc2…980250), (43)–(46), p.23, and §5.4, pp.24–25). The phase runs the
method (44) on `f̃ = f + μ/2 ‖· − a‖²` with the ball oracle `O μ a` for `f̃`:
`x_p = (x̄ + h w̄)/(1 + h√μ)`, `x_c = O μ a x_p`, `g = ∇f̃(x_c)`. If `g = 0` the phase is done at
`x_c` ("If a ball query returns ∇f(x_c) = 0, return x_c and stop"). Otherwise the update (44) is
applied, and the block bookkeeping advances: block `j` uses `h_j` from (43) with `𝓗 = 𝓗_j` and
runs `N_j` steps (46); once `𝓗_j ≤ μr²/2` ("We stop the blocks once 𝓗_j ≤ μr²/2") the method keeps
`h_j` for every further step. A done state is fixed.

**Formalization Note** The oracle answer's regularized gradient `∇f(x_c) + μ(x_c − a)` is part of
the query. After the last block the paper says the next query returns the minimizer; the method
keeps stepping with the last block's duration until a query returns a zero gradient, and adds no
other stopping rule. -/
noncomputable def laPhaseStep {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : E → ℝ) (O : ℝ → E → E → E) (μ R r : ℝ) (a : E)
    (s : LAState E) : LAState E :=
  if s.done then s else
    let h := blockStep μ R r s.blk
    let xc := O μ a (laPredict μ h s.x s.w)
    let g := regGrad f μ a xc
    if g = 0 then ⟨s.blk, s.left, xc, s.w, true⟩ else
      let p := laUpdate μ r h s.x s.w xc g
      if blockBound μ R s.blk ≤ μ * r ^ 2 / 2 then ⟨s.blk, s.left, p.1, p.2, false⟩
      else if s.left ≤ 1 then
        ⟨s.blk + 1, blockLen μ (blockStep μ R r (s.blk + 1)), p.1, p.2, false⟩
      else ⟨s.blk, s.left - 1, p.1, p.2, false⟩

end UnivAccel


