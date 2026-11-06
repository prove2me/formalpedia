-- Prove2me | Definitions.Def_UnivAccel_lookRun
-- name    : UnivAccel_lookRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:19:58.065036+00:00
-- url     : https://prove2.me/theorems/aad6ea37-2010-43a0-8d7b-08f03bcdbcef
-- title:
--   The lookahead method (44) restarted as in §5.4, indexed by ball queries
-- statement:
--   The **restarted lookahead method** takes the function $f$ (through gradients at oracle answers), the ball oracle $O$, the distance bound $R$, the radius $r$, the gap bound $\Delta$, the accuracy $\varepsilon$ and the start $x_0$. Phase $k$ uses $\mu_k = (\Delta/2^k)/R^2$ and runs one phase (`laPhaseStep`) on $\tilde f_k = f + \frac{\mu_k}{2}\|\cdot - a_k\|^2$ from its anchor $a_k$ ($a_0 = x_0$); when a query of phase $k$ returns the minimizer $z_k$ of $\tilde f_k$, phase $k+1$ starts at $a_{k+1} = z_k$ with zero velocity. After $K = \lceil\log_2(\Delta/\varepsilon)\rceil$ phases the method has **halted**, with output the anchor $a_K$.
--
--   `lookRun … t` is the state after $t$ ball queries: every step of the iteration (`lookStep`) is exactly one ball query, including the one that ends a phase, and a halted state is fixed.
--
--   **Formalization Note** The method never receives the minimizer $x^*$ or the value $f(x^*)$; halting is decided by its own phase counter.
-- source:
--   Adil, Kyng, Universal Acceleration: New Approaches to Heavy Ball Discretization, STOC 2027 submission (manuscript sha256 c7b64bc2…), Theorem 2, p.5; §5.3–5.4, pp.23–25

import Mathlib
import Definitions.Def_UnivAccel_phaseMu
import Definitions.Def_UnivAccel_laPhaseStep

namespace UnivAccel

/-- The state of the restarted lookahead method: the phase index `k`, the phase anchor `a_k`
(the output once the method has halted), and the state of the current phase. -/
structure LookState (E : Type*) where
  /-- the phase index `k` -/
  phase : ℕ
  /-- the anchor `a_k` of phase `k` -/
  anchor : E
  /-- the state inside phase `k` -/
  st : LAState E

open Classical in
/-- One ball query of the lookahead method (44) restarted as in §5.4 (Adil–Kyng, *Universal
Acceleration: New Approaches to Heavy Ball Discretization*, STOC 2027 submission manuscript
(sha256 c7b64bc2…980250), §5.3–5.4, pp.23–25). Once the phase counter reaches `K` the method
has halted and the state is fixed. Otherwise phase `k` (parameter `μ_k = phaseMu Δ R k`, anchor
`a_k`) makes one query by `laPhaseStep`; when that query returns a point `z` with zero
regularized gradient, phase `k + 1` starts at `a_{k+1} = z` with zero velocity. -/
noncomputable def lookStep {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : E → ℝ) (O : ℝ → E → E → E) (R r Δ : ℝ) (K : ℕ)
    (s : LookState E) : LookState E :=
  if K ≤ s.phase then s else
    let st' := laPhaseStep f O (phaseMu Δ R s.phase) R r s.anchor s.st
    if st'.done then
      ⟨s.phase + 1, st'.x, laPhaseInit (phaseMu Δ R (s.phase + 1)) R r st'.x⟩
    else ⟨s.phase, s.anchor, st'⟩

/-- The state of the restarted lookahead method after `t` ball queries, started at `x0`
(Adil–Kyng, *Universal Acceleration: New Approaches to Heavy Ball Discretization*, STOC 2027
submission manuscript (sha256 c7b64bc2…980250), Theorem 2, p.5, and §5.3–5.4, pp.23–25). The
method's inputs are `f` (through its gradient at oracle answers), the oracle `O`, the distance
bound `R`, the radius `r`, the gap bound `Δ` and the accuracy `ε`; it runs
`K = numPhases Δ ε = ⌈log₂(Δ/ε)⌉` phases. It halts when `K ≤ phase`, with output the anchor.

**Formalization Note** The method never receives the minimizer `x*` or the value `f(x*)`. -/
noncomputable def lookRun {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : E → ℝ) (O : ℝ → E → E → E) (R r Δ ε : ℝ) (x0 : E) (t : ℕ) :
    LookState E :=
  (lookStep f O R r Δ (numPhases Δ ε))^[t] ⟨0, x0, laPhaseInit (phaseMu Δ R 0) R r x0⟩

end UnivAccel


