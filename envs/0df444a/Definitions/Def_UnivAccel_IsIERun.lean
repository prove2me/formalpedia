-- Prove2me | Definitions.Def_UnivAccel_IsIERun
-- name    : UnivAccel_IsIERun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:19:01.739863+00:00
-- url     : https://prove2.me/theorems/8905fda8-33a2-4c19-ae19-61f174741428
-- title:
--   Runs of the rescaled implicit Euler method (§4.2) restarted as in §5.4
-- statement:
--   The **rescaled implicit Euler method** restarted as in §5.4 keeps a phase index $k$, an anchor $a_k$, a position $x$ and a velocity $v$. In phase $k$, with $\mu = \mu_k = (\Delta/2^k)/R^2$, $\tilde f = f + \frac\mu2\|\cdot - a_k\|^2$ and the ball oracle $O(\mu, a_k, \cdot)$ for $\tilde f$, write
--   $$
--   x_{1/2}(h) = x + \frac{h}{1 + 2h\sqrt\mu}\, v \quad (`ieHalf`), \qquad x + \frac{v}{2\sqrt\mu} \quad (`ieLimit`).
--   $$
--   One step (`IEStep`) makes one ball query and is one of:
--   1. a duration $h > 0$ whose answer $y = O(\mu, a_k, x_{1/2}(h))$ has $\nabla\tilde f(y) = 0$: the phase ends at $y$;
--   2. the query at the limit point $x + v/(2\sqrt\mu)$ returning $y$ with $\nabla\tilde f(y) = 0$: the phase ends at $y$;
--   3. a duration $h > 0$ whose answer $y$ has $\nabla\tilde f(y) \neq 0$ and solves (17), $h^2\|\nabla\tilde f(y)\| = r(1 + 2h\sqrt\mu)$: then $x_+ = y$ and $v_+ = v/(1 + 2h\sqrt\mu) + \sigma/h$ with $\sigma = y - x_{1/2}(h)$.
--
--   When a phase ends at $y$, phase $k + 1$ starts at $a_{k+1} = y$ with $v = 0$. A **run** started at $x_0$ (`IsIERun`) is a sequence of states $s_0, s_1, \dots$ with $s_0 = (0, x_0, x_0, 0)$ in which consecutive states are related by a step until the phase counter reaches $K = \lceil\log_2(\Delta/\varepsilon)\rceil$; from then on the method has halted, with output the anchor, and the state is fixed.
--
--   **Formalization Note** A step is a relation: every admissible duration may be chosen. The bisection search for $h$ is not modelled: Theorem 2's $\tilde O$ hides its cost, and the analysis of §4.2 "treated this search as exact and let N count the number of such calls" (p.14). The method never receives $x^*$ or $f(x^*)$.
-- source:
--   Adil, Kyng, Universal Acceleration: New Approaches to Heavy Ball Discretization, STOC 2027 submission (manuscript sha256 c7b64bc2…), §4.2, pp.12–14; §5.4, p.24; Theorem 2, p.5

import Mathlib
import Definitions.Def_UnivAccel_regObj
import Definitions.Def_UnivAccel_phaseMu

namespace UnivAccel

/-- The state of the restarted implicit-Euler method: phase index `k`, anchor `a_k` (the output
once halted), position `x` and velocity `v`. -/
structure IEState (E : Type*) where
  /-- the phase index `k` -/
  phase : ℕ
  /-- the anchor `a_k` -/
  anchor : E
  /-- the position `x` -/
  x : E
  /-- the velocity `v` -/
  v : E

/-- The free prediction of a ball-driven implicit-Euler step of duration `h`,
`x_{1/2}(h) = x + h/(1 + 2h√μ) v` (Adil–Kyng, *Universal Acceleration: New Approaches to Heavy
Ball Discretization*, STOC 2027 submission manuscript (sha256 c7b64bc2…980250), §4.2, pp.12–13). -/
noncomputable def ieHalf {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (μ h : ℝ) (x v : E) : E :=
  x + (h / (1 + 2 * h * Real.sqrt μ)) • v

/-- The limit `x + v/(2√μ)` of `x_{1/2}(h)` as `h → ∞`, where the method "call[s] the oracle once"
(same source, §4.2 "Computing h", p.14). -/
noncomputable def ieLimit {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (μ : ℝ) (x v : E) : E :=
  x + (1 / (2 * Real.sqrt μ)) • v

/-- One step of the rescaled implicit-Euler method (§4.2), restarted as in §5.4 (Adil–Kyng,
*Universal Acceleration: New Approaches to Heavy Ball Discretization*, STOC 2027 submission
manuscript (sha256 c7b64bc2…980250), pp.12–14 and p.24). In phase `k`, with `μ = μ_k`,
`f̃ = f + μ/2 ‖· − a_k‖²` and the ball oracle `O μ a_k` for `f̃`, one step makes one counted ball
query and is one of:
1. a duration `h > 0` whose answer `y = O μ a_k (x_{1/2}(h))` has `∇f̃(y) = 0`: the phase ends at
   `y` ("if any call returns the minimizer, we stop");
2. the query at the limit centre `x + v/(2√μ)` returning `y` with `∇f̃(y) = 0`: the phase ends;
3. a duration `h > 0` whose answer `y` has `∇f̃(y) ≠ 0` and solves (17),
   `h² ‖∇f̃(y)‖ = r(1 + 2h√μ)`; then `x₊ = y`, `v₊ = v/(1 + 2h√μ) + σ/h` with
   `σ = y − x_{1/2}(h)`.
When a phase ends at `y`, phase `k + 1` starts at `a_{k+1} = y` with zero velocity.

**Formalization Note** The step is a relation: any admissible duration may be chosen. The
bisection search for `h` is not modelled; Theorem 2's `Õ` hides its cost, and the paper's analysis
"treated this search as exact and let N count the number of such calls" (p.14). -/
def IEStep {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (O : ℝ → E → E → E) (R r Δ : ℝ) (s s' : IEState E) : Prop :=
  let μ := phaseMu Δ R s.phase
  (∃ h : ℝ, 0 < h ∧ regGrad f μ s.anchor (O μ s.anchor (ieHalf μ h s.x s.v)) = 0 ∧
      s' = ⟨s.phase + 1, O μ s.anchor (ieHalf μ h s.x s.v),
        O μ s.anchor (ieHalf μ h s.x s.v), 0⟩) ∨
  (regGrad f μ s.anchor (O μ s.anchor (ieLimit μ s.x s.v)) = 0 ∧
      s' = ⟨s.phase + 1, O μ s.anchor (ieLimit μ s.x s.v), O μ s.anchor (ieLimit μ s.x s.v), 0⟩) ∨
  (∃ h : ℝ, 0 < h ∧ regGrad f μ s.anchor (O μ s.anchor (ieHalf μ h s.x s.v)) ≠ 0 ∧
      h ^ 2 * ‖regGrad f μ s.anchor (O μ s.anchor (ieHalf μ h s.x s.v))‖
        = r * (1 + 2 * h * Real.sqrt μ) ∧
      s' = ⟨s.phase, s.anchor, O μ s.anchor (ieHalf μ h s.x s.v),
        (1 + 2 * h * Real.sqrt μ)⁻¹ • s.v
          + h⁻¹ • (O μ s.anchor (ieHalf μ h s.x s.v) - ieHalf μ h s.x s.v)⟩)

/-- A run of the rescaled implicit-Euler method restarted as in §5.4, started at `x0` (Adil–Kyng,
*Universal Acceleration: New Approaches to Heavy Ball Discretization*, STOC 2027 submission
manuscript (sha256 c7b64bc2…980250), Theorem 2, p.5; §4.2, pp.12–14; §5.4, p.24): `s t` is the
state after `t` steps (one counted ball query each). It starts in phase 0 at `x0` with zero
velocity; once the phase counter reaches `K = numPhases Δ ε = ⌈log₂(Δ/ε)⌉` the method has halted,
with output the anchor, and the state is fixed; before that, consecutive states are related by
`IEStep`.

**Formalization Note** The method receives `f` (gradients at oracle answers), `O`, `R`, `r`, `Δ`,
`ε` and `x0`, never `x*` or `f(x*)`. -/
def IsIERun {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (O : ℝ → E → E → E) (R r Δ ε : ℝ) (x0 : E) (s : ℕ → IEState E) : Prop :=
  s 0 = ⟨0, x0, x0, 0⟩ ∧
    ∀ t : ℕ, (numPhases Δ ε ≤ (s t).phase → s (t + 1) = s t) ∧
      (¬ numPhases Δ ε ≤ (s t).phase → IEStep f O R r Δ (s t) (s (t + 1)))

end UnivAccel


