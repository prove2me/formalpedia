-- Prove2me | Definitions.Def_RollingProbeQN_Convex_step
-- name    : RollingProbeQN_Convex_step
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:23:58.133187+00:00
-- url     : https://prove2.me/theorems/f0318af6-7a03-4c07-95ed-06f735746e71
-- title:
--   One step of the run of Algorithm 1 (with the return at a zero gradient)
-- statement:
--   One iteration of Algorithm 1 on its state: if the run has returned, nothing changes; if the cached oracle value at $x_k$ is $0$, Step 1 returns $x_k$ and the state is frozen; otherwise the state moves to $x_{k+1},z_{k+1},A_{k+1},M_k$, caches $G(x_{k+1})$ and records $\delta_k=\|y_k-x_k\|+\|r_k\|$.
--
--   **Formalization Note** The stopping rule of Step 5 (target accuracy $\varepsilon$) is not part of the step; the $\varepsilon$-run is the run stopped at its first return.
-- source:
--   Mokhtari, Patitucci, Improved Gradient Complexity for Quasi-Newton Proximal Extragradient Methods via Certified Curvature Reuse, arXiv:2610.40608, Algorithm 1, p. 9

import Mathlib
import Definitions.Def_RollingProbeQN_Convex_iterData__5c24ab

namespace RollingProbeQN.Convex

/-- **One iteration of Algorithm 1 (without the stopping rule of Step 5).**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, Algorithm 1, p. 9: "1. Refresh and certify. If `∇f(x_k) = 0`, return `x_k`. […] 4. Correct
the momentum. Evaluate `∇f(x_{k+1})` and set `z_{k+1} = z_k − a_k ∇f(x_{k+1})`."

If the run has returned, the state is unchanged. If the cached oracle answer at `x_k` is zero, Step 1
returns: `done` is set and nothing else changes. Otherwise the state moves to `x_{k+1}`, `z_{k+1}`,
`A_{k+1}`, `M_k`, the cached answer at `x_{k+1}`, and records `δ_k = ‖y_k − x_k‖ + ‖r_k‖`.

**Formalization Note.** Reading R2: the return of Step 1 freezes the state. The stopping rule of
Step 5 is not part of the step; the ε-run is the run stopped at its first return (`epsReturns`). -/
noncomputable def step {d χ : ℕ} (cfg : Config d χ)
    (G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (k : ℕ) (st : RunState d) :
    RunState d :=
  open Classical in
  if st.done then st
  else if st.gx = 0 then { st with done := true }
  else
    { x := (iterData cfg G k st).x', z := (iterData cfg G k st).z', A := (iterData cfg G k st).A',
      M := (iterData cfg G k st).M, gx := (iterData cfg G k st).gx',
      δ := Function.update st.δ k (‖(iterData cfg G k st).y - st.x‖ + ‖(iterData cfg G k st).r‖),
      done := false }

end RollingProbeQN.Convex


