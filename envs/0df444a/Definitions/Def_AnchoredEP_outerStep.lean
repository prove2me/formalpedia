-- Prove2me | Definitions.Def_AnchoredEP_outerStep
-- name    : AnchoredEP_outerStep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:44:22.612656+00:00
-- url     : https://prove2.me/theorems/b1871055-ff88-49b9-83f4-7921274b857b
-- title:
--   One outer iteration of the AEP Tensor Method
-- statement:
--   From the state $(z_k,v_k,A_k)$, one outer iteration of Algorithm 3:
--
--   1. returns $z_k$ (with $v_k$) if $\|F(z_k)+v_k\|\le\varepsilon$;
--   2. otherwise returns $z_{k+1}(\bar a_k)$ (with $v_{k+1}(\bar a_k)$) if the upper trial passes;
--   3. otherwise, with the step $a_k$ found by bisection, moves to $\big(z_{k+1}(a_k),\,v_{k+1}(a_k),\,A_k+a_k\big)$.
--
--   A returned state stays unchanged.
-- source:
--   Jiang–Yoon, Anchored Extra-Proximal Methods: Optimal Higher-Order Methods for Monotone Inclusion Problems, arXiv:2609.30212, Algorithm 3, p.37, and Appendix G.2, p.38

import Mathlib
import Definitions.Def_AnchoredEP_IterState
import Definitions.Def_AnchoredEP_RunState
import Definitions.Def_AnchoredEP_abar
import Definitions.Def_AnchoredEP_trialZ
import Definitions.Def_AnchoredEP_trialV
import Definitions.Def_AnchoredEP_upperPasses
import Definitions.Def_AnchoredEP_stepSize

namespace AnchoredEP

open Classical in
/-- **One outer iteration of the AEP Tensor Method, Algorithm 3.** Jiang–Yoon, arXiv:2609.30212,
Algorithm 3, p.37, with the line search of Appendix G.2, p.38. From the state
`(z_k, v_k, A_k)`:
1. if `‖F(z_k) + v_k‖ ≤ ε`, return `z_k` (with `v_k`);
2. otherwise, if the upper trial passes (`ψ_k(ā_k) ≤ p!ρ`), return `z_{k+1}(ā_k)` (with
   `v_{k+1}(ā_k)`);
3. otherwise, with the step `a_k` selected by bisection, move to
   `(z_{k+1}(a_k), v_{k+1}(a_k), A_k + a_k)` (lines 8–10).
A returned state is left unchanged. -/
noncomputable def outerStep {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (p : ℕ) (L ε : ℝ)
    (sol : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (z0 : EuclideanSpace ℝ (Fin d)) : RunState d → RunState d
  | .returned z v => .returned z v
  | .running s =>
    if ‖F s.z + s.v‖ ≤ ε then .returned s.z s.v
    else if upperPasses F p L ε sol z0 s then
      .returned (trialZ F sol z0 s (abar F p L ε s)) (trialV F p L sol z0 s (abar F p L ε s))
    else
      .running ⟨trialZ F sol z0 s (stepSize F p L ε sol z0 s),
        trialV F p L sol z0 s (stepSize F p L ε sol z0 s), s.A + stepSize F p L ε sol z0 s⟩

end AnchoredEP


