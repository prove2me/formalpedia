-- Prove2me | Definitions.Def_AnchoredEP_Supplement_newtonOuterStep
-- name    : AnchoredEP_Supplement_newtonOuterStep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:09:56.320657+00:00
-- url     : https://prove2.me/theorems/a253aaec-f869-4398-8489-a2a375690ab8
-- title:
--   One outer iteration of AEP Newton (Algorithm 1)
-- statement:
--   One outer iteration of the Anchored Extra-Proximal Newton method acts on the state $(z_k,v_k,A_k)$ as follows:
--
--   1. if $\|F(z_k)+v_k\|\le\varepsilon$, the method returns $z_k$ (with the certificate $v_k$);
--   2. otherwise, if the upper trial passes ($\varphi_k(\bar a_k)\le\sqrt2$), the method returns $z_{k+1}(\bar a_k)$ (with $v_{k+1}(\bar a_k)$);
--   3. otherwise, with the step $a_k$ accepted by the bisection, the next state is $\big(z_{k+1}(a_k),\,v_{k+1}(a_k),\,A_k+a_k\big)$.
--
--   A run that has returned stays returned.
-- source:
--   Jiang–Yoon, Anchored Extra-Proximal Methods: Optimal Higher-Order Methods for Monotone Inclusion Problems, arXiv:2609.30212, Algorithm 1, p.8; Subroutine 1, p.25

import Mathlib
import Definitions.Def_AnchoredEP_IterState
import Definitions.Def_AnchoredEP_RunState
import Definitions.Def_AnchoredEP_trialZ
import Definitions.Def_AnchoredEP_Supplement_newtonV
import Definitions.Def_AnchoredEP_Supplement_newtonAbar
import Definitions.Def_AnchoredEP_Supplement_newtonUpperPasses
import Definitions.Def_AnchoredEP_Supplement_newtonStepSize

namespace AnchoredEP.Supplement

open Classical in
/-- **One outer iteration of the AEP Newton method, Algorithm 1.** Jiang–Yoon, arXiv:2609.30212,
Algorithm 1, p.8, with Subroutine 1, p.25. From the state `(z_k, v_k, A_k)`:
1. if `‖F(z_k) + v_k‖ ≤ ε`, return `z_k` (with `v_k`) (lines 4–5);
2. otherwise, if the upper trial passes (`φ_k(ā_k) ≤ √2`), terminate and return
   `(z_{k+1}(ā_k), v_{k+1}(ā_k))` (Subroutine 1 lines 4–5);
3. otherwise, with the step `a_k` accepted by bisection, move to
   `(z_{k+1}(a_k), v_{k+1}(a_k), A_k + a_k)` (lines 7–10).
A returned state is left unchanged. -/
noncomputable def newtonOuterStep {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (L ε : ℝ)
    (sol : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (z0 : EuclideanSpace ℝ (Fin d)) : RunState d → RunState d
  | .returned z v => .returned z v
  | .running s =>
    if ‖F s.z + s.v‖ ≤ ε then .returned s.z s.v
    else if newtonUpperPasses F L ε sol z0 s then
      .returned (trialZ F sol z0 s (newtonAbar F L ε s)) (newtonV F sol z0 s (newtonAbar F L ε s))
    else
      .running ⟨trialZ F sol z0 s (newtonStepSize F L ε sol z0 s),
        newtonV F sol z0 s (newtonStepSize F L ε sol z0 s), s.A + newtonStepSize F L ε sol z0 s⟩

end AnchoredEP.Supplement


