-- Prove2me | Definitions.Def_WhittFLT_TimeReversal_Supplement_StandardM1
-- name    : WhittFLT_TimeReversal_Supplement_StandardM1
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T06:39:57.907878+00:00
-- url     : https://prove2.me/theorems/0da1143c-5593-4f10-a6d9-9f4481fd586f
-- title:
--   Standard M₁ convergence on intervals with least point zero
-- statement:
--   For a real càdlàg path $x$ on $[0,b]$, the completed graph contains the line segment from $x(t-)$ to $x(t)$ at each time, with the standard convention $x(0-)=x(0)$. The graph order follows increasing time and, at a jump, increasing distance along that segment from the left limit. A parametric representation is a continuous, ordered, onto traversal of this graph. Convergence in $M_1$ means that representations can be chosen with both components uniformly arbitrarily close:
--
--   $$\|u_n-u\|_\infty\vee\|r_n-r\|_\infty\longrightarrow0.$$
--
--   For an interval $T$ with least point zero, convergence is tested on $[0,b]\subseteq T$ whenever $b>0$ is a continuity point of the limit or the right endpoint of $T$. This is the standard $M_1$ used in Theorem 6.3.
--
--   **Formalization Note** Origin values converge as well, explicitly covering $T=\{0\}$; on positive-length intervals this follows from the graph criterion. This is distinct from the published first-passage convention $M_1'$ with $x(0-)=0$. The published ChenWhitt93 compact graph and parametric-representation criterion is reused at left endpoint zero and scalar state space. Its compact criterion already has the standard origin convention; its open-half-line convergence definition is not used. All paths and the limit are required to be càdlàg.
-- source:
--   Whitt, Some Useful Functions for Functional Limit Theorems, Math. Oper. Res. 5(1) (1980), DOI 10.1287/moor.5.1.67, §6, pp. 80–81, Theorem 6.3

import Mathlib
import Definitions.Def_WhittFLT_Composition_SkorohodD
import Definitions.Def_ChenWhitt93_JumpDiffusion_M1

namespace WhittFLT.TimeReversal.Supplement
open Set Filter Topology
open WhittFLT.Composition

/-- Standard M₁ on any interval with least point 0. Reuse the published compact
completed-graph criterion at a=0, which has x(0−)=x(0). The open-half-line
ChenWhitt93 M1Tendsto is deliberately not used. Origin-value convergence also
handles T={0}; on a positive-length interval it follows from the graph criterion. -/
def StandardM1Tendsto (T : Set ℝ) (xs : ℕ → ℝ → ℝ) (x : ℝ → ℝ) : Prop :=
  (∀ n, IsCadlagOn T (xs n)) ∧ IsCadlagOn T x ∧
    Tendsto (fun n => xs n 0) atTop (𝓝 (x 0)) ∧
    ∀ b : ℝ, 0 < b → b ∈ T →
      (ContinuousWithinAt x T b ∨ IsGreatest T b) →
      ChenWhitt93.JumpDiffusion.M1TendstoOn 0 b xs x

end WhittFLT.TimeReversal.Supplement


