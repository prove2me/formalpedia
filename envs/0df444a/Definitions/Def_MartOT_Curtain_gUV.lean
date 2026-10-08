-- Prove2me | Definitions.Def_MartOT_Curtain_gUV
-- name    : MartOT_Curtain_gUV
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T00:19:28.77865+00:00
-- url     : https://prove2.me/theorems/4aa23e19-d7cc-451e-82bd-bdc6107303b1
-- title:
--   (13), p. 33 — the test functions g_{u,v}(x) = (v − x)·1_{[u,v]}(x)
-- statement:
--   For real numbers $u<v$ the function $g_{u,v}:\mathbb R\to\mathbb R$ is
--
--   $$g_{u,v}(x)=\begin{cases}v-x,&x\in[u,v],\\0,&\text{otherwise.}\end{cases}$$
--
--   It is a bounded Borel function supported on $[u,v]$, decreasing linearly from $v-u$ at $x=u$ to $0$ at $x=v$, and it agrees on $[u,+\infty[$ with the convex function $x\mapsto(v-x)^+$. Beiglböck and Juillet use these functions as test functions to detect a difference between two measures in the uniqueness proof of the left-curtain coupling (Lemma 5.2 and Theorem 5.3).
--
--   **Formalization Note** The function is defined for all real $u,v$; for $u>v$ it is identically $0$ and for $u=v$ it is $0$ everywhere. The paper only uses $u<v$, and every statement of the mission that uses it assumes $u<v$.
-- source:
--   arXiv:1208.1509v2, §5, display (13), p. 33

import Mathlib

namespace MartOT.Curtain

/-- **(13)** (p. 33): for `u < v`, `g_{u,v}(x) = v − x` if `x ∈ [u, v]` and `0` otherwise. -/
noncomputable def gUV (u v : ℝ) (x : ℝ) : ℝ :=
  if x ∈ Set.Icc u v then v - x else 0

end MartOT.Curtain


