-- Prove2me | Definitions.Def_DetTerminalEmbedding1373_Real_solver
-- name    : DetTerminalEmbedding1373_Real_solver
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:24:37.189768+00:00
-- url     : https://prove2.me/theorems/b627bb6b-c09c-4c02-a266-3e23f493faf5
-- title:
--   Finite correlation objective and projected subgradient iterates
-- statement:
--   For vectors $a_i\in E_m$ and real scalars $c_i$, put $f(w)=\max_i|\langle w,a_i\rangle-c_i|$. A left-to-right scan chooses the earliest maximizing index. The chosen subgradient is the signed active vector, or zero when its residual is zero. The explicit radial projection and the iterates are
--
--   $$P(v)=\frac v{\max\{1,\|v\|\}},\quad w_0=0,\quad w_{t+1}=P(w_t-(\eta/4)g_t),\quad T=\lceil4/\eta^2\rceil.$$
--
--   The returned value is the earliest minimum of $f(w_t)$ over $0\le t<T$. For a linear map $A$, nonzero vectors $x_i$ and a norm-bounded vector $u$, the correlation data are $a_i=A(x_i/\|x_i\|)$ and $c_i=\langle u,x_i/\|x_i\|\rangle$. These definitions have no feasibility, convergence or runtime guarantees as fields. The published general projection is imported for its mathematical reuse; the executable formula remains radial.
-- source:
--   Vladimir Braverman, Kuan Cheng, Jiaqing Zhu, STOC 2027 submission #1373 (October 2026), pp. 18–20, equations (33)–(37) and the earliest-best rule on p.20; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1373.pdf

import Definitions.Def_DetTerminalEmbedding1373_Real_geometry
import Definitions.Def_CalamaiMore_Convergence_proj

set_option autoImplicit false

namespace DetTerminalEmbedding1373.Real

/-- Finite maximum, with zero on an empty list. Resource/correlation targets use
nonempty lists; the empty default is not an extra constraint or a free optimizer. -/
noncomputable def objective {N m : ℕ} (a : Fin N → E m) (c : Fin N → ℝ) (w : E m) : ℝ :=
  (List.finRange N).foldl (fun b i => max b |inner ℝ w (a i) - c i|) 0

/-- Left-to-right scan, replacing the maximizer only on strict improvement. -/
noncomputable def activeIndex {N m : ℕ} (a : Fin N → E m) (c : Fin N → ℝ)
    (w : E m) : Option (Fin N) :=
  (List.finRange N).foldl (fun acc i => match acc with
    | none => some i
    | some j => if |inner ℝ w (a j) - c j| < |inner ℝ w (a i) - c i|
        then some i else some j) none

noncomputable def selectedSubgradient {N m : ℕ} (a : Fin N → E m) (c : Fin N → ℝ)
    (w : E m) : E m :=
  match activeIndex a c w with
  | none => 0
  | some i => (if inner ℝ w (a i) - c i = 0 then 0
      else if 0 < inner ℝ w (a i) - c i then 1 else -1 : ℝ) • a i

/-- Explicit arithmetic radial formula (36), with no nearest-point oracle. -/
noncomputable def radialProjection {m : ℕ} (w : E m) : E m :=
  (max 1 ‖w‖)⁻¹ • w

noncomputable def solverIterations (η : ℝ) : ℕ := ⌈4 / η ^ 2⌉₊

noncomputable def solverIterate {N m : ℕ} (a : Fin N → E m) (c : Fin N → ℝ)
    (η : ℝ) : ℕ → E m
  | 0 => 0
  | t+1 => radialProjection (solverIterate a c η t -
      (η / 4) • selectedSubgradient a c (solverIterate a c η t))

/-- Earliest minimum over exactly 0 ≤ t < T, not the last iterate. -/
noncomputable def bestIterateIndex {N m : ℕ} (a : Fin N → E m) (c : Fin N → ℝ)
    (η : ℝ) : ℕ :=
  (List.range (solverIterations η)).foldl (fun best t =>
    if objective a c (solverIterate a c η t) < objective a c (solverIterate a c η best)
    then t else best) 0

noncomputable def solve {N m : ℕ} (a : Fin N → E m) (c : Fin N → ℝ) (η : ℝ) : E m :=
  solverIterate a c η (bestIterateIndex a c η)

/-- Equation (33), generalized to norm-bounded u; Section 6 needs ‖u‖ < 1
for queries with a component orthogonal to the terminal span. -/
noncomputable def correlationVectors {N d m : ℕ} (A : E d →ₗ[ℝ] E m)
    (x : Fin N → E d) : Fin N → E m := fun i => A (direction (x i))

noncomputable def correlationScalars {N d : ℕ} (x : Fin N → E d)
    (u : E d) : Fin N → ℝ := fun i => inner ℝ u (direction (x i))

end DetTerminalEmbedding1373.Real


