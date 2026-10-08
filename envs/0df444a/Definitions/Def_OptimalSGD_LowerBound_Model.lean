-- Prove2me | Definitions.Def_OptimalSGD_LowerBound_Model
-- name    : OptimalSGD_LowerBound_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T12:23:43.411747+00:00
-- url     : https://prove2.me/theorems/46d59e74-fbb5-4b67-9f43-d3f576d3ffaf
-- title:
--   The two lower-bound examples of §4: box domains, projection, uniform noise, SGD with η_t = c/t and its average (pp. 3–5)
-- statement:
--   This file fixes the objects of the two lower-bound examples of Rakhlin, Shamir and Sridharan (§4). Points live in $\mathbb R^d$ with $d\ge1$ and the Euclidean norm; $w_1$ denotes the **first coordinate** of a point $w$ (not the first iterate).
--
--   1. **Boxes and projection.** For $lo\le hi$, the box is $[lo,hi]^d=\{w: lo\le w_i\le hi \text{ for all } i\}$, and $\Pi_{[lo,hi]^d}$ clamps every coordinate: $\Pi(v)_i=\max\{lo,\min\{hi,v_i\}\}$. This is the Euclidean projection onto the box.
--   2. **Noise.** Each $Z_t$ is uniformly distributed on $[-1,3]$, and $Z_1,Z_2,\dots$ are independent. A noise sequence of horizon $T$ is drawn from the product law $\mathrm{Unif}[-1,3]^{\otimes T}$.
--   3. **SGD with steps $\eta_t=c/t$.** Given a projection $\Pi$, an oracle $\hat g(w,z)$ (the gradient estimate returned at the query point $w$ when the noise value is $z$), a constant $c$ and an arbitrary starting point $w_1$, the iterates are
--   $$w_{t+1}=\Pi\big(w_t-\tfrac{c}{t}\,\hat g(w_t,Z_t)\big),\qquad t=1,2,\dots,$$
--   and the averaged iterate after $T$ rounds is $\bar w_T=\frac1T(w_1+\dots+w_T)$.
--   4. **Example A** (Theorem 3). Domain $W=[0,1]^d$, objective and oracle
--   $$F(w)=\tfrac12\|w\|^2+w_1,\qquad \hat g(w,z)=w+(z,0,\dots,0).$$
--   5. **Example B** (Theorem 4). Domain $W=[-1,1]^d$, objective and state-dependent oracle
--   $$F(w)=\tfrac12\|w\|^2+\begin{cases}w_1&w_1\ge0\\-7w_1&w_1<0\end{cases},\qquad \hat g(w,z)=w+\begin{cases}(z,0,\dots,0)&w_1\ge0\\(-7,0,\dots,0)&w_1<0.\end{cases}$$
--
--   In both examples $F$ is $1$-strongly convex with global minimum $F(0)=0$, and for $Z\sim\mathrm{Unif}[-1,3]$ the mean $\mathbb E[\hat g(w,Z)]$ is a subgradient of $F$ at $w$. These are the problems on which the paper shows that SGD with averaging converges no faster than order $\log(T)/T$.
--
--   **Formalization Note** The carrier is `UnderstandingML.Vec d` $=\mathbb R^d$ with $d\ge1$ (`NeZero d`); the first coordinate is index `0`. The run `sgdRun` is indexed from $0$: index $k$ is the paper's $w_{k+1}$, and the step at index $k$ uses $\eta_{k+1}=c/(k+1)$ and the noise value `Z k`. The uniform law is `ProbabilityTheory.cond volume (Set.Icc (-1) 3)`, and the law of $(Z_1,\dots,Z_T)$ is the published `UnderstandingML.iidLaw` (the product measure). A finite noise sequence is extended by $0$ beyond its horizon (`extendNoise`); the first $T$ iterates never read the extension.
-- source:
--   Rakhlin, Shamir, Sridharan, Making Gradient Descent Optimal for Strongly Convex Stochastic Optimization, arXiv:1109.5647v7, p. 3, §2 (SGD algorithm, projection, averaging); pp. 4–5, §4 (the two examples preceding Theorems 3 and 4)

import Mathlib
import Definitions.Def_UnderstandingML_Framework
import Definitions.Def_UnderstandingML_Linear

namespace OptimalSGD.LowerBound

open MeasureTheory UnderstandingML

variable {d : ℕ}

/-- The box `[lo, hi]^d = {w ∈ ℝ^d : lo ≤ w_i ≤ hi for every coordinate i}` (Rakhlin, Shamir,
Sridharan, arXiv:1109.5647v7, §4, pp. 4–5: the domains `W = [0, 1]^d` and `W = [−1, 1]^d`). -/
def box (lo hi : ℝ) : Set (Vec d) :=
  {w | ∀ i, w i ∈ Set.Icc lo hi}

/-- The projection `Π_W` onto the box `W = [lo, hi]^d` (arXiv:1109.5647v7, §2, p. 3), given by
coordinatewise clamping `v_i ↦ max lo (min hi v_i)`; for `lo ≤ hi` this is the Euclidean
projection onto the box. -/
noncomputable def boxProj (lo hi : ℝ) (v : Vec d) : Vec d :=
  WithLp.toLp 2 (fun i => max lo (min hi (v i)))

/-- Projected SGD with step sizes `η_t = c/t`, started at an arbitrary point `w₁`
(arXiv:1109.5647v7, §2, p. 3 and §4, pp. 4–5). The oracle `g w z` is the gradient estimate
returned at the query point `w` when the noise value is `z`, and `Z t` is the noise drawn in
round `t`. Index `t` of `sgdRun` is the paper's `w_{t+1}`: `sgdRun … 0 = w₁` and
`w_{t+2} = Π(w_{t+1} − (c/(t+1)) ĝ_{t+1})`, i.e. the paper's `w_{s+1} = Π_W(w_s − η_s ĝ_s)` with
`η_s = c/s`, `s = t + 1`. -/
noncomputable def sgdRun (proj : Vec d → Vec d) (g : Vec d → ℝ → Vec d) (c : ℝ) (w₁ : Vec d)
    (Z : ℕ → ℝ) : ℕ → Vec d
  | 0 => w₁
  | t + 1 => proj (sgdRun proj g c w₁ Z t - (c / ((t : ℝ) + 1)) • g (sgdRun proj g c w₁ Z t) (Z t))

/-- The law of one noise value `Z_t`: the uniform distribution on `[−1, 3]`
(Lebesgue measure conditioned on `[−1, 3]`, i.e. density `1/4` there). -/
noncomputable def noiseLaw : Measure ℝ :=
  ProbabilityTheory.cond volume (Set.Icc (-1 : ℝ) 3)

/-- A noise sequence `(Z_0, …, Z_{T−1})`, extended by `0` beyond the horizon (the extension is
never read by the first `T` iterates). -/
noncomputable def extendNoise {T : ℕ} (Z : Fin T → ℝ) : ℕ → ℝ :=
  fun t => if h : t < T then Z ⟨t, h⟩ else 0

/-! ### Example A (Theorem 3): `W = [0, 1]^d`, `F(w) = ½‖w‖² + w₁` -/

/-- Example A's objective `F(w) = ½‖w‖² + w₁` (arXiv:1109.5647v7, §4, p. 4); `w 0` is the
paper's first coordinate `w₁`. -/
noncomputable def objA [NeZero d] (w : Vec d) : ℝ :=
  (1 / 2) * ‖w‖ ^ 2 + w 0

/-- Example A's oracle `ĝ = w + (z, 0, …, 0)` (arXiv:1109.5647v7, §4, p. 4). -/
noncomputable def oracleA [NeZero d] (w : Vec d) (z : ℝ) : Vec d :=
  w + EuclideanSpace.single 0 z

/-- SGD on Example A: projection onto `[0, 1]^d`, oracle `oracleA`, steps `η_t = c/t`. -/
noncomputable def runA [NeZero d] (c : ℝ) (w₁ : Vec d) (Z : ℕ → ℝ) : ℕ → Vec d :=
  sgdRun (boxProj 0 1) oracleA c w₁ Z

/-- The averaged iterate `w̄_T = (w₁ + … + w_T)/T` of SGD on Example A, for a noise sequence
`(Z_0, …, Z_{T−1})` (only `Z_0, …, Z_{T−2}` are read). -/
noncomputable def avgA [NeZero d] (c : ℝ) (w₁ : Vec d) {T : ℕ} (Z : Fin T → ℝ) : Vec d :=
  (T : ℝ)⁻¹ • ∑ t ∈ Finset.range T, runA c w₁ (extendNoise Z) t

/-! ### Example B (Theorem 4): `W = [−1, 1]^d`, `F(w) = ½‖w‖² + (w₁ if w₁ ≥ 0, −7w₁ if w₁ < 0)` -/

/-- Example B's objective `F(w) = ½‖w‖² + w₁` if `w₁ ≥ 0` and `½‖w‖² − 7w₁` if `w₁ < 0`
(arXiv:1109.5647v7, §4, p. 5). -/
noncomputable def objB [NeZero d] (w : Vec d) : ℝ :=
  (1 / 2) * ‖w‖ ^ 2 + (if 0 ≤ w 0 then w 0 else -7 * w 0)

/-- Example B's state-dependent oracle (arXiv:1109.5647v7, §4, p. 5): at the query point `w`,
`ĝ = w + (z, 0, …, 0)` if `w₁ ≥ 0` and `ĝ = w + (−7, 0, …, 0)` if `w₁ < 0`. -/
noncomputable def oracleB [NeZero d] (w : Vec d) (z : ℝ) : Vec d :=
  w + EuclideanSpace.single 0 (if 0 ≤ w 0 then z else -7)

/-- SGD on Example B: projection onto `[−1, 1]^d`, oracle `oracleB`, steps `η_t = c/t`. -/
noncomputable def runB [NeZero d] (c : ℝ) (w₁ : Vec d) (Z : ℕ → ℝ) : ℕ → Vec d :=
  sgdRun (boxProj (-1) 1) oracleB c w₁ Z

/-- The averaged iterate `w̄_T = (w₁ + … + w_T)/T` of SGD on Example B, for a noise sequence
`(Z_0, …, Z_{T−1})` (only `Z_0, …, Z_{T−2}` are read). -/
noncomputable def avgB [NeZero d] (c : ℝ) (w₁ : Vec d) {T : ℕ} (Z : Fin T → ℝ) : Vec d :=
  (T : ℝ)⁻¹ • ∑ t ∈ Finset.range T, runB c w₁ (extendNoise Z) t

end OptimalSGD.LowerBound


