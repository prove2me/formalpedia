-- Prove2me | Definitions.Def_ReflNewton_FirstOrder_Setting
-- name    : ReflNewton_FirstOrder_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T05:26:37.938733+00:00
-- url     : https://prove2.me/theorems/71165992-0775-4552-b410-3319bb2fd9f1
-- title:
--   Definition 2, (2.3), (3.2)–(3.5), Figs. 4, 6, 9, Definitions 3–4 — scaling vector v(x), reflective path, the interior-reflective algorithm
-- statement:
--   This file fixes the objects of Coleman and Li's first-order analysis of interior-reflective methods for the bound-constrained problem
--   $$\min_{x\in\mathbb R^n} f(x)\quad\text{subject to}\quad l\le x\le u,\qquad(1.1)$$
--   where $l\in(\mathbb R\cup\{-\infty\})^n$, $u\in(\mathbb R\cup\{+\infty\})^n$ and $l\le u$. The feasible box is $\mathcal F=\{x: l\le x\le u\}$ and its strict interior is $\operatorname{int}(\mathcal F)=\{x: l<x<u\}$. Write $g(x)=\nabla f(x)$ and $H(x)=\nabla^2 f(x)$.
--
--   1. **The scaling vector $v(x)$** (Definition 2). For each index $i$:
--      (i) if $g_i(x)<0$ and $u_i<\infty$, then $v_i=x_i-u_i$;
--      (ii) if $g_i(x)\ge 0$ and $l_i>-\infty$, then $v_i=x_i-l_i$;
--      (iii) if $g_i(x)<0$ and $u_i=\infty$, then $v_i=-1$;
--      (iv) if $g_i(x)\ge 0$ and $l_i=-\infty$, then $v_i=1$.
--      The scaling matrix is $D(x)=\operatorname{diag}(|v(x)|^{1/2})$ (2.3). The file names the vectors $D(x)^2g(x)$, $D(x)g(x)$, $D(x)^{-2}s$ and $D(x)^2\operatorname{sgn}(g(x))$, with $\operatorname{sgn}(t)=1$ for $t\ge0$ and $-1$ for $t<0$ (footnote 4), and the curvature $s^{T}H(x)s$.
--   2. **The reflective transformation $R$** (Fig. 6), componentwise: if $l_i,u_i$ are finite, $w_i=|y_i-l_i| \bmod 2(u_i-l_i)$ and $R(y)_i=\min(w_i,\,2(u_i-l_i)-w_i)+l_i$; if only $l_i$ is finite, $R(y)_i=y_i$ for $y_i\ge l_i$ and $2l_i-y_i$ otherwise; if only $u_i$ is finite, $R(y)_i=y_i$ for $y_i\le u_i$ and $2u_i-y_i$ otherwise; if both are infinite, $R(y)_i=y_i$. The **reflective path** from $x$ in the direction $s$ is $p(\alpha)=R(x+\alpha s)-x$, the piecewise linear path of (3.2) and Fig. 4 that bounces off the faces of the box. A **breakpoint** is a stepsize at which $x+p(\alpha)$ lies on the boundary.
--   3. **Descent direction** (footnote 3): $f(x+p(\alpha))<f(x)$ for all sufficiently small $\alpha>0$.
--   4. **Line-search conditions** (3.4)–(3.5), for $0<\sigma_l<\sigma_u<1$:
--      $$f(x_{k+1})<f(x_k)+\sigma_l\Big(\alpha_kg_k^{T}s_k+\tfrac12\alpha_k^2\min(s_k^{T}H_ks_k,0)\Big),$$
--      $$f(x_{k+1})>f(x_k)+\sigma_u\Big(\alpha_kg_k^{T}s_k+\tfrac12\alpha_k^2\min(s_k^{T}H_ks_k,0)\Big).$$
--   5. **The interior-reflective algorithm** (Fig. 9), with a positive scalar $\rho$: $x_1\in\operatorname{int}(\mathcal F)$, and for every $k$ the direction $s_k$ is a descent direction at $x_k$, the stepsize $\alpha_k>0$ is not a breakpoint, (3.4) holds, either (3.5) holds or $\alpha_k>\rho$, and $x_{k+1}=x_k+p_k(\alpha_k)$.
--   6. **Constraint compatibility** (Definition 3): $\{D_k^{-2}s_k\}$ is bounded, where $D_k=D(x_k)$.
--   7. **Consistency** (Definition 4): $s_k^{T}g_k\to0$ implies $D_kg_k\to0$.
--
--   These are the objects of Theorem 8: along a run of Fig. 9 whose directions are consistent and constraint-compatible, $D_k^2g_k\to0$.
--
--   **Formalization Note** Points are `EuclideanSpace ℝ (Fin n)`, bounds are `EReal` vectors, and the box $\mathcal F$ and the level set $\mathcal L$ are the published `LewisTorczon.BoundPS.box` and `levelSet`. No arithmetic is done in `EReal`: each formula branches on whether a bound is infinite and uses the real value of the finite bound. $D(x)$ is never formed as a matrix; its actions are written componentwise, and $D(x)^{-2}s$ is $s_i/|v_i(x)|$, which is meaningful at interior points, where $v_i(x)\neq0$. $H(x)s$ is the derivative of the gradient map applied to $s$. The reflective path is encoded through $R$, which the paper presents as the same method as Fig. 4 in other notation (p. 199); the real `mod` is $P\cdot\mathrm{fract}(t/P)$. The sequences are indexed from $0$, so `x 0` is the paper's $x_1$; the stepsize $\alpha_k>0$ is explicit.
-- source:
--   Coleman & Li, On the convergence of interior-reflective Newton methods for nonlinear minimization subject to bounds, Math. Programming 67 (1994), pp. 189–205: (1.1) p. 189–190; Definition 2 and (2.3) pp. 193–194; (3.2), Fig. 4, Fig. 6, footnote 3 pp. 197–199; (3.4)–(3.5) p. 200; Fig. 9 p. 202; Definition 3 p. 202; footnote 4 p. 204; Definition 4 p. 205

import Mathlib
import Definitions.Def_LewisTorczon_BoundPS_Box
open Filter Topology

namespace ReflNewton.FirstOrder

/-- Points of `ℝⁿ` with the Euclidean norm. The paper's index `i = 1, …, n` is Lean's `i : Fin n`. -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The strict interior `int(𝓕) = {x : l < x < u}` (Coleman–Li, p. 190). The bounds are extended
reals: `l i = ⊥` is `lᵢ = −∞`, `u i = ⊤` is `uᵢ = +∞`. -/
def intBox {n : ℕ} (l u : Fin n → EReal) : Set (E n) :=
  {x | ∀ i, l i < ((x i : ℝ) : EReal) ∧ ((x i : ℝ) : EReal) < u i}

/-- One component of `v(x)`, Definition 2 (pp. 193–194), with `a = lᵢ`, `b = uᵢ`, `xi = xᵢ`,
`gi = ∇f(x)ᵢ`:
(i) `gᵢ < 0`, `uᵢ < ∞`: `xᵢ − uᵢ`; (iii) `gᵢ < 0`, `uᵢ = ∞`: `−1`;
(ii) `gᵢ ≥ 0`, `lᵢ > −∞`: `xᵢ − lᵢ`; (iv) `gᵢ ≥ 0`, `lᵢ = −∞`: `1`.
The finite bound is read through `EReal.toReal` only on the branch where it is finite. -/
noncomputable def vCoord (a b : EReal) (xi gi : ℝ) : ℝ :=
  if gi < 0 then (if b = ⊤ then -1 else xi - b.toReal)
  else (if a = ⊥ then 1 else xi - a.toReal)

/-- The vector `v(x)` of Definition 2, with `g = ∇f(x)` the gradient of `f`. -/
noncomputable def vVec {n : ℕ} (l u : Fin n → EReal) (f : E n → ℝ) (x : E n) : E n :=
  WithLp.toLp 2 (fun i => vCoord (l i) (u i) (x i) (gradient f x i))

/-- `D(x)² ∇f(x)`, where `D(x) = diag(|v(x)|^{1/2})` (2.3): component `i` is `|vᵢ(x)| gᵢ(x)`. -/
noncomputable def dSqG {n : ℕ} (l u : Fin n → EReal) (f : E n → ℝ) (x : E n) : E n :=
  WithLp.toLp 2 (fun i => |vVec l u f x i| * gradient f x i)

/-- `D(x) ∇f(x)`: component `i` is `|vᵢ(x)|^{1/2} gᵢ(x)`. -/
noncomputable def dG {n : ℕ} (l u : Fin n → EReal) (f : E n → ℝ) (x : E n) : E n :=
  WithLp.toLp 2 (fun i => Real.sqrt |vVec l u f x i| * gradient f x i)

/-- `D(x)⁻² s`: component `i` is `sᵢ / |vᵢ(x)|`. Only meaningful at interior points, where
`vᵢ(x) ≠ 0`; every use below is at an interior iterate. -/
noncomputable def dInvSq {n : ℕ} (l u : Fin n → EReal) (f : E n → ℝ) (x s : E n) : E n :=
  WithLp.toLp 2 (fun i => s i / |vVec l u f x i|)

/-- The curvature `sᵀ H(x) s`, with `H(x) = ∇²f(x)` the derivative of the gradient. -/
noncomputable def hq {n : ℕ} (f : E n → ℝ) (x s : E n) : ℝ :=
  inner ℝ (fderiv ℝ (gradient f) x s) s

/-- The sign of footnote 4 (p. 204): `+1` if `t ≥ 0`, `−1` if `t < 0` (so `sgn 0 = +1`). -/
noncomputable def sgnP (t : ℝ) : ℝ := if 0 ≤ t then 1 else -1

/-- `D(x)² sgn(∇f(x))`: component `i` is `|vᵢ(x)| sgn(gᵢ(x))` with the sign of footnote 4. -/
noncomputable def dSqSgn {n : ℕ} (l u : Fin n → EReal) (f : E n → ℝ) (x : E n) : E n :=
  WithLp.toLp 2 (fun i => |vVec l u f x i| * sgnP (gradient f x i))

/-- The one-dimensional reflective transformation of Fig. 6 (p. 199), `xᵢ = R(y)ᵢ`:
Case 1 (`lᵢ, uᵢ` finite): `wᵢ = |yᵢ − lᵢ| mod [2(uᵢ − lᵢ)]`, `xᵢ = min(wᵢ, 2(uᵢ − lᵢ) − wᵢ) + lᵢ`;
Case 2 (only `lᵢ` finite): `yᵢ` if `yᵢ ≥ lᵢ`, else `2lᵢ − yᵢ`;
Case 3 (only `uᵢ` finite): `yᵢ` if `yᵢ ≤ uᵢ`, else `2uᵢ − yᵢ`;
Case 4: `yᵢ`.
The real `mod` is `P · fract(t / P)` with `P = 2(uᵢ − lᵢ)`; when `lᵢ = uᵢ` this gives `xᵢ = lᵢ`
(int(𝓕) is then empty and no run starts). -/
noncomputable def reflectCoord (a b : EReal) (y : ℝ) : ℝ :=
  if a = ⊥ then
    (if b = ⊤ then y else (if y ≤ b.toReal then y else 2 * b.toReal - y))
  else if b = ⊤ then
    (if a.toReal ≤ y then y else 2 * a.toReal - y)
  else
    let P := 2 * (b.toReal - a.toReal)
    let w := P * Int.fract (|y - a.toReal| / P)
    min w (P - w) + a.toReal

/-- The reflective transformation `R : ℝⁿ → 𝓕` of Fig. 6, applied componentwise. -/
noncomputable def reflect {n : ℕ} (l u : Fin n → EReal) (y : E n) : E n :=
  WithLp.toLp 2 (fun i => reflectCoord (l i) (u i) (y i))

/-- The reflective path `p(α)` of (3.2) and Fig. 4 from the point `x` in the direction `s`,
`x + p(α) = R(x + α s)` (the x-space form of the straight line search of Fig. 8, p. 199). -/
noncomputable def reflPath {n : ℕ} (l u : Fin n → EReal) (x s : E n) (α : ℝ) : E n :=
  reflect l u (x + α • s) - x

/-- Footnote 3 (p. 199), in x-space: `s` is a descent direction for `f` at `x` if
`f(x + p(α)) < f(x)` for all positive sufficiently small `α`. -/
def IsDescentDir {n : ℕ} (l u : Fin n → EReal) (f : E n → ℝ) (x s : E n) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ α : ℝ, 0 < α → α < ε → f (x + reflPath l u x s α) < f x

/-- Condition (3.4) (p. 200) for the step from `x` along `s` with stepsize `α` to `x'`:
`f(x') < f(x) + σ_l(α gᵀs + ½ α² min(sᵀHs, 0))`. -/
def cond34 {n : ℕ} (f : E n → ℝ) (σl : ℝ) (x s : E n) (α : ℝ) (x' : E n) : Prop :=
  f x' < f x + σl * (α * inner ℝ (gradient f x) s + 1 / 2 * α ^ 2 * min (hq f x s) 0)

/-- Condition (3.5) (p. 200): `f(x') > f(x) + σ_u(α gᵀs + ½ α² min(sᵀHs, 0))`. -/
def cond35 {n : ℕ} (f : E n → ℝ) (σu : ℝ) (x s : E n) (α : ℝ) (x' : E n) : Prop :=
  f x + σu * (α * inner ℝ (gradient f x) s + 1 / 2 * α ^ 2 * min (hq f x s) 0) < f x'

/-- A run of the interior-reflective algorithm of Fig. 9 (p. 202) with line-search parameters
`σl, σu` and threshold `ρ`: iterates `x k` (the paper's `x_{k+1}`; `x 0` is `x₁`), directions
`s k`, stepsizes `α k`. `x₁ ∈ int(𝓕)`; for every `k`, `s_k` is a descent direction (step 1);
`α_k > 0` is not a breakpoint, i.e. `x_k + p_k(α_k) ∈ int(𝓕)` (2a); (3.4) holds (2b); (3.5)
holds or `α_k > ρ` (2c); and `x_{k+1} = x_k + p_k(α_k)` (step 3). -/
def IsIRRun {n : ℕ} (l u : Fin n → EReal) (f : E n → ℝ) (σl σu ρ : ℝ)
    (x s : ℕ → E n) (α : ℕ → ℝ) : Prop :=
  x 0 ∈ intBox l u ∧
  ∀ k, IsDescentDir l u f (x k) (s k) ∧ 0 < α k ∧
    x k + reflPath l u (x k) (s k) (α k) ∈ intBox l u ∧
    cond34 f σl (x k) (s k) (α k) (x (k + 1)) ∧
    (cond35 f σu (x k) (s k) (α k) (x (k + 1)) ∨ ρ < α k) ∧
    x (k + 1) = x k + reflPath l u (x k) (s k) (α k)

/-- Definition 3 (p. 202): `{s_k}` is constraint-compatible (along the iterates `{x_k}`) if
`{D_k⁻² s_k}` is bounded. -/
def IsConstraintCompatible {n : ℕ} (l u : Fin n → EReal) (f : E n → ℝ) (x s : ℕ → E n) : Prop :=
  Bornology.IsBounded (Set.range fun k => dInvSq l u f (x k) (s k))

/-- Definition 4 (p. 205): `{s_k}` satisfies the consistency condition if `{s_kᵀ g_k} → 0`
implies `{D_k g_k} → 0`. -/
def IsConsistent {n : ℕ} (l u : Fin n → EReal) (f : E n → ℝ) (x s : ℕ → E n) : Prop :=
  Tendsto (fun k => inner ℝ (s k) (gradient f (x k))) atTop (𝓝 0) →
    Tendsto (fun k => dG l u f (x k)) atTop (𝓝 0)

end ReflNewton.FirstOrder


