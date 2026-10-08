-- Prove2me | Definitions.Def_ConicQuadIPM_NTScaling_Scaling
-- name    : ConicQuadIPM_NTScaling_Scaling
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T03:09:08.366624+00:00
-- url     : https://prove2.me/theorems/87a13b4a-d0dc-49b3-9993-10b9af13cd79
-- title:
--   Definition 3.3, (28), (30)–(32), (34) — scaling matrices, the NT scaling x̄ = s̄, θ, w, and the matrices of Lemma 4.2
-- statement:
--   Fix one cone block of kind $K\in\{\mathbb R_+, K^q, K^r\}$ and dimension $d$, with the matrices $T$, $Q$ of Definition 3.2.
--
--   1. **Scaling matrix** (Definition 3.3, p. 11). $W\in\mathbb R^{d\times d}$ is a scaling matrix if $W\succ0$ (symmetric positive definite) and $WQW = Q$.
--   2. **Scaled points** (p. 11). For $\theta\in\mathbb R$: $\bar x := \theta W x$ and $\bar s := (\theta W)^{-1}s$.
--   3. **NT scaling** (28), p. 14. $(\theta, W)$ is an NT scaling of $(x,s)$ if $\theta>0$, $W$ is a scaling matrix, and $\bar x = \bar s$.
--   4. **The NT quantities** of Lemma 4.2 (p. 15):
--   $$\theta = \Bigl(\frac{s^TQs}{x^TQx}\Bigr)^{1/4},\ \text{i.e. } \theta^2 = \sqrt{\frac{s^TQs}{x^TQx}}\quad(30),\qquad w = \frac{\theta^{-1}s + \theta Qx}{\sqrt2\sqrt{x^Ts + \sqrt{x^TQx\, s^TQs}}}\quad(32).$$
--   5. **The matrices of Lemma 4.2.** For $\mathbb R_+$: $W = \frac1\theta\bigl(X^{-1}S\bigr)^{1/2} = \theta^{-1}\sqrt{s_1/x_1}$. For $K^q$, the two forms of (31):
--   $$\begin{bmatrix} w_1 & w_{2:d}^T\\ w_{2:d} & I + \frac{w_{2:d}w_{2:d}^T}{1+w_1}\end{bmatrix}\quad\text{and}\quad -Q + \frac{(e_1+w)(e_1+w)^T}{1+e_1^Tw}.$$
--   For $K^r$, (34): $-Q + \dfrac{(Te_1+w)(Te_1+w)^T}{1+e_1^TTw}$ with $T$, $Q$ of the rotated cone.
--
--   These are the objects whose properties Lemma 4.2 and its proof establish.
--
--   **Formalization Note** Vectors are `Fin d → ℝ` with 0-based indices (the paper's $x_1$ is `coord x 0`); $\|x_{2:n}\|^2$ is `tailSq x 1`, a sum of squares (Euclidean, never Mathlib's sup norm); $x^Ts$ is `x ⬝ᵥ s`. The scaled points, Definition 3.3 and (28) are stated per block, which is what the block-diagonal $\Theta$ and $W$ of p. 11–12 reduce to. The positivity $\theta>0$ is part of `IsNT`: the paper calls $\Theta$ positive definite (p. 24) and needs $(\Theta W)^{-1}$ to exist. The inverse is Mathlib's `Matrix.inv`, which is $0$ on singular matrices; `IsNT` requires $W\succ0$, so it is never read at a singular argument. For $\mathbb R_+$, $X=\operatorname{mat}(Tx)=[x_1]$ and $S=[s_1]$, so $(X^{-1}S)^{1/2}=\sqrt{s_1/x_1}$; `Wnonneg` is this $1\times1$ matrix written as a multiple of the identity. `thetaNT`, `wNT` and the matrices are total functions; they are only claimed meaningful for interior $x$, $s$, where every denominator is positive.
-- source:
--   Andersen, Roos & Terlaky, On implementing a primal-dual interior-point method for conic quadratic optimization, Math. Program. (2003), DOI 10.1007/s10107-002-0349-3; authors' preprint of 18 Dec 2000, pp. 11–15, Definition 3.3, (28), (30)–(32), (34), Lemma 4.2 i)

import Mathlib
import Definitions.Def_ConicQuadIPM_NTScaling_Setting

namespace ConicQuadIPM.NTScaling

open Matrix

/-- Definition 3.3, p. 11: `W ∈ ℝ^{d×d}` is a **scaling matrix** for a cone block of the given kind
if `W ≻ 0` (symmetric positive definite) and `W Q W = Q`. -/
def IsScaling (kind : ConicQuadIPM.Complementarity.ConeKind) (d : ℕ) (W : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  W.PosDef ∧ W * Qmat kind d * W = Qmat kind d

/-- The scaled primal point of Definition 3.3, p. 11, for one block: `x̄ := θ W x`. -/
def xbar {d : ℕ} (θ : ℝ) (W : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ) : Fin d → ℝ :=
  (θ • W) *ᵥ x

/-- The scaled dual point of Definition 3.3, p. 11, for one block: `s̄ := (θ W)⁻¹ s`. -/
noncomputable def sbar {d : ℕ} (θ : ℝ) (W : Matrix (Fin d) (Fin d) ℝ) (s : Fin d → ℝ) : Fin d → ℝ :=
  (θ • W)⁻¹ *ᵥ s

/-- The Nesterov–Todd scaling, (28) of p. 14, for one block: `θ > 0`, `W` is a scaling matrix,
and the scaled points coincide, `x̄ = s̄`. -/
def IsNT (kind : ConicQuadIPM.Complementarity.ConeKind) (d : ℕ) (θ : ℝ) (W : Matrix (Fin d) (Fin d) ℝ)
    (x s : Fin d → ℝ) : Prop :=
  0 < θ ∧ IsScaling kind d W ∧ xbar θ W x = sbar θ W s

/-- The NT scalar `θ` of (30), p. 15: `θ = √(√(sᵀQs / xᵀQx))`, so that
`θ² = √(sᵀQs / xᵀQx)`. -/
noncomputable def thetaNT (kind : ConicQuadIPM.Complementarity.ConeKind) (d : ℕ) (x s : Fin d → ℝ) : ℝ :=
  Real.sqrt (Real.sqrt ((s ⬝ᵥ (Qmat kind d *ᵥ s)) / (x ⬝ᵥ (Qmat kind d *ᵥ x))))

/-- The vector `w` of (32), p. 15:
`w = (θ⁻¹ s + θ Q x) / (√2 · √(xᵀs + √(xᵀQx · sᵀQs)))` with `θ = thetaNT`. -/
noncomputable def wNT (kind : ConicQuadIPM.Complementarity.ConeKind) (d : ℕ) (x s : Fin d → ℝ) : Fin d → ℝ :=
  (Real.sqrt 2 *
      Real.sqrt (x ⬝ᵥ s +
        Real.sqrt ((x ⬝ᵥ (Qmat kind d *ᵥ x)) * (s ⬝ᵥ (Qmat kind d *ᵥ s)))))⁻¹ •
    ((thetaNT kind d x s)⁻¹ • s + thetaNT kind d x s • (Qmat kind d *ᵥ x))

/-- Lemma 4.2 i), p. 15, for `R₊` (`d = 1`): `W = (1/θ)((X)⁻¹S)^{1/2}`. Since `X = mat(T x) = [x₁]`
and `S = [s₁]`, this is the `1 × 1` matrix `θ⁻¹ √(s₁ / x₁)` (written as a scalar multiple of the
identity). -/
noncomputable def Wnonneg (d : ℕ) (x s : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  ((thetaNT .nonneg d x s)⁻¹ * Real.sqrt (ConicQuadIPM.Complementarity.coord s 0 / ConicQuadIPM.Complementarity.coord x 0)) • (1 : Matrix (Fin d) (Fin d) ℝ)

/-- The first form of (31), p. 15: the block matrix
`[w₁, w_{2:n}ᵀ; w_{2:n}, I + w_{2:n} w_{2:n}ᵀ / (1 + w₁)]`, entrywise. -/
noncomputable def WquadArrow {d : ℕ} (w : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i j =>
    if i.val = 0 then w j
    else if j.val = 0 then w i
    else (if i = j then 1 else 0) + w i * w j / (1 + ConicQuadIPM.Complementarity.coord w 0)

/-- The second form of (31), p. 15: `−Q + (e₁ + w)(e₁ + w)ᵀ / (1 + e₁ᵀw)` with `Q` of the
quadratic cone. -/
noncomputable def WquadOuter (d : ℕ) (w : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  -Qmat .quad d + (1 + ConicQuadIPM.Complementarity.e1 (d := d) ⬝ᵥ w)⁻¹ • vecMulVec (ConicQuadIPM.Complementarity.e1 (d := d) + w) (ConicQuadIPM.Complementarity.e1 (d := d) + w)

/-- (34), p. 15: `−Q + (T e₁ + w)(T e₁ + w)ᵀ / (1 + e₁ᵀ T w)` with `T`, `Q` of the rotated
quadratic cone. -/
noncomputable def Wrot (d : ℕ) (w : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  -Qmat .rot d +
    (1 + ConicQuadIPM.Complementarity.e1 (d := d) ⬝ᵥ (Tmat .rot d *ᵥ w))⁻¹ •
      vecMulVec (Tmat .rot d *ᵥ ConicQuadIPM.Complementarity.e1 (d := d) + w) (Tmat .rot d *ᵥ ConicQuadIPM.Complementarity.e1 (d := d) + w)

end ConicQuadIPM.NTScaling


