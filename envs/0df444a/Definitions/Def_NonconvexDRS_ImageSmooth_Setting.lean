-- Prove2me | Definitions.Def_NonconvexDRS_ImageSmooth_Setting
-- name    : NonconvexDRS_ImageSmooth_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T15:35:48.641459+00:00
-- url     : https://prove2.me/theorems/ea51afd6-2fd8-4408-888f-f26045916f8e
-- title:
--   §2.1–§2.2, Definitions 5.1 and 5.12, pp. 5–6, 17, 24 — the image function (Ch), strong convexity, smoothness relative to a matrix, smoothness of the image function (Af)
-- statement:
--   This file fixes the objects used to state when the image function of a smooth function is itself smooth (Themelis–Patrinos, §5.4.2). Throughout, $\mathbb R^n$ and $\mathbb R^p$ are Euclidean spaces with inner product $\langle\cdot,\cdot\rangle$ and norm $\|\cdot\|$, matrices $C\in\mathbb R^{p\times n}$ are linear maps $\mathbb R^n\to\mathbb R^p$ with transpose $C^\top$ and spectral norm $\|C\|$, and $\overline{\mathbb R}=\mathbb R\cup\{\infty\}$.
--
--   1. **Proper functions (p. 5).** $h:\mathbb R^n\to\overline{\mathbb R}$ is *proper* if it never takes the value $-\infty$ and $\operatorname{dom}h=\{x\mid h(x)<\infty\}\neq\emptyset$.
--   2. **Image function (Definition 5.1, p. 17).** For $h:\mathbb R^n\to\overline{\mathbb R}$ and $C\in\mathbb R^{p\times n}$,
--   $$(Ch)(s)=\inf_{x\in\mathbb R^n}\{h(x)\mid Cx=s\}\in[-\infty,+\infty],$$
--   which is $+\infty$ when $s\notin\operatorname{range}C$.
--   3. **Smoothness and hypoconvexity (§2.2, p. 6).** A differentiable $h:\mathbb R^n\to\mathbb R$ is *$L$-smooth* if $\|\nabla h(x)-\nabla h(y)\|\le L\|x-y\|$ for all $x,y$, and *$\sigma$-hypoconvex* if $h-\frac\sigma2\|\cdot\|^2$ is convex.
--   4. **Strong convexity.** $h:\mathbb R^n\to\overline{\mathbb R}$ is *$\mu$-strongly convex* if $\operatorname{dom}h$ is convex and $h-\frac\mu2\|\cdot\|^2$ is convex on $\operatorname{dom}h$.
--   5. **Smoothness relative to a matrix (Definition 5.12, p. 24).** A differentiable $h:\mathbb R^n\to\mathbb R$ is smooth relative to $C$, written $h\in C^{1,1}_C(\mathbb R^n)$, with constants $L_{h,C}$ and $\sigma_{h,C}$, $|\sigma_{h,C}|\le L_{h,C}$, if
--   $$\sigma_{h,C}\|C(x-y)\|^2\le\langle\nabla h(x)-\nabla h(y),x-y\rangle\le L_{h,C}\|C(x-y)\|^2\qquad(5.6)$$
--   whenever $\nabla h(x),\nabla h(y)\in\operatorname{range}C^\top$.
--   6. **Smoothness of an image function.** For $A\in\mathbb R^{p\times n}$ and a real-valued $f$, "$(Af)$ is smooth with $L_{(Af)}=L$ and $\sigma_{(Af)}=\sigma$" means that $(Af)$ is real-valued on all of $\mathbb R^p$, $L$-smooth and $\sigma$-hypoconvex.
--
--   These objects are the vocabulary of Theorem 5.13, which identifies conditions under which $(Af)$, the first DRS function in the primal equivalence of ADMM and DRS, satisfies the smoothness assumption of the DRS theory.
--
--   **Formalization Note** Points are `EuclideanSpace ℝ (Fin n)`, matrices are continuous linear maps, $C^\top$ is `ContinuousLinearMap.adjoint`. Extended-real functions are `EReal`-valued; the image function `imageFn` is the `EReal` infimum over the fibre $\{x\mid Cx=s\}$ and can be $\pm\infty$, as on the page. `IsStronglyConvexE` applies `toReal` only on $\operatorname{dom}h$, so it is faithful for functions that are never $-\infty$. `IsSmoothRel` keeps the guard "$\nabla h(x),\nabla h(y)\in\operatorname{range}C^\top$" of (5.6) and takes the constants as arguments. `IsImageSmooth A f L σ` asserts that `imageFn A f` equals the coercion of a real function $F$ that is `IsLSmooth F L` and `IsHypoconvex F σ`. `IsProper`, `IsLSmooth` and `IsHypoconvex` (items 1 and 3) are not redeclared here: they are the shared definitions `NonconvexDRS.DRS.IsProper`, `NonconvexDRS.DRS.IsLSmooth` and `NonconvexDRS.DRS.IsHypoconvex` of this series, which this file imports.
-- source:
--   Themelis & Patrinos, Douglas-Rachford splitting and ADMM for nonconvex optimization: tight convergence results, arXiv:1709.05747v4, pp. 5–6, 17, 24, §2.1 notation, §2.2, Definition 5.1, Definition 5.12 (5.6)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexDRS_DRS_Setting

open NonconvexSplitting.Shared
open scoped InnerProductSpace

namespace NonconvexDRS.ImageSmooth

noncomputable section

/-- The image function (Definition 5.1, p. 17) of `h : ℝⁿ → ℝ̄` under `C ∈ ℝ^{p×n}`:
`(Ch)(s) = inf {h(x) | Cx = s}`, an infimum in `[-∞, +∞]` (`+∞` when `s ∉ range C`). -/
def imageFn {n p : ℕ} (C : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin p))
    (h : EuclideanSpace ℝ (Fin n) → EReal) (s : EuclideanSpace ℝ (Fin p)) : EReal :=
  ⨅ (x : EuclideanSpace ℝ (Fin n)) (_ : C x = s), h x

/-- `h : ℝⁿ → ℝ̄` is `μ`-strongly convex: `dom h` is convex and `h - (μ/2)‖·‖²` is convex on
`dom h` (equivalently, `h - (μ/2)‖·‖²` is convex as an extended-real-valued function). The real
part `toReal` is only evaluated on `dom h`, where `h` is finite when `h` is never `-∞`. -/
def IsStronglyConvexE {n : ℕ} (h : EuclideanSpace ℝ (Fin n) → EReal) (μ : ℝ) : Prop :=
  Convex ℝ {x | h x ≠ ⊤} ∧
    ConvexOn ℝ {x | h x ≠ ⊤} (fun x => (h x).toReal - μ / 2 * ‖x‖ ^ 2)

/-- Smoothness relative to a matrix (Definition 5.12, p. 24), with the constants `L = L_{h,C}`
and `σ = σ_{h,C}` as arguments: `h` is differentiable, `|σ| ≤ L`, and
`σ‖C(x - y)‖² ≤ ⟨∇h(x) - ∇h(y), x - y⟩ ≤ L‖C(x - y)‖²` (5.6) whenever
`∇h(x), ∇h(y) ∈ range Cᵀ`. -/
def IsSmoothRel {n p : ℕ} (h : EuclideanSpace ℝ (Fin n) → ℝ)
    (C : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin p)) (L σ : ℝ) : Prop :=
  Differentiable ℝ h ∧ |σ| ≤ L ∧
    ∀ x y, gradient h x ∈ Set.range (ContinuousLinearMap.adjoint C) →
      gradient h y ∈ Set.range (ContinuousLinearMap.adjoint C) →
      σ * ‖C (x - y)‖ ^ 2 ≤ ⟪gradient h x - gradient h y, x - y⟫_ℝ ∧
        ⟪gradient h x - gradient h y, x - y⟫_ℝ ≤ L * ‖C (x - y)‖ ^ 2

/-- "The image function `(Af)` of a real-valued `f` is smooth on `ℝᵖ` with `L_{(Af)} = L` and
`σ_{(Af)} = σ`" (Theorem 5.13, p. 25, in the sense of §2.2): `(Af)` is real-valued, equal to some
`F : ℝᵖ → ℝ` that is `L`-smooth and `σ`-hypoconvex. -/
def IsImageSmooth {n p : ℕ} (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin p))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (L σ : ℝ) : Prop :=
  ∃ F : EuclideanSpace ℝ (Fin p) → ℝ,
    (∀ s, imageFn A (fun x => (f x : EReal)) s = (F s : EReal)) ∧ NonconvexDRS.DRS.IsLSmooth F L ∧ NonconvexDRS.DRS.IsHypoconvex F σ

end

end NonconvexDRS.ImageSmooth


