-- Prove2me | Definitions.Def_NonconvexDRS_ADMM_Setting
-- name    : NonconvexDRS_ADMM_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T16:31:53.813985+00:00
-- url     : https://prove2.me/theorems/a98dbee4-0e08-4520-a0c9-cf5397fcaaf0
-- title:
--   (1.2), (ADMM), (1.3), (2.5), Def. 5.1, Assumption II — image functions, the augmented Lagrangian, relaxed ADMM steps, the DRE (3.3) and the ranges of Theorem 4.1
-- statement:
--   This file fixes the objects of the primal equivalence between the alternating direction method of multipliers (ADMM) and Douglas–Rachford splitting (DRS) in Themelis and Patrinos. Throughout, $\mathbb R^m,\mathbb R^n,\mathbb R^p$ are Euclidean spaces, $\overline{\mathbb R}=\mathbb R\cup\{\infty\}$, and $A\in\mathbb R^{p\times m}$, $B\in\mathbb R^{p\times n}$ are linear maps with adjoints $A^\top,B^\top$.
--
--   **Basic notions (pp. 5–7).** $[r]_-=\max\{0,-r\}$. A function $h$ with values in $\overline{\mathbb R}$ is *proper* if it never takes the value $-\infty$ and $\operatorname{dom}h=\{x\mid h(x)<\infty\}\neq\emptyset$. A differentiable $h:\mathbb R^n\to\mathbb R$ is *$L$-smooth* if $\nabla h$ is $L$-Lipschitz, and *$\sigma$-hypoconvex* if $h-\frac\sigma2\|\cdot\|^2$ is convex. The proximal mapping (2.5) is the set
--   $$\operatorname{prox}_{\gamma h}(x)=\operatorname*{arg\,min}_{w}\Big\{h(w)+\tfrac1{2\gamma}\|w-x\|^2\Big\}.$$
--
--   **Image function (Definition 5.1, p. 17).** For $h:\mathbb R^n\to\overline{\mathbb R}$ and a linear map $C:\mathbb R^n\to\mathbb R^p$,
--   $$(Ch)(s)=\inf_{x\in\mathbb R^n}\{h(x)\mid Cx=s\}\in[-\infty,+\infty],$$
--   which is $+\infty$ off $C(\operatorname{dom}h)$. For $\beta>0$, $X_\beta(s)=\operatorname*{arg\,min}_x\{h(x)+\frac\beta2\|Cx-s\|^2\}$ (Proposition 5.2).
--
--   **ADMM (pp. 2, 18).** For problem (1.2), minimize $f(x)+g(z)$ subject to $Ax+Bz=b$, with $f:\mathbb R^m\to\overline{\mathbb R}$, $g:\mathbb R^n\to\overline{\mathbb R}$, $b\in\mathbb R^p$, the $\beta$-augmented Lagrangian (1.3) is
--   $$\mathcal L_\beta(x,z,y)=f(x)+g(z)+\langle y,Ax+Bz-b\rangle+\tfrac\beta2\|Ax+Bz-b\|^2 .$$
--   One ADMM update with penalty $\beta>0$ and relaxation $\lambda$ maps $(x,y,z)$ to $(x^+,y^+,z^+)$ by
--   $$y^{+/2}=y-\beta(1-\lambda)(Ax+Bz-b),\quad x^+\in\operatorname*{arg\,min}\mathcal L_\beta(\cdot,z,y^{+/2}),\quad y^+=y^{+/2}+\beta(Ax^++Bz-b),\quad z^+\in\operatorname*{arg\,min}\mathcal L_\beta(x^+,\cdot,y^+).$$
--   The penalty is *large enough* if every such $x$- and $z$-subproblem, for all data, has a minimizer. The cost of Assumption II.a5 is $\Phi(x,z)=f(x)+g(z)+\delta_S(x,z)$ with $S=\{(x,z)\mid Ax+Bz=b\}$.
--
--   **DRS objects (pp. 8, 10).** For $\varphi_1:\mathbb R^p\to\mathbb R$ smooth and $\varphi_2:\mathbb R^p\to\overline{\mathbb R}$, the Douglas–Rachford envelope (3.3) at $s$ is, for $u\in\operatorname{prox}_{\gamma\varphi_1}(s)$,
--   $$\varphi^{\mathrm{DR}}_\gamma(s)=\inf_{w}\Big\{\varphi_2(w)+\varphi_1(u)+\langle\nabla\varphi_1(u),w-u\rangle+\tfrac1{2\gamma}\|w-u\|^2\Big\}.$$
--   With $p=\sigma/L$ and $\delta=\sqrt{(p\lambda)^2-8p(\lambda-2)}$, the stepsize ranges of Theorem 4.1 are: $\lambda\in(0,2)$ and $\gamma<\min\{\frac{2-\lambda}{2[\sigma]_-},\frac1L\}$; or $\sigma>0$, $2\le\lambda<\frac4{1+\sqrt{1-p}}$ and $\frac{p\lambda-\delta}{4\sigma}<\gamma<\frac{p\lambda+\delta}{4\sigma}$. The decrease constants are
--   $$c=\frac{2-\lambda}{2\lambda\gamma}-\begin{cases}L\max\Big\{\frac{[p]_-}{2(1-[p]_-)},\ \frac{\gamma L}{\lambda}-\frac12\Big\}&\text{if }p\ge\frac\lambda2-1,\\[2pt] \frac{[\sigma]_-}{\lambda}&\text{otherwise,}\end{cases}\qquad c_{\mathrm{sc}}=\frac{2-\lambda}{2\lambda\gamma}+\sigma\Big(\frac12-\frac{\gamma L}{\lambda}\Big).$$
--
--   These objects carry the statement that ADMM on (1.2) is DRS on $\varphi_1=(Af)$, $\varphi_2=(Bg)(b-\cdot)$ with $\gamma=1/\beta$.
--
--   **Formalization Note** Points are `EuclideanSpace ℝ (Fin _)`, matrices are continuous linear maps, $A^\top$ is `ContinuousLinearMap.adjoint`. Extended-real functions are `EReal`-valued; `IsProper` also forbids $-\infty$. The image function is the `EReal` infimum over $\{x\mid Cx=s\}$, so it is $+\infty$ when that set is empty and may be $-\infty$. The proximal mapping and $X_\beta$ are sets, and ADMM updates are selections of minimizers. The two ADMM subproblems are written with the objective terms that depend on the minimized variable (`xObj`, `zObj`): $\mathcal L_\beta(\cdot,z,y)$ differs from `xObj` by the constant $g(z)$, which could be $+\infty$ at an arbitrary starting $z$ and would then make every $x$ a minimizer in $\overline{\mathbb R}$; dropping it is the standard meaning of the subproblem. The reciprocal bounds of Theorem 4.1 are multiplied out, so that $1/0=\infty$ is respected. The constant $c$ uses $\frac{\gamma L}\lambda-\frac12$ as derived in the proof of Theorem 4.1 ((4.8), p. 11) in place of the printed $\frac12-\frac{\gamma L}\lambda$, and $c_{\mathrm{sc}}$ is (4.10) of that proof in place of the printed (4.5); both corrections are the ones made in mission I of this series. This file declares `imageFn`, `Xbeta`, `augLag`, `xObj`, `zObj`, `IsADMMStep`, `SubproblemsSolvable`, `PhiADMM` and `dre`; the basic notions, `dreAt`, `deltaDR`, `StepRange`, `cDR` and `cDRsc` are imported from `NonconvexDRS.DRS.Setting`, and `proxSet` and `IsProper` from `NonconvexDRS.Tight.Setting`. Its `dre` is the same function as `NonconvexDRS.DRS.dre`, written over `NonconvexDRS.Tight.proxSet`.
-- source:
--   Themelis & Patrinos, Douglas-Rachford splitting and ADMM for nonconvex optimization: tight convergence results, arXiv:1709.05747v4, pp. 2, 5–8, 10–12, 17–20, (1.2), (ADMM), (1.3), (2.5), (3.3), Theorem 4.1 (4.3)–(4.5) with proof (4.8), (4.10), Definition 5.1, Proposition 5.2, Theorem 5.5, Assumption II

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexDRS_DRS_Setting
import Definitions.Def_NonconvexDRS_Tight_Setting

open NonconvexSplitting.Shared
open scoped InnerProductSpace

namespace NonconvexDRS.ADMM

noncomputable section

/-- The image function (Definition 5.1, p. 17): `(Ch)(s) := inf { h(x) | Cx = s }`, an infimum in
`[-∞, +∞]`; it is `+∞` when no `x` satisfies `Cx = s`. -/
def imageFn {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (C : E →L[ℝ] F) (h : E → EReal) (s : F) : EReal :=
  ⨅ (x : E) (_ : C x = s), h x

/-- The set `X_β(s) := argmin_x { h(x) + (β/2)‖Cx - s‖² }` of Proposition 5.2, p. 17. -/
def Xbeta {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (h : E → EReal) (C : E →L[ℝ] F) (β : ℝ) (s : F) : Set E :=
  {x | ∀ x', h x + ((β / 2 * ‖C x - s‖ ^ 2 : ℝ) : EReal) ≤
    h x' + ((β / 2 * ‖C x' - s‖ ^ 2 : ℝ) : EReal)}

/-- The `β`-augmented Lagrangian (1.3), p. 2:
`L_β(x, z, y) = f(x) + g(z) + ⟨y, Ax + Bz - b⟩ + (β/2)‖Ax + Bz - b‖²`. -/
def augLag {m n p : ℕ} (f : EuclideanSpace ℝ (Fin m) → EReal) (g : EuclideanSpace ℝ (Fin n) → EReal)
    (A : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin p))
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin p))
    (b : EuclideanSpace ℝ (Fin p)) (β : ℝ)
    (x : EuclideanSpace ℝ (Fin m)) (z : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin p)) :
    EReal :=
  f x + g z + ((⟪y, A x + B z - b⟫_ℝ + β / 2 * ‖A x + B z - b‖ ^ 2 : ℝ) : EReal)

/-- The `x`-subproblem objective of (ADMM): the terms of `L_β(·, z, y)` that depend on `x'`,
`f(x') + ⟨y, Ax' + Bz - b⟩ + (β/2)‖Ax' + Bz - b‖²` (the constant `g(z)` dropped). -/
def xObj {m n p : ℕ} (f : EuclideanSpace ℝ (Fin m) → EReal)
    (A : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin p))
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin p))
    (b : EuclideanSpace ℝ (Fin p)) (β : ℝ)
    (z : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin p)) (x' : EuclideanSpace ℝ (Fin m)) :
    EReal :=
  f x' + ((⟪y, A x' + B z - b⟫_ℝ + β / 2 * ‖A x' + B z - b‖ ^ 2 : ℝ) : EReal)

/-- The `z`-subproblem objective of (ADMM): the terms of `L_β(x, ·, y)` that depend on `z'`,
`g(z') + ⟨y, Ax + Bz' - b⟩ + (β/2)‖Ax + Bz' - b‖²` (the constant `f(x)` dropped). -/
def zObj {m n p : ℕ} (g : EuclideanSpace ℝ (Fin n) → EReal)
    (A : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin p))
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin p))
    (b : EuclideanSpace ℝ (Fin p)) (β : ℝ)
    (x : EuclideanSpace ℝ (Fin m)) (y : EuclideanSpace ℝ (Fin p)) (z' : EuclideanSpace ℝ (Fin n)) :
    EReal :=
  g z' + ((⟪y, A x + B z' - b⟫_ℝ + β / 2 * ‖A x + B z' - b‖ ^ 2 : ℝ) : EReal)

/-- One (ADMM) update (p. 2) with penalty `β` and relaxation `λ` (`lam`), from `(x, y, z)` to
`(x⁺, y⁺, z⁺)` (`xp`, `yp`, `zp`), in selection form:
`y^{+/2} = y - β(1 - λ)(Ax + Bz - b)`, `x⁺ ∈ argmin L_β(·, z, y^{+/2})`,
`y⁺ = y^{+/2} + β(Ax⁺ + Bz - b)`, `z⁺ ∈ argmin L_β(x⁺, ·, y⁺)`. -/
def IsADMMStep {m n p : ℕ} (f : EuclideanSpace ℝ (Fin m) → EReal)
    (g : EuclideanSpace ℝ (Fin n) → EReal)
    (A : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin p))
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin p))
    (b : EuclideanSpace ℝ (Fin p)) (β lam : ℝ)
    (x : EuclideanSpace ℝ (Fin m)) (y : EuclideanSpace ℝ (Fin p)) (z : EuclideanSpace ℝ (Fin n))
    (xp : EuclideanSpace ℝ (Fin m)) (yp : EuclideanSpace ℝ (Fin p))
    (zp : EuclideanSpace ℝ (Fin n)) : Prop :=
  let yh := y - (β * (1 - lam)) • (A x + B z - b)
  (∀ x', xObj f A B b β z yh xp ≤ xObj f A B b β z yh x') ∧
  yp = yh + β • (A xp + B z - b) ∧
  (∀ z', zObj g A B b β xp yp zp ≤ zObj g A B b β xp yp z')

/-- "The penalty `β` is large enough that every ADMM minimization subproblem has solutions"
(Theorem 5.5, p. 18; Assumption II.a2, p. 19): both subproblems have a minimizer for all data. -/
def SubproblemsSolvable {m n p : ℕ} (f : EuclideanSpace ℝ (Fin m) → EReal)
    (g : EuclideanSpace ℝ (Fin n) → EReal)
    (A : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin p))
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin p))
    (b : EuclideanSpace ℝ (Fin p)) (β : ℝ) : Prop :=
  (∀ z y, ∃ x, ∀ x', xObj f A B b β z y x ≤ xObj f A B b β z y x') ∧
  (∀ x y, ∃ z, ∀ z', zObj g A B b β x y z ≤ zObj g A B b β x y z')

/-- The cost `Φ(x, z) := f(x) + g(z) + δ_S(x, z)` of Assumption II.a5, p. 20, with
`S = {(x, z) | Ax + Bz = b}`. -/
def PhiADMM {m n p : ℕ} (f : EuclideanSpace ℝ (Fin m) → EReal)
    (g : EuclideanSpace ℝ (Fin n) → EReal)
    (A : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin p))
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin p))
    (b : EuclideanSpace ℝ (Fin p))
    (xz : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) : EReal :=
  if A xz.1 + B xz.2 = b then f xz.1 + g xz.2 else ⊤

/-- The Douglas–Rachford envelope (3.3), p. 8: `φ^DR_γ(s)` is the value of (3.3) at
`u ∈ prox_{γφ₁}(s)`, taken as the infimum over the proximal set (the page's value whenever
`prox_{γφ₁}(s)` is a singleton, e.g. for `γ L < 1`). -/
def dre {p : ℕ} (φ₁ : EuclideanSpace ℝ (Fin p) → ℝ) (φ₂ : EuclideanSpace ℝ (Fin p) → EReal)
    (γ : ℝ) (s : EuclideanSpace ℝ (Fin p)) : EReal :=
  ⨅ u ∈ NonconvexDRS.Tight.proxSet (fun x => (φ₁ x : EReal)) γ s, NonconvexDRS.DRS.dreAt φ₁ φ₂ γ u

end

end NonconvexDRS.ADMM


