-- Prove2me | Definitions.Def_NonconvexDRS_Tight_Setting
-- name    : NonconvexDRS_Tight_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T15:36:09.335099+00:00
-- url     : https://prove2.me/theorems/e998c9f1-3a4c-4cc1-954d-e31be1c35940
-- title:
--   pp. 1, 5–7, 16 — proper functions, L-smoothness, σ-hypoconvexity, the proximal set (2.5), DRS runs and fixed points, and the one-dimensional example (4.12)
-- statement:
--   This file fixes the objects in which Theorems 4.7 and 4.8 of Themelis and Patrinos are stated. Throughout, $E$ is a real Hilbert space (in the theorems, $E=\mathbb R^p$ or $E=\mathbb R$) and $\overline{\mathbb R}=\mathbb R\cup\{+\infty\}$.
--
--   1. **Negative part.** For $r\in\mathbb R$, $[r]_-:=\max\{0,-r\}$ (imported from `NonconvexDRS.DRS.Setting`).
--   2. **Proper.** A function $h:E\to\overline{\mathbb R}$ is proper if it never takes the value $-\infty$ and $\operatorname{dom}h=\{x\mid h(x)<\infty\}$ is nonempty.
--   3. **$L$-smooth.** A function $h:E\to\mathbb R$ is $L$-smooth if it is differentiable and $\|\nabla h(x)-\nabla h(y)\|\le L\|x-y\|$ for all $x,y$.
--   4. **$\sigma$-hypoconvex.** $h:E\to\mathbb R$ is $\sigma$-hypoconvex if $h-\tfrac{\sigma}{2}\|\cdot\|^2$ is convex. For $\sigma>0$ this is $\sigma$-strong convexity.
--   5. **Proximal mapping (2.5).** For $h:E\to\overline{\mathbb R}$ and $\gamma>0$, $$\operatorname{prox}_{\gamma h}(x)=\operatorname*{arg\,min}_{w\in E}\Big\{h(w)+\tfrac1{2\gamma}\|w-x\|^2\Big\},$$ a possibly empty, possibly multivalued set.
--   6. **DRS run.** Given $\varphi_1:E\to\mathbb R$, $\varphi_2:E\to\overline{\mathbb R}$, a stepsize $\gamma$ and a relaxation $\lambda$, sequences $(s^k,u^k,v^k)_{k\in\mathbb N}$ form a DRS run if for every $k$ $$u^k\in\operatorname{prox}_{\gamma\varphi_1}(s^k),\qquad v^k\in\operatorname{prox}_{\gamma\varphi_2}(2u^k-s^k),\qquad s^{k+1}=s^k+\lambda(v^k-u^k).$$ Any selection from the proximal sets is allowed.
--   7. **Fixed point.** $s$ is a fixed point of the DR-iteration if some admissible step leaves it unchanged, i.e. there is $u\in\operatorname{prox}_{\gamma\varphi_1}(s)$ with $u\in\operatorname{prox}_{\gamma\varphi_2}(2u-s)$ (take $v=u$, so that $s^+=s$ for every $\lambda>0$).
--   8. **Strong convexity in $\overline{\mathbb R}$.** A function $h:E\to\overline{\mathbb R}$ that never takes the value $-\infty$ is strongly convex if for some $\mu>0$ the function $h-\tfrac\mu2\|\cdot\|^2$ is convex, i.e. $\operatorname{dom}h$ is convex and $h-\tfrac\mu2\|\cdot\|^2$ is convex on it.
--   9. **Indicator.** $\delta_S(x)=0$ for $x\in S$ and $+\infty$ otherwise.
--   10. **The example (4.12).** For $L,\sigma,t\in\mathbb R$, $\varphi_1:\mathbb R\to\mathbb R$ is $$\varphi_1(x)=\begin{cases}\tfrac L2x^2 & x\le t,\\ \tfrac L2x^2-\tfrac{L-\sigma}2(x-t)^2 & \text{otherwise.}\end{cases}$$
--   11. **Set-valued sign.** $\operatorname{sgn}(x)=\{1\}$ for $x>0$, $\{-1\}$ for $x<0$, and $\operatorname{sgn}(0)=\{\pm1\}$.
--
--   These are the objects of the paper's problem (1.1), the DRS scheme of p. 1, and the counterexamples of §4.2.
--
--   **Formalization Note** $\overline{\mathbb R}$ is `EReal`; properness excludes $-\infty$. The proximal mapping is a set, never a chosen function, so a run is any selection. The fixed-point notion asks for an admissible step with $v=u$, which is the paper's "$s^+=s$" for $\lambda>0$. In the strong-convexity definition, the real value of $h$ is used only on $\operatorname{dom}h$, where it is finite.
-- source:
--   Themelis & Patrinos, Douglas-Rachford splitting and ADMM for nonconvex optimization: tight convergence results, arXiv:1709.05747v4, p. 1 (DRS) and the fixed-point sentence, p. 5 (notation), p. 6 §2.2, p. 7 (2.5), p. 16 (4.12) and sgn(0) = {±1}

import Mathlib
import Definitions.Def_NonconvexDRS_DRS_Setting

namespace NonconvexDRS.Tight

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- `h : E → ℝ̄` is proper (p. 5): it never takes the value `-∞` and `dom h ≠ ∅`. -/
def IsProper (h : E → EReal) : Prop := (∀ x, h x ≠ ⊥) ∧ ∃ x, h x ≠ ⊤

/-- `h` is `L`-smooth (§2.2, p. 6): differentiable with `L`-Lipschitz gradient. -/
def IsLSmooth (h : E → ℝ) (L : ℝ) : Prop :=
  Differentiable ℝ h ∧ ∀ x y, ‖gradient h x - gradient h y‖ ≤ L * ‖x - y‖

/-- `h` is `σ`-hypoconvex (§2.2, p. 6): `h - (σ/2)‖·‖²` is convex. -/
def IsHypoconvex (h : E → ℝ) (σ : ℝ) : Prop :=
  ConvexOn ℝ Set.univ (fun x => h x - σ / 2 * ‖x‖ ^ 2)

/-- The proximal mapping (2.5) as a set:
`prox_{γh}(x) = argmin_w { h(w) + ‖w - x‖² / (2γ) }`. -/
def proxSet (h : E → EReal) (γ : ℝ) (x : E) : Set E :=
  {w | ∀ w', h w + ((‖w - x‖ ^ 2 / (2 * γ) : ℝ) : EReal) ≤
    h w' + ((‖w' - x‖ ^ 2 / (2 * γ) : ℝ) : EReal)}

/-- A DRS run (p. 1) with stepsize `γ` and relaxation `lam`, as a selection:
`uᵏ ∈ prox_{γφ₁}(sᵏ)`, `vᵏ ∈ prox_{γφ₂}(2uᵏ - sᵏ)`, `sᵏ⁺¹ = sᵏ + λ(vᵏ - uᵏ)`. -/
def IsDRSRun (φ₁ : E → ℝ) (φ₂ : E → EReal) (γ lam : ℝ) (s u v : ℕ → E) : Prop :=
  ∀ k, u k ∈ proxSet (fun x => (φ₁ x : EReal)) γ (s k) ∧
    v k ∈ proxSet φ₂ γ (2 • u k - s k) ∧ s (k + 1) = s k + lam • (v k - u k)

/-- `s` is a fixed point of the DR-iteration (p. 1): some admissible step has `s⁺ = s`,
i.e. some `u ∈ prox_{γφ₁}(s)` satisfies `u ∈ prox_{γφ₂}(2u - s)` (take `v = u`). -/
def IsDRSFixedPoint (φ₁ : E → ℝ) (φ₂ : E → EReal) (γ : ℝ) (s : E) : Prop :=
  ∃ u ∈ proxSet (fun x => (φ₁ x : EReal)) γ s, u ∈ proxSet φ₂ γ (2 • u - s)

/-- `h : E → ℝ̄` (never `-∞`) is strongly convex: for some `μ > 0`, `h - (μ/2)‖·‖²` is
convex as an extended-real function, i.e. `dom h` is convex and the real function
`h - (μ/2)‖·‖²` is convex on `dom h`. -/
def IsStronglyConvexE (h : E → EReal) : Prop :=
  (∀ x, h x ≠ ⊥) ∧ ∃ μ : ℝ, 0 < μ ∧
    ConvexOn ℝ {x | h x ≠ ⊤} (fun x => (h x).toReal - μ / 2 * ‖x‖ ^ 2)

end General

/-- The indicator `δ_S` of a set: `0` on `S`, `+∞` off `S`. -/
noncomputable def indic {α : Type*} (S : Set α) (x : α) : EReal :=
  open Classical in if x ∈ S then 0 else ⊤

/-- The function (4.12) on `ℝ`:
`φ₁(x) = (L/2)x²` for `x ≤ t`, and `(L/2)x² - ((L-σ)/2)(x-t)²` otherwise. -/
noncomputable def phi1Ex (L σ t : ℝ) (x : ℝ) : ℝ :=
  if x ≤ t then L / 2 * x ^ 2 else L / 2 * x ^ 2 - (L - σ) / 2 * (x - t) ^ 2

/-- The set-valued sign on `ℝ`, with `sgn(0) = {±1}` (p. 16). -/
def sgnSet (x : ℝ) : Set ℝ :=
  if 0 < x then {1} else if x < 0 then {-1} else {-1, 1}

end NonconvexDRS.Tight


