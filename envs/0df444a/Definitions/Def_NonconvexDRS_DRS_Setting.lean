-- Prove2me | Definitions.Def_NonconvexDRS_DRS_Setting
-- name    : NonconvexDRS_DRS_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T14:45:11.016285+00:00
-- url     : https://prove2.me/theorems/c3267043-b4c2-4101-ad30-bd3987f8f7f4
-- title:
--   §1–§4, pp. 1–10 — proper/level-bounded functions, L-smooth σ-hypoconvex φ₁, the proximal set (2.5), DRS runs, the Douglas–Rachford envelope (3.3), the ranges and constants of Theorem 4.1
-- statement:
--   This file fixes the objects of the nonconvex Douglas–Rachford splitting (DRS) analysis of Themelis and Patrinos. Throughout, $\mathbb R^p$ is the Euclidean space with inner product $\langle\cdot,\cdot\rangle$ and norm $\|\cdot\|$, and $\overline{\mathbb R}=\mathbb R\cup\{\infty\}$.
--
--   **Basic notions (p. 5).** The negative part of $r\in\mathbb R$ is $[r]_-=\max\{0,-r\}$. A function $h:\mathbb R^n\to\overline{\mathbb R}$ is *proper* if $\operatorname{dom}h=\{x\mid h(x)<\infty\}\neq\emptyset$, and *level bounded* if every level set $\operatorname{lev}_{\le\alpha}h=\{x\mid h(x)\le\alpha\}$, $\alpha\in\mathbb R$, is bounded.
--
--   **Smoothness and hypoconvexity (§2.2, p. 6).** A differentiable $h:\mathbb R^n\to\mathbb R$ is *$L$-smooth* if $\|\nabla h(x)-\nabla h(y)\|\le L\|x-y\|$ for all $x,y$, and *$\sigma$-hypoconvex* if $h-\frac\sigma2\|\cdot\|^2$ is convex ($\sigma>0$ is $\sigma$-strong convexity, $\sigma<0$ allows nonconvexity).
--
--   **Proximal mapping (2.5), p. 7.** For $\gamma>0$,
--   $$\operatorname{prox}_{\gamma h}(x)=\operatorname*{arg\,min}_{w\in\mathbb R^n}\Big\{h(w)+\tfrac1{2\gamma}\|w-x\|^2\Big\},$$
--   a possibly empty or multivalued set.
--
--   **Problem and DRS (p. 1).** The problem is to minimize $\varphi=\varphi_1+\varphi_2$ with $\varphi_1:\mathbb R^p\to\mathbb R$ and $\varphi_2:\mathbb R^p\to\overline{\mathbb R}$. A DRS run with stepsize $\gamma$ and relaxation $\lambda$ is a sequence $(s^k,u^k,v^k)_{k\in\mathbb N}$ with
--   $$u^k\in\operatorname{prox}_{\gamma\varphi_1}(s^k),\qquad v^k\in\operatorname{prox}_{\gamma\varphi_2}(2u^k-s^k),\qquad s^{k+1}=s^k+\lambda(v^k-u^k).$$
--
--   **Douglas–Rachford envelope (3.3), p. 8.** For $u\in\operatorname{prox}_{\gamma\varphi_1}(s)$,
--   $$\varphi^{\mathrm{DR}}_\gamma(s)=\inf_{w\in\mathbb R^p}\Big\{\varphi_2(w)+\varphi_1(u)+\langle\nabla\varphi_1(u),w-u\rangle+\tfrac1{2\gamma}\|w-u\|^2\Big\}.$$
--
--   **Ranges and constants of Theorem 4.1 (p. 10).** With $p=\sigma/L$ and $\delta=\sqrt{(p\lambda)^2-8p(\lambda-2)}$, the admissible pairs $(\gamma,\lambda)$ are: either $\lambda\in(0,2)$ and $\gamma<\min\{\frac{2-\lambda}{2[\sigma]_-},\frac1L\}$ (with $1/0=\infty$); or $\sigma>0$, $2\le\lambda<\frac4{1+\sqrt{1-p}}$ and $\frac{p\lambda-\delta}{4\sigma}<\gamma<\frac{p\lambda+\delta}{4\sigma}$. The sufficient-decrease constants are
--   $$c=\frac{2-\lambda}{2\lambda\gamma}-\begin{cases}L\max\Big\{\frac{[p]_-}{2(1-[p]_-)},\ \frac{\gamma L}{\lambda}-\frac12\Big\}&\text{if }p\ge\frac\lambda2-1,\\[2pt] \frac{[\sigma]_-}{\lambda}&\text{otherwise,}\end{cases}\qquad c_{\mathrm{sc}}=\frac{2-\lambda}{2\lambda\gamma}+\sigma\Big(\frac12-\frac{\gamma L}{\lambda}\Big).$$
--
--   These objects are the vocabulary of every statement of the mission: the DRE is the Lyapunov function along which DRS decreases.
--
--   **Formalization Note** Points are `EuclideanSpace ℝ (Fin p)`. Extended-real functions are `EReal`-valued and never `⊥`; `IsProper` requires this. The proximal mapping is the set `proxSet`, and runs are selections from it; no prox function is chosen. The DRE `dre` is the `EReal` infimum of (3.3) over $u\in\operatorname{prox}_{\gamma\varphi_1}(s)$, which equals the page's value whenever that prox is a singleton (for $\gamma L<1$, by Proposition 2.3(i)). Reciprocal bounds are multiplied out ($\gamma L<1$, $2\gamma[\sigma]_-<2-\lambda$), so that $1/0=\infty$ is respected. The second entry of the max in $c$ is $\frac{\gamma L}{\lambda}-\frac12$, as derived in the proof of Theorem 4.1 ((4.8), p. 11), whereas the printed (4.3) has $\frac12-\frac{\gamma L}\lambda$, which is false; $c_{\mathrm{sc}}$ is (4.10) of the proof, whereas the printed (4.5) has $\frac{\sigma}{\lambda}$ in place of $\sigma$ and is then not always positive. See the theorem item `theorem_4_1`.
-- source:
--   Themelis & Patrinos, Douglas-Rachford splitting and ADMM for nonconvex optimization: tight convergence results, arXiv:1709.05747v4, pp. 1, 5–8, 10–12, (1.1), (DRS), §2.1 notation, §2.2, (2.5), (3.3), Theorem 4.1 (4.3)–(4.5), proof (4.8), (4.10)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff

open NonconvexSplitting.Shared
open scoped InnerProductSpace

namespace NonconvexDRS.DRS

noncomputable section

/-- The negative part `[r]₋ := max {0, -r}` (p. 5). -/
def negPartR (r : ℝ) : ℝ := max 0 (-r)

/-- An extended-real-valued function `h : ℝⁿ → ℝ ∪ {∞}` (never `-∞`) is proper (p. 5) if its
domain `dom h = {x | h x < ∞}` is nonempty. -/
def IsProper {n : ℕ} (h : EuclideanSpace ℝ (Fin n) → EReal) : Prop :=
  (∀ x, h x ≠ ⊥) ∧ ∃ x, h x ≠ ⊤

/-- `h` is level bounded (p. 5): every level set `lev_{≤α} h = {x | h x ≤ α}`, `α ∈ ℝ`, is
bounded. -/
def LevelBounded {n : ℕ} (h : EuclideanSpace ℝ (Fin n) → EReal) : Prop :=
  ∀ α : ℝ, Bornology.IsBounded {x | h x ≤ (α : EReal)}

/-- `h ∈ C^{1,1}(ℝⁿ)` is `L`-smooth (§2.2, p. 6): `h` is differentiable and `∇h` is Lipschitz
continuous with modulus `L`. -/
def IsLSmooth {n : ℕ} (h : EuclideanSpace ℝ (Fin n) → ℝ) (L : ℝ) : Prop :=
  Differentiable ℝ h ∧ ∀ x y, ‖gradient h x - gradient h y‖ ≤ L * ‖x - y‖

/-- `h` is `σ`-hypoconvex (§2.2, p. 6): `h - (σ/2)‖·‖²` is convex. -/
def IsHypoconvex {n : ℕ} (h : EuclideanSpace ℝ (Fin n) → ℝ) (σ : ℝ) : Prop :=
  ConvexOn ℝ Set.univ (fun x => h x - σ / 2 * ‖x‖ ^ 2)

/-- The proximal mapping (2.5), p. 7, as a set:
`prox_{γh}(x) = argmin_w { h(w) + ‖w - x‖² / (2γ) }`. -/
def proxSet {n : ℕ} (h : EuclideanSpace ℝ (Fin n) → EReal) (γ : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {w | ∀ w', h w + ((‖w - x‖ ^ 2 / (2 * γ) : ℝ) : EReal) ≤
    h w' + ((‖w' - x‖ ^ 2 / (2 * γ) : ℝ) : EReal)}

/-- The cost `φ = φ₁ + φ₂` of problem (1.1), p. 1, with `φ₁` real-valued and `φ₂` extended-real. -/
def phi {p : ℕ} (φ₁ : EuclideanSpace ℝ (Fin p) → ℝ) (φ₂ : EuclideanSpace ℝ (Fin p) → EReal)
    (x : EuclideanSpace ℝ (Fin p)) : EReal :=
  (φ₁ x : EReal) + φ₂ x

/-- A DRS run (p. 1) with stepsize `γ` and relaxation `λ` (`lam`): for every `k`,
`uᵏ ∈ prox_{γφ₁}(sᵏ)`, `vᵏ ∈ prox_{γφ₂}(2uᵏ - sᵏ)` and `s^{k+1} = sᵏ + λ(vᵏ - uᵏ)`. -/
def IsDRSRun {p : ℕ} (φ₁ : EuclideanSpace ℝ (Fin p) → ℝ) (φ₂ : EuclideanSpace ℝ (Fin p) → EReal)
    (γ lam : ℝ) (s u v : ℕ → EuclideanSpace ℝ (Fin p)) : Prop :=
  ∀ k, u k ∈ proxSet (fun x => (φ₁ x : EReal)) γ (s k) ∧
    v k ∈ proxSet φ₂ γ ((2 : ℝ) • u k - s k) ∧
    s (k + 1) = s k + lam • (v k - u k)

/-- The value of the minimization problem (3.3) at the point `u`:
`inf_w { φ₂(w) + φ₁(u) + ⟨∇φ₁(u), w - u⟩ + ‖w - u‖² / (2γ) }`. -/
def dreAt {p : ℕ} (φ₁ : EuclideanSpace ℝ (Fin p) → ℝ) (φ₂ : EuclideanSpace ℝ (Fin p) → EReal)
    (γ : ℝ) (u : EuclideanSpace ℝ (Fin p)) : EReal :=
  ⨅ w, φ₂ w + ((φ₁ u + ⟪gradient φ₁ u, w - u⟫_ℝ + ‖w - u‖ ^ 2 / (2 * γ) : ℝ) : EReal)

/-- The Douglas–Rachford envelope (3.3), p. 8: `φ^DR_γ(s)` is the value of (3.3) at
`u ∈ prox_{γφ₁}(s)`. Taken as the infimum over the proximal set, it is the page's value whenever
`prox_{γφ₁}(s)` is a singleton (Proposition 2.3(i), e.g. for `γ L < 1`). -/
def dre {p : ℕ} (φ₁ : EuclideanSpace ℝ (Fin p) → ℝ) (φ₂ : EuclideanSpace ℝ (Fin p) → EReal)
    (γ : ℝ) (s : EuclideanSpace ℝ (Fin p)) : EReal :=
  ⨅ u ∈ proxSet (fun x => (φ₁ x : EReal)) γ s, dreAt φ₁ φ₂ γ u

/-- `δ := √((pλ)² − 8p(λ − 2))` of (4.4), p. 10, with `p = σ / L`. -/
def deltaDR (L σ lam : ℝ) : ℝ :=
  Real.sqrt ((σ / L * lam) ^ 2 - 8 * (σ / L) * (lam - 2))

/-- The stepsize and relaxation ranges of Theorem 4.1, p. 10, with `p = σ / L`, reciprocal bounds
multiplied out (convention `1/0 = ∞`, p. 5):
either `λ ∈ (0, 2)` and `γ < min {(2 - λ) / (2[σ]₋), 1 / L}`,
or `σ > 0` (`φ₁` strongly convex) and the range (4.4)
`2 ≤ λ < 4 / (1 + √(1 - p))`, `(pλ - δ) / (4σ) < γ < (pλ + δ) / (4σ)`. -/
def StepRange (L σ γ lam : ℝ) : Prop :=
  (0 < lam ∧ lam < 2 ∧ γ * L < 1 ∧ 2 * γ * negPartR σ < 2 - lam) ∨
  (0 < σ ∧ 2 ≤ lam ∧ lam * (1 + Real.sqrt (1 - σ / L)) < 4 ∧
    σ / L * lam - deltaDR L σ lam < 4 * σ * γ ∧ 4 * σ * γ < σ / L * lam + deltaDR L σ lam)

/-- The sufficient-decrease constant of Theorem 4.1 for `λ ∈ (0, 2)`, (4.3) p. 10, **with the sign
of the second entry of the max corrected** to `γL/λ - 1/2` as derived in the proof (Case 1a,
(4.8) p. 11): `c = (2-λ)/(2λγ) - L max {[p]₋/(2(1-[p]₋)), γL/λ - 1/2}` if `p ≥ λ/2 - 1`, and
`c = (2-λ)/(2λγ) - [σ]₋/λ` otherwise, where `p = σ / L`. -/
def cDR (L σ γ lam : ℝ) : ℝ :=
  (2 - lam) / (2 * lam * γ) -
    (if lam / 2 - 1 ≤ σ / L then
      L * max (negPartR (σ / L) / (2 * (1 - negPartR (σ / L)))) (γ * L / lam - 1 / 2)
     else negPartR σ / lam)

/-- The sufficient-decrease constant of Theorem 4.1 in the strongly convex case (4.4), as derived in
the proof, (4.10) p. 12: `c = (2-λ)/(2λγ) + σ(1/2 - γL/λ)` (the printed (4.5) carries an extra
factor `1/λ` on the second term). -/
def cDRsc (L σ γ lam : ℝ) : ℝ :=
  (2 - lam) / (2 * lam * γ) + σ * (1 / 2 - γ * L / lam)

end

end NonconvexDRS.DRS


