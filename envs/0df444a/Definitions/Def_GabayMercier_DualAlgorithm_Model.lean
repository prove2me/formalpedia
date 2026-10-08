-- Prove2me | Definitions.Def_GabayMercier_DualAlgorithm_Model
-- name    : GabayMercier_DualAlgorithm_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T09:38:12.82278+00:00
-- url     : https://prove2.me/theorems/98261559-e52b-4cd6-926e-5f4a04301276
-- title:
--   (𝒫), (2.2)–(2.5), (1.1)–(1.2), (3.4) — the problem, standing hypotheses, Lagrangians and the modified dual algorithm
-- statement:
--   This file fixes the setting of Sections 1–3 of Gabay and Mercier.
--
--   **Spaces and data.** $V$ and $Y$ are real Hilbert spaces with inner products $((\cdot,\cdot))$, $(\cdot,\cdot)$ and norms $\|\cdot\|$, $|\cdot|$. $A:V\to Y$ is a continuous linear operator, $b\in V'$ is a continuous linear functional on $V$ (the pairing is written $\langle b,v\rangle$), and the dual $Y'$ is identified with $Y$, so Lagrange multipliers $\lambda$ are elements of $Y$. The function $f:Y\to(-\infty,+\infty]$ is the sum (2.2)
--   $$f=f_1+f_2 .$$
--
--   **Problem (𝒫).** Minimize the **objective**
--   $$J(v)=f(Av)-\langle b,v\rangle=f_1(Av)-\langle b,v\rangle+f_2(Av),\qquad v\in V .$$
--   A **solution** of (𝒫) is a point $v^*$ with $J(v^*)<+\infty$ and $J(v^*)\le J(w)$ for every $w\in V$.
--
--   **Standing hypotheses** (p. 8), with constants $\gamma,\alpha$:
--   1. $f_1:Y\to\mathbb R$ is convex and continuously differentiable, with gradient $f_1'$;
--   2. (2.3) $f_1'$ is strongly monotone: $(f_1'(y)-f_1'(z),\,y-z)\ge\gamma|y-z|^2$ for all $y,z$, with $\gamma>0$;
--   3. $f_2$ is proper (never $-\infty$, not identically $+\infty$), convex and lower semicontinuous;
--   4. (2.5) there is $\alpha>0$ with $|Av|^2\ge\alpha^2\|v\|^2$ for all $v\in V$.
--
--   **Qualification hypothesis.** Some point of the range of $A$ lies in the interior of $\operatorname{dom}f_2=\{y: f_2(y)<+\infty\}$:
--   $$\exists v_0\in V,\qquad Av_0\in\operatorname{int}\operatorname{dom}f_2 .$$
--
--   **Lagrangians.** For $v\in V$, $y,\lambda\in Y$ and $r\in\mathbb R$,
--   $$\mathcal L(v,y;\lambda)=f(y)+(\lambda,Av-y)-\langle b,v\rangle,\qquad \mathcal L_r(v,y;\lambda)=f(y)+(\lambda,Av-y)+\frac r2|Av-y|^2-\langle b,v\rangle .$$
--   A **saddle point** of a function $L$ on $(V\times Y)\times Y$ is a triple $(v^*,y^*;\lambda^*)$ with
--   $$L(v^*,y^*;\lambda)\le L(v^*,y^*;\lambda^*)\le L(v,y;\lambda^*)\qquad\text{for all }(v,y)\in V\times Y,\ \lambda\in Y .$$
--
--   **The modified dual algorithm (3.4).** Given $r,\rho$, sequences $(v^n,y^n,\lambda^n)_{n\ge0}$ form a run if, for every $n\ge0$:
--   1. (Step 1, (3.5)) $r(Av^{n+1},Aw)=(ry^n-\lambda^n,Aw)+\langle b,w\rangle$ for all $w\in V$;
--   2. (Step 2, (3.6)) $(f_1'(y^{n+1}),y-y^{n+1})+f_2(y)-f_2(y^{n+1})+(ry^{n+1}-\lambda^n-rAv^{n+1},\,y-y^{n+1})\ge0$ for all $y\in Y$, with $f_2(y^{n+1})<+\infty$; equivalently $\lambda^n+rAv^{n+1}-ry^{n+1}-f_1'(y^{n+1})\in\partial f_2(y^{n+1})$;
--   3. (Step 3, (3.7)) $\lambda^{n+1}=\lambda^n+\rho(Av^{n+1}-y^{n+1})$.
--
--   The start $(y^0,\lambda^0)$ is arbitrary and $v^0$ plays no role.
--
--   **Projection.** $P$ is the orthogonal projection of $Y$ onto the closure of the range $R(A)$; under (2.5) the range is closed, and $Py$ is the unique element of $R(A)$ with $(Py,Av)=(y,Av)$ for all $v$. $I-P$ is the complementary projection onto $R(A)^\perp$.
--
--   These objects are used by every statement of the mission: Proposition 2.1, Theorems 2.1–2.2, the estimates (3.8)–(3.24) and Theorem 3.1.
--
--   **Formalization Note.** $f_2$ takes values in `EReal`; properness, convexity (of the epigraph) and the subdifferential $\partial f_2$ are the published `IsProperFn`, `IsConvexFn`, `IsSubgradient` of `InertialFB.IFB.ConvexAnalysis`, where `IsSubgradient f₂ u g` means $f_2(u)\ne+\infty$ and $f_2(u)+(g,v-u)\le f_2(v)$ for all $v$. The paper's inequality (3.6) is rearranged into this form so that no subtraction in `EReal` occurs; for a proper $f_2$ the printed inequality forces $f_2(y^{n+1})<+\infty$, so nothing is added. The paper writes $f_1$ with values in $(-\infty,+\infty]$, but a Gateaux-differentiable function is finite, so $f_1:Y\to\mathbb R$; "C¹ Gateaux-differentiable" is encoded as a gradient at every point that is continuous in the point (a continuous Gateaux derivative is a Fréchet derivative), and "$f_1'$ weakly continuous on finite-dimensional subspaces" then holds automatically. $b$ is a `StrongDual ℝ V`. Two deliberate departures from the printed text: (i) Step 1 is written with $+\langle b,w\rangle$; the paper prints $-\langle b,v\rangle$ in (3.5) (and in (3.8) and Remark 1, p. 15), but the minimization of $\mathcal L_r(\cdot,y^n;\lambda^n)$, which (3.5) is meant to express, gives $+\langle b,v\rangle$; with the printed sign the algorithm solves (𝒫) with $-b$ in place of $b$. (ii) The paper's qualification (2.4) "the interior of $\operatorname{dom}f_2$ is non empty" is replaced by the stronger $\operatorname{int}\operatorname{dom}f_2\cap R(A)\ne\emptyset$; (2.4) as printed does not give the saddle point of Theorem 2.1 (see that theorem). (2.4) itself is implied and so not stated separately. $P$ is the projection onto the closure of $R(A)$, which is $R(A)$ under (2.5).
-- source:
--   Gabay & Mercier, IRIA RR-126 (1975), hal-04716124v1, pp. 1–2 ((1.1), (1.2), footnote), p. 8 ((𝒫), (2.2)–(2.5)), p. 10 (ℒ), p. 12 (ℒ_r), p. 15 ((3.4)–(3.7)), p. 16 (P)

import Mathlib
import Definitions.Def_InertialFB_IFB_ConvexAnalysis

open Filter Topology InertialFB.IFB

namespace GabayMercier.DualAlgorithm

variable {V Y : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- The objective of (𝒫), `f(Av) − ⟨b, v⟩` with `f = f₁ + f₂` (2.2), valued in `(−∞, +∞]`. -/
noncomputable def objective (A : V →L[ℝ] Y) (f₁ : Y → ℝ) (f₂ : Y → EReal) (b : StrongDual ℝ V)
    (v : V) : EReal :=
  ((f₁ (A v) - b v : ℝ) : EReal) + f₂ (A v)

/-- `v` is a solution of (𝒫): finite value, and minimal. -/
def IsSolution (A : V →L[ℝ] Y) (f₁ : Y → ℝ) (f₂ : Y → EReal) (b : StrongDual ℝ V) (v : V) : Prop :=
  objective A f₁ f₂ b v ≠ ⊤ ∧ ∀ w, objective A f₁ f₂ b v ≤ objective A f₁ f₂ b w

/-- Standing hypotheses (2.2), (2.3), (2.5) of p. 8, with their constants `γ` and `α`:
`f₁` is convex and C¹ (gradient `f₁'`) with strongly monotone gradient, `f₂` is proper, convex and
lower semicontinuous, and `|Av|² ≥ α²‖v‖²`. The qualification hypothesis (2.4) is kept separate,
see `Qualification`. -/
structure StandingHyp (A : V →L[ℝ] Y) (f₁ : Y → ℝ) (f₁' : Y → Y) (f₂ : Y → EReal)
    (γ α : ℝ) : Prop where
  f₁_convex : ConvexOn ℝ Set.univ f₁
  f₁_hasGradient : ∀ y, HasGradientAt f₁ (f₁' y) y
  f₁'_continuous : Continuous f₁'
  γ_pos : 0 < γ
  strongMono : ∀ y z, γ * ‖y - z‖ ^ 2 ≤ inner ℝ (f₁' y - f₁' z) (y - z)
  f₂_proper : IsProperFn f₂
  f₂_convex : IsConvexFn f₂
  f₂_lsc : LowerSemicontinuous f₂
  α_pos : 0 < α
  bddBelow : ∀ v, α ^ 2 * ‖v‖ ^ 2 ≤ ‖A v‖ ^ 2

/-- The qualification hypothesis: some point `A v₀` of the range of `A` lies in the interior of
`dom f₂`. This strengthens the paper's (2.4) ("the interior in `Y` of `dom f₂` is non empty"),
which is not sufficient for the existence of a saddle point; it is the hypothesis of the result
the paper cites for the chain rule ([E] ch. 1, PR 5.7) and the one stated in Remark 2, p. 11. -/
def Qualification (A : V →L[ℝ] Y) (f₂ : Y → EReal) : Prop :=
  ∃ v₀ : V, A v₀ ∈ interior {y | f₂ y ≠ ⊤}

/-- The Lagrangian of (𝒫_c), (2.6) = (1.1) with `g = −⟨b, ·⟩` (p. 10):
`ℒ(v, y; λ) = f(y) + (λ, Av − y) − ⟨b, v⟩`. -/
noncomputable def lagrangian (A : V →L[ℝ] Y) (f₁ : Y → ℝ) (f₂ : Y → EReal) (b : StrongDual ℝ V)
    (v : V) (y lam : Y) : EReal :=
  ((f₁ y + inner ℝ lam (A v - y) - b v : ℝ) : EReal) + f₂ y

/-- The augmented Lagrangian (1.2) / (𝒟_r), p. 12:
`ℒ_r(v, y; λ) = f(y) + (λ, Av − y) + (r/2)|Av − y|² − ⟨b, v⟩`. -/
noncomputable def augLagrangian (A : V →L[ℝ] Y) (f₁ : Y → ℝ) (f₂ : Y → EReal)
    (b : StrongDual ℝ V) (r : ℝ) (v : V) (y lam : Y) : EReal :=
  ((f₁ y + inner ℝ lam (A v - y) + r / 2 * ‖A v - y‖ ^ 2 - b v : ℝ) : EReal) + f₂ y

/-- Saddle point, footnote of p. 2: `L(v*, y*; λ) ≤ L(v*, y*; λ*) ≤ L(v, y; λ*)` for all
`(v, y)` and `λ`. -/
def IsSaddlePoint (L : V → Y → Y → EReal) (v : V) (y lam : Y) : Prop :=
  (∀ μ, L v y μ ≤ L v y lam) ∧ ∀ w z, L v y lam ≤ L w z lam

/-- The modified dual algorithm (3.4), Steps 1–3 = (3.5), (3.6), (3.7), p. 15, for every `n`.
Step 1 is written with `+ ⟨b, w⟩`, the sign that makes it the minimization of `ℒ_r(·, yⁿ; λⁿ)`
(the paper prints `− ⟨b, v⟩`). Step 2 is the variational inequality (3.6) in subgradient form:
`λⁿ + rAvⁿ⁺¹ − ryⁿ⁺¹ − f₁'(yⁿ⁺¹) ∈ ∂f₂(yⁿ⁺¹)`. -/
def IsModifiedDualRun (A : V →L[ℝ] Y) (f₁' : Y → Y) (f₂ : Y → EReal) (b : StrongDual ℝ V)
    (r ρ : ℝ) (v : ℕ → V) (y lam : ℕ → Y) : Prop :=
  ∀ n,
    (∀ w, r * inner ℝ (A (v (n + 1))) (A w) = inner ℝ (r • y n - lam n) (A w) + b w) ∧
    IsSubgradient f₂ (y (n + 1)) (lam n + r • A (v (n + 1)) - r • y (n + 1) - f₁' (y (n + 1))) ∧
    lam (n + 1) = lam n + ρ • (A (v (n + 1)) - y (n + 1))

/-- `P`, the orthogonal projection of `Y` onto the closure of the range `R(A)` (p. 16). Under
(2.5) the range is closed, so this is the projection onto `R(A)`. -/
noncomputable def projRange (A : V →L[ℝ] Y) : Y →L[ℝ] Y :=
  (LinearMap.range (A : V →ₗ[ℝ] Y)).topologicalClosure.starProjection

end GabayMercier.DualAlgorithm


