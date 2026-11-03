-- Prove2me | Definitions.Def_DNNProj_Problem9
-- name    : DNNProj_Problem9
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:15:28.774896+00:00
-- url     : https://prove2.me/theorems/853a052d-d9b3-4547-b587-d44862966076
-- title:
--   Problem (9), its Lagrangian dual (10), the KKT system (11), quadratic growth (Definition 4), Assumption 1 and the sets (12)–(13)
-- statement:
--   Let $\mathbb X,\mathbb W,\mathbb Y$ be finite-dimensional real inner-product spaces, $\mathcal F:\mathbb X\to\mathbb W$ and $\mathcal A:\mathbb X\to\mathbb Y$ linear maps, $\mathcal Q\subseteq\mathbb Y$ a cone, $c\in\mathbb X$, $b\in\mathbb Y$, $p:\mathbb X\to(-\infty,+\infty]$ and $h:\mathbb W\to(-\infty,+\infty]$. Problem (9) is
--   $$\min_{x\in\mathbb X}\ \theta(x)\triangleq h(\mathcal Fx)+\langle c,x\rangle+p(x)\quad\text{s.t. }\mathcal Ax-b\in\mathcal Q,$$
--   and its Lagrangian dual (10) maximizes $g(y)\triangleq\inf_{x}\{\theta(x)+\langle y,\mathcal Ax-b\rangle\}$ over $y\in\mathcal Q^\circ$. $\mathrm{SOL_P}$ and $\mathrm{SOL_D}$ are their solution sets. The KKT system (11) at $(x,y)$ is
--   $$0\in\mathcal F^*\nabla h(\mathcal Fx)+c+\partial p(x)+\mathcal A^*y,\qquad y\in\mathcal N_{\mathcal Q}(\mathcal Ax-b).$$
--   The **standing assumptions** of §3.1: $\mathcal Q$ is a convex polyhedral cone, $p$ is closed proper convex, $h$ is essentially smooth and essentially locally strictly convex, and (11) has a solution.
--
--   **Definition 4.** The **quadratic growth condition** holds at $\bar x$ if for some $\kappa,\varepsilon>0$, $\theta(x)\ge\theta(\bar x)+\kappa\operatorname{dist}^2(x,\mathrm{SOL_P})$ for all feasible $x\in\mathbb B_\varepsilon(\bar x)$ (14).
--
--   **Assumption 1.** (a) For each $w$ in the domain of $h$ (where $\nabla h(w)$ exists) there are $\kappa_1,\varepsilon_1>0$ with $h(w')\ge h(w)+\langle\nabla h(w),w'-w\rangle+\kappa_1\|w'-w\|^2$ on $\mathbb B_{\varepsilon_1}(w)$; (b) for each $(x,v)\in\operatorname{gph}\partial p$ there are $\kappa_2,\varepsilon_2>0$ with $p(x')\ge p(x)+\langle v,x'-x\rangle+\kappa_2\operatorname{dist}^2(x',(\partial p)^{-1}(v))$ on $\mathbb B_{\varepsilon_2}(x)$.
--
--   **(12)–(13).** For $\bar x\in\mathrm{SOL_P}$: $\bar\zeta=\mathcal F\bar x$, $\bar\eta=\mathcal F^*\nabla h(\bar\zeta)+c$, $\overline{\mathcal V}=\{x\mid\mathcal Fx=\bar\zeta\}$, $\mathcal G_1(y)=(\partial p)^{-1}(-\mathcal A^*y-\bar\eta)$ and $\mathcal G_2(y)=\{x\mid y\in\mathcal N_{\mathcal Q}(\mathcal Ax-b)\}$.
--
--   These are the objects of the paper's general quadratic-growth theory (Lemma 1, Propositions 6, Lemma 2, Theorem 1).
--
--   **Formalization Note** $h$ is encoded by its domain `domh` and its real values on it ($+\infty$ off it). "Essentially smooth and essentially locally strictly convex" is read as: `domh` convex, $h$ convex on it, differentiable and strictly convex on its interior (steepness is not required); $\nabla h$ is `gradient h`, used only at interior points, and the KKT system includes $\mathcal Fx\in\operatorname{int}(\operatorname{dom}h)$. Assumption 1(a) is required at interior points of $\operatorname{dom}h$, where $\nabla h(w)$ exists, and is trivially true at $w'\notin\operatorname{dom}h$. $\theta$, $g$, $p$ take values in `EReal`; $g$ may be $-\infty$. $\overline{\mathcal V}$, $\bar\eta$ and $\mathcal G_1$ are built from a given point $\bar x$.
-- source:
--   Cui, Liang, Sun, Toh, On Degenerate Doubly Nonnegative Projection Problems, arXiv:2009.11272v2 (preprint basis), https://arxiv.org/abs/2009.11272v2, §3.1: problem (9), dual (10), KKT system (11), SOL_P/SOL_D p.8; (12)–(13), Definition 4 (14), Assumption 1 p.9

import Mathlib
import Definitions.Def_TensorAHPE_IsProperClosedConvex
import Definitions.Def_DNNProj_Basics

open scoped RealInnerProductSpace

namespace DNNProj

/-! # Problem (9), its dual (10), the KKT system (11), Definition 4, Assumption 1, (12)–(13)

Y. Cui, L. Liang, D. Sun, K.-C. Toh, *On Degenerate Doubly Nonnegative Projection Problems*,
arXiv:2009.11272v2, §3.1, pp.8–9.

**Formalization Note.**
* The spaces `𝕏, 𝕎, 𝕐` are finite-dimensional real inner-product spaces; `ℱ, 𝒜` are linear maps
  and `ℱ*, 𝒜*` their adjoints (`LinearMap.adjoint`).
* `p : 𝕏 → (−∞, +∞]`, `θ`, `g` take values in `EReal`.
* The function `h : 𝕎 → (−∞, +∞]` is encoded by its effective domain `domh : Set 𝕎` and a real
  function `h : 𝕎 → ℝ`: the extended value is `h w` on `domh` and `+∞` off it (`hExt`). Values of
  the real function off `domh` are never read. The paper's "essentially smooth and essentially
  locally strictly convex" is read as `HReading`: `domh` convex, `h` convex on `domh`,
  differentiable and strictly convex on `int(domh)`; `∇h(w)` is `gradient h w` at interior points.
* Distances to `SOL_P` and to `(∂p)⁻¹(v)` are `Metric.infDist`; both sets contain the base point
  wherever they are used. -/

noncomputable section

/-- The data of problem (9) (arXiv:2009.11272v2, p.8):
`minimize θ(x) ≜ h(ℱx) + ⟨c, x⟩ + p(x)` subject to `𝒜x − b ∈ 𝒬`. The function `h` is given by its
domain `domh` and its (real) values `h` there. No hypothesis is bundled; see `Standing`. -/
structure LinConvexProblem (X W Y : Type*)
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] where
  /-- the linear map `ℱ : 𝕏 → 𝕎` -/
  F : X →ₗ[ℝ] W
  /-- the linear map `𝒜 : 𝕏 → 𝕐` -/
  A : X →ₗ[ℝ] Y
  /-- the cone `𝒬 ⊆ 𝕐` -/
  Q : Set Y
  /-- `b ∈ 𝕐` -/
  b : Y
  /-- `c ∈ 𝕏` -/
  c : X
  /-- `p : 𝕏 → (−∞, +∞]` -/
  p : X → EReal
  /-- the effective domain `dom h ⊆ 𝕎` -/
  domh : Set W
  /-- the finite values of `h` on `dom h` -/
  h : W → ℝ

namespace LinConvexProblem

variable {X W Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
    (P : LinConvexProblem X W Y)

open Classical in
/-- The extended-valued `h : 𝕎 → (−∞, +∞]`: `h w` on `dom h`, `+∞` off it. -/
def hExt (w : W) : EReal := if w ∈ P.domh then (P.h w : EReal) else ⊤

/-- The objective of (9): `θ(x) ≜ h(ℱx) + ⟨c, x⟩ + p(x)` (p.8). -/
def theta (x : X) : EReal := P.hExt (P.F x) + ((⟪P.c, x⟫ : ℝ) : EReal) + P.p x

/-- The feasible set `{x ∈ 𝕏 | 𝒜x − b ∈ 𝒬}` of (9). -/
def feasible : Set X := {x | P.A x - P.b ∈ P.Q}

/-- The dual function of (10): `g(y) ≜ inf_{x ∈ 𝕏} {θ(x) + ⟨y, 𝒜x − b⟩}` (p.8), an infimum in
`EReal` (it may be `−∞`). -/
def g (y : Y) : EReal := ⨅ x : X, P.theta x + ((⟪y, P.A x - P.b⟫ : ℝ) : EReal)

/-- `SOL_P`, the solution set of (9) (p.8): feasible points minimizing `θ` over the feasible set. -/
def solP : Set X := {x | x ∈ P.feasible ∧ ∀ x' ∈ P.feasible, P.theta x ≤ P.theta x'}

/-- `SOL_D`, the solution set of (10) (p.8): points of `𝒬°` maximizing `g` over `𝒬°`. -/
def solD : Set Y := {y | y ∈ polar P.Q ∧ ∀ y' ∈ polar P.Q, P.g y' ≤ P.g y}

/-- The KKT system (11) (p.8) at `(x, y) ∈ 𝕏 × 𝕐`:
`0 ∈ ℱ*∇h(ℱx) + c + ∂p(x) + 𝒜*y` and `y ∈ N_𝒬(𝒜x − b)`.
**Formalization Note.** `∇h(ℱx)` exists only for `ℱx ∈ int(dom h)` (h essentially smooth), so
that membership is part of the system. -/
def KKT (x : X) (y : Y) : Prop :=
  P.F x ∈ interior P.domh ∧
    (∃ v ∈ subdiff P.p x,
      LinearMap.adjoint P.F (gradient P.h (P.F x)) + P.c + v + LinearMap.adjoint P.A y = 0) ∧
    y ∈ normalCone P.Q (P.A x - P.b)

/-- The reading of "`h` essentially smooth and essentially locally strictly convex" (p.8):
`dom h` is convex, `h` is convex on `dom h`, and `h` is differentiable and strictly convex on
`int(dom h)`. (Steepness at the boundary is not required.) -/
def HReading : Prop :=
  ConvexOn ℝ P.domh P.h ∧ DifferentiableOn ℝ P.h (interior P.domh) ∧
    StrictConvexOn ℝ (interior P.domh) P.h

/-- The standing assumptions of §3.1 (p.8): `𝒬` is a convex polyhedral cone, `p` is closed proper
convex, `h` is as in `HReading`, and the KKT system (11) admits at least one solution. (The
spaces are finite-dimensional and `ℱ, 𝒜` linear by the typing.) -/
def Standing : Prop :=
  IsPolyhedralCone P.Q ∧ TensorAHPE.IsProperClosedConvex P.p ∧ P.HReading ∧ ∃ x y, P.KKT x y

/-- **Definition 4** (arXiv:2009.11272v2, p.9). The quadratic growth condition for (9) holds at
`x̄` if there are `κ > 0`, `ε > 0` with
`θ(x) ≥ θ(x̄) + κ dist²(x, SOL_P)` for all `x ∈ 𝔹_ε(x̄) ∩ {x | 𝒜x − b ∈ 𝒬}` (14). -/
def QuadGrowthAt (xbar : X) : Prop :=
  ∃ κ ε : ℝ, 0 < κ ∧ 0 < ε ∧ ∀ x ∈ Metric.closedBall xbar ε, x ∈ P.feasible →
    P.theta xbar + ((κ * Metric.infDist x P.solP ^ 2 : ℝ) : EReal) ≤ P.theta x

/-- **Assumption 1** (arXiv:2009.11272v2, p.9).
(a) for every `w ∈ dom h` (read: `int(dom h)`, where `∇h(w)` exists) there are `κ₁, ε₁ > 0` with
`h(w') ≥ h(w) + ⟨∇h(w), w' − w⟩ + κ₁‖w' − w‖²` for all `w' ∈ 𝔹_{ε₁}(w)` (trivial when
`w' ∉ dom h`, where `h(w') = +∞`);
(b) for every `(x, v) ∈ gph(∂p)` there are `κ₂, ε₂ > 0` with
`p(x') ≥ p(x) + ⟨v, x' − x⟩ + κ₂ dist²(x', (∂p)⁻¹(v))` for all `x' ∈ 𝔹_{ε₂}(x)`. -/
def Assumption1 : Prop :=
  (∀ w ∈ interior P.domh, ∃ κ₁ ε₁ : ℝ, 0 < κ₁ ∧ 0 < ε₁ ∧
      ∀ w' ∈ Metric.closedBall w ε₁, w' ∈ P.domh →
        P.h w + ⟪gradient P.h w, w' - w⟫ + κ₁ * ‖w' - w‖ ^ 2 ≤ P.h w') ∧
  (∀ x v, v ∈ subdiff P.p x → ∃ κ₂ ε₂ : ℝ, 0 < κ₂ ∧ 0 < ε₂ ∧
      ∀ x' ∈ Metric.closedBall x ε₂,
        ((((P.p x).toReal + ⟪v, x' - x⟫ +
            κ₂ * Metric.infDist x' (invMap (subdiff P.p) v) ^ 2 : ℝ)) : EReal) ≤ P.p x')

/-- `ζ̄ ≜ ℱx̄` of (12) (p.9), for a point `x̄` (in use, `x̄ ∈ SOL_P`). -/
def zetaBar (xbar : X) : W := P.F xbar

/-- `η̄ ≜ ℱ*∇h(ζ̄) + c` of (12) (p.9). -/
def etaBar (xbar : X) : X := LinearMap.adjoint P.F (gradient P.h (P.zetaBar xbar)) + P.c

/-- `𝒱̄ ≜ {x ∈ 𝕏 | ℱx = ζ̄}` of (12) (p.9) (the bar is part of the name, not a closure). -/
def Vbar (xbar : X) : Set X := {x | P.F x = P.zetaBar xbar}

/-- `𝒢₁(y) ≜ (∂p)⁻¹(−𝒜*y − η̄)` of (13) (p.9). -/
def G1 (xbar : X) (y : Y) : Set X :=
  invMap (subdiff P.p) (-(LinearMap.adjoint P.A y) - P.etaBar xbar)

/-- `𝒢₂(y) ≜ {x ∈ 𝕏 | y ∈ N_𝒬(𝒜x − b)}` of (13) (p.9). -/
def G2 (y : Y) : Set X := {x | y ∈ normalCone P.Q (P.A x - P.b)}

end LinConvexProblem

end

end DNNProj


