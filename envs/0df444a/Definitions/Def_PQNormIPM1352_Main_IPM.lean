-- Prove2me | Definitions.Def_PQNormIPM1352_Main_IPM
-- name    : PQNormIPM1352_Main_IPM
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T07:06:28.665012+00:00
-- url     : https://prove2.me/theorems/455a2029-8d36-45cd-b8cf-5b5362ac9131
-- title:
--   Self-concordant barriers, Newton decrement and the inexact short-step path-following method
-- statement:
--   Points live in $\mathbb R^N$. For a function $G : \mathbb R^N \to \mathbb R$ write $\nabla G(x)$ for its gradient and $H_G(x) = \nabla^2 G(x)$ for its Hessian matrix, and $\|h\|_x = \sqrt{h^\top H_G(x) h}$ for the **Hessian (local) norm**.
--
--   1. **Self-concordance** (Definition 4). Let $K \subseteq \mathbb R^N$ be closed and convex with nonempty interior. A function $F$ that is smooth on $\mathrm{int}(K)$ is *self-concordant* if it is convex there and $|D^3F(x)[h,h,h]| \le 2\,\big(D^2F(x)[h,h]\big)^{3/2}$ for all $x \in \mathrm{int}(K)$ and $h \in \mathbb R^N$.
--   2. $F$ **diverges at the boundary** if $F(x) \to +\infty$ as $x \to x_0$ within $\mathrm{int}(K)$, for every boundary point $x_0$ of $K$.
--   3. $F$ is a **$\nu$-self-concordant barrier** ($\nu > 0$) if it is self-concordant, diverges at the boundary, and $|\langle \nabla F(x), h\rangle| \le \sqrt{\nu}\, \|h\|_x$ for all $x \in \mathrm{int}(K)$ and $h$.
--   4. For $c \in \mathbb R^N$ and $\eta > 0$, the **penalized objective** is $\Phi_\eta(x) = F(x) + \eta \langle c, x\rangle$. The **Newton step** of $G$ at $x$ is $\Delta(x) = -H_G(x)^{-1}\nabla G(x)$ and the **Newton decrement** is $\lambda(x) = \|\Delta(x)\|_x$; for $G = \Phi_\eta$ these are $\Delta_\eta(x)$ and $\lambda_\eta(x)$ (the Hessian of $\Phi_\eta$ is that of $F$).
--   5. A vector $\tilde\Delta$ is a **$\delta$-approximate Newton step** at $x$ if
--   $$\|\tilde\Delta - \Delta(x)\|_x \le \delta\, \|\Delta(x)\|_x. \tag{3}$$
--   6. The **inexact short-step path-following method** with parameters $\nu, \delta, \eta_0$ starts at $x_0$ and sets $x_{t+1} = x_t + \tilde\Delta_t$, where $\tilde\Delta_t$ is a $\delta$-approximate Newton step of $\Phi_{\eta_t}$ at $x_t$ and $\eta_t = (1 + 1/(20\sqrt\nu))^t\,\eta_0$.
--
--   These are the objects of the generic interior-point analysis (Theorems 5 and 12, Lemmas 13–15) that the mission specializes to the barrier (6).
--
--   **Formalization Note** Self-concordance is the published definition `ConvexOptimization.IsSelfConcordantOn` (convex, $C^3$, and the cubic inequality along every line $t \mapsto F(x + th)$), applied to $\mathrm{int}(K)$, together with smoothness ($C^\infty$) on $\mathrm{int}(K)$, as Definition 4 asks. Derivatives are Fréchet derivatives of a function defined on all of $\mathbb R^N$; statements only use them at points of $\mathrm{int}(K)$. The matrix inverse is Mathlib's, which agrees with the true inverse whenever the Hessian is invertible; statements that need the Newton step assume an invertible (positive definite) Hessian. A run is an infinite sequence; any finite run extends to one (exact Newton steps are $\delta$-approximate for every $\delta \ge 0$).
-- source:
--   Marco Pirazzini, Daniel Spielman, A Fast and Accurate Algorithm for the p → q Norm of Sparse Non-Negative Matrices, STOC 2027 submission #1352 (October 2026), §2.2.1, Definition 4, p. 5; §2.2.2, pp. 5–6 (Φ_η, Δ_η, λ_η, eq. (3)); Appendix A, Theorem 12, p. 23 (update of η)

import Mathlib
import Definitions.Def_ConvexOptimization_selfConcordance

/-!
# Self-concordant barriers and the inexact short-step path-following method

Pirazzini–Spielman, STOC 2027 submission #1352, §2.2.1 (Definition 4, p. 5), §2.2.2 (pp. 5–6:
`Φ_η`, Newton step, Newton decrement, the δ-approximate step (3)) and Appendix A, p. 23 (the
update `η⁺ = (1 + 1/(20√ν)) η`).

Points live in `ℝᴺ = EuclideanSpace ℝ (Fin N)`. Derivatives are Fréchet derivatives of a function
defined on all of `ℝᴺ`; every statement using them quantifies over `int(K)` only, so values of the
function outside `int(K)` never matter.
-/

open scoped RealInnerProductSpace ContDiff
open Filter Topology Matrix

namespace PQNormIPM1352.Main

noncomputable section

/-- The ambient space `ℝᴺ`. -/
abbrev Vec (N : ℕ) := EuclideanSpace ℝ (Fin N)

variable {N : ℕ}

/-- The gradient `∇F(x)` as a coordinate vector: `(∇F(x))_i = DF(x)[eᵢ]`. -/
def gradVec (F : Vec N → ℝ) (x : Vec N) : Fin N → ℝ :=
  fun i => fderiv ℝ F x (EuclideanSpace.single i 1)

/-- The Hessian matrix `H(x) = ∇²F(x)`: `H(x)_{ij} = D²F(x)[eᵢ, eⱼ]`. -/
def hessMat (F : Vec N → ℝ) (x : Vec N) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => iteratedFDeriv ℝ 2 F x ![EuclideanSpace.single i 1, EuclideanSpace.single j 1]

/-- The Hessian (local) norm `‖h‖_x = √(hᵀ H(x) h)` (§2.2.1, p. 5). -/
def localNorm (F : Vec N → ℝ) (x h : Vec N) : ℝ :=
  Real.sqrt (WithLp.ofLp h ⬝ᵥ (hessMat F x *ᵥ WithLp.ofLp h))

/-- The penalized objective `Φ_η(x) = F(x) + η⟨c, x⟩` (§2.2.2, p. 5). -/
def penalized (F : Vec N → ℝ) (c : Vec N) (η : ℝ) : Vec N → ℝ :=
  fun x => F x + η * ⟪c, x⟫

/-- The Newton step of a function `G` at `x`: `Δ(x) = −H_G(x)⁻¹ ∇G(x)` (§2.2.2, p. 6). For
`G = Φ_η` this is `Δ_η(x)`; since `⟨c, ·⟩` is linear, `H_{Φ_η} = H_F`. `⁻¹` is Mathlib's matrix
inverse; it is the true inverse whenever `H_G(x)` is invertible. -/
def newtonStep (G : Vec N → ℝ) (x : Vec N) : Vec N :=
  WithLp.toLp 2 (-((hessMat G x)⁻¹ *ᵥ gradVec G x))

/-- The Newton decrement `λ(x) = ‖Δ(x)‖_x` of `G` at `x` (§2.2.2, p. 6); `λ_η(x)` is
`newtonDecrement (penalized F c η) x`. -/
def newtonDecrement (G : Vec N → ℝ) (x : Vec N) : ℝ :=
  localNorm G x (newtonStep G x)

/-- A δ-approximate Newton step in the sense of (3) (§2.2.2, p. 6):
`‖Δ̃ − Δ(x)‖_x ≤ δ ‖Δ(x)‖_x`. -/
def IsApproxNewtonStep (G : Vec N → ℝ) (δ : ℝ) (x Δt : Vec N) : Prop :=
  localNorm G x (Δt - newtonStep G x) ≤ δ * localNorm G x (newtonStep G x)

/-- Self-concordance (Definition 4, p. 5): `K` is closed and convex with nonempty interior, `F` is
smooth (`C^∞`) on `int(K)`, and `F` is self-concordant on `int(K)` in the sense of the published
`ConvexOptimization.IsSelfConcordantOn`: convex there, and `|D³F(x)[h,h,h]| ≤ 2 (D²F(x)[h,h])^{3/2}`
for all `x ∈ int(K)` and `h`, written through the line restrictions `t ↦ F(x + t h)`. -/
def IsSelfConcordantFunction (K : Set (Vec N)) (F : Vec N → ℝ) : Prop :=
  IsClosed K ∧ Convex ℝ K ∧ (interior K).Nonempty ∧ ContDiffOn ℝ ∞ F (interior K) ∧
    ConvexOptimization.IsSelfConcordantOn (interior K) F

/-- "`F` diverges to `+∞` at the boundary" (Definition 4, p. 5): for every boundary point `x₀` of
`K`, `F(x) → +∞` as `x → x₀` within `int(K)`. -/
def DivergesAtBoundary (K : Set (Vec N)) (F : Vec N → ℝ) : Prop :=
  ∀ x₀ ∈ frontier K, Tendsto F (𝓝[interior K] x₀) atTop

/-- `F` is a `ν`-self-concordant barrier for `K` (Definition 4, p. 5): self-concordant, divergent
at the boundary, `ν > 0`, and `|⟨∇F(x), h⟩| ≤ √ν ‖h‖_x` for all `x ∈ int(K)` and `h ∈ ℝᴺ`. -/
def IsNuSCB (K : Set (Vec N)) (F : Vec N → ℝ) (ν : ℝ) : Prop :=
  IsSelfConcordantFunction K F ∧ DivergesAtBoundary K F ∧ 0 < ν ∧
    ∀ x ∈ interior K, ∀ h : Vec N, |fderiv ℝ F x h| ≤ Real.sqrt ν * localNorm F x h

/-- The barrier parameter after `t` path updates `η⁺ = (1 + 1/(20√ν)) η` (Theorem 12, p. 23):
`η_t = (1 + 1/(20√ν))^t η₀`. -/
def pathParam (ν η₀ : ℝ) (t : ℕ) : ℝ := (1 + 1 / (20 * Real.sqrt ν)) ^ t * η₀

/-- A run of the inexact short-step path-following method of Theorem 12 (p. 23): `x 0 = x₀` and,
for every `t`, `x (t+1) = x t + Δ̃_t` with `Δ̃_t` a δ-approximate Newton step (3) of `Φ_{η_t}` at
`x t`, where `η_t = pathParam ν η₀ t`. -/
def IsApproxPathRun (F : Vec N → ℝ) (c : Vec N) (ν δ η₀ : ℝ) (x₀ : Vec N) (x : ℕ → Vec N) :
    Prop :=
  x 0 = x₀ ∧ ∀ t : ℕ, IsApproxNewtonStep (penalized F c (pathParam ν η₀ t)) δ (x t) (x (t + 1) - x t)

end

end PQNormIPM1352.Main


