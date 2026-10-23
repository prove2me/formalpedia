-- Prove2me | Definitions.Def_SAPMM_Regret_Model
-- name    : SAPMM_Regret_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T07:22:48.530572+00:00
-- url     : https://prove2.me/theorems/65bec0d8-ac67-4c8d-a2fe-f125a0365a62
-- title:
--   (1.1), (A1)–(A5), (1.4)–(1.5), (2.13), (3.1), pp. 1–4, 9, 12 — the expectation-constrained problem, PMMSopt, the history σ-algebras and the constants
-- statement:
--   This file sets up the convex stochastic program with expectation constraints studied by Zhang, Zhang and Wu, the algorithm PMMSopt, and the constants of their regret analysis.
--
--   **The problem (1.1).** Let $\Xi$ be a measurable space, $X_0\subset\mathbb R^n$ a nonempty closed convex set and $O_0\subset\mathbb R^n$ an open bounded convex set with $X_0\subseteq O_0$. Let $F:\mathbb R^n\times\Xi\to\mathbb R$ and $G=(G_1,\dots,G_p):\mathbb R^n\times\Xi\to\mathbb R^p$ be jointly measurable, with $F(\cdot,\xi)$ and every $G_i(\cdot,\xi)$ continuous and convex on $O_0$. For a law $P$ on $\Xi$ put
--
--   $$
--   f(x)=\int_\Xi F(x,\xi)\,dP(\xi),\qquad g_i(x)=\int_\Xi G_i(x,\xi)\,dP(\xi),\qquad \Phi=\{x\in X_0:\ g_i(x)\le 0,\ i=1,\dots,p\}.
--   $$
--
--   The problem is to minimize $f$ over $\Phi$. The integrands are assumed integrable for every $x\in O_0$.
--
--   **Assumptions.** The oracle returns vectors $v_0(x,\xi)$ and $v_i(x,\xi)$ that are subgradients of $F(\cdot,\xi)$ and $G_i(\cdot,\xi)$ at $x$ relative to $O_0$ (pointwise part of (A2)). (A3): $\|x'-x''\|\le D_0$ on $X_0$, $F(x',\xi)-F(x'',\xi)\le\nu_f$ and $\|G(x,\xi)\|\le\nu_g$ on $O_0$, with $D_0,\nu_f,\nu_g>0$. (A4): $\|v_0(x,\xi)\|\le\kappa_f$ and $\|v_i(x,\xi)\|\le\kappa_g$ on $O_0$, with $\kappa_f,\kappa_g>0$. (A5), Slater: $\epsilon_0>0$ and $\hat x\in X_0$ with $g_i(\hat x)\le-\epsilon_0$ for all $i$. (A1): the samples $\xi_0,\xi_1,\dots$ are independent, identically distributed and measurable random variables on a probability space $(\Omega,\mathbb P)$.
--
--   **The algorithm.** Write $[y]_+$ for the componentwise positive part of $y\in\mathbb R^p$, the Euclidean projection onto $\mathbb R^p_+$. The augmented Lagrangian (1.4) at the sample $\xi_t$ is
--
--   $$
--   \mathcal L^t_\sigma(x,\lambda)=F(x,\xi_t)+\frac1{2\sigma}\Big[\big\|[\lambda+\sigma G(x,\xi_t)]_+\big\|^2-\|\lambda\|^2\Big].
--   $$
--
--   A run of PMMSopt (1.5) with parameters $\sigma,\alpha$ and start $x^0$ consists of $\lambda^0=0$ and, for $t\ge0$,
--
--   $$
--   x^{t+1}\in\operatorname*{arg\,min}_{x\in X_0}\Big\{\mathcal L^t_\sigma(x,\lambda^t)+\frac\alpha2\|x-x^t\|^2\Big\},\qquad \lambda^{t+1}=[\lambda^t+\sigma G(x^{t+1},\xi_t)]_+,
--   $$
--
--   where each $x^t$ is a measurable function of the history $\xi_0,\dots,\xi_{t-1}$. The history σ-algebra $\sigma(\xi_0,\dots,\xi_{t-1})$ is denoted $\mathcal H_t$, with $\mathcal H_0$ trivial.
--
--   **Constants.** From (3.1), (2.13) and p. 15:
--
--   $$
--   \kappa_0=\frac{2\nu_f}{\epsilon_0},\quad \kappa_1=\frac{D_0^2}{\epsilon_0},\quad \kappa_3=\frac{\nu_g^2}{\epsilon_0}-\nu_g,\quad \kappa_4=2\nu_g+\frac{\epsilon_0}2+\frac{8\nu_g^2}{\epsilon_0}\log\frac{32\nu_g^2}{\epsilon_0^2},
--   $$
--
--   $$
--   \kappa_*=\kappa_0+\kappa_1+\kappa_3+2\kappa_4,\qquad \kappa_c=\kappa_*+4\kappa_g\kappa_f+4\sqrt p\,(\kappa_*+\nu_g)\kappa_g^2,\qquad \kappa_o=\frac{\kappa_f^2}2+\frac{D_0^2}2+\frac{\nu_g^2}2,
--   $$
--
--   $$
--   \vartheta(\sigma,\alpha,s)=\frac{\epsilon_0\sigma s}2+\nu_g\sigma(s-1)+\frac{\alpha D_0^2}{\epsilon_0 s}+\frac{2\nu_f}{\epsilon_0}+\frac{\sigma\nu_g^2}{\epsilon_0}.
--   $$
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** $\mathbb R^n$ and $\mathbb R^p$ are `EuclideanSpace`, so all norms and inner products are Euclidean. $\Xi$ is a general measurable space (the paper has $\Xi\subseteq\mathbb R^q$). Samples are indexed from $0$, so the paper's $\xi_{[k]}$ is $\mathcal H_{k+1}$ (`hist ξ (k+1)`). Joint measurability of $F$ and $G$ is the paper's implicit convention. The expectation clause of (A2) ($\mathbb E[v_i(x,\xi)]\in\partial g_i(x)$) is omitted because no proof in §§2–3 uses it. The run is a predicate (`IsRun`), not a chosen argmin: the step-1 objective is strongly convex and continuous on the compact $X_0$, so the run is unique, and the measurability of $x^t$ in the history is the paper's own assertion (p. 4). **Corrected constants:** $\kappa_*$ uses $2\kappa_4$ (printed $\kappa_4$) and $\kappa_c$ uses $4\sqrt p$ (printed $2\sqrt p$); see Theorem 3.1. `Real.log` is the natural logarithm; its argument $32\nu_g^2/\epsilon_0^2$ is positive. The coefficient $1/(2\sigma)$ requires $\sigma>0$, which every statement assumes.
-- source:
--   Zhang, Zhang and Wu, Stochastic Approximation Proximal Method of Multipliers for Convex Stochastic Programming, arXiv:1907.12226v3, pp. 1–4, 9, 12, 15, (1.1), (A1)–(A5), (1.4), (1.5), (2.13), (3.1)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace SAPMM.Regret

/-- `w` is a subgradient of `φ` at `x` relative to the set `S`:
`φ x + ⟪w, y - x⟫ ≤ φ y` for every `y ∈ S`. -/
def IsSubgradOn {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n)))
    (φ : EuclideanSpace ℝ (Fin n) → ℝ) (x w : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ y ∈ S, φ x + inner ℝ w (y - x) ≤ φ y

/-- The data of problem (1.1) together with the oracle of (A2) and the constants of (A3)–(A5)
(Zhang–Zhang–Wu, arXiv:1907.12226v3, pp. 1–2). `F x ξ` and `G x ξ` are the random objective and
the random constraint vector `(G_1, …, G_p)`; `v0 x ξ`, `v i x ξ` are the stochastic
subgradients returned by the oracle; `xhat` is the Slater point `x̂` of (A5). -/
structure Problem (n p : ℕ) (Ξ : Type*) where
  X0 : Set (EuclideanSpace ℝ (Fin n))
  O0 : Set (EuclideanSpace ℝ (Fin n))
  F : EuclideanSpace ℝ (Fin n) → Ξ → ℝ
  G : EuclideanSpace ℝ (Fin n) → Ξ → EuclideanSpace ℝ (Fin p)
  v0 : EuclideanSpace ℝ (Fin n) → Ξ → EuclideanSpace ℝ (Fin n)
  v : Fin p → EuclideanSpace ℝ (Fin n) → Ξ → EuclideanSpace ℝ (Fin n)
  D0 : ℝ
  νf : ℝ
  νg : ℝ
  κf : ℝ
  κg : ℝ
  ε0 : ℝ
  xhat : EuclideanSpace ℝ (Fin n)

namespace Problem

variable {n p : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]

/-- The objective `f(x) = E[F(x, ξ)]` of (1.1), `ξ` distributed according to `law`. -/
noncomputable def f (P : Problem n p Ξ) (law : Measure Ξ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∫ ξ, P.F x ξ ∂law

/-- The constraint functions `g_i(x) = E[G_i(x, ξ)]` of (1.1). -/
noncomputable def g (P : Problem n p Ξ) (law : Measure Ξ) (i : Fin p)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∫ ξ, P.G x ξ i ∂law

/-- The feasible region `Φ = {x ∈ X0 : g_i(x) ≤ 0, i = 1, …, p}` (p. 2). -/
def Phi (P : Problem n p Ξ) (law : Measure Ξ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | x ∈ P.X0 ∧ ∀ i, P.g law i x ≤ 0}

/-- The pathwise standing assumptions of §1 (pp. 1–2) and (A2)–(A4): `X0` nonempty closed
convex, `O0` open bounded convex containing `X0`; `F(·, ξ)`, `G_i(·, ξ)` continuous and convex on
`O0`; the oracle returns subgradients (pointwise part of (A2)); the bounds of (A3) and (A4).
Joint measurability of `F` and `G` is the paper's implicit convention (it writes `E[F(x^t, ξ_t)]`). -/
structure Standing (P : Problem n p Ξ) : Prop where
  X0_nonempty : P.X0.Nonempty
  X0_closed : IsClosed P.X0
  X0_convex : Convex ℝ P.X0
  O0_open : IsOpen P.O0
  O0_convex : Convex ℝ P.O0
  O0_bounded : Bornology.IsBounded P.O0
  X0_sub_O0 : P.X0 ⊆ P.O0
  F_cont : ∀ ξ, ContinuousOn (fun x => P.F x ξ) P.O0
  F_conv : ∀ ξ, ConvexOn ℝ P.O0 (fun x => P.F x ξ)
  G_cont : ∀ ξ i, ContinuousOn (fun x => P.G x ξ i) P.O0
  G_conv : ∀ ξ i, ConvexOn ℝ P.O0 (fun x => P.G x ξ i)
  F_meas : Measurable (Function.uncurry P.F)
  G_meas : Measurable (Function.uncurry P.G)
  v0_sub : ∀ x ∈ P.O0, ∀ ξ, IsSubgradOn P.O0 (fun y => P.F y ξ) x (P.v0 x ξ)
  v_sub : ∀ i, ∀ x ∈ P.O0, ∀ ξ, IsSubgradOn P.O0 (fun y => P.G y ξ i) x (P.v i x ξ)
  D0_pos : 0 < P.D0
  νf_pos : 0 < P.νf
  νg_pos : 0 < P.νg
  diam : ∀ x' ∈ P.X0, ∀ x'' ∈ P.X0, ‖x' - x''‖ ≤ P.D0
  F_osc : ∀ x' ∈ P.O0, ∀ x'' ∈ P.O0, ∀ ξ, P.F x' ξ - P.F x'' ξ ≤ P.νf
  G_bdd : ∀ x ∈ P.O0, ∀ ξ, ‖P.G x ξ‖ ≤ P.νg
  κf_pos : 0 < P.κf
  κg_pos : 0 < P.κg
  v0_bdd : ∀ x ∈ P.O0, ∀ ξ, ‖P.v0 x ξ‖ ≤ P.κf
  v_bdd : ∀ i, ∀ x ∈ P.O0, ∀ ξ, ‖P.v i x ξ‖ ≤ P.κg

/-- The expectations `E[F(x, ξ)]`, `E[G_i(x, ξ)]` are well defined and finite for every
`x ∈ O0` (p. 2): the integrands are integrable against the law of `ξ`. -/
structure FiniteExpect (P : Problem n p Ξ) (law : Measure Ξ) : Prop where
  F_int : ∀ x ∈ P.O0, Integrable (fun ξ => P.F x ξ) law
  G_int : ∀ x ∈ P.O0, ∀ i, Integrable (fun ξ => P.G x ξ i) law

/-- Slater's condition (A5): `ε0 > 0`, `x̂ ∈ X0` and `g_i(x̂) ≤ -ε0` for every `i`. -/
structure Slater (P : Problem n p Ξ) (law : Measure Ξ) : Prop where
  ε0_pos : 0 < P.ε0
  xhat_mem : P.xhat ∈ P.X0
  slater : ∀ i, P.g law i P.xhat ≤ -P.ε0

/-- `κ0 = 2νf/ε0` of (3.1), p. 12. -/
noncomputable def κ0 (P : Problem n p Ξ) : ℝ := 2 * P.νf / P.ε0
/-- `κ1 = D0²/ε0` of (3.1). -/
noncomputable def κ1 (P : Problem n p Ξ) : ℝ := P.D0 ^ 2 / P.ε0
/-- `κ3 = νg²/ε0 - νg` of (3.1). -/
noncomputable def κ3 (P : Problem n p Ξ) : ℝ := P.νg ^ 2 / P.ε0 - P.νg
/-- `κ4 = 2νg + ε0/2 + (8νg²/ε0) log(32νg²/ε0²)` of (3.1) (natural logarithm). -/
noncomputable def κ4 (P : Problem n p Ξ) : ℝ :=
  2 * P.νg + P.ε0 / 2 + 8 * P.νg ^ 2 / P.ε0 * Real.log (32 * P.νg ^ 2 / P.ε0 ^ 2)
/-- `κ* = κ0 + κ1 + κ3 + 2κ4` (Theorem 3.1, **corrected**: printed `+ κ4`). -/
noncomputable def κstar (P : Problem n p Ξ) : ℝ := P.κ0 + P.κ1 + P.κ3 + 2 * P.κ4
/-- `κc = κ* + 4κgκf + 4√p(κ* + νg)κg²` (Theorem 3.1, **corrected**: printed `2√p`). -/
noncomputable def κc (P : Problem n p Ξ) : ℝ :=
  P.κstar + 4 * P.κg * P.κf + 4 * Real.sqrt p * (P.κstar + P.νg) * P.κg ^ 2
/-- `κo = κf²/2 + D0²/2 + νg²/2` (Theorem 3.2, p. 15). -/
noncomputable def κo (P : Problem n p Ξ) : ℝ := P.κf ^ 2 / 2 + P.D0 ^ 2 / 2 + P.νg ^ 2 / 2
/-- The drift threshold `ϑ(σ, α, s)` of (2.13), p. 9. -/
noncomputable def vartheta (P : Problem n p Ξ) (σ α : ℝ) (s : ℕ) : ℝ :=
  P.ε0 * σ * s / 2 + P.νg * σ * ((s : ℝ) - 1) + α * P.D0 ^ 2 / (P.ε0 * s) + 2 * P.νf / P.ε0
    + σ * P.νg ^ 2 / P.ε0

end Problem

/-- (A1): `ξ 0, ξ 1, …` is an i.i.d. sequence of `Ξ`-valued random variables on `(Ω, μ)`. -/
structure IsIIDSample {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ξ : ℕ → Ω → Ξ) : Prop where
  meas : ∀ t, Measurable (ξ t)
  indep : iIndepFun ξ μ
  ident : ∀ t, IdentDistrib (ξ t) (ξ 0) μ μ

/-- The history `σ(ξ 0, …, ξ (t-1))`; `hist ξ 0 = ⊥`. The paper's `ξ_[k]` is `hist ξ (k+1)`. -/
@[instance_reducible]
def hist {Ω Ξ : Type*} [MeasurableSpace Ξ] (ξ : ℕ → Ω → Ξ) (t : ℕ) : MeasurableSpace Ω :=
  ⨆ j ∈ Finset.range t, MeasurableSpace.comap (ξ j) inferInstance

/-- `[y]_+`, the Euclidean projection of `y ∈ ℝ^p` onto `ℝ^p_+` (componentwise positive part). -/
noncomputable def projPos {p : ℕ} (y : EuclideanSpace ℝ (Fin p)) : EuclideanSpace ℝ (Fin p) :=
  WithLp.toLp 2 (fun i => max (y i) 0)

/-- The augmented Lagrangian `L^t_σ(x, λ)` of (1.4) at the sample value `ξv = ξ_t`. -/
noncomputable def augLag {n p : ℕ} {Ξ : Type*} (P : Problem n p Ξ) (σ : ℝ) (ξv : Ξ)
    (lam : EuclideanSpace ℝ (Fin p)) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  P.F x ξv + 1 / (2 * σ) * (‖projPos (lam + σ • P.G x ξv)‖ ^ 2 - ‖lam‖ ^ 2)

/-- `(x, lam)` is the run of PMMSopt (1.5) with parameters `σ, α`, start `x0`, `λ^0 = 0`,
driven by the samples `ξ`: `x^{t+1}` minimizes `L^t_σ(·, λ^t) + (α/2)‖· - x^t‖²` over `X0`, and
`λ^{t+1} = [λ^t + σ G(x^{t+1}, ξ_t)]_+`. `x^t` is a function of the history `ξ_0, …, ξ_{t-1}`
(p. 4). -/
structure IsRun {n p : ℕ} {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Problem n p Ξ) (σ α : ℝ) (x0 : EuclideanSpace ℝ (Fin n)) (ξ : ℕ → Ω → Ξ)
    (x : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (lam : ℕ → Ω → EuclideanSpace ℝ (Fin p)) : Prop where
  x_zero : ∀ ω, x 0 ω = x0
  lam_zero : ∀ ω, lam 0 ω = 0
  x_mem : ∀ t ω, x (t + 1) ω ∈ P.X0
  x_min : ∀ t ω, IsMinOn (fun y => augLag P σ (ξ t ω) (lam t ω) y + α / 2 * ‖y - x t ω‖ ^ 2)
    P.X0 (x (t + 1) ω)
  lam_succ : ∀ t ω, lam (t + 1) ω = projPos (lam t ω + σ • P.G (x (t + 1) ω) (ξ t ω))
  x_meas : ∀ t, Measurable[hist ξ t] (x t)

end SAPMM.Regret


