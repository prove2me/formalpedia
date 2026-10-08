-- Prove2me | Definitions.Def_CouplingHMC_Exact_Setting
-- name    : CouplingHMC_Exact_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T05:26:57.975002+00:00
-- url     : https://prove2.me/theorems/6bf6c96f-4f55-496e-9caa-4e76380e764f
-- title:
--   §2.1–2.3, 2.5.2, 2.6, pp. 5–9, 13, 17 — Assumption 2.1, the exact Hamiltonian flow (5), the coupling (18)–(21), the distance f of (26), the rate c of (32), the HMC kernel and W_ρ
-- statement:
--   This file fixes the objects of exact Hamiltonian Monte Carlo (HMC) and of the coupling of Bou-Rabee, Eberle and Zimmer. Throughout, $\mathbb R^d$ is the Euclidean space with norm $|\cdot|$ and inner product $x\cdot y$.
--
--   1. **Assumption 2.1.** $U:\mathbb R^d\to\mathbb R$ is four times continuously differentiable with $\int e^{-U(x)}\,dx<\infty$, and
--      - (A1) $U$ has a local minimum at $0$ and $U(0)=0$;
--      - (A2) $\|\nabla^2U\|\le L$, $\|\nabla^3U\|\le M$, $\|\nabla^4U\|\le N$ everywhere (operator norms);
--      - (A3) there are $\mathcal R\in[0,\infty)$ and $K\in(0,\infty)$ with $(x-y)\cdot(\nabla U(x)-\nabla U(y))\ge K|x-y|^2$ whenever $|x-y|\ge\mathcal R$.
--   2. **Exact Hamiltonian flow (5).** $(q_t,p_t)$ solves $\frac{d}{dt}q_t=p_t$, $\frac{d}{dt}p_t=-\nabla U(q_t)$ with $(q_0(x,v),p_0(x,v))=(x,v)$.
--   3. **Parameters (28)–(30)** for a duration $T>0$: $\gamma=\min(T^{-1},\mathcal R^{-1}/4)$ (equal to $T^{-1}$ when $\mathcal R=0$), $a=T^{-1}$, $R_1=\tfrac52(\mathcal R+T)$. The **step condition** is $LT^2\le\min(K/L,\tfrac14,\tfrac1{16\Lambda})$ with $\Lambda=16L\mathcal R^2$.
--   4. **Distance (25)–(26).** $f(r)=\int_0^r e^{-a\min(s,R_1)}\,ds$ and $\rho(x,y)=f(|x-y|)$.
--   5. **Rate (32).** $c=\tfrac1{10}\min\bigl(1,\tfrac12KT^2(1+\mathcal R/T)e^{-\mathcal R/(2T)}\bigr)e^{-2\mathcal R/T}$.
--   6. **Coupling (18)–(21).** The randomness of one step is $(\xi,\tilde{\mathcal U})$ with $\xi\sim N(0,I_d)$ independent of $\tilde{\mathcal U}\sim\mathrm{Unif}(0,1)$. For $z=x-y$, $e=z/|z|$ and $\varphi_{0,1}$ the standard normal density,
--   $$\eta=\begin{cases}\xi+\gamma z & \text{if } \tilde{\mathcal U}\le \varphi_{0,1}(e\cdot\xi+\gamma|z|)/\varphi_{0,1}(e\cdot\xi),\\ \xi-2(e\cdot\xi)e & \text{otherwise,}\end{cases}$$
--   used when $|x-y|<2\mathcal R$; when $|x-y|\ge2\mathcal R$ the coupling is synchronous, $\eta=\xi$. The coupled step is $X'=q_T(x,\xi)$, $Y'=q_T(y,\eta)$, and $R'(x,y)=|X'-Y'|$.
--   7. **Kernel and distances (9), p. 17.** $\pi(x,\cdot)$ is the law of $q_T(x,\xi)$, $\pi^n$ its $n$-th power, $\nu\pi^n$ the law after $n$ steps from $\nu$; $\mathcal W_c(\nu,\eta)=\inf_{\gamma\in C(\nu,\eta)}\int c(x,y)\,\gamma(dx\,dy)$ with $C(\nu,\eta)$ the couplings of $\nu$ and $\eta$; $\mu(dx)=\mathcal Z^{-1}e^{-U(x)}dx$ is the target measure (2).
--
--   These are the objects every statement of the mission is phrased in.
--
--   **Formalization Note.** $L,M,N$ are upper bounds rather than the suprema of (10); every statement of the mission is monotone in them, so nothing changes. The flow is a predicate on a pair of functions $(q,p)$, required for all $t\in\mathbb R$; since $\nabla U$ is globally Lipschitz it exists and is unique. At $z=0$ the vector $e$ is $0$, the ratio is $1$ and $\eta=\xi$. The condition $LT^2\le 1/(16\Lambda)$ is written $256L^2\mathcal R^2T^2\le1$ so that $\mathcal R=0$ imposes nothing, as on the page; $\gamma$ is defined by cases for the same reason. Kantorovich distances take values in $[0,\infty]$, and $C(\nu,\eta)$ is the published set `MongeKantorovichYao.transferencePlans`.
-- source:
--   Bou-Rabee, Eberle, Zimmer, Coupling and convergence for Hamiltonian Monte Carlo, arXiv:1805.00452v2, §2.1–2.3, 2.5.2, 2.6, (1)–(6), (9)–(11), (18)–(21), (25)–(30), (32), pp. 5–6, 8, 13, 17

import Mathlib
import Definitions.Def_MongeKantorovichYao_Defs

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace

namespace CouplingHMC.Exact

/-- The state space `ℝᵈ`, as the Euclidean space on `Fin d`. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Assumption 2.1 (p. 6), together with the standing hypotheses of §2.1 (p. 5):
`U ∈ C⁴(ℝᵈ)` with `∫ exp(-U) < ∞`, and
(A1) `U` has a local minimum at `0` and `U 0 = 0`;
(A2) `L`, `M`, `N` bound the operator norms of the second, third and fourth derivatives of `U`
     (upper bounds; the paper's `L = sup ‖∇²U‖` etc. are the least such bounds);
(A3) `ℛ ≥ 0`, `K > 0`, and `(x - y) · (∇U(x) - ∇U(y)) ≥ K |x - y|²` whenever `|x - y| ≥ ℛ`. -/
def Assumption21 {d : ℕ} (U : E d → ℝ) (L M N ℛ K : ℝ) : Prop :=
  (ContDiff ℝ 4 U ∧ Integrable (fun x => Real.exp (-U x))) ∧
  (IsLocalMin U 0 ∧ U 0 = 0) ∧
  ((∀ x, ‖iteratedFDeriv ℝ 2 U x‖ ≤ L) ∧ (∀ x, ‖iteratedFDeriv ℝ 3 U x‖ ≤ M) ∧
    (∀ x, ‖iteratedFDeriv ℝ 4 U x‖ ≤ N)) ∧
  (0 ≤ ℛ ∧ 0 < K ∧
    ∀ x y : E d, ℛ ≤ ‖x - y‖ → K * ‖x - y‖ ^ 2 ≤ ⟪x - y, gradient U x - gradient U y⟫_ℝ)

/-- `(q, p)` is the exact Hamiltonian flow (5) of `H(x, v) = U(x) + |v|²/2`:
`(q₀(x, v), p₀(x, v)) = (x, v)`, `d/dt q_t = p_t`, `d/dt p_t = -∇U(q_t)`, for every time `t ∈ ℝ`. -/
def IsExactFlow {d : ℕ} (U : E d → ℝ) (q p : ℝ → E d → E d → E d) : Prop :=
  ∀ x v : E d, q 0 x v = x ∧ p 0 x v = v ∧
    ∀ t : ℝ, HasDerivAt (fun s => q s x v) (p t x v) t ∧
      HasDerivAt (fun s => p s x v) (-gradient U (q t x v)) t

/-- The coupling parameter `γ := min(T⁻¹, ℛ⁻¹/4)` of (28); for `ℛ = 0` (where `ℛ⁻¹ = +∞`)
it is `T⁻¹`. -/
noncomputable def gammaC (T ℛ : ℝ) : ℝ := if ℛ = 0 then T⁻¹ else min T⁻¹ (ℛ⁻¹ / 4)

/-- The parameter `a := T⁻¹` of (29). -/
noncomputable def aC (T : ℝ) : ℝ := T⁻¹

/-- The parameter `R₁ := (5/2)(ℛ + T)` of (30). -/
noncomputable def R1C (T ℛ : ℝ) : ℝ := 5 / 2 * (ℛ + T)

/-- The step-length condition `LT² ≤ min(K/L, 1/4, 1/(16Λ))` with `Λ = 16Lℛ²` of Theorem 2.3
(equivalently (38), and (27) with `h₁ = 0`); the third clause is written without division,
as `256 L² ℛ² T² ≤ 1`, so that `ℛ = 0` imposes no constraint. -/
def StepCond (L K ℛ T : ℝ) : Prop :=
  L * T ^ 2 ≤ K / L ∧ L * T ^ 2 ≤ 1 / 4 ∧ 256 * L ^ 2 * ℛ ^ 2 * T ^ 2 ≤ 1

/-- The concave function `f(r) = ∫₀ʳ exp(-a min(s, R₁)) ds` of (26). -/
noncomputable def fConc (a R1 r : ℝ) : ℝ := ∫ s in (0 : ℝ)..r, Real.exp (-(a * min s R1))

/-- The distance `ρ(x, y) = f(|x - y|)` of (25). -/
noncomputable def rhoC {d : ℕ} (a R1 : ℝ) (x y : E d) : ℝ := fConc a R1 ‖x - y‖

/-- The contraction rate
`c = (1/10) min(1, ½ K T² (1 + ℛ/T) e^{-ℛ/(2T)}) e^{-2ℛ/T}` of (32). -/
noncomputable def rateC (K T ℛ : ℝ) : ℝ :=
  1 / 10 * min 1 (1 / 2 * K * T ^ 2 * (1 + ℛ / T) * Real.exp (-(ℛ / (2 * T)))) *
    Real.exp (-(2 * ℛ / T))

/-- The law of the randomness `(ξ, Ũ)` of one coupled step of exact HMC:
`ξ ∼ N(0, I_d)` and, independently, `Ũ ∼ Unif(0, 1)`. -/
noncomputable def noiseLaw (d : ℕ) : Measure (E d × ℝ) :=
  (stdGaussian (E d)).prod (volume.restrict (Set.Ioo (0 : ℝ) 1))

/-- The velocity `η` of (21) for `z = x - y`, `e = z/|z|`:
`η = ξ + γz` if `u ≤ φ₀,₁(e·ξ + γ|z|)/φ₀,₁(e·ξ)`, and `η = ξ - 2(e·ξ)e` otherwise,
where `φ₀,₁` is the standard normal density. -/
noncomputable def reflEta {d : ℕ} (γ : ℝ) (z ξ : E d) (u : ℝ) : E d :=
  let e : E d := ‖z‖⁻¹ • z
  if u ≤ gaussianPDFReal 0 1 (⟪e, ξ⟫_ℝ + γ * ‖z‖) / gaussianPDFReal 0 1 ⟪e, ξ⟫_ℝ then ξ + γ • z
  else ξ - (2 * ⟪e, ξ⟫_ℝ) • e

/-- The velocity used for the copy started at `y`: the reflection/maximal coupling (19)–(21)
if `|x - y| < 2ℛ`, and the synchronous coupling (18) (`η = ξ`) otherwise. -/
noncomputable def couplingEta {d : ℕ} (γ ℛ : ℝ) (x y ξ : E d) (u : ℝ) : E d :=
  if ‖x - y‖ < 2 * ℛ then reflEta γ (x - y) ξ u else ξ

/-- The coupling distance after one step of exact HMC,
`R'(x, y) = |X'(x, y) - Y'(x, y)| = |q_T(x, ξ) - q_T(y, η)|`, as a function of `ω = (ξ, Ũ)`. -/
noncomputable def Rprime {d : ℕ} (q : ℝ → E d → E d → E d) (T γ ℛ : ℝ) (x y : E d)
    (ω : E d × ℝ) : ℝ :=
  ‖q T x ω.1 - q T y (couplingEta γ ℛ x y ω.1 ω.2)‖

/-- `π` is the transition kernel (9) of exact HMC with duration `T`:
`π(x, ·)` is the law of `q_T(x, ξ)` with `ξ ∼ N(0, I_d)`. -/
def IsExactHMCKernel {d : ℕ} (q : ℝ → E d → E d → E d) (T : ℝ) (π : Kernel (E d) (E d)) :
    Prop :=
  ∀ x, π x = (stdGaussian (E d)).map (q T x)

/-- The `n`-step kernel `πⁿ`: `π⁰ = id`, `πⁿ⁺¹ = π ∘ πⁿ`; `νπⁿ = ν.bind (iterKernel π n)`. -/
noncomputable def iterKernel {d : ℕ} (π : Kernel (E d) (E d)) : ℕ → Kernel (E d) (E d)
  | 0 => Kernel.id
  | n + 1 => π ∘ₖ iterKernel π n

/-- The Kantorovich distance `𝒲_c(ν, η) = inf_{γ ∈ C(ν, η)} ∫ c(x, y) γ(dx dy)` for a cost
`c`, valued in `[0, ∞]`; the infimum runs over all couplings of `ν` and `η`. -/
noncomputable def kantorovich {d : ℕ} (c : E d → E d → ℝ) (ν η : Measure (E d)) : ℝ≥0∞ :=
  ⨅ γ ∈ MongeKantorovichYao.transferencePlans ν η, ∫⁻ p, ENNReal.ofReal (c p.1 p.2) ∂γ

/-- The target measure `μ(dx) = 𝒵⁻¹ exp(-U(x)) dx` of (2), `𝒵 = ∫ exp(-U(x)) dx`. -/
noncomputable def targetMeasure {d : ℕ} (U : E d → ℝ) : Measure (E d) :=
  (ENNReal.ofReal (∫ x, Real.exp (-U x)))⁻¹ •
    volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-U x)))

end CouplingHMC.Exact


