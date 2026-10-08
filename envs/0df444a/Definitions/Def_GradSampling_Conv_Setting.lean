-- Prove2me | Definitions.Def_GradSampling_Conv_Setting
-- name    : GradSampling_Conv_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T04:47:47.129273+00:00
-- url     : https://prove2.me/theorems/c49365d5-89af-4367-9668-6aa9b9c1e08d
-- title:
--   §2–§3, pp. 754–758 — G_ε, ρ_ε of (1), the Clarke ε-subdifferential, ℒ, V_ε, and the GS algorithm (Steps 0–4) with random sampling
-- statement:
--   Throughout, $\mathbb R^n$ carries the Euclidean norm $\|\cdot\|$, $\mathbb B=\{x : \|x\|\le 1\}$ is the closed unit ball, $f:\mathbb R^n\to\mathbb R$, and $D\subseteq\mathbb R^n$ is the set on which $f$ is continuously differentiable. $\bar\partial f(x)$ is the Clarke subdifferential (the published item `ClarkeGradients.Shared.generalizedGradient`).
--
--   1. **Level set.** For $\tilde x\in\mathbb R^n$, $\mathcal L=\{x : f(x)\le f(\tilde x)\}$.
--   2. **Sampled-gradient sets.** For $\epsilon>0$,
--   $$G_\epsilon(x)=\operatorname{cl}\operatorname{conv}\nabla f\big((x+\epsilon\mathbb B)\cap D\big),\qquad \rho_\epsilon(x)=\operatorname{dist}\big(0\mid G_\epsilon(x)\big).$$
--   3. **Clarke $\epsilon$-subdifferential** (Goldstein): $\bar\partial_\epsilon f(x)=\operatorname{cl}\operatorname{conv}\bar\partial f(x+\epsilon\mathbb B)$, the closed convex hull of $\bigcup_{\|y-x\|\le\epsilon}\bar\partial f(y)$. A point $x$ is *Clarke $\epsilon$-stationary* if $0\in\bar\partial_\epsilon f(x)$.
--   4. **Least-norm element.** $g$ is a least-norm element of $G$ if $g\in G$ and $\|g\|\le\|h\|$ for all $h\in G$.
--   5. **$V_\epsilon(x',x,\delta)$** is the set of $m$-tuples $(x^1,\dots,x^m)$ with every $x^j\in D\cap(x+\epsilon\mathbb B)$ for which there are $\lambda_j\ge0$, $\sum_j\lambda_j=1$, with $\big\|\sum_j\lambda_j\nabla f(x^j)\big\|\le\rho_\epsilon(x')+\delta$.
--   6. **The GS algorithm.** Given $x^0$, $\gamma,\beta,\epsilon_0,\nu_0,\mu,\theta$, $m$ and unit-ball samples $u^{kj}$, a run consists of iterates $x^k$, radii $\epsilon_k$, tolerances $\nu_k$, step lengths $t_k$, vectors $g^k$, directions $d^k$ and a stopping iteration $\tau\in\mathbb N\cup\{\infty\}$, such that $(x^0,\epsilon_0,\nu_0)$ are the given values and, for every iteration $k\le\tau$:
--      - *Step 1.* The sampling points are $x^{kj}=x^k+\epsilon_k u^{kj}$, $j=1,\dots,m$; if all lie in $D$, $g^k$ is the least-norm element of $G_k=\operatorname{conv}\{\nabla f(x^k),\nabla f(x^{k1}),\dots,\nabla f(x^{km})\}$.
--      - *Stopping.* $\tau=k$ exactly when some $x^{kj}\notin D$ (Step 1 STOP), or all $x^{kj}\in D$ and $\nu_k=\|g^k\|=0$ (Step 2 STOP).
--      - *Step 2.* If $k<\tau$ and $\|g^k\|\le\nu_k$: $t_k=0$, $\nu_{k+1}=\theta\nu_k$, $\epsilon_{k+1}=\mu\epsilon_k$.
--      - *Steps 2–3.* If $k<\tau$ and $\|g^k\|>\nu_k$: $\nu_{k+1}=\nu_k$, $\epsilon_{k+1}=\epsilon_k$, $d^k=-g^k/\|g^k\|$, and $t_k=\gamma^s$ with $s\in\{0,1,2,\dots\}$ the least integer for which $f(x^k+\gamma^s d^k)<f(x^k)-\beta\gamma^s\|g^k\|$.
--      - *Step 4.* If $k<\tau$: when $x^k+t_kd^k\in D$, $x^{k+1}=x^k+t_kd^k$; otherwise $x^{k+1}=\hat x^k+t_kd^k$ for some $\hat x^k\in x^k+\epsilon_k\mathbb B$ with $\hat x^k+t_kd^k\in D$ and $f(\hat x^k+t_kd^k)<f(x^k)-\beta t_k\|g^k\|$ (display (2)).
--   7. **Random run.** On a probability space $(\Omega,P)$ with a filtration $(\mathcal F_k)$, random sequences form a random GS run if every sample path is a run as in item 6; each $u^{kj}$ is uniformly distributed on $\mathbb B$; $u^{k1},\dots,u^{km}$ are independent; the tuple $(u^{k1},\dots,u^{km})$ is independent of $\mathcal F_k$ and $\mathcal F_{k+1}$-measurable; and $x^k,\epsilon_k,\nu_k$ are $\mathcal F_k$-measurable.
--
--   These are the objects of §2 and §3 on which every statement of the mission is built: the GS algorithm approximates the Clarke $\epsilon$-subdifferential by the convex hull of gradients at randomly sampled nearby points, and $\rho_\epsilon$ measures how far $x$ is from Clarke $\epsilon$-stationarity.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)` and $\nabla f$ is Mathlib's `gradient f`. $\operatorname{dist}(0\mid C)$ is `Metric.infDist 0 C`, which is $0$ for $C=\emptyset$; with $D$ dense and $\epsilon>0$ the set $G_\epsilon(x)$ is nonempty. "$\max\gamma^s$" in Step 3 is encoded as the least $s$ (for $\gamma\in(0,1)$, $\gamma^s$ decreases in $s$). The run imposes nothing after iteration $\tau$, and $d^k$ is unconstrained in the branch $t_k=0$, where $t_kd^k=0$. The paper's "realization of a stochastic process" and its nondeterministic Step 4 are made precise by the filtration: $\hat x^k$ may depend on the past and on extra randomness, never on future samples. The paper's event $\mathcal E$ (realizations hitting every positive-measure subset of $\mathbb B^m$ infinitely often) is not formalized, since no sequence has that property; the theorems speak of "almost surely" directly.
-- source:
--   Burke, Lewis, Overton, A robust gradient sampling algorithm for nonsmooth, nonconvex optimization, SIAM J. Optim. 15 (2005), pp. 754–758: §2 (ℒ, G_ε, ∂̄_ε f, display (1), the GS algorithm Steps 0–4 and display (2) on p. 755, the stochastic structure on p. 757) and §3 (V_ε, p. 758)

import Mathlib
import Definitions.Def_ClarkeGradients_Shared_generalizedGradient

open MeasureTheory ProbabilityTheory

namespace GradSampling.Conv

/-- The level set `ℒ = {x | f(x) ≤ f(x̃)}` (Burke–Lewis–Overton 2005, §2, p. 754). -/
def levelSet {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (xt : EuclideanSpace ℝ (Fin n)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {x | f x ≤ f xt}

/-- `G_ε(x) = cl conv ∇f((x + ε𝔹) ∩ D)`, where `𝔹` is the closed Euclidean unit ball (§2, p. 754). -/
def Gset {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (D : Set (EuclideanSpace ℝ (Fin n))) (ε : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  closure (convexHull ℝ (gradient f '' (Metric.closedBall x ε ∩ D)))

/-- Display (1), p. 754: `ρ_ε(x) = dist(0 | G_ε(x))`, the Euclidean distance from the origin to
`G_ε(x)`. -/
noncomputable def rho {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (D : Set (EuclideanSpace ℝ (Fin n)))
    (ε : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Metric.infDist 0 (Gset f D ε x)

/-- The Clarke `ε`-subdifferential of Goldstein, `∂̄_ε f(x) = cl conv ∂̄f(x + ε𝔹)`: the closed convex
hull of the union of the Clarke subdifferentials `∂̄f(y)` over the closed ball `‖y − x‖ ≤ ε`
(§2, p. 754). A point `x` is Clarke `ε`-stationary when `0 ∈ ∂̄_ε f(x)`. -/
def epsSubdiff {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (ε : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  closure (convexHull ℝ
    (⋃ y ∈ Metric.closedBall x ε, ClarkeGradients.Shared.generalizedGradient f y))

/-- `g` is an element of least Euclidean norm of `G`: `g ∈ G` and `‖g‖ = dist(0 | G)`. -/
def IsMinNormIn {n : ℕ} (g : EuclideanSpace ℝ (Fin n)) (G : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  g ∈ G ∧ ∀ h ∈ G, ‖g‖ ≤ ‖h‖

/-- Step 1 of the GS algorithm, p. 755: `G_k = conv {∇f(x^{k0}), ∇f(x^{k1}), …, ∇f(x^{km})}`, with
`x^{k0} = x` the current iterate and `x^{kj} = pts j` the `m` sampling points. -/
def sampleHull {n m : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (pts : Fin m → EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  convexHull ℝ (insert (gradient f x) (Set.range fun j => gradient f (pts j)))

/-- §3, p. 758: `V_ε(x′, x, δ)` is the set of `m`-tuples `(x¹, …, x^m)` with every `x^j ∈ D ∩ (x + ε𝔹)`
for which some convex combination `Σ λ_j ∇f(x^j)` (`λ_j ≥ 0`, `Σ λ_j = 1`) has norm at most
`ρ_ε(x′) + δ`. -/
def Vset {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (D : Set (EuclideanSpace ℝ (Fin n))) (ε : ℝ)
    (m : ℕ) (x' x : EuclideanSpace ℝ (Fin n)) (δ : ℝ) : Set (Fin m → EuclideanSpace ℝ (Fin n)) :=
  {y | (∀ i, y i ∈ D ∩ Metric.closedBall x ε) ∧
    ∃ lam : Fin m → ℝ, (∀ i, 0 ≤ lam i) ∧ ∑ i, lam i = 1 ∧
      ‖∑ i, lam i • gradient f (y i)‖ ≤ rho f D ε x' + δ}

/-- The sampling points of Step 1, p. 755: `x^{kj} = x^k + ε_k u^{kj}`, `j = 1, …, m`. -/
def samplePts {n m : ℕ} (X : ℕ → EuclideanSpace ℝ (Fin n)) (eps : ℕ → ℝ)
    (u : ℕ → Fin m → EuclideanSpace ℝ (Fin n)) (k : ℕ) (j : Fin m) : EuclideanSpace ℝ (Fin n) :=
  X k + eps k • u k j

/-- The two STOP rules of the GS algorithm at iteration `k` (p. 755): Step 1 stops when some sampling
point `x^{kj}` lies outside `D`; Step 2 stops when all sampling points lie in `D` and
`ν_k = ‖g^k‖ = 0`. -/
def StopsAt {n m : ℕ} (D : Set (EuclideanSpace ℝ (Fin n))) (X : ℕ → EuclideanSpace ℝ (Fin n))
    (eps nu : ℕ → ℝ) (g : ℕ → EuclideanSpace ℝ (Fin n)) (u : ℕ → Fin m → EuclideanSpace ℝ (Fin n))
    (k : ℕ) : Prop :=
  (∃ j, samplePts X eps u k j ∉ D) ∨
    ((∀ j, samplePts X eps u k j ∈ D) ∧ nu k = ‖g k‖ ∧ ‖g k‖ = 0)

/-- The Armijo test of Step 3, p. 755, for the trial step `γ^s`:
`f(x^k + γ^s d^k) < f(x^k) − β γ^s ‖g^k‖` (strict). -/
def Armijo {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (γ β : ℝ) (X : ℕ → EuclideanSpace ℝ (Fin n))
    (g d : ℕ → EuclideanSpace ℝ (Fin n)) (k s : ℕ) : Prop :=
  f (X k + γ ^ s • d k) < f (X k) - β * γ ^ s * ‖g k‖

/-- A run of the GS algorithm (Steps 0–4, p. 755) on the sample realization `u` (`u k j = u^{kj}`):
iterates `X k = x^k`, sampling radii `eps k = ε_k`, optimality tolerances `nu k = ν_k`, step lengths
`t k = t_k`, shortest approximate subgradients `g k = g^k`, search directions `d k = d^k`, and the
iteration `τ` at which the algorithm stops (`τ = ⊤`: it never stops). Nothing is required of the
sequences after iteration `τ`. -/
structure IsGSRun {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (D : Set (EuclideanSpace ℝ (Fin n)))
    (x0 : EuclideanSpace ℝ (Fin n)) (γ β ε0 ν0 μ θ : ℝ) (m : ℕ)
    (u : ℕ → Fin m → EuclideanSpace ℝ (Fin n)) (X : ℕ → EuclideanSpace ℝ (Fin n))
    (eps nu t : ℕ → ℝ) (g d : ℕ → EuclideanSpace ℝ (Fin n)) (τ : ℕ∞) : Prop where
  /-- Step 0: `x^0`, `ε_0`, `ν_0` are the given initial values. -/
  init : X 0 = x0 ∧ eps 0 = ε0 ∧ nu 0 = ν0
  /-- Steps 1–2: when every sampling point lies in `D`, `g^k` is the least-norm element of `G_k`. -/
  minNorm : ∀ k : ℕ, (k : ℕ∞) ≤ τ → (∀ j, samplePts X eps u k j ∈ D) →
    IsMinNormIn (g k) (sampleHull f (X k) (samplePts X eps u k))
  /-- The algorithm stops at iteration `k` exactly when one of the two STOP rules fires. -/
  stop_iff : ∀ k : ℕ, (k : ℕ∞) ≤ τ → (τ = (k : ℕ∞) ↔ StopsAt D X eps nu g u k)
  /-- Step 2, second branch: if `‖g^k‖ ≤ ν_k`, then `t_k = 0`, `ν_{k+1} = θ ν_k`, `ε_{k+1} = μ ε_k`. -/
  shrink : ∀ k : ℕ, (k : ℕ∞) < τ → ‖g k‖ ≤ nu k →
    t k = 0 ∧ nu (k + 1) = θ * nu k ∧ eps (k + 1) = μ * eps k
  /-- Step 2, third branch, and Step 3: if `‖g^k‖ > ν_k`, then `ν_{k+1} = ν_k`, `ε_{k+1} = ε_k`,
  `d^k = −g^k/‖g^k‖`, and `t_k = γ^s` for the least `s ∈ {0, 1, 2, …}` passing the Armijo test
  (that is, `t_k` is the largest such `γ^s`). -/
  descend : ∀ k : ℕ, (k : ℕ∞) < τ → nu k < ‖g k‖ →
    nu (k + 1) = nu k ∧ eps (k + 1) = eps k ∧ d k = -(‖g k‖⁻¹ • g k) ∧
      ∃ s : ℕ, t k = γ ^ s ∧ Armijo f γ β X g d k s ∧ ∀ s' < s, ¬ Armijo f γ β X g d k s'
  /-- Step 4: if `x^k + t_k d^k ∈ D` then `x^{k+1} = x^k + t_k d^k`; otherwise `x^{k+1} = x̂^k + t_k d^k`
  for some `x̂^k ∈ x^k + ε_k𝔹` with `x̂^k + t_k d^k ∈ D` and (2):
  `f(x̂^k + t_k d^k) < f(x^k) − β t_k ‖g^k‖`. -/
  update : ∀ k : ℕ, (k : ℕ∞) < τ →
    (X k + t k • d k ∈ D → X (k + 1) = X k + t k • d k) ∧
    (X k + t k • d k ∉ D → ∃ xh ∈ Metric.closedBall (X k) (eps k),
      xh + t k • d k ∈ D ∧ f (xh + t k • d k) < f (X k) - β * t k * ‖g k‖ ∧
        X (k + 1) = xh + t k • d k)

/-- The GS algorithm run on random samples (p. 755 and p. 757). On a probability space `(Ω, P)` with a
filtration `ℱ` (the information available at the start of each iteration):
every sample path is a run of the GS algorithm; each `u^{kj}` is uniformly distributed on the closed
unit ball `𝔹`; `u^{k1}, …, u^{km}` are independent; the tuple `(u^{k1}, …, u^{km})` is independent of
`ℱ_k` and `ℱ_{k+1}`-measurable; and `x^k`, `ε_k`, `ν_k` are `ℱ_k`-measurable. Hence the choice of
`x̂^k` in Step 4 may use the past and additional randomness, but not future samples. -/
structure IsRandomGSRun {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (D : Set (EuclideanSpace ℝ (Fin n)))
    (x0 : EuclideanSpace ℝ (Fin n)) (γ β ε0 ν0 μ θ : ℝ) (m : ℕ)
    (U : ℕ → Fin m → Ω → EuclideanSpace ℝ (Fin n)) (X : ℕ → Ω → EuclideanSpace ℝ (Fin n))
    (eps nu t : ℕ → Ω → ℝ) (g d : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (τ : Ω → ℕ∞) : Prop where
  /-- Every sample path is a run of the GS algorithm. -/
  run : ∀ ω, IsGSRun f D x0 γ β ε0 ν0 μ θ m (fun k j => U k j ω) (fun k => X k ω)
    (fun k => eps k ω) (fun k => nu k ω) (fun k => t k ω) (fun k => g k ω) (fun k => d k ω) (τ ω)
  /-- Each `u^{kj}` is uniformly distributed on the closed unit ball `𝔹`. -/
  uniform : ∀ k j, pdf.IsUniform (U k j) (Metric.closedBall 0 1) P volume
  /-- `u^{k1}, …, u^{km}` are sampled independently. -/
  indep_within : ∀ k, iIndepFun (fun j => U k j) P
  /-- The `k`-th sample tuple is independent of the information `ℱ_k` available before it is drawn. -/
  indep_past : ∀ k, Indep (MeasurableSpace.comap (fun ω j => U k j ω) inferInstance) (ℱ k) P
  /-- The `k`-th sample tuple is known at time `k + 1`. -/
  sample_adapted : ∀ k j, Measurable[ℱ (k + 1)] (U k j)
  /-- `x^k`, `ε_k` and `ν_k` are known at time `k`. -/
  iterate_adapted : ∀ k, Measurable[ℱ k] (X k) ∧ Measurable[ℱ k] (eps k) ∧ Measurable[ℱ k] (nu k)

end GradSampling.Conv


