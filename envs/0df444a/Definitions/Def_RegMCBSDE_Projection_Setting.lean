-- Prove2me | Definitions.Def_RegMCBSDE_Projection_Setting
-- name    : RegMCBSDE_Projection_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T06:36:13.976268+00:00
-- url     : https://prove2.me/theorems/5855a542-bf47-4291-98f5-42dfe758a849
-- title:
--   §2.1, (3), pp. 4–6 — standing data (H1)–(H2), the time grid, the Euler scheme and the probabilistic model
-- statement:
--   This file fixes the data and the standing hypotheses of Gobet, Lemor and Warin's regression scheme for backward stochastic differential equations.
--
--   Let $T>0$ be the horizon and $d,q\ge 1$ the dimensions of the state and of the driving noise. The drift $b:[0,T]\times\mathbb R^d\to\mathbb R^d$, the diffusion $\sigma:[0,T]\times\mathbb R^d\to\mathbb R^{d\times q}$ and the driver $f:[0,T]\times\mathbb R^d\times\mathbb R\times\mathbb R^q\to\mathbb R$ satisfy:
--
--   1. **(H1)** there is $L$ with $|b(t,x)-b(t',x')|+\|\sigma(t,x)-\sigma(t',x')\|_F\le L(|t-t'|+|x-x'|)$ for $t,t'\in[0,T]$, $x,x'\in\mathbb R^d$, where $\|\cdot\|_F$ is the Frobenius norm;
--   2. **(H2)** for $t_1,t_2\in[0,T]$ and all $x_i,y_i,z_i$,
--   $$|f(t_2,x_2,y_2,z_2)-f(t_1,x_1,y_1,z_1)|\le C_f\big(|t_2-t_1|^{1/2}+|x_2-x_1|+|y_2-y_1|+|z_2-z_1|\big).$$
--
--   For $N\ge1$ the time step is $h=T/N$ and the grid is $t_k=kh$. Given increments $\Delta W_k$, the **Euler scheme** (3) is $S^N_{t_0}=S_0$ and
--   $$S^N_{t_{k+1}}=S^N_{t_k}+b(t_k,S^N_{t_k})\,h+\sigma(t_k,S^N_{t_k})\,\Delta W_k .$$
--
--   The **standing model** on a probability space $(\Omega,\mathcal F,\mathbb P)$ with a filtration $(\mathcal F_k)_k$ ($\mathcal F_k$ standing for $\mathcal F_{t_k}$) requires, for $k<N$:
--
--   1. $\Delta W_k\in\mathbb R^q$ is $\mathcal F_{k+1}$-measurable, independent of $\mathcal F_k$, and has law $\mathcal N(0,hI_q)$ (independent components of law $\mathcal N(0,h)$);
--   2. the chain $P^N_{t_k}\in\mathbb R^{d'}$, $d'\ge d$, is $\mathcal F_k$-measurable (for $k\le N$) and its first $d$ components are those of $S^N_{t_k}$;
--   3. the terminal function $\Phi^N:\mathbb R^{d'}\to\mathbb R$ is measurable with $\mathbb E[\Phi^N(P^N_{t_N})]^2<\infty$.
--
--   These are the objects every result of §4 of the paper is about.
--
--   **Formalization Note** The paper assumes (H1)–(H3); (H3) is a functional Lipschitz condition on the terminal functional $\Phi$ of the continuous path, which no statement of this mission involves, so it is dropped. The paper's $\mathcal F_t$ is the augmented Brownian filtration and $\Delta W_k=W_{t_{k+1}}-W_{t_k}$; these satisfy the three listed properties, which are all the statements use, so the model quantifies over every such filtration and increment family. The paper's description of $P^N$ as a Markov chain $P^N_{t_k}=F^N_k(U_k,P^N_{t_{k-1}})$ is used only by Propositions 1 and 3, and is not part of the model. Component $m$ of the Lean vector $\Delta W_k$ (indexed from $0$) is the paper's $\Delta W_{m+1,k}$.
-- source:
--   Gobet, Lemor and Warin, A regression-based Monte Carlo method to solve backward stochastic differential equations, arXiv:math/0508491v1, pp. 4–6, §2.1 (H1)–(H2), Eq. (3) and §2.2

import Mathlib

namespace RegMCBSDE.Projection

open MeasureTheory ProbabilityTheory

/-- The Frobenius norm `‖A‖_F = (∑_{i,j} a_{ij}^2)^{1/2}` of a real `d × q` matrix; it is the
matrix norm used in (H1) (all matrix norms are equivalent, and the Lipschitz constant absorbs the
choice). -/
noncomputable def frobNorm {d q : ℕ} (A : Matrix (Fin d) (Fin q) ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, A i j ^ 2)

/-- **(H1)** (Gobet–Lemor–Warin, p. 4), with an explicit Lipschitz constant `L`: the drift
`b : [0,T] × ℝ^d → ℝ^d` and the diffusion `σ : [0,T] × ℝ^d → ℝ^{d×q}` are uniformly Lipschitz
continuous in `(t, x) ∈ [0,T] × ℝ^d`. -/
def H1 (T L : ℝ) {d q : ℕ}
    (b : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (σ : ℝ → EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin q) ℝ) : Prop :=
  ∀ t t' : ℝ, t ∈ Set.Icc 0 T → t' ∈ Set.Icc 0 T → ∀ x x' : EuclideanSpace ℝ (Fin d),
    ‖b t x - b t' x'‖ + frobNorm (σ t x - σ t' x') ≤ L * (|t - t'| + ‖x - x'‖)

/-- **(H2)** (p. 4): the driver `f : [0,T] × ℝ^d × ℝ × ℝ^q → ℝ` satisfies
`|f(t₂,x₂,y₂,z₂) - f(t₁,x₁,y₁,z₁)| ≤ C_f (|t₂ - t₁|^{1/2} + |x₂ - x₁| + |y₂ - y₁| + |z₂ - z₁|)`
for `t₁, t₂ ∈ [0,T]`. -/
def H2 (T Cf : ℝ) {d q : ℕ}
    (f : ℝ → EuclideanSpace ℝ (Fin d) → ℝ → EuclideanSpace ℝ (Fin q) → ℝ) : Prop :=
  ∀ t₁ t₂ : ℝ, t₁ ∈ Set.Icc 0 T → t₂ ∈ Set.Icc 0 T →
    ∀ (x₁ x₂ : EuclideanSpace ℝ (Fin d)) (y₁ y₂ : ℝ) (z₁ z₂ : EuclideanSpace ℝ (Fin q)),
      |f t₂ x₂ y₂ z₂ - f t₁ x₁ y₁ z₁|
        ≤ Cf * (Real.sqrt |t₂ - t₁| + ‖x₂ - x₁‖ + |y₂ - y₁| + ‖z₂ - z₁‖)

/-- The grid time `t_k = k h = k T / N` (p. 5). -/
noncomputable def gridTime (T : ℝ) (N k : ℕ) : ℝ := (k : ℝ) * (T / N)

/-- **The Euler scheme (3)** (p. 5), driven by the increments `ΔW k = W_{t_{k+1}} - W_{t_k}`:
`S^N_{t_0} = S_0` and
`S^N_{t_{k+1}} = S^N_{t_k} + b(t_k, S^N_{t_k}) h + σ(t_k, S^N_{t_k}) ΔW_k`, with `h = T/N`. -/
noncomputable def euler {Ω : Type*} {d q : ℕ} (T : ℝ) (N : ℕ)
    (b : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (σ : ℝ → EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin q) ℝ)
    (S0 : EuclideanSpace ℝ (Fin d)) (ΔW : ℕ → Ω → EuclideanSpace ℝ (Fin q)) :
    ℕ → Ω → EuclideanSpace ℝ (Fin d)
  | 0 => fun _ => S0
  | k + 1 => fun ω =>
      euler T N b σ S0 ΔW k ω + (T / N) • b (gridTime T N k) (euler T N b σ S0 ΔW k ω)
        + Matrix.toEuclideanLin (σ (gridTime T N k) (euler T N b σ S0 ΔW k ω)) (ΔW k ω)

/-- **The standing probabilistic model** (§2.1–2.2, pp. 4–6) on a probability space
`(Ω, 𝓕, P)` with a filtration `𝓕 k` (standing for `𝓕_{t_k}`), for the grid `h = T/N`:

* `ΔW k` (`k < N`) is `𝓕_{k+1}`-measurable, independent of `𝓕_k`, and has law `𝒩(0, h I_q)`
  (independent components, each with law `𝒩(0, h)`). Component `l` of `ΔW k` (`l : Fin q`) is the
  paper's `ΔW_{l+1,k}`.
* `PN : ℕ → Ω → ℝ^{d'}` is the chain `P^N`, with `d ≤ d'`, `P^N_{t_k}` is `𝓕_k`-measurable, and its
  first `d` components are those of the Euler scheme `S^N_{t_k}`.
* `ΦN : ℝ^{d'} → ℝ` is measurable and `𝔼[Φ^N(P^N_{t_N})]^2 < ∞`.

The augmented Brownian filtration and `ΔW_k = W_{t_{k+1}} - W_{t_k}` satisfy these properties; the
Markov representation of `P^N` and the hypothesis (H3) on the continuous terminal functional are not
used by the results of §4 and are not part of the model. -/
structure IsStandingModel {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (𝓕 : Filtration ℕ mΩ) {d q d' : ℕ} (T : ℝ) (N : ℕ)
    (b : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (σ : ℝ → EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin q) ℝ)
    (S0 : EuclideanSpace ℝ (Fin d)) (ΔW : ℕ → Ω → EuclideanSpace ℝ (Fin q))
    (PN : ℕ → Ω → EuclideanSpace ℝ (Fin d')) (ΦN : EuclideanSpace ℝ (Fin d') → ℝ) : Prop where
  increment_measurable : ∀ k < N, Measurable[𝓕 (k + 1)] (ΔW k)
  increment_indep : ∀ k < N, Indep (MeasurableSpace.comap (ΔW k) inferInstance) (𝓕 k) P
  increment_components_indep : ∀ k < N, iIndepFun (fun (l : Fin q) ω => ΔW k ω l) P
  increment_law : ∀ k < N, ∀ l : Fin q,
    P.map (fun ω => ΔW k ω l) = gaussianReal 0 (T / N).toNNReal
  dim_le : d ≤ d'
  chain_adapted : ∀ k ≤ N, Measurable[𝓕 k] (PN k)
  chain_first_components : ∀ k ≤ N, ∀ ω, ∀ i : Fin d,
    PN k ω (Fin.castLE dim_le i) = euler T N b σ S0 ΔW k ω i
  terminal_measurable : Measurable ΦN
  terminal_memLp : MemLp (fun ω => ΦN (PN N ω)) 2 P

end RegMCBSDE.Projection


