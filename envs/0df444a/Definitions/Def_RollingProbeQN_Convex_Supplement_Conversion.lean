-- Prove2me | Definitions.Def_RollingProbeQN_Convex_Supplement_Conversion
-- name    : RollingProbeQN_Convex_Supplement_Conversion
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:44:56.930678+00:00
-- url     : https://prove2.me/theorems/2e028746-59fe-4264-bc2f-704188983684
-- title:
--   The online-to-nonconvex conversion with the optimistic learner, (23)–(31)
-- statement:
--   Fix a radius $D>0$, a learning rate $\eta>0$ and an accuracy $\nu$. Given increments $\Delta_n$ with $\Delta_0=0$ and symmetric matrices $B_n$, the **conversion** (23) defines, for $n\ge1$,
--   $$x_n=x_{n-1}+\Delta_n,\qquad w_n=x_{n-1}+\tfrac12\Delta_n,\qquad z_n=x_n+\tfrac12\Delta_n,$$
--   with $z_0=x_0$, and the prediction errors $\theta_0=0$, $\theta_{n+1}=\nabla f(w_{n+1})-\nabla f(z_n)-\tfrac12B_n(\Delta_{n+1}-\Delta_n)$ (29).
--
--   A point $\Delta$ is a **$\nu$-approximate solution of the subproblem at step $n$** (31) if $\|\Delta\|\le D$ and there is $\varrho\ge0$ with $\varrho(\|\Delta\|-D)=0$ and $\|\nabla\phi_n(\Delta)+\varrho\Delta\|\le\nu$, where
--   $$\nabla\phi_n(\Delta)=\nabla f(z_n)+\theta_n+\tfrac12B_n(\Delta-\Delta_n)+\eta^{-1}(\Delta-\Delta_n)$$
--   is the gradient of the trust-region objective $\phi_n$ of (30). The **conversion with the optimistic learner** requires $\Delta_{n+1}$ to be such a solution at every step $n$.
--
--   Episodes are $\mathcal N_k=\{(k-1)T+1,\dots,kT\}$; the summed loss is $G_k=\sum_{n\in\mathcal N_k}\nabla f(w_n)$ (26), the episode average is $\bar w_k=\frac1T\sum_{n\in\mathcal N_k}w_n$, and the output is $\bar w_{k^\star}$ for an episode $k^\star\in\arg\min_{1\le k\le K}\|G_k\|$.
--
--   **Formalization Note** The sequences $B$ and $\Delta$ are arbitrary, and the run is a predicate on them, so every symmetric model and every choice of approximate solution is covered. The episode sum and average take the observed gradients and midpoints as sequences, so Algorithm 3 reuses them with its oracle answers. $\nabla\phi_n$ is written by its formula (81), valid for symmetric $B_n$. Ties in $\arg\min$ are not broken: the theorems hold for every minimizing $k^\star$.
-- source:
--   Mokhtari, Patitucci, Improved Gradient Complexity for Quasi-Newton Proximal Extragradient Methods via Certified Curvature Reuse, arXiv:2610.40608, (23)–(31), pp. 18–19; (81), p. 72; Lemma I.1, p. 70

import Mathlib

namespace RollingProbeQN.Convex.Supplement

/-- **ν-approximate solution of the subproblem, (30)–(31).**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, (30)–(31), p. 19:
"`φn(Δ) = ⟨∇f(zn) + θn, Δ⟩ + 1/4⟨Bn(Δ − Δn), Δ − Δn⟩ + 1/(2η)‖Δ − Δn‖²` […] We call a point `Δ` with
`‖Δ‖ ≤ D` a `ν`-approximate solution of the subproblem at step `n` if `‖∇φn(Δ) + ϱΔ‖ ≤ ν` for some
`ϱ ≥ 0` with `ϱ(‖Δ‖ − D) = 0`", with (81), p. 72:
`∇φn(Δ) = ∇f(zn) + θn + 1/2 Bn(Δ − Δn) + 1/η(Δ − Δn)` for symmetric `Bn`.

`IsNuApprox D η ν gz θ B Δn Δ`: `gz` stands for `∇f(z_n)`, `θ` for `θ_n`, `B` for `B_n`, `Δn` for
`Δ_n`, and `Δ` is the candidate.

**Formalization Note.** The gradient of `φ_n` is written by the formula (81), which is the gradient for
symmetric `B`; every use has symmetric `B`. `B` acts on `ℝ^d` through `Matrix.toEuclideanLin`. -/
def IsNuApprox {d : ℕ} (D η ν : ℝ) (gz θ : EuclideanSpace ℝ (Fin d))
    (B : Matrix (Fin d) (Fin d) ℝ) (Δn Δ : EuclideanSpace ℝ (Fin d)) : Prop :=
  ‖Δ‖ ≤ D ∧ ∃ ϱ : ℝ, 0 ≤ ϱ ∧ ϱ * (‖Δ‖ - D) = 0 ∧
    ‖gz + θ + (1 / 2 : ℝ) • Matrix.toEuclideanLin B (Δ - Δn) + η⁻¹ • (Δ - Δn) + ϱ • Δ‖ ≤ ν

/-- **The iterates `x_n` of the conversion, (23).**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, (23), p. 18: "`xn = xn−1 + Δn`, […] `n ≥ 1`".

`convX x₀ Δ n = x₀ + Δ_1 + ⋯ + Δ_n`. -/
noncomputable def convX {d : ℕ} (x₀ : EuclideanSpace ℝ (Fin d))
    (Δ : ℕ → EuclideanSpace ℝ (Fin d)) (n : ℕ) : EuclideanSpace ℝ (Fin d) :=
  x₀ + ∑ i ∈ Finset.Icc 1 n, Δ i

/-- **The midpoints `w_n` of the conversion, (23).**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, (23), p. 18: "`wn = xn−1 + 1/2 Δn`, `n ≥ 1`".

**Formalization Note.** Only `n ≥ 1` is used. -/
noncomputable def convW {d : ℕ} (x₀ : EuclideanSpace ℝ (Fin d))
    (Δ : ℕ → EuclideanSpace ℝ (Fin d)) (n : ℕ) : EuclideanSpace ℝ (Fin d) :=
  convX x₀ Δ (n - 1) + (1 / 2 : ℝ) • Δ n

/-- **The probe points `z_n` of the conversion, (23).**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, (23), p. 18: "`zn = xn + 1/2 Δn`, `n ≥ 1`,
with `Δ0 = 0` and `z0 = x0`".

**Formalization Note.** The same formula at `n = 0` gives `z₀ = x₀` when `Δ 0 = 0`. -/
noncomputable def convZ {d : ℕ} (x₀ : EuclideanSpace ℝ (Fin d))
    (Δ : ℕ → EuclideanSpace ℝ (Fin d)) (n : ℕ) : EuclideanSpace ℝ (Fin d) :=
  convX x₀ Δ n + (1 / 2 : ℝ) • Δ n

/-- **The prediction errors `θ_n` of the optimistic learner, (27)–(29).**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, (27)–(29), pp. 18–19: "`θ0 = 0`",
"`hn+1 = ∇f(zn) + 1/2 Bn(Δn+1 − Δn)`", "`θn+1 = ∇f(wn+1) − hn+1`".

`convTheta f B x₀ Δ n` is `θ_n` for the increments `Δ` and the matrices `B`. -/
noncomputable def convTheta {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (B : ℕ → Matrix (Fin d) (Fin d) ℝ) (x₀ : EuclideanSpace ℝ (Fin d))
    (Δ : ℕ → EuclideanSpace ℝ (Fin d)) : ℕ → EuclideanSpace ℝ (Fin d)
  | 0 => 0
  | n + 1 => gradient f (convW x₀ Δ (n + 1)) - gradient f (convZ x₀ Δ n)
      - (1 / 2 : ℝ) • Matrix.toEuclideanLin (B n) (Δ (n + 1) - Δ n)

/-- **The conversion run with the optimistic learner and ν-approximate subproblem solutions,
for `N` iterations.**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, §5.1, pp. 18–19: increments `Δn` with
`Δ0 = 0`, symmetric models `Bn`, and `Δn+1` "a `ν`-approximate solution of the subproblem at step `n`"
(31), as in Theorem I.6, p. 73; "The conversion runs for `N = KT` iterations" (p. 18).

`IsOptimisticRun f x₀ D η ν B Δ N`: `Δ 0 = 0` and, for every step `n < N`, `B n` is symmetric and
`Δ (n+1)` is a ν-approximate solution at step `n` for `∇f(z_n)`, `θ_n`, `B_n`, `Δ_n`.

**Formalization Note.** `B` and `Δ` are arbitrary sequences (they may depend on the run in any way);
the predicate constrains only the realized steps `0, …, N − 1`, so every admissible choice of
approximate solutions is covered and nothing is required beyond the horizon. `‖Δ_n‖ ≤ D` for
`1 ≤ n ≤ N` is part of (31). -/
def IsOptimisticRun {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) (x₀ : EuclideanSpace ℝ (Fin d))
    (D η ν : ℝ) (B : ℕ → Matrix (Fin d) (Fin d) ℝ) (Δ : ℕ → EuclideanSpace ℝ (Fin d)) (N : ℕ) :
    Prop :=
  Δ 0 = 0 ∧ ∀ n < N, (B n).IsSymm ∧
    IsNuApprox D η ν (gradient f (convZ x₀ Δ n)) (convTheta f B x₀ Δ n) (B n) (Δ n) (Δ (n + 1))

/-- **The summed loss `G_k` of episode `k`, (26).**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, §5.1, p. 18: "`K` episodes
`Nk = {(k − 1)T + 1, . . . , kT}` of length `T`", "`Gk = ∑_{n∈Nk} ∇f(wn)`".

`epSum g T k = ∑_{n ∈ N_k} g n`, where `g n` is the observed gradient at the midpoint `w_n`. -/
noncomputable def epSum {d : ℕ} (g : ℕ → EuclideanSpace ℝ (Fin d)) (T k : ℕ) :
    EuclideanSpace ℝ (Fin d) :=
  ∑ n ∈ Finset.Icc ((k - 1) * T + 1) (k * T), g n

/-- **The episode average `w̄_k` of the midpoints.**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, §5.1, p. 18 and Lemma I.1, p. 70:
"`w̄k = 1/T ∑_{n∈Nk} wn`". -/
noncomputable def epAvg {d : ℕ} (w : ℕ → EuclideanSpace ℝ (Fin d)) (T k : ℕ) :
    EuclideanSpace ℝ (Fin d) :=
  ((T : ℝ))⁻¹ • ∑ n ∈ Finset.Icc ((k - 1) * T + 1) (k * T), w n

/-- **`k★` is an episode with the smallest summed loss.**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, §5.1, p. 18: "The output is the average
`w̄k★` of the midpoints of the episode with the smallest summed gradient, `k★ ∈ arg mink ‖Gk‖`".

`IsBestEpisode g T K k★`: `1 ≤ k★ ≤ K` and `‖G_{k★}‖ ≤ ‖G_k‖` for every `1 ≤ k ≤ K`.

**Formalization Note.** Ties are not broken: the theorems hold for every minimizing `k★`. -/
def IsBestEpisode {d : ℕ} (g : ℕ → EuclideanSpace ℝ (Fin d)) (T K kstar : ℕ) : Prop :=
  1 ≤ kstar ∧ kstar ≤ K ∧ ∀ k, 1 ≤ k → k ≤ K → ‖epSum g T kstar‖ ≤ ‖epSum g T k‖

end RollingProbeQN.Convex.Supplement


