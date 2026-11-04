-- Prove2me | Definitions.Def_GOLiQ_Model_goliq
-- name    : GOLiQ_Model_goliq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:52:08.335389+00:00
-- url     : https://prove2.me/theorems/f7b4b9d1-4f34-4920-b230-e7c19d7fcafc
-- title:
--   GOLiQ (Algorithm 1): the iterates $x_k$ and estimators $H_k$
-- statement:
--   Algorithm 1 has inputs $0<\xi<1$, cycle lengths $D_k$, step sizes $\eta_k$ and an initial value $x_1\in\mathcal B$. For $k=1,2,\dots$:
--
--   1. operate the system under $x_k=(\mu_k,p_k)$ until $D_k$ customers enter service, and observe $(W^k_n,X^k_n)$ for $n=1,\dots,D_k$;
--   2. form the average $\hat m_k=\frac1{\lceil D_k(1-\xi)\rceil}\sum_{\xi D_k<n\le D_k}(X^k_n+W^k_n)$ and the partial estimates
--   $$\hat g_p=-\lambda(p_k)-p_k\lambda'(p_k)+h_0\lambda'(p_k)\Big[\hat m_k+\frac1{\mu_k}\Big],\qquad \hat g_\mu=c'(\mu_k)-h_0\frac{\lambda(p_k)}{\mu_k}\Big[\hat m_k+\frac1{\mu_k}\Big];$$
--   3. with the draw $Z_k$, set $H_k=2\hat g_p$ in the $p$-coordinate if $Z_k=1$, and $H_k=2\hat g_\mu$ in the $\mu$-coordinate if $Z_k=2$;
--   4. update $x_{k+1}=\Pi_{\mathcal B}(x_k-\eta_kH_k)$.
--
--   The module defines the iterates $x_k$, by recursion on $k$ (cycle $k$ depends only on $x_1,\dots,x_k$), and the estimators $H_k$ computed from the queue run under these iterates.
--
--   **Formalization Note** The pseudocode writes $H_k\leftarrow(2h,0)$ for the $p$-partial although $x=(\mu,p)$; the proof of Theorem 3(i) (p.68) pairs each partial with its own coordinate, which is the reading used here. The loop header "for $n=1,\dots,D_k$" is the loop over cycles, and $\lambda(p)/\mu_k$ is $\lambda(p_k)/\mu_k$.
-- source:
--   Chen, Liu, Hong, An Online Learning Approach to Dynamic Pricing and Capacity Sizing in Service Systems, arXiv:2009.02911v3, Algorithm 1, p.32; (18), p.30

import Mathlib
import Definitions.Def_GOLiQ_Model
import Definitions.Def_GOLiQ_Primitives
import Definitions.Def_GOLiQ_CycleSystem

open scoped Classical

namespace GOLiQ

/-- The empirical average of Algorithm 1 for cycle `k` (Chen, Liu, Hong, arXiv:2009.02911v3,
p.32), with warm-up parameter `ξ`:

`m̂ₖ = (1/⌈Dₖ(1 − ξ)⌉) Σ_{ξDₖ < n ≤ Dₖ} (Xₙᵏ + Wₙᵏ)`. -/
noncomputable def CycleSystem.empMean (S : CycleSystem) (ξ : ℝ) (k : ℕ) : ℝ :=
  (1 / (⌈(S.D k : ℝ) * (1 - ξ)⌉₊ : ℝ)) *
    ∑ n ∈ (Finset.Icc (1 : ℕ) (S.D k)).filter (fun n : ℕ => ξ * (S.D k : ℝ) < (n : ℝ)),
      (S.cycleBusy k n + S.cycleWait k n)

namespace Model

variable {Ω : Type*} [MeasurableSpace Ω] (M : Model) (Pr : Primitives Ω)

/-- The gradient estimator `Hₖ` of Algorithm 1 (p.32) for cycle `k`, from the cycle data `S` and
the coordinate draw `z ∈ {1, 2}`. With `µ = µₖ`, `p = pₖ` and `m̂ = m̂ₖ`:

* `ĝ_p = −λ(p) − pλ′(p) + h₀λ′(p)(m̂ + 1/µ)` (estimate of `∂f/∂p`, (18)),
* `ĝ_µ = c′(µ) − h₀(λ(p)/µ)(m̂ + 1/µ)` (estimate of `∂f/∂µ`, (18)),
* `Hₖ = 2ĝ_p` in the `p`-coordinate if `z = 1`, and `Hₖ = 2ĝ_µ` in the `µ`-coordinate otherwise.

**Formalization Note.** The pseudocode writes `Hₖ ← (2h, 0)` for the `p`-partial and `(0, 2h)` for
the `µ`-partial, while `x = (µ, p)`; the proof of Theorem 3(i) (p.68) pairs each partial with its
own coordinate, which is the reading used here. `λ(p)/µₖ` of the else-branch is `λ(pₖ)/µₖ`. -/
noncomputable def estimate (ξ : ℝ) (S : CycleSystem) (k : ℕ) (z : ℝ) : Point :=
  let mu := S.mu k
  let p := S.price k
  let m := S.empMean ξ k
  let gp := -M.lam p - p * M.dlam p + M.h0 * M.dlam p * (m + 1 / mu)
  let gmu := M.dc mu - M.h0 * (M.lam p / mu) * (m + 1 / mu)
  if z = 1 then !₂[0, 2 * gp] else !₂[2 * gmu, 0]

/-- The policies `x₁, …, xₖ` of Algorithm 1 after `k` iterations, on the sample path `ω`, extended
as the constant `xₖ` after index `k`. Cycle `k` is run under `x₁, …, xₖ`; its data give `Hₖ`, and
`xₖ₊₁ = Π_B(xₖ − ηₖHₖ)`. -/
noncomputable def goliqPrefix (ξ : ℝ) (D : ℕ → ℕ) (step : ℕ → ℝ) (x₁ : Point) (ω : Ω) :
    ℕ → ℕ → Point
  | 0 => fun _ => x₁
  | k + 1 =>
      if k = 0 then fun _ => x₁ else
      let pol := goliqPrefix ξ D step x₁ ω k
      let S : CycleSystem :=
        ⟨M, D, fun i => pol i 0, fun i => pol i 1, fun j => Pr.U j ω, fun j => Pr.V j ω⟩
      let xnew := M.proj (pol k - step k • M.estimate ξ S k (Pr.Z k ω))
      fun i => if i ≤ k then pol i else xnew

/-- **GOLiQ (Algorithm 1)**: the iterate `xₖ = (µₖ, pₖ)` of iteration `k ≥ 1`
(Chen, Liu, Hong, arXiv:2009.02911v3, p.32), with warm-up parameter `ξ`, cycle lengths `Dₖ`, step
sizes `ηₖ` (`step k`) and initial value `x₁`:

for `k = 1, 2, …`: operate the system under `xₖ` until `Dₖ` customers enter service; observe
`(Wₙᵏ, Xₙᵏ)`, `n = 1, …, Dₖ`; draw `Zₖ ∈ {1, 2}`; form `Hₖ` (`Model.estimate`); update
`xₖ₊₁ = Π_B(xₖ − ηₖHₖ)`.

The queue is the cycle system of §3.3 run under these iterates (`M.system Pr D (M.goliq …)`). -/
noncomputable def goliq (ξ : ℝ) (D : ℕ → ℕ) (step : ℕ → ℝ) (x₁ : Point) (k : ℕ) (ω : Ω) :
    Point :=
  M.goliqPrefix Pr ξ D step x₁ ω k k

/-- The estimator `Hₖ` of GOLiQ in iteration `k`, computed from the data of cycle `k` of the queue
run under the GOLiQ iterates and the draw `Zₖ`. -/
noncomputable def goliqEstimator (ξ : ℝ) (D : ℕ → ℕ) (step : ℕ → ℝ) (x₁ : Point) (k : ℕ)
    (ω : Ω) : Point :=
  M.estimate ξ (M.system Pr D (M.goliq Pr ξ D step x₁) ω) k (Pr.Z k ω)

end Model

end GOLiQ


