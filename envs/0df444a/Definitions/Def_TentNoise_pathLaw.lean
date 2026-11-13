-- Prove2me | Definitions.Def_TentNoise_pathLaw
-- name    : TentNoise_pathLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:40:04.463121+00:00
-- url     : https://prove2.me/theorems/c7af21cf-61e5-45f4-bb5d-b8d47b4b1e1c
-- title:
--   Law of the path $(X_0,\dots,X_T)$ of a Markov chain
-- statement:
--   Given an initial law $\mu_0$ on $\mathbb R$ and a transition kernel $\kappa$, the **path law** at horizon $T$ is the law of $(X_0,X_1,\dots,X_T)$ where
--
--   $$
--   X_0\sim\mu_0,\qquad X_{t+1}\sim\kappa(X_t,\cdot)\quad(t=0,\dots,T-1).
--   $$
--
--   It is built recursively: at $T=0$ it is the law of $X_0$; at horizon $T+1$ one draws $X_{T+1}$ from $\kappa(X_T,\cdot)$ given the path up to time $T$ and appends it.
--
--   All three path measures of the paper (the true law $\mathbb P_T$, the noised true law $\mathbb P^\sigma_T$ and the noised fitted law $\mathbb Q^\sigma_T$) are instances, with the same construction.
--
--   **Formalization Note** Paths are functions $\mathrm{Fin}(T+1)\to\mathbb R$ with the product $\sigma$-algebra; the step uses `Measure.compProd` with the kernel read at the last coordinate and appends with `Fin.snoc`. For a probability $\mu_0$ and a Markov kernel $\kappa$ the result is a probability measure (proved in the mission's sanity file).
-- source:
--   Huan, Risteski, Wei, Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling, STOC 2027 submission (manuscript sha256 67925b3e946da20fbfc5ba5a928c6f5743bf4b2ee96e526e8e738f0494f558e6), Definitions 2.2 and 2.9, pp.3 and 5 (PDF pp.3, 5): the path measures (X_0, …, X_T)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace TentNoise

/-- The law of the path `(X₀, X₁, …, X_T)` of a time-homogeneous Markov chain on `ℝ` with initial
law `μ₀` (`X₀ ∼ μ₀`) and transition kernel `κ` (`X_{t+1} ∼ κ(X_t, ·)`); the construction behind
the path measures of Huan, Risteski, Wei, *Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling*, STOC 2027 submission (manuscript sha256 67925b3e…), Definitions 2.2 and 2.9, p.3 and p.5.

Recursively: at `T = 0` the law of the one-point path `X₀`; the law at horizon `T + 1` draws
`X_{T+1} ∼ κ(X_T, ·)` given the path up to `T` (`Measure.compProd`) and appends it (`Fin.snoc`).

**Formalization Note** Paths are `Fin (T+1) → ℝ` with the product σ-algebra; coordinate `t` is
`X_t`. For a probability `μ₀` and a Markov kernel `κ` this is a probability measure. -/
noncomputable def pathLaw (κ : Kernel ℝ ℝ) (μ₀ : Measure ℝ) : (T : ℕ) → Measure (Fin (T + 1) → ℝ)
  | 0 => μ₀.map (fun x _ => x)
  | T + 1 =>
      ((pathLaw κ μ₀ T) ⊗ₘ (κ.comap (fun p : Fin (T + 1) → ℝ => p (Fin.last T))
          (measurable_pi_apply _))).map
        (fun q => (Fin.snoc q.1 q.2 : Fin (T + 2) → ℝ))

end TentNoise


