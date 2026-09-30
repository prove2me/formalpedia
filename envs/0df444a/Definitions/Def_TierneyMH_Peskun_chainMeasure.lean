-- Prove2me | Definitions.Def_TierneyMH_Peskun_chainMeasure
-- name    : TierneyMH_Peskun_chainMeasure
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T12:17:31.931393+00:00
-- url     : https://prove2.me/theorems/7f3a2380-06fa-42b2-9bb0-96d32d892e84
-- title:
--   Law of the Markov chain started from $\pi$, and the path sums $\sum_{i=1}^n f(X_i)$
-- statement:
--   Let $(E,\mathcal E)$ be a measurable space, $\pi$ a probability measure on $E$ and $H$ a Markov transition kernel on $E$. The **law of the Markov chain** $X_0, X_1, X_2, \dots$ with initial distribution $\pi$ and transition kernel $H$ is the unique probability measure $\mathbb P_{\pi,H}$ on the path space $E^{\mathbb N}$ under which $X_0 \sim \pi$ and, for every $n \ge 0$, given $X_0,\dots,X_n$ the next state $X_{n+1}$ has law $H(X_n, \cdot)$. Here $X_i(\omega) = \omega_i$ is the $i$-th coordinate of a path $\omega$.
--
--   For $f : E \to \mathbb R$ and $n \ge 0$, the **path sum** is
--
--   $$
--   S_n(\omega) \;=\; \sum_{i=1}^{n} f(X_i(\omega)), \qquad S_0 = 0 .
--   $$
--
--   The initial state $X_0$ is not included, matching the variance $\operatorname{Var}_H\bigl(\sum_{i=1}^n f(X_i)\bigr)$ in Tierney's Theorem 4.
--
--   These are the objects in which the asymptotic variance $v(f,H) = \lim_{n\to\infty} \frac1n \operatorname{Var}_H(S_n)$ is defined.
--
--   **Formalization Note** The path measure is Mathlib's Ionescu–Tulcea trajectory measure `Kernel.trajMeasure` with the constant family of state spaces $E$ and, at time $n$, the kernel $H$ applied to the current coordinate $\omega_n$.
-- source:
--   L. Tierney, A Note on Metropolis–Hastings Kernels for General State Spaces, Ann. Appl. Probab. 8(1) (1998) 1–9, DOI 10.1214/aoap/1027961031, p. 5, Theorem 4 (the chain X_0, X_1, … and the sum Σ_{i=1}^n f(X_i))

import Mathlib

open MeasureTheory ProbabilityTheory

namespace TierneyMH.Peskun

/-- The law, on the path space `ℕ → E`, of the time-homogeneous Markov chain `X₀, X₁, …` with
**initial distribution** `π` (the coordinate `ω 0` has law `π`) and transition kernel `H`
(given the past `X₀, …, Xₙ`, the next state `Xₙ₊₁` has law `H(Xₙ, ·)`). It is Mathlib's
Ionescu–Tulcea trajectory measure `Kernel.trajMeasure` with the time-`n` kernel
`H` applied to the current coordinate. The coordinate `ω i` is `X_i`. -/
noncomputable def chainMeasure {E : Type*} [MeasurableSpace E] (π : Measure E)
    (H : Kernel E E) [IsMarkovKernel H] : Measure (ℕ → E) :=
  Kernel.trajMeasure (X := fun _ => E) π
    (fun n => H.comap (fun x : (Π _ : Finset.Iic n, E) => x ⟨n, Finset.mem_Iic.2 le_rfl⟩)
      (measurable_pi_apply _))

/-- The path sum `Sₙ(ω) = ∑_{i=1}^{n} f(ω i) = f(X₁) + ⋯ + f(Xₙ)`. The initial state `X₀` is
**not** included, matching Theorem 4 of Tierney (1998, p. 5). `Sₙ = 0` for `n = 0`. -/
noncomputable def pathSum {E : Type*} (f : E → ℝ) (n : ℕ) (ω : ℕ → E) : ℝ :=
  ∑ i ∈ Finset.Icc 1 n, f (ω i)

end TierneyMH.Peskun


