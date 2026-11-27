-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket
-- name    : BauerleRiederMDP_LQ_Supplement_JumpMarket
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:11:09.86313+00:00
-- url     : https://prove2.me/theorems/4dacf5e0-3005-4501-b3a5-9db74d2d4715
-- title:
--   The pure jump market of §9.3
-- statement:
--   **The pure jump market of §9.3** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), §9.3, pp.280–281, PDF 290–291, with the market of §3.2): a bond $S^0_t = e^{\rho t}$ with interest rate $\rho  \ge  0$ and $d$ stocks $dS^k_t = S^k_{t-}(\mu _k dt + dC^k_t)$, where $C_t = \sum _{n=1}^{N_t} Y_n$ is a multivariate compound Poisson process: the jump times form a Poisson process with rate $\lambda  > 0$ and the relative jump heights $Y_n$ are i.i.d. with law $Q^Y$, whose support is $(-1, \infty )^d$, and $\mathbb E \|Y_n\| < \infty $; the horizon is $T > 0$.
--
--   **Formalization Note.** $\mathbb R ^d$ is $Fin d \to  \mathbb R $. The support condition is stated as: $Q^Y$ is carried by $(-1, \infty )^d$ and charges every open set that meets $(-1, \infty )^d$. The utility function is not part of the market (the theorems vary it).
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §9.3, pp.280–281, PDF 290–291, with the market of §3.2

import Mathlib

open MeasureTheory ProbabilityTheory

namespace BauerleRiederMDP.LQ.Supplement

/-- **The pure jump market of §9.3** (Bäuerle & Rieder, *Markov Decision Processes with
Applications to Finance* (2011), §9.3, pp.280–281, PDF 290–291, with the market of §3.2): a bond
`S^0_t = e^{ρt}` with interest rate `ρ ≥ 0` and `d` stocks `dS^k_t = S^k_{t−}(μ_k dt + dC^k_t)`,
where `C_t = ∑_{n=1}^{N_t} Y_n` is a multivariate compound Poisson process: the jump times form a
Poisson process with rate `λ > 0` and the relative jump heights `Y_n` are i.i.d. with law `Q^Y`,
whose support is `(−1, ∞)^d`, and `𝔼‖Y_n‖ < ∞`; the horizon is `T > 0`.

**Formalization Note.** `ℝ^d` is `Fin d → ℝ`. The support condition is stated as: `Q^Y` is carried
by `(−1, ∞)^d` and charges every open set that meets `(−1, ∞)^d`. The utility function is not part
of the market (the theorems vary it). -/
structure JumpMarket (d : ℕ) where
  ρ : ℝ
  ρ_nonneg : 0 ≤ ρ
  μ : Fin d → ℝ
  lam : ℝ
  lam_pos : 0 < lam
  QY : Measure (Fin d → ℝ)
  QY_prob : IsProbabilityMeasure QY
  QY_carried : ∀ᵐ y ∂QY, ∀ k, -1 < y k
  QY_support : ∀ G : Set (Fin d → ℝ), IsOpen G → (G ∩ {y | ∀ k, -1 < y k}).Nonempty → 0 < QY G
  QY_moment : ∫⁻ y, ‖y‖ₑ ∂QY < ⊤
  T : ℝ
  T_pos : 0 < T

attribute [instance] JumpMarket.QY_prob

end BauerleRiederMDP.LQ.Supplement


