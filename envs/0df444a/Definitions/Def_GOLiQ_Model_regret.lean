-- Prove2me | Definitions.Def_GOLiQ_Model_regret
-- name    : GOLiQ_Model_regret
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:52:48.797537+00:00
-- url     : https://prove2.me/theorems/d11bb361-dafb-4450-ba87-e2639b0d74b3
-- title:
--   Cycle cost (8), regret (9) and its split (10)–(11) into $R_1$ and $R_2$
-- statement:
--   The net cost of cycle $k$ along a sample path is
--   $$\sum_{n=1}^{Q_k\wedge D_k}\big(h_0(W^k_n+S^k_n)-p^k_n\big)+\sum_{n=Q_k+1}^{D_k}\big(h_0(W^k_n+S^k_n)-p_k\big)+c(\mu_k)T_k ,$$
--   the second sum being $0$ when $D_k<Q_k+1$; its expectation is $\rho_k$ (8). With $f^*=f(\mu^*,p^*)$,
--   $$R(L)=\sum_{k=1}^L R_k,\qquad R_k=\rho_k-f^*\,\mathbb E[T_k].\tag{9}$$
--   The regret splits as $R_k=R_{1,k}+R_{2,k}$ with $R_{1,k}=\rho_k-\mathbb E[f(\mu_k,p_k)T_k]$ and $R_{2,k}=\mathbb E[T_k(f(\mu_k,p_k)-f^*)]$, and $R_i(L)=\sum_{k\le L}R_{i,k}$ (10)–(11). The module also defines
--   $$I_3=\mathbb E\Big[(D_k-\lambda_kT_k)\Big(h_0w(\mu_k,p_k)+\frac{h_0}{\mu_k}-p_k\Big)\Big]+\mathbb E\Big[\sum_{n=1}^{Q_k\wedge D_k}(p_k-p^k_n)\Big],$$
--   the remainder term of the decomposition of $R_{1,k}$ on p.22, with $\lambda_k=\lambda(p_k)$.
--
--   These are the quantities bounded by Theorems 1–3.
-- source:
--   Chen, Liu, Hong, An Online Learning Approach to Dynamic Pricing and Capacity Sizing in Service Systems, arXiv:2009.02911v3, (8)–(11), p.19; I₃, p.22

import Mathlib
import Definitions.Def_GOLiQ_Model
import Definitions.Def_GOLiQ_Primitives
import Definitions.Def_GOLiQ_Model_objective
import Definitions.Def_GOLiQ_CycleSystem

open MeasureTheory

namespace GOLiQ

/-- The net cost incurred in cycle `k` along one sample path, the integrand of (8)
(Chen, Liu, Hong, arXiv:2009.02911v3, p.19):

`Σ_{n=1}^{Qₖ∧Dₖ} (h₀(Wₙᵏ + Sₙᵏ) − pₙᵏ) + Σ_{n=Qₖ+1}^{Dₖ} (h₀(Wₙᵏ + Sₙᵏ) − pₖ) + c(µₖ)Tₖ`,

the second sum being `0` when `Dₖ < Qₖ + 1`. -/
noncomputable def CycleSystem.cost (S : CycleSystem) (k : ℕ) : ℝ :=
  let q := (min (S.leftover k) (S.D k : ℕ∞)).toNat
  (∑ n ∈ Finset.Icc 1 q,
      (S.model.h0 * (S.cycleWait k n + S.cycleService k n) - S.cyclePrice k n)) +
    (∑ n ∈ Finset.Icc (q + 1) (S.D k),
      (S.model.h0 * (S.cycleWait k n + S.cycleService k n) - S.price k)) +
    S.model.c (S.mu k) * S.length k

namespace Model

variable {Ω : Type*} [MeasurableSpace Ω] (M : Model) (Pr : Primitives Ω)

/-- **The regret (9)** of the policy `x` over the first `L` cycles (p.19):
`R(L) = Σ_{k=1}^L Rₖ`, `Rₖ = ρₖ − f(µ*, p*) E[Tₖ]`, with `ρₖ` the expected net cost (8) of cycle `k`. -/
noncomputable def regret (D : ℕ → ℕ) (x : ℕ → Ω → Point) (xstar : Point) (L : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 L,
    ((∫ ω, (M.system Pr D x ω).cost k ∂Pr.P) -
      M.objective Pr xstar * ∫ ω, (M.system Pr D x ω).length k ∂Pr.P)

/-- `R₁,ₖ = ρₖ − E[f(µₖ, pₖ)Tₖ]`, the regret of nonstationarity in cycle `k`, (10), p.19. -/
noncomputable def nonstatRegretCycle (D : ℕ → ℕ) (x : ℕ → Ω → Point) (k : ℕ) : ℝ :=
  (∫ ω, (M.system Pr D x ω).cost k ∂Pr.P) -
    ∫ ω, M.objective Pr (x k ω) * (M.system Pr D x ω).length k ∂Pr.P

/-- `R₁(L) = Σ_{k=1}^L R₁,ₖ`, (11), p.19. -/
noncomputable def nonstatRegret (D : ℕ → ℕ) (x : ℕ → Ω → Point) (L : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 L, M.nonstatRegretCycle Pr D x k

/-- `R₂(L) = Σ_{k=1}^L E[Tₖ(f(µₖ, pₖ) − f(µ*, p*))]`, (10)–(11), p.19. -/
noncomputable def suboptRegret (D : ℕ → ℕ) (x : ℕ → Ω → Point) (xstar : Point) (L : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 L,
    ∫ ω, (M.system Pr D x ω).length k * (M.objective Pr (x k ω) - M.objective Pr xstar) ∂Pr.P

/-- `I₃`, the remaining error term of the decomposition of `R₁,ₖ` (p.22):

`I₃ = E[(Dₖ − λₖTₖ)(h₀ w(µₖ, pₖ) + h₀/µₖ − pₖ)] + E[Σ_{n=1}^{Qₖ∧Dₖ} (pₖ − pₙᵏ)]`,

with `λₖ = λ(pₖ)` and `w(µ, p) = E[W∞(µ, p)]`. -/
noncomputable def nonstatRemainder (D : ℕ → ℕ) (x : ℕ → Ω → Point) (k : ℕ) : ℝ :=
  (∫ ω, ((D k : ℝ) - M.lam (x k ω 1) * (M.system Pr D x ω).length k) *
      (M.h0 * M.waitMean Pr (x k ω 0) (x k ω 1) + M.h0 / x k ω 0 - x k ω 1) ∂Pr.P) +
    ∫ ω, ∑ n ∈ Finset.Icc 1 (min ((M.system Pr D x ω).leftover k) (D k : ℕ∞)).toNat,
      (x k ω 1 - (M.system Pr D x ω).cyclePrice k n) ∂Pr.P

end Model

end GOLiQ


