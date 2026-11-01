-- Prove2me | Definitions.Def_MarkdownReadjust_markdownRevenue
-- name    : MarkdownReadjust_markdownRevenue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:14:35.190635+00:00
-- url     : https://prove2.me/theorems/686b11d1-3060-42f1-b3b6-c742125dfe96
-- title:
--   Expected revenue $J^{\pi^{\mathrm{Re}}_\searrow}(x_0,T)$ of the markdown readjustment policy
-- statement:
--   With update times (14) and shift terms (15), the markdown readjustment policy with $N$ updates and parameter $\alpha$ earns, from inventory $x_0$ over $[0,T]$, the expected revenue
--
--   $$
--   J^{\pi^{\mathrm{Re}}_\searrow}(x_0,T)=\mathsf E\Big[\sum_{n=0}^{N}\bar F^{-1}(\rho_n)\,S_n\Big],\qquad S_n=\min(D_n,X_n),
--   $$
--
--   where $D_n$ is the number of customers arriving in $[t_n,t_{n+1})$ who would buy at $\bar F^{-1}(\rho_n)$, $X_n$ the stock at $t_n$, and, given the past, $D_n$ is Poisson with mean $\lambda(t_{n+1}-t_n)\rho_n$. This is $\mathsf E[\int_0^T\pi_t\,dY_t]$ for the policy. The module also defines $\rho_n$, $S_n$ and the law of $(D_0,\dots,D_N)$.
--
--   **Formalization Note** The continuous-time process is replaced by the exact law of the interval demand counts (Poisson thinning). After stock-out the price is the turn-off price and nothing is sold, which $\min(D_n,X_n)$ records. The integrand is bounded by $Vx_0$.
-- source:
--   Chen, Jasin, Simple monotonic readjustment policies with applications to markdown pricing and pricing in the presence of strategic customers, SSRN 3740871 (2023-10-09), §3 p.7 (J^π), §5.1 pp.9–10, §7.1 pp.18–19

import Mathlib
import Definitions.Def_MarkdownReadjust_Model
import Definitions.Def_MarkdownReadjust_tgrid
import Definitions.Def_MarkdownReadjust_seqPoissonLaw
import Definitions.Def_MarkdownReadjust_procState

open MeasureTheory

namespace MarkdownReadjust

/-- The adjusted purchase rate `ρₙ` of the markdown readjustment policy `π^Re_↘` (Chen–Jasin,
SSRN 3740871, §5.1, p.9) along the demand path `ω`, with sales capped by the remaining stock. -/
noncomputable def rhoAct (M : Model) (α : ℝ) (N x : ℕ) (τ : ℝ) (ω : ℕ → ℕ) (n : ℕ) : ℝ :=
  procRhoAt M α N x τ (fun d s => min d s) ω n

/-- The realized sales `Sₙ = min(Dₙ, Xₙ)` of `π^Re_↘` on `[tₙ, t_{n+1})` (p.10: sales "until
stock-out"), where `Dₙ = ω n` and `Xₙ` is the stock at `tₙ`. -/
noncomputable def salesAct (M : Model) (α : ℝ) (N x : ℕ) (τ : ℝ) (ω : ℕ → ℕ) (n : ℕ) : ℕ :=
  min (ω n) (procState M α N x τ (fun d s => min d s) ω n).2.2

/-- The law of the demand counts `(D₀, …, D_N)` under `π^Re_↘`: given the past,
`Dₙ ~ Poisson(λ(t_{n+1} − tₙ)ρₙ)`. -/
noncomputable def actLaw (M : Model) (α : ℝ) (N x : ℕ) (τ : ℝ) : Measure (Fin (N + 1) → ℕ) :=
  seqPoissonLaw (fun n p => Real.toNNReal
    (M.lam * (tgrid x τ N (n + 1) - tgrid x τ N n) * rhoAct M α N x τ (pathExt p) n)) (N + 1)

/-- The expected revenue `J^{π^Re_↘}(x₀, T)` of the markdown readjustment policy with update
times (14) and shift terms (15) (Chen–Jasin, SSRN 3740871, §3 p.7, §5.1 pp.9–10, §7.1
pp.18–19), for inventory `x` and horizon `τ`:
`E[Σ_{n=0}^{N} F̄⁻¹(ρₙ) Sₙ]`.

**Formalization Note.** On `[tₙ, t_{n+1})` the price is `F̄⁻¹(ρₙ)` until stock-out and then
the turn-off price `V` (no sales). By Poisson thinning the number `Dₙ` of arrivals in the
interval who would buy at `F̄⁻¹(ρₙ)` is, given the past, Poisson with mean
`λ(t_{n+1} − tₙ)ρₙ`, and the sales are `Sₙ = min(Dₙ, Xₙ)`; so `∫ Σₙ F̄⁻¹(ρₙ)Sₙ` under the
sequential Poisson law `actLaw` is exactly the expectation of `∫₀ᵀ πₜ dYₜ` (p.7). The
continuous-time process is not built. The integrand is bounded by `V·x`, so the Bochner integral
is the true expectation. -/
noncomputable def markdownRevenue (M : Model) (α : ℝ) (N x : ℕ) (τ : ℝ) : ℝ :=
  ∫ ω, ∑ n ∈ Finset.range (N + 1),
      M.Finv (rhoAct M α N x τ (pathExt ω) n) * (salesAct M α N x τ (pathExt ω) n : ℝ)
    ∂(actLaw M α N x τ)

end MarkdownReadjust


