-- Prove2me | Definitions.Def_MarkdownReadjust_procState
-- name    : MarkdownReadjust_procState
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:13:43.772394+00:00
-- url     : https://prove2.me/theorems/3f278987-7ceb-447e-b405-1642fd79f39a
-- title:
--   Recursion of the markdown readjustment policy
-- statement:
--   The **markdown readjustment policy** $\pi^{\mathrm{Re}}_{\searrow}$ posts the price $\bar F^{-1}(\rho_n)$ on $[t_n,t_{n+1})$ until stock-out, where
--
--   $$
--   \rho_0=(\rho^d-\eta_0)^+,\qquad \rho_n=\max\Big\{\Big(\rho^d-\eta_n-\sum_{m=0}^{n-1}\frac{\Delta_m}{\lambda(T-t_{m+1})}\Big)^+,\ \rho_{n-1}\Big\},\quad n=1,\dots,N,
--   $$
--
--   $(\cdot)^+$ is the projection onto $[0,1]$, and $\Delta_m=S_m-\lambda(t_{m+1}-t_m)\rho_m$ with $S_m$ the realized sales of interval $m$. The recursion runs along a path of demand counts and carries the previous rate, the accumulated correction $\sum_{m<n}\Delta_m/(\lambda(T-t_{m+1}))$ and the stock; a sales rule turns demand and stock into sales.
--
--   **Formalization Note** The rule $S_m=\min(D_m,X_m)$ gives the actual policy (sales until stock-out); $S_m=D_m$ gives the uncapped process of Appendix B.1. The maximum makes $\rho_0\le\rho_1\le\dots\le\rho_N$, so prices are non-increasing (a markdown policy).
-- source:
--   Chen, Jasin, Simple monotonic readjustment policies with applications to markdown pricing and pricing in the presence of strategic customers, SSRN 3740871 (2023-10-09), §5.1, pp.9–10

import Mathlib
import Definitions.Def_MarkdownReadjust_Model
import Definitions.Def_MarkdownReadjust_rhoD
import Definitions.Def_MarkdownReadjust_tgrid
import Definitions.Def_MarkdownReadjust_eta
import Definitions.Def_MarkdownReadjust_proj

namespace MarkdownReadjust

/-- The adjusted purchase rate rule of the markdown readjustment policy (Chen–Jasin, SSRN
3740871, §5.1, p.9): `ρ₀ = (ρᵈ − η₀)⁺` and, for `n ≥ 1`,
`ρₙ = max{(ρᵈ − ηₙ − Σ_{m=0}^{n−1} Δₘ/(λ(T − t_{m+1})))⁺, ρ_{n−1}}`, where `prev = ρ_{n−1}` and
`acc = Σ_{m=0}^{n−1} Δₘ/(λ(T − t_{m+1}))`; `(·)⁺` is the projection onto `[0,1]`. -/
noncomputable def procRho (M : Model) (α : ℝ) (N x : ℕ) (τ : ℝ) (n : ℕ) (prev acc : ℝ) : ℝ :=
  if n = 0 then proj (rhoD M x τ - eta M.lam α x τ N 0)
  else max (proj (rhoD M x τ - eta M.lam α x τ N n - acc)) prev

/-- The state of the markdown readjustment policy at the start of interval `[tₙ, t_{n+1})`
along a path of demand counts `ω` (Chen–Jasin, SSRN 3740871, §5.1, pp.9–10): the triple
`(ρ_{n−1}, Σ_{m=0}^{n−1} Δₘ/(λ(T − t_{m+1})), Xₙ)` (previous rate, accumulated correction,
remaining stock), starting from `(0, 0, x₀)`.

`ω m` is the number of customers arriving in `[tₘ, t_{m+1})` who would buy at the posted price
`F̄⁻¹(ρₘ)`, and `sale (ω m) Xₘ` is the realized sales `Sₘ` of the interval;
`Δₘ = Sₘ − λ(t_{m+1} − tₘ)ρₘ`.

**Formalization Note.** `sale = min` gives the actual policy (sales until stock-out, p.10);
`sale = fun d _ => d` gives the uncapped process of Appendix B.1 (p.ec12), whose stock component
is unused. The dummy `ρ_{−1} = 0` is never read (`procRho` at `n = 0` ignores it). The state
after the last interval divides by `T − t_{N+1} = 0` (junk `0`), but it is never used. -/
noncomputable def procState (M : Model) (α : ℝ) (N x : ℕ) (τ : ℝ) (sale : ℕ → ℕ → ℕ)
    (ω : ℕ → ℕ) : ℕ → ℝ × ℝ × ℕ
  | 0 => (0, 0, x)
  | n + 1 =>
    let s := procState M α N x τ sale ω n
    let r := procRho M α N x τ n s.1 s.2.1
    let S := sale (ω n) s.2.2
    (r, s.2.1 + ((S : ℝ) - M.lam * (tgrid x τ N (n + 1) - tgrid x τ N n) * r)
          / (M.lam * (τ - tgrid x τ N (n + 1))),
      s.2.2 - S)

/-- The adjusted purchase rate `ρₙ` used on `[tₙ, t_{n+1})` along the path `ω`, for the sales
rule `sale`. It depends on `ω m` for `m < n` only. -/
noncomputable def procRhoAt (M : Model) (α : ℝ) (N x : ℕ) (τ : ℝ) (sale : ℕ → ℕ → ℕ)
    (ω : ℕ → ℕ) (n : ℕ) : ℝ :=
  procRho M α N x τ n (procState M α N x τ sale ω n).1 (procState M α N x τ sale ω n).2.1

end MarkdownReadjust


