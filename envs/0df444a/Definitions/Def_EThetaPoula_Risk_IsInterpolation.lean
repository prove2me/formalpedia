-- Prove2me | Definitions.Def_EThetaPoula_Risk_IsInterpolation
-- name    : EThetaPoula_Risk_IsInterpolation
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:23:23.813124+00:00
-- url     : https://prove2.me/theorems/7d010f2b-d2be-4c19-a628-bd0346aa9f19
-- title:
--   The continuous-time interpolation $\bar\theta^\lambda$ of e-TH$\varepsilon$O POULA, (39)
-- statement:
--   $\bar\theta^\lambda$ is the interpolation of (39): $\bar\theta^\lambda_0=\theta_0$ and, for $n\in\mathbb N_0$, $t\in(n,n+1]$,
--   $$
--   \bar\theta^\lambda_t=\bar\theta^\lambda_n-\lambda(t-n)H_\lambda(\bar\theta^\lambda_n,X_{n+1})+\sqrt{2\lambda\beta^{-1}}\,(B^\lambda_t-B^\lambda_n).
--   $$
--
--   **Formalization Note** This is (39) integrated over $(n,t]$: on $(n,n+1)$ one has $\lfloor t\rfloor=n$ and $\lceil t\rceil=\lfloor t\rfloor+1=n+1$ in the paper's convention, and the endpoint has measure zero. The recursion determines the process.
-- source:
--   Lim, Neufeld, Sabanis, Zhang, arXiv:2210.13193v3, §6.1, (39), p.23

import Mathlib
import Definitions.Def_EThetaPoula_Risk_Model
import Definitions.Def_EThetaPoula_Risk_timeChanged

open scoped NNReal

namespace EThetaPoula.Risk

/-- `θb` is the continuous-time interpolation `θ̄^λ` of (39), Lim, Neufeld, Sabanis, Zhang,
arXiv:2210.13193v3, §6.1, p.23: `θ̄^λ₀ = θ₀` and, for `t ∈ (n, n+1]`,
`θ̄^λ_t = θ̄^λ_n − λ(t − n) H_λ(θ̄^λ_n, X_{n+1}) + √(2λβ⁻¹)(B^λ_t − B^λ_n)`.

**Formalization Note.** This is the integrated form of (39): on `(n, n+1)` one has `⌊t⌋ = n` and
`⌈t⌉ = ⌊t⌋ + 1 = n + 1`, with the paper's `⌈·⌉` of §1, and the endpoint has measure zero. The
recursion determines `θb` uniquely from `S`, `B`. -/
def Model.IsInterpolation {d m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (S : Model d m Ω)
    (B : ℝ≥0 → Ω → Eucl d) (lam β ε : ℝ) (θb : ℝ≥0 → Ω → Eucl d) : Prop :=
  (∀ ω, θb 0 ω = S.θ₀ ω) ∧
  ∀ (n : ℕ) (t : ℝ≥0), (n : ℝ≥0) < t → t ≤ n + 1 → ∀ ω, θb t ω =
    θb n ω - (lam * ((t : ℝ) - n)) • S.Hlam lam ε (θb n ω) (S.X (n + 1) ω)
      + √(2 * lam * β⁻¹) • (timeChangedBM B lam t ω - timeChangedBM B lam n ω)

end EThetaPoula.Risk


