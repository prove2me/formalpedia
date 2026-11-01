-- Prove2me | Definitions.Def_MarkdownReadjust_hatLaw
-- name    : MarkdownReadjust_hatLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:14:40.185463+00:00
-- url     : https://prove2.me/theorems/10f06494-43a7-4848-9942-94fcfb1109ed
-- title:
--   Uncapped process $\hat\rho_n$, $\hat S_n$, $\hat\Delta_m$ of Appendix B.1
-- statement:
--   The uncapped process ignores the inventory: $\hat\rho_0=(\rho^d-\eta_0)^+$ and
--
--   $$
--   \hat\rho_n=\max\Big\{\Big(\rho^d-\eta_n-\sum_{m=0}^{n-1}\frac{\hat\Delta_m}{\lambda(T-t_{m+1})}\Big)^+,\ \hat\rho_{n-1}\Big\},\qquad \hat\Delta_m=\hat S_m-\lambda(t_{m+1}-t_m)\hat\rho_m,
--   $$
--
--   where $\hat S_n$ is Poisson with mean $\lambda(t_{n+1}-t_n)\hat\rho_n$ given the past. It coincides with the policy until stock-out and is the object of the analysis in Appendix B.
--
--   **Formalization Note** A path is $(\hat S_0,\dots,\hat S_N)$ under the sequential Poisson law; $\hat\rho_n$ depends on $\hat S_0,\dots,\hat S_{n-1}$ only.
-- source:
--   Chen, Jasin, Simple monotonic readjustment policies with applications to markdown pricing and pricing in the presence of strategic customers, SSRN 3740871 (2023-10-09), Appendix B.1, p.ec12

import Mathlib
import Definitions.Def_MarkdownReadjust_Model
import Definitions.Def_MarkdownReadjust_tgrid
import Definitions.Def_MarkdownReadjust_seqPoissonLaw
import Definitions.Def_MarkdownReadjust_procState

open MeasureTheory

namespace MarkdownReadjust

/-- The uncapped adjusted purchase rate `ρ̂ₙ` of Appendix B.1 (Chen–Jasin, SSRN 3740871,
p.ec12): `ρ̂₀ = (ρᵈ − η₀)⁺`, `ρ̂ₙ = max{(ρᵈ − ηₙ − Σ_{m=0}^{n−1} Δ̂ₘ/(λ(T − t_{m+1})))⁺, ρ̂_{n−1}}`,
along the path `ω` with `Ŝₘ = ω m` (no stock-out). -/
noncomputable def rhoHat (M : Model) (α : ℝ) (N x : ℕ) (τ : ℝ) (ω : ℕ → ℕ) (n : ℕ) : ℝ :=
  procRhoAt M α N x τ (fun d _ => d) ω n

/-- `Δ̂ₘ = Ŝₘ − λ(t_{m+1} − tₘ)ρ̂ₘ` (p.ec12), with `Ŝₘ = ω m`. -/
noncomputable def DeltaHat (M : Model) (α : ℝ) (N x : ℕ) (τ : ℝ) (ω : ℕ → ℕ) (m : ℕ) : ℝ :=
  (ω m : ℝ) - M.lam * (tgrid x τ N (m + 1) - tgrid x τ N m) * rhoHat M α N x τ ω m

/-- The law of the uncapped sales `(Ŝ₀, …, Ŝ_N)` of Appendix B.1 (Chen–Jasin, SSRN 3740871,
p.ec12): "Ŝn is a Poisson random variable with mean λ(tn+1 − tn)ρ̂n", sequentially given the
past.

**Formalization Note.** A path `ω : Fin (N+1) → ℕ` is `(Ŝ₀, …, Ŝ_N)`; `ρ̂ₙ` is computed from
`pathExt ω` and depends on `Ŝ₀, …, Ŝ_{n−1}` only. -/
noncomputable def hatLaw (M : Model) (α : ℝ) (N x : ℕ) (τ : ℝ) : Measure (Fin (N + 1) → ℕ) :=
  seqPoissonLaw (fun n p => Real.toNNReal
    (M.lam * (tgrid x τ N (n + 1) - tgrid x τ N n) * rhoHat M α N x τ (pathExt p) n)) (N + 1)

end MarkdownReadjust


