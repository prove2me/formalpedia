-- Prove2me | Definitions.Def_DRORSEquiv_thetaBar
-- name    : DRORSEquiv_thetaBar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:35:22.349062+00:00
-- url     : https://prove2.me/theorems/87aacadb-ef4f-46f6-8831-f1a45aea4193
-- title:
--   Largest transport radius $\bar\theta$
-- statement:
--   The **largest transport radius** is
--
--   $$\bar\theta=\frac1S\sum_{s\in[S]}\sup_{z\in\mathcal Z}\rho(z,\hat z_s)\in[0,\infty],$$
--
--   the largest Wasserstein distance from $\mathbb P^\dagger$ to a distribution on $\mathcal Z$. For radii $\theta\ge\bar\theta$ the Wasserstein ball contains every distribution on $\mathcal Z$, and Problem (DRO) becomes classical robust optimization.
--
--   **Formalization Note** Computed in `EReal`; it is $+\infty$ when $\mathcal Z$ is unbounded for $\rho$.
-- source:
--   Wang, Ran, Zhou, He, On the Equivalence and Performance of Distributionally Robust Optimization and Robust Satisficing Models, authors' manuscript (2025), Appendix A, proof of Theorem 1, p.33; also p.12

import Mathlib
import Definitions.Def_DRORSEquiv_Model

namespace DRORSEquiv

/-- **The largest transport radius** `θ̄ = (1/S) ∑_{s ∈ [S]} sup_{z ∈ Z} ρ(z, ẑ_s)` (Wang, Ran, Zhou, He, *On the Equivalence and Performance of Distributionally Robust Optimization and Robust Satisficing Models*, authors' manuscript (2025),
Appendix A, proof of Theorem 1, p.33: "Simply let θ̄ = 1/S ∑_{s∈[S]} sup_{z∈Z}{ρ(z, ẑs)} which means there
is no distance restriction on the distribution"; also p.12).

**Formalization Note.** Computed in `EReal`; it is `+∞` when the support is unbounded for `ρ`. -/
noncomputable def thetaBar {E Ω : Type*} {S : ℕ} (M : Model E Ω S) : EReal :=
  ((1 / (S : ℝ) : ℝ) : EReal) * ∑ s : Fin S, ⨆ z ∈ M.Z, (M.ρ z (M.zhat s) : EReal)

end DRORSEquiv


