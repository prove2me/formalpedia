-- Prove2me | Definitions.Def_GradSuffice_Supplement_seqRadW
-- name    : GradSuffice_Supplement_seqRadW
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T20:25:48.136938+00:00
-- url     : https://prove2.me/theorems/e2dc185d-85c5-48f9-8c3c-8e8790e819d8
-- title:
--   Non-dual sequential Rademacher complexity $\mathcal R^{(s)}_m(W;\bar\xi)$
-- statement:
--   Let $W\subseteq B$ and let $\bar\xi=(\xi_1,\dots,\xi_m)$ be an adaptive sequence, $\xi_i:\{-1,1\}^{i-1}\to X^\star$, and let $\sigma_1,\dots,\sigma_m$ be independent uniform random signs. The **non-dual sequential Rademacher complexity** of $W$ along $\bar\xi$ is
--   $$\mathcal R^{(s)}_m(W;\bar\xi)=\frac1m\,\mathbb E_\sigma\Big[\rho_W\Big(\sum_{i=1}^m\sigma_i\,\xi_i(\sigma_{<i})\Big)\Big],$$
--   and $\mathcal R^{(s)}_m(W)=\sup_{\bar\xi}\mathcal R^{(s)}_m(W;\bar\xi)$, the supremum over $B^\star$-valued adaptive sequences of length $m$. For $W=B$ it is the sequential Rademacher complexity $\mathcal R^{(s)}_m(B;\bar\xi)$ of §2.
--
--   It is the complexity measure of Theorems 5 and 6.
--
--   **Formalization Note** The expectation is the average over the $2^m$ sign strings, and the signed sum is the published `GradSuffice.signedSum`. The supremum is not a separate definition: statements bound $\mathcal R^{(s)}_m(W)$ from above by quantifying over every $B^\star$-valued $\bar\xi$. At $m=0$ the value is $0$.
-- source:
--   Alon–Koren–Livni–Moran, When Do Gradients Suffice? A Characterization of First-Order Convex Optimization, manuscript of November 3, 2026 (STOC 2027 submission), §6.1, p.14; Eq. (9), p.16

import Mathlib
import Definitions.Def_NondualOpt_Tree
import Definitions.Def_GradSuffice_signedSum
import Definitions.Def_GradSuffice_Supplement_rhoW

namespace GradSuffice.Supplement

/-- **Non-dual sequential Rademacher complexity along an adaptive sequence.** Alon–Koren–Livni–Moran, *When Do Gradients Suffice?*, manuscript of November 3, 2026, §6.1, p.14 and
Eq. (9), p.16: `R⁽ˢ⁾ₘ(W; ξ̄) = (1/m) E_σ[ρ_W(∑_{i=1}^m σᵢ ξᵢ(σ<ᵢ))]`, with `σ₁, …, σₘ` independent
Rademacher signs; `R⁽ˢ⁾ₘ(W)` is its supremum over `B⋆`-valued adaptive sequences of length `m`.

**Formalization Note.** The expectation is the average over the `2^m` sign strings
`Fin m → Bool`; `∑ σᵢ ξᵢ(σ<ᵢ)` is the base mission's `GradSuffice.signedSum`. The supremum
`R⁽ˢ⁾ₘ(W)` is not a separate definition: an upper bound on it is stated "for every `B⋆`-valued
`ξ`". For `W = B` this is the base `GradSuffice.seqRad` (the dual norm is `ρ_B`). -/
noncomputable def seqRadW {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (W : Set X) {m : ℕ}
    (ξ : NondualOpt.Tree (StrongDual ℝ X) m) : ℝ :=
  (1 / (m : ℝ)) * ((2 ^ m : ℝ)⁻¹ * ∑ σ : Fin m → Bool, rhoW W (GradSuffice.signedSum ξ σ))

end GradSuffice.Supplement


