-- Prove2me | Definitions.Def_GradSuffice_seqRad
-- name    : GradSuffice_seqRad
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:20:31.993022+00:00
-- url     : https://prove2.me/theorems/7829d842-36f3-4d3d-a1ab-93fb62b83062
-- title:
--   Sequential Rademacher complexity $\mathcal R^{(s)}_m(B;\bar\xi)$
-- statement:
--   Let $\bar\xi=(\xi_1,\dots,\xi_m)$ be an adaptive sequence and let $\sigma_1,\dots,\sigma_m$ be independent uniform random signs. The **sequential Rademacher complexity** of $B$ along $\bar\xi$ is
--   $$\mathcal R^{(s)}_m(B;\bar\xi)=\frac1m\,\mathbb E_\sigma\Big\|\sum_{i=1}^m\sigma_i\,\xi_i(\sigma_{<i})\Big\|_\star ,$$
--   and $\mathcal R^{(s)}_m(B)=\sup_{\bar\xi}\mathcal R^{(s)}_m(B;\bar\xi)$, the supremum over $B^\star$-valued adaptive sequences of length $m$. It satisfies $0\le\mathcal R^{(s)}_m(B)\le 1$.
--
--   **Formalization Note** The expectation is the average over the $2^m$ sign strings. The supremum is not a separate definition: statements bound $\mathcal R^{(s)}_m(B)$ from above by quantifying over every $B^\star$-valued $\bar\xi$, and from below by exhibiting one. At $m=0$ the value is $0$; every use has $m\ge 1$.
-- source:
--   Alon–Koren–Livni–Moran, When Do Gradients Suffice? A Characterization of First-Order Convex Optimization, manuscript of November 3, 2026 (STOC 2027 submission), §2, p.5

import Mathlib
import Definitions.Def_NondualOpt_Tree
import Definitions.Def_GradSuffice_signedSum

namespace GradSuffice

/-- **Sequential Rademacher complexity of `B` along an adaptive sequence.** Alon–Koren–Livni–Moran, *When Do Gradients Suffice?*, manuscript of November 3, 2026, §2, p.5:
`R⁽ˢ⁾ₘ(B; ξ̄) := (1/m) E_σ ‖∑_{i=1}^m σᵢ ξᵢ(σ<ᵢ)‖⋆`, with `σ₁, …, σₘ` independent Rademacher
signs; `R⁽ˢ⁾ₘ(B) := sup_ξ̄ R⁽ˢ⁾ₘ(B; ξ̄)` over `B⋆`-valued adaptive sequences.

**Formalization Note.** The expectation over independent uniform signs is the average over all
`2^m` sign strings `Fin m → Bool`. The supremum `R⁽ˢ⁾ₘ(B)` is not a separate definition: an upper
bound on it is stated as "for every `B⋆`-valued `ξ`" and a strict lower bound as "for some
`B⋆`-valued `ξ`" (the supremum is finite, at most 1). At `m = 0` the value is `0`; every use has
`m ≥ 1`. -/
noncomputable def seqRad {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {m : ℕ} (ξ : NondualOpt.Tree (StrongDual ℝ X) m) : ℝ :=
  (1 / (m : ℝ)) * ((2 ^ m : ℝ)⁻¹ * ∑ σ : Fin m → Bool, ‖signedSum ξ σ‖)

end GradSuffice


