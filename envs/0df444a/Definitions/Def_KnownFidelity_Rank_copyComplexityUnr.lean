-- Prove2me | Definitions.Def_KnownFidelity_Rank_copyComplexityUnr
-- name    : KnownFidelity_Rank_copyComplexityUnr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:49:41.753382+00:00
-- url     : https://prove2.me/theorems/dd43c8da-e5ad-4444-aa3e-dab7048b02e3
-- title:
--   Copy complexity $\mathsf S_\sigma(\varepsilon)$ for an unrestricted unknown state
-- statement:
--   $\mathsf S_\sigma(\varepsilon)$ is the copy complexity of estimating $F(\rho,\sigma)$ to accuracy $\varepsilon$ with probability $2/3$ when the unknown state $\rho$ on $\mathbb C^d$ is unrestricted:
--
--   $$\mathsf S_\sigma(\varepsilon)=\mathsf S^{(\le d)}_\sigma(\varepsilon).$$
--
--   **Formalization Note** Every state on $\mathbb C^d$ has rank at most $d$, so the rank bound $s=d$ is no restriction.
-- source:
--   Lee, Jo, Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank, arXiv:2608.01770, §1 (unnumbered), p. 1 (PDF p. 3)

import Mathlib
import Definitions.Def_KnownFidelity_Rank_copyComplexity

namespace KnownFidelity.Rank

/-- **Copy complexity `S_σ(ε)` with the unknown state unrestricted.**
Lee, Jo, *Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank*,
arXiv:2608.01770, §1 (unnumbered), printed p. 1 (PDF p. 3): "Write S_σ(ε) when ρ is
unrestricted".

**Formalization Note.** Every state on `ℂ^d` has rank at most `d`, so "unrestricted" is the rank
bound `s = d`: `copyComplexityUnr σ ε = copyComplexity σ d ε`. -/
noncomputable def copyComplexityUnr {d : ℕ} (σ : Matrix (Fin d) (Fin d) ℂ) (ε : ℝ) : ℕ∞ :=
  copyComplexity σ d ε

end KnownFidelity.Rank


