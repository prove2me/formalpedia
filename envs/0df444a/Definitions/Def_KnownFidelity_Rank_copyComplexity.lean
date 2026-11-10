-- Prove2me | Definitions.Def_KnownFidelity_Rank_copyComplexity
-- name    : KnownFidelity_Rank_copyComplexity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:48:10.438897+00:00
-- url     : https://prove2.me/theorems/a5984c73-74f1-4845-be4e-152f7c00ad4a
-- title:
--   Copy complexity $\mathsf S^{(\le s)}_\sigma(\varepsilon)$
-- statement:
--   For a known state $\sigma$ on $\mathbb C^d$, a rank bound $s$ and an accuracy $\varepsilon$, the **copy complexity** $\mathsf S^{(\le s)}_\sigma(\varepsilon)$ is the least number $n$ of copies for which some collective measurement on $(\mathbb C^d)^{\otimes n}$ estimates $F(\rho,\sigma)$ within additive error $\varepsilon$ with probability at least $2/3$, simultaneously for every state $\rho$ of rank at most $s$:
--
--   $$\mathsf S^{(\le s)}_\sigma(\varepsilon)=\min\{\,n:\ \exists\,E\ \text{a good estimator on } n \text{ copies}\,\}.$$
--
--   **Formalization Note** The minimum is an infimum in $\mathbb N\cup\{\infty\}$, equal to $\infty$ when no number of copies works; in $\mathbb N$ the empty infimum would be $0$ and every upper bound would hold trivially.
-- source:
--   Lee, Jo, Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank, arXiv:2608.01770, §1 (unnumbered), p. 1 (PDF p. 3)

import Mathlib
import Definitions.Def_KnownFidelity_Rank_IsGoodEstimator

namespace KnownFidelity.Rank

/-- **Copy complexity `S^{(≤s)}_σ(ε)`.**
Lee, Jo, *Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank*,
arXiv:2608.01770, §1 (unnumbered), printed p. 1 (PDF p. 3): "Let S^(≤s)_σ(ε) be the least number
of copies needed to estimate F(ρ, σ) within additive error ε, with probability at least 2/3, for
every ρ of rank at most a supplied bound s."

`copyComplexity σ s ε` is the least `n` for which some POVM on `(ℂ^d)^{⊗n}` with real outcomes
estimates `F(ρ, σ)` within `ε` with probability at least `2/3` for every state `ρ` on `ℂ^d` of
rank at most `s` (`IsGoodEstimator`).

**Formalization Note.** The value is an infimum in `ℕ∞`: it is `⊤` when no number of copies
works, so an upper bound on it is never satisfied by a junk default (in `ℕ`, `sInf ∅ = 0`). -/
noncomputable def copyComplexity {d : ℕ} (σ : Matrix (Fin d) (Fin d) ℂ) (s : ℕ) (ε : ℝ) : ℕ∞ :=
  ⨅ (n : ℕ) (_ : ∃ E : QAlgorithms.Measurements.OperatorPOVM (Fin n → Fin d) ℝ,
      IsGoodEstimator σ s ε n E), (n : ℕ∞)

end KnownFidelity.Rank


