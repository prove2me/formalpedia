-- Prove2me | Definitions.Def_ReplicableOL_covJ
-- name    : ReplicableOL_covJ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:47:58.066992+00:00
-- url     : https://prove2.me/theorems/b8f6ee75-ef39-48c6-aa06-5fc9db991bc0
-- title:
--   Conditional covariance $\mathrm{Cov}_j$
-- statement:
--   The conditional covariance of the epoch mean with the fraction played on expert 1, given the past: $\mathrm{Cov}_j=\mathbb E[\mu_jp_j\mid\mathcal G_{j-1}]$. At a prefix $h$ it is $\int\mu\sum_s\nu_\mu(s)P_j(h;s)\,dU(\mu)$.
--
--   **Formalization Note** The explicit version as a function of one prefix: `∫ μ Σ_s ν_μ(s) P_j(h; s) dU(μ)`. Lemma 4.1 (`lemma_4_1`) ties it to Mathlib's `condExp`.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Sec. 4.1, p.15

import Mathlib
import Definitions.Def_ReplicableOL_frac
import Definitions.Def_ReplicableOL_blockWeight
import Definitions.Def_ReplicableOL_uniformPrior
open MeasureTheory ProbabilityTheory

namespace ReplicableOL

/-- **Conditional covariance $\mathrm{Cov}_j$.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Sec. 4.1, p.15. `Cov_j := E[μ_j p_j | G_{j−1}]`.

**Formalization Note.** The explicit version as a function of one prefix: `∫ μ Σ_s ν_μ(s) P_j(h; s) dU(μ)`. Lemma 4.1 (`lemma_4_1`) ties it to Mathlib's `condExp`. -/
noncomputable def covJ {k L : ℕ} (Δ : ℝ) (Φ : EpochRule k L) (j : Fin k) (h : Fin j → Block L) : ℝ :=
  ∫ μ, μ * ∑ s : Block L, blockWeight μ s * frac Φ j h s ∂(uniformPrior Δ)

end ReplicableOL


