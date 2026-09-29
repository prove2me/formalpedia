-- Prove2me | Definitions.Def_HighDimStat_MetricEntropy_CoveringNumber
-- name    : HighDimStat_MetricEntropy_CoveringNumber
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T22:57:58.291906+00:00
-- url     : https://prove2.me/theorems/b51ee5c4-7968-481f-96f0-d687b0bf2931
-- title:
--   The delta-covering number of a finite metric space
-- statement:
--   **Definition 5.1.** A $\delta$-cover of a set $T$ with respect to a metric $\rho$ is a set
--   $\{\theta_1,\dots,\theta_N\} \subset T$ such that for each $\theta \in T$, there exists some
--   $i$ with $\rho(\theta,\theta_i) \le \delta$. The $\delta$-covering number $N(\delta; T, \rho)$
--   is the cardinality of the smallest $\delta$-cover.
--
--   $$
--   N(\delta; T, \rho) \;:=\; \min\{|C| : C \subseteq T,\ \forall \theta \in T,\ \exists \theta_i \in C,\ \rho(\theta,\theta_i) \le \delta\}.
--   $$
--
--   This is the basic measure of the "size" of a metric space used throughout the chapter to
--   quantify metric entropy $\log N(\delta;T,\rho)$.
--
--   **Formalization Note** Restricted to a finite index type $T$ (a `Fintype`), rather than the
--   book's general totally bounded metric space, so that the minimum is realized over an explicit,
--   always-nonempty family of `Finset` covers (`Finset.univ` is itself always a valid cover, since
--   $\rho(\theta,\theta)=0\le\delta$ for every $\delta\ge0$), and `Nat.sInf` returns the genuine
--   minimum rather than the junk value $0$ for an empty candidate set.
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 122 (PDF p. 142), Definition 5.1

import Mathlib

namespace HighDimStat.MetricEntropy

/-- **Definition 5.1**, Wainwright, *High-Dimensional Statistics* (2019), p. 122. The
`δ`-covering number `N(δ; T, ρ)` of a finite metric space `(T, ρ)` (`ρ` realized as `dist` from a
`PseudoMetricSpace T` instance) is the cardinality of the smallest `δ`-cover of `T`: a finite set
`{θ₁,...,θN} ⊆ T` such that every `θ ∈ T` lies within `δ` of some `θᵢ`. `Finset.univ` is always a
valid cover (using `dist θ θ = 0`), so the defining set of candidate cardinalities is nonempty and
`Nat.sInf` returns the genuine minimum, not the junk value `0`, for every `δ`. -/
noncomputable def CoveringNumber (T : Type*) [Fintype T] [PseudoMetricSpace T] (δ : ℝ) : ℕ :=
  sInf {N : ℕ | ∃ C : Finset T, C.card = N ∧ ∀ θ : T, ∃ θi ∈ C, dist θ θi ≤ δ}

end HighDimStat.MetricEntropy


