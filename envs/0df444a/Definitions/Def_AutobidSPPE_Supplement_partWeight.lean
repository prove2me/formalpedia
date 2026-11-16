-- Prove2me | Definitions.Def_AutobidSPPE_Supplement_partWeight
-- name    : AutobidSPPE_Supplement_partWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:37:47.694606+00:00
-- url     : https://prove2.me/theorems/e8b1801c-1a6e-4121-914a-5b825e6d33d7
-- title:
--   Participation-set probability $\pi(\alpha,P)$
-- statement:
--   Bidder $j$ participates in the throttled auction with probability $\alpha_j$, through a coin $\xi_j\sim\mathrm{Bernoulli}(\alpha_j)$, independently across bidders. The probability that the set of participants is exactly $P\subseteq[n]$ is
--   $$
--   \pi(\alpha,P)=\prod_{j\in P}\alpha_j\prod_{k\notin P}(1-\alpha_k).
--   $$
--   It is the weight with which every expectation over the coins is computed.
--
--   **Formalization Note** $P$ ranges over all subsets of the bidders, including the bidder's own coin; the paper's $\pi_S(\alpha)$ for a rival set $S\subseteq[n]\setminus\{i\}$ is the same product with bidder $i$'s factor omitted.
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), Problem 1.2, p.4; §3.2, p.26; §3.3 ($\pi_S$), p.27

import Mathlib

namespace AutobidSPPE.Supplement

open AutobidSPPE

/-- The probability `π(α, P) = ∏_{j∈P} αⱼ ∏_{k∉P} (1 − αₖ)` that the set of participating
bidders is exactly `P` (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), Problem 1.2, p.4; §3.2, p.26; `π_S` of §3.3, p.27): bidder `j` participates
with probability `αⱼ` (its coin `ξⱼ ∼ Bernoulli(αⱼ)`), independently across bidders.

**Formalization Note** `P` ranges over all subsets of `Fin n` and includes the bidder's own coin; the
paper's `π_S(α)` for a rival set `S ⊆ [n]∖{i}` is the same product with bidder `i`'s factor omitted. -/
noncomputable def partWeight {n : ℕ} (α : Fin n → ℝ) (P : Finset (Fin n)) : ℝ :=
  (∏ j ∈ P, α j) * ∏ k ∈ Pᶜ, (1 - α k)

end AutobidSPPE.Supplement


