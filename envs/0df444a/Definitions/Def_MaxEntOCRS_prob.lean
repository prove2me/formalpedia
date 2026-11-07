-- Prove2me | Definitions.Def_MaxEntOCRS_prob
-- name    : MaxEntOCRS_prob
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:29:57.80873+00:00
-- url     : https://prove2.me/theorems/c30feda0-b35c-4a79-8a45-fa4ba2151235
-- title:
--   Probability $\Pr_\mu[S]$ of an event on edge sets
-- statement:
--   For a weight function $\mu$ on the subsets of a finite set $E$ and a property $S$ of edge sets, the probability of $S$ is
--   $$
--   \Pr_\mu[S] = \sum_{M \subseteq E,\ S(M)} \mu(M).
--   $$
--   All probabilities of the mission (marginals, covering probabilities, the event $\mathrm{Add}(e)$) are of this form.
-- source:
--   Chen–Wang, Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality, STOC 2027 submission (manuscript sha256 06944af9…), Sections 2–6 (probabilities under distributions on matchings)

import Mathlib

namespace MaxEntOCRS

open Classical in
/-- The probability `Pr_μ[S] = ∑_{M : S M} μ(M)` of an event `S` on edge sets under a weight
function `μ` on `Finset E` (Chen–Wang, *Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality*, STOC 2027 submission manuscript (sha256 06944af9…2d0462c), used throughout §§2–6). -/
noncomputable def prob {E : Type} [Fintype E] (μ : Finset E → ℝ) (S : Finset E → Prop) : ℝ :=
  ∑ M, if S M then μ M else 0

end MaxEntOCRS


