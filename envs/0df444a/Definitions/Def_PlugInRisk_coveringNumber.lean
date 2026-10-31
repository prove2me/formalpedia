-- Prove2me | Definitions.Def_PlugInRisk_coveringNumber
-- name    : PlugInRisk_coveringNumber
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:25:42.91519+00:00
-- url     : https://prove2.me/theorems/01d3b535-4760-4f7e-b226-85f07a2ef31a
-- title:
--   Covering number $\mathcal N(\Lambda,d,\varepsilon)$
-- statement:
--   For a set $\Lambda$ with a (pseudo-)distance $d$ and $\varepsilon>0$, the **covering number** $\mathcal N(\Lambda,d,\varepsilon)$ is the smallest cardinality of a subset $\tilde\Lambda\subset\Lambda$ such that every $s\in\Lambda$ has some $\tilde s\in\tilde\Lambda$ with $d(s,\tilde s)\le\varepsilon$; it is $\infty$ if no finite such subset exists.
--
--   The module also defines the entropy integrand $\sqrt{\log\mathcal N}$, with value $\infty$ when $\mathcal N=\infty$, used in Dudley's entropy integral.
--
--   **Formalization Note** The distance is $[0,\infty]$-valued, so it covers the supremum distance and the $L^2(\mu_N)$ pseudo-distance between functions. Centres are taken in $\Lambda$ (internal covers). Values are in $\mathbb N\cup\{\infty\}$; the empty set has covering number $0$.
-- source:
--   Bartl & Tangpi, Non-asymptotic convergence rates for the plug-in estimation of risk measures, arXiv:2003.10479v2, §3, p.11; Theorem A.4, p.34

import Mathlib

open scoped ENNReal

namespace PlugInRisk

/-- **Covering number** (Bartl & Tangpi, arXiv:2003.10479v2, §3, p.11): "For a metric space
(Λ, d_Λ) and ε > 0, denote by N(Λ, d_Λ, ε) the covering numbers at scale ε, that is,
N(Λ, d_Λ, ε) is the smallest number for which there is a subset Λ̃ with that cardinality
satisfying: For every s ∈ Λ there is s̃ ∈ Λ̃ with d_Λ(s, s̃) ≤ ε."

**Formalization Note** The distance is an arbitrary `[0, ∞]`-valued function `d` (the paper
applies the notion to sets of functions with the pseudo-distances of `L²(μ_N)` and of the
supremum norm). The cover `T` is a subset of `A` (internal cover, as in the quote). The value is
in `ℕ∞`: it is `⊤` when no finite cover exists, and `0` for `A = ∅`. -/
noncomputable def coveringNumber {α : Type*} (d : α → α → ℝ≥0∞) (A : Set α) (ε : ℝ≥0∞) : ℕ∞ :=
  ⨅ (T : Finset α) (_ : (↑T : Set α) ⊆ A) (_ : ∀ a ∈ A, ∃ t ∈ T, d a t ≤ ε), (T.card : ℕ∞)

/-- **Entropy integrand** `√(log N)` of a covering number `N` (Bartl & Tangpi,
arXiv:2003.10479v2, Theorem A.4, p.34: the integrand `√(log N(ℱ, ‖·‖_{L²(μ_N)}, ε))`).

**Formalization Note** Valued in `[0, ∞]`: it is `∞` when `N = ∞` (no finite cover). For a
finite `N ≥ 1` it is `√(log N)`; the value at `N = 0` (empty set) is `0`, and the statements using
it concern nonempty classes, where `N ≥ 1`. -/
noncomputable def sqrtLog (c : ℕ∞) : ℝ≥0∞ :=
  if c = ⊤ then ⊤ else ENNReal.ofReal (Real.sqrt (Real.log (c.toNat : ℝ)))

end PlugInRisk


