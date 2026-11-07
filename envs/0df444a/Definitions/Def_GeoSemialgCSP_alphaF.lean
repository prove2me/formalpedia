-- Prove2me | Definitions.Def_GeoSemialgCSP_alphaF
-- name    : GeoSemialgCSP_alphaF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:47:39.023125+00:00
-- url     : https://prove2.me/theorems/56957fbb-d210-4eca-93f7-9217c149718e
-- title:
--   Best biased random assignment value $\alpha^*_f$ of a finite payoff
-- statement:
--   For a payoff $f:[q]^k\to[0,1]$,
--   $$\alpha^*_f=\sup_{w}\ \sum_{a\in[q]^k}f(a)\prod_{j=1}^k w(a_j),$$
--   the supremum over probability distributions $w$ on $[q]$: the best expected payoff of independent labels with a common law.
--
--   **Formalization Note** $w$ ranges over `stdSimplex ℝ (Fin q)`. For $q=0$ the set is empty and the value is $0$.
-- source:
--   Arvanitakis, Chatziafratis, Makarychev, Hardness of Approximation for Semialgebraic CSPs, manuscript (STOC 2027 submission, held version sha256 ee702c42…), §4, p.9 (PDF p.10)

import Mathlib
import Definitions.Def_GeoSemialgCSP_multilin

namespace GeoSemialgCSP

/-- **Best biased random assignment for a finite payoff.** Arvanitakis, Chatziafratis, Makarychev, *Hardness of Approximation for Semialgebraic CSPs*,
manuscript (STOC 2027 submission, held version sha256 ee702c42…), §4, printed p.9
(PDF p.10): for `f : [q]^k → [0,1]`, `α*_f` is defined as `α*_P`, the supremum over probability
distributions `w` on `[q]` of `E_{a ∼ w^{⊗k}} f(a)`.

**Formalization Note.** Distributions on `[q]` are `stdSimplex ℝ (Fin q)`. For `q ≥ 1` the set is
nonempty and bounded, so `sSup` is the supremum; for `q = 0` it is `sSup ∅ = 0`. -/
noncomputable def alphaF {k q : ℕ} (f : (Fin k → Fin q) → ℝ) : ℝ :=
  sSup {v : ℝ | ∃ w ∈ stdSimplex ℝ (Fin q), v = multilin f (fun _ => w)}

end GeoSemialgCSP


