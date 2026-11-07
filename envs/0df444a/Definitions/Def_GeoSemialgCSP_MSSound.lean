-- Prove2me | Definitions.Def_GeoSemialgCSP_MSSound
-- name    : GeoSemialgCSP_MSSound
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:50:36.589932+00:00
-- url     : https://prove2.me/theorems/61c2d7e3-60fe-440c-af03-85fa7914fc11
-- title:
--   Height property of Lemma 4.1
-- statement:
--   A height $h$ has the **multiscale soundness property** for $q_0$ and $\varepsilon$ if for every $q\le q_0$ and every payoff $f:[q]^k\to[0,1]$,
--   $$\mathrm{OPT}(\tilde I_f)\ \le\ \alpha^*_f+\varepsilon .$$
--
--   Lemma 4.1 says that all sufficiently large heights have this property; Section 4 fixes such a height.
-- source:
--   Arvanitakis, Chatziafratis, Makarychev, Hardness of Approximation for Semialgebraic CSPs, manuscript (STOC 2027 submission, held version sha256 ee702c42…), Lemma 4.1, p.10 (PDF p.11)

import Mathlib
import Definitions.Def_GeoSemialgCSP_msOPT
import Definitions.Def_GeoSemialgCSP_alphaF

namespace GeoSemialgCSP

/-- **The height property of Lemma 4.1.** Arvanitakis, Chatziafratis, Makarychev, *Hardness of Approximation for Semialgebraic CSPs*,
manuscript (STOC 2027 submission, held version sha256 ee702c42…), Lemma 4.1, printed p.10 (PDF
p.11): the height `h` has the property that for every `q ≤ q₀` and every payoff
`f : [q]^k → [0,1]`, `OPT(Ĩ_f) ≤ α*_f + ε`. Section 4 fixes such a height ("fix `q₀`, `ε` and a
height `h` satisfying Lemma 4.1", p.10). -/
def MSSound (k q₀ : ℕ) (ε : ℝ) (h : ℕ) : Prop :=
  ∀ q ≤ q₀, ∀ f : (Fin k → Fin q) → ℝ, (∀ a, f a ∈ Set.Icc (0 : ℝ) 1) →
    msOPT h f ≤ alphaF f + ε

end GeoSemialgCSP


