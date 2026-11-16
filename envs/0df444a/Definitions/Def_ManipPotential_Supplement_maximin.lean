-- Prove2me | Definitions.Def_ManipPotential_Supplement_maximin
-- name    : ManipPotential_Supplement_maximin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:06:32.140668+00:00
-- url     : https://prove2.me/theorems/35347d06-72ca-454f-99ad-e79cc7601dc3
-- title:
--   Maximin $\mathrm{MM}$
-- statement:
--   **Maximin** ($\mathrm{MM}$) scores each candidate by its lowest margin against the candidates and outputs the candidates of highest score:
--   $$\mathrm{MM}(\succ_N) = \arg\max_{c \in C} \min_{c' \in C} M(\succ_N)[c, c'] .$$
--
--   **Formalization Note** The minimum is over all $c' \in C$, as printed, including $c' = c$ where $M[c,c] = 0$. The proof in Appendix A.4 minimizes over $c' \ne c$; both give the same set of maximizers.
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 4.3.2, p.20

import Mathlib
import Definitions.Def_ManipPotential_Supplement_SCC
import Definitions.Def_ManipPotential_Supplement_margin

namespace ManipPotential.Supplement

open Classical in
/-- Maximin `MM(≻_N) = argmax_{c∈C} min_{c'∈C} M(≻_N)[c, c']` (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 4.3.2, p.20).

**Formalization Note** The minimum is over all `c' ∈ C`, as printed (including `c' = c`, where
`M[c, c] = 0`); the proof in Appendix A.4 minimizes over `c' ≠ c`, which gives the same set of
maximizers. Requires `m ≥ 1` (`[NeZero m]`) for the minimum to exist. -/
noncomputable def maximin {m : ℕ} [NeZero m] : SCC m := fun P =>
  Finset.univ.filter (fun c => ∀ d : Fin m,
    Finset.univ.inf' Finset.univ_nonempty (margin P d) ≤
      Finset.univ.inf' Finset.univ_nonempty (margin P c))

end ManipPotential.Supplement


