-- Prove2me | Definitions.Def_CompDesignBFM_Supplement_IsBetaSelfBounding
-- name    : CompDesignBFM_Supplement_IsBetaSelfBounding
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T21:04:05.081084+00:00
-- url     : https://prove2.me/theorems/b6464bf0-0e00-48f6-8607-b0a8ca135fd0
-- title:
--   $\beta$-self-bounding set function
-- statement:
--   For a real $\beta$, a function $F:2^N\to\mathbb R_{\ge0}$ is **$\beta$-self-bounding** if it is monotone ($F(S)\le F(T)$ for $S\subseteq T$) and
--
--   $$\sum_{i\in S}\bigl(F(S)-F(S\setminus\{i\})\bigr)\le\beta\,F(S)\qquad\text{for every }S\subseteq N.$$
--
--   For $\beta=1$ this is the class of self-bounding functions, which contains all monotone submodular and XOS functions; every $\beta$-MPH valuation is $\beta$-self-bounding.
--
--   **Formalization Note** Nonnegativity of $F$ is a conjunct. The theorems using this class assume $\beta>0$.
-- source:
--   Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, Definition 1.2, eq. (1), p.4 (PDF 6), restated p.14 (PDF 16)

import Mathlib
import Definitions.Def_CompDesignBFM_IsMonotoneSF

namespace CompDesignBFM

namespace Supplement

/-- A `β`-self-bounding function (Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, Definition 1.2, eq. (1), p.4, PDF 6, restated p.14, PDF 16):
`F : 2^N → ℝ≥0` is monotone and `∑_(i ∈ S) (F(S) − F(S ∖ {i})) ≤ β · F(S)` for every `S ⊆ N`.
**Formalization Note.** The codomain `ℝ≥0` is the conjunct `∀ S, 0 ≤ F S`. At `β = 1` this is the
base mission's `IsSelfBounding`. `β` is a real parameter; the theorems using it assume `0 < β`. -/
def IsBetaSelfBounding {n : ℕ} (β : ℝ) (F : Finset (Fin n) → ℝ) : Prop :=
  (∀ S, 0 ≤ F S) ∧ IsMonotoneSF F ∧ ∀ S, ∑ i ∈ S, (F S - F (S.erase i)) ≤ β * F S

end Supplement

end CompDesignBFM


