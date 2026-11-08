-- Prove2me | Definitions.Def_CompDesignBFM_IsSelfBounding
-- name    : CompDesignBFM_IsSelfBounding
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:33:13.69125+00:00
-- url     : https://prove2.me/theorems/7b12df61-b2cd-4fb8-9eb1-f0056613bf61
-- title:
--   Self-bounding function
-- statement:
--   A function $F:2^N\to\mathbb R_{\ge0}$ is **self-bounding** if it is monotone and
--
--   $$\sum_{i\in S}\bigl(F(S)-F(S\setminus\{i\})\bigr)\le F(S)\quad\text{for every } S\subseteq N.$$
--
--   This is exactly what makes the marginal-contribution payment rule budget feasible.
-- source:
--   Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, Definition 1.2 at β = 1, eq. (1), p.4 (PDF 6), restated p.14 (PDF 16)

import Mathlib
import Definitions.Def_CompDesignBFM_IsMonotoneSF

namespace CompDesignBFM

/-- A self-bounding function (Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, Definition 1.2 at `β = 1`, eq. (1), p.4 = PDF 6, restated p.14 =
PDF 16): nonnegative, monotone, and `∑ i ∈ S, (F S - F (S ∖ {i})) ≤ F S` for every `S`. -/
def IsSelfBounding {n : ℕ} (F : Finset (Fin n) → ℝ) : Prop :=
  (∀ S, 0 ≤ F S) ∧ IsMonotoneSF F ∧ ∀ S, ∑ i ∈ S, (F S - F (S.erase i)) ≤ F S

end CompDesignBFM


