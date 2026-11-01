-- Prove2me | Definitions.Def_DattaDiscord_minCondEntropy
-- name    : DattaDiscord_minCondEntropy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:23:53.419973+00:00
-- url     : https://prove2.me/theorems/7060fbd4-75de-4c57-94ae-9b9af6677eec
-- title:
--   Minimized measured conditional entropy $\tilde H(A|B)=\min_{\{\Pi_i\}}\tilde H_{\{\Pi_i\}}(A|B)$
-- statement:
--   For a bipartite operator $\rho_{AB}$,
--
--   $$
--   \tilde H(A|B)=\min_{\{\Pi_i\}}\tilde H_{\{\Pi_i\}}(A|B),
--   $$
--
--   the minimum of the measured conditional entropy over all rank-one POVMs $\{\Pi_i\}$ on $B$, with any finite number of outcomes.
--
--   **Formalization Note** The minimum is written as the infimum (`sInf`) of the set of values $\tilde H_{\{\Pi_i\}}(A|B)$, taken over every $n$ and every rank-one POVM indexed by `Fin n`. For a density matrix this set is nonempty (the standard basis of $B$) and bounded below by $0$, so the infimum is a genuine one; that it is attained is the milestone `DattaDiscord.minCondEntropy_attained`.
-- source:
--   Datta, A Condition for the Nullity of Quantum Discord, arXiv:1003.5256v2, p.1 (before Eq. (2), "H̃(A|B) = min{Πi} H̃{Πi}(A|B)")

import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_DattaDiscord_IsRankOnePOVM
import Definitions.Def_DattaDiscord_measuredCondEntropy

open scoped ComplexConjugate

namespace DattaDiscord

/-- **Minimized measured conditional entropy** `H̃(A|B) = min_{Πᵢ} H̃_{Πᵢ}(A|B)`, Datta, *A Condition for the Nullity of Quantum Discord*, arXiv:1003.5256v2,
p.1 (before Eq. (2)), the minimum taken over all rank-one POVMs on `B` ("where {Πi} are now, and
henceforth in the paper, rank 1 POVMs", p.1), with any finite number of outcomes.

**Formalization Note** The minimum is written as the infimum `sInf` of the set of values
`H̃_{Π}(A|B)` over every `n` and every rank-one POVM `M : Fin n → Matrix B B ℂ`. For a density
matrix this set is nonempty (the standard basis of `B` is a rank-one POVM) and bounded below by
`0`, so the infimum is not a junk value; that the infimum is attained (the paper's "min") is a
separate milestone. -/
noncomputable def minCondEntropy {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B]
    [DecidableEq B] (ρ : Matrix (A × B) (A × B) ℂ) : ℝ :=
  sInf {h : ℝ | ∃ (n : ℕ) (M : Fin n → Matrix B B ℂ), IsRankOnePOVM M ∧
    h = measuredCondEntropy ρ M}

end DattaDiscord


