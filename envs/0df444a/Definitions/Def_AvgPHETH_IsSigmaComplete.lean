-- Prove2me | Definitions.Def_AvgPHETH_IsSigmaComplete
-- name    : AvgPHETH_IsSigmaComplete
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:33:12.480814+00:00
-- url     : https://prove2.me/theorems/ef33be1c-9509-42f3-813a-5a95eb5efd7d
-- title:
--   $\Sigma_j^{p,O}$-complete languages
-- statement:
--   A language $C$ is $\Sigma_j^{p,O}$-complete if $C\in\Sigma_j^{p,O}$ and every language in $\Sigma_j^{p,O}$ many-one reduces to $C$ by a function computable in polynomial time with oracle $O$.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), proof of Lemma 6.5, p.29 (PDF 31)

import Mathlib
import Definitions.Def_AvgPHETH_SigmaPO
import Definitions.Def_AvgPHETH_outAt
import Definitions.Def_KarpLiptonOM_OracleTM_HaltsWithin
import Definitions.Def_KarpLiptonOM_tupleEnc
open KarpLiptonOM

namespace AvgPHETH

/-- `C` is `Σ_j^{p,O}`-complete: `C ∈ Σ_j^{p,O}` and every language of the class many-one reduces to `C` by
a function computable in polynomial time with oracle `O` (Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), proof of Lemma 6.5, p.29 (PDF 31)). -/
def IsSigmaComplete (O : Set (List Bool)) (j : ℕ) (C : Set (List Bool)) : Prop :=
  C ∈ SigmaPO O j ∧ ∀ L ∈ SigmaPO O j, ∃ (M : OracleTM) (e : ℕ), ∀ x : List Bool,
    M.HaltsWithin O (x.length ^ e + e) (tupleEnc [x]) ∧
      (x ∈ L ↔ outAt M O (x.length ^ e + e) (tupleEnc [x]) ∈ C)

end AvgPHETH


