-- Prove2me | Definitions.Def_KawasakiSOS_Threshold_IsSlideChain
-- name    : KawasakiSOS_Threshold_IsSlideChain
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:07:18.469584+00:00
-- url     : https://prove2.me/theorems/7d000772-a9f9-4a9d-8b6f-769bf6c48cc5
-- title:
--   Chains of slide realizations
-- statement:
--   Given the list of stages produced by a site sequence, this predicate describes the middle of a canonical path: consecutive equal stages contribute nothing, and each change of stage $S\to S'$ is a slide and contributes its realization, carrying the reservoir site along.
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), unnumbered, p. 14 (PDF p. 15)

import Mathlib
import Definitions.Def_KawasakiSOS_Threshold_Config
import Definitions.Def_KawasakiSOS_Threshold_Stage
import Definitions.Def_KawasakiSOS_Threshold_Segment
import Definitions.Def_KawasakiSOS_Threshold_IsSlide
import Definitions.Def_KawasakiSOS_Threshold_IsSlideRealization

namespace KawasakiSOS.Threshold

/-- Walking along the list of stages from `S` with reservoir `ξ`: a repeated stage does nothing, and each change of stage is a slide with its realization. `ξf` is the final reservoir site.

Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), unnumbered, p. 14 (PDF p. 15). -/
def IsSlideChain {n k : ℕ} [NeZero k] (x y : Config n k) :
    Stage k → ZMod k → List (Stage k) → ZMod k → List (Segment k × List (Config n k)) → Prop
  | _, ξ, [], ξf, segs => ξf = ξ ∧ segs = []
  | S, ξ, S' :: rest, ξf, segs =>
      if S' = S then IsSlideChain x y S ξ rest ξf segs
      else ∃ ξ' l segs', IsSlide S S' ∧ IsSlideRealization x y S S' ξ ξ' l ∧
        IsSlideChain x y S' ξ' rest ξf segs' ∧ segs = (Segment.slide S S' ξ ξ', l) :: segs'

end KawasakiSOS.Threshold


