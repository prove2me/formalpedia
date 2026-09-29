-- Prove2me | Definitions.Def_Freiman_lowerOther22
-- name    : Freiman_lowerOther22
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T11:50:19.253838+00:00
-- url     : https://prove2.me/theorems/32a2a8a4-201c-43fd-ad10-0161e4074357
-- title:
--   Freiman old23-other22 target history
-- statement:
--   The exact selected Z→B→R→S ancestry with retained and strictly reflected incoming order, actual goodness and source tests; local scalar endpoints and the two source target bounds.
-- source:
--   Freiman report, parts/other22_target.tex, lem:old23-other22-target and eq:other22-upper-bound.

import Definitions.Def_Freiman_lowerCertificates

namespace Freiman
noncomputable def lowerBaseLower (p : LowerPair) : ℝ :=
  if (lowerNormalize p).1.length % 2 = 0 then lowerEndpoint p false else -lowerEndpoint p true
noncomputable def lowerChildUpper (p : LowerPair) (l : LowerLabel) : ℝ :=
  if (lowerNormalize p).1.length % 2 = 0 then lowerEndpoint (lowerChild p l) true
  else -lowerEndpoint (lowerChild p l) false

structure LowerOther22Geometry (Z B R S : LowerPair) : Prop where
  normalizedZ : lowerNormalize Z = Z
  equalZ : Z.1.length % 2 = Z.2.length % 2
  right31 : lowerEnds Z.2 [3,1]
  admissibleZ : lowerAdmissible Z
  goodZ : lowerGood Z
  boxZ : lowerParameterBox Z
  largeZ3 : ¬ lowerA Z 3
  largeZ9 : ¬ lowerA Z 9
  birth : B = lowerChild Z ([2],[3])
  normalizedB : lowerNormalize B = B
  admissibleB : lowerAdmissible B
  goodB : lowerGood B
  boxB : lowerParameterBox B
  sourceB : lowerA B 3 ∨ (¬ lowerA B 3 ∧ lowerA B 9)
  stepR : R = lowerChild B ([2],[])
  reflectsR : lowerWidth R.1 < lowerWidth R.2
  normalizedR : lowerNormalize R = (B.2,B.1 ++ [2])
  admissibleR : lowerAdmissible R
  goodR : lowerGood R
  boxR : lowerParameterBox R
  stepS : S = lowerChild R ([1],[])
  normalizedS : lowerNormalize S = S
  admissibleS : lowerAdmissible S
  goodS : lowerGood S
  boxS : lowerParameterBox S
  equalS : S.1.length % 2 = S.2.length % 2
  largeS3 : ¬ lowerA S 3
  largeS9 : ¬ lowerA S 9

noncomputable def lowerOther22EndpointBound (Z S : LowerPair) : Prop := by
  classical
  exact if lowerEnds Z.1 [3,1] then lowerLocalLower S ([2],[1]) ≤ lowerBaseLower Z
  else lowerLocalLower S ([2],[1]) ≤ lowerChildUpper Z ([3],[2])
end Freiman

namespace Freiman
noncomputable def lowerOther22Reached (t : ℝ) (S : LowerPair) : Prop :=
  ∃ Z B R : LowerPair, LowerOther22Geometry Z B R S ∧
    t ∈ lowerCover Z ∧ lowerPriority t Z ([2],[3])
end Freiman


