-- Prove2me | Definitions.Def_Freiman_section14Geometry
-- name    : Freiman_section14Geometry
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T12:46:53.482988+00:00
-- url     : https://prove2.me/theorems/a2b4dce9-e43a-48e2-92bc-0f378b06cac1
-- title:
--   Freiman §14: section14Geometry
-- statement:
--   Exact §14 source model, finite verifier or lossless report data; no theorem or axiom declarations.
-- source:
--   Freiman report, active §14; Appendix Complete finite certificates for the scalar geometry of §14; full_readable_model.json.

import Definitions.Def_Freiman_section14Data

namespace Freiman

noncomputable def section14R (p : LowerPair) : ℝ := lowerRatio (lowerNormalize p).1
noncomputable def section14S (p : LowerPair) : ℝ := lowerRatio (lowerNormalize p).2
noncomputable def section14Q (p : LowerPair) : ℝ := lowerScale (lowerNormalize p)
def section14SuffixMatches (w s : List ℕ+) : Prop :=
  (∀ u : List ℕ+, lowerEnds (w++u) [3] ↔ lowerEnds (s++u) [3]) ∧
  (∀ u : List ℕ+, lowerEnds (w++u) [3,1] ↔ lowerEnds (s++u) [3,1])
noncomputable def section14Matches (p : LowerPair) (S : Section14State) : Prop :=
  section14SuffixMatches (lowerNormalize p).1 S.context.words.1 ∧
  section14SuffixMatches (lowerNormalize p).2 S.context.words.2 ∧
  S.context.parity = (false,true)
noncomputable def section14TargetLower (p : LowerPair) : Bool := by
  classical
  exact decide (¬ lowerH p 2 ∧ lowerH p 5 ∧ lowerL p)
noncomputable def section14RawList (p : LowerPair) : List LowerLabel := by
  classical
  let b : List LowerLabel := [([1],[]),([],[1])]
  let x : List LowerLabel := [([1],[]),([2],[2]),([2,3],[3,2]),([2,3],[3,3])]
  let y : List LowerLabel := [([1,1,3],[3,1,1]),([2,1,3],[3,1,2]),([2,1,3],[3,1,1])]
  let z : List LowerLabel := [([1,1,3],[3,2]),([1,1,3],[3,3]),([2,1,3],[3,2]),([2],[1,1]),([2],[1])]
  let w : List LowerLabel := [([1],[]),([2],[2]),([3,3],[2,1,3]),([3,3],[2,1,2]),
    ([2,3],[2,1,3]),([2,3],[2,1,2]),([2,3],[2,1,1]),([2],[1])]
  let extra : List LowerLabel := if lowerL p then [] else [([3],[1])]
  exact if lowerH p 2 then b else
    if lowerH p 5 then
      if lowerL p then [([1],[]),([2],[])] else
        if lowerH p 6 ∧ lowerH p 7 then [([1],[]),([2],[]),([3],[])]
        else [([1],[]),([2],[]),([3],[1])] else
    if ¬ lowerH p 21 ∧ ¬ lowerEnds (lowerNormalize p).2 [3] ∧ lowerH p 23 then b else
    if lowerH p 21 then x ++ (if lowerH p 17 then [] else y) ++ z ++ extra
    else w ++ extra
noncomputable def section14LocalEndpoint (p : LowerPair) (w : LowerPair) (upper : Bool) : ℝ :=
  let q := lowerNormalize p
  if q.1.length % 2 = 0 then lowerEndpoint (q.1++w.1,q.2++w.2) upper
  else -lowerEndpoint (q.1++w.1,q.2++w.2) (!upper)
noncomputable def section14SpecHolds (p : LowerPair) (s : Section14Spec) : Prop :=
  section14Holds s.extra (section14R p) (section14S p) (section14Q p) →
    if s.strict then
      section14LocalEndpoint p s.second s.secondUpper < section14LocalEndpoint p s.first s.firstUpper
    else section14LocalEndpoint p s.second s.secondUpper ≤ section14LocalEndpoint p s.first s.firstUpper
noncomputable def section14RawGeometry (p : LowerPair) : Prop :=
  ∀ s ∈ section14ExpectedSpecs (section14RawList p) (section14TargetLower p), section14SpecHolds p s

end Freiman


