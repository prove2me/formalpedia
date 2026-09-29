-- Prove2me | Definitions.Def_Freiman_lowerEarlyTerminalGeometry
-- name    : Freiman_lowerEarlyTerminalGeometry
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T13:38:18.80491+00:00
-- url     : https://prove2.me/theorems/1e92cd53-da89-4f7c-81c0-c874baafa1e3
-- title:
--   Freiman.lowerEarlyTerminalGeometry
-- statement:
--   Actual normalized-state matching, source rectangle and cut applicability, endpoint/field semantic laws, and finite interval-contact graph interfaces. Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert. Source: certificates/section15_early/{residual_geometry_certificate,extension_1,extension_2}.json and certificates/section15_terminal/geometry_certificate.json; PROOF_GUIDE.md; verification/families/section15_early/{independent_residual,independent_extensions}.py and section15_terminal/verify_independent.py.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert. Source: certificates/section15_early/{residual_geometry_certificate,extension_1,extension_2}.json and certificates/section15_terminal/geometry_certificate.json; PROOF_GUIDE.md; verification/families/section15_early/{independent_residual,independent_extensions}.py and section15_terminal/verify_independent.py. Lean module: Definitions.Def_Freiman_lowerEarlyTerminalGeometry.

import Definitions.Def_Freiman_lowerEarlyTerminalData
import Definitions.Def_Freiman_lowerEarlyTerminalSource

namespace Freiman

def LowerEarlyTerminalEndpointLaw : Prop :=
  ∀ (base : LowerPair) (C : LowerHistoryContext), C.parity = (false,false) →
    lowerHistoryContextFits base C → ∀ (w : LowerPair) (upper : Bool),
      ∃ z cs, (z,cs) ∈ section14EndpointCases C w upper ∧
        lowerHistoryAtBase base cs ∧
        (0 ≤ certFieldVal z.1 ∧ 0 ≤ certFieldVal z.2) ∧
        lowerHistoryEndpointReal base C w upper = lowerHistoryValue base C z
def LowerEarlyTerminalGreaterLaw : Prop :=
  ∀ (base : LowerPair) (C : LowerHistoryContext), C.parity = (false,false) →
    lowerHistoryContextFits base C → ∀ (x y : CertField × CertField) (strict : Bool),
      (0 ≤ certFieldVal x.1 ∧ 0 ≤ certFieldVal x.2) →
      (0 ≤ certFieldVal y.1 ∧ 0 ≤ certFieldVal y.2) →
      (section14ComparisonHolds (lowerEarlyTerminalGreater x y strict)
        (lowerRatio base.1) (lowerRatio base.2) (lowerScale base) ↔
        if strict then lowerHistoryValue base C y < lowerHistoryValue base C x
        else lowerHistoryValue base C y ≤ lowerHistoryValue base C x)
noncomputable def lowerEarlyTerminalMatches (p : LowerPair) (C : LowerEarlyTerminalCatalog) : Prop :=
  lowerHistoryContextFits (lowerNormalize p) (lowerEarlyTerminalContext C)
noncomputable def lowerEarlyTerminalApplied (p : LowerPair) (C : LowerEarlyTerminalCatalog)
    (mode : ℕ) : Prop :=
  lowerEarlyTerminalMatches p C ∧
  certRectangleMem C.rectangle (lowerEarlyTerminalR p) (lowerEarlyTerminalS p) ∧
  lowerEarlyTerminalAt p (lowerEarlyTerminalHyp C mode)
noncomputable def lowerEarlyTerminalRecordSound (C : LowerEarlyTerminalCatalog)
    (rec : LowerEarlyTerminalRecord) : Prop :=
  ∀ r s q : ℝ, certRectangleMem C.rectangle r s →
    ¬ section14Holds (lowerEarlyTerminalResidual C (lowerEarlyTerminalGoal C rec.goal) rec.branch) r s q
noncomputable def lowerEarlyTerminalPairSound (C : LowerEarlyTerminalCatalog) : Prop :=
  ∀ p ∈ C.pairs, ∀ r s q : ℝ, certRectangleMem C.rectangle r s →
    ¬ (certBoundHolds (lowerEarlyTerminalBound C p.lowerId) r s q ∧
      certBoundHolds (lowerEarlyTerminalBound C p.upperId) r s q)
noncomputable def lowerEarlyTerminalRecordsSound (C : LowerEarlyTerminalCatalog) : Prop :=
  ∀ rec ∈ C.records, lowerEarlyTerminalRecordSound C rec
noncomputable def lowerEarlyTerminalUnionHolds (p : LowerPair) : Prop :=
  lowerEarlyTerminalEndpoint p ([2,1,1,3],[3,3]) false ≤ lowerEarlyTerminalEndpoint p ([2,1,1,2],[3,3]) true ∨
    lowerEarlyTerminalEndpoint p ([2],[2]) false ≤ lowerEarlyTerminalEndpoint p ([2,1,1,2],[3,3]) true
noncomputable def lowerEarlyTerminalContact (p : LowerPair) (a b : LowerLabel) : Prop :=
  (lowerCover (lowerChild p a) ∩ lowerCover (lowerChild p b)).Nonempty
noncomputable def lowerEarlyTerminalPrimary (p : LowerPair) : Bool := by
  classical
  exact decide (lowerA p 40)
noncomputable def lowerEarlyTerminalLabelsGood (p : LowerPair) (ls : List LowerLabel) : Prop :=
  ∀ l ∈ ls, lowerGood (lowerChild p l) ∧ (lowerCover (lowerChild p l)).Nonempty
noncomputable def lowerEarlyTerminalShortData (p : LowerPair) (ls : List LowerLabel) : Prop :=
  lowerEarlyTerminalLabelsGood p ls ∧ ls.IsChain (lowerEarlyTerminalContact p)
noncomputable def lowerEarlyTerminalTerminalData (p : LowerPair) (primary : Bool) : Prop :=
  lowerEarlyTerminalLabelsGood p (lowerEarlyTerminalTerminal primary) ∧
  (∀ ab ∈ lowerEarlyTerminalContacts, lowerEarlyTerminalContact p ab.1 ab.2) ∧
  lowerEarlyTerminalContact p ([3,1,2],[3,1,1]) (lowerEarlyTerminalMiddle primary) ∧
  lowerEarlyTerminalContact p (lowerEarlyTerminalMiddle primary) ([2,1,2],[3,1,1]) ∧
  (lowerEarlyTerminalContact p ([1,1,1,2],[3,1,1]) ([2,1,1,2],[3,1,1]) ∨
    lowerEarlyTerminalContact p ([1,1,1,2],[3,1,1]) ([1,1,1,2],[3,2])) ∧
  lowerEarlyTerminalContact p lowerEarlyTerminalLast ([2],[2]) ∧
  (lowerCover (lowerChild p ([2,1,1,2],[3,3])) ∩
    (lowerCover (lowerChild p lowerEarlyTerminalLast) ∪ lowerCover (lowerChild p ([2],[2])))).Nonempty
noncomputable def lowerEarlyTerminalListGeometry (p : LowerPair) (ls : List LowerLabel) : Prop :=
  (∀ l ∈ ls, lowerGood (lowerChild p l)) ∧
    IsPreconnected {t : ℝ | ∃ l ∈ ls, t ∈ lowerCover (lowerChild p l)} ∧
    lowerCover (lowerChild p ([3],[2])) ⊆ {t : ℝ | ∃ l ∈ ls, t ∈ lowerCover (lowerChild p l)} ∧
    lowerCover (lowerChild p ([2],[2])) ⊆ {t : ℝ | ∃ l ∈ ls, t ∈ lowerCover (lowerChild p l)}

def lowerEarlyTerminalShortCatalog (i : Fin 3) : LowerEarlyTerminalCatalog :=
  lowerEarlyTerminalCatalog ⟨i.val,by omega⟩
def lowerEarlyTerminalTerminalCatalog (i : Fin 3) : LowerEarlyTerminalCatalog :=
  lowerEarlyTerminalCatalog ⟨i.val+1,by omega⟩
def LowerEarlyTerminalParameterLaws : Prop :=
  ∀ p : LowerPair,
    (lowerEarlyTerminalAt p [lowerEarlyTerminalH7] ↔ ¬ lowerA p 3) ∧
    (lowerEarlyTerminalAt p [lowerEarlyTerminalH18] ↔ ¬ lowerA p 16) ∧
    (lowerEarlyTerminalAt p [lowerEarlyTerminalA9] ↔ lowerA p 9) ∧
    (lowerEarlyTerminalAt p [{lowerEarlyTerminalH27 with lower := true}] ↔ lowerA p 27) ∧
    (lowerEarlyTerminalAt p [{lowerEarlyTerminalH34 with lower := true}] ↔ lowerA p 34) ∧
    (lowerEarlyTerminalAt p [lowerEarlyTerminalD40] ↔ lowerA p 40) ∧
    (lowerEarlyTerminalAt p [lowerEarlyTerminalD46] ↔ lowerA p 46)

def LowerEarlyTerminalDomainLaws : Prop :=
  ∀ t p, lowerState t p → lowerEarlyDomain p →
    (∃ i : Fin 3,
      lowerEarlyTerminalMatches p (lowerEarlyTerminalShortCatalog i) ∧
      certRectangleMem (lowerEarlyTerminalShortCatalog i).rectangle
        (lowerEarlyTerminalR p) (lowerEarlyTerminalS p)) ∧
    (∀ i : Fin 3, lowerEnds (lowerNormalize p).1
        (lowerEarlyTerminalTerminalCatalog i).leftContext →
      lowerEarlyTerminalMatches p (lowerEarlyTerminalTerminalCatalog i) ∧
      certRectangleMem (lowerEarlyTerminalTerminalCatalog i).rectangle
        (lowerEarlyTerminalR p) (lowerEarlyTerminalS p))

/- Incoming order matters at an ordinary or virtual full-width tie. -/
noncomputable def LowerEarlyTerminalNoTies (w : LowerPair) : Prop :=
  lowerWidth w.1 ≠ lowerWidth w.2 ∧
  (w.1.length % 2 ≠ w.2.length % 2 →
    lowerWidth (w.1 ++ [1]) ≠ lowerWidth w.2 ∧
    lowerWidth w.1 ≠ lowerWidth (w.2 ++ [1]))
noncomputable def lowerEarlyTerminalNative (p : LowerPair) (l : LowerLabel) : Prop :=
  l ∈ (lowerEarlyList p).tail.dropLast
def lowerEarlyTerminalForkWords (l : LowerLabel) (wide : Bool) (d : ℕ+) : LowerPair :=
  let w := section14LabelWords l
  lowerHistorySet w wide (lowerHistoryPick w wide ++ [d])
noncomputable def lowerEarlyTerminalForkPair (p : LowerPair) (l : LowerLabel)
    (wide : Bool) (d : ℕ+) : LowerPair :=
  lowerHistoryAppend (lowerNormalize p) (lowerEarlyTerminalForkWords l wide d)
noncomputable def lowerEarlyTerminalForkAlignment (p : LowerPair) (l : LowerLabel) : Prop :=
  ∀ (wide : Bool) (norm : CertBound), (wide,norm) ∈ section14NormalCases (section14LabelWords l) →
    lowerEarlyTerminalAt p [norm] → ∀ d ∈ ([1,2] : List ℕ+), ∀ upper : Bool,
      lowerEndpoint (lowerChild (lowerChild p l) ([d],[])) upper =
        lowerEndpoint (lowerEarlyTerminalForkPair p l wide d) upper
noncomputable def lowerEarlyTerminalTie2 (p : LowerPair) (l : LowerLabel) : Prop :=
  l = ([2,2],[3,2]) ∧ lowerEnds (lowerNormalize p).1 [2] ∧
    lowerWidth (lowerEarlyTerminalForkPair p l true 1).1 =
      lowerWidth ((lowerEarlyTerminalForkPair p l true 1).2 ++ [1])
noncomputable def lowerEarlyTerminalTie3 (p : LowerPair) (l : LowerLabel) : Prop :=
  l = ([2,2],[3,2]) ∧ lowerEnds (lowerNormalize p).1 [3] ∧
    lowerWidth (lowerEarlyTerminalForkPair p l true 2).1 =
      lowerWidth (lowerEarlyTerminalForkPair p l true 2).2

/- This finite range table is generated from the actual four native lists. -/
def lowerEarlyTerminalNativeLabels : List LowerLabel :=
  (lowerEarlyTerminalFirst.tail.dropLast ++ lowerEarlyTerminalSecond.tail.dropLast ++
    (lowerEarlyTerminalTerminal false).tail.dropLast ++
    (lowerEarlyTerminalTerminal true).tail.dropLast).eraseDups
structure LowerEarlyTerminalForkCase where
  leftContext : ℕ+
  label : LowerLabel
  digit : ℕ+
  virtual : Fin 3
  deriving DecidableEq
def lowerEarlyTerminalForkCases : List LowerEarlyTerminalForkCase :=
  ([1,2,3] : List ℕ+).flatMap fun c => lowerEarlyTerminalNativeLabels.flatMap fun l =>
    ([1,2] : List ℕ+).flatMap fun d =>
      (if (l.1.length + l.2.length + 1) % 2 = 0 then [0] else [0,1,2]).map
        fun v => ⟨c,l,d,v⟩
def lowerEarlyTerminalForkExceptional (c : LowerEarlyTerminalForkCase) : Prop :=
  c.label = ([2,2],[3,2]) ∧
    ((c.leftContext = 2 ∧ c.digit = 1 ∧ c.virtual = 2) ∨
     (c.leftContext = 3 ∧ c.digit = 2 ∧ c.virtual = 0))
def lowerEarlyTerminalRatioWords (c : LowerEarlyTerminalForkCase) : LowerPair :=
  ((if c.virtual = 1 then [1] else []) ++ c.label.1 ++ [c.leftContext],
   (if c.virtual = 2 then [1] else []) ++ [c.digit] ++ c.label.2.reverse ++ [1,3])
def lowerEarlyTerminalRatCF (w : List ℕ+) (x : ℚ) : ℚ :=
  w.foldr (fun d t => 1 / ((d : ℚ) + t)) x
def lowerEarlyTerminalRatioRange (w : List ℕ+) : ℚ × ℚ :=
  (min (lowerEarlyTerminalRatCF w 0) (lowerEarlyTerminalRatCF w 1),
   max (lowerEarlyTerminalRatCF w 0) (lowerEarlyTerminalRatCF w 1))
def lowerEarlyTerminalReflectRatio (r : ℚ) : ℚ := (4-3*r)/(3+4*r)
def lowerEarlyTerminalRangesApart (a b : ℚ × ℚ) : Prop := a.2 < b.1 ∨ b.2 < a.1
def lowerEarlyTerminalForkRangeExcluded (c : LowerEarlyTerminalForkCase) : Prop :=
  let w := lowerEarlyTerminalRatioWords c
  let a := lowerEarlyTerminalRatioRange w.1
  let b := lowerEarlyTerminalRatioRange w.2
  lowerEarlyTerminalRangesApart a b ∧
    lowerEarlyTerminalRangesApart (lowerEarlyTerminalReflectRatio a.2, lowerEarlyTerminalReflectRatio a.1) b
def lowerEarlyTerminalForkRangesValid : Prop :=
  ∀ c ∈ lowerEarlyTerminalForkCases, ¬ lowerEarlyTerminalForkExceptional c →
    lowerEarlyTerminalForkRangeExcluded c

end Freiman


