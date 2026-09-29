-- Prove2me | Definitions.Def_Freiman_lowerEarlyTerminalSource
-- name    : Freiman_lowerEarlyTerminalSource
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T13:25:11.516569+00:00
-- url     : https://prove2.me/theorems/f78be60c-e7a8-434b-9b8c-32d83480dd4d
-- title:
--   Freiman.lowerEarlyTerminalSource
-- statement:
--   The two short lists,15 terminal interiors,11 common contacts,A40/A46 alternatives and complete final union-case requirement grammar. Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert. Source: certificates/section15_early/{residual_geometry_certificate,extension_1,extension_2}.json and certificates/section15_terminal/geometry_certificate.json; PROOF_GUIDE.md; verification/families/section15_early/{independent_residual,independent_extensions}.py and section15_terminal/verify_independent.py.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert. Source: certificates/section15_early/{residual_geometry_certificate,extension_1,extension_2}.json and certificates/section15_terminal/geometry_certificate.json; PROOF_GUIDE.md; verification/families/section15_early/{independent_residual,independent_extensions}.py and section15_terminal/verify_independent.py. Lean module: Definitions.Def_Freiman_lowerEarlyTerminalSource.

import Definitions.Def_Freiman_lowerEarlyTerminalConstants

namespace Freiman

def lowerEarlyTerminalFirst : List LowerLabel :=
  [([3],[2]),([2,2],[3,1,1]),([2,2],[3,2]),([2],[2])]
def lowerEarlyTerminalSecond : List LowerLabel :=
  [([3],[2]),([1,1,2],[3,1,1]),([1,1,2],[3,2]),([2,1,1,2],[3,3]),
    ([3,1,1,2],[3,3]),([2,2],[3,1,1]),([2,2],[3,2]),([2],[2])]
def lowerEarlyTerminalCommon : List LowerLabel :=
  [([3,1,2],[3,1,2]),([3,1,2],[3,1,1]),([2,1,2],[3,1,1]),([3,1,2],[3,2]),
    ([3,1,2],[3,3]),([2,1,2],[3,2]),([1,1,1,2],[3,1,1]),([2,1,1,2],[3,1,1]),
    ([1,1,1,2],[3,2]),([1,1,1,2],[3,3]),([2,1,1,2],[3,2]),([3,1,1,2],[3,2]),([2,1,1,2],[3,3])]
def lowerEarlyTerminalContacts : List (LowerLabel × LowerLabel) :=
  [((([3],[2])),([3,1,2],[3,1,2])),
   (([3,1,2],[3,1,2]),([3,1,2],[3,1,1])),
   (([2,1,2],[3,1,1]),([3,1,2],[3,2])),
   (([3,1,2],[3,2]),([3,1,2],[3,3])),
   (([3,1,2],[3,3]),([2,1,2],[3,2])),
   (([2,1,2],[3,2]),([1,1,1,2],[3,1,1])),
   (([2,1,1,2],[3,1,1]),([1,1,1,2],[3,2])),
   (([1,1,1,2],[3,2]),([1,1,1,2],[3,3])),
   (([1,1,1,2],[3,3]),([2,1,1,2],[3,2])),
   (([2,1,1,2],[3,2]),([3,1,1,2],[3,2])),
   (([3,1,1,2],[3,2]),([2,1,1,2],[3,3]))]
def lowerEarlyTerminalMiddle (a : Bool) : LowerLabel :=
  if a then ([2,1,2],[3,1,2]) else ([1,2,1,2],[3,1,2])
def lowerEarlyTerminalLast : LowerLabel := ([3,1,1,2],[3,3])
def lowerEarlyTerminalTerminal (a : Bool) : List LowerLabel :=
  [([3],[2]),([3,1,2],[3,1,2]),([3,1,2],[3,1,1]),lowerEarlyTerminalMiddle a] ++
    lowerEarlyTerminalCommon.drop 2 ++ [lowerEarlyTerminalLast,([2],[2])]
def lowerEarlyTerminalBase (C : LowerEarlyTerminalCatalog) : List CertBound :=
  [lowerEarlyTerminalH7,lowerEarlyTerminalH18,⟨false,false,lowerHistoryWH ([],[])⟩] ++
    if C.leftContext = [3] then [] else [lowerEarlyTerminalA9]
def lowerEarlyTerminalHyp (C : LowerEarlyTerminalCatalog) (mode : ℕ) : List CertBound :=
  lowerEarlyTerminalBase C ++ if mode=0 then
    [{lowerEarlyTerminalH27 with lower := true}] else if mode=1 then
    [lowerEarlyTerminalH27,{lowerEarlyTerminalH34 with lower := true}] else
    [lowerEarlyTerminalH27,lowerEarlyTerminalH34]
abbrev LowerEarlyTerminalRequirement := List CertBound × LowerEarlyTerminalKind
def lowerEarlyTerminalCmp (hyp : List CertBound) (a b : LowerLabel) (strict := false) : LowerEarlyTerminalRequirement :=
  (hyp,.compare (section14LabelWords a) true (section14LabelWords b) false strict)
def lowerEarlyTerminalContactRequirements (hyp : List CertBound) (a b : LowerLabel) :
    List LowerEarlyTerminalRequirement :=
  [lowerEarlyTerminalCmp hyp a b,lowerEarlyTerminalCmp hyp b a]
def lowerEarlyTerminalGoodRequirements (hyp : List CertBound) (l : LowerLabel) :
    List LowerEarlyTerminalRequirement :=
  let w := section14LabelWords l
  (section14NormalCases w).flatMap fun (wide,norm) =>
    let one := lowerHistorySet w wide (lowerHistoryPick w wide++[1])
    let two := lowerHistorySet w wide (lowerHistoryPick w wide++[2])
    [(hyp++[norm],.compare one true two false true),
     (hyp++[norm],.compare two true one false true)]
def lowerEarlyTerminalShortRequirements (C : LowerEarlyTerminalCatalog) (mode : ℕ) :
    List LowerEarlyTerminalRequirement :=
  let hyp := lowerEarlyTerminalHyp C mode
  let ls := if mode=0 then lowerEarlyTerminalFirst else lowerEarlyTerminalSecond
  (ls.tail.dropLast.flatMap fun l =>
    lowerEarlyTerminalCmp hyp l l :: lowerEarlyTerminalGoodRequirements hyp l) ++
    (ls.zip ls.tail).flatMap fun (a,b) => lowerEarlyTerminalContactRequirements hyp a b
def lowerEarlyTerminalTerminalRequirements (C : LowerEarlyTerminalCatalog) :
    List LowerEarlyTerminalRequirement :=
  let hyp := lowerEarlyTerminalHyp C 2
  let ordinary := lowerEarlyTerminalCommon ++ [lowerEarlyTerminalLast]
  (ordinary.flatMap fun l => lowerEarlyTerminalCmp hyp l l :: lowerEarlyTerminalGoodRequirements hyp l) ++
  (lowerEarlyTerminalContacts.flatMap fun (a,b) => lowerEarlyTerminalContactRequirements hyp a b) ++
  ([false,true].flatMap fun yes =>
    let h := hyp++[if yes then lowerEarlyTerminalD40 else lowerHistoryComplement lowerEarlyTerminalD40]
    let m := lowerEarlyTerminalMiddle yes
    [lowerEarlyTerminalCmp h m m] ++ lowerEarlyTerminalGoodRequirements h m ++
      lowerEarlyTerminalContactRequirements h ([3,1,2],[3,1,1]) m ++
      lowerEarlyTerminalContactRequirements h m ([2,1,2],[3,1,1])) ++
  ([false,true].flatMap fun yes =>
    let h := hyp++[if yes then lowerEarlyTerminalD46 else lowerHistoryComplement lowerEarlyTerminalD46]
    lowerEarlyTerminalContactRequirements h ([1,1,1,2],[3,1,1])
      (if yes then ([2,1,1,2],[3,1,1]) else ([1,1,1,2],[3,2]))) ++
  lowerEarlyTerminalContactRequirements hyp lowerEarlyTerminalLast ([2],[2]) ++
  [(lowerEarlyTerminalCmp hyp ([2],[2]) ([2,1,1,2],[3,3]))] ++
  ((List.range (lowerEarlyTerminalUnionCases C).length).map fun j => (hyp,.unionCase j))
def lowerEarlyTerminalRequirements (C : LowerEarlyTerminalCatalog) (mode : ℕ) :
    List LowerEarlyTerminalRequirement :=
  if mode < 2 then lowerEarlyTerminalShortRequirements C mode else lowerEarlyTerminalTerminalRequirements C
def lowerEarlyTerminalRequirementBinding (C : LowerEarlyTerminalCatalog) (mode : ℕ) : Prop :=
  ∀ req ∈ lowerEarlyTerminalRequirements C mode,
    ∃ g ∈ C.goals, g.kind = req.2 ∧
      (lowerEarlyTerminalBoundsAt C g.premises).toFinset = req.1.toFinset

noncomputable def lowerEarlyTerminalR (p : LowerPair) : ℝ := lowerRatio (lowerNormalize p).1
noncomputable def lowerEarlyTerminalS (p : LowerPair) : ℝ := lowerRatio (lowerNormalize p).2
noncomputable def lowerEarlyTerminalQ (p : LowerPair) : ℝ := lowerScale (lowerNormalize p)
noncomputable def lowerEarlyTerminalAt (p : LowerPair) (bs : List CertBound) : Prop :=
  section14Holds bs (lowerEarlyTerminalR p) (lowerEarlyTerminalS p) (lowerEarlyTerminalQ p)
noncomputable def lowerEarlyTerminalEndpoint (p : LowerPair) (w : LowerPair) (upper : Bool) : ℝ :=
  lowerHistoryEndpointReal (lowerNormalize p) ⟨([],[]),(false,false)⟩ w upper
noncomputable def lowerEarlyTerminalKindHolds (p : LowerPair) (k : LowerEarlyTerminalKind) : Prop :=
  match k with
  | .compare a hi b hj strict =>
    if strict then lowerEarlyTerminalEndpoint p b hj < lowerEarlyTerminalEndpoint p a hi
    else lowerEarlyTerminalEndpoint p b hj ≤ lowerEarlyTerminalEndpoint p a hi
  | .unionCase _ =>
    lowerEarlyTerminalEndpoint p ([2,1,1,3],[3,3]) false ≤ lowerEarlyTerminalEndpoint p ([2,1,1,2],[3,3]) true ∨
      lowerEarlyTerminalEndpoint p ([2],[2]) false ≤ lowerEarlyTerminalEndpoint p ([2,1,1,2],[3,3]) true
  | .scalar _ | .normalCase _ => True
noncomputable def lowerEarlyTerminalRequiredSound (C : LowerEarlyTerminalCatalog) (p : LowerPair)
    (mode : ℕ) : Prop :=
  ∀ req ∈ lowerEarlyTerminalRequirements C mode, lowerEarlyTerminalAt p req.1 →
    lowerEarlyTerminalKindHolds p req.2

end Freiman


