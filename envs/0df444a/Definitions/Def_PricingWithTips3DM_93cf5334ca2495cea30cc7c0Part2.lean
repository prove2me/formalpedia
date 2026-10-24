-- Prove2me | Definitions.Def_PricingWithTips3DM_93cf5334ca2495cea30cc7c0Part2
-- name    : PricingWithTips3DM_93cf5334ca2495cea30cc7c0Part2
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T06:30:48.959682+00:00
-- url     : https://prove2.me/theorems/a221e0b5-d5f1-4fa1-a0a4-389741a90047
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.QueryNormalizer.Basic.Part2
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_93cf5334ca2495cea30cc7c0Part1
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.QueryNormalizer
open PolyBuilder

def revProgram : Program CliqueSym CliqueSym where
  Label := Label
  main := .scan
  op
    | .scan => .popInput .halt fun
        | .edgeMark => .left
        | _ => .invalid
    | .left => .popInput .invalid fun
        | .tick => .incrementLeft
        | .pairSep => .right
        | _ => .invalid
    | .incrementLeft => .inc₁ .left
    | .right => .popInput .invalid fun
        | .tick => .incrementRight
        | .recordEnd => .compareLeft
        | _ => .invalid
    | .incrementRight => .inc₂ .right
    | .compareLeft => .dec₁ .probeRight .compareRight
    | .compareRight => .dec₂
        (.restoreMatched .rightLess) .saveMatched
    | .saveMatched => .inc₃ .compareLeft
    | .probeRight => .dec₂
        (.restoreMatched .equal) (.restoreMatched .leftLess)
    | .restoreMatched order => .dec₃
        (match order with
          | .leftLess => .restoreExtraRight
          | .equal => .pushEdgeMark .equal
          | .rightLess => .restoreExtraLeft)
        (.restoreLeft order)
    | .restoreLeft order => .inc₁ (.restoreRight order)
    | .restoreRight order => .inc₂ (.restoreMatched order)
    | .restoreExtraLeft => .inc₁ (.pushEdgeMark .rightLess)
    | .restoreExtraRight => .inc₂ (.pushEdgeMark .leftLess)
    | .pushEdgeMark order => .pushOutput .edgeMark (.lower order)
    | .lower .leftLess => .dec₁
        (.pushPairSeparator .leftLess) (.pushLowerTick .leftLess)
    | .lower .equal => .dec₁
        (.pushPairSeparator .equal) (.pushLowerTick .equal)
    | .lower .rightLess => .dec₂
        (.pushPairSeparator .rightLess) (.pushLowerTick .rightLess)
    | .pushLowerTick order => .pushOutput .tick (.lower order)
    | .pushPairSeparator order => .pushOutput .pairSep (.upper order)
    | .upper .leftLess => .dec₂ .pushRecordEnd
        (.pushUpperTick .leftLess)
    | .upper .equal => .dec₂ .pushRecordEnd
        (.pushUpperTick .equal)
    | .upper .rightLess => .dec₁ .pushRecordEnd
        (.pushUpperTick .rightLess)
    | .pushUpperTick order => .pushOutput .tick (.upper order)
    | .pushRecordEnd => .pushOutput .recordEnd .scan
    | .halt => .halt
    | .invalid => .popInput .halt fun _ => .invalid

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.QueryNormalizer


