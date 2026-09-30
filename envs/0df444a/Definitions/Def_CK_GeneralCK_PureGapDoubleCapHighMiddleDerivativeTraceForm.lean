-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapDoubleCapHighMiddleDerivativeTraceForm
-- name    : CK_GeneralCK_PureGapDoubleCapHighMiddleDerivativeTraceForm
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T05:04:05.107171+00:00
-- url     : https://prove2.me/theorems/0d8c6612-ff11-40ce-9bae-2e3920b46330
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapDoubleCapHighMiddleDerivativeTraceForm` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapDoubleCapHighMiddleDerivativeTraceForm` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapDoubleCapHighMiddleDerivativeTraceForm` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapDoubleCapHighMiddleDerivativeTraceForm (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapDoubleCapHighMiddleDerivativeTraceForm.lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapHighMiddleDerivativeChecker

-- ===== source module GeneralCK.PureGapDoubleCapHighMiddleDerivativeTraceForm =====
section

/-! Factored trace form for generated exact-rational derivative interval proofs.
The equivalence to the true checked derivative expression is a Lean theorem,
so a generator may use whichever algebraic shape is easiest to replay. -/

namespace GeneralCK
open Certificates.Reflection

noncomputable def doubleCapBridgeDerivativeTraceForm (x : ℝ) : ℝ :=
  let y := doubleCapHighTailY x;
  let c := doubleCapHighTailC x;
  let ay := SmallMean.A y;
  let ac := SmallMean.A c;
  let a2 := SmallMean.A (2 * x);
  let b := biasB c;
  let e := biasE c;
  let l := doubleCapBridgeL x;
  let dy := (1 - y * y) * ay;
  let dc := (1 - c * c) * b;
  let yp := a2 / ay;
  let cp := (e + c * a2) / (l + x * ac);
  -2 * (((1 + y * y) * ay - y) / (dy * dy)) * yp +
    2 * (c * (2 * b - c * c) / (dc * dc)) * cp

theorem doubleCapBridgeDerivativeTraceForm_eq (x : ℝ) :
    doubleCapBridgeDerivativeTraceForm x =
      doubleCapBridgeDerivativeExpression x := by
  simp only [doubleCapBridgeDerivativeTraceForm,
    doubleCapBridgeDerivativeExpression, pow_two]

#print axioms doubleCapBridgeDerivativeTraceForm_eq

end GeneralCK

end


