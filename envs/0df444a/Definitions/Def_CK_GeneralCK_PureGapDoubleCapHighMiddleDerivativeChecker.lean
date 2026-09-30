-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapDoubleCapHighMiddleDerivativeChecker
-- name    : CK_GeneralCK_PureGapDoubleCapHighMiddleDerivativeChecker
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:58:34.066354+00:00
-- url     : https://prove2.me/theorems/cee07bc5-3002-467d-a8c1-7cf8fd258e0a
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapDoubleCapHighMiddleDerivativeChecker` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapDoubleCapHighMiddleDerivativeChecker` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapDoubleCapHighMiddleDerivativeChecker` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapDoubleCapHighMiddleDerivativeChecker (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapDoubleCapHighMiddleDerivativeChecker.lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapHighMiddleDerivativeCoverage
import Definitions.Def_CK_GeneralCK_ReflectionContactInverse

-- ===== source module GeneralCK.PureGapDoubleCapHighMiddleDerivativeChecker =====
section

/-! Sound finite-cell interface for the true high-cap slope derivative.
The explicit derivative identity and 256 cell certificates are hypotheses
until they are separately proved; no external numerical output is trusted. -/

namespace GeneralCK
open Certificates.Reflection

noncomputable def doubleCapBridgeL (x : ℝ) : ℝ :=
  Real.log 2 * doubleCapHighTailFloor x

noncomputable def doubleCapBridgeSlope (x : ℝ) : ℝ :=
  doubleCapSlopeBiasExpression (doubleCapHighTailY x)
    (doubleCapHighTailC x)

noncomputable def doubleCapBridgeDerivativeExpression (x : ℝ) : ℝ :=
  let y := doubleCapHighTailY x;
  let c := doubleCapHighTailC x;
  let ay := SmallMean.A y;
  let ac := SmallMean.A c;
  let a2x := SmallMean.A (2 * x);
  let b := biasB c;
  let e := biasE c;
  let l := doubleCapBridgeL x;
  let dy := (1 - y ^ 2) * ay;
  let dc := (1 - c ^ 2) * b;
  (-2 : ℝ) * (((1 + y ^ 2) * ay - y) / dy ^ 2) * (a2x / ay) +
    2 * (c * (2 * b - c ^ 2) / dc ^ 2) *
      ((e + c * a2x) / (l + x * ac))

/-- Conditional soundness of the exact derivative identity plus complete
256-cell finite certificate replay. The two premises are formal Lean proof
obligations; the external interval probe is not used here. -/
theorem doubleCapBridge_true_deriv_pos_of_256_cells
    (hFormula : ∀ x : ℝ, x ∈ Set.Icc (1 / 8 : ℝ) (1 / 5 : ℝ) →
      HasDerivAt doubleCapBridgeSlope
        (doubleCapBridgeDerivativeExpression x) x)
    (hCells : ∀ i : Fin 256,
      DoubleCapBridgeDerivativeCellCertificate i
        doubleCapBridgeDerivativeExpression)
    {x : ℝ} (hx : x ∈ Set.Icc (1 / 8 : ℝ) (1 / 5 : ℝ)) :
    0 < deriv doubleCapBridgeSlope x := by
  rw [(hFormula x hx).deriv]
  exact doubleCapBridge_derivative_pos_of_256_cells hCells hx

#print axioms doubleCapBridge_true_deriv_pos_of_256_cells

end GeneralCK

end


