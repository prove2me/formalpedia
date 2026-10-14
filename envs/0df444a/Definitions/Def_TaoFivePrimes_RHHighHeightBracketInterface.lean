-- Prove2me | Definitions.Def_TaoFivePrimes_RHHighHeightBracketInterface
-- name    : TaoFivePrimes_RHHighHeightBracketInterface
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-14T10:20:43.316787+00:00
-- url     : https://prove2.me/theorems/a1a8be25-331c-4761-a1dc-b30219769d55
-- title:
--   TaoFivePrimes_RHHighHeightBracketInterface
-- statement:
--   The list interpretation of the typed bracket tree, rational sample points at spacing 1/32, scale 2^64, and the exact proposition that all proposed endpoint boxes contain the normalized zeta values. That containment proposition is defined without any proof or assumption.
-- source:
--   Finite structural sign and order certificates, generated from the native FLINT 3.6.0 Platt FFT/interpolation proposal on [3289999872,3290000000]. Numeric tests are necessary constructor proof fields and use ordinary decide +kernel. No value containment, total zero count or RH conclusion is asserted. Platt method: DOI 10.1090/mcom/3198. The surrounding project preserves attribution to sometik179 (c9908072-d99a-4431-aad8-a72c6352619a) and Gabewhigham. The interpretation uses the Mathlib completed-zeta normalization from the separately accepted normalization theorem.

/- Mathematical interpretation of the ordinary finite bracket certificates.
Value containment remains an explicit unproved property of the proposal. -/
import Definitions.Def_TaoFivePrimes_RHHighHeightBracketTree
import Definitions.Def_TaoFivePrimes_RHHighHeightWindow
set_option autoImplicit false
namespace RHHighHeightBracketInterface
open RHHighHeightBracketData
noncomputable def leaves {l r n : Nat} : Tree l r n → List Bracket
  | .leaf b => [b]
  | .join u v _ => leaves u ++ leaves v
noncomputable def point (k : Nat) : ℝ := 3289999872+(k:ℝ)/32
noncomputable def scale : ℝ := 2^64
noncomputable def proposalContains : Prop :=
  ∀ p ∈ leaves certificate,
    (p.llo:ℝ)/scale ≤ RHHighHeight.normalized (point p.l) ∧
    RHHighHeight.normalized (point p.l) ≤ (p.lhi:ℝ)/scale ∧
    (p.rlo:ℝ)/scale ≤ RHHighHeight.normalized (point p.r) ∧
    RHHighHeight.normalized (point p.r) ≤ (p.rhi:ℝ)/scale
end RHHighHeightBracketInterface
noncomputable def TaoFivePrimes_RHHighHeightBracketInterface : Prop :=
  RHHighHeightBracketInterface.proposalContains


