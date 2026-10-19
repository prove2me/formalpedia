-- Prove2me | Definitions.Def_TaoFivePrimes_RHBatch02HeightBracketInterface
-- name    : TaoFivePrimes_RHBatch02HeightBracketInterface
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-16T18:28:22.944929+00:00
-- url     : https://prove2.me/theorems/0f5db52b-f3a5-41ca-93fa-abcabdd0f208
-- title:
--   TaoFivePrimes_RHBatch02HeightBracketInterface
-- statement:
--   The list interpretation of the typed bracket tree, rational sample points at spacing 1/32, scale 2^64, and the exact proposition that all proposed endpoint boxes contain the normalized zeta values. That containment proposition is defined without any proof or assumption.
-- source:
--   Finite structural sign and order certificates, generated from the native FLINT 3.6.0 Platt FFT/interpolation proposal on [3289999616,3289999744]. Numeric tests are necessary constructor proof fields and use ordinary decide +kernel. No value containment, total zero count or RH conclusion is asserted. Platt method: DOI 10.1090/mcom/3198. The surrounding project preserves attribution to sometik179 (c9908072-d99a-4431-aad8-a72c6352619a) and Gabewhigham. The interpretation uses the Mathlib completed-zeta normalization from the separately accepted normalization theorem.

/- Mathematical interpretation of the ordinary finite bracket certificates.
Value containment remains an explicit unproved property of the proposal. -/
import Definitions.Def_TaoFivePrimes_RHBatch02HeightBracketTree
import Definitions.Def_TaoFivePrimes_RHHighHeightWindow
set_option autoImplicit false
namespace RHBatch02HeightBracketInterface
open RHBatch02HeightBracketData
noncomputable def leaves {l r n : Nat} : Tree l r n → List Bracket
  | .leaf b => [b]
  | .join u v _ => leaves u ++ leaves v
noncomputable def point (k : Nat) : ℝ := 3289999616+(k:ℝ)/32
noncomputable def scale : ℝ := 2^64
noncomputable def proposalContains : Prop :=
  ∀ p ∈ leaves certificate,
    (p.llo:ℝ)/scale ≤ RHHighHeight.normalized (point p.l) ∧
    RHHighHeight.normalized (point p.l) ≤ (p.lhi:ℝ)/scale ∧
    (p.rlo:ℝ)/scale ≤ RHHighHeight.normalized (point p.r) ∧
    RHHighHeight.normalized (point p.r) ≤ (p.rhi:ℝ)/scale
end RHBatch02HeightBracketInterface
noncomputable def TaoFivePrimes_RHBatch02HeightBracketInterface : Prop :=
  RHBatch02HeightBracketInterface.proposalContains


