-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_PolyChartSmoothFractionLift
-- name    : Development_AbelianVarietyTheory_Proofs_GenericRegularity_PolyChartSmoothFractionLift
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:29:34.460504+00:00
-- url     : https://prove2.me/theorems/e13d6872-89be-42dc-a6ad-8a4013b72518
-- title:
--   Poly Chart Smooth Fraction Lift
-- statement:
--   Definitions and structural lemmas for Poly Chart Smooth Fraction Lift, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/PolyChartSmoothFractionLift.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory
open MvPolynomial
section PolyChart
variable {K F₀ : Type} (V : Type) [Field K] [Field F₀] [Algebra K F₀] (R₀ : Subalgebra K F₀)
noncomputable def polyChartHom :
    MvPolynomial V R₀ →ₐ[K] FractionRing (MvPolynomial V F₀) :=
  (IsScalarTower.toAlgHom K (MvPolynomial V F₀) (FractionRing (MvPolynomial V F₀))).comp
    (MvPolynomial.mapAlgHom R₀.val)
end PolyChart
end GlobalTheory


