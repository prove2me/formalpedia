-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceBundleRadicalAway
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceBundleRadicalAway
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:34.147804+00:00
-- url     : https://prove2.me/theorems/a3abcc29-2885-4caf-99b3-17241780d560
-- title:
--   St Slice Bundle Radical Away
-- statement:
--   Definitions and structural lemmas for St Slice Bundle Radical Away, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StSliceBundleRadicalAway.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericFibreRadicalAway
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial Matrix
noncomputable section
def universalSliceIdeal {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (d : ℕ) (q : Fin n → ℂ) :
    Ideal (MvPolynomial (Fin n) (MvPolynomial (Fin d × Fin n) ℂ)) :=
  J.map (MvPolynomial.map (C : ℂ →+* MvPolynomial (Fin d × Fin n) ℂ)) ⊔
    Ideal.span (Set.range fun i : Fin d => ∑ j, C (X (i, j)) * (X j - C (C (q j))))
def SliceBundleRadicalAway.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ), J.IsRadical → ∀ k : Fin n,
    IsRadicalAway (universalSliceIdeal J d q) (X k - C (C (q k)))
end
end GroundTheory.Heights₂.Heights


