-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsShortIso
-- name    : Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsShortIso
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:44:44.881442+00:00
-- url     : https://prove2.me/theorems/f3b5dc45-2f10-416f-a5df-85013a1213fa
-- title:
--   Exists Short Iso
-- statement:
--   Definitions and structural lemmas for Exists Short Iso, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsShortIso.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroNormSqLeMulCovolumeRpow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
namespace GlobalTheory.SW.MinkowskiProductBounds
open Module Submodule
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)}
def IsoRows' {k n : ℕ} (Γ : Matrix (Fin n) (Fin n) E) (T : Matrix (Fin k) (Fin n) E) : Prop :=
  LinearIndependent E (fun i => (T * Γ) i) ∧ T * Γ * ccT T = 0
end GlobalTheory.SW.MinkowskiProductBounds


