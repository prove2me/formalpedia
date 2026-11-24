-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PKHFreeDecomp
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PKHFreeDecomp
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:40.712957+00:00
-- url     : https://prove2.me/theorems/68a8d5d9-b2b5-45d1-b65a-ca10db100a62
-- title:
--   PKHFree Decomp
-- statement:
--   Definitions and structural lemmas for PKHFree Decomp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHFreeDecomp.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KHFreeDecompSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KHFree
noncomputable section
namespace KHFreeDecomp
variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
section Frac
variable {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
def overDen (T : Submonoid (MRingOver S ι)) (t : T) : M →ₗ[S] LocalizedModule T M where
  toFun m := LocalizedModule.mk m t
  map_add' x y := by
    simp only [IsLocalizedModule.mk_eq_mk', IsLocalizedModule.mk'_add]
  map_smul' s m := by
    rw [RingHom.id_apply, LocalizedModule.smul'_mk]
end Frac
end KHFreeDecomp
end
end GroundTheory.Heights₂.Heights.Kleiman


