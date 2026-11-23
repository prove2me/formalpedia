-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_Adele_IntegersLattice
-- name    : GroundTheory_GlobalFields_Adele_IntegersLattice
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:02:32.608792+00:00
-- url     : https://prove2.me/theorems/4d847a99-e943-452a-857f-0079a8818fdf
-- title:
--   Integers Lattice
-- statement:
--   Definitions and structural lemmas for Integers Lattice, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/IntegersLattice.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Global
open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped NumberField.AdeleRing
variable (K : Type*) [Field K]
open scoped Classical in

noncomputable def homeomorphMixedSpace : K∞ ≃ₜ mixedEmbedding.mixedSpace K :=
  (Homeomorph.piEquivPiSubtypeProd (fun v : InfinitePlace K => IsReal v)
      (fun v => v.Completion)).trans
    (Homeomorph.prodCongr
      (Homeomorph.piCongrRight fun v => (isometryEquivRealOfIsReal v.2).toHomeomorph)
      ((Homeomorph.piCongrRight fun v =>
          (isometryEquivComplexOfIsComplex (not_isReal_iff_isComplex.1 v.2)).toHomeomorph).trans
        (Homeomorph.piCongrLeft (Y := fun _ => ℂ)
          (Equiv.subtypeEquivRight fun _ => not_isReal_iff_isComplex))))
variable [NumberField K]
noncomputable def integersInfinite : AddSubgroup K∞ :=
  (algebraMap (𝓞 K) K∞).range.toAddSubgroup
open scoped Classical
noncomputable def fundamentalSetInfinite : Set K∞ :=
  homeomorphMixedSpace K ⁻¹' ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis K)
end GroundTheory.Global


