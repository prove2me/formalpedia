-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussUniqueness_GaussUniquenessStatements_GaussUniquenessLemmas_KernelLineArguments_NotInjOfTrdeg
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussUniqueness_GaussUniquenessStatements_GaussUniquenessLemmas_KernelLineArguments_NotInjOfTrdeg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:01:06.84251+00:00
-- url     : https://prove2.me/theorems/36aeeb28-5e63-4aae-bc8d-2fe0c97142f6
-- title:
--   Not Inj Of Trdeg
-- statement:
--   Definitions and structural lemmas for Not Inj Of Trdeg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/GaussUniqueness/GaussUniquenessStatements/GaussUniquenessLemmas/KernelLineArguments/NotInjOfTrdeg.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussUniqueness_GaussUniquenessStatements_GaussUniquenessLemmas_KernelLineArguments_ImgRSuccAbove
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GaussValuationUniqueness
open ReciprocityTheory.ChartRestriction.G.T0
section Tr
variable {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω] {D N : ℕ}
  (v : AddValuation Ω (WithTop ℤ))
noncomputable def gK (hv : IsTrivOn K v) :
    K →+* IsLocalRing.ResidueField ((vRing v).comap (algebraMap K Ω)) :=
  (IsLocalRing.residue _).comp ((RingHom.id K).codRestrict ((vRing v).comap (algebraMap K Ω))
    (fun x => by rw [ValuationSubring.mem_comap]; exact alg_mem v hv x))
end Tr
end GaussValuationUniqueness


