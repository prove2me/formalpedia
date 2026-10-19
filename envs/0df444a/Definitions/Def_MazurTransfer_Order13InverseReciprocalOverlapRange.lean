-- Prove2me | Definitions.Def_MazurTransfer_Order13InverseReciprocalOverlapRange
-- name    : MazurTransfer_Order13InverseReciprocalOverlapRange
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T06:13:15.272223+00:00
-- url     : https://prove2.me/theorems/4e177a6e-6686-47ba-8ee9-7d0505f30b44
-- title:
--   The inverse reciprocal chart parameter-open comparison
-- statement:
--   Let $R$ be a noetherian commutative integral domain with $104$ invertible. In the actual positive reciprocal patch, the basic open of the inverse parameter $s$ equals the basic open of the reciprocal coordinate $z$. The specified ring map from the actual inverse finite algebra sends its parameter to $s$, and its spectral map is the retained reciprocal chart inclusion. Consequently the inverse image of the ordinary finite chart is exactly $D(z)$. These constructors and structural identities specify the actual inverse-atlas overlap.
-- source:
--   MazurTheorem, Apache-2.0, Vas and contributors. Six original declarations from Order13InverseParameterReciprocalOverlapRange.lean. The ring-map constructor body is unchanged. One proof additionally unfolds the kernel-equal public s alias to expose its original product formula; all other proof bodies are unchanged. All original closed types and the original ring-map value are compared in the kernel. Native, strict and full frontend checks pass with standard axioms only. Named downstream consumer: global inverse finite-chart gluing and actual integral FiniteMapData.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the reciprocal finite chart meets the ordinary finite chart
exactly in the original reciprocal z-open locus.
Named downstream consumer: the inverse finite atlas comparison with the
actual original curve. This does not assume a global comparison.
-/
import Definitions.Def_MazurTransfer_Order13InverseFiniteChartCurveMaps

noncomputable section
universe u
namespace MazurTransfer.Order13InverseParameterFiniteAlgebra
open CategoryTheory AlgebraicGeometry
variable (R : Type u) [CommRing R]

open Order13InverseParameterPositiveReciprocalPatch in
theorem reciprocal_patch_parameter_basicOpen :
    PrimeSpectrum.basicOpen (s R) = PrimeSpectrum.basicOpen (z R) := by
  have he : PrimeSpectrum.basicOpen (F R) ⊓ PrimeSpectrum.basicOpen (r R) = ⊤ := by
    rw [← PrimeSpectrum.basicOpen_mul, F_mul_r, PrimeSpectrum.basicOpen_one]
  have hr : PrimeSpectrum.basicOpen (r R) = ⊤ :=
    top_unique (he.symm.le.trans inf_le_right)
  rw [s, InverseParameterChartComparisonLibrary.MazurTransfer.Order13InverseParameterPositiveReciprocalPatch.s,
    PrimeSpectrum.basicOpen_mul, PrimeSpectrum.basicOpen_pow _ 3 (by norm_num), hr, inf_top_eq]

variable [IsDomain R] [IsNoetherianRing R]

def reciprocalFiniteChartRingHom (h104 : IsUnit (104 : R)) :
    candidateAlgebra R →+* Order13InverseParameterPositiveReciprocalPatch.PatchRing R :=
  (recoveredReciprocalPatchEquiv R h104).symm.toRingHom.comp
    (algebraMap (candidateAlgebra R) (infinityLocalization R))

theorem reciprocalFiniteChartRingHom_s (h104 : IsUnit (104 : R)) :
    reciprocalFiniteChartRingHom R h104 (sElement R) =
      Order13InverseParameterPositiveReciprocalPatch.s R := by
  change (recoveredReciprocalPatchEquiv R h104).symm (infinityS R) = _
  apply (recoveredReciprocalPatchEquiv R h104).injective
  rw [AlgEquiv.apply_symm_apply, recoveredReciprocalPatchEquiv_s]

theorem reciprocalFiniteChart_parameter_preimage (h104 : IsUnit (104 : R)) :
    TopologicalSpace.Opens.comap
      ⟨PrimeSpectrum.comap (reciprocalFiniteChartRingHom R h104),
        PrimeSpectrum.continuous_comap (reciprocalFiniteChartRingHom R h104)⟩
      (PrimeSpectrum.basicOpen (sElement R)) =
        PrimeSpectrum.basicOpen (Order13InverseParameterPositiveReciprocalPatch.z R) := by
  rw [PrimeSpectrum.comap_basicOpen, reciprocalFiniteChartRingHom_s,
    reciprocal_patch_parameter_basicOpen]

theorem reciprocalFiniteChartRingHom_Spec (h104 : IsUnit (104 : R)) :
    Spec.map (CommRingCat.ofHom (reciprocalFiniteChartRingHom R h104)) =
      reciprocalToFiniteAffineScheme R h104 := by
  rw [reciprocalToFiniteAffineScheme, reciprocalFiniteChartIso, candidateInfinityChartMap]
  change Spec.map (CommRingCat.ofHom (reciprocalFiniteChartRingHom R h104)) =
    Spec.map (CommRingCat.ofHom (recoveredReciprocalPatchEquiv R h104).symm.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (candidateAlgebra R) (infinityLocalization R)))
  rw [← Spec.map_comp]
  rfl

theorem reciprocalToFiniteAffineScheme_parameter_preimage (h104 : IsUnit (104 : R)) :
    (reciprocalToFiniteAffineScheme R h104) ⁻¹ᵁ (PrimeSpectrum.basicOpen (sElement R)) =
      PrimeSpectrum.basicOpen (Order13InverseParameterPositiveReciprocalPatch.z R) := by
  rw [← reciprocalFiniteChartRingHom_Spec]
  exact reciprocalFiniteChart_parameter_preimage R h104

end MazurTransfer.Order13InverseParameterFiniteAlgebra
#print axioms MazurTransfer.Order13InverseParameterFiniteAlgebra.reciprocal_patch_parameter_basicOpen
#print axioms MazurTransfer.Order13InverseParameterFiniteAlgebra.reciprocalToFiniteAffineScheme_parameter_preimage


