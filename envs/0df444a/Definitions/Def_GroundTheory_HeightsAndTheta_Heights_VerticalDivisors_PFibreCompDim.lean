-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PFibreCompDim
-- name    : GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PFibreCompDim
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T01:52:38.852421+00:00
-- url     : https://prove2.me/theorems/f047d62e-68a9-4585-a22b-fce3e7ae3d4d
-- title:
--   PFibre Comp Dim
-- statement:
--   Definitions and structural lemmas for PFibre Comp Dim, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PFibreCompDim.lean

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsFibreCompDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsFibreCut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial IsDedekindDomain
section Residue
variable {O : Type} [CommRing O] [IsDedekindDomain O] {n : ℕ} (v : HeightOneSpectrum O)
  (W : Ideal (MvPolynomial (Fin n) O))
noncomputable def quotientResidueEquiv (hW : Ideal.map (C : O →+* MvPolynomial (Fin n) O) v.asIdeal ≤ W) :
    (MvPolynomial (Fin n) O ⧸ W) ≃+*
      (MvPolynomial (Fin n) v.asIdeal.ResidueField ⧸
        W.map (MvPolynomial.map (algebraMap O v.asIdeal.ResidueField))) :=
  let φ : MvPolynomial (Fin n) O →+* MvPolynomial (Fin n) v.asIdeal.ResidueField :=
    MvPolynomial.map (algebraMap O v.asIdeal.ResidueField)
  have hφ : Function.Surjective φ :=
    MvPolynomial.map_surjective _ (Ideal.algebraMap_residueField_surjective _)
  have hψ : Function.Surjective ((Ideal.Quotient.mk (W.map φ)).comp φ) :=
    Ideal.Quotient.mk_surjective.comp hφ
  have hker : RingHom.ker ((Ideal.Quotient.mk (W.map φ)).comp φ) = W := by
    have : RingHom.ker φ = Ideal.map C v.asIdeal := by
      rw [MvPolynomial.ker_map, Ideal.ker_algebraMap_residueField]
    rw [← RingHom.comap_ker, Ideal.mk_ker, Ideal.comap_map_of_surjective _ hφ,
      ← RingHom.ker_eq_comap_bot, this, sup_eq_left.mpr hW]
  (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hψ)
end Residue
end GroundTheory.Heights₂.Heights.Vertical


