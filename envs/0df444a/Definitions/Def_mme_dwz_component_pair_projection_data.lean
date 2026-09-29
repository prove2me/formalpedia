-- Prove2me | Definitions.Def_mme_dwz_component_pair_projection_data
-- name    : mme_dwz_component_pair_projection_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-27T10:39:24.638025+00:00
-- url     : https://prove2.me/theorems/be8487bc-8492-4619-bf51-265983b9974a
-- title:
--   Paired allowed-word projection data for Table-2 components
-- statement:
--   For one Table-2 component power, let $P$ be the canonical projection that retains precisely the prescribed allowed $Z$-basis words and acts as the identity on the $X$ and $Y$ modes. This module packages the paired source used by the 121/211 analysis: the Kronecker product of the projected component with its copy under the transposition of the first two tensor modes. It also packages the corresponding unprojected ambient pair, the tensor product of the two canonical inclusions, and the tensor product projector $P\otimes P^{\mathrm{swap}}$.
--
--   The definitions preserve the literal source of the DWZ construction. They do not replace the projected tensor by a larger coupled tensor and therefore do not assert an invalid dimension comparison.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definitions 5.4 and 6.3 and the paired 121/211 treatment in Section 7; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_component_word_projection
import Definitions.Def_mme_six_symmetrized_tau_value

open MME Module TensorProduct

universe u

namespace MME.DWZComponentRestriction

set_option autoImplicit false
set_option warningAsError true

/-- The unprojected pair of equal Table-2 component powers, with the second
factor carrying the transposition of tensor modes zero and one. -/
noncomputable def componentPairAmbient
    (K : Type u) [Field K] (s : Fin 15) (m : ℕ) : TensorObj K 3 :=
  let full := (canonicalComponentBlock K s).kronPow
    (DWZTable2Counts.component s * m)
  TensorObj.kron full (TensorObj.permObj swapFirstTwoPerm full)

/-- The literal paired source used by the 121/211 branch: both component
powers have undergone their Table-2 allowed-word Z projections. -/
noncomputable def componentPairRestricted
    (K : Type u) [Field K] (s : Fin 15) (m : ℕ) : TensorObj K 3 :=
  TensorObj.kron (restrictedComponentPower K s m)
    (TensorObj.permObj swapFirstTwoPerm
      (restrictedComponentPower K s m))

/-- The canonical inclusion of one restricted component power into its
unprojected component power. -/
noncomputable def componentPowerInclusion
    (K : Type u) [Field K] (s : Fin 15) (m : ℕ)
    (i : Fin 3) :
    (restrictedComponentPower K s m).V i →ₗ[K]
      (((canonicalComponentBlock K s).kronPow
        (DWZTable2Counts.component s * m)).V i) :=
  (componentPowerProjectionGrading K s m).classOf i 0 |>.subtype

/-- The canonical endomorphism of one full component power that keeps
exactly the allowed Z-basis words and is the identity on X and Y. -/
noncomputable def componentPowerProject
    (K : Type u) [Field K] (s : Fin 15) (m : ℕ)
    (i : Fin 3) :
    (((canonicalComponentBlock K s).kronPow
        (DWZTable2Counts.component s * m)).V i) →ₗ[K]
      (((canonicalComponentBlock K s).kronPow
        (DWZTable2Counts.component s * m)).V i) := by
  classical
  exact Function.update (fun _ ↦ LinearMap.id) 2
    ((componentPowerZBasis K s m).constr K
      (fun w ↦ if componentWordAllowed s m w then
        componentPowerZBasis K s m w else 0)) i

/-- Modewise tensor product of the two factor inclusions, with the second
factor reindexed by the X/Y transposition. -/
noncomputable def componentPairInclusion
    (K : Type u) [Field K] (s : Fin 15) (m : ℕ)
    (i : Fin 3) :
    (componentPairRestricted K s m).V i →ₗ[K]
      (componentPairAmbient K s m).V i :=
  TensorProduct.map (componentPowerInclusion K s m i)
    (componentPowerInclusion K s m (swapFirstTwoPerm.symm i))

/-- Modewise tensor product of the two allowed-word projectors, with the
second factor reindexed by the X/Y transposition. -/
noncomputable def componentPairProject
    (K : Type u) [Field K] (s : Fin 15) (m : ℕ)
    (i : Fin 3) :
    (componentPairAmbient K s m).V i →ₗ[K]
      (componentPairAmbient K s m).V i :=
  TensorProduct.map (componentPowerProject K s m i)
    (componentPowerProject K s m (swapFirstTwoPerm.symm i))

end MME.DWZComponentRestriction


