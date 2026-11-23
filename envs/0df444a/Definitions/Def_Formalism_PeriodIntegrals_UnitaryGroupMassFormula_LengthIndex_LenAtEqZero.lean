-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LengthIndex_LenAtEqZero
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LengthIndex_LenAtEqZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:37.165165+00:00
-- url     : https://prove2.me/theorems/4b967d2d-4fea-420b-944c-97f6534ec83b
-- title:
--   Len At Eq Zero
-- statement:
--   Definitions and structural lemmas for Len At Eq Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LengthIndex/LenAtEqZero.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_IdxCalc
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


set_option autoImplicit false
noncomputable section
namespace PI.Dv.ProjAW
open NumberField IsDedekindDomain Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K] [StarRing K]
section Gen
variable (A : HLat K)
def toQ (f : Module.End K A.V) :
    A.L →ₗ[𝓞 K] (↥(imgE A f A.L) ⧸ (cutE A f A.L).comap (imgE A f A.L).subtype) :=
  Submodule.mkQ _ ∘ₗ (f.restrictScalars (𝓞 K)).submoduleMap A.L
lemma toQ_surj (f : Module.End K A.V) : Function.Surjective (toQ A f) :=
  (Submodule.mkQ_surjective _).comp (LinearMap.submoduleMap_surjective _ _)
lemma mem_ker_toQ (f : Module.End K A.V) (a : A.L) :
    a ∈ LinearMap.ker (toQ A f) ↔ f a ∈ A.L := by
  rw [LinearMap.mem_ker]
  change Submodule.Quotient.mk _ = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  change f a ∈ A.L ∧ f a ∈ LinearMap.range f ↔ f a ∈ A.L
  exact ⟨fun h => h.1, fun h => ⟨h, a, rfl⟩⟩
lemma ker_toQ_eq (e : Module.End K A.V) :
    LinearMap.ker (toQ A e) = LinearMap.ker (toQ A (1 - e)) := by
  ext a
  rw [mem_ker_toQ, mem_ker_toQ]
  have h : (1 - e) (a : A.V) = (a : A.V) - e a := by simp
  rw [h]
  constructor
  · intro h1; exact A.L.sub_mem a.2 h1
  · intro h1
    have := A.L.sub_mem a.2 h1
    simpa using this
def quotEquiv (e : Module.End K A.V) :
    (↥(imgE A e A.L) ⧸ (cutE A e A.L).comap (imgE A e A.L).subtype) ≃ₗ[𝓞 K]
    (↥(imgE A (1 - e) A.L) ⧸ (cutE A (1 - e) A.L).comap (imgE A (1 - e) A.L).subtype) :=
  ((toQ A e).quotKerEquivOfSurjective (toQ_surj A e)).symm.trans
    ((Submodule.quotEquivOfEq _ _ (ker_toQ_eq A e)).trans
      ((toQ A (1 - e)).quotKerEquivOfSurjective (toQ_surj A (1 - e))))
end Gen
section Len
variable {V W : Type} [AddCommGroup V] [Module (𝓞 K) V] [AddCommGroup W] [Module (𝓞 K) W]
end Len
end PI.Dv.ProjAW


