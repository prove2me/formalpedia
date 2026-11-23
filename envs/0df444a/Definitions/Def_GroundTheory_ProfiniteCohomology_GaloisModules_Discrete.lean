-- Prove2me | Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_Discrete
-- name    : GroundTheory_ProfiniteCohomology_GaloisModules_Discrete
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:32:26.735673+00:00
-- url     : https://prove2.me/theorems/68fe4e0e-84bc-4194-9eb0-fe1e0cccdbd2
-- title:
--   Discrete
-- statement:
--   Definitions and structural lemmas for Discrete, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GaloisModules/Discrete.lean

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_DiscreteModules
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_CoeGalRootsOfUnityHomApply
import Theorems.Thm_GroundTheory_ProfCoh_mem_stabilizer
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galRootsOfUnityZ___apply_40a7d6b8f2a7
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galRootsOfUnity___apply_600492b04171
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galUnitsZ___apply_2d4ee74d5783
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galUnits___apply_5e27268f2c21
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.ProfCoh.mem_stabilizer
attribute [local simp] P2M_GroundTheory_ProfCoh_galRootsOfUnityZ___apply_40a7d6b8f2a7
attribute [local simp] P2M_GroundTheory_ProfCoh_galRootsOfUnity___apply_600492b04171
attribute [local simp] P2M_GroundTheory_ProfCoh_galUnitsZ___apply_2d4ee74d5783
attribute [local simp] P2M_GroundTheory_ProfCoh_galUnits___apply_5e27268f2c21


set_option autoImplicit false
namespace GroundTheory.ProfCoh
open IntermediateField
universe w u
variable {K : Type*} {L : Type u} [Field K] [Field L] [Algebra K L]
section Topology
variable (K L)
end Topology
section Open
theorem apply_eq_of_mem_fixingSubgroup_adjoin {x : L} {σ : Gal(L/K)}
    (hσ : σ ∈ (K⟮x⟯).fixingSubgroup) : σ x = x :=
  (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ x (mem_adjoin_simple_self K x)
theorem isOpen_of_forall_apply_eq_mem [Algebra.IsIntegral K L] (H : Subgroup Gal(L/K)) (x : L)
    (h : ∀ σ : Gal(L/K), σ x = x → σ ∈ H) : IsOpen (H : Set Gal(L/K)) := by
  have : FiniteDimensional K K⟮x⟯ :=
    adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  exact Subgroup.isOpen_mono (fun σ hσ => h σ (apply_eq_of_mem_fixingSubgroup_adjoin hσ))
    (fixingSubgroup_isOpen K⟮x⟯)
end Open
section Discrete
variable [Algebra.IsIntegral K L]
instance isDiscreteRep_galAdd : IsDiscreteRep (galAdd K L) :=
  ⟨fun x => isOpen_of_forall_apply_eq_mem _ (x : L) fun _ h => h⟩
instance isDiscreteRep_galAddInt : IsDiscreteRep (galAddInt.{w} K L) :=
  ⟨fun x => isOpen_of_forall_apply_eq_mem _ (x : L) fun _ h => h⟩
instance isDiscreteRep_galAddZ : IsDiscreteRep (galAddZ K L) :=
  ⟨fun x => isOpen_of_forall_apply_eq_mem _ (x : L) fun _ h => h⟩
instance isDiscreteRep_galUnits : IsDiscreteRep (galUnits.{w} K L) :=
  ⟨fun x => isOpen_of_forall_apply_eq_mem _ ((Additive.toMul x : Lˣ) : L) fun σ h => by
    rw [mem_stabilizer, galUnits_ρ_apply]
    change Additive.ofMul (galUnitsHom K L σ (Additive.toMul x)) = x
    rw [← ofMul_toMul x]
    congr 1
    exact Units.ext h⟩
instance isDiscreteRep_galUnitsZ : IsDiscreteRep (galUnitsZ K L) :=
  ⟨fun x => isOpen_of_forall_apply_eq_mem _ ((Additive.toMul x : Lˣ) : L) fun σ h => by
    rw [mem_stabilizer, galUnitsZ_ρ_apply]
    change Additive.ofMul (galUnitsHom K L σ (Additive.toMul x)) = x
    rw [← ofMul_toMul x]
    congr 1
    exact Units.ext h⟩
instance isDiscreteRep_galRootsOfUnity (n : ℕ) : IsDiscreteRep (galRootsOfUnity.{w} K L n) :=
  ⟨fun x => isOpen_of_forall_apply_eq_mem _
    (((Additive.toMul x : rootsOfUnity n L) : Lˣ) : L) fun σ h => by
    rw [mem_stabilizer, galRootsOfUnity_ρ_apply]
    change Additive.ofMul (galRootsOfUnityHom K L n σ (Additive.toMul x)) = x
    rw [← ofMul_toMul x]
    congr 1
    exact Subtype.ext (Units.ext h)⟩
instance isDiscreteRep_galRootsOfUnityZ (n : ℕ) : IsDiscreteRep (galRootsOfUnityZ K L n) :=
  ⟨fun x => isOpen_of_forall_apply_eq_mem _
    (((Additive.toMul x : rootsOfUnity n L) : Lˣ) : L) fun σ h => by
    rw [mem_stabilizer, galRootsOfUnityZ_ρ_apply]
    change Additive.ofMul (galRootsOfUnityHom K L n σ (Additive.toMul x)) = x
    rw [← ofMul_toMul x]
    congr 1
    exact Subtype.ext (Units.ext h)⟩
end Discrete
section Galois
variable (K L) [IsGalois K L]
example : IsDiscreteRep (galUnits.{u} K L) := inferInstance
example (n : ℕ) : IsDiscreteRep (galRootsOfUnity.{u} K L n) := inferInstance
example : IsDiscreteRep (galAdd K L) := inferInstance
end Galois
end GroundTheory.ProfCoh


