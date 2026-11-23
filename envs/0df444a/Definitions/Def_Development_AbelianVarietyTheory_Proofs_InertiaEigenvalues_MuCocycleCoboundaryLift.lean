-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MuCocycleCoboundaryLift
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MuCocycleCoboundaryLift
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:50:09.021832+00:00
-- url     : https://prove2.me/theorems/7756ae24-fe28-44d6-a195-9051844a9068
-- title:
--   Mu Cocycle Coboundary Lift
-- statement:
--   Definitions and structural lemmas for Mu Cocycle Coboundary Lift, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MuCocycleCoboundaryLift.lean

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__PoitouTateNineTermTransgressionZeroApply_433ca0b5d42a991a
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__ContinuousCycMod_abd9886c27059cc0
import Definitions.Def_Formalism_GaloisCohomology_Statement
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply


set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
namespace GlobalTheory.MuTowerInj
section Abstract
variable {Γ : Type} [Group Γ] [TopologicalSpace Γ]
  {R₁ R₂ R₃ M₁ M₂ M₃ : Type} [CommRing R₁] [CommRing R₂] [CommRing R₃]
  [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
  [Module R₁ M₁] [Module R₂ M₂] [Module R₃ M₃]
  [TopologicalSpace M₁] [TopologicalSpace M₂] [TopologicalSpace M₃]
  [DiscreteTopology M₁] [DiscreteTopology M₂] [DiscreteTopology M₃]
def twoCocycleMapOfEquivariantAdd (ρ₁ : Representation R₁ Γ M₁) (ρ₂ : Representation R₂ Γ M₂) (u : M₁ →+ M₂)
    (hu : ∀ g m, u (ρ₁ g m) = ρ₂ g (u m)) : Z2 ρ₁ →+ Z2 ρ₂ where
  toFun f := ⟨u ∘ f.1, (continuous_of_discreteTopology (f := u)).comp f.2.1, fun g h k => by
    simp only [Function.comp_apply, ← hu, ← map_sub, ← map_add, f.2.2 g h k, map_zero]⟩
  map_zero' := Subtype.ext (funext fun _ => map_zero u)
  map_add' f f' := Subtype.ext (funext fun _ => map_add u _ _)
def secondCohomologyMapOfEquivariantAdd (ρ₁ : Representation R₁ Γ M₁) (ρ₂ : Representation R₂ Γ M₂) (u : M₁ →+ M₂)
    (hu : ∀ g m, u (ρ₁ g m) = ρ₂ g (u m)) : H2 ρ₁ →+ H2 ρ₂ :=
  QuotientAddGroup.map ((B2 ρ₁).comap (Z2 ρ₁).subtype).toAddSubgroup
    ((B2 ρ₂).comap (Z2 ρ₂).subtype).toAddSubgroup (twoCocycleMapOfEquivariantAdd ρ₁ ρ₂ u hu) fun f hf => by
    obtain ⟨c, hc, hcf⟩ := (separated_dvr_second_cohomology_mem ρ₁ _).1 hf
    refine (separated_dvr_second_cohomology_mem ρ₂ _).2 ⟨u ∘ c, (continuous_of_discreteTopology (f := u)).comp hc, ?_⟩
    funext p
    have e := congrFun hcf p
    simp only [Submodule.coe_subtype] at e
    change _ = u (f.1 p)
    rw [← e]
    simp [d1, hu]
end Abstract
section Cyclic
variable (l : ℕ) [Fact l.Prime] (n : ℕ)
omit [Fact l.Prime] in
theorem pow_mul_val (x : ℕ) :
    ((l ^ n * (x : ZMod (l ^ 1)).val : ℕ) : ZMod (l ^ (n + 1))) = ((l ^ n * x : ℕ) : _) := by
  rw [ZMod.val_natCast, pow_one]
  conv_rhs => rw [← Nat.mod_add_div x l]
  rw [mul_add, Nat.cast_add, ← mul_assoc, ← pow_succ, Nat.cast_mul (l ^ (n + 1)), ZMod.natCast_self,
    zero_mul, add_zero]
def iota : ZMod (l ^ 1) →+ ZMod (l ^ (n + 1)) :=
  AddMonoidHom.mk' (fun b => ((l ^ n * b.val : ℕ) : ZMod (l ^ (n + 1)))) fun a b => by
    obtain ⟨x, rfl⟩ := ZMod.natCast_zmod_surjective a
    obtain ⟨y, rfl⟩ := ZMod.natCast_zmod_surjective b
    rw [← Nat.cast_add, pow_mul_val, pow_mul_val, pow_mul_val, mul_add, Nat.cast_add]
def red : ZMod (l ^ (n + 1)) →+* ZMod (l ^ n) :=
  ZMod.castHom (pow_dvd_pow l (Nat.le_succ n)) (ZMod (l ^ n))
end Cyclic
end GlobalTheory.MuTowerInj


