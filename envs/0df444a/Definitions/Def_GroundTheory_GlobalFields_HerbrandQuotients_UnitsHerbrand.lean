-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_UnitsHerbrand
-- name    : GroundTheory_GlobalFields_HerbrandQuotients_UnitsHerbrand
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T04:16:17.21227+00:00
-- url     : https://prove2.me/theorems/e3f9a9ac-8ed9-4e2d-9892-9f581f8708c5
-- title:
--   Units Herbrand
-- statement:
--   Definitions and structural lemmas for Units Herbrand, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/UnitsHerbrand.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnitsExact
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnitsPerm
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnitsRep
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_LatticeBridge
import Theorems.Thm_GroundTheory_Global_SemiLocal_tensorHomeomorph_apply
import Theorems.Thm_GroundTheory_Global_coeff_permOfFun
import Theorems.Thm_GroundTheory_Global_cycSub_apply
import Theorems.Thm_GroundTheory_Global_normHom_apply
import Theorems.Thm_GroundTheory_Global_piRep_apply
import Theorems.Thm_GroundTheory_Global_unitsRep_apply
import Theorems.Thm_GroundTheory_GroupCoh_restrictEnd_apply
import Theorems.Thm_P2M_GroundTheory_Global_SemiLocal_tensorEquiv__tmul_7bea2d8929c7
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.SemiLocal.tensorHomeomorph_apply
attribute [local simp] GroundTheory.Global.coeff_permOfFun
attribute [local simp] GroundTheory.Global.cycSub_apply
attribute [local simp] GroundTheory.Global.normHom_apply
attribute [local simp] GroundTheory.Global.piRep_apply
attribute [local simp] GroundTheory.GroupCoh.restrictEnd_apply
attribute [local simp] P2M_GroundTheory_Global_SemiLocal_tensorEquiv__tmul_7bea2d8929c7


set_option autoImplicit false
namespace GroundTheory.Global
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem NumberField.InfinitePlace
  MulAction Module
open scoped TensorProduct
noncomputable section
section Log
open scoped Classical
variable (L : Type*) [Field L] [NumberField L]
def fullLog : Additive (𝓞 L)ˣ →+ (InfinitePlace L → ℝ) where
  toFun x w := (w.mult : ℝ) * Real.log (w (algebraMap (𝓞 L) L (x.toMul : 𝓞 L)))
  map_zero' := by
    funext w
    simp
  map_add' x y := by
    funext w
    simp only [toMul_add, Units.val_mul, map_mul, Pi.add_apply]
    rw [Real.log_mul (pos_at_place _ w).ne' (pos_at_place _ w).ne', mul_add]
omit [NumberField L] in
theorem fullLog_apply (x : Additive (𝓞 L)ˣ) (w : InfinitePlace L) :
    fullLog L x w = (w.mult : ℝ) * Real.log (w (algebraMap (𝓞 L) L (x.toMul : 𝓞 L))) :=
  rfl
def logLattice : Submodule ℤ (InfinitePlace L → ℝ) :=
  LinearMap.range (fullLog L).toIntLinearMap
def logProj : (InfinitePlace L → ℝ) →ₗ[ℝ] logSpace L :=
  LinearMap.funLeft ℝ ℝ Subtype.val
theorem logProj_fullLog (x : Additive (𝓞 L)ˣ) : logProj L (fullLog L x) = logEmbedding L x :=
  rfl
theorem fullLog_eq_zero_iff (x : Additive (𝓞 L)ˣ) : fullLog L x = 0 ↔ x.toMul ∈ torsion L := by
  constructor
  · intro h
    rw [← logEmbedding_eq_zero_iff, ofMul_toMul, ← logProj_fullLog, h, map_zero]
  · intro h
    rw [mem_torsion] at h
    funext w
    rw [fullLog_apply, h w, Real.log_one, mul_zero, Pi.zero_apply]
theorem logProj_mem_unitLattice (m : logLattice L) : logProj L m ∈ unitLattice L := by
  obtain ⟨x, hx⟩ := m.2
  rw [← hx]
  exact ⟨x, trivial, rfl⟩
def logLatticeEquiv : logLattice L ≃ₗ[ℤ] unitLattice L :=
  LinearEquiv.ofBijective
    (LinearMap.codRestrict (unitLattice L) ((logProj L).restrictScalars ℤ ∘ₗ (logLattice L).subtype)
      (logProj_mem_unitLattice L)) <| by
    constructor
    · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro m hm
      obtain ⟨x, hx⟩ := m.2
      have h1 : logEmbedding L x = 0 := by
        rw [← logProj_fullLog]
        have := congrArg Subtype.val hm
        simp only [ZeroMemClass.coe_zero] at this
        change logProj L (fullLog L x) = 0
        rw [show fullLog L x = (m : InfinitePlace L → ℝ) from hx]
        exact this
      rw [← ofMul_toMul x, logEmbedding_eq_zero_iff, ← fullLog_eq_zero_iff] at h1
      apply Subtype.ext
      rw [← hx]
      exact h1
    · rintro ⟨y, x, -, rfl⟩
      exact ⟨⟨fullLog L x, x, rfl⟩, rfl⟩
instance : Module.Free ℤ (logLattice L) :=
  have := ZLattice.module_free ℝ (unitLattice L)
  Module.Free.of_equiv (logLatticeEquiv L).symm
instance : Module.Finite ℤ (logLattice L) :=
  have := ZLattice.module_finite ℝ (unitLattice L)
  Module.Finite.equiv (logLatticeEquiv L).symm
end Log
section Galois
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
omit [NumberField K] [NumberField L] in
theorem mult_smul (g : L ≃ₐ[K] L) (w : InfinitePlace L) : (g • w).mult = w.mult := by
  have := isReal_smul_iff (σ := g) (w := w)
  unfold mult
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (this.mp h1) h2
  · exact absurd (this.mpr h2) h1
  · rfl
omit [NumberField K] [NumberField L] in

theorem fullLog_unitsRep (g : L ≃ₐ[K] L) (x : Additive (𝓞 L)ˣ) :
    fullLog L (unitsRep K L g x) = funPermRep ℝ (L ≃ₐ[K] L) (InfinitePlace L) g (fullLog L x) := by
  funext w
  rw [funPermRep_apply, fullLog_apply, fullLog_apply, mult_smul, unitsRep_apply, toMul_ofMul,
    InfinitePlace.smul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_symm]
  rfl
omit [NumberField K] [NumberField L] in
theorem funPermRep_mem_logLattice (g : L ≃ₐ[K] L) {m : InfinitePlace L → ℝ}
    (hm : m ∈ logLattice L) : funPermRep ℝ (L ≃ₐ[K] L) (InfinitePlace L) g m ∈ logLattice L := by
  obtain ⟨x, rfl⟩ := hm
  exact ⟨unitsRep K L g x, fullLog_unitsRep g x⟩
variable (K L) in

def logLatticeRep : Representation ℤ (L ≃ₐ[K] L) (logLattice L) where
  toFun g := ((funPermRep ℝ (L ≃ₐ[K] L) (InfinitePlace L) g).restrictScalars ℤ).restrict
    fun _ hm => funPermRep_mem_logLattice g hm
  map_one' := by
    refine LinearMap.ext fun m => Subtype.ext ?_
    funext w
    change (m : InfinitePlace L → ℝ) ((1 : L ≃ₐ[K] L)⁻¹ • w) = (m : InfinitePlace L → ℝ) w
    rw [inv_one, one_smul]
  map_mul' g h := by
    refine LinearMap.ext fun m => Subtype.ext ?_
    funext w
    change (m : InfinitePlace L → ℝ) ((g * h)⁻¹ • w) = (m : InfinitePlace L → ℝ) (h⁻¹ • g⁻¹ • w)
    rw [mul_inv_rev, mul_smul]
variable [FiniteDimensional K L]
end Galois
end
end GroundTheory.Global


