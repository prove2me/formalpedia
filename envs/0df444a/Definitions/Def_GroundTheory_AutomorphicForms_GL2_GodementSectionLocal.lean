-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_GL2_GodementSectionLocal
-- name    : GroundTheory_AutomorphicForms_GL2_GodementSectionLocal
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T10:29:15.762796+00:00
-- url     : https://prove2.me/theorems/fff025c9-c049-4654-b482-f078d7d02e25
-- title:
--   Godement Section Local
-- statement:
--   Definitions and structural lemmas for Godement Section Local, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GodementSectionLocal.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZeta
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_congruenceSubgroup_antitone
import Theorems.Thm_GroundTheory_LocalField_coe_homeomorphOfIsAlgebraic
import Theorems.Thm_GroundTheory_LocalField_modulus_eq_zero
import Theorems.Thm_GroundTheory_LocalField_modulus_one
import Theorems.Thm_GroundTheory_LocalField_modulus_zero
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_selfDual_apply
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.coe_homeomorphOfIsAlgebraic
attribute [local simp] GroundTheory.LocalField.modulus_eq_zero
attribute [local simp] GroundTheory.LocalField.modulus_one
attribute [local simp] GroundTheory.LocalField.modulus_zero
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.selfDual_apply
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply


set_option autoImplicit false
open MeasureTheory Matrix Filter Topology
open scoped NNReal ValuativeRel
namespace GroundTheory.Automorphic.GodementSectionLocal
open GroundTheory.LocalField
noncomputable section
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable (F) in

def schwartzBruhat2 : Submodule ℂ ((Fin 2 → F) → ℂ) where
  carrier := {Φ | IsLocallyConstant Φ ∧ HasCompactSupport Φ}
  add_mem' hf hg := ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  zero_mem' := ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩
  smul_mem' c _ hf := ⟨hf.1.comp (c • ·), hf.2.smul_left (f := fun _ ↦ c)⟩
def slice (Φ : (Fin 2 → F) → ℂ) (g : GL (Fin 2) F) : F → ℂ :=
  fun t ↦ Φ (![0, t] ᵥ* (g : Matrix (Fin 2) (Fin 2) F))
def modPow (x : F) (s : ℂ) : ℂ := ((modulus x : ℝ) : ℂ) ^ s
def borelElt (a d : Fˣ) (x : F) : GL (Fin 2) F where
  val := !![(a : F), x; 0, (d : F)]
  inv := !![((a⁻¹ : Fˣ) : F), -(x * ((a⁻¹ : Fˣ) : F) * ((d⁻¹ : Fˣ) : F)); 0, ((d⁻¹ : Fˣ) : F)]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Units.val_inv_eq_inv_val]
    all_goals field_simp
    all_goals ring
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Units.val_inv_eq_inv_val]
    all_goals field_simp
    all_goals ring
abbrev detU (g : GL (Fin 2) F) : Fˣ := Matrix.GeneralLinearGroup.det g
def principalSeries (χ₁ χ₂ : Fˣ →* ℂˣ) (s : ℂ) : Submodule ℂ (GL (Fin 2) F → ℂ) where
  carrier := {f | ∀ (a d : Fˣ) (x : F) (g : GL (Fin 2) F),
    f (borelElt a d x * g) =
      (χ₁ a : ℂ) * (χ₂ d : ℂ) * modPow (a : F) s * modPow (d : F) (-s) * f g}
  add_mem' {f₁ f₂} h₁ h₂ a d x g := by
    simp only [Pi.add_apply, h₁ a d x g, h₂ a d x g]; ring
  zero_mem' a d x g := by simp
  smul_mem' c f h a d x g := by
    simp only [Pi.smul_apply, smul_eq_mul, h a d x g]; ring
def IsSmooth (f : GL (Fin 2) F → ℂ) : Prop :=
  ∃ m : ℕ, ∀ g, ∀ u ∈ GLnLocal.congruenceSubgroup F 2 m, f (g * u) = f g
variable [MeasurableSpace F] [BorelSpace F]
def localSection (χ₁ χ₂ : Fˣ →* ℂˣ) (s : ℂ) (Φ : (Fin 2 → F) → ℂ) (g : GL (Fin 2) F) : ℂ :=
  (χ₁ (detU g) : ℂ) * modPow (detU g : F) s * localZeta (slice Φ g) (χ₁ * χ₂⁻¹) (2 * s)
def rightTranslate (h : GL (Fin 2) F) (Φ : (Fin 2 → F) → ℂ) : (Fin 2 → F) → ℂ :=
  fun x ↦ Φ (x ᵥ* (h : Matrix (Fin 2) (Fin 2) F))
variable (F) in

def box (n : ℤ) : AddSubgroup (Fin 2 → F) := AddSubgroup.pi Set.univ fun _ ↦ valBall F n
variable (F) in

def shell : Set (Fin 2 → F) := (box F 0 : Set (Fin 2 → F)) \ box F 1
variable (F) in

def shellAt (m : ℤ) : Set (Fin 2 → F) := (box F m : Set (Fin 2 → F)) \ box F (m + 1)
abbrev unifPow (k : ℤ) : Fˣ := unifUnit F ^ k
variable (F) in

def boxInd (n : ℤ) : (Fin 2 → F) → ℂ := (box F n : Set (Fin 2 → F)).indicator 1
def shellPiece (Φ : (Fin 2 → F) → ℂ) (m : ℤ) : (Fin 2 → F) → ℂ :=
  (shell F).indicator fun y ↦ Φ (((unifPow m : Fˣ) : F) • y)
variable (F) in

def shellInd : (Fin 2 → F) → ℂ := (shell F).indicator 1
omit [MeasurableSpace F] [BorelSpace F] in
theorem IsSmooth.mono {f : GL (Fin 2) F → ℂ} {m : ℕ}
    (hf : ∀ g, ∀ u ∈ GLnLocal.congruenceSubgroup F 2 m, f (g * u) = f g) {m' : ℕ} (h : m ≤ m') :
    ∀ g, ∀ u ∈ GLnLocal.congruenceSubgroup F 2 m', f (g * u) = f g :=
  fun g u hu ↦ hf g u (GLnLocal.congruenceSubgroup_antitone F 2 h hu)
def smoothPrincipalSeries (χ₁ χ₂ : Fˣ →* ℂˣ) (s : ℂ) : Submodule ℂ (GL (Fin 2) F → ℂ) where
  carrier := {f | f ∈ principalSeries χ₁ χ₂ s ∧ IsSmooth f}
  add_mem' {f₁ f₂} h₁ h₂ := by
    refine ⟨add_mem h₁.1 h₂.1, ?_⟩
    obtain ⟨m₁, hm₁⟩ := h₁.2
    obtain ⟨m₂, hm₂⟩ := h₂.2
    refine ⟨max m₁ m₂, fun g u hu ↦ ?_⟩
    simp only [Pi.add_apply, IsSmooth.mono hm₁ (le_max_left _ _) g u hu,
      IsSmooth.mono hm₂ (le_max_right _ _) g u hu]
  zero_mem' := ⟨zero_mem _, 0, fun _ _ _ ↦ rfl⟩
  smul_mem' c f h := by
    refine ⟨Submodule.smul_mem _ c h.1, ?_⟩
    obtain ⟨m, hm⟩ := h.2
    exact ⟨m, fun g u hu ↦ by simp only [Pi.smul_apply, hm g u hu]⟩
end
end GroundTheory.Automorphic.GodementSectionLocal


