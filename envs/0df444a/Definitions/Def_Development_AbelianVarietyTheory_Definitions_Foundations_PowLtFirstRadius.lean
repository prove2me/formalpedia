-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_PowLtFirstRadius
-- name    : Development_AbelianVarietyTheory_Definitions_Foundations_PowLtFirstRadius
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:23:37.431403+00:00
-- url     : https://prove2.me/theorems/9b6cb40e-a57a-47a3-ae01-bad77129a813
-- title:
--   Pow Lt First Radius
-- statement:
--   Definitions and structural lemmas for Pow Lt First Radius, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/PowLtFirstRadius.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.Cyc.Model
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc Polynomial
variable {l : ℕ} [Fact l.Prime]
open Polynomial in
variable {l : ℕ} [Fact l.Prime] in
theorem _root_.GlobalTheory.Cyc.Model.isom_gal (g : _root_.Formalism.BasicNotions.Loc.GQ l) :
    Isometry (g : _root_.Formalism.BasicNotions.Loc.Om l →+* _root_.Formalism.BasicNotions.Loc.Om l) := by
  refine AddMonoidHomClass.isometry_of_norm _ fun x => ?_
  change spectralNorm ℚ_[l] (PadicAlgCl l) (g x) = spectralNorm ℚ_[l] (PadicAlgCl l) x
  exact (spectralNorm_eq_of_equiv g x).symm
def extHom (g : GQ l) : PadicComplex l →+* PadicComplex l :=
  UniformSpace.Completion.mapRingHom (g : Om l →+* Om l) (isom_gal g).continuous
open Polynomial in
variable {l : ℕ} [Fact l.Prime] in
theorem continuous_cyc_extHom (g : _root_.Formalism.BasicNotions.Loc.GQ l) :
    Continuous (_root_.GlobalTheory.Cyc.Model.extHom g) :=
  UniformSpace.Completion.continuous_extension
open Polynomial in
variable {l : ℕ} [Fact l.Prime] in
theorem cyc_extHom_coe (g : _root_.Formalism.BasicNotions.Loc.GQ l) (x : _root_.Formalism.BasicNotions.Loc.Om l) :
    _root_.GlobalTheory.Cyc.Model.extHom g (x : PadicComplex l) = ((g x : _root_.Formalism.BasicNotions.Loc.Om l) : PadicComplex l) := by
  simp only [_root_.GlobalTheory.Cyc.Model.extHom, UniformSpace.Completion.mapRingHom]
  rw [UniformSpace.Completion.extensionHom_coe]; rfl
open Polynomial in
variable {l : ℕ} [Fact l.Prime] in
theorem _root_.GlobalTheory.Cyc.Model.extHom_mul (g h : _root_.Formalism.BasicNotions.Loc.GQ l) (y : PadicComplex l) :
    _root_.GlobalTheory.Cyc.Model.extHom (g * h) y =
      _root_.GlobalTheory.Cyc.Model.extHom g (_root_.GlobalTheory.Cyc.Model.extHom h y) := by
  refine UniformSpace.Completion.induction_on y (isClosed_eq (continuous_cyc_extHom _)
    ((continuous_cyc_extHom g).comp (continuous_cyc_extHom h))) fun x => ?_
  rw [cyc_extHom_coe, cyc_extHom_coe, cyc_extHom_coe]; rfl
open Polynomial in
variable {l : ℕ} [Fact l.Prime] in
theorem _root_.GlobalTheory.Cyc.Model.extHom_one (y : PadicComplex l) :
    _root_.GlobalTheory.Cyc.Model.extHom (1 : _root_.Formalism.BasicNotions.Loc.GQ l) y = y := by
  refine UniformSpace.Completion.induction_on y
    (isClosed_eq (continuous_cyc_extHom _) continuous_id) fun x => ?_
  rw [cyc_extHom_coe]; rfl
def actC : GQ l →* (PadicComplex l ≃+* PadicComplex l) where
  toFun g := { extHom g with
    invFun := extHom g⁻¹
    left_inv := fun y => by
      change extHom g⁻¹ (extHom g y) = y
      rw [← extHom_mul, inv_mul_cancel, extHom_one]
    right_inv := fun y => by
      change extHom g (extHom g⁻¹ y) = y
      rw [← extHom_mul, mul_inv_cancel, extHom_one] }
  map_one' := by ext y; exact extHom_one y
  map_mul' g h := by ext y; exact extHom_mul g h y
def chiZ : GQ l →* ℤ_[l]ˣ :=
  (cyclotomicCharacter (Om l) l).comp (MulSemiringAction.toRingAut (GQ l) (Om l))
def chi : GQ l →* ℚ_[l]ˣ :=
  (Units.map (algebraMap ℤ_[l] ℚ_[l]).toMonoidHom).comp chiZ
def base (l : ℕ) [Fact l.Prime] : FinExt l := ⟨⊥, inferInstance⟩
def Utw (σ : GQ l) : Matrix (Fin 1) (Fin 1) (PadicComplex l) := fun _ _ => chiC chi 1 σ
end GlobalTheory.Cyc.Model


