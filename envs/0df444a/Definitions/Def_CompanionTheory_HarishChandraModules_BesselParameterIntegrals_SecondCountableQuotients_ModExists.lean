-- Prove2me | Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_ModExists
-- name    : CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_ModExists
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:27:48.672238+00:00
-- url     : https://prove2.me/theorems/6d351c12-a967-4933-8734-1ef33ef21bbe
-- title:
--   Mod Exists
-- statement:
--   Definitions and structural lemmas for Mod Exists, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SecondCountableQuotients/ModExists.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SsetGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure Matrix TopologicalSpace
open scoped ENNReal NNReal Pointwise
noncomputable section
namespace CompanionTheory.D.Upq.ModEx
section Abstract
variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
end Abstract
section Concrete
open PI PI.QuotSetU.UnitaryGroupMassFormula
variable {m : ℕ}
def MG (G : Set (Matrix (Fin m) (Fin m) ℂ)) (_hG : IsMatGroup G) : Type := {x : (Matrix (Fin m) (Fin m) ℂ) // x ∈ G}
variable {G : Set (Matrix (Fin m) (Fin m) ℂ)} {hG : IsMatGroup G}
def MG.mat (x : MG G hG) : (Matrix (Fin m) (Fin m) ℂ) := Subtype.val x
theorem MG.mem (x : MG G hG) : x.mat ∈ G := Subtype.property x
def MG.mk (hG : IsMatGroup G) (x : (Matrix (Fin m) (Fin m) ℂ)) (hx : x ∈ G) : MG G hG := Subtype.mk x hx
@[simp] theorem MG.mat_mk (x : (Matrix (Fin m) (Fin m) ℂ)) (hx : x ∈ G) : (MG.mk hG x hx).mat = x := rfl
theorem MG.ext {x y : MG G hG} (h : x.mat = y.mat) : x = y := Subtype.ext h
instance : Group (MG G hG) where
  mul a b := MG.mk hG (a.mat * b.mat) (hG.2.2.1 _ a.mem _ b.mem)
  one := MG.mk hG 1 hG.2.1
  inv a := MG.mk hG a.mat⁻¹ (hG.2.2.2 _ a.mem).1
  mul_assoc a b c := MG.ext (Matrix.mul_assoc a.mat b.mat c.mat)
  one_mul a := MG.ext (Matrix.one_mul a.mat)
  mul_one a := MG.ext (Matrix.mul_one a.mat)
  inv_mul_cancel a := MG.ext (mul_eq_one_comm.1 (hG.2.2.2 _ a.mem).2)
@[simp] theorem MG.mat_mul (a b : MG G hG) : (a * b).mat = a.mat * b.mat := rfl
@[simp] theorem MG.mat_inv (a : MG G hG) : (a⁻¹).mat = a.mat⁻¹ := rfl
instance : TopologicalSpace (MG G hG) := inferInstanceAs (TopologicalSpace {x : (Matrix (Fin m) (Fin m) ℂ) // x ∈ G})
theorem MG.isClosedEmbedding_mat : Topology.IsClosedEmbedding (MG.mat : MG G hG → (Matrix (Fin m) (Fin m) ℂ)) :=
  hG.1.isClosedEmbedding_subtypeVal
theorem MG.continuous_mat : Continuous (MG.mat : MG G hG → (Matrix (Fin m) (Fin m) ℂ)) :=
  MG.isClosedEmbedding_mat.continuous
theorem MG.continuous_iff {X : Type*} [TopologicalSpace X] {f : X → MG G hG} :
    Continuous f ↔ Continuous (fun x => (f x).mat) :=
  MG.isClosedEmbedding_mat.isInducing.continuous_iff
theorem MG.det_ne_zero (a : MG G hG) : a.mat.det ≠ 0 := by
  intro h
  have := congrArg Matrix.det (hG.2.2.2 _ a.mem).2
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this
instance : IsTopologicalGroup (MG G hG) where
  continuous_mul := MG.continuous_iff.2
    ((MG.continuous_mat.comp continuous_fst).matrix_mul (MG.continuous_mat.comp continuous_snd))
  continuous_inv := by
    refine MG.continuous_iff.2 ?_
    have : (fun a : MG G hG => (a⁻¹).mat) = fun a => (a.mat.det)⁻¹ • a.mat.adjugate := by
      ext1 a
      rw [MG.mat_inv, Matrix.inv_def, Ring.inverse_eq_inv']
    rw [this]
    exact (MG.continuous_mat.matrix_det.inv₀ MG.det_ne_zero).smul
      MG.continuous_mat.matrix_adjugate
instance : LocallyCompactSpace (MG G hG) :=
  haveI : LocallyCompactSpace (Matrix (Fin m) (Fin m) ℂ) := inferInstanceAs (LocallyCompactSpace (Fin m → Fin m → ℂ))
  MG.isClosedEmbedding_mat.locallyCompactSpace
instance : SecondCountableTopology (MG G hG) :=
  haveI : SecondCountableTopology (Matrix (Fin m) (Fin m) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin m → Fin m → ℂ))
  MG.isClosedEmbedding_mat.isEmbedding.secondCountableTopology
instance : MeasurableSpace (MG G hG) := borel _
instance : BorelSpace (MG G hG) := ⟨rfl⟩
def MG.toM (x : MG G hG) : MtM m := Matrix.of.symm x.mat
def conjAut (hG : IsMatGroup G) (c : (Matrix (Fin m) (Fin m) ℂ)) (hc : IsUnit c) (hn : ∀ g, c * g * c⁻¹ ∈ G ↔ g ∈ G) :
    MG G hG ≃ₜ* MG G hG :=
  have h1 : c⁻¹ * c = 1 := Matrix.nonsing_inv_mul c ((Matrix.isUnit_iff_isUnit_det c).1 hc)
  have h2 : c * c⁻¹ = 1 := Matrix.mul_nonsing_inv c ((Matrix.isUnit_iff_isUnit_det c).1 hc)
  have h3 : ∀ g : (Matrix (Fin m) (Fin m) ℂ), c * (c⁻¹ * g * c) * c⁻¹ = g := fun g => by
    rw [show c * (c⁻¹ * g * c) * c⁻¹ = (c * c⁻¹) * g * (c * c⁻¹) by simp only [Matrix.mul_assoc],
      h2, Matrix.one_mul, Matrix.mul_one]
  have h4 : ∀ g : (Matrix (Fin m) (Fin m) ℂ), c⁻¹ * (c * g * c⁻¹) * c = g := fun g => by
    rw [show c⁻¹ * (c * g * c⁻¹) * c = (c⁻¹ * c) * g * (c⁻¹ * c) by simp only [Matrix.mul_assoc],
      h1, Matrix.one_mul, Matrix.mul_one]
  { toFun := fun g => MG.mk hG (c * g.mat * c⁻¹) ((hn _).2 g.mem)
    invFun := fun g => MG.mk hG (c⁻¹ * g.mat * c) ((hn _).1 (by rw [h3]; exact g.mem))
    left_inv := fun g => MG.ext (h4 g.mat)
    right_inv := fun g => MG.ext (h3 g.mat)
    map_mul' := fun a b => MG.ext (by
      change c * (a.mat * b.mat) * c⁻¹ = (c * a.mat * c⁻¹) * (c * b.mat * c⁻¹)
      rw [show (c * a.mat * c⁻¹) * (c * b.mat * c⁻¹) = c * a.mat * (c⁻¹ * c) * b.mat * c⁻¹ by
        simp only [Matrix.mul_assoc], h1]
      simp only [Matrix.mul_assoc, Matrix.one_mul])
    continuous_toFun := MG.continuous_iff.2
      ((continuous_const.matrix_mul MG.continuous_mat).matrix_mul continuous_const)
    continuous_invFun := MG.continuous_iff.2
      ((continuous_const.matrix_mul MG.continuous_mat).matrix_mul continuous_const) }
open Classical in

def modD (hG : IsMatGroup G) (x : (Matrix (Fin m) (Fin m) ℂ)) : ℝ :=
  if hx : x ∈ G then (modularCharacterFun (MG.mk hG x hx) : ℝ) else 1
end Concrete
end CompanionTheory.D.Upq.ModEx
end


