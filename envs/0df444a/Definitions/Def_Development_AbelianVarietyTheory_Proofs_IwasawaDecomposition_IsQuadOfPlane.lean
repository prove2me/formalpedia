-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsQuadOfPlane
-- name    : Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsQuadOfPlane
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:47:20.260283+00:00
-- url     : https://prove2.me/theorems/470f7c7e-ef3c-4b4e-86a6-3f3466946a9f
-- title:
--   Is Quad Of Plane
-- statement:
--   Definitions and structural lemmas for Is Quad Of Plane, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsQuadOfPlane.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped ContDiff Real
namespace GlobalTheory.Mem.Lift
section General
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
def dH (ρ : V → B →L[ℂ] B) (v : V) (f : B) : B := fderiv ℝ (fun u => ρ u f) 0 v
def quad (ρ : V → B →L[ℂ] B) {κ : Type} [Fintype κ] (c : κ → ℂ) (p q : κ → V) (f : B) : B :=
  ∑ i, c i • dH ρ (p i) (dH ρ (q i) f)
def IsQuadOf (om : V → V → ℝ) (X : V → V) {κ : Type} [Fintype κ] (c : κ → ℂ) (p q : κ → V) : Prop :=
  ∀ (l : V →ₗ[ℝ] ℂ) (v : V),
    2 * π * I * ∑ i, c i * ((om (q i) v : ℂ) * l (p i) + (om (p i) v : ℂ) * l (q i)) = l (X v)
def smS (ρ : V → B →L[ℂ] B) : Submodule ℂ B where
  carrier := {f | Sm ρ f}
  add_mem' := fun hf hg => by simpa only [Set.mem_setOf_eq, Sm, map_add] using ContDiff.add (show ContDiff ℝ ∞ _ from hf) (show ContDiff ℝ ∞ _ from hg)
  zero_mem' := by simpa only [Set.mem_setOf_eq, Sm, map_zero] using contDiff_const
  smul_mem' := fun a _ hf => by simpa only [Set.mem_setOf_eq, Sm, map_smul] using ContDiff.const_smul a (show ContDiff ℝ ∞ _ from hf)
end General
section Coord
variable {ι : Type} [Fintype ι] [DecidableEq ι] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
def xOp (ρ : (ι → ℂ) → B →L[ℂ] B) (k : ι) (f : B) : B :=
  dH ρ (Pi.single k 1) f - I • dH ρ (I • Pi.single k 1) f
def dOp (ρ : (ι → ℂ) → B →L[ℂ] B) (H : Matrix ι ι ℂ) (l : ι) (f : B) : B :=
  (-(1 / (4 * π)) : ℂ) • (dH ρ (H⁻¹ *ᵥ Pi.single l 1) f + I • dH ρ (I • H⁻¹ *ᵥ Pi.single l 1) f)
def nOp (ρ : (ι → ℂ) → B →L[ℂ] B) (H X : Matrix ι ι ℂ) (f : B) : B := ∑ k, ∑ l, X k l • xOp ρ k (dOp ρ H l f)
end Coord
def IsCCR {A : Type} [Ring A] {κ : Type} [DecidableEq κ] (x d : κ → A) : Prop :=
  (∀ k l, x k * x l = x l * x k) ∧ (∀ k l, d k * d l = d l * d k) ∧
    ∀ k l, d l * x k - x k * d l = if k = l then 1 else 0
end GlobalTheory.Mem.Lift
end


