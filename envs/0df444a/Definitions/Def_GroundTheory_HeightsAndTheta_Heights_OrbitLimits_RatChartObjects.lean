-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_RatChartObjects
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_RatChartObjects
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:25:47.854978+00:00
-- url     : https://prove2.me/theorems/04994a00-bd59-4bf6-acda-c5664332fb2e
-- title:
--   Rat Chart Objects
-- statement:
--   Definitions and structural lemmas for Rat Chart Objects, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/RatChartObjects.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsChartCompare
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ComplexSets
namespace RatChart
variable {n d : ℕ}
def ratMap (p : Fin d → MvPolynomial (Fin n) ℂ) (q : MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ) : Fin d → ℂ :=
  fun r => eval x (p r) / eval x q
def ratFibre (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin d → MvPolynomial (Fin n) ℂ)
    (q : MvPolynomial (Fin n) ℂ) (y : Fin d → ℂ) : Set (Fin n → ℂ) :=
  {x | x ∈ zeroSet J ∧ eval x q ≠ 0 ∧ ratMap p q x = y}
def IsRatSheetAt (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin d → MvPolynomial (Fin n) ℂ)
    (q : MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ) (s : (Fin d → ℂ) → Fin n → ℂ) : Prop :=
  ∃ U : Set (Fin d → ℂ), IsOpen U ∧ ratMap p q x ∈ U ∧ DifferentiableOn ℂ s U ∧ s (ratMap p q x) = x ∧
    (∀ y ∈ U, s y ∈ zeroSet J ∧ eval (s y) q ≠ 0 ∧ ratMap p q (s y) = y) ∧
    ∃ V ∈ 𝓝 x, ∀ x' ∈ zeroSet J ∩ V, eval x' q ≠ 0 → ratMap p q x' ∈ U → x' = s (ratMap p q x')
open Classical in

def ratSheetSum (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin d → MvPolynomial (Fin n) ℂ)
    (q : MvPolynomial (Fin n) ℂ) (F : (Fin n → ℂ) → ((Fin d → ℂ) → Fin n → ℂ) → ℝ) (y : Fin d → ℂ) : ℝ :=
  ∑ᶠ (x : Fin n → ℂ) (_ : x ∈ ratFibre J p q y),
    if h : ∃ s, IsRatSheetAt J p q x s then F x h.choose else 0
def ratDens (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin d → MvPolynomial (Fin n) ℂ)
    (q : MvPolynomial (Fin n) ℂ) (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (y : Fin d → ℂ) : ℝ :=
  ratSheetSum J p q (fun x s => f x * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) y) y
def ratAbsDens (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin d → MvPolynomial (Fin n) ℂ)
    (q : MvPolynomial (Fin n) ℂ) (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (y : Fin d → ℂ) : ℝ :=
  ratSheetSum J p q (fun x s => |f x * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) y|) y
end RatChart
namespace PtsSegreChart
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
def segrePoly (a : (k : K) → ι k) : MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ :=
  ∏ k, X (coordEquiv ⟨k, a k⟩)
open Classical in

def projPoly {e : ℕ} (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (r : Fin (e + 1)) :
    MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ :=
  ∑ a, C (Ψ (fun b => if a = b then 1 else 0) r) * segrePoly a
def chartNum {e : ℕ} (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) :
    Fin e → MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ :=
  fun r => projPoly Ψ r.succ
def chartDen {e : ℕ} (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) :
    MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ :=
  projPoly Ψ 0
omit [DecidableEq K] in

def chartWeight (g : ((Σ k, ι k) → ℂ) → ℝ) : (Fin (Fintype.card (Σ k, ι k)) → ℂ) → ℝ :=
  {x | ∀ k, ∃ j, pt x ⟨k, j⟩ ≠ 0}.indicator fun x => g (pt x)
end PtsSegreChart
end GroundTheory.Heights₂.Heights


