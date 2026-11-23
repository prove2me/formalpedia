-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
-- name    : ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:19:15.589794+00:00
-- url     : https://prove2.me/theorems/f5ca5e2d-613c-4e5d-b868-dab32a3d6be3
-- title:
--   Is Local Homeomorph
-- statement:
--   Definitions and structural lemmas for Is Local Homeomorph, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/IsLocalHomeomorph.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.L2DbarEstimates
open MeasureTheory
open scoped ContDiff ENNReal
noncomputable section
abbrev V (n : ℕ) : Type := EuclideanSpace ℂ (Fin n)
def bas (n : ℕ) (j : Fin n) : V n := EuclideanSpace.single j 1
def wd (n : ℕ) (j : Fin n) (g : V n → ℂ) (y : V n) : ℂ :=
  (fderiv ℝ g y (bas n j) - Complex.I * fderiv ℝ g y (Complex.I • bas n j)) / 2
def wdb (n : ℕ) (j : Fin n) (g : V n → ℂ) (y : V n) : ℂ :=
  (fderiv ℝ g y (bas n j) + Complex.I * fderiv ℝ g y (Complex.I • bas n j)) / 2
def IsChart {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (e : OpenPartialHomeomorph M (V n)) : Prop :=
  Set.EqOn z e e.source
def leviV (n : ℕ) (g : V n → ℂ) (y : V n) (ξ : Fin n → ℂ) : ℂ :=
  ∑ j, ∑ k, wd n j (wdb n k g) y * ξ j * (starRingEnd ℂ) (ξ k)
def cHess (n : ℕ) (g : V n → ℂ) (y : V n) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun j k => wd n j (wdb n k g) y
def Smooth {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f : M → ℂ) : Prop :=
  ∀ e : OpenPartialHomeomorph M (V n), IsChart n z e → ContDiffOn ℝ ∞ (f ∘ e.symm) e.target
def Ck {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (k : ℕ) (f : M → ℂ) : Prop :=
  ∀ e : OpenPartialHomeomorph M (V n), IsChart n z e → ContDiffOn ℝ k (f ∘ e.symm) e.target
def CkR {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (k : ℕ) (f : M → ℝ) : Prop :=
  Ck n z k (fun x => (f x : ℂ))
def SmoothR {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f : M → ℝ) : Prop :=
  Smooth n z (fun x => (f x : ℂ))
def Holo {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f : M → ℂ) : Prop :=
  ∀ e : OpenPartialHomeomorph M (V n), IsChart n z e → DifferentiableOn ℂ (f ∘ e.symm) e.target
open scoped Classical in

def d {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (j : Fin n) (f : M → ℂ) (x : M) :
    ℂ :=
  if h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source then
    wd n j (f ∘ (Classical.choose h).symm) (z x)
  else 0
open scoped Classical in

def db {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (j : Fin n) (f : M → ℂ) (x : M) :
    ℂ :=
  if h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source then
    wdb n j (f ∘ (Classical.choose h).symm) (z x)
  else 0
def dbarDot {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f : M → ℂ) (x : M)
    (ξ : Fin n → ℂ) : ℂ :=
  ∑ j, db n z j f x * (starRingEnd ℂ) (ξ j)
def dDot {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f : M → ℂ) (x : M)
    (ξ : Fin n → ℂ) : ℂ :=
  ∑ j, d n z j f x * ξ j
def Levi {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (ph : M → ℝ) (x : M)
    (ξ : Fin n → ℂ) : ℂ :=
  ∑ j, ∑ k, d n z j (db n z k (fun y => (ph y : ℂ))) x * ξ j * (starRingEnd ℂ) (ξ k)
def LeviNonneg {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (ph : M → ℝ) : Prop :=
  ∀ x ξ, 0 ≤ (Levi n z ph x ξ).re
def IsTest {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (g : M → ℂ) : Prop :=
  Smooth n z g ∧ HasCompactSupport g
def volFun {M : Type*} (n : ℕ) (z : M → V n) (A : Set M) : ℝ≥0∞ :=
  ∫⁻ y, ((A ∩ z ⁻¹' {y}).encard : ℝ≥0∞)
def VolAdditive {M : Type*} [MeasurableSpace M] (n : ℕ) (z : M → V n) : Prop :=
  ∀ ⦃f : ℕ → Set M⦄, (∀ i, MeasurableSet (f i)) → Pairwise (Function.onFun Disjoint f) →
    volFun n z (⋃ i, f i) = ∑' i, volFun n z (f i)
open scoped Classical in

def vol {M : Type*} [MeasurableSpace M] (n : ℕ) (z : M → V n) : Measure M :=
  if h : VolAdditive n z then
    Measure.ofMeasurable (fun A _ => volFun n z A) (by simp [volFun]) (fun _ hf hd => h hf hd)
  else 0
def wint {M : Type*} [MeasurableSpace M] (n : ℕ) (z : M → V n) (f : M → ℂ) (ph : M → ℝ) :
    ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2 * Real.exp (-ph x)) ∂vol n z
def jac {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (g : Fin n → M → ℂ) (x : M) : ℂ :=
  (Matrix.of fun i k => d n z k (g i) x).det
def VanishesBeyond {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (u : M → ℂ) (x : M)
    (m : ℕ) : Prop :=
  ∀ e : OpenPartialHomeomorph M (V n), IsChart n z e → x ∈ e.source →
    ∀ k ≤ m, iteratedFDeriv ℂ k (u ∘ e.symm) (z x) = 0
def IsBergmanProj {M : Type*} [TopologicalSpace M] [MeasurableSpace M] (n : ℕ) (z : M → V n)
    (ps : M → ℝ) (F0 F : M → ℂ) : Prop :=
  Holo n z F ∧ wint n z F ps < ⊤ ∧
    ∀ G : M → ℂ, Holo n z G → wint n z G ps < ⊤ →
      ∫ x, (F0 x - F x) * (starRingEnd ℂ) (G x) * (Real.exp (-ps x) : ℂ) ∂vol n z = 0
structure EtaleStein (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] where

  z : M → V n
  isLocalHomeomorph : IsLocalHomeomorph z

  e : M → ℝ
  smooth_e : SmoothR n z e
  levi_e : LeviNonneg n z e
  isCompact_le : ∀ a : ℝ, IsCompact {x | e x ≤ a}
end
end ReciprocityTheory.L2DbarEstimates


