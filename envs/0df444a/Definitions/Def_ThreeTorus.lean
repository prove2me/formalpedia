-- Prove2me | Definitions.Def_ThreeTorus
-- name    : ThreeTorus
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:31.985138+00:00
-- url     : https://prove2.me/theorems/00f5f01c-5935-44f8-9563-17ec061aae12
-- statement:
--   The block models the three-torus as Torus=(ℝ/ℤ)³, built from three copies of the unit additive circle, with Cover=ℝ³ as its universal cover and project the coordinatewise quotient map. A self-map T of the torus is Smooth if every point x of the cover has an open neighbourhood U and a map F on the cover, C^∞ on U, such that T(project y)=project(F y) for all y in U. The measure μ is the product of three copies of the normalized Haar measure on the circle, a probability measure, and H is the complex L²(μ) space. The subspace meanZero (H₀) consists of those f in H with ∫f dμ=0, and CircleH is the complex L² space of the normalized Haar measure on the circle of length 1. A mean-zero element f is IsReal if its imaginary part vanishes μ-almost everywhere. MainConclusion is a defined proposition, not an established theorem. It asserts that there is a permutation T of the torus such that T and its inverse are both Smooth and T preserves μ, together with a real f in H₀ and a family v indexed by the integers, with each v n equal almost everywhere to f∘Tⁿ, such that v is orthonormal and its complex span is dense in H₀. T is also required to be ergodic with respect to μ. Finally there must be a linear isometric equivalence W from H₀ onto CircleH such that, for every g in H₀, some h in H₀ equals g∘T almost everywhere and satisfies W h(z)=e^{2πiz}·W g(z) for almost every z, where e^{2πiz} is the first Fourier character. In words, this is complete simple Lebesgue spectrum for a smooth, measure-preserving, ergodic diffeomorphism of the torus.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/ThreeTorus.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/ThreeTorus.lean; bytes 16..2901
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

/-!
The torus is (ℝ/ℤ)³ with normalized product Haar measure. Smoothness means
local smooth lifts on the universal cover, for both the map and its inverse.

The almost-everywhere graph conditions are independent of representatives of
L² classes. The real generator's bilateral Koopman orbit spans the entire
complex mean-zero L² space. The spectral model is the full circle L² space
with multiplication by the first Fourier character.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal Topology

namespace ThreeTorus

abbrev Torus := Fin 3 → UnitAddCircle
abbrev Cover := Fin 3 → ℝ

def project (x : Cover) : Torus := fun i => (x i : UnitAddCircle)

def Smooth (T : Torus → Torus) : Prop :=
  ∀ x : Cover, ∃ U : Set Cover, IsOpen U ∧ x ∈ U ∧
    ∃ F : Cover → Cover, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F U ∧
      ∀ y ∈ U, T (project y) = project (F y)

def μ : Measure Torus := Measure.pi (fun _ : Fin 3 => AddCircle.haarAddCircle)

instance : IsProbabilityMeasure μ := by unfold μ; infer_instance

abbrev H : Type := Lp ℂ 2 μ

/-- The full complex subspace defined by zero Lebesgue integral. -/
def meanZero : Submodule ℂ H where
  carrier := {f | ∫ x, f x ∂μ = 0}
  zero_mem' := by
    change ∫ x, (0 : H) x ∂μ = 0
    rw [integral_congr_ae (Lp.coeFn_zero ℂ 2 μ)]
    simp
  add_mem' := by
    intro f g hf hg
    change ∫ x, (f + g) x ∂μ = 0
    rw [integral_congr_ae (Lp.coeFn_add f g)]
    change ∫ x, f x + g x ∂μ = 0
    rw [integral_add (MemLp.integrable (by norm_num) (Lp.memLp f))
      (MemLp.integrable (by norm_num) (Lp.memLp g))]
    change (∫ x, f x ∂μ) + (∫ x, g x ∂μ) = 0
    rw [show ∫ x, f x ∂μ = 0 from hf, show ∫ x, g x ∂μ = 0 from hg, add_zero]
  smul_mem' := by
    intro c f hf
    change ∫ x, (c • f) x ∂μ = 0
    rw [integral_congr_ae (Lp.coeFn_smul c f)]
    change ∫ x, c • f x ∂μ = 0
    rw [integral_smul]
    rw [show ∫ x, f x ∂μ = 0 from hf, smul_zero]

abbrev H₀ := ↥meanZero
abbrev CircleH : Type := Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))

def IsReal (f : H₀) : Prop := ∀ᵐ x ∂μ, (f.1 x).im = 0

/-- Complete simple Lebesgue spectrum, including the stated consequences. -/
def MainConclusion : Prop :=
  ∃ T : Equiv.Perm Torus,
    Smooth T ∧ Smooth T.symm ∧ MeasurePreserving T μ μ ∧
    ∃ f : H₀, IsReal f ∧
    ∃ v : ℤ → H₀,
      (∀ n : ℤ, ∀ᵐ x ∂μ, (v n).1 x = f.1 ((T ^ n) x)) ∧
      Orthonormal ℂ v ∧
      Dense (Submodule.span ℂ (Set.range v) : Set H₀) ∧
      Ergodic T μ ∧
      ∃ W : H₀ ≃ₗᵢ[ℂ] CircleH,
        ∀ g : H₀, ∃ h : H₀,
          (∀ᵐ x ∂μ, h.1 x = g.1 (T x)) ∧
          (∀ᵐ z ∂(AddCircle.haarAddCircle (T := (1 : ℝ))),
            W h z = fourier 1 z * W g z)



end ThreeTorus
end
end OAI


