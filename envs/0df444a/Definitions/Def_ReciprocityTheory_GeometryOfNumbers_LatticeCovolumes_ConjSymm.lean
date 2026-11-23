-- Prove2me | Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_ConjSymm
-- name    : ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_ConjSymm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:06:02.020425+00:00
-- url     : https://prove2.me/theorems/60dd3fb9-c7d8-4f79-b5a5-272dbb932123
-- title:
--   Conj Symm
-- statement:
--   Definitions and structural lemmas for Conj Symm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/LatticeCovolumes/ConjSymm.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.GeometryOfNumbersTheory
open NumberField Module
open scoped ComplexOrder
structure HermFam (K : Type*) [Field K] (V : Type*) [AddCommGroup V] [Module K V] where

  form : (K →+* ℂ) → V → V → ℂ
  add_right : ∀ σ x y z, form σ x (y + z) = form σ x y + form σ x z
  smul_right : ∀ σ (a : K) x y, form σ x (a • y) = σ a * form σ x y
  conj_symm : ∀ σ x y, starRingEnd ℂ (form σ x y) = form σ y x
  posDef : ∀ σ (n : ℕ) (v : Fin n → V), LinearIndependent K v →
    (Matrix.of fun i j => form σ (v i) (v j)).PosDef
section
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
def HermFam.gram (h : HermFam K V) (σ : K →+* ℂ) {n : ℕ} (v : Fin n → V) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => h.form σ (v i) (v j)
def HermFam.nrm (h : HermFam K V) (σ : K →+* ℂ) (x : V) : ℝ :=
  Real.sqrt (h.form σ x x).re
end
section
variable (K : Type*) [Field K] [NumberField K] {V : Type*} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
def latRank (E : Submodule (𝓞 K) V) : ℕ :=
  finrank K (Submodule.span K (E : Set V))
def IsFrame (E : Submodule (𝓞 K) V) {r : ℕ} (v : Fin r → V) : Prop :=
  (∀ i, v i ∈ E) ∧ LinearIndependent K v ∧ (E : Set V) ⊆ Submodule.span K (Set.range v)
def meanLog (A : (K →+* ℂ) → ℝ) : ℝ :=
  (∑ σ : K →+* ℂ, Real.log (A σ)) / finrank ℚ K
variable {K}
def degreeOfFamily (h : HermFam K V) (E : Submodule (𝓞 K) V) {r : ℕ} (v : Fin r → V) : ℝ :=
  (Real.log ((Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.relIndex E.toAddSubgroup : ℝ)
    - (1 / 2) * ∑ σ : K →+* ℂ, Real.log (h.gram σ v).det.re) / finrank ℚ K
open Classical in

def deg (h : HermFam K V) (E : Submodule (𝓞 K) V) : ℝ :=
  if hE : ∃ p : (Σ r : ℕ, Fin r → V), IsFrame K E p.2 then degreeOfFamily h E hE.choose.2 else 0
end
end ReciprocityTheory.GeometryOfNumbersTheory


