-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_DefiniteClassNumber_Places
-- name    : GroundTheory_AutomorphicForms_DefiniteClassNumber_Places
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:32:04.022626+00:00
-- url     : https://prove2.me/theorems/2c112915-4246-4d38-b081-252f3d0451d1
-- title:
--   Places
-- statement:
--   Definitions and structural lemmas for Places, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DefiniteClassNumber/Places.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DefiniteClassNumber_HermTraceSelfOfHermValue
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GroundTheory.Automorphic
open Module Matrix TensorProduct NumberField NumberField.InfinitePlace
variable {K : Type*} [Field K] [NumberField K]
section TotallyReal
abbrev realEmb (hreal : ∀ w : InfinitePlace K, w.IsReal) (w : InfinitePlace K) : K →+* ℝ :=
  embedding_of_isReal (hreal w)
def embeddingsEquivPlaces (hreal : ∀ w : InfinitePlace K, w.IsReal) :
    (K →+* ℂ) ≃ InfinitePlace K where
  toFun := InfinitePlace.mk
  invFun w := w.embedding
  left_inv φ := by
    show (InfinitePlace.mk φ).embedding = φ
    rcases embedding_mk_eq φ with h | h
    · exact h
    · have hr := isReal_iff.1 (hreal (InfinitePlace.mk φ))
      rw [ComplexEmbedding.isReal_iff, h] at hr
      have hφ : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate φ) = φ := star_star φ
      rw [h]
      exact hr.symm.trans hφ
  right_inv w := mk_embedding w
end TotallyReal
section Form
variable {E : Type*} [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι E)
variable {κ : Type*} [Fintype κ] (b : Basis κ K E)
def traceGram : Matrix (ι × κ) (ι × κ) K :=
  fun a c => hermTrace K H K (stdVec K b a) (stdVec K b c)
variable (R : Type*) [CommRing R] [Algebra K R]
def vecOfCoords (c : ι × κ → R) : ι → R ⊗[K] E :=
  fun i => (Algebra.TensorProduct.basis R b).equivFun.symm fun k => c (i, k)
variable {H b}
variable (H b) in

def ratGram (θ : K) :
    Matrix ((ι × κ) × Free.ChooseBasisIndex ℤ (𝓞 K)) ((ι × κ) × Free.ChooseBasisIndex ℤ (𝓞 K)) ℚ :=
  fun j j' => Algebra.trace ℚ K (θ * integralBasis K j.2 * integralBasis K j'.2 * traceGram H b j.1 j'.1)
end Form
end GroundTheory.Automorphic


