-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FmSmulLeft
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_FmSmulLeft
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T02:42:57.256006+00:00
-- url     : https://prove2.me/theorems/6949aea1-4c64-45c7-96c7-852c003c13fd
-- title:
--   Fm Smul Left
-- statement:
--   Definitions and structural lemmas for Fm Smul Left, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FmSmulLeft.lean

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementTB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.GermFibreKernels
open scoped InnerProductSpace ComplexConjugate ComplexOrder
noncomputable section
structure PKer (α : Type) where
  K : α → α → ℂ
  psd : ∀ Y : Finset α, Formalism.FourierDecayAlt.TB.PSDOn Y K
namespace PKer
variable {α : Type} (P : PKer α)
def Sp (_P : PKer α) : Type := α →₀ ℂ
instance : AddCommGroup P.Sp := inferInstanceAs (AddCommGroup (α →₀ ℂ))
instance : Module ℂ P.Sp := inferInstanceAs (Module ℂ (α →₀ ℂ))
def fm (f g : α →₀ ℂ) : ℂ := f.sum fun x a => conj a * g.sum fun y b => P.K x y * b
theorem herm (x y : α) : conj (P.K y x) = P.K x y := by
  classical
  have h := (P.psd {x, y}).1
  have hx : x ∈ ({x, y} : Finset α) := by simp
  have hy : y ∈ ({x, y} : Finset α) := by simp
  have := congrFun (congrFun h ⟨x, hx⟩) ⟨y, hy⟩
  simpa [Matrix.conjTranspose_apply, Matrix.of_apply] using this
theorem fm_add_left (f₁ f₂ g : α →₀ ℂ) : P.fm (f₁ + f₂) g = P.fm f₁ g + P.fm f₂ g := by
  unfold fm
  exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by simp [map_add]; ring)
theorem fm_smul_left (f g : α →₀ ℂ) (r : ℂ) : P.fm (r • f) g = conj r * P.fm f g := by
  unfold fm
  rw [Finsupp.sum_smul_index' (fun _ => by simp), Finsupp.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [smul_eq_mul, map_mul]; ring
theorem fm_conj (f g : α →₀ ℂ) : conj (P.fm g f) = P.fm f g := by
  unfold fm
  simp only [Finsupp.sum, map_sum, map_mul, Complex.conj_conj, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
  rw [P.herm y x]; ring
theorem fm_nonneg (f : α →₀ ℂ) : 0 ≤ (P.fm f f).re := by
  classical
  have h := (Matrix.posSemidef_iff_dotProduct_mulVec.1 (P.psd f.support)).2 (fun i => f i)
  have e : dotProduct (star (fun i : f.support => f i)) (Matrix.mulVec (Matrix.of fun x y : f.support => P.K x y) (fun i => f i)) =
      P.fm f f := by
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply]
    unfold fm
    simp only [Finsupp.sum]
    rw [← Finset.sum_coe_sort f.support (fun x => (starRingEnd ℂ) (f x) * ∑ y ∈ f.support, P.K x y * f y)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_coe_sort f.support (fun y => P.K (↑i) y * f y)]
    simp only [Complex.star_def]
  rw [e] at h
  exact (Complex.nonneg_iff.1 h).1
instance core : PreInnerProductSpace.Core ℂ P.Sp where
  inner f g := P.fm f g
  conj_inner_symm f g := P.fm_conj f g
  re_inner_nonneg f := P.fm_nonneg f
  add_left f₁ f₂ g := P.fm_add_left f₁ f₂ g
  smul_left f g r := P.fm_smul_left f g r
instance : SeminormedAddCommGroup P.Sp := InnerProductSpace.Core.toSeminormedAddCommGroup (c := P.core)
instance : InnerProductSpace ℂ P.Sp := InnerProductSpace.ofCore P.core
abbrev H : Type := UniformSpace.Completion P.Sp
def vec (x : α) : P.H := UniformSpace.Completion.coe' (show P.Sp from Finsupp.single x (1 : ℂ))
end PKer
end
end Formalism.FourierDecayAlt.P.GermFibreKernels


