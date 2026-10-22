-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P08
-- name    : QAlgorithms_Papers_Independent_Gap48_P08
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-21T21:09:52.649143+00:00
-- url     : https://prove2.me/theorems/7754b53a-d638-4223-ba2b-b587ff08ac7a
-- title:
--   Definitions for Relative tensor products for modules over von Neumann algebras
-- statement:
--   The objects the formalized statements of *Relative tensor products for modules over von Neumann algebras* (arXiv:math/0301061) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `IsNormalRepresentation`: Normality of a unital representation, §2, PDF p.2: preservation of suprema of nonempty increasing bounded families of positive operators. An `IsLUB` in B(S) supplies the bound; no default-valued supremum is used.
--   - `boundedVectorDomain`: Intrinsic bounded-vector domain, §5, PDF p.10. Here A is the standard right-action algebra R(M), hence a copy of M-op, omega is phi^(1/2), and rho is the given right action in these coordinates. A continuous linear extension of a omega ↦ rho(a) xi is required on the entire standard Hilbert space. No normalization of omega or xi is imposed. This is the source's intrinsic choice of definition, not a coordinate square-summability surrogate.
--   - `BilinearPreclosedOn`: Bilinear preclosedness, §7, PDF p.11. Both input limits use the ambient norm topology and the first limit must belong to D. The bilinear map itself is supplied separately; this predicate records precisely the sequential condition, without asserting continuity or extending its domain.
-- source:
--   Relative tensor products for modules over von Neumann algebras, arXiv:math/0301061v1, https://arxiv.org/abs/math/0301061v1

import Mathlib

/-!
David Sherman, Relative Tensor Products for Modules over von Neumann Algebras,
arXiv:math/0301061v1. Only bounded-vector density is stated in this draft.
The other inventoried nodes are explicitly deferred in the unit's HARD.md.
Compilation is pending the batch handoff.
-/

open Set Filter
open scoped Topology

namespace QAlgorithms.Papers.Independent.Gap48.P08

variable {S K : Type*}
variable [NormedAddCommGroup S] [InnerProductSpace ℂ S] [CompleteSpace S]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Normality of a unital representation, §2, PDF p.2: preservation of suprema
of nonempty increasing bounded families of positive operators. An `IsLUB` in
B(S) supplies the bound; no default-valued supremum is used. -/
def IsNormalRepresentation (A : StarSubalgebra ℂ (S →L[ℂ] S))
    (rho : A →⋆ₐ[ℂ] (K →L[ℂ] K)) : Prop :=
  ∀ T : Set A, T.Nonempty →
    DirectedOn (fun a b : A => A.subtype a ≤ A.subtype b) T →
    (∀ a ∈ T, (0 : S →L[ℂ] S) ≤ A.subtype a) →
    ∀ a : A, IsLUB (A.subtype '' T) (A.subtype a) →
      IsLUB (rho '' T) (rho a)

/-- Intrinsic bounded-vector domain, §5, PDF p.10. Here A is the standard
right-action algebra R(M), hence a copy of M-op, omega is phi^(1/2), and rho
is the given right action in these coordinates. A continuous linear extension
of a omega ↦ rho(a) xi is required on the entire standard Hilbert space.
No normalization of omega or xi is imposed. This is the source's intrinsic
choice of definition, not a coordinate square-summability surrogate. -/
def boundedVectorDomain (A : StarSubalgebra ℂ (S →L[ℂ] S))
    (rho : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (omega : S) : Set K :=
  {xi | ∃ T : S →L[ℂ] K, ∀ a : A, T (A.subtype a omega) = rho a xi}

/-- Bilinear preclosedness, §7, PDF p.11. Both input limits use the ambient
norm topology and the first limit must belong to D. The bilinear map itself
is supplied separately; this predicate records precisely the sequential
condition, without asserting continuity or extending its domain. -/
def BilinearPreclosedOn {E F G : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
    (D : Set E) (f : D → F → G) : Prop :=
  ∀ (xs : ℕ → D) (ys : ℕ → F) (x : D) (y : F) (z : G),
    Tendsto (fun n => (xs n : E)) atTop (𝓝 (x : E)) →
    Tendsto ys atTop (𝓝 y) →
    Tendsto (fun n => f (xs n) (ys n)) atTop (𝓝 z) →
    z = f x y

/-- The inclusion of a concrete von Neumann algebra preserves positive
suprema in its concrete representation; sanity check of the normality API. -/
example (A : StarSubalgebra ℂ (S →L[ℂ] S)) :
    IsNormalRepresentation A A.subtype := by
  intro T hnonempty hdirected hpositive a hlub
  exact hlub

/-- Zero is bounded with the zero extension, including for the zero module. -/
example (A : StarSubalgebra ℂ (S →L[ℂ] S))
    (rho : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (omega : S) :
    (0 : K) ∈ boundedVectorDomain A rho omega := by
  refine ⟨0, ?_⟩
  intro a
  simp

/-- The zero bilinear map is preclosed on any domain, including the empty
one. This is the zero-module edge of Proposition 7.4, PDF p.16. -/
example {E F G : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
    (D : Set E) : BilinearPreclosedOn D (fun (_ : D) (_ : F) => (0 : G)) := by
  intro xs ys x y z hx hy hz
  exact tendsto_nhds_unique hz tendsto_const_nhds

end QAlgorithms.Papers.Independent.Gap48.P08


