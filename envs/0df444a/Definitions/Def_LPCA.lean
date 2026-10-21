-- Prove2me | Definitions.Def_LPCA
-- name    : LPCA
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-20T22:37:35.341906+00:00
-- url     : https://prove2.me/theorems/3ddd3bd9-d4ca-4ddf-bffa-9b6efe91f075
-- title:
--   Face complexes, face rings and localized homogeneous pieces
-- statement:
--   Let $k$ be a field and $V$ an ambient vertex type. A finite complex is a downward-closed finite family of finite subsets of $V$, with the void complex distinguished from the complex containing only the empty face. The bundle defines deletion, link, coordinate links, monotone filtration levels, the Stanley–Reisner quotient $k[\Delta]$, localization at a coordinate monomial, and the actual integer-graded homogeneous subspaces spanned by monomial fractions. The combinatorial nonvanishing criterion is a separate predicate. Local cohomology is Mathlib's Ext-colimit object; its comparison with Čech cohomology is not assumed.
-- source:
--   https://arxiv.org/abs/2609.02858v1, Sections 1, 2.1, 3.1 and 6; definitions supporting Lemma 2.1.

import Mathlib.Algebra.Homology.LocalCohomology
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Powerset

set_option autoImplicit false

namespace LPCA

universe u

/-- Finite downward-closed face families, allowing both the void complex and `{∅}`.
The original complex's singleton convention is imposed separately, because links and
filtration levels may have ghost vertices or no faces. -/
structure Complex (V : Type u) [DecidableEq V] where
  faces : Finset (Finset V)
  down_closed : ∀ {s t : Finset V}, s ∈ faces → t ⊆ s → t ∈ faces

variable {V : Type u} [DecidableEq V]

def AllVertices (K : Complex V) : Prop := ∀ i : V, {i} ∈ K.faces

def deletion (K : Complex V) (i : V) : Complex V where
  faces := K.faces.filter (fun s => i ∉ s)
  down_closed := by
    intro s t hs hts
    simp only [Finset.mem_filter] at hs ⊢
    exact ⟨K.down_closed hs.1 hts, fun hit => hs.2 (hts hit)⟩

def link (K : Complex V) (A : Finset V) : Complex V where
  faces := K.faces.filter (fun s => Disjoint s A ∧ s ∪ A ∈ K.faces)
  down_closed := by
    intro s t hs hts
    simp only [Finset.mem_filter] at hs ⊢
    exact ⟨K.down_closed hs.1 hts, hs.2.1.mono_left hts,
      K.down_closed hs.2.2 (Finset.union_subset_union hts (Finset.Subset.refl A))⟩

def coordinateLink (K : Complex V) (U A : Finset V) : Complex V where
  faces := K.faces.filter (fun s => Disjoint s U ∧ s ∪ A ∈ K.faces)
  down_closed := by
    intro s t hs hts
    simp only [Finset.mem_filter] at hs ⊢
    exact ⟨K.down_closed hs.1 hts, hs.2.1.mono_left hts,
      K.down_closed hs.2.2 (Finset.union_subset_union hts (Finset.Subset.refl A))⟩

def FiltrationMonotone (K : Complex V) (f : Finset V → ℝ) : Prop :=
  ∀ {s t : Finset V}, t ∈ K.faces → s ⊆ t → f s ≤ f t

noncomputable def level (K : Complex V) (f : Finset V → ℝ)
    (hf : FiltrationMonotone K f) (r : ℝ) : Complex V where
  faces := K.faces.filter (fun s => f s ≤ r)
  down_closed := by
    intro s t hs hts
    simp only [Finset.mem_filter] at hs ⊢
    exact ⟨K.down_closed hs.1 hts, (hf hs.1 hts).trans hs.2⟩

section Ring

variable (k : Type u) [Field k]

noncomputable def srIdeal (K : Complex V) : Ideal (MvPolynomial V k) :=
  Ideal.span {p | ∃ F : Finset V, F ∉ K.faces ∧ p = ∏ j ∈ F, MvPolynomial.X j}

abbrev FaceRing (K : Complex V) : Type u := MvPolynomial V k ⧸ srIdeal k K

noncomputable def variableClass (K : Complex V) (j : V) : FaceRing k K :=
  Ideal.Quotient.mk (srIdeal k K) (MvPolynomial.X j)

noncomputable def coordinateIdeal (T : Finset V) : Ideal (MvPolynomial V k) :=
  Ideal.span (MvPolynomial.X '' (T : Set V))

noncomputable def invertedMonomial (K : Complex V) (F : Finset V) : FaceRing k K :=
  ∏ j ∈ F, variableClass k K j

abbrev LocalizedFaceRing (K : Complex V) (F : Finset V) : Type u :=
  Localization.Away (invertedMonomial k K F)

noncomputable instance localizedAlgebra (K : Complex V) (F : Finset V) :
    Algebra k (LocalizedFaceRing k K F) :=
  ((algebraMap (FaceRing k K) (LocalizedFaceRing k K F)).comp
    (algebraMap k (FaceRing k K))).toAlgebra

/-- A genuine local-cohomology object from Mathlib's direct-limit-of-Ext definition.
No comparison with a combinatorial model is assumed by this definition. -/
noncomputable def supportCohomology (K : Complex V) (T : Finset V) (q : ℕ) :=
  (localCohomology (coordinateIdeal k T) q).obj
    (ModuleCat.of (MvPolynomial V k) (FaceRing k K))

/-- A fraction with numerator a monomial and denominator `(x_F)^N`. -/
noncomputable def localizedMonomial (K : Complex V) (F : Finset V)
    (m : V →₀ ℕ) (N : ℕ) : LocalizedFaceRing k K F :=
  IsLocalization.mk' (M := Submonoid.powers (invertedMonomial k K F))
    (LocalizedFaceRing k K F)
    (Ideal.Quotient.mk (srIdeal k K) (MvPolynomial.monomial m (1 : k)))
    ⟨invertedMonomial k K F ^ N, ⟨N, rfl⟩⟩

/-- The actual homogeneous subspace in the localized face ring. Integer degrees
record the denominator; negative exponents are never truncated into a new definition. -/
noncomputable def localizedPiece (K : Complex V) (F : Finset V) (a : V → ℤ) :
    Submodule k (LocalizedFaceRing k K F) :=
  Submodule.span k {z | ∃ (m : V →₀ ℕ) (N : ℕ),
    (∀ j : V, (m j : ℤ) - (if j ∈ F then (N : ℤ) else 0) = a j) ∧
      z = localizedMonomial k K F m N}

end Ring

section Grading

variable [Fintype V]

def positiveSupport (a : V → ℤ) : Finset V := Finset.univ.filter (fun j => 0 < a j)

def negativeSupport (a : V → ℤ) : Finset V := Finset.univ.filter (fun j => a j < 0)

/-- The explicit nonvanishing criterion from Lemma 2.1, kept separate from
the actual localized homogeneous piece. Their dimension comparison is a theorem. -/
def LocalizationCriterion (K : Complex V) (F : Finset V) (a : V → ℤ) : Prop :=
  (∀ j : V, j ∉ F → 0 ≤ a j) ∧ positiveSupport a ∪ F ∈ K.faces

/-- Candidate monomial basis indices for the multidegree-a Cech term.
The comparison with actual localizations is intentionally a separate target. -/
abbrev CechBasis (K : Complex V) (T : Finset V) (a : V → ℤ) (p : ℕ) : Type u :=
  {F : Finset V // F ⊆ T ∧ F.card = p ∧ LocalizationCriterion K F a}

end Grading

end LPCA


