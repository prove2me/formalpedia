-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_LocalizedGradingSpan_Defs
-- name    : LPCA_Solutions_LPCA_LocalizedGradingSpan_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:22:44.605832+00:00
-- url     : https://prove2.me/theorems/c04839a4-cba8-44a7-90af-984fbf62c1e3
-- title:
--   Localized Grading Span for localized persistent commutative algebra
-- statement:
--   This bundle supplies localized Grading Span for localized persistent commutative algebra. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
--
--   The included constructions and necessary compatibility results are:
--
--   - Agreement of the actual native k-action with the composite base map.
--   - Expanding a polynomial numerator expresses the actual fraction as a finite sum of actual homogeneous monomial fractions.
--   - The actual integer-homogeneous pieces span the entire localization. Their directness is a further theorem, not an assumption here.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_LocalizedGradingSpan.lean, selected declarations in lines 12–76; source SHA-256 f2da6b040d766ffc78f064ada2c1d085af102e9773d4267d764fee4a9a699a57; source certificate Sapelo2 job 49172236.

import Mathlib.Algebra.Homology.LocalCohomology
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Tactic
import Definitions.Def_LPCA
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationConsequences_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedBasis_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedDimension_Defs

set_option autoImplicit false

namespace LPCA

universe u

variable {V : Type u} [DecidableEq V]
variable (k : Type u) [Field k]

/-- Agreement of the actual native k-action with the composite base map. -/
theorem localized_smul_base (K : Complex V) (F : Finset V)
    (c : k) (z : LocalizedFaceRing k K F) :
    c • z = algebraMap (FaceRing k K) (LocalizedFaceRing k K F)
      (algebraMap k (FaceRing k K) c) * z := by
  have h := OreLocalization.smul_one_oreDiv_one_smul
    (R := k) (M := FaceRing k K) (S := Submonoid.powers (invertedMonomial k K F)) c z
  rw [← Algebra.algebraMap_eq_smul_one] at h
  exact h.symm

/-- Expanding a polynomial numerator expresses the actual fraction as a
finite sum of actual homogeneous monomial fractions. -/
theorem localizedFraction_as_sum (K : Complex V) (F : Finset V)
    (N : ℕ) (p : MvPolynomial V k) :
    IsLocalization.mk' (M := Submonoid.powers (invertedMonomial k K F))
        (LocalizedFaceRing k K F) (Ideal.Quotient.mk (srIdeal k K) p)
          ⟨invertedMonomial k K F ^ N, ⟨N, rfl⟩⟩ =
      ∑ m ∈ p.support, p.coeff m • localizedMonomial k K F m N := by
  classical
  rw [IsLocalization.mk'_eq_mul_mk'_one]
  have hp := congrArg (fun q : MvPolynomial V k =>
    algebraMap (FaceRing k K) (LocalizedFaceRing k K F)
      (Ideal.Quotient.mk (srIdeal k K) q)) p.as_sum
  simp only [map_sum] at hp
  rw [hp, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m _
  have hf : localizedMonomial k K F m N =
      algebraMap (FaceRing k K) (LocalizedFaceRing k K F)
        (Ideal.Quotient.mk (srIdeal k K) (MvPolynomial.monomial m (1 : k))) *
      IsLocalization.mk' (M := Submonoid.powers (invertedMonomial k K F))
        (LocalizedFaceRing k K F) 1 ⟨invertedMonomial k K F ^ N, ⟨N, rfl⟩⟩ :=
    IsLocalization.mk'_eq_mul_mk'_one _ _
  rw [localized_smul_base, hf]
  have hm : MvPolynomial.monomial m (p.coeff m) =
      MvPolynomial.C (p.coeff m) * MvPolynomial.monomial m (1 : k) := by
    simp only [MvPolynomial.C_mul_monomial, mul_one]
  rw [hm, map_mul, map_mul, mul_assoc]
  rfl

theorem localizedMonomial_mem_degree (K : Complex V) (F : Finset V)
    (m : V →₀ ℕ) (N : ℕ) :
    localizedMonomial k K F m N ∈ localizedPiece k K F
      (fun j => (m j : ℤ) - if j ∈ F then (N : ℤ) else 0) :=
  Submodule.subset_span ⟨m, N, fun _ => rfl, rfl⟩

/-- The actual integer-homogeneous pieces span the entire localization.
Their directness is a further theorem, not an assumption here. -/
theorem localizedPieces_iSup_eq_top (K : Complex V) (F : Finset V) :
    (⨆ a : V → ℤ, localizedPiece k K F a) = ⊤ := by
  classical
  apply top_unique
  intro z _
  obtain ⟨r, s, hs⟩ := IsLocalization.exists_mk'_eq
    (Submonoid.powers (invertedMonomial k K F)) z
  obtain ⟨N, hN⟩ := s.2
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective r
  have he : s = ⟨invertedMonomial k K F ^ N, ⟨N, rfl⟩⟩ := Subtype.ext hN.symm
  rw [← hs, he, localizedFraction_as_sum]
  apply Submodule.sum_mem
  intro m _
  apply Submodule.smul_mem
  exact Submodule.mem_iSup_of_mem
    (fun j => (m j : ℤ) - if j ∈ F then (N : ℤ) else 0)
      (localizedMonomial_mem_degree k K F m N)

end LPCA


