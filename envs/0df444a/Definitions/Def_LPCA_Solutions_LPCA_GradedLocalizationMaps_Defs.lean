-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_GradedLocalizationMaps_Defs
-- name    : LPCA_Solutions_LPCA_GradedLocalizationMaps_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:22:05.25523+00:00
-- url     : https://prove2.me/theorems/ef19e2a9-7982-45f3-ab55-d62420d76902
-- title:
--   Graded Localization Maps for localized persistent commutative algebra
-- statement:
--   This bundle supplies graded Localization Maps for localized persistent commutative algebra. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
--
--   The included constructions and necessary compatibility results are:
--
--   - Enlarging the inversion set sends each coefficient-one fraction to the coefficient-one fraction of the same degree, including when it becomes zero.
--   - The native scalar action on the localization agrees with the base-ring action.
--   - The degree-preserving restriction of the genuine localization map.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_GradedLocalizationMaps.lean, selected declarations in lines 28–134; source SHA-256 dffe0a3a92824290859ff99b130588566d96fe3314e2a6d8fc9d3041a6a55284; source certificate Sapelo2 job 49172236.

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
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedBasis_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedDimension_Defs

set_option autoImplicit false

namespace LPCA

universe u

variable {V : Type u} [DecidableEq V]
variable (k : Type u) [Field k]

private noncomputable def indicator (F : Finset V) : V →₀ ℕ :=
  Finsupp.indicator F (fun _ _ => 1)

private theorem inverted_pow (K : Complex V) (F : Finset V) (N : ℕ) :
    invertedMonomial k K F ^ N = Ideal.Quotient.mk (srIdeal k K)
      (MvPolynomial.monomial (N • indicator F) (1 : k)) := by
  have heq : invertedMonomial k K F = Ideal.Quotient.mk (srIdeal k K)
      (MvPolynomial.monomial (indicator F) (1 : k)) := by
    unfold invertedMonomial variableClass
    rw [← map_prod]
    congr 1
    simpa only [indicator, pow_one] using
      MvPolynomial.prod_X_pow (R := k) (fun _ : V => 1) F
  rw [heq, ← map_pow, MvPolynomial.monomial_pow, one_pow]

/-- Enlarging the inversion set sends each coefficient-one fraction to the
coefficient-one fraction of the same degree, including when it becomes zero. -/
theorem localizationMap_monomial_of_degree
    (K : Complex V) (F G : Finset V) (hFG : F ⊆ G) (a : V → ℤ)
    (m m' : V →₀ ℕ) (N N' : ℕ)
    (hm : ∀ j : V, (m j : ℤ) - (if j ∈ F then (N : ℤ) else 0) = a j)
    (hm' : ∀ j : V, (m' j : ℤ) - (if j ∈ G then (N' : ℤ) else 0) = a j) :
    localizationMap k K F G hFG (localizedMonomial k K F m N) =
      localizedMonomial k K G m' N' := by
  have hexponents : m + N' • indicator G = m' + N • indicator F := by
    ext j
    have h := hm j
    have h' := hm' j
    by_cases hjF : j ∈ F <;> by_cases hjG : j ∈ G <;>
      simp [indicator, hjF, hjG, Finsupp.indicator_of_mem,
        Finsupp.indicator_of_notMem, Finsupp.smul_apply, smul_eq_mul] at * <;> omega
  have hcross :
      Ideal.Quotient.mk (srIdeal k K) (MvPolynomial.monomial m (1 : k)) *
        invertedMonomial k K G ^ N' =
      Ideal.Quotient.mk (srIdeal k K) (MvPolynomial.monomial m' (1 : k)) *
        invertedMonomial k K F ^ N := by
    rw [inverted_pow, inverted_pow, ← map_mul, ← map_mul,
      MvPolynomial.monomial_mul, MvPolynomial.monomial_mul, one_mul, hexponents]
  have hunit : IsUnit (algebraMap (FaceRing k K) (LocalizedFaceRing k K G)
      (invertedMonomial k K F ^ N)) := by
    rw [map_pow]
    exact (IsLocalization.Away.isUnit_of_dvd (S := LocalizedFaceRing k K G)
      (invertedMonomial k K G) (invertedMonomial_dvd k K F G hFG)).pow N
  have hspec :
      localizationMap k K F G hFG (localizedMonomial k K F m N) *
        algebraMap (FaceRing k K) (LocalizedFaceRing k K G)
          (invertedMonomial k K F ^ N) =
      algebraMap (FaceRing k K) (LocalizedFaceRing k K G)
        (Ideal.Quotient.mk (srIdeal k K) (MvPolynomial.monomial m (1 : k))) := by
    rw [← localizationMap_base k K F G hFG (invertedMonomial k K F ^ N), ← map_mul]
    unfold localizedMonomial
    rw [IsLocalization.mk'_spec, localizationMap_base]
  change _ = IsLocalization.mk' (M := Submonoid.powers (invertedMonomial k K G))
    (LocalizedFaceRing k K G)
    (Ideal.Quotient.mk (srIdeal k K) (MvPolynomial.monomial m' (1 : k)))
    ⟨invertedMonomial k K G ^ N', ⟨N', rfl⟩⟩
  apply IsLocalization.eq_mk'_iff_mul_eq.mpr
  dsimp only [Subtype.coe_mk]
  apply hunit.mul_left_inj.mp
  change (_ * _) * _ = _ * _
  calc
    _ = (localizationMap k K F G hFG (localizedMonomial k K F m N) *
        algebraMap (FaceRing k K) (LocalizedFaceRing k K G)
          (invertedMonomial k K F ^ N)) *
        algebraMap (FaceRing k K) (LocalizedFaceRing k K G)
          (invertedMonomial k K G ^ N') := by ring
    _ = _ := by rw [hspec, ← map_mul, ← map_mul, hcross]

/-- The native scalar action on the localization agrees with the base-ring action. -/
theorem localizationMap_smul
    (K : Complex V) (F G : Finset V) (hFG : F ⊆ G)
    (c : k) (z : LocalizedFaceRing k K F) :
    localizationMap k K F G hFG (c • z) = c • localizationMap k K F G hFG z := by
  have hsmul : ∀ (H : Finset V) (w : LocalizedFaceRing k K H),
      c • w = algebraMap (FaceRing k K) (LocalizedFaceRing k K H)
        (algebraMap k (FaceRing k K) c) * w := by
    intro H w
    have h := OreLocalization.smul_one_oreDiv_one_smul
      (R := k) (M := FaceRing k K) (S := Submonoid.powers (invertedMonomial k K H)) c w
    rw [← Algebra.algebraMap_eq_smul_one] at h
    exact h.symm
  rw [hsmul F z, hsmul G (localizationMap k K F G hFG z)]
  rw [map_mul, localizationMap_base]

noncomputable def localizationLinearMap
    (K : Complex V) (F G : Finset V) (hFG : F ⊆ G) :
    LocalizedFaceRing k K F →ₗ[k] LocalizedFaceRing k K G where
  toFun := localizationMap k K F G hFG
  map_add' := map_add _
  map_smul' := localizationMap_smul k K F G hFG

variable [Fintype V]

theorem localizationMap_mem_piece
    (K : Complex V) (F G : Finset V) (hFG : F ⊆ G) (a : V → ℤ)
    {z : LocalizedFaceRing k K F} (hz : z ∈ localizedPiece k K F a) :
    localizationMap k K F G hFG z ∈ localizedPiece k K G a := by
  have hle : localizedPiece k K F a ≤
      (localizedPiece k K G a).comap (localizationLinearMap k K F G hFG) := by
    apply Submodule.span_le.mpr
    rintro z ⟨m, N, hm, rfl⟩
    have hnonnegative : ∀ j : V, j ∉ G → 0 ≤ a j := by
      intro j hj
      have hjF : j ∉ F := fun hjF => hj (hFG hjF)
      have h := hm j
      simp only [if_neg hjF, sub_zero] at h
      omega
    obtain ⟨m', N', hm', _⟩ := exists_positive_denominator_rep G a hnonnegative
    change localizationMap k K F G hFG (localizedMonomial k K F m N) ∈
      localizedPiece k K G a
    rw [localizationMap_monomial_of_degree k K F G hFG a m m' N N' hm hm']
    exact Submodule.subset_span ⟨m', N', hm', rfl⟩
  exact hle hz

/-- The degree-preserving restriction of the genuine localization map. -/
noncomputable def localizedPieceMap
    (K : Complex V) (F G : Finset V) (hFG : F ⊆ G) (a : V → ℤ) :
    localizedPiece k K F a →ₗ[k] localizedPiece k K G a where
  toFun z := ⟨localizationMap k K F G hFG z.1,
    localizationMap_mem_piece k K F G hFG a z.2⟩
  map_add' x y := Subtype.ext (map_add _ _ _)
  map_smul' c x := Subtype.ext (localizationMap_smul k K F G hFG c x.1)





end LPCA


