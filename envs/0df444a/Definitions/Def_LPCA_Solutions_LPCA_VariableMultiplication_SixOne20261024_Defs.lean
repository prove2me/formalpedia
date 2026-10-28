-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_VariableMultiplication_SixOne20261024_Defs
-- name    : LPCA_Solutions_LPCA_VariableMultiplication_SixOne20261024_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-24T20:05:16.167618+00:00
-- url     : https://prove2.me/theorems/0e347770-ed0b-4713-8cf9-1c007a699d3f
-- title:
--   Variable Multiplication — coordinate chain dependencies
-- statement:
--   This bundle supplies the selected constructions and proved compatibility results for variable multiplication used in the coordinate Čech chain comparison. Each construction retains the rings, categories, grading indices and hypotheses in its formal declaration.
--
--   Multiplication by the image of the polynomial variable, on the actual localization.
--
--   The genuine variable action restricted from degree a to degree b=a+e_j.
-- source:
--   https://arxiv.org/abs/2609.02858v1, Section 6, Theorem 6.1 and its formalization dependencies. Certified Lean source: Solutions/LPCA_VariableMultiplication.lean, selected declarations in lines 14–151; source SHA-256 adc5acf0400a3aaad11cc254803291215309d517855d8955d4de43cffc163b2c; exact-source certificate Sapelo2 job 49296539.

import Mathlib.Algebra.Homology.LocalCohomology
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Tactic
import Definitions.Def_LPCA
import Definitions.Def_LPCA_Solutions_LPCA_CechNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechTerms_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechTerms_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_GradedLocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationConsequences_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedBasis_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedDimension_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexSplitting_Defs

set_option autoImplicit false

namespace LPCA

open scoped Classical

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]
variable (k : Type u) [Field k]

/-- Multiplication by the image of the polynomial variable, on the actual localization. -/
noncomputable def localizedVariableLinearMap
    (K : Complex V) (F : Finset V) (j : V) :
    LocalizedFaceRing k K F →ₗ[k] LocalizedFaceRing k K F where
  toFun z := algebraMap (FaceRing k K) (LocalizedFaceRing k K F)
    (variableClass k K j) * z
  map_add' x y := mul_add _ x y
  map_smul' c z := mul_smul_comm c _ z

theorem localizedVariable_mul_monomial
    (K : Complex V) (F : Finset V) (j : V) (m : V →₀ ℕ) (N : ℕ) :
    localizedVariableLinearMap k K F j (localizedMonomial k K F m N) =
      localizedMonomial k K F (Finsupp.single j 1 + m) N := by
  change algebraMap (FaceRing k K) (LocalizedFaceRing k K F) (variableClass k K j) *
    localizedMonomial k K F m N = _
  unfold localizedMonomial
  rw [IsLocalization.mul_mk'_eq_mk'_of_mul]
  unfold variableClass
  congr 1
  rw [← map_mul, MvPolynomial.monomial_single_add, pow_one]

theorem variable_mul_mem_piece
    (K : Complex V) (F : Finset V) (a b : V → ℤ) (j : V)
    (hab : ∀ v, b v = a v + if v = j then 1 else 0)
    {z : LocalizedFaceRing k K F} (hz : z ∈ localizedPiece k K F a) :
    localizedVariableLinearMap k K F j z ∈ localizedPiece k K F b := by
  have hle : localizedPiece k K F a ≤
      (localizedPiece k K F b).comap (localizedVariableLinearMap k K F j) := by
    apply Submodule.span_le.mpr
    rintro z ⟨m, N, hm, rfl⟩
    change localizedVariableLinearMap k K F j (localizedMonomial k K F m N) ∈
      localizedPiece k K F b
    rw [localizedVariable_mul_monomial]
    apply Submodule.subset_span
    refine ⟨Finsupp.single j 1 + m, N, ?_, rfl⟩
    intro v
    have h := hm v
    rw [hab v]
    by_cases hv : v = j
    · subst v
      simp only [Finsupp.add_apply, Finsupp.single_eq_same, Nat.cast_add,
        Nat.cast_one, ite_true]
      linear_combination hm j
    · simp only [Finsupp.add_apply, Finsupp.single_eq_of_ne hv, zero_add,
        if_neg hv, add_zero]
      exact h
  exact hle hz

/-- The genuine variable action restricted from degree a to degree b=a+e_j. -/
noncomputable def pieceVariableMap
    (K : Complex V) (F : Finset V) (a b : V → ℤ) (j : V)
    (hab : ∀ v, b v = a v + if v = j then 1 else 0) :
    localizedPiece k K F a →ₗ[k] localizedPiece k K F b where
  toFun z := ⟨localizedVariableLinearMap k K F j z.1,
    variable_mul_mem_piece k K F a b j hab z.2⟩
  map_add' x y := Subtype.ext (map_add (localizedVariableLinearMap k K F j) x.1 y.1)
  map_smul' c z := Subtype.ext (map_smul (localizedVariableLinearMap k K F j) c z.1)

theorem pieceVariableMap_coordinate
    (K : Complex V) (F : Finset V) (a b : V → ℤ) (j : V)
    (hab : ∀ v, b v = a v + if v = j then 1 else 0)
    (ha : LocalizationCriterion K F a) (hb : LocalizationCriterion K F b) (c : k) :
    pieceVariableMap k K F a b j hab (pieceCoordinateEquiv k K F a ha c) =
      pieceCoordinateEquiv k K F b hb c := by
  obtain ⟨m, N, hm, _, _⟩ := localizedPiece_nonzero_generator k K F a ha
  have hm' : ∀ v : V,
      (((Finsupp.single j 1 + m : V →₀ ℕ) v : ℕ) : ℤ) -
        (if v ∈ F then (N : ℤ) else 0) = b v := by
    intro v
    rw [hab v]
    have h := hm v
    by_cases hv : v = j
    · subst v
      simp only [Finsupp.add_apply, Finsupp.single_eq_same, Nat.cast_add,
        Nat.cast_one, ite_true]
      linear_combination hm j
    · simpa only [Finsupp.add_apply, Finsupp.single_eq_of_ne hv, zero_add,
        if_neg hv, add_zero] using h
  apply Subtype.ext
  change localizedVariableLinearMap k K F j (pieceCoordinateEquiv k K F a ha c).1 = _
  rw [pieceCoordinateEquiv_apply_val k K F a ha m N hm,
    pieceCoordinateEquiv_apply_val k K F b hb (Finsupp.single j 1 + m) N hm',
    map_smul, localizedVariable_mul_monomial]

theorem pieceVariableMap_coordinates_apply
    (K : Complex V) (F : Finset V) (a b : V → ℤ) (j : V)
    (hab : ∀ v, b v = a v + if v = j then 1 else 0)
    (hb : LocalizationCriterion K F b) (z : localizedPiece k K F a) :
    (pieceCoordinateEquiv k K F b hb).symm (pieceVariableMap k K F a b j hab z) =
      if ha : LocalizationCriterion K F a then
        (pieceCoordinateEquiv k K F a ha).symm z else 0 := by
  classical
  by_cases ha : LocalizationCriterion K F a
  · rw [dif_pos ha]
    have h := pieceVariableMap_coordinate k K F a b j hab ha hb
      ((pieceCoordinateEquiv k K F a ha).symm z)
    rw [LinearEquiv.apply_symm_apply] at h
    rw [h, LinearEquiv.symm_apply_apply]
  · rw [dif_neg ha]
    have hz : z = 0 := by
      apply Subtype.ext
      exact (Submodule.mem_bot k).mp
        (((localizedPiece_eq_bot_iff k K F a).mpr ha).le z.2)
    rw [hz, map_zero, map_zero]

noncomputable def actualTermVariableMap
    (K : Complex V) (T : Finset V) (a b : V → ℤ) (j : V) (p : ℕ)
    (hab : ∀ v, b v = a v + if v = j then 1 else 0) :
    LocalizedCechTerm k K T a p →ₗ[k] LocalizedCechTerm k K T b p where
  toFun y F := pieceVariableMap k K F.1 a b j hab (y F)
  map_add' x y := by
    funext F
    exact map_add (pieceVariableMap k K F.1 a b j hab) (x F) (y F)
  map_smul' c y := by
    funext F
    exact map_smul (pieceVariableMap k K F.1 a b j hab) c (y F)

theorem actualTermVariableMap_coordinates
    (K : Complex V) (T : Finset V) (a b : V → ℤ) (j : V) (p : ℕ)
    (hab : ∀ v, b v = a v + if v = j then 1 else 0)
    (y : LocalizedCechTerm k K T a p) (G : CechBasis K T b p) :
    actualToModel k K T b p (actualTermVariableMap k K T a b j p hab y) G =
      if ha : LocalizationCriterion K G.1 a then
        (pieceCoordinateEquiv k K G.1 a ha).symm (y ⟨G.1, G.2.1, G.2.2.1⟩)
      else 0 :=
  pieceVariableMap_coordinates_apply k K G.1 a b j hab G.2.2.2 _

theorem pieceVariableMap_localization
    (K : Complex V) (F G : Finset V) (hFG : F ⊆ G) (a b : V → ℤ) (j : V)
    (hab : ∀ v, b v = a v + if v = j then 1 else 0) (z : localizedPiece k K F a) :
    localizedPieceMap k K F G hFG b (pieceVariableMap k K F a b j hab z) =
      pieceVariableMap k K G a b j hab (localizedPieceMap k K F G hFG a z) := by
  apply Subtype.ext
  change localizationMap k K F G hFG
      (algebraMap (FaceRing k K) (LocalizedFaceRing k K F) (variableClass k K j) * z.1) =
    algebraMap (FaceRing k K) (LocalizedFaceRing k K G) (variableClass k K j) *
      localizationMap k K F G hFG z.1
  rw [map_mul, localizationMap_base]

end LPCA


