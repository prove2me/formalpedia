-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszul_Defs
-- name    : LPCA_Solutions_LPCA_CoordinateKoszul_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:34:32.572743+00:00
-- url     : https://prove2.me/theorems/df07bb10-ad5f-4b1d-abb6-6e8ebdd6349c
-- title:
--   Coordinate Koszul for localized persistent commutative algebra
-- statement:
--   This bundle supplies coordinate Koszul for localized persistent commutative algebra. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
--
--   The included constructions and necessary compatibility results are:
--
--   - The finite free p-th term of the coordinate-power Koszul chain complex.
--   - Weighted incidence from the (p+1)-subset G to the p-subset F. The scalar sign lies in k; the coordinate powers lie in the ambient polynomial ring.
--   - This is the finite free chain complex. Its augmentation and exactness are separate targets; defining it does not assert that it is a resolution.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_CoordinateKoszul.lean, selected declarations in lines 17–124; source SHA-256 bd11e5719d2011d0878d250bd3fe5e682bcbd002cbddaf00763be6998669a3de; source certificate Sapelo2 job 49172236.

import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.LocalCohomology
import Mathlib.Algebra.Homology.Single
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic
import Definitions.Def_LPCA
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_Common_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_dd_sum_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_eps_insert_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_eps_mul_self_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_exists_insert_of_inc_ne_zero_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_hc_inc_sum_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_eq_zero_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_inc_sum_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_insert_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_sdiff_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_erase_self_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_insert_of_gt_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_insert_of_lt_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_sdiff_add_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechDifferential_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechSquareZero_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechTerms_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinatePowerCofinality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_GradedLocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationConsequences_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedBasis_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedDimension_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SignedSubsetMatrices_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexSplitting_Defs

set_option autoImplicit false

namespace LPCA

open CategoryTheory

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]
variable (k : Type u) [Field k]

/-- The finite free p-th term of the coordinate-power Koszul chain complex. -/
abbrev CoordinateKoszulTerm (T : Finset V) (p : ℕ) : Type u :=
  CechSlot T p → MvPolynomial V k

/-- Weighted incidence from the (p+1)-subset G to the p-subset F.
The scalar sign lies in k; the coordinate powers lie in the ambient polynomial ring. -/
noncomputable def coordinateKoszulCoefficient
    (rank : V ↪ ℕ) (n : ℕ) (F G : Finset V) : MvPolynomial V k :=
  MvPolynomial.C (cechCoefficient k rank F G) *
    ∏ j ∈ G \ F, MvPolynomial.X j ^ (n + 1)

private theorem difference_product (n : ℕ) (F G H : Finset V)
    (hFG : F ⊆ G) (hGH : G ⊆ H) :
    (∏ j ∈ G \ F, (MvPolynomial.X j : MvPolynomial V k) ^ (n + 1)) *
        (∏ j ∈ H \ G, MvPolynomial.X j ^ (n + 1)) =
      ∏ j ∈ H \ F, MvPolynomial.X j ^ (n + 1) := by
  have hd : Disjoint (H \ G) (G \ F) := by
    apply Finset.disjoint_left.mpr
    intro j hjH hjG
    exact (Finset.mem_sdiff.mp hjH).2 (Finset.mem_sdiff.mp hjG).1
  rw [mul_comm, ← Finset.prod_union hd, Finset.sdiff_union_sdiff_cancel hGH hFG]

theorem coordinateKoszulCoefficient_mul
    (rank : V ↪ ℕ) (n : ℕ) (F G H : Finset V) :
    coordinateKoszulCoefficient k rank n F G * coordinateKoszulCoefficient k rank n G H =
      MvPolynomial.C (cechCoefficient k rank F G * cechCoefficient k rank G H) *
        ∏ j ∈ H \ F, MvPolynomial.X j ^ (n + 1) := by
  by_cases hFG : F ⊆ G
  · by_cases hGH : G ⊆ H
    · unfold coordinateKoszulCoefficient
      rw [map_mul]
      calc
        _ = (MvPolynomial.C (cechCoefficient k rank F G) *
            MvPolynomial.C (cechCoefficient k rank G H)) *
            ((∏ j ∈ G \ F, MvPolynomial.X j ^ (n + 1)) *
              ∏ j ∈ H \ G, MvPolynomial.X j ^ (n + 1)) := by ring
        _ = _ := by rw [difference_product k n F G H hFG hGH]
    · simp [coordinateKoszulCoefficient, cechCoefficient_zero_of_not_subset k rank G H hGH]
  · simp [coordinateKoszulCoefficient, cechCoefficient_zero_of_not_subset k rank F G hFG]

theorem coordinateKoszulCoefficient_square
    (rank : V ↪ ℕ) (n : ℕ) (T : Finset V) (p : ℕ)
    (F : CechSlot T p) (H : CechSlot T (p + 1 + 1)) :
    ∑ G : CechSlot T (p + 1),
      coordinateKoszulCoefficient k rank n F.1 G.1 *
        coordinateKoszulCoefficient k rank n G.1 H.1 = 0 := by
  simp_rw [coordinateKoszulCoefficient_mul]
  rw [← Finset.sum_mul, ← map_sum, cechCoefficient_square_slots, map_zero, zero_mul]

noncomputable def coordinateKoszulDifferential
    (rank : V ↪ ℕ) (n : ℕ) (T : Finset V) (p : ℕ) :
    CoordinateKoszulTerm k T (p + 1) →ₗ[MvPolynomial V k] CoordinateKoszulTerm k T p where
  toFun y F := ∑ G : CechSlot T (p + 1), coordinateKoszulCoefficient k rank n F.1 G.1 * y G
  map_add' x y := by
    funext F
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c y := by
    funext F
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro G _
    ring

theorem coordinateKoszulDifferential_square
    (rank : V ↪ ℕ) (n : ℕ) (T : Finset V) (p : ℕ)
    (y : CoordinateKoszulTerm k T (p + 1 + 1)) :
    coordinateKoszulDifferential k rank n T p
      (coordinateKoszulDifferential k rank n T (p + 1) y) = 0 := by
  classical
  funext F
  change (∑ G : CechSlot T (p + 1), coordinateKoszulCoefficient k rank n F.1 G.1 *
    ∑ H : CechSlot T (p + 1 + 1), coordinateKoszulCoefficient k rank n G.1 H.1 * y H) = 0
  simp_rw [Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro H _
  rw [← Finset.sum_mul, coordinateKoszulCoefficient_square, zero_mul]

theorem coordinateKoszulDifferential_comp_zero
    (rank : V ↪ ℕ) (n : ℕ) (T : Finset V) (p : ℕ) :
    (coordinateKoszulDifferential k rank n T p).comp
      (coordinateKoszulDifferential k rank n T (p + 1)) = 0 := by
  apply LinearMap.ext
  exact coordinateKoszulDifferential_square k rank n T p

/-- This is the finite free chain complex. Its augmentation and exactness
are separate targets; defining it does not assert that it is a resolution. -/
noncomputable def coordinateKoszulComplex
    (rank : V ↪ ℕ) (n : ℕ) (T : Finset V) : ChainComplex (ModuleCat (MvPolynomial V k)) ℕ :=
  ChainComplex.of
    (fun p => ModuleCat.of (MvPolynomial V k) (CoordinateKoszulTerm k T p))
    (fun p => ModuleCat.ofHom (coordinateKoszulDifferential k rank n T p))
    (fun p => by
      apply ModuleCat.hom_ext
      exact coordinateKoszulDifferential_comp_zero k rank n T p)

theorem coordinateKoszulComplex_d
    (rank : V ↪ ℕ) (n : ℕ) (T : Finset V) (p : ℕ) :
    (coordinateKoszulComplex k rank n T).d (p + 1) p =
      ModuleCat.ofHom (coordinateKoszulDifferential k rank n T p) :=
  ChainComplex.of_d
    (fun q => ModuleCat.of (MvPolynomial V k) (CoordinateKoszulTerm k T q))
    (fun q => ModuleCat.ofHom (coordinateKoszulDifferential k rank n T q)) p

noncomputable instance coordinateKoszulComplex_projective
    (rank : V ↪ ℕ) (n : ℕ) (T : Finset V) (p : ℕ) :
    Projective ((coordinateKoszulComplex k rank n T).X p) :=
  ModuleCat.projective_of_free (Pi.basisFun (MvPolynomial V k) (CechSlot T p))

end LPCA


