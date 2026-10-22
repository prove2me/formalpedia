-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_KoszulGrading_Defs
-- name    : LPCA_Solutions_LPCA_KoszulGrading_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:43:52.792637+00:00
-- url     : https://prove2.me/theorems/3eaf338e-d0ed-416e-baba-369e24e237cf
-- title:
--   Koszul Grading for localized persistent commutative algebra
-- statement:
--   This bundle supplies koszul Grading for localized persistent commutative algebra. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
--
--   The included constructions and necessary compatibility results are:
--
--   - Reindex the actual polynomial monomials by their shifted multidegree.
--   - An exhaustive, direct multidegree decomposition of the actual free module.
--   - The decomposition intertwines the actual polynomial differential with the scalar simplex boundaries, in every multidegree.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_KoszulGrading.lean, selected declarations in lines 18–138; source SHA-256 0db551a1e0650a82fd95dc31026994618f08f0cc6fb7d369652b9729f660231a; source certificate Sapelo2 job 49172236.

import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Homology.LocalCohomology
import Mathlib.Algebra.Homology.Single
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Ideal
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
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszul_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinatePowerCofinality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_GradedLocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulMultidegree_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationConsequences_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedBasis_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedDimension_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SignedSubsetMatrices_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SimplexContraction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SimplexDegreeContraction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexSplitting_Defs

set_option autoImplicit false
set_option maxHeartbeats 300000

namespace LPCA

open Module

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]
variable (k : Type u) [Field k]

/-- Reindex the actual polynomial monomials by their shifted multidegree. -/
noncomputable abbrev coordinateKoszulMonomialIndexEquiv (n : ℕ) (T : Finset V) (p : ℕ) :
    (Σ _F : CechSlot T p, V →₀ ℕ) ≃
      (Σ d : V →₀ ℕ, CechSlot (eligibleVertices n T d) p) where
  toFun x := ⟨x.2 + coordinateWeight n x.1.1,
    x.1.1, degree_eligible_of_subset n T x.1.1 x.1.2.1 x.2, x.1.2.2⟩
  invFun x := ⟨⟨x.2.1, (fun j hj => (Finset.mem_filter.mp (x.2.2.1 hj)).1), x.2.2.2⟩,
    normalizedKoszulExponent n x.1 x.2.1⟩
  left_inv x := by
    rcases x with ⟨F, m⟩
    change (⟨F, (m + coordinateWeight n F.1) - coordinateWeight n F.1⟩ :
      Σ _F : CechSlot T p, V →₀ ℕ) = ⟨F, m⟩
    rw [add_tsub_cancel_right]
  right_inv x := by
    have hd := normalizedKoszulExponent_add_weight n T x.1 x.2.1 x.2.2.1
    refine Sigma.ext ?_ ?_
    · exact hd
    · exact (Subtype.heq_iff_coe_eq (fun F => by
        change (F ⊆ eligibleVertices n T
          (normalizedKoszulExponent n x.1 x.2.1 + coordinateWeight n x.2.1) ∧ F.card = p) ↔
          (F ⊆ eligibleVertices n T x.1 ∧ F.card = p)
        rw [hd])).mpr rfl

noncomputable def coordinateKoszulMonomialBasis (T : Finset V) (p : ℕ) :
    Basis (Σ _F : CechSlot T p, V →₀ ℕ) k (CoordinateKoszulTerm k T p) :=
  Pi.basis (fun _ => MvPolynomial.basisMonomials V k)

abbrev GradedCoordinateKoszulTerm (n : ℕ) (T : Finset V) (p : ℕ) : Type u :=
  Π₀ d : V →₀ ℕ, (CechSlot (eligibleVertices n T d) p → k)

/-- An exhaustive, direct multidegree decomposition of the actual free module. -/
noncomputable def coordinateKoszulGradingEquiv (n : ℕ) (T : Finset V) (p : ℕ) :
    CoordinateKoszulTerm k T p ≃ₗ[k] GradedCoordinateKoszulTerm k n T p :=
  (coordinateKoszulMonomialBasis k T p).repr |>.trans
    (Finsupp.domLCongr (coordinateKoszulMonomialIndexEquiv n T p)) |>.trans
    (sigmaFinsuppLequivDFinsupp k) |>.trans
    (DFinsupp.mapRange.linearEquiv (fun d =>
      Finsupp.linearEquivFunOnFinite k k (CechSlot (eligibleVertices n T d) p)))

@[simp] theorem coordinateKoszulGradingEquiv_apply
    (n : ℕ) (T : Finset V) (p : ℕ) (y : CoordinateKoszulTerm k T p)
    (d : V →₀ ℕ) (F : CechSlot (eligibleVertices n T d) p) :
    coordinateKoszulGradingEquiv k n T p y d F =
      (y ⟨F.1, (fun j hj => (Finset.mem_filter.mp (F.2.1 hj)).1), F.2.2⟩).coeff
        (normalizedKoszulExponent n d F.1) := by
  change (Finsupp.domCongr (coordinateKoszulMonomialIndexEquiv n T p)
    ((coordinateKoszulMonomialBasis k T p).repr y)) ⟨d, F⟩ = _
  rw [Finsupp.domCongr_apply, Finsupp.equivMapDomain_apply]
  rw [coordinateKoszulMonomialBasis, Pi.basis_repr]
  rfl

theorem coordinateKoszul_normalized_coeff
    (rank : V ↪ ℕ) (n : ℕ) (T : Finset V) (d : V →₀ ℕ)
    (F G : Finset V) (hF : F ⊆ eligibleVertices n T d) (hGT : G ⊆ T)
    (y : MvPolynomial V k) :
    (coordinateKoszulCoefficient k rank n F G * y).coeff
        (normalizedKoszulExponent n d F) =
      if G ⊆ eligibleVertices n T d then
        cechCoefficient k rank F G * y.coeff (normalizedKoszulExponent n d G) else 0 := by
  classical
  by_cases hFG : F ⊆ G
  · by_cases hG : G ⊆ eligibleVertices n T d
    · rw [if_pos hG, coordinateKoszulCoefficient_monomial,
        MvPolynomial.coeff_monomial_mul']
      have hd := normalizedKoszulExponent_difference n T d F G hFG hG
      have hs : coordinateWeight n (G \ F) ≤ normalizedKoszulExponent n d F := by
        rw [← hd]
        exact le_add_right le_rfl
      rw [if_pos hs, ← hd, add_tsub_cancel_left]
    · rw [if_neg hG, coordinateKoszulCoefficient_monomial,
        MvPolynomial.coeff_monomial_mul']
      have hs : ¬coordinateWeight n (G \ F) ≤ normalizedKoszulExponent n d F := by
        intro h
        apply hG
        intro j hjG
        apply Finset.mem_filter.mpr
        refine ⟨hGT hjG, ?_⟩
        by_cases hjF : j ∈ F
        · exact (Finset.mem_filter.mp (hF hjF)).2
        · have hj := h j
          simpa [normalizedKoszulExponent, hjF, hjG] using hj
      rw [if_neg hs]
  · simp [coordinateKoszulCoefficient, cechCoefficient_zero_of_not_subset k rank F G hFG]

noncomputable def gradedCoordinateKoszulDifferential
    (rank : V ↪ ℕ) (n : ℕ) (T : Finset V) (p : ℕ) :
    GradedCoordinateKoszulTerm k n T (p + 1) →ₗ[k] GradedCoordinateKoszulTerm k n T p :=
  DirectSum.lmap (fun d => simplexDegreeBoundary k rank (eligibleVertices n T d) p)

/-- The decomposition intertwines the actual polynomial differential with
the scalar simplex boundaries, in every multidegree. -/
theorem coordinateKoszulGradingEquiv_differential
    (rank : V ↪ ℕ) (n : ℕ) (T : Finset V) (p : ℕ)
    (y : CoordinateKoszulTerm k T (p + 1)) :
    coordinateKoszulGradingEquiv k n T p (coordinateKoszulDifferential k rank n T p y) =
      gradedCoordinateKoszulDifferential k rank n T p
        (coordinateKoszulGradingEquiv k n T (p + 1) y) := by
  classical
  ext d F
  rw [coordinateKoszulGradingEquiv_apply]
  change (∑ G : CechSlot T (p + 1), coordinateKoszulCoefficient k rank n F.1 G.1 * y G).coeff
      (normalizedKoszulExponent n d F.1) = _
  rw [MvPolynomial.coeff_sum]
  conv_lhs =>
    arg 2
    ext G
    rw [coordinateKoszul_normalized_coeff k rank n T d F.1 G.1 F.2.1 G.2.1]
  change (∑ G : CechSlot T (p + 1), if G.1 ⊆ eligibleVertices n T d then _ else 0) =
    ∑ G : CechSlot (eligibleVertices n T d) (p + 1), _ * _
  symm
  apply Fintype.sum_of_injective
    (fun G : CechSlot (eligibleVertices n T d) (p + 1) =>
      (⟨G.1, (fun j hj => (Finset.mem_filter.mp (G.2.1 hj)).1), G.2.2⟩ : CechSlot T (p + 1)))
    (fun G H h => Subtype.ext (congrArg (fun x : CechSlot T (p + 1) => x.1) h))
  · intro G hG
    have hnot : ¬G.1 ⊆ eligibleVertices n T d := by
      intro h
      exact hG ⟨⟨G.1, h, G.2.2⟩, Subtype.ext rfl⟩
    rw [if_neg hnot]
  · intro G
    rw [if_pos G.2.1, coordinateKoszulGradingEquiv_apply]

end LPCA


