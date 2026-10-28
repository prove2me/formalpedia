-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_FaceCofaceIntervals_MinusOne20261025_Defs
-- name    : LPCA_Solutions_LPCA_FaceCofaceIntervals_MinusOne20261025_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-26T01:34:26.159875+00:00
-- url     : https://prove2.me/theorems/fc811d81-f17d-4a0d-97c3-07531ee5201e
-- title:
--   Face Coface Intervals — degree minus-one interval dependencies
-- statement:
--   Selected constructions and proved compatibility results for face coface intervals, used in the explicit degree-minus-one interval presentations. The formal declarations retain their exact objects, hypotheses and structure maps.
--
--   This is the empty-face-only complex, distinguished from the void complex.
--
--   The candidate vertices that can kill reduced degree minus one.
--
--   The right endpoint, with the minimum of the empty set equal to infinity.
--
--   The literal support interval, including the absent-face and zero-length
--   cases. All allowed cofaces have to be strictly later than the current time.
--
--   The single-interval support equals the explicit birth/death inequality:
--
--   Let $K$ be a finite downward-closed complex on a decidable vertex type, $f$ any real face weight, and $B,T$ finite vertex sets. Define $D=\min\{f(B\cup\{v\}):v\in T\setminus B,\ B\cup\{v\}\in K\}$ in $\mathbb R\cup\{+\infty\}$, with the empty minimum $+\infty$. For every real $t$, the literal support condition that $B\in K$, $f(B)\le t$, and every such coface has weight strictly greater than $t$ is equivalent to
--
--   $$B\in K\quad\text{and}\quad f(B)\le t<D.$$
--
--   This identifies the support used by the constructed interval functors with the paper's explicit half-open endpoint formula.
-- source:
--   https://arxiv.org/abs/2609.02858v1, Proposition3.12 and Corollary6.4, with their formalization dependencies. Certified Lean source: Solutions/LPCA_FaceCofaceIntervals.lean, selected declarations in lines 15–125; source SHA-256 7c54ef0fde4f3a9d08747a7a1b514bcd014db08fdb2bea07a66bf5f176b6a2e4; exact-source certificate Sapelo2 job 49311470.

import Mathlib
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Homology.Embedding.Restriction
import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.LocalCohomology
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Homology.Single
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Order.WithBot
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Ring
import Definitions.Def_LPCA
import Definitions.Def_LPCA_Proofs_BassLyubeznik_BassStatic_Common_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_BassStatic_redRestrictLin_dLin_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_BassStatic_signed_complex_d_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_BassStatic_signed_dLin_idxCongr_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_BassStatic_signed_restrictLin_dLin_Defs
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
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SrFamily_Common_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SrFamily_faceFamily_convex_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SrFamily_faceFamily_mono_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SrFamily_faceFamily_of_subset_Defs
import Definitions.Def_LPCA_Solutions_LPCA_AmbientCechComplex_Defs
import Definitions.Def_LPCA_Solutions_LPCA_AmbientFieldScalars_Defs
import Definitions.Def_LPCA_Solutions_LPCA_AmbientLocalizationTelescope_Defs
import Definitions.Def_LPCA_Solutions_LPCA_AmbientLocalizations_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechComplex_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechComplex_MinusOne20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechDifferential_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechDifferential_MinusOne20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechGradedInclusions_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechGradingColimit_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechSquareZero_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechTermGrading_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechTerms_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechTerms_MinusOne20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechTerms_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechVariableMaps_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechVariableNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechVariableNaturality_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CohomologyGradingInclusions_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementCech_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementCech_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementFaceNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementFaceNaturality_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementLocalizations_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementNaturality_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementRings_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementRings_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulAugmentation_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulExt_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulHom_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulResolution_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulTransitions_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszul_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinatePowerCofinality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ExactColimitHomologyLegs_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ExactColimitHomology_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionCech_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionCech_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionLocalizations_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionLocalizations_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FilteredColimitHomology_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FiltrationFunctor_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FinitePiColimit_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FinitePiGrading_Defs
import Definitions.Def_LPCA_Solutions_LPCA_GradedFaceRestrictionCech_Defs
import Definitions.Def_LPCA_Solutions_LPCA_GradedLocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HochsterActualComparison_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HochsterCochainComparison_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HochsterCohomology_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HochsterIncidence_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HochsterLinkTerms_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HochsterNonfaceVanishing_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HochsterSigns_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HomLocalizationColumns_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HomLocalizationDifferential_Defs
import Definitions.Def_LPCA_Solutions_LPCA_IntervalPersistence_MinusOne20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulAugmentationNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulExactness_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulGrading_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulHomDiagram_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulHomTransitions_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulMultidegree_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LaurentFaceEvaluation_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LegacyExtNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LinkIdentities_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalCohomologyCechComparison_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalCohomologyGrading_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalCohomologyKoszulComparison_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationConsequences_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationTelescope_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedBasis_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedDegreeSeparation_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedDimension_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedGradingSpan_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedGrading_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ModuleDirectSumColimit_Defs
import Definitions.Def_LPCA_Solutions_LPCA_NatRestrictionHomology_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ReducedFaceCochains_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ReducedFaceCochains_MinusOne20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SignedSubsetMatrices_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SimplexContraction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SimplexDegreeContraction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SupportCohomologyPieces_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VariableMultiplication_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexSplitting_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexSplitting_MinusOne20261025_Defs

set_option autoImplicit false

namespace LPCA

universe u

variable {V : Type u} [DecidableEq V]

/-- This is the empty-face-only complex, distinguished from the void complex. -/
def EmptyFaceOnly (K : Complex V) : Prop := K.faces = {∅}

theorem emptyFaceOnly_iff (K : Complex V) :
    EmptyFaceOnly K ↔ ∅ ∈ K.faces ∧ ∀ v : V, {v} ∉ K.faces := by
  constructor
  · intro h
    simp [EmptyFaceOnly] at h
    simp [h]
  · rintro ⟨he, hv⟩
    apply Finset.ext
    intro F
    constructor
    · intro hF
      have hzero : F = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro v hvm
        exact hv v (K.down_closed hF (Finset.singleton_subset_iff.mpr hvm))
      simp [hzero]
    · intro hF
      have hzero : F = ∅ := Finset.mem_singleton.mp hF
      simpa [hzero] using he

theorem mem_link_faces_iff (K : Complex V) (B F : Finset V) :
    F ∈ (link K B).faces ↔ Disjoint F B ∧ F ∪ B ∈ K.faces := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    exact Finset.mem_filter.mpr
      ⟨K.down_closed h.2 Finset.subset_union_left, h⟩

/-- The candidate vertices that can kill reduced degree minus one. -/
def allowedCofaceVertices (K : Complex V) (B T : Finset V) : Finset V :=
  T.filter (fun v => v ∉ B ∧ B ∪ {v} ∈ K.faces)

/-- The right endpoint, with the minimum of the empty set equal to infinity. -/
noncomputable def faceCofaceDeath (K : Complex V) (f : Finset V → ℝ)
    (B T : Finset V) : WithTop ℝ :=
  (allowedCofaceVertices K B T).inf (fun v => (f (B ∪ {v}) : WithTop ℝ))

/-- The literal support interval, including the absent-face and zero-length
cases. All allowed cofaces have to be strictly later than the current time. -/
def faceCofaceInterval (K : Complex V) (f : Finset V → ℝ) (B T : Finset V) : Set ℝ :=
  {t | B ∈ K.faces ∧ f B ≤ t ∧
    ∀ v ∈ T, v ∉ B → B ∪ {v} ∈ K.faces → t < f (B ∪ {v})}

theorem faceCofaceInterval_isInterval (K : Complex V) (f : Finset V → ℝ)
    (B T : Finset V) : IsTimeInterval (faceCofaceInterval K f B T) := by
  intro s t w hst htw hs hw
  exact ⟨hs.1, hs.2.1.trans hst,
    fun v hv hvB hvK => lt_of_le_of_lt htw (hw.2.2 v hv hvB hvK)⟩

theorem mem_faceCofaceInterval_iff (K : Complex V) (f : Finset V → ℝ)
    (B T : Finset V) (t : ℝ) :
    t ∈ faceCofaceInterval K f B T ↔
      B ∈ K.faces ∧ f B ≤ t ∧ (t : WithTop ℝ) < faceCofaceDeath K f B T := by
  classical
  simp only [faceCofaceInterval, Set.mem_setOf_eq, faceCofaceDeath,
    Finset.lt_inf_iff (show (t : WithTop ℝ) < ⊤ by simp),
    allowedCofaceVertices, Finset.mem_filter, and_imp, WithTop.coe_lt_coe]

theorem faceCofaceDeath_of_no_cofaces (K : Complex V) (f : Finset V → ℝ)
    (B T : Finset V) (h : allowedCofaceVertices K B T = ∅) :
    faceCofaceDeath K f B T = ⊤ := by
  simp [faceCofaceDeath, h]

theorem faceCofaceInterval_empty_of_not_face (K : Complex V) (f : Finset V → ℝ)
    (B T : Finset V) (h : B ∉ K.faces) : faceCofaceInterval K f B T = ∅ := by
  ext t
  simp [faceCofaceInterval, h]

theorem faceCofaceInterval_empty_of_equal_birth_death (K : Complex V)
    (f : Finset V → ℝ) (B T : Finset V)
    (h : faceCofaceDeath K f B T = (f B : WithTop ℝ)) :
    faceCofaceInterval K f B T = ∅ := by
  ext t
  rw [mem_faceCofaceInterval_iff, h]
  simp only [WithTop.coe_lt_coe, Set.mem_empty_iff_false, iff_false, not_and]
  intro _ hbt htb
  exact (not_lt_of_ge hbt) htb

variable {W : Type u} [DecidableEq W] [Fintype W]

theorem emptyFaceOnly_restrict_link_level_iff (K : Complex V)
    (f : Finset V → ℝ) (hf : FiltrationMonotone K f) (B : Finset V)
    (e : W ↪ V) (t : ℝ) :
    EmptyFaceOnly (restrictComplex (link (level K f hf t) B) e) ↔
      t ∈ faceCofaceInterval K f B (Finset.univ.map e) := by
  classical
  rw [emptyFaceOnly_iff]
  simp only [mem_restrictComplex, Finset.map_empty, Finset.map_singleton,
    mem_link_faces_iff, Finset.disjoint_empty_left, Finset.empty_union, true_and,
    Finset.disjoint_singleton_left]
  simp only [level, Finset.mem_filter, faceCofaceInterval, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨hB, hBt⟩, hv⟩
    refine ⟨hB, hBt, ?_⟩
    intro v hvT hvB hvK
    obtain ⟨w, _, rfl⟩ := Finset.mem_map.mp hvT
    exact lt_of_not_ge (fun hvt => hv w ⟨hvB, by
      simpa only [Finset.union_comm] using And.intro hvK hvt⟩)
  · rintro ⟨hB, hBt, hv⟩
    refine ⟨⟨hB, hBt⟩, ?_⟩
    intro w hw
    have hwK : B ∪ {e w} ∈ K.faces := by
      simpa only [Finset.union_comm] using hw.2.1
    have hwt : f (B ∪ {e w}) ≤ t := by
      simpa only [Finset.union_comm] using hw.2.2
    exact (not_lt_of_ge hwt)
      (hv (e w) (Finset.mem_map.mpr ⟨w, Finset.mem_univ w, rfl⟩) hw.1 hwK)

end LPCA


