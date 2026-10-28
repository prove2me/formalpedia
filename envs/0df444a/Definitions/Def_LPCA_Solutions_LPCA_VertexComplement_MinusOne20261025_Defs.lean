-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_VertexComplement_MinusOne20261025_Defs
-- name    : LPCA_Solutions_LPCA_VertexComplement_MinusOne20261025_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-26T01:34:22.380485+00:00
-- url     : https://prove2.me/theorems/fad3426b-37fc-46a4-ae78-b81cce1da806
-- title:
--   Vertex Complement — degree minus-one interval dependencies
-- statement:
--   Selected constructions and proved compatibility results for vertex complement, used in the explicit degree-minus-one interval presentations. The formal declarations retain their exact objects, hypotheses and structure maps.
--
--   The positive-coordinate Cech splitting uses the actual complement link ring.
--   The erased i-coordinate is the separate external shift recorded by a i.
--
--   The coordinate support of the vertex prime, with the remaining vertices explicit.
--
--   The zero-coordinate Cech splitting, now on the actual complement vertex type.
-- source:
--   https://arxiv.org/abs/2609.02858v1, Proposition3.12 and Corollary6.4, with their formalization dependencies. Certified Lean source: Solutions/LPCA_VertexComplement.lean, selected declarations in lines 14–97; source SHA-256 23f0cb9a5fb1c00a65312a253f8ca4173927094324ae3cb4a4ab7519ec197b0c; exact-source certificate Sapelo2 job 49311470.

import Mathlib
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.LocalCohomology
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
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
import Definitions.Def_LPCA_Solutions_LPCA_CechComplex_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechComplex_MinusOne20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechDifferential_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechDifferential_MinusOne20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechSquareZero_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechTerms_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechTerms_MinusOne20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechTerms_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechVariableMaps_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechVariableNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechVariableNaturality_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementCech_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementCech_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementLocalizations_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementNaturality_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementRings_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementRings_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_GradedLocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationConsequences_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedBasis_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedDimension_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VariableMultiplication_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexComplement_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexSplitting_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexSplitting_MinusOne20261025_Defs

set_option autoImplicit false

namespace LPCA

open CategoryTheory CategoryTheory.Limits

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]
variable (k : Type u) [Field k]

/-- The coordinate support of the vertex prime, with the remaining vertices explicit. -/
noncomputable def vertexSupport (i : V) : Finset V :=
  (Finset.univ : Finset {v : V // v ≠ i}).map (complementEmbedding i)

theorem vertexSupport_eq_erase (i : V) : vertexSupport i = Finset.univ.erase i := by
  ext v
  simp [vertexSupport, complementEmbedding]

theorem vertex_not_mem_support (i : V) : i ∉ vertexSupport i := by
  rw [vertexSupport_eq_erase]
  exact Finset.notMem_erase _ _



theorem link_faces_in_complement (K : Complex V) (i : V) :
    ∀ F ∈ (link K {i}).faces, ∀ v ∈ F, v ∈ Set.range (complementEmbedding i) := by
  intro F hF v hv
  refine ⟨⟨v, ?_⟩, rfl⟩
  intro hvi
  have hd := (Finset.mem_filter.mp hF).2.1
  exact Finset.disjoint_left.mp hd hv (by simp [hvi])

theorem zero_outside_complement (i : V) (a : V → ℤ) (ha : a i = 0) :
    ∀ v, v ∉ Set.range (complementEmbedding i) → a v = 0 := by
  intro v hv
  by_cases hvi : v = i
  · simpa only [hvi] using ha
  · exact False.elim (hv ⟨⟨v, hvi⟩, rfl⟩)

theorem update_restrict_complement (i : V) (a : V → ℤ) :
    Function.update a i 0 ∘ complementEmbedding i = a ∘ complementEmbedding i := by
  funext v
  exact Function.update_of_ne v.2 _ _

/-- The zero-coordinate Cech splitting, now on the actual complement vertex type. -/
noncomputable def zeroDegreeComplementCechComplexIso
    (rank : V ↪ ℕ) (K : Complex V) (i : V) (a : V → ℤ) (ha : a i = 0) :
    localizedCechComplex k rank K (vertexSupport i) a ≅
      localizedCechComplex k ((complementEmbedding i).trans rank)
        (restrictComplex (deletion K i) (complementEmbedding i))
        Finset.univ (a ∘ complementEmbedding i) :=
  zeroDegreeCechComplexIso k rank K i (vertexSupport i) a
    (vertex_not_mem_support i) ha ≪≫
      restrictionCechComplexIso k rank (deletion K i) (complementEmbedding i)
        (deletion_faces_in_complement K i) Finset.univ a (zero_outside_complement i a ha)

/-- The positive-coordinate Cech splitting uses the actual complement link ring.
The erased i-coordinate is the separate external shift recorded by a i. -/
noncomputable def positiveDegreeComplementCechComplexIso
    (rank : V ↪ ℕ) (K : Complex V) (i : V) (a : V → ℤ) (ha : 0 < a i) :
    localizedCechComplex k rank K (vertexSupport i) a ≅
      localizedCechComplex k ((complementEmbedding i).trans rank)
        (restrictComplex (link K {i}) (complementEmbedding i))
        Finset.univ (a ∘ complementEmbedding i) :=
  positiveDegreeCechComplexIso k rank K i (vertexSupport i) a
    (vertex_not_mem_support i) ha ≪≫
      restrictionCechComplexIso k rank (link K {i}) (complementEmbedding i)
        (link_faces_in_complement K i) Finset.univ (Function.update a i 0)
        (zero_outside_complement i (Function.update a i 0) (by simp)) ≪≫
      eqToIso (congrArg
        (fun b => localizedCechComplex k ((complementEmbedding i).trans rank)
          (restrictComplex (link K {i}) (complementEmbedding i)) Finset.univ b)
        (update_restrict_complement i a))

noncomputable def zeroDegreeComplementCechCohomologyIso
    (rank : V ↪ ℕ) (K : Complex V) (i : V) (a : V → ℤ) (q : ℕ) (ha : a i = 0) :
    localizedCechCohomology k rank K (vertexSupport i) a q ≅
      localizedCechCohomology k ((complementEmbedding i).trans rank)
        (restrictComplex (deletion K i) (complementEmbedding i))
        Finset.univ (a ∘ complementEmbedding i) q :=
  (HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.up ℕ) q).mapIso
    (zeroDegreeComplementCechComplexIso k rank K i a ha)

noncomputable def positiveDegreeComplementCechCohomologyIso
    (rank : V ↪ ℕ) (K : Complex V) (i : V) (a : V → ℤ) (q : ℕ) (ha : 0 < a i) :
    localizedCechCohomology k rank K (vertexSupport i) a q ≅
      localizedCechCohomology k ((complementEmbedding i).trans rank)
        (restrictComplex (link K {i}) (complementEmbedding i))
        Finset.univ (a ∘ complementEmbedding i) q :=
  (HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.up ℕ) q).mapIso
    (positiveDegreeComplementCechComplexIso k rank K i a ha)



end LPCA


