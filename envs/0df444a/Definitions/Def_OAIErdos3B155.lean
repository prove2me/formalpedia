-- Prove2me | Definitions.Def_OAIErdos3B155
-- name    : OAIErdos3B155
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-10T00:29:55.479933+00:00
-- url     : https://prove2.me/theorems/02dda3b6-43d4-4cbd-a4f0-c6ca861c1765
-- title:
--   OpenAI Erdős-3 split, definitions bundle 156 of 177
-- statement:
--   Definitions bundle 156 of 177 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B154`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 156 available.
--
--   Modules: `OAI.Erdos3.BiasedNativeTerminalSpec`, `OAI.Erdos3.BiasedSynchronizedSquareFamilySpec`, `OAI.Erdos3.NativeCorrelationStructure.multilinearFactor`, `OAI.Erdos3.NativeCrossWitnesses.exists_integer_quadruple_interval`, `OAI.Erdos3.NativeCrossWitnesses.exists_integer_quadruple_interval_budget`, `OAI.Erdos3.NativeCrossWitnesses.extension_quadruple_integer`, `OAI.Erdos3.NativeCrossWitnesses.integerLower`, `OAI.Erdos3.NativeCrossWitnesses.integerLower_val`, `OAI.Erdos3.NativeCrossWitnesses.integerProduct`, `OAI.Erdos3.NativeCrossWitnesses.integerProduct_fourPoint_factorization`, `OAI.Erdos3.NativeCrossWitnesses.integerProduct_val`, `OAI.Erdos3.NativeMixedReductionData.double_translation`, `OAI.Erdos3.NativeMixedReductionData.reduce_family`, `OAI.Erdos3.NativeMixedReductionData.reduce_quadruple`, `OAI.Erdos3.NativeMixedReductionData.reductionCodeEquiv`, `OAI.Erdos3.NativeMixedReductionData.reductionCodeFintype`, `OAI.Erdos3.NativeMixedReductionData.reductionCode_card`, `OAI.Erdos3.NativeMixedReductionData.translationCodeEquiv`, `OAI.Erdos3.NativeMixedReductionData.translationCodeFintype`, `OAI.Erdos3.NativeMixedReductionData.translationCode_card`, `OAI.Erdos3.NilpotentLieFiltration.PointwiseSynchronizedSquareFamilySpec`, `OAI.Erdos3.NilpotentLieFiltration.ReducedSquareRelativeCongruent`, `OAI.Erdos3.NilpotentLieFiltration.SynchronizedReducedSquareFamilySpec`, `OAI.Erdos3.NilpotentLieFiltration.associatedGradedBasis_repr_of_basis_reindex`, `OAI.Erdos3.NilpotentLieFiltration.exists_pointwise_synchronized_square_family`, `OAI.Erdos3.NilpotentLieFiltration.exists_synchronized_reduced_square_family`, `OAI.Erdos3.NilpotentLieFiltration.graded_submodule_iff_of_basis_reindex`, `OAI.Erdos3.NilpotentLieFiltration.graded_top_annihilation_iff_of_basis_reindex`, `OAI.Erdos3.NilpotentLieFiltration.graded_top_annihilation_reindex_iff`, `OAI.Erdos3.NilpotentLieFiltration.squareTopQuotientModel_factorization_iff`, `OAI.Erdos3.NilpotentLieFiltration.squareTopQuotientModel_graded_iff`, `OAI.Erdos3.NilpotentLieFiltration.squareTopQuotientModel_graded_logHeight`, `OAI.Erdos3.NilpotentLieFiltration.squareTopQuotientModel_graded_repr`, `OAI.Erdos3.NilpotentLieFiltration.squareTopQuotientModel_top_annihilation_iff`, `OAI.Erdos3.NilpotentLieFiltration.symbolFactorizationIn_iff_of_basis_reindex`, `OAI.Erdos3.NilpotentLieFiltration.symbolFactorizationIn_reindex_iff`, `OAI.Erdos3.NilpotentLieFiltration.symbolFastIn_reducedSquareRealSymbolHom`, `OAI.Erdos3.RationalFilteredNilmanifold.HasFixedNativeSquareFactors.canonical_factors`, `OAI.Erdos3.RationalFilteredNilmanifold.HasFixedNativeSquareFactors.fullFast_top_frequency`, `OAI.Erdos3.RationalFilteredNilmanifold.MarkedRefilteredNativeDiagramData`, `OAI.Erdos3.RationalFilteredNilmanifold.SynchronizedNativeSquareData`, `OAI.Erdos3.RationalFilteredNilmanifold.SynchronizedNativeSquareData.mono`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_controlled_marked_top_quotient`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_marked_refiltered_native_diagram`, `OAI.Erdos3.SynchronizedNativeCommonCoefficientSpec`, `OAI.Erdos3.SynchronizedNativeSquareFamilySpec`, `OAI.Erdos3.SynchronizedNativeTerminalSpec`, `OAI.Erdos3.cyclicBranchOffset`, `OAI.Erdos3.cyclicTranslationOffset_eq_branch`, `OAI.Erdos3.exists_biased_native_terminal`, `OAI.Erdos3.exists_biased_synchronized_square_family`, `OAI.Erdos3.exists_fourPoint_integer_interval`, `OAI.Erdos3.exists_integer_multilinear_quadruples`, `OAI.Erdos3.exists_integer_multilinear_quadruples_with_equivalence`, `OAI.Erdos3.exists_interval_split_budget`, `OAI.Erdos3.exists_synchronized_native_common_coefficients`, `OAI.Erdos3.exists_synchronized_native_square_family`, `OAI.Erdos3.exists_synchronized_native_terminal`, `OAI.Erdos3.native_interval_weight_pairs`, `OAI.Erdos3.restrictedLieMap_coordinate_logHeight`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B156

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ReindexSymbolFactorization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (e : ι ≃ κ)
  (hF' : ∀ j, F.layer j = Submodule.span ℚ ((b.reindex e) '' {k | j ≤ ω (e.symm k)}))

theorem symbolFactorizationIn_reindex_iff (T : σ → ℝ)
    (X : F.RealPolynomialSymbolGroup (fun _ : σ => 1)) (p : ℝ) (l : ℕ)
    (W : LieSubalgebra ℚ F.AssociatedGraded) :
    F.SymbolFactorizationIn (b.reindex e) (fun k => ω (e.symm k)) hF' T X p l W ↔
      F.SymbolFactorizationIn b ω hF T X p l W := by
  simp only [SymbolFactorizationIn,
    F.symbolSlowBound_reindex_iff b ω hF e hF',
    F.symbolRationalGrid_reindex_iff b ω hF e hF',
    F.symbolPointwiseSubalgebra_basis_independent b ω hF
      (b.reindex e) (fun k => ω (e.symm k)) hF']

theorem graded_top_annihilation_reindex_iff (η : L →ₗ[ℚ] ℚ)
    (W : LieSubalgebra ℚ F.AssociatedGraded) :
    (∀ x ∈ W, basisGradeProjection
        (F.associatedGradedBasis (b.reindex e) (fun k => ω (e.symm k)) hF')
        (fun k => ω (e.symm k)) s x = x →
      F.gradedFrequency (b.reindex e) (fun k => ω (e.symm k)) hF' η x = 0) ↔
    (∀ x ∈ W, basisGradeProjection (F.associatedGradedBasis b ω hF) ω s x = x →
      F.gradedFrequency b ω hF η x = 0) := by
  rw [F.associatedGradedBasis_reindex b ω hF e hF',
    F.gradedFrequency_reindex b ω hF e hF' η]
  simp only [basisGradeProjection_reindex]

theorem symbolFactorizationIn_iff_of_basis_reindex (c : Basis κ ℚ L) (ν : κ → ℕ)
    (hC : ∀ j, F.layer j = Submodule.span ℚ (c '' {k | j ≤ ν k}))
    (hc : c = b.reindex e) (hν : ν = fun k => ω (e.symm k))
    (T : σ → ℝ) (X : F.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (p : ℝ) (l : ℕ) (W : LieSubalgebra ℚ F.AssociatedGraded) :
    F.SymbolFactorizationIn c ν hC T X p l W ↔ F.SymbolFactorizationIn b ω hF T X p l W := by
  subst c
  subst ν
  exact F.symbolFactorizationIn_reindex_iff b ω hF e hC T X p l W

theorem graded_top_annihilation_iff_of_basis_reindex (c : Basis κ ℚ L) (ν : κ → ℕ)
    (hC : ∀ j, F.layer j = Submodule.span ℚ (c '' {k | j ≤ ν k}))
    (hc : c = b.reindex e) (hν : ν = fun k => ω (e.symm k))
    (η : L →ₗ[ℚ] ℚ) (W : LieSubalgebra ℚ F.AssociatedGraded) :
    (∀ x ∈ W, basisGradeProjection (F.associatedGradedBasis c ν hC) ν s x = x →
      F.gradedFrequency c ν hC η x = 0) ↔
    (∀ x ∈ W, basisGradeProjection (F.associatedGradedBasis b ω hF) ω s x = x →
      F.gradedFrequency b ω hF η x = 0) := by
  subst c
  subst ν
  exact F.graded_top_annihilation_reindex_iff b ω hF e hC η W

theorem graded_submodule_iff_of_basis_reindex (c : Basis κ ℚ L) (ν : κ → ℕ)
    (hC : ∀ j, F.layer j = Submodule.span ℚ (c '' {k | j ≤ ν k}))
    (hc : c = b.reindex e) (hν : ν = fun k => ω (e.symm k))
    (U : Submodule ℚ F.AssociatedGraded) :
    BasisGradedSubmodule (F.associatedGradedBasis c ν hC) ν U ↔
      BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω U := by
  subst c
  subst ν
  rw [F.associatedGradedBasis_reindex b ω hF e hC]
  exact basisGradedSubmodule_reindex_iff (F.associatedGradedBasis b ω hF) ω e U

theorem associatedGradedBasis_repr_of_basis_reindex (c : Basis κ ℚ L) (ν : κ → ℕ)
    (hC : ∀ j, F.layer j = Submodule.span ℚ (c '' {k | j ≤ ν k}))
    (hc : c = b.reindex e) (hν : ν = fun k => ω (e.symm k))
    (x : F.AssociatedGraded) (i : ι) :
    (F.associatedGradedBasis c ν hC).repr x (e i) =
      (F.associatedGradedBasis b ω hF).repr x i := by
  subst c
  subst ν
  rw [F.associatedGradedBasis_reindex b ω hF e hC,
    Basis.repr_reindex_apply, Equiv.symm_apply_apply]

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SquareQuotientHeightTransport
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (Γ : Subgroup F.squareFiltration.Group) (N : ℕ) (hN : 0 < N)
  (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates (F.squareFinBasis b ω (hF 2)) Γ)
  (hout : bchSubgroupCoordinates (F.squareFinBasis b ω (hF 2)) Γ ⊆ denominatorGrid N)

local notation "Q" => F.squareFiltration.topQuotientModel (F.squareFinBasis b ω (hF 2))
  (squareFinWeight ω) (F.squareFinBasis_layers b ω hF) Γ N hN hin hout
local notation "hQ" => F.squareFiltration.topQuotientModel_basis_layers
  (F.squareFinBasis b ω (hF 2)) (squareFinWeight ω) (F.squareFinBasis_layers b ω hF) Γ N hN hin hout
local notation "bq" => F.reducedSquareBasis b ω hF
local notation "ωq" => (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val i))
local notation "hq" => F.reducedSquareBasis_layers b ω hF

theorem squareTopQuotientModel_factorization_iff (T : σ → ℝ)
    (X : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (p : ℝ) (l : ℕ) (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded) :
    (Q).filtration.SymbolFactorizationIn (Q).basis
        (quotientFinWeight (squareFinWeight ω) {i | s + 1 ≤ squareFinWeight ω i}) hQ T X p l W ↔
      F.squareFiltration.quotientTop.SymbolFactorizationIn bq ωq hq T X p l W := by
  exact F.squareFiltration.quotientTop.symbolFactorizationIn_iff_of_basis_reindex bq ωq hq
    (reducedSquareFinIndexEquiv s ω) (Q).basis
    (quotientFinWeight (squareFinWeight ω) {i | s + 1 ≤ squareFinWeight ω i}) hQ
    (F.squareTopQuotientModel_basis_reindex b ω hF Γ N hN hin hout) rfl T X p l W

theorem squareTopQuotientModel_graded_iff
    (U : Submodule ℚ F.squareFiltration.quotientTop.AssociatedGraded) :
    BasisGradedSubmodule ((Q).filtration.associatedGradedBasis (Q).basis
        (quotientFinWeight (squareFinWeight ω) {i | s + 1 ≤ squareFinWeight ω i}) hQ)
        (quotientFinWeight (squareFinWeight ω) {i | s + 1 ≤ squareFinWeight ω i}) U ↔
      BasisGradedSubmodule (F.squareFiltration.quotientTop.associatedGradedBasis bq ωq hq) ωq U := by
  exact F.squareFiltration.quotientTop.graded_submodule_iff_of_basis_reindex bq ωq hq
    (reducedSquareFinIndexEquiv s ω) (Q).basis
    (quotientFinWeight (squareFinWeight ω) {i | s + 1 ≤ squareFinWeight ω i}) hQ
    (F.squareTopQuotientModel_basis_reindex b ω hF Γ N hN hin hout) rfl U

theorem squareTopQuotientModel_graded_repr (x : F.squareFiltration.quotientTop.AssociatedGraded)
    (i : ReducedSquareBasisIndex s ω) :
    ((Q).filtration.associatedGradedBasis (Q).basis
      (quotientFinWeight (squareFinWeight ω) {i | s + 1 ≤ squareFinWeight ω i}) hQ).repr x
        (reducedSquareFinIndexEquiv s ω i) =
      (F.squareFiltration.quotientTop.associatedGradedBasis bq ωq hq).repr x i := by
  exact F.squareFiltration.quotientTop.associatedGradedBasis_repr_of_basis_reindex bq ωq hq
    (reducedSquareFinIndexEquiv s ω) (Q).basis
    (quotientFinWeight (squareFinWeight ω) {i | s + 1 ≤ squareFinWeight ω i}) hQ
    (F.squareTopQuotientModel_basis_reindex b ω hF Γ N hN hin hout) rfl x i

theorem squareTopQuotientModel_top_annihilation_iff
    (ξ : (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)) →ₗ[ℚ] ℚ)
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded) :
    (∀ x ∈ W, basisGradeProjection ((Q).filtration.associatedGradedBasis (Q).basis
          (quotientFinWeight (squareFinWeight ω) {i | s + 1 ≤ squareFinWeight ω i}) hQ)
          (quotientFinWeight (squareFinWeight ω) {i | s + 1 ≤ squareFinWeight ω i}) s x = x →
      (Q).filtration.gradedFrequency (Q).basis
        (quotientFinWeight (squareFinWeight ω) {i | s + 1 ≤ squareFinWeight ω i}) hQ ξ x = 0) ↔
    (∀ x ∈ W, basisGradeProjection (F.squareFiltration.quotientTop.associatedGradedBasis bq ωq hq)
        ωq s x = x → F.squareFiltration.quotientTop.gradedFrequency bq ωq hq ξ x = 0) := by
  exact F.squareFiltration.quotientTop.graded_top_annihilation_iff_of_basis_reindex bq ωq hq
    (reducedSquareFinIndexEquiv s ω) (Q).basis
    (quotientFinWeight (squareFinWeight ω) {i | s + 1 ≤ squareFinWeight ω i}) hQ
    (F.squareTopQuotientModel_basis_reindex b ω hF Γ N hN hin hout) rfl ξ W

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem squareTopQuotientModel_graded_logHeight
    {ι κ L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L (s + 1)) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (Γ : Subgroup F.squareFiltration.Group) (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates (F.squareFinBasis b ω (hF 2)) Γ)
    (hout : bchSubgroupCoordinates (F.squareFinBasis b ω (hF 2)) Γ ⊆ denominatorGrid N)
    (v : κ → F.squareFiltration.quotientTop.AssociatedGraded) {p : ℝ}
    (hheight : BasisFamilyLogHeight
      ((F.squareFiltration.topQuotientModel (F.squareFinBasis b ω (hF 2))
        (squareFinWeight ω) (F.squareFinBasis_layers b ω hF) Γ N hN hin hout).filtration.associatedGradedBasis
        (F.squareFiltration.topQuotientModel (F.squareFinBasis b ω (hF 2))
          (squareFinWeight ω) (F.squareFinBasis_layers b ω hF) Γ N hN hin hout).basis
        (quotientFinWeight (squareFinWeight ω) {i | s + 1 ≤ squareFinWeight ω i})
        (F.squareFiltration.topQuotientModel_basis_layers (F.squareFinBasis b ω (hF 2))
          (squareFinWeight ω) (F.squareFinBasis_layers b ω hF) Γ N hN hin hout)) v p) :
    BasisFamilyLogHeight
      (F.squareFiltration.quotientTop.associatedGradedBasis
        (F.reducedSquareBasis b ω hF) (fun i => squareBasisWeight ω i.val)
        (F.reducedSquareBasis_layers b ω hF)) v p := by
  intro i j
  have heq := F.squareTopQuotientModel_graded_repr b ω hF Γ N hN hin hout (v i) j
  exact (congrArg rationalLogHeight heq).symm.le.trans
    (hheight i (reducedSquareFinIndexEquiv s ω j))

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BiasedSynchronizedSquareFamily
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {α σ ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ) (hw : ∀ i, 0 < w i)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

def ReducedSquareRelativeCongruent {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]
    {s : ℕ} (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)
    (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (P Q : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w) : Prop :=
  (F.reducedSquareRealRelativePart w P).coord - (F.reducedSquareRealRelativePart w Q).coord ∈
    (F.reducedSquareFastRelativeSubmodule w U).baseChange ℝ

theorem symbolFastIn_reducedSquareRealSymbolHom {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]
    {s : ℕ} (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)
    (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (g : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w)
    (hg : F.squareFiltration.quotientTop.SymbolFastIn w U g) :
    F.quotientTop.SymbolFastIn w (U.map (F.reducedSquareSndSymbolMap w))
      (F.reducedSquareRealSymbolHom w g) := F.reducedSquareRealSymbolHom_fast w U g hg

def SynchronizedReducedSquareFamilySpec (s C : ℕ) : Prop :=
  ∀ {σ ι κ L : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
    (F : NilpotentLieFiltration L (s + 1)) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (_hw : ∀ i, 0 < w i)
    (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (v : κ → F.squareFiltration.quotientTop.PolynomialSymbol w)
    (_hv : Submodule.span ℚ (Set.range v) = U.toSubmodule)
    (_hU : BasisBlockInvariant (F.reducedSquareSymbolBasis b ω hF w) (fun z => z.val.1) U.toSubmodule)
    (H l : ℕ) (p : ℝ) (_hH : 1 ≤ H) (_hl : 0 < l) (_hp : 0 ≤ p)
    (_hι : (Fintype.card ι : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hκ : (Fintype.card κ : ℝ) ≤ p) (_hHp : (H : ℝ) ≤ Real.exp p) (_hlp : (l : ℝ) ≤ Real.exp p)
    (_hc : ∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H)
    (_hh : ∀ i j, RationalHeightLE ((F.reducedSquareSymbolBasis b ω hF w).repr (v i) j) H),
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
      ∀ {α : Type*} (T : σ → ℝ) (_hT : ∀ i, Real.exp ((p + C) ^ C) ≤ T i)
        (S : Finset α) (a₀ : α) (_ha₀ : a₀ ∈ S)
        (E P R : α → F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w)
        (_hP : ∀ a ∈ S, F.squareFiltration.quotientTop.SymbolFastIn w U (P a))
        (_hE : ∀ a ∈ S, F.squareFiltration.quotientTop.SymbolSlowBound (F.reducedSquareBasis b ω hF)
          (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers b ω hF) w T (Real.exp p) (E a))
        (_hR : ∀ a ∈ S, F.squareFiltration.quotientTop.SymbolRationalGrid (F.reducedSquareBasis b ω hF)
          (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers b ω hF) w l (R a))
        (_hprojection : ∀ a ∈ S, F.reducedSquareRealSymbolHom w (E a * P a * R a) =
          F.reducedSquareRealSymbolHom w (E a₀ * P a₀ * R a₀)),
        ∃ E' P' R' : α → F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w,
          (∀ a ∈ S, E' a * P' a * R' a = E a * P a * R a ∧
            F.squareFiltration.quotientTop.SymbolFastIn w U (P' a) ∧
            F.reducedSquareRealSymbolHom w (E' a) = F.reducedSquareRealSymbolHom w (E a₀) ∧
            F.reducedSquareRealSymbolHom w (R' a) = F.reducedSquareRealSymbolHom w (R a₀) ∧
            F.reducedSquareRealSymbolHom w (P' a) = F.reducedSquareRealSymbolHom w (P a₀) ∧
            F.squareFiltration.quotientTop.SymbolSlowBound (F.reducedSquareBasis b ω hF)
              (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers b ω hF)
              w T (Real.exp ((p + C) ^ C)) (E' a) ∧
            F.squareFiltration.quotientTop.SymbolRationalGrid (F.reducedSquareBasis b ω hF)
              (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers b ω hF) w m (R' a)) ∧
          ∀ a ∈ S, F.ReducedSquareRelativeCongruent w U (P' a) (P' a₀)

theorem exists_synchronized_reduced_square_family (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ SynchronizedReducedSquareFamilySpec s C := by
  obtain ⟨C, hC, hreset⟩ := exists_compatible_reduced_fast_reset s 1
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L _ _ _ _ _ F b ω hF w hw U v hv hU H l p hH hl hp hι hσ hκ hHp hlp hc hh
  obtain ⟨sectionMap, m, hm, hmp, hlm, hsync⟩ :=
    hreset F b ω hF w hw U v hv hU H l p hH hl hp hι hσ hκ hHp hlp hc hh
  refine ⟨m, hm, hmp, hlm, ?_⟩
  intro α T hT S a₀ ha₀ E P R hP hE hR hprojection
  let π := F.reducedSquareRealSymbolHom w
  let A := π (E a₀)
  let B := π (P a₀)
  let D := π (R a₀)
  let c := fun a => F.reducedSquareRealLinearLift w sectionMap (A⁻¹ * π (E a))
  let d := fun a => F.reducedSquareRealLinearLift w sectionMap (π (R a) * D⁻¹)
  let E' := fun a => E a * (c a)⁻¹
  let P' := fun a => c a * P a * d a
  let R' := fun a => (d a)⁻¹ * R a
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  have hEin : ∀ a ∈ S, F.squareFiltration.quotientTop.SymbolSlowBound (F.reducedSquareBasis b ω hF)
      (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers b ω hF) w T
      (Real.exp ((p + 2) ^ 1)) (E a) := by
    intro a ha
    exact F.squareFiltration.quotientTop.symbolSlowBound_mono (F.reducedSquareBasis b ω hF)
      (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers b ω hF) w T hTpos
      (Real.exp_le_exp.mpr (by norm_num)) (E a) (hE a ha)
  have hA := F.reducedSquareRealSymbolHom_slow b ω hF w T (Real.exp ((p + 2) ^ 1)) (E a₀) (hEin a₀ ha₀)
  have hD := F.reducedSquareRealSymbolHom_grid b ω hF w l (R a₀) (hR a₀ ha₀)
  have hB := F.reducedSquareRealSymbolHom_fast w U (P a₀) (hP a₀ ha₀)
  have hresult : ∀ a ∈ S, E' a * P' a * R' a = E a * P a * R a ∧
      F.squareFiltration.quotientTop.SymbolFastIn w U (P' a) ∧
      π (E' a) = A ∧ π (R' a) = D ∧ π (P' a) = B ∧
      F.squareFiltration.quotientTop.SymbolSlowBound (F.reducedSquareBasis b ω hF)
        (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers b ω hF)
        w T (Real.exp ((p + C) ^ C)) (E' a) ∧
      F.squareFiltration.quotientTop.SymbolRationalGrid (F.reducedSquareBasis b ω hF)
        (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers b ω hF) w m (R' a) := by
    intro a ha
    have heq : A * B * D = π (E a * P a * R a) := by
      simpa only [A, B, D, π, map_mul] using (hprojection a ha).symm
    exact hsync T hT (E a) (P a) (R a) A B D (hP a ha) hB heq
      (hEin a ha) (hR a ha) hA hD
  refine ⟨E', P', R', hresult, ?_⟩
  intro a ha
  exact F.reducedSquareRealRelative_same_diagonal_mod_kernel w hw U
    (hresult a ha).2.1 (hresult a₀ ha₀).2.1
    ((hresult a ha).2.2.2.2.1.trans (hresult a₀ ha₀).2.2.2.2.1.symm)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

def PointwiseSynchronizedSquareFamilySpec (s C : ℕ) : Prop :=
  ∀ {σ ι κ L : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
    (F : NilpotentLieFiltration L (s + 1)) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (_hw : ∀ i, 0 < w i)
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)
    (v : κ → F.squareFiltration.quotientTop.AssociatedGraded)
    (_hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    (_hW : BasisGradedSubmodule
      (F.squareFiltration.quotientTop.associatedGradedBasis (F.reducedSquareBasis b ω hF)
        (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers b ω hF))
      (fun i => squareBasisWeight ω i.val) W.toSubmodule)
    (H l : ℕ) (p : ℝ) (_hH : 1 ≤ H) (_hl : 0 < l) (_hp : 0 ≤ p)
    (_hι : 2 * (Fintype.card ι : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hκ : (Fintype.card κ : ℝ) ≤ p) (_hHp : (H : ℝ) ≤ Real.exp p) (_hlp : (l : ℝ) ≤ Real.exp p)
    (_hc : ∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H)
    (_hh : ∀ i j, RationalHeightLE
      ((F.squareFiltration.quotientTop.associatedGradedBasis (F.reducedSquareBasis b ω hF)
        (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers b ω hF)).repr (v i) j) H),
    let U := F.squareFiltration.quotientTop.symbolPointwiseSubalgebra (F.reducedSquareBasis b ω hF)
      (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers b ω hF) w W
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
      ∀ {α : Type*} (T : σ → ℝ) (_hT : ∀ i, Real.exp ((p + C) ^ C) ≤ T i)
        (S : Finset α) (a₀ : α) (_ha₀ : a₀ ∈ S)
        (E P R : α → F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w)
        (_hP : ∀ a ∈ S, F.squareFiltration.quotientTop.SymbolFastIn w U (P a))
        (_hE : ∀ a ∈ S, F.squareFiltration.quotientTop.SymbolSlowBound (F.reducedSquareBasis b ω hF)
          (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers b ω hF) w T (Real.exp p) (E a))
        (_hR : ∀ a ∈ S, F.squareFiltration.quotientTop.SymbolRationalGrid (F.reducedSquareBasis b ω hF)
          (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers b ω hF) w l (R a))
        (_hprojection : ∀ a ∈ S, F.reducedSquareRealSymbolHom w (E a * P a * R a) =
          F.reducedSquareRealSymbolHom w (E a₀ * P a₀ * R a₀)),
        ∃ E' P' R' : α → F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w,
          (∀ a ∈ S, E' a * P' a * R' a = E a * P a * R a ∧
            F.squareFiltration.quotientTop.SymbolFastIn w U (P' a) ∧
            F.reducedSquareRealSymbolHom w (E' a) = F.reducedSquareRealSymbolHom w (E a₀) ∧
            F.reducedSquareRealSymbolHom w (R' a) = F.reducedSquareRealSymbolHom w (R a₀) ∧
            F.reducedSquareRealSymbolHom w (P' a) = F.reducedSquareRealSymbolHom w (P a₀) ∧
            F.squareFiltration.quotientTop.SymbolSlowBound (F.reducedSquareBasis b ω hF)
              (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers b ω hF)
              w T (Real.exp ((p + C) ^ C)) (E' a) ∧
            F.squareFiltration.quotientTop.SymbolRationalGrid (F.reducedSquareBasis b ω hF)
              (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers b ω hF) w m (R' a)) ∧
          ∀ a ∈ S, F.ReducedSquareRelativeCongruent w U (P' a) (P' a₀)

theorem exists_pointwise_synchronized_square_family (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ PointwiseSynchronizedSquareFamilySpec s C := by
  obtain ⟨a, _, hfamily⟩ := exists_synchronized_reduced_square_family s
  let Q : Polynomial ℕ := (Polynomial.X + Polynomial.C (s + 3)) ^ (s + 3)
  let B : Polynomial ℕ := (Q + Polynomial.C a) ^ a
  obtain ⟨C, hC, hfinal⟩ := exists_natPolynomial_eval_budget B
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L _ _ _ _ _ F b ω hF w hw W v hv hW H l p hH hl hp hι hσ hκ hHp hlp hc hh
  let bq := F.reducedSquareBasis b ω hF
  let ωq := fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω i.val
  let hq := F.reducedSquareBasis_layers b ω hF
  let U := F.squareFiltration.quotientTop.symbolPointwiseSubalgebra bq ωq hq w W
  let v' := F.squareFiltration.quotientTop.pointwiseSymbolSpanningFamily bq ωq hq w v
  let : Fintype (ReducedSquareSymbolIndex s w ω) :=
    symbolBasisIndexFintype w ωq s hw
      (F.squareFiltration.quotientTop.adaptedBasis_weight_le_step bq ωq hq)
  let q : ℝ := (p + (s + 3)) ^ (s + 3)
  have hqpos : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := symbol_spanning_parameter_ge s hp
  have hιp : (Fintype.card ι : ℝ) ≤ p := by
    have hi := Nat.cast_nonneg (α := ℝ) (Fintype.card ι)
    linarith
  have hdim : (Fintype.card (ReducedSquareBasisIndex s ω) : ℝ) ≤ p := by
    have hnat : Fintype.card (ReducedSquareBasisIndex s ω) ≤ 2 * Fintype.card ι :=
      (Fintype.card_subtype_le _).trans (card_squareBasis_index_le ω)
    have hreal : (Fintype.card (ReducedSquareBasisIndex s ω) : ℝ) ≤ 2 * (Fintype.card ι : ℝ) := by
      exact_mod_cast hnat
    exact hreal.trans hι
  have hcount : (Fintype.card (ReducedSquareSymbolIndex s w ω × κ) : ℝ) ≤ q := by
    have hnat : Fintype.card (ReducedSquareSymbolIndex s w ω × κ) ≤
        Fintype.card (ReducedSquareBasisIndex s ω) * (s + 1) * (Fintype.card σ + 1) ^ s *
          Fintype.card κ := by
      rw [Fintype.card_prod]
      exact Nat.mul_le_mul_right _ (symbolBasisIndex_card_le w ωq s hw
        (F.squareFiltration.quotientTop.adaptedBasis_weight_le_step bq ωq hq))
    exact (Nat.cast_le.mpr hnat).trans (symbol_spanning_count_bound s _ _ _ hp hdim hσ hκ)
  have hbound : (q + a) ^ a ≤ (p + C) ^ C := by
    simpa [B, Q, q, Polynomial.eval₂_pow] using hfinal p hp
  obtain ⟨m, hm, hmp, hlm, hsync⟩ := hfamily F b ω hF w hw U v'
    (F.squareFiltration.quotientTop.pointwiseSymbolSpanningFamily_span bq ωq hq w W hW v hv)
    (F.squareFiltration.quotientTop.symbolPointwiseSubalgebra_blockInvariant bq ωq hq w W)
    H l q hH hl hqpos (hιp.trans hpq) (hσ.trans hpq) hcount
    (hHp.trans (Real.exp_le_exp.mpr hpq)) (hlp.trans (Real.exp_le_exp.mpr hpq)) hc
    (F.squareFiltration.quotientTop.pointwiseSymbolSpanningFamily_height bq ωq hq w v hH hh)
  refine ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr hbound), hlm, ?_⟩
  intro α T hT S a₀ ha₀ E P R hP hE hR hprojection
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  have hEin : ∀ x ∈ S, F.squareFiltration.quotientTop.SymbolSlowBound bq ωq hq w T
      (Real.exp q) (E x) := fun x hx =>
    F.squareFiltration.quotientTop.symbolSlowBound_mono bq ωq hq w T hTpos
      (Real.exp_le_exp.mpr hpq) (E x) (hE x hx)
  have hchosen := hsync T
    (fun i => (Real.exp_le_exp.mpr hbound).trans (hT i)) S a₀ ha₀ E P R
  obtain ⟨E', P', R', hgood, hrelative⟩ := hchosen hP hEin hR hprojection
  refine ⟨E', P', R', ?_, hrelative⟩
  intro x hx
  obtain ⟨heq, hfast, hleft, hright, hmiddle, hslow, hrat⟩ := hgood x hx
  exact ⟨heq, hfast, hleft, hright, hmiddle,
    F.squareFiltration.quotientTop.symbolSlowBound_mono bq ωq hq w T hTpos
      (Real.exp_le_exp.mpr hbound) (E' x) hslow, hrat⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration NilpotentLieBCHGroup VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (N : ℕ) (hN : 0 < N)
  (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates
    (D.filtration.squareFinBasis b ω (hF 2)) (D.filtration.squareLattice D.lattice))
  (hout : bchSubgroupCoordinates (D.filtration.squareFinBasis b ω (hF 2))
    (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid N)

local notation "Q" => D.filtration.squareFiltration.topQuotientModel
  (D.filtration.squareFinBasis b ω (hF 2)) (squareFinWeight ω)
  (D.filtration.squareFinBasis_layers b ω hF) (D.filtration.squareLattice D.lattice) N hN hin hout
local notation "hQ" => D.filtration.squareFiltration.topQuotientModel_basis_layers
  (D.filtration.squareFinBasis b ω (hF 2)) (squareFinWeight ω)
  (D.filtration.squareFinBasis_layers b ω hF) (D.filtration.squareLattice D.lattice) N hN hin hout
local notation "bq" => D.filtration.reducedSquareBasis b ω hF
local notation "ωq" => (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val i))
local notation "hq" => D.filtration.reducedSquareBasis_layers b ω hF

theorem HasFixedNativeSquareFactors.canonical_factors {hs : 1 ≤ s}
    {g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1)} {η : L →ₗ[ℚ] ℚ}
    {T : σ → ℝ} {h : σ → ℤ} {p : ℝ} {l : ℕ}
    {W : LieSubalgebra ℚ D.filtration.squareFiltration.quotientTop.AssociatedGraded}
    (hdata : D.HasFixedNativeSquareFactors (D.filtration.squareFinBasis b ω (hF 2))
      (squareFinWeight ω) (D.filtration.squareFinBasis_layers b ω hF)
      N hN hin hout hs g η T h p l W) :
    ∃ ε γ : D.RealGroup, γ ∈ D.realLattice ∧
      (∀ i, |(D.basis.baseChange ℝ).repr ε.coord i| ≤ Real.exp p) ∧
      ∃ r : D.filtration.squareFiltration.RealAdaptedPolynomialGroup (fun _ : σ => 1),
        D.filtration.realAdaptedPolynomialMap (fun _ => 1)
            (D.filtration.realSquareFstPolynomialHom (fun _ => 1) r).coord =
          normalizedShiftLog (s + 1) (fun i => (h i : ℚ)) (-ε.coord) (-γ.coord)
            (D.filtration.realAdaptedPolynomialMap (fun _ => 1) g.coord) ∧
        D.filtration.realSquareSndPolynomialHom (fun _ => 1) r = g ∧
        D.filtration.realFirstCoefficientDirectionMap g.coord (fun i => (h i : ℝ)) -
            D.filtration.realFirstCoefficientConstant (fun _ => 1) ε.coord -
            D.filtration.realFirstCoefficientAdjoint (fun _ => 1) g
              (D.filtration.realFirstCoefficientConstant (fun _ => 1) γ.coord) =
          D.filtration.realReducedRelativeCoefficient (fun _ => 1) (fun _ => Nat.zero_lt_one)
            (D.filtration.squareFiltration.adaptedReducedRealSymbolHom (fun _ => 1) r) ∧
        D.filtration.squareFiltration.quotientTop.SymbolFactorizationIn bq ωq hq T
          (D.filtration.squareFiltration.adaptedReducedRealSymbolHom (fun _ => 1) r) p l W := by
  obtain ⟨ε, γ, hγ, hε, r, hf, hsecond, hderivative, ξ, _, _, _, hfixed⟩ := hdata
  refine ⟨ε, γ, hγ, hε, r, hf, hsecond, hderivative, ?_⟩
  exact (D.filtration.squareTopQuotientModel_factorization_iff b ω hF
    (D.filtration.squareLattice D.lattice) N hN hin hout T _ p l W).mp hfixed

theorem HasFixedNativeSquareFactors.fullFast_top_frequency {hs : 1 ≤ s}
    {g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1)} {η : L →ₗ[ℚ] ℚ}
    {T : σ → ℝ} {h : σ → ℤ} {p : ℝ} {l : ℕ}
    {W : LieSubalgebra ℚ D.filtration.squareFiltration.quotientTop.AssociatedGraded}
    (hdata : D.HasFixedNativeSquareFactors (D.filtration.squareFinBasis b ω (hF 2))
      (squareFinWeight ω) (D.filtration.squareFinBasis_layers b ω hF)
      N hN hin hout hs g η T h p l W)
    (hW : BasisGradedSubmodule ((Q).filtration.associatedGradedBasis (Q).basis
        (quotientFinWeight (squareFinWeight ω) {i | s + 1 ≤ squareFinWeight ω i}) hQ)
        (quotientFinWeight (squareFinWeight ω) {i | s + 1 ≤ squareFinWeight ω i}) W.toSubmodule) :
    ∀ x ∈ D.filtration.fullFastGradedRelative b ω hF W,
      basisGradeProjection (D.filtration.associatedGradedBasis b ω hF) ω (s + 1) x = x →
        D.filtration.gradedFrequency b ω hF η x = 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, ξ, _, hrestriction, hξ, _⟩ := hdata
  exact D.filtration.square_mode_fullFast_top_frequency b ω hF hs η ξ hrestriction W
    ((D.filtration.squareTopQuotientModel_graded_iff b ω hF
      (D.filtration.squareLattice D.lattice) N hN hin hout W.toSubmodule).mp hW)
    ((D.filtration.squareTopQuotientModel_top_annihilation_iff b ω hF
      (D.filtration.squareLattice D.lattice) N hN hin hout ξ W).mp hξ)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration NilpotentLieBCHGroup VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

def SynchronizedNativeSquareData (T : σ → ℝ)
    (g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (S : Finset (σ → ℤ)) (h₀ : σ → ℤ)
    (W : LieSubalgebra ℚ D.filtration.squareFiltration.quotientTop.AssociatedGraded)
    (p q : ℝ) (l m : ℕ) : Prop :=
  let U := D.filtration.fastPointwiseSquare b ω hF (fun _ : σ => 1) W
  ∃ (ε γ : (σ → ℤ) → D.RealGroup)
    (r : (σ → ℤ) → D.filtration.squareFiltration.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (E P R : (σ → ℤ) → D.filtration.squareFiltration.quotientTop.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (A B D₀ : D.filtration.quotientTop.RealPolynomialSymbolGroup (fun _ : σ => 1)),
    A * B * D₀ = D.filtration.adaptedReducedRealSymbolHom (fun _ => 1) g ∧
    D.filtration.quotientTop.SymbolSlowBound (D.filtration.quotientTopBasis b ω hF)
      (fun i => ω i.val) (D.filtration.quotientTopBasis_layers b ω hF)
      (fun _ => 1) T (Real.exp p) A ∧
    D.filtration.quotientTop.SymbolRationalGrid (D.filtration.quotientTopBasis b ω hF)
      (fun i => ω i.val) (D.filtration.quotientTopBasis_layers b ω hF) (fun _ => 1) l D₀ ∧
    D.filtration.quotientTop.SymbolFastIn (fun _ => 1)
      (U.map (D.filtration.reducedSquareSndSymbolMap (fun _ => 1))) B ∧
    (∀ h ∈ S, γ h ∈ D.realLattice ∧
      (∀ i, |(D.basis.baseChange ℝ).repr (ε h).coord i| ≤ Real.exp p) ∧
      D.filtration.realAdaptedPolynomialMap (fun _ => 1)
          (D.filtration.realSquareFstPolynomialHom (fun _ => 1) (r h)).coord =
        normalizedShiftLog (s + 1) (fun i => (h i : ℚ)) (-(ε h).coord) (-(γ h).coord)
          (D.filtration.realAdaptedPolynomialMap (fun _ => 1) g.coord) ∧
      D.filtration.realSquareSndPolynomialHom (fun _ => 1) (r h) = g ∧
      D.filtration.realFirstCoefficientDirectionMap g.coord (fun i => (h i : ℝ)) -
          D.filtration.realFirstCoefficientConstant (fun _ => 1) (ε h).coord -
          D.filtration.realFirstCoefficientAdjoint (fun _ => 1) g
            (D.filtration.realFirstCoefficientConstant (fun _ => 1) (γ h).coord) =
        D.filtration.realReducedRelativeCoefficient (fun _ => 1) (fun _ => Nat.zero_lt_one)
          (D.filtration.squareFiltration.adaptedReducedRealSymbolHom (fun _ => 1) (r h)) ∧
      E h * P h * R h = D.filtration.squareFiltration.adaptedReducedRealSymbolHom (fun _ => 1) (r h) ∧
      D.filtration.squareFiltration.quotientTop.SymbolFastIn (fun _ => 1) U (P h) ∧
      D.filtration.reducedSquareRealSymbolHom (fun _ => 1) (E h) = A ∧
      D.filtration.reducedSquareRealSymbolHom (fun _ => 1) (R h) = D₀ ∧
      D.filtration.reducedSquareRealSymbolHom (fun _ => 1) (P h) = B ∧
      D.filtration.squareFiltration.quotientTop.SymbolSlowBound
        (D.filtration.reducedSquareBasis b ω hF) (fun i => squareBasisWeight ω i.val)
        (D.filtration.reducedSquareBasis_layers b ω hF) (fun _ => 1) T (Real.exp q) (E h) ∧
      D.filtration.squareFiltration.quotientTop.SymbolRationalGrid
        (D.filtration.reducedSquareBasis b ω hF) (fun i => squareBasisWeight ω i.val)
        (D.filtration.reducedSquareBasis_layers b ω hF) (fun _ => 1) m (R h)) ∧
    ∀ h ∈ S, D.filtration.ReducedSquareRelativeCongruent (fun _ => 1) U (P h) (P h₀)

omit [Fintype ι] in
theorem SynchronizedNativeSquareData.mono {T : σ → ℝ}
    {g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1)}
    {S : Finset (σ → ℤ)} {h₀ : σ → ℤ}
    {W : LieSubalgebra ℚ D.filtration.squareFiltration.quotientTop.AssociatedGraded}
    {p q p' q' : ℝ} {l m : ℕ}
    (hdata : D.SynchronizedNativeSquareData b ω hF T g S h₀ W p q l m)
    (hp : p ≤ p') (hq : q ≤ q') (hT : ∀ i, 0 < T i) :
    D.SynchronizedNativeSquareData b ω hF T g S h₀ W p' q' l m := by
  obtain ⟨ε, γ, r, E, P, R, A, B, D₀, hprod, hA, hD, hB, hgood, hrelative⟩ := hdata
  refine ⟨ε, γ, r, E, P, R, A, B, D₀, hprod, ?_, hD, hB, ?_, hrelative⟩
  · exact D.filtration.quotientTop.symbolSlowBound_mono
      (D.filtration.quotientTopBasis b ω hF) (fun i => ω i.val)
      (D.filtration.quotientTopBasis_layers b ω hF) (fun _ => 1) T hT
      (Real.exp_le_exp.mpr hp) A hA
  · intro h hh
    obtain ⟨hγ, hε, hf, hs, hderivative, hfactor, hfast, hleft, hright, hmiddle, hslow, hrat⟩ := hgood h hh
    refine ⟨hγ, (fun i => (hε i).trans (Real.exp_le_exp.mpr hp)), hf, hs, hderivative,
      hfactor, hfast, hleft, hright, hmiddle, ?_, hrat⟩
    exact D.filtration.squareFiltration.quotientTop.symbolSlowBound_mono
      (D.filtration.reducedSquareBasis b ω hF) (fun i => squareBasisWeight ω i.val)
      (D.filtration.reducedSquareBasis_layers b ω hF) (fun _ => 1) T hT
      (Real.exp_le_exp.mpr hq) (E h) hslow

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open Module NilpotentLieFiltration NilpotentLieBCHGroup VectorPolynomial
open scoped TensorProduct

def SynchronizedNativeCommonCoefficientSpec (s C : ℕ) : Prop :=
  ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
    {d : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (H l m : ℕ) (p : ℝ) (_hH : 1 ≤ H) (_hl : 0 < l) (_hm : 0 < m) (_hp : 0 ≤ p)
    (_hι : (Fintype.card ι : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p) (_hd : (d : ℝ) ≤ p)
    (_hHp : (H : ℝ) ≤ Real.exp p) (_hlp : (l : ℝ) ≤ Real.exp p) (_hmp : (m : ℝ) ≤ Real.exp p)
    (_hgrid : (D.grid : ℝ) ≤ Real.exp p)
    (_hc : ∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H)
    (_hb : ∀ i j, RationalHeightLE (b.repr (D.basis j) i) H)
    (T : σ → ℝ) (_hT : ∀ i, 0 < T i)
    (g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (S : Finset (σ → ℤ)) (h₀ : σ → ℤ) (_hh₀ : h₀ ∈ S)
    (W : LieSubalgebra ℚ D.filtration.squareFiltration.quotientTop.AssociatedGraded)
    (_hbox : ∀ h ∈ S, ∀ i, |(h i : ℝ)| ≤ T i)
    (_hdata : D.SynchronizedNativeSquareData b ω hF T g S h₀ W p p l m),
    let q := (p + 2) ^ 3 + 3 * p + 1
    let U := D.filtration.fastPointwiseSquare b ω hF (fun _ : σ => 1) W
    ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((q + C) ^ C) ∧ l ∣ n ∧ m ∣ n ∧
      ∃ (A B R : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1))
        (small rational : (σ → ℤ) → D.filtration.RealFirstCoefficientModule (fun _ : σ => 1))
        (Z : D.filtration.RealFirstCoefficientModule (fun _ : σ => 1)),
        A * B * R = g ∧ B ∈ D.filtration.realFastDiagonalSubgroup (fun _ => 1) U ∧
        D.filtration.RealAdaptedCoefficientBound b ω hF (fun _ => 1) T (Real.exp p) A.coord ∧
        D.filtration.RealAdaptedCoefficientGrid b ω hF (fun _ => 1) l R.coord ∧
        coefficients (D.filtration.realAdaptedPolynomialMap (fun _ => 1) A.coord) 0 = 0 ∧
        coefficients (D.filtration.realAdaptedPolynomialMap (fun _ => 1) R.coord) 0 = 0 ∧
        coefficients (D.filtration.realAdaptedPolynomialMap (fun _ => 1) B.coord) 0 =
          coefficients (D.filtration.realAdaptedPolynomialMap (fun _ => 1) g.coord) 0 ∧
        ∀ h ∈ S,
          (D.filtration.realFirstCoefficientDirectionMap B.coord (fun i => (h i : ℝ)) -
            (small h + D.filtration.realFirstCoefficientAdjoint (fun _ => 1) B (rational h) + Z) ∈
              D.filtration.realFirstCoefficientFastSubmodule (fun _ => 1) (fun _ => Nat.zero_lt_one)
                (D.filtration.reducedSquareFastRelativeSubmodule (fun _ => 1) U)) ∧
          D.filtration.FirstCoefficientSlowBound b ω hF (fun _ => 1) T
            (Real.exp ((q + C) ^ C)) (small h) ∧
          D.filtration.FirstCoefficientGrid b ω hF (fun _ => 1) n (rational h)

theorem exists_synchronized_native_common_coefficients (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ SynchronizedNativeCommonCoefficientSpec s C := by
  obtain ⟨C, hC, hfamily⟩ := exists_normalized_common_family s
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ d D b ω hF H l m p hH hl hm hp hι hσ hd hHp hlp hmp hgrid hc hb
    T hT g S h₀ hh₀ W hbox hdata
  let U := D.filtration.fastPointwiseSquare b ω hF (fun _ : σ => 1) W
  let δ := matrixDenominator (fun i j => b.repr (D.basis j) i)
  let k := δ * D.grid * l * m
  let q := (p + 2) ^ 3 + 3 * p + 1
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by
    have h3 : 0 ≤ (p + 2) ^ 3 := by positivity
    dsimp [q]
    linarith
  have h2q : (p + 2) ^ 2 ≤ q := by
    have h23 : (p + 2) ^ 2 ≤ (p + 2) ^ 3 := pow_le_pow_right₀ (by linarith) (by decide)
    dsimp [q]
    linarith
  have hd' : (Fintype.card (Fin d) : ℝ) ≤ p := by simpa only [Fintype.card_fin] using hd
  have hδ : 0 < δ := matrixDenominator_pos _
  have hk : 0 < k := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hδ D.grid_pos) hl) hm
  have hδp : (δ : ℝ) ≤ Real.exp ((p + 2) ^ 3) :=
    real_basis_transfer_denominator D.basis b hp hd' hι hHp hb
  have hkq : (k : ℝ) ≤ Real.exp q := by
    dsimp only [k]
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul]
    calc
      _ ≤ Real.exp ((p + 2) ^ 3) * Real.exp p * Real.exp p * Real.exp p :=
        mul_le_mul (mul_le_mul (mul_le_mul hδp hgrid (Nat.cast_nonneg _) (Real.exp_nonneg _))
          hlp (Nat.cast_nonneg _) (by positivity)) hmp (Nat.cast_nonneg _) (by positivity)
      _ = Real.exp ((p + 2) ^ 3 + 3 * p) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp q := Real.exp_le_exp.mpr (by dsimp [q]; linarith)
  have hlk : l ∣ k := dvd_mul_of_dvd_left (dvd_mul_left l (δ * D.grid)) m
  have hmk : m ∣ k := dvd_mul_left m (δ * D.grid * l)
  have hδk : δ * D.grid ∣ k :=
    (dvd_mul_right (δ * D.grid) l).trans (dvd_mul_right (δ * D.grid * l) m)
  obtain ⟨ε, γ, r, E, P, R, A₀, B₀, R₀, hproduct, hA₀, hR₀, hB₀, hgood, _⟩ := hdata
  obtain ⟨A, B, D₀, hABD, hA, hB, hD, hAslow, hDgrid, hAzero, hDzero, hBzero⟩ :=
    D.filtration.exists_reduced_native_factorization b ω hF (fun _ : σ => 1)
      T hT (Real.exp_nonneg p) l g A₀ B₀ R₀ hproduct hA₀ hR₀
  have hBfast : B ∈ D.filtration.realFastDiagonalSubgroup (fun _ => 1) U := by
    change (D.filtration.adaptedReducedRealSymbolHom (fun _ => 1) B).coord ∈
      realificationLieSubalgebra (U.map (D.filtration.reducedSquareSndSymbolMap (fun _ => 1)))
    rw [hB]
    exact hB₀
  obtain ⟨n, hn, hnq, hkn, hcoeff⟩ := hfamily D.filtration b ω hF U H q hH hq
    (hι.trans hpq) (hσ.trans hpq) (hHp.trans (Real.exp_le_exp.mpr hpq)) hc k hk hkq
  have hE : ∀ h ∈ S, D.filtration.squareFiltration.quotientTop.SymbolSlowBound
      (D.filtration.reducedSquareBasis b ω hF) (fun i => squareBasisWeight ω i.val)
      (D.filtration.reducedSquareBasis_layers b ω hF) (fun _ => 1) T (Real.exp q) (E h) := by
    intro h hh
    exact D.filtration.squareFiltration.quotientTop.symbolSlowBound_mono
      (D.filtration.reducedSquareBasis b ω hF) (fun i => squareBasisWeight ω i.val)
      (D.filtration.reducedSquareBasis_layers b ω hF) (fun _ => 1) T hT
      (Real.exp_le_exp.mpr hpq) (E h) (hgood h hh).2.2.2.2.2.2.2.2.2.2.1
  have hR : ∀ h ∈ S, D.filtration.squareFiltration.quotientTop.SymbolRationalGrid
      (D.filtration.reducedSquareBasis b ω hF) (fun i => squareBasisWeight ω i.val)
      (D.filtration.reducedSquareBasis_layers b ω hF) (fun _ => 1) k (R h) := by
    intro h hh
    exact D.filtration.squareFiltration.quotientTop.symbolRationalGrid_mono
      (D.filtration.reducedSquareBasis b ω hF) (fun i => squareBasisWeight ω i.val)
      (D.filtration.reducedSquareBasis_layers b ω hF) (fun _ => 1) hm hmk (R h)
      (hgood h hh).2.2.2.2.2.2.2.2.2.2.2
  have hε : ∀ h ∈ S, ∀ i, |(b.baseChange ℝ).repr (ε h).coord i| ≤ Real.exp q := by
    intro h hh i
    exact (real_basis_coordinates_exp_bound D.basis b hp hd' hHp hb (ε h).coord
      (hgood h hh).2.1 i).trans (Real.exp_le_exp.mpr h2q)
  have hγ : ∀ h ∈ S, (fun i => (b.baseChange ℝ).repr (γ h).coord i) ∈ realDenominatorGrid k := by
    intro h hh
    have hdeclared := realification_subgroup_grid D.basis D.lattice D.grid D.outer_grid
      (γ h) (hgood h hh).1
    exact realDenominatorGrid_subset_of_dvd (Nat.mul_pos hδ D.grid_pos) hδk
      (real_basis_coordinates_grid D.basis b D.grid (γ h).coord hdeclared)
  obtain ⟨small, rational, hcommon⟩ := hcoeff T hT A B D₀
    (D.filtration.realAdaptedCoefficientBound_mono b ω hF (fun _ => 1) T hT
      (Real.exp_le_exp.mpr hpq) A.coord hAslow)
    (D.filtration.realAdaptedCoefficientGrid_mono b ω hF (fun _ => 1) hl hlk D₀.coord hDgrid)
    S r E P R (P h₀) (fun h => (ε h).coord) (fun h => (γ h).coord) hbox
    (by intro h hh; rw [hABD]; exact (hgood h hh).2.2.1)
    (by intro h hh; rw [hABD, (hgood h hh).2.2.2.1])
    (fun h hh => (hgood h hh).2.2.2.2.2.1.symm)
    (fun h hh => hA.trans (hgood h hh).2.2.2.2.2.2.2.1.symm)
    (fun h hh => hB.trans (hgood h hh).2.2.2.2.2.2.2.2.2.1.symm)
    (fun h hh => (hgood h hh).2.2.2.2.2.2.1)
    (hgood h₀ hh₀).2.2.2.2.2.2.1
    (fun h hh => (hgood h hh).2.2.2.2.2.2.2.2.2.1.trans
      (hgood h₀ hh₀).2.2.2.2.2.2.2.2.2.1.symm) hE hR hε hγ
  exact ⟨n, hn, hnq, hlk.trans hkn, hmk.trans hkn, A, B, D₀, small, rational,
    D.filtration.realReducedRelativeCoefficient (fun _ => 1) (fun _ => Nat.zero_lt_one) (P h₀),
    hABD, hBfast, hAslow, hDgrid, hAzero, hDzero, hBzero, hcommon⟩

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieFiltration NilpotentLieBCHGroup VectorPolynomial
open scoped TensorProduct

def SynchronizedNativeSquareFamilySpec (s C : ℕ) : Prop :=
  ∀ {σ ι κ L : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
    {d : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates
      (D.filtration.squareFinBasis b ω (hF 2)) (D.filtration.squareLattice D.lattice))
    (hout : bchSubgroupCoordinates (D.filtration.squareFinBasis b ω (hF 2))
      (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid N)
    (W : LieSubalgebra ℚ D.filtration.squareFiltration.quotientTop.AssociatedGraded)
    (v : κ → D.filtration.squareFiltration.quotientTop.AssociatedGraded)
    (_hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    (_hW : BasisGradedSubmodule
      (D.filtration.squareFiltration.quotientTop.associatedGradedBasis
        (D.filtration.reducedSquareBasis b ω hF)
        (fun i => squareBasisWeight ω i.val) (D.filtration.reducedSquareBasis_layers b ω hF))
      (fun i => squareBasisWeight ω i.val) W.toSubmodule)
    (H l : ℕ) (p : ℝ) (_hH : 1 ≤ H) (_hl : 0 < l) (_hp : 0 ≤ p)
    (_hι : 2 * (Fintype.card ι : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hκ : (Fintype.card κ : ℝ) ≤ p) (_hHp : (H : ℝ) ≤ Real.exp p) (_hlp : (l : ℝ) ≤ Real.exp p)
    (_hc : ∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H)
    (_hh : ∀ i j, RationalHeightLE
      ((D.filtration.squareFiltration.quotientTop.associatedGradedBasis
        (D.filtration.reducedSquareBasis b ω hF)
        (fun i => squareBasisWeight ω i.val) (D.filtration.reducedSquareBasis_layers b ω hF)).repr
          (v i) j) H),
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
      ∀ (T : σ → ℝ) (_hT : ∀ i, Real.exp ((p + C) ^ C) ≤ T i)
        (hs : 1 ≤ s) (g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1))
        (η : L →ₗ[ℚ] ℚ) (S : Finset (σ → ℤ)) (h₀ : σ → ℤ) (_hh₀ : h₀ ∈ S)
        (_hdata : ∀ h ∈ S, D.HasFixedNativeSquareFactors
          (D.filtration.squareFinBasis b ω (hF 2)) (squareFinWeight ω)
          (D.filtration.squareFinBasis_layers b ω hF) N hN hin hout hs g η T h p l W),
        D.SynchronizedNativeSquareData b ω hF T g S h₀ W p ((p + C) ^ C) l m

theorem exists_synchronized_native_square_family (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ SynchronizedNativeSquareFamilySpec s C := by
  obtain ⟨C, hC, hfamily⟩ := exists_pointwise_synchronized_square_family s
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L _ _ _ _ _ d D b ω hF N hN hin hout W v hv hW H l p hH hl hp hι hσ hκ hHp hlp hc hh
  obtain ⟨m, hm, hmp, hlm, hsync⟩ := hfamily D.filtration b ω hF (fun _ : σ => 1)
    (fun _ => Nat.zero_lt_one) W v hv hW H l p hH hl hp hι hσ hκ hHp hlp hc hh
  refine ⟨m, hm, hmp, hlm, ?_⟩
  intro T hT hs g η S h₀ hh₀ hdata
  have hcanonical := fun h hh =>
    RationalFilteredNilmanifold.HasFixedNativeSquareFactors.canonical_factors D b ω hF
      N hN hin hout (hdata h hh)
  choose! ε γ hγ hε r hf hsecond hderivative hfactor using hcanonical
  have hfastFactors := fun h hh => SymbolFactorizationIn.exists_fast_factors
    D.filtration.squareFiltration.quotientTop (D.filtration.reducedSquareBasis b ω hF)
    (fun i => squareBasisWeight ω i.val) (D.filtration.reducedSquareBasis_layers b ω hF) (hfactor h hh)
  choose! E P R hprod hE hR hP using hfastFactors
  let π := D.filtration.reducedSquareRealSymbolHom (fun _ : σ => 1)
  have hprojection : ∀ h ∈ S, π (E h * P h * R h) = D.filtration.adaptedReducedRealSymbolHom (fun _ => 1) g := by
    intro h hh
    rw [hprod h hh]
    change D.filtration.reducedSquareRealSymbolHom (fun _ => 1)
      (D.filtration.squareFiltration.adaptedReducedRealSymbolHom (fun _ => 1) (r h)) = _
    rw [D.filtration.adaptedReducedRealSymbolHom_square_projection, hsecond h hh]
  obtain ⟨E', P', R', hgood, hrelative⟩ := hsync T hT S h₀ hh₀ E P R hP hE hR
    (fun h hh => (hprojection h hh).trans (hprojection h₀ hh₀).symm)
  refine ⟨ε, γ, r, E', P', R', π (E h₀), π (P h₀), π (R h₀), ?_, ?_, ?_, ?_, ?_, hrelative⟩
  · rw [← map_mul, ← map_mul]
    exact hprojection h₀ hh₀
  · exact D.filtration.reducedSquareRealSymbolHom_slow b ω hF (fun _ => 1) T (Real.exp p) (E h₀) (hE h₀ hh₀)
  · exact D.filtration.reducedSquareRealSymbolHom_grid b ω hF (fun _ => 1) l (R h₀) (hR h₀ hh₀)
  · exact D.filtration.symbolFastIn_reducedSquareRealSymbolHom (fun _ => 1) _ (P h₀) (hP h₀ hh₀)
  · intro h hh
    obtain ⟨heq, hfast, hleft, hright, hmiddle, hslow, hrat⟩ := hgood h hh
    exact ⟨hγ h hh, hε h hh, hf h hh, hsecond h hh, hderivative h hh,
      heq.trans (hprod h hh), hfast, hleft, hright, hmiddle, hslow, hrat⟩

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieFiltration NilpotentLieBCHGroup VectorPolynomial CircleFourier
open scoped TensorProduct BigOperators

universe uσ uL

def BiasedSynchronizedSquareFamilySpec (s C : ℕ) : Prop :=
  ∀ (_hs : 1 ≤ s) {σ : Type uσ} {L : Type uL}
    [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (D : RationalFilteredNilmanifold L (s + 1) d)
    [TopologicalSpace (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
    [T2Space (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
    [TopologicalSpace (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1)))]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1)))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1)))]
    [T2Space (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1)))]
    (p : ℝ) (_hp : 0 ≤ p) (T : D.Niltest (fun _ : σ => 1)) (_hT : T.ComplexityLE p),
    ∃ (e : Basis (Fin (finrank ℚ L)) ℚ L) (ω : Fin (finrank ℚ L) → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
      (N : ℕ) (hN : 0 < N)
      (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates
        (D.filtration.squareFinBasis e ω (hF 2)) (D.filtration.squareLattice D.lattice))
      (hout : bchSubgroupCoordinates (D.filtration.squareFinBasis e ω (hF 2))
        (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid N),
      (∀ i j, rationalLogHeight (D.basis.repr (e i) j) ≤ p + 1) ∧
      (D.filtration.squareFiltration.topQuotientModel
        (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
        (D.filtration.squareFinBasis_layers e ω hF)
        (D.filtration.squareLattice D.lattice) N hN hin hout).GeometryComplexityLE (squareGeometryBudget p) ∧
      ∀ (g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1)),
        D.filtration.nativePolynomialOrbit (fun _ => 1) g = T.orbit →
      ∀ (η : L →ₗ[ℚ] ℚ),
        (∀ z ∈ D.filtration.realification.subgroup (s + 1), ∀ x,
          T.observable (z • x) = character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) *
            T.observable x) →
      ∀ (origin : σ → ℤ) (lengths : σ → ℕ), (∀ i, 0 < lengths i) →
        (Fintype.card σ : ℝ) ≤ p →
        (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
        Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths, T.eval x‖ →
        ∃ (S : Finset (σ → ℤ)) (h₀ : σ → ℤ) (l m : ℕ)
          (W : LieSubalgebra ℚ D.filtration.squareFiltration.quotientTop.AssociatedGraded)
          (u : Fin (Fintype.card {i // ¬ s + 1 ≤ squareFinWeight ω i}) →
            D.filtration.squareFiltration.quotientTop.AssociatedGraded),
          h₀ ∈ S ∧ Real.exp (-((p + C) ^ C)) * (∏ i, (lengths i : ℝ)) ≤ S.card ∧
          0 < l ∧ (l : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
          0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
          Submodule.span ℚ (Set.range u) = W.toSubmodule ∧
          BasisGradedSubmodule
            (D.filtration.squareFiltration.quotientTop.associatedGradedBasis
              (D.filtration.reducedSquareBasis e ω hF) (fun i => squareBasisWeight ω i.val)
              (D.filtration.reducedSquareBasis_layers e ω hF))
            (fun i => squareBasisWeight ω i.val) W.toSubmodule ∧
          (∀ i j, rationalLogHeight
            ((D.filtration.squareFiltration.quotientTop.associatedGradedBasis
              (D.filtration.reducedSquareBasis e ω hF) (fun i => squareBasisWeight ω i.val)
              (D.filtration.reducedSquareBasis_layers e ω hF)).repr (u i) j) ≤ (p + C) ^ C) ∧
          (∀ x ∈ D.filtration.fullFastGradedRelative e ω hF W,
            basisGradeProjection (D.filtration.associatedGradedBasis e ω hF) ω (s + 1) x = x →
              D.filtration.gradedFrequency e ω hF η x = 0) ∧
          (∀ h ∈ S, (∀ i, |(h i : ℝ)| ≤ lengths i) ∧
            ∀ i, Real.exp (-((p + C) ^ C)) * lengths i <
              (((lengths i : ℤ) - |h i|).toNat : ℝ)) ∧
          D.SynchronizedNativeSquareData e ω hF (fun i => (lengths i : ℝ)) g S h₀ W
            ((p + C) ^ C) ((p + C) ^ C) l m

theorem exists_biased_synchronized_square_family (s c : ℕ)
    (hI : TranslatedStepDropSpec.{uσ, uL} s c) :
    ∃ C : ℕ, 2 ≤ C ∧ BiasedSynchronizedSquareFamilySpec.{uσ, uL} s C := by
  obtain ⟨a, _, hfamily⟩ := exists_common_fixed_native_square_family s c hI
  obtain ⟨b, _, hsynchronize⟩ := exists_synchronized_native_square_family s
  let B : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  let G : Polynomial ℕ := ((Polynomial.X + 3) ^ 11 + 2 * Polynomial.X + 5) ^ 11
  let Q : Polynomial ℕ := B + (Polynomial.X + 4) ^ 11 + G + 2 * Polynomial.X + 2
  let P : Polynomial ℕ := B + (Q + 1) + (Q + 1 + Polynomial.C b) ^ b
  obtain ⟨C, hC, hfinal⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro hs σ L _ _ _ _ d _ _ _ _ D _ _ _ _ _ _ _ _ p hp T hT
  let k : ℝ := (p + a) ^ a
  let q : ℝ := k + (p + 4) ^ 11 + squareGeometryBudget p + 2 * p + 2
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hbracket : 0 ≤ (p + 4) ^ 11 := by positivity
  have hgeompos := squareGeometryBudget_nonneg hp
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hkq : k ≤ q := by dsimp [q]; linarith
  have hbracketq : (p + 4) ^ 11 ≤ q := by dsimp [q]; linarith
  have hgeomq : squareGeometryBudget p ≤ q := by dsimp [q]; linarith
  have h2pq : 2 * p ≤ q := by dsimp [q]; linarith
  have hpq : p ≤ q := by linarith
  have hq1 : 0 ≤ q + 1 := by linarith
  have hbq : 0 ≤ (q + 1 + b) ^ b := by positivity
  have hbound : k + (q + 1) + (q + 1 + b) ^ b ≤ (p + C) ^ C := by
    simpa [P, Q, B, G, k, q, squareGeometryBudget, Polynomial.eval₂_pow] using hfinal p hp
  have hkC : k ≤ (p + C) ^ C := by linarith
  have hqC : q + 1 ≤ (p + C) ^ C := by linarith
  have hbC : (q + 1 + b) ^ b ≤ (p + C) ^ C := by linarith
  obtain ⟨e, ω, hF, N, hN, hin, hout, he, hgeometry, hconstruct⟩ := hfamily hs D p hp T hT
  obtain ⟨hdim, _, hstructure⟩ := D.basis_geometry_of_forward_height e hp hT.1 he
  refine ⟨e, ω, hF, N, hN, hin, hout, he, hgeometry, ?_⟩
  intro g hgOrbit η hvert origin lengths hlengths hσ hlarge hbias
  have hTpos : ∀ i, 0 < (lengths i : ℝ) := fun i => by exact_mod_cast hlengths i
  obtain ⟨S, l, W, u, hS, hcount, hl, hlk, hu, hW, hheight, hgood⟩ :=
    hconstruct g hgOrbit η hvert origin lengths hlengths hσ
      (fun i => (Real.exp_le_exp.mpr hkC).trans (hlarge i)) hbias
  obtain ⟨h₀, hh₀⟩ := hS
  have hWcanonical := (D.filtration.squareTopQuotientModel_graded_iff e ω hF
    (D.filtration.squareLattice D.lattice) N hN hin hout W.toSubmodule).mp hW
  have hcanonicalHeight : BasisFamilyLogHeight
      (D.filtration.squareFiltration.quotientTop.associatedGradedBasis
        (D.filtration.reducedSquareBasis e ω hF) (fun i => squareBasisWeight ω i.val)
        (D.filtration.reducedSquareBasis_layers e ω hF)) u k :=
    D.filtration.squareTopQuotientModel_graded_logHeight e ω hF
      (D.filtration.squareLattice D.lattice) N hN hin hout u hheight
  let H := ⌈Real.exp q⌉₊
  have hH : 1 ≤ H := one_le_ceil_exp q
  have hHq : (H : ℝ) ≤ Real.exp (q + 1) := ceil_exp_le_exp_add_one hq
  have hdimq : 2 * (Fintype.card (Fin (finrank ℚ L)) : ℝ) ≤ q + 1 := by
    have := mul_le_mul_of_nonneg_left hdim (by norm_num : (0 : ℝ) ≤ 2)
    linarith
  have hκq : (Fintype.card (Fin (Fintype.card {i // ¬ s + 1 ≤ squareFinWeight ω i})) : ℝ) ≤ q + 1 := by
    rw [Fintype.card_fin]
    exact hgeometry.1.trans (hgeomq.trans (by linarith))
  have hσq : (Fintype.card σ : ℝ) ≤ q + 1 := hσ.trans (hpq.trans (by linarith))
  have hlq : (l : ℝ) ≤ Real.exp (q + 1) :=
    hlk.trans (Real.exp_le_exp.mpr (hkq.trans (by linarith)))
  have hc : ∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H :=
    fun i j k => rationalHeightLE_ceil_exp ((hstructure i j k).trans hbracketq)
  have hh : ∀ i j, RationalHeightLE
      ((D.filtration.squareFiltration.quotientTop.associatedGradedBasis
        (D.filtration.reducedSquareBasis e ω hF) (fun i => squareBasisWeight ω i.val)
        (D.filtration.reducedSquareBasis_layers e ω hF)).repr (u i) j) H :=
    fun i j => rationalHeightLE_ceil_exp ((hcanonicalHeight i j).trans hkq)
  obtain ⟨m, hm, hmb, hlm, hsync⟩ := hsynchronize D e ω hF N hN hin hout W u hu hWcanonical
    H l (q + 1) hH hl hq1 hdimq hσq hκq hHq hlq hc hh
  have hfixed : ∀ h ∈ S, D.HasFixedNativeSquareFactors
      (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
      (D.filtration.squareFinBasis_layers e ω hF) N hN hin hout hs g η
      (fun i => (lengths i : ℝ)) h (q + 1) l W := by
    intro h hh
    exact RationalFilteredNilmanifold.HasFixedNativeSquareFactors.mono D
      (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
      (D.filtration.squareFinBasis_layers e ω hF) N hN hin hout
      (hgood h hh).2.2 (hkq.trans (by linarith)) hTpos
  have hdata := hsync (fun i => (lengths i : ℝ))
    (fun i => (Real.exp_le_exp.mpr hbC).trans (hlarge i)) hs g η S h₀ hh₀ hfixed
  refine ⟨S, h₀, l, m, W, u, hh₀, ?_, hl, hlk.trans (Real.exp_le_exp.mpr hkC),
    hm, hmb.trans (Real.exp_le_exp.mpr hbC), hlm, hu, hWcanonical, ?_, ?_, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hkC))
      (Finset.prod_nonneg (fun i _ => Nat.cast_nonneg (lengths i)))).trans hcount
  · exact fun i j => (hcanonicalHeight i j).trans hkC
  · exact RationalFilteredNilmanifold.HasFixedNativeSquareFactors.fullFast_top_frequency
      D e ω hF N hN hin hout (hgood h₀ hh₀).2.2 hW
  · intro h hh
    exact ⟨(hgood h hh).1, fun i =>
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hkC))
        (Nat.cast_nonneg (lengths i))).trans_lt ((hgood h hh).2.1 i)⟩
  · exact RationalFilteredNilmanifold.SynchronizedNativeSquareData.mono
      D e ω hF hdata hqC hbC hTpos

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BiasedNativeTerminal
namespace OAI

section

namespace Erdos3

open Module NilpotentLieFiltration VectorPolynomial
open scoped BigOperators

def SynchronizedNativeTerminalSpec (s C : ℕ) : Prop :=
  ∀ {σ ι τ L : Type*} [Fintype σ] [DecidableEq σ] [Fintype ι] [Fintype τ]
    [LieRing L] [LieAlgebra ℚ L] {d : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (H l m : ℕ) (p : ℝ) (_hH : 1 ≤ H) (_hl : 0 < l) (_hm : 0 < m) (_hp : 0 ≤ p) (_hs : 1 ≤ s)
    (_hι : (Fintype.card ι : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hτ : (Fintype.card τ : ℝ) ≤ p) (_hd : (d : ℝ) ≤ p)
    (_hHp : (H : ℝ) ≤ Real.exp p) (_hlp : (l : ℝ) ≤ Real.exp p) (_hmp : (m : ℝ) ≤ Real.exp p)
    (_hgrid : (D.grid : ℝ) ≤ Real.exp p)
    (_hc : ∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H)
    (_hb : ∀ i j, RationalHeightLE (b.repr (D.basis j) i) H)
    (W : LieSubalgebra ℚ D.filtration.squareFiltration.quotientTop.AssociatedGraded)
    (v : τ → D.filtration.squareFiltration.quotientTop.AssociatedGraded)
    (_hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    (_hW : BasisGradedSubmodule
      (D.filtration.squareFiltration.quotientTop.associatedGradedBasis
        (D.filtration.reducedSquareBasis b ω hF) (fun i => squareBasisWeight ω i.val)
        (D.filtration.reducedSquareBasis_layers b ω hF)) (fun i => squareBasisWeight ω i.val) W.toSubmodule)
    (_hh : ∀ i j, RationalHeightLE
      ((D.filtration.squareFiltration.quotientTop.associatedGradedBasis
        (D.filtration.reducedSquareBasis b ω hF) (fun i => squareBasisWeight ω i.val)
        (D.filtration.reducedSquareBasis_layers b ω hF)).repr (v i) j) H)
    (η : D.filtration.AssociatedGraded →ₗ[ℚ] ℚ)
    (_hη : ∀ x ∈ D.filtration.fullFastGradedRelative b ω hF W,
      basisGradeProjection (D.filtration.associatedGradedBasis b ω hF) ω (s + 1) x = x → η x = 0)
    (T : σ → ℝ) (_hT : ∀ i, Real.exp ((p + C) ^ C) ≤ T i)
    (g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (S : Finset (σ → ℤ)) (h₀ : σ → ℤ) (_hh₀ : h₀ ∈ S)
    (_hbox : ∀ h ∈ S, ∀ i, |(h i : ℝ)| ≤ T i)
    (_hdense : Real.exp (-p) * ∏ i, T i ≤ (S.card : ℝ))
    (_hdata : D.SynchronizedNativeSquareData b ω hF T g S h₀ W p p l m),
    ∃ A B R : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1),
      A * B * R = g ∧
      D.filtration.RealAdaptedCoefficientBound b ω hF (fun _ => 1) T (Real.exp p) A.coord ∧
      D.filtration.RealAdaptedCoefficientGrid b ω hF (fun _ => 1) l R.coord ∧
      D.filtration.SymbolTerminalFactorization b ω hF W η T
        (D.filtration.realPolynomialSymbolHom b ω hF (fun _ => 1)
          (D.filtration.realAdaptedPolynomialGroupHom (fun _ => 1) B)) ((p + C) ^ C)

theorem exists_synchronized_native_terminal (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ SynchronizedNativeTerminalSpec s C := by
  obtain ⟨a, _, hcommon⟩ := exists_synchronized_native_common_coefficients s
  obtain ⟨b, _, hterminal⟩ := exists_unnormalized_common_symbolFactorization_bound s
  let Q : Polynomial ℕ := ((Polynomial.X + 2) ^ 3 + 3 * Polynomial.X + 1 + Polynomial.C a) ^ a
  let P : Polynomial ℕ := Polynomial.X + Q
  let R : Polynomial ℕ := P + (P + Polynomial.C b) ^ b
  obtain ⟨C, hC, hfinal⟩ := exists_natPolynomial_eval_budget R
  refine ⟨C, hC, ?_⟩
  intro σ ι τ L _ _ _ _ _ _ d D e ω hF H l m p hH hl hm hp hs hι hσ hτ hd hHp hlp hmp hgrid hc hb
    W v hv hW hh η hη T hT g S h₀ hh₀ hbox hdense hdata
  let q : ℝ := ((p + 2) ^ 3 + 3 * p + 1 + a) ^ a
  let r : ℝ := p + q
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hr : 0 ≤ r := add_nonneg hp hq
  have hpr : p ≤ r := le_add_of_nonneg_right hq
  have hqr : q ≤ r := le_add_of_nonneg_left hp
  have hterminalPos : 0 ≤ (r + b) ^ b := by positivity
  have hbound : r + (r + b) ^ b ≤ (p + C) ^ C := by
    simpa [R, P, Q, r, q, Polynomial.eval₂_pow] using hfinal p hp
  have hterminalC : (r + b) ^ b ≤ (p + C) ^ C := by linarith
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  obtain ⟨n, hn, hnq, _, _, A, B, D₀, small, rational, Z, hprod, hB, hA, hD, _, _, _, hgood⟩ :=
    hcommon D e ω hF H l m p hH hl hm hp hι hσ hd hHp hlp hmp hgrid hc hb
      T hTpos g S h₀ hh₀ W hbox hdata
  let B' : D.filtration.realFastDiagonalSubgroup (fun _ : σ => 1)
      (D.filtration.fastPointwiseSquare e ω hF (fun _ => 1) W) := ⟨B, hB⟩
  have hfactor := hterminal D.filtration e ω hF W H r hH hr hs
    (hι.trans hpr) (hσ.trans hpr) (hτ.trans hpr) (hHp.trans (Real.exp_le_exp.mpr hpr)) hc
    hW v hv hh η hη B' T (fun i => (Real.exp_le_exp.mpr hterminalC).trans (hT i))
    (Real.exp q) (Real.exp_nonneg q) (Real.exp_le_exp.mpr hqr)
    n hn (hnq.trans (Real.exp_le_exp.mpr hqr)) S h₀ hh₀ small rational Z
    hbox (fun h hh => (hgood h hh).1) (fun h hh => (hgood h hh).2.1) (fun h hh => (hgood h hh).2.2)
    (Real.exp (-p)) (Real.exp_pos _) (by
      simpa only [Real.exp_neg, inv_inv] using Real.exp_le_exp.mpr hpr) hdense
  exact ⟨A, B, D₀, hprod, hA, hD,
    SymbolTerminalFactorization.mono D.filtration e ω hF W hfactor hterminalC hTpos⟩

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieFiltration NilpotentLieBCHGroup VectorPolynomial CircleFourier
open scoped TensorProduct BigOperators

universe uσ uL

def BiasedNativeTerminalSpec (s C : ℕ) : Prop :=
  ∀ (_hs : 1 ≤ s) {σ : Type uσ} {L : Type uL}
    [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (D : RationalFilteredNilmanifold L (s + 1) d)
    [TopologicalSpace (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
    [T2Space (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
    [TopologicalSpace (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1)))]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1)))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1)))]
    [T2Space (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1)))]
    (p : ℝ) (_hp : 0 ≤ p) (T : D.Niltest (fun _ : σ => 1)) (_hT : T.ComplexityLE p),
    ∃ (e : Basis (Fin (finrank ℚ L)) ℚ L) (ω : Fin (finrank ℚ L) → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
      (N : ℕ) (hN : 0 < N)
      (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates
        (D.filtration.squareFinBasis e ω (hF 2)) (D.filtration.squareLattice D.lattice))
      (hout : bchSubgroupCoordinates (D.filtration.squareFinBasis e ω (hF 2))
        (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid N),
      (∀ i j, rationalLogHeight (D.basis.repr (e i) j) ≤ p + 1) ∧
      (D.filtration.squareFiltration.topQuotientModel
        (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
        (D.filtration.squareFinBasis_layers e ω hF)
        (D.filtration.squareLattice D.lattice) N hN hin hout).GeometryComplexityLE (squareGeometryBudget p) ∧
      ∀ (g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1)),
        D.filtration.nativePolynomialOrbit (fun _ => 1) g = T.orbit →
      ∀ (η : L →ₗ[ℚ] ℚ),
        (∀ z ∈ D.filtration.realification.subgroup (s + 1), ∀ x,
          T.observable (z • x) = character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) *
            T.observable x) →
      ∀ (origin : σ → ℤ) (lengths : σ → ℕ), (∀ i, 0 < lengths i) →
        (Fintype.card σ : ℝ) ≤ p →
        (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
        Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths, T.eval x‖ →
        ∃ (l : ℕ) (W : LieSubalgebra ℚ D.filtration.squareFiltration.quotientTop.AssociatedGraded)
          (A B R : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1)),
          0 < l ∧ (l : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ A * B * R = g ∧
          D.filtration.RealAdaptedCoefficientBound e ω hF (fun _ => 1)
            (fun i => (lengths i : ℝ)) (Real.exp ((p + C) ^ C)) A.coord ∧
          D.filtration.RealAdaptedCoefficientGrid e ω hF (fun _ => 1) l R.coord ∧
          D.filtration.SymbolTerminalFactorization e ω hF W (D.filtration.gradedFrequency e ω hF η)
            (fun i => (lengths i : ℝ))
            (D.filtration.realPolynomialSymbolHom e ω hF (fun _ => 1)
              (D.filtration.realAdaptedPolynomialGroupHom (fun _ => 1) B)) ((p + C) ^ C)

theorem exists_biased_native_terminal (s c : ℕ)
    (hI : TranslatedStepDropSpec.{uσ, uL} s c) :
    ∃ C : ℕ, 2 ≤ C ∧ BiasedNativeTerminalSpec.{uσ, uL} s C := by
  obtain ⟨a, _, hfamily⟩ := exists_biased_synchronized_square_family s c hI
  obtain ⟨b, _, hterminal⟩ := exists_synchronized_native_terminal s
  let B : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  let G : Polynomial ℕ := ((Polynomial.X + 3) ^ 11 + 2 * Polynomial.X + 5) ^ 11
  let Q : Polynomial ℕ := B + (Polynomial.X + 4) ^ 11 + (Polynomial.X + 4) ^ 5 + G + Polynomial.X + 2
  let P : Polynomial ℕ := B + (Q + 1) + (Q + 1 + Polynomial.C b) ^ b
  obtain ⟨C, hC, hfinal⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro hs σ L _ _ _ _ d _ _ _ _ D _ _ _ _ _ _ _ _ p hp T hT
  let k : ℝ := (p + a) ^ a
  let q : ℝ := k + (p + 4) ^ 11 + (p + 4) ^ 5 + squareGeometryBudget p + p + 2
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have h11 : 0 ≤ (p + 4) ^ 11 := by positivity
  have h5 : 0 ≤ (p + 4) ^ 5 := by positivity
  have hgeom := squareGeometryBudget_nonneg hp
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hkq : k ≤ q := by dsimp [q]; linarith
  have h11q : (p + 4) ^ 11 ≤ q := by dsimp [q]; linarith
  have h5q : (p + 4) ^ 5 ≤ q := by dsimp [q]; linarith
  have hGq : squareGeometryBudget p ≤ q := by dsimp [q]; linarith
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hq1 : 0 ≤ q + 1 := by linarith
  have hlast : 0 ≤ (q + 1 + b) ^ b := by positivity
  have hbound : k + (q + 1) + (q + 1 + b) ^ b ≤ (p + C) ^ C := by
    simpa [P, Q, B, G, k, q, squareGeometryBudget, Polynomial.eval₂_pow] using hfinal p hp
  have hkC : k ≤ (p + C) ^ C := by linarith
  have hqC : q + 1 ≤ (p + C) ^ C := by linarith
  have hbC : (q + 1 + b) ^ b ≤ (p + C) ^ C := by linarith
  have hkq1 : k ≤ q + 1 := by linarith
  have hpq1 : p ≤ q + 1 := by linarith
  obtain ⟨e, ω, hF, N, hN, hin, hout, he, hgeometry, hconstruct⟩ := hfamily hs D p hp T hT
  obtain ⟨hdim, hinverse, hstructure⟩ := D.basis_geometry_of_forward_height e hp hT.1 he
  refine ⟨e, ω, hF, N, hN, hin, hout, he, hgeometry, ?_⟩
  intro g hgOrbit η hvert origin lengths hlengths hσ hlarge hbias
  have hTpos : ∀ i, 0 < (lengths i : ℝ) := fun i => by exact_mod_cast hlengths i
  obtain ⟨S, h₀, l, m, W, u, hh₀, hcount, hl, hlk, hm, hmk, _, hu, hW, hheight, hη, hshift, hdata⟩ :=
    hconstruct g hgOrbit η hvert origin lengths hlengths hσ
      (fun i => (Real.exp_le_exp.mpr hkC).trans (hlarge i)) hbias
  let H := ⌈Real.exp q⌉₊
  have hH : 1 ≤ H := one_le_ceil_exp q
  have hHp : (H : ℝ) ≤ Real.exp (q + 1) := ceil_exp_le_exp_add_one hq
  have hc : ∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H :=
    fun i j k => rationalHeightLE_ceil_exp ((hstructure i j k).trans h11q)
  have hb : ∀ i j, RationalHeightLE (e.repr (D.basis j) i) H :=
    fun i j => rationalHeightLE_ceil_exp ((hinverse j i).trans h5q)
  have hh : ∀ i j, RationalHeightLE
      ((D.filtration.squareFiltration.quotientTop.associatedGradedBasis
        (D.filtration.reducedSquareBasis e ω hF) (fun i => squareBasisWeight ω i.val)
        (D.filtration.reducedSquareBasis_layers e ω hF)).repr (u i) j) H :=
    fun i j => rationalHeightLE_ceil_exp ((hheight i j).trans hkq)
  have hτ : (Fintype.card (Fin (Fintype.card {i // ¬ s + 1 ≤ squareFinWeight ω i})) : ℝ) ≤ q + 1 := by
    rw [Fintype.card_fin]
    exact hgeometry.1.trans (hGq.trans (by linarith))
  have hdense : Real.exp (-(q + 1)) * (∏ i, (lengths i : ℝ)) ≤ S.card :=
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hkq1))
      (Finset.prod_nonneg (fun i _ => Nat.cast_nonneg (lengths i)))).trans hcount
  have hdata' := RationalFilteredNilmanifold.SynchronizedNativeSquareData.mono
    D e ω hF hdata hkq1 hkq1 hTpos
  obtain ⟨A, M, R, hprod, hA, hR, hfactor⟩ := hterminal D e ω hF H l m (q + 1)
    hH hl hm hq1 hs (hdim.trans hpq1) (hσ.trans hpq1) hτ (hT.1.1.trans hpq1) hHp
    (hlk.trans (Real.exp_le_exp.mpr hkq1)) (hmk.trans (Real.exp_le_exp.mpr hkq1))
    (hT.1.2.1.trans (Real.exp_le_exp.mpr hpq1)) hc hb W u hu hW hh
    (D.filtration.gradedFrequency e ω hF η) hη (fun i => (lengths i : ℝ))
    (fun i => (Real.exp_le_exp.mpr hbC).trans (hlarge i)) g S h₀ hh₀
    (fun h hh => (hshift h hh).1) hdense hdata'
  exact ⟨l, W, A, M, R, hl, hlk.trans (Real.exp_le_exp.mpr hkC), hprod,
    D.filtration.realAdaptedCoefficientBound_mono e ω hF (fun _ => 1)
      (fun i => (lengths i : ℝ)) hTpos (Real.exp_le_exp.mpr hqC) A.coord hA, hR,
    SymbolTerminalFactorization.mono D.filtration e ω hF W hfactor hbC hTpos⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MarkedRefilteredLowerNativeDiagram
namespace OAI

namespace Erdos3

open Module

variable {L M ι κ α β : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] [Fintype ι] [Fintype κ] [Fintype β]

theorem restrictedLieMap_coordinate_logHeight
    (e : Basis ι ℚ L) (f : Basis κ ℚ M)
    (U : LieSubalgebra ℚ L) (V : LieSubalgebra ℚ M)
    (b : Basis α ℚ U) (c : Basis β ℚ V)
    (φ : L →ₗ⁅ℚ⁆ M) (hUV : ∀ x ∈ U, φ x ∈ V)
    {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hβ : (Fintype.card β : ℝ) ≤ p)
    (hφ : ∀ i j, rationalLogHeight (f.repr (φ (e i)) j) ≤ p)
    (hb : ∀ i j, rationalLogHeight (e.repr (b i : L) j) ≤ p)
    (hc : ∀ i j, rationalLogHeight (f.repr (c i : M) j) ≤ p)
    (i : α) (j : β) :
    rationalLogHeight (c.repr ⟨φ (b i), hUV _ (b i).property⟩ j) ≤
      ((p + 2) ^ 4 + p + 4) ^ 8 := by
  let q := (p + 2) ^ 4 + p + 1
  have hp4 : 0 ≤ (p + 2) ^ 4 := by positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hp4q : (p + 2) ^ 4 ≤ q := by dsimp [q]; linarith
  have hq : 0 ≤ q := hp.trans hpq
  have himage (k : κ) : rationalLogHeight (f.repr (φ (b i)) k) ≤ q :=
    (linearMap_coordinate_logHeight e f φ.toLinearMap hp hι hφ (b i) (hb i) k).trans hp4q
  let x : V := ⟨φ (b i), hUV _ (b i).property⟩
  apply rationalLogHeight_le_of_height
    (embedding_basis_coordinate_height c f V.incl.toLinearMap
      (fun _ _ h => Subtype.ext h) (one_le_ceil_exp q)
      (fun k l => rationalHeightLE_ceil_exp ((hc l k).trans hpq)) x
      (fun k => rationalHeightLE_ceil_exp (himage k)) j)
  have hraw := embedding_coordinate_height_budget (Fintype.card κ) (Fintype.card β)
    ⌈Real.exp q⌉₊ ⌈Real.exp q⌉₊ (show 0 ≤ q + 1 by linarith)
    (hκ.trans (hpq.trans (by linarith))) (hβ.trans (hpq.trans (by linarith)))
    (ceil_exp_le_exp_add_one hq) (ceil_exp_le_exp_add_one hq)
  convert hraw using 1
  dsimp [q]
  congr 2
  ring

end Erdos3

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieFiltration

theorem exists_controlled_marked_top_quotient :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M : Type*}
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      {s d e n : ℕ}
      (D : RationalFilteredNilmanifold L (s + 1) d)
      (E : RationalFilteredNilmanifold M (s + 1) e)
      (φ : L →ₗ⁅ℚ⁆ M)
      (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ E.filtration.layer j)
      (Q : RationalFilteredNilmanifold (L ⧸ D.filtration.layerIdeal (s + 1)) s n)
      (_hQ : Q.filtration = D.filtration.quotientTop),
      (∀ j, ∀ y ∈ E.filtration.layer j, ∃ x ∈ D.filtration.layer j, φ x = y) →
      ∀ {p : ℝ}, 0 ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p →
      Q.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (Q.basis.repr
        (lieQuotientMap (D.filtration.layerIdeal (s + 1)) (D.basis j)) i) ≤ p) →
      (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis i)) j) ≤ p) →
      ∃ m : ℕ, m ≤ e ∧
        ∃ QF : RationalFilteredNilmanifold (M ⧸ E.filtration.layerIdeal (s + 1)) s m,
          QF.filtration = E.filtration.quotientTop ∧
          QF.lattice = E.lattice.map
            (E.filtration.quotientStepHom (E.filtration.layerIdeal (s + 1)) le_rfl) ∧
          QF.GeometryComplexityLE ((p + C) ^ C) ∧
          (∀ i j, rationalLogHeight (QF.basis.repr
            (lieQuotientMap (E.filtration.layerIdeal (s + 1)) (E.basis j)) i) ≤
              (p + C) ^ C) ∧
          (∀ i j, rationalLogHeight
            (QF.basis.repr (D.topQuotientMarkedMap E φ hφ (Q.basis i)) j) ≤
              (p + C) ^ C) ∧
          (∀ j, ∀ x ∈ Q.filtration.layer j,
            D.topQuotientMarkedMap E φ hφ x ∈ QF.filtration.layer j) ∧
          ∀ j, ∀ y ∈ QF.filtration.layer j, ∃ x ∈ Q.filtration.layer j,
            D.topQuotientMarkedMap E φ hφ x = y := by
  obtain ⟨C, hC, hbudget⟩ := exists_nativeMarkedQuotientHeightBudget 11
  refine ⟨C, hC, ?_⟩
  intro L M _ _ _ _ s d e n D E φ hφ Q hQ hsurj p hp hD hE hQgeom hproj hmark
  obtain ⟨m, hm, QF, hQF, hQFL, hQFgeom, hprojF, _⟩ :=
    E.exists_controlled_top_quotient hp hE
  have hpA : p ≤ (p + 11) ^ 11 := by
    calc
      p ≤ (p + 2) ^ 11 := le_power_budget hp (by decide)
      _ ≤ (p + 11) ^ 11 := by gcongr; norm_num
  have hgeoA : (p + 3) ^ 11 ≤ (p + 11) ^ 11 := by gcongr; norm_num
  have hprojA : (p + 3) ^ 5 ≤ (p + 11) ^ 11 := by
    calc
      (p + 3) ^ 5 ≤ (p + 3) ^ 11 :=
        pow_le_pow_right₀ (by linarith) (by decide)
      _ ≤ (p + 11) ^ 11 := hgeoA
  obtain ⟨hAC, hmapC⟩ := hbudget p hp
  refine ⟨m, hm, QF, hQF, hQFL, hQFgeom.mono QF (hgeoA.trans hAC),
    (fun i j => (hprojF j i).trans (hprojA.trans hAC)), ?_, ?_, ?_⟩
  · intro i j
    exact (D.topQuotientMarkedMap_basis_logHeight E φ hφ Q QF (hp.trans hpA)
      (hD.mono D hpA) (hE.mono E hpA) (hQgeom.mono Q hpA)
      (fun i j => (hproj i j).trans hpA) (fun i j => (hmark i j).trans hpA)
      (fun i j => (hprojF j i).trans hprojA) i j).trans hmapC
  · exact D.topQuotientMarkedMap_mem_layer E φ hφ Q hQ QF hQF
  · exact D.topQuotientMarkedMap_layer_surjective E φ hφ Q hQ QF hQF hsurj

end Erdos3.RationalFilteredNilmanifold

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration

end Erdos3.RationalFilteredNilmanifold

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration

universe u

def MarkedRefilteredNativeDiagramData
    {L M : Type u} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d f : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d)
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded) (P : ℝ) : Prop :=
      let V := W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)
      let mark := D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W
      ∃ E : RationalFilteredNilmanifold (D.filtration.gradedRefiltrationSubalgebra W) (s + 1)
          (finrank ℚ (D.filtration.gradedRefiltrationSubalgebra W)),
        E.filtration = D.filtration.gradedRefiltration W ∧
        E.lattice = D.lattice.comap
          (NilpotentLieBCHGroup.map
            (hnil := (D.filtration.gradedRefiltration W).lowerCentralSeries_eq_bot)
            (D.filtration.gradedRefiltrationSubalgebra W).incl) ∧
        E.GeometryComplexityLE (P) ∧
        (∀ i j, rationalLogHeight (D.basis.repr (E.basis j : L) i) ≤ P) ∧
        ∃ EF : RationalFilteredNilmanifold (Fmark.filtration.gradedRefiltrationSubalgebra V) (s + 1)
            (finrank ℚ (Fmark.filtration.gradedRefiltrationSubalgebra V)),
          EF.filtration = Fmark.filtration.gradedRefiltration V ∧
          EF.lattice = Fmark.lattice.comap
            (NilpotentLieBCHGroup.map
              (hnil := (Fmark.filtration.gradedRefiltration V).lowerCentralSeries_eq_bot)
              (Fmark.filtration.gradedRefiltrationSubalgebra V).incl) ∧
          EF.GeometryComplexityLE (P) ∧
          (∀ i j, rationalLogHeight (Fmark.basis.repr (EF.basis j : M) i) ≤ P) ∧
          (∀ i j, rationalLogHeight (EF.basis.repr (mark (E.basis i)) j) ≤ P) ∧
          (∀ j, ∀ x ∈ E.filtration.layer j, mark x ∈ EF.filtration.layer j) ∧
          (∀ j, ∀ y ∈ EF.filtration.layer j, ∃ x ∈ E.filtration.layer j, mark x = y) ∧
          (∃ m : ℕ, m ≤ finrank ℚ (D.filtration.gradedRefiltrationSubalgebra W) ∧
            ∃ Q : RationalFilteredNilmanifold
                ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s m,
              Q.filtration = E.filtration.quotientTop ∧
              Q.lattice = E.lattice.map
                (E.filtration.quotientStepHom (E.filtration.layerIdeal (s + 1)) le_rfl) ∧
              Q.GeometryComplexityLE (P) ∧
              ∀ i j, rationalLogHeight (Q.basis.repr
                (lieQuotientMap (E.filtration.layerIdeal (s + 1)) (E.basis j)) i) ≤ P) ∧
          (∃ m : ℕ, m ≤ finrank ℚ (Fmark.filtration.gradedRefiltrationSubalgebra V) ∧
            ∃ QF : RationalFilteredNilmanifold
                ((Fmark.filtration.gradedRefiltrationSubalgebra V) ⧸ EF.filtration.layerIdeal (s + 1)) s m,
              QF.filtration = EF.filtration.quotientTop ∧
              QF.lattice = EF.lattice.map
                (EF.filtration.quotientStepHom (EF.filtration.layerIdeal (s + 1)) le_rfl) ∧
              QF.GeometryComplexityLE (P) ∧
              ∀ i j, rationalLogHeight (QF.basis.repr
                (lieQuotientMap (EF.filtration.layerIdeal (s + 1)) (EF.basis j)) i) ≤ P)

theorem exists_marked_refiltered_native_diagram :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {L M : Type u} {κ : Type*} [LieRing L] [LieAlgebra ℚ L]
      [LieRing M] [LieAlgebra ℚ M] [Fintype κ]
      {s d f n k : ℕ}
      (D : RationalFilteredNilmanifold L (s + 1) d)
      (Fmark : RationalFilteredNilmanifold M (s + 1) f)
      (b : Basis (Fin n) ℚ L) (ω : Fin n → ℕ)
      (hD : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (c : Basis (Fin k) ℚ M) (ν : Fin k → ℕ)
      (_hF : ∀ j, Fmark.filtration.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
      (φ : L →ₗ⁅ℚ⁆ M)
      (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j),
      (∀ j, ∀ y ∈ Fmark.filtration.layer j, ∃ x ∈ D.filtration.layer j, φ x = y) →
    ∀ (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
      (v : κ → D.filtration.AssociatedGraded),
      Submodule.span ℚ (Set.range v) = W.toSubmodule →
      BasisGradedSubmodule (D.filtration.associatedGradedBasis b ω hD) ω W.toSubmodule →
    ∀ {p : ℝ}, 0 ≤ p → D.GeometryComplexityLE p → Fmark.GeometryComplexityLE p →
      (Fintype.card κ : ℝ) ≤ p →
      (∀ i j, rationalLogHeight (D.basis.repr (b i) j) ≤ p) →
      (∀ i j, rationalLogHeight (Fmark.basis.repr (c i) j) ≤ p) →
      (∀ i j, rationalLogHeight (Fmark.basis.repr (φ (D.basis i)) j) ≤ p) →
      (∀ i j, rationalLogHeight ((D.filtration.associatedGradedBasis b ω hD).repr (v i) j) ≤ p) →
      MarkedRefilteredNativeDiagramData D Fmark φ hφ W ((p + C) ^ C) := by
  obtain ⟨A, _, hmodels⟩ := exists_adapted_single_refiltered_models
  obtain ⟨C, hC, hbudget⟩ := exists_markedRefilteredModelInput_budget A
  refine ⟨C, hC, ?_⟩
  intro L M κ _ _ _ _ _ s d f n k D Fmark b ω hD c ν hF φ hφ hsurj
    W v hspan hW p hp hDgeom hFgeom hκ hb hc hφheight hv
  obtain ⟨hq, hpq, hmapq, ht, hqt, himaget, hr, hpr, hmodelr⟩ :=
    markedRefilteredModelInput_bounds A hp
  obtain ⟨hrC, hmarkC⟩ := hbudget p hp
  have hpt := hpq.trans hqt
  have hmodelC := hmodelr.trans hrC
  have hbn : (Fintype.card (Fin n) : ℝ) ≤ p :=
    (D.basis_geometry_of_forward_height b hp hDgeom
      (fun i j => (hb i j).trans (by linarith))).1
  have hadapted (i : Fin n) (j : Fin k) :
      rationalLogHeight (c.repr (φ (b i)) j) ≤ markedRefilteredBasisInput p :=
    (D.markedMap_basisChange_logHeight Fmark b c φ.toLinearMap hp hDgeom hFgeom
      hb hc hφheight i j).trans hmapq
  let V := W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)
  let imagev : κ → Fmark.filtration.AssociatedGraded := D.filtration.gradedImageSpanningFamily Fmark.filtration φ hφ v
  obtain ⟨himage, _, himageH⟩ :=
    D.filtration.gradedImage_bounded_spanning Fmark.filtration φ hφ
      b ω hD c ν hF W v hspan hW hq (hbn.trans hpq)
      (fun i j => (hv i j).trans hpq) hadapted
  obtain ⟨E, hEF, hEL, hEgeom, hEinc, m, hm, Q, hQF, hQL, hQgeom, hQmap⟩ :=
    hmodels D b ω hD W v hspan ht (hDgeom.mono D hpt) (hκ.trans hpt)
      (fun i j => (hb i j).trans hpt) (fun i j => (hv i j).trans hpt)
  have himageSpan : Submodule.span ℚ (Set.range imagev) = V.toSubmodule := by
    with_reducible exact himage
  have htarget := by
    with_reducible exact (hmodels (L := M) (κ := κ) (s := s) (d := f) (n := k) Fmark c ν hF V imagev himageSpan (p := markedRefilteredMapInput p) ht (hFgeom.mono Fmark hpt) (hκ.trans hpt) (fun i j => (hc i j).trans hpt) (fun i j => (himageH i j).trans himaget))
  obtain ⟨EF, hEFF, hEFL, hEFgeom, hEFinc, mf, hmf, QF, hQFF, hQFL, hQFgeom, hQFmap⟩ := htarget
  let mark := D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W
  have hmarked (i) (j) : rationalLogHeight (EF.basis.repr (mark (E.basis i)) j) ≤
      (p + C) ^ C := by
    apply (restrictedLieMap_coordinate_logHeight D.basis Fmark.basis
      (D.filtration.gradedRefiltrationSubalgebra W)
      (Fmark.filtration.gradedRefiltrationSubalgebra V) E.basis EF.basis φ
      (fun x hx => D.filtration.gradedRefiltrationLayer_map_mem Fmark.filtration φ hφ W 1 x hx)
      hr (by simpa only [Fintype.card_fin] using hDgeom.1.trans hpr)
      (by simpa only [Fintype.card_fin] using hFgeom.1.trans hpr)
      (by simpa only [Fintype.card_fin] using hEFgeom.1.trans hmodelr)
      (fun i j => (hφheight i j).trans hpr)
      (fun i j => (hEinc j i).trans hmodelr)
      (fun i j => (hEFinc j i).trans hmodelr) i j).trans hmarkC
  unfold MarkedRefilteredNativeDiagramData
  refine ⟨E, hEF, hEL, hEgeom.mono E hmodelC,
    fun i j => (hEinc i j).trans hmodelC,
    EF, hEFF, hEFL, hEFgeom.mono EF hmodelC,
    fun i j => (hEFinc i j).trans hmodelC, hmarked, ?_, ?_, ?_, ?_⟩
  · intro j x hx
    rw [hEF] at hx
    rw [hEFF]
    exact D.filtration.gradedRefiltrationMap_mem_layer Fmark.filtration φ hφ W j x hx
  · intro j y hy
    rw [hEFF] at hy
    obtain ⟨x, hx, heq⟩ := D.filtration.gradedRefiltrationMap_layer_surjective
      Fmark.filtration b ω hD c ν hF φ hφ W hW hsurj j y hy
    exact ⟨x, by rwa [hEF], heq⟩
  · exact ⟨m, hm, Q, hQF, hQL, hQgeom.mono Q hmodelC,
      fun i j => (hQmap i j).trans hmodelC⟩
  · exact ⟨mf, hmf, QF, hQFF, hQFL, hQFgeom.mono QF hmodelC,
      fun i j => (hQFmap i j).trans hmodelC⟩

end Erdos3.RationalFilteredNilmanifold

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L M : Type u} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d f : ℕ}
    (D : RationalFilteredNilmanifold L (s + 1) d)
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

end Erdos3.RationalFilteredNilmanifold

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration NilpotentLieBCHGroup
open scoped TensorProduct NNReal

end Erdos3.RationalFilteredNilmanifold

end

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration

universe u

end Erdos3.RationalFilteredNilmanifold

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedFixedReduction
namespace OAI

section

namespace Erdos3.NativeMixedReductionData

open scoped BigOperators

variable {s : ℕ} {p P : ℝ}
  {V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p}
  (D : NativeMixedReductionData V P)

def translationCodeEquiv (k : Fin 4 → Fin V.outputDim) :
    D.TranslationCode k ≃
      (Σ a₂ : MixedExpansionIndex V, Σ a₄ : MixedExpansionIndex V,
        Fin (D.translation.selectedExpansion (k 1) a₂).count ×
          Fin (D.translation.selectedExpansion (k 3) a₄).count) where
  toFun t := ⟨t.second, t.fourth, t.secondTerm, t.fourthTerm⟩
  invFun t := ⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance translationCodeFintype (k : Fin 4 → Fin V.outputDim) :
    Fintype (D.TranslationCode k) :=
  Fintype.ofEquiv _ (D.translationCodeEquiv k).symm

def reductionCodeEquiv (k : Fin 4 → Fin V.outputDim) :
    D.ReductionCode k ≃ (Σ t : D.TranslationCode k,
      Fin (D.parallelogram (D.translationCoordinates k t)).count) where
  toFun a := ⟨a.translations, a.term⟩
  invFun a := ⟨a.1, a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance reductionCodeFintype (k : Fin 4 → Fin V.outputDim) :
    Fintype (D.ReductionCode k) :=
  Fintype.ofEquiv _ (D.reductionCodeEquiv k).symm

theorem translationCode_card (k : Fin 4 → Fin V.outputDim) :
    (Fintype.card (D.TranslationCode k) : ℝ) ≤ Real.exp (4 * P) := by
  classical
  have he := D.translation.right_dimension
  calc
    (Fintype.card (D.TranslationCode k) : ℝ) =
        ∑ a₂ : MixedExpansionIndex V, ∑ a₄ : MixedExpansionIndex V,
          ((D.translation.selectedExpansion (k 1) a₂).count : ℝ) *
            ((D.translation.selectedExpansion (k 3) a₄).count : ℝ) := by
      rw [Fintype.card_congr (D.translationCodeEquiv k)]
      simp only [Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin,
        Nat.cast_sum, Nat.cast_mul]
    _ ≤ ∑ _ : MixedExpansionIndex V, ∑ _ : MixedExpansionIndex V,
        Real.exp P * Real.exp P := by
      apply Finset.sum_le_sum
      intro a₂ _
      apply Finset.sum_le_sum
      intro a₄ _
      exact mul_le_mul (D.translation.selectedExpansion (k 1) a₂).count_bound
        (D.translation.selectedExpansion (k 3) a₄).count_bound
        (Nat.cast_nonneg _) (Real.exp_nonneg _)
    _ = (Fintype.card (MixedExpansionIndex V) : ℝ) *
        ((Fintype.card (MixedExpansionIndex V) : ℝ) * (Real.exp P * Real.exp P)) := by
      simp
    _ ≤ Real.exp P * (Real.exp P * (Real.exp P * Real.exp P)) := by
      gcongr
    _ = Real.exp (4 * P) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

theorem reductionCode_card (k : Fin 4 → Fin V.outputDim) :
    (Fintype.card (D.ReductionCode k) : ℝ) ≤ Real.exp (5 * P) := by
  classical
  calc
    (Fintype.card (D.ReductionCode k) : ℝ) =
        ∑ t : D.TranslationCode k, ((D.parallelogram (D.translationCoordinates k t)).count : ℝ) := by
      rw [Fintype.card_congr (D.reductionCodeEquiv k)]
      simp only [Fintype.card_sigma, Fintype.card_fin, Nat.cast_sum]
    _ ≤ ∑ _ : D.TranslationCode k, Real.exp P := by
      exact Finset.sum_le_sum (fun t _ => (D.parallelogram (D.translationCoordinates k t)).count_bound)
    _ = (Fintype.card (D.TranslationCode k) : ℝ) * Real.exp P := by simp
    _ ≤ Real.exp (4 * P) * Real.exp P :=
      mul_le_mul_of_nonneg_right (D.translationCode_card k) (Real.exp_nonneg P)
    _ = Real.exp (5 * P) := by
      rw [← Real.exp_add]
      congr 1
      ring

end Erdos3.NativeMixedReductionData

end

section

namespace Erdos3.NativeMixedReductionData

open scoped BigOperators

variable {s : ℕ} {p P : ℝ}
  {V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p}
  (D : NativeMixedReductionData V P)

theorem double_translation (h₁ h₂ h₃ h₄ δ : ℤ)
    (hrel : -h₁ + h₂ + h₃ - h₄ = 0) {X : Type*} (S : Finset X) (n : X → ℤ)
    (k : Fin 4 → Fin V.outputDim) (f : X → ℂ) (q : ℝ)
    (hcorr : Real.exp (-q) ≤
      ‖𝔼 u ∈ S, f u * translatedMixedProduct V k h₁ h₂ h₃ h₄ δ (n u)‖) :
    ∃ (t : D.TranslationCode k) (c : D.LowerCode t h₂ h₄ δ),
      Real.exp (-(q + 6 * P)) ≤ ‖𝔼 u ∈ S,
        f u * D.translationGlobal k t ![h₁, h₂, h₃, n u, δ] *
          D.translationLower t h₂ h₄ δ c (n u) *
          untranslatedMixedProduct V (D.translationCoordinates k t) h₁ h₂ h₃ h₄ (n u)‖ := by
  let f₄ (u : X) := f u * star (V.eval (k 0) (fun j => correlationInput h₁ (n u) j.1)) *
    V.eval (k 1) (fun j => correlationInput h₂ (n u + δ) j.1) *
    V.eval (k 2) (fun j => correlationInput h₃ (n u) j.1)
  have hc₄ : Real.exp (-q) ≤ ‖𝔼 u ∈ S, f₄ u *
      star (V.eval (k 3) (fun j => correlationInput h₄ (n u + δ) j.1))‖ := by
    simpa only [f₄, translatedMixedProduct, fourPointProduct, mul_assoc] using hcorr
  obtain ⟨a₄, b₄, c₄, h₄'⟩ := D.translation_negative h₄ δ S n (k 3) f₄ q hc₄
  let f₂ (u : X) := f u * star (V.eval (k 0) (fun j => correlationInput h₁ (n u) j.1)) *
    V.eval (k 2) (fun j => correlationInput h₃ (n u) j.1) *
    star (D.correction h₄ δ (k 3) a₄ b₄ c₄ (n u))
  have hc₂ : Real.exp (-(q + 3 * P)) ≤ ‖𝔼 u ∈ S, f₂ u *
      V.eval (k 1) (fun j => correlationInput h₂ (n u + δ) j.1)‖ := by
    simpa only [f₄, f₂, mul_assoc, mul_left_comm, mul_comm] using h₄'
  obtain ⟨a₂, b₂, c₂, h₂'⟩ := D.translation_positive h₂ δ S n (k 1) f₂ (q + 3 * P) hc₂
  let t : D.TranslationCode k := ⟨a₂, a₄, b₂, b₄⟩
  let c : D.LowerCode t h₂ h₄ δ := ⟨c₂, c₄⟩
  refine ⟨t, c, ?_⟩
  rw [show (q + 3 * P) + 3 * P = q + 6 * P by ring] at h₂'
  have hmean : (𝔼 u ∈ S, f₂ u * D.correction h₂ δ (k 1) a₂ b₂ c₂ (n u)) =
      𝔼 u ∈ S, f u * D.translationGlobal k t ![h₁, h₂, h₃, n u, δ] *
        D.translationLower t h₂ h₄ δ c (n u) *
        untranslatedMixedProduct V (D.translationCoordinates k t) h₁ h₂ h₃ h₄ (n u) := by
    apply Finset.expect_congr rfl
    intro u _
    exact D.correction_factorization k t h₁ h₂ h₃ h₄ δ (n u) c (f u) hrel
  rwa [← hmean]

end Erdos3.NativeMixedReductionData

end

section

namespace Erdos3.NativeMixedReductionData

open scoped BigOperators

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s : ℕ} {p P : ℝ}
  {V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p}
  (D : NativeMixedReductionData V P)

theorem reduce_quadruple (h₁ h₂ h₃ h₄ δ : ℤ)
    (hrel : -h₁ + h₂ + h₃ - h₄ = 0) {X : Type*} (S : Finset X) (n : X → ℤ)
    (k : Fin 4 → Fin V.outputDim) (f : X → ℂ) (q : ℝ)
    (hcorr : Real.exp (-q) ≤
      ‖𝔼 u ∈ S, f u * translatedMixedProduct V k h₁ h₂ h₃ h₄ δ (n u)‖) :
    ∃ (a : D.ReductionCode k) (c : D.LowerCode a.translations h₂ h₄ δ),
      Real.exp (-(q + 7 * P)) ≤ ‖𝔼 u ∈ S,
        f u * D.globalError k a ![h₁, h₂, h₃, n u, δ] *
          D.translationLower a.translations h₂ h₄ δ c (n u)‖ := by
  obtain ⟨t, c, ht⟩ := D.double_translation h₁ h₂ h₃ h₄ δ hrel S n k f q hcorr
  let g (u : X) := f u * D.translationGlobal k t ![h₁, h₂, h₃, n u, δ] *
    D.translationLower t h₂ h₄ δ c (n u)
  have hg : Real.exp (-(q + 6 * P)) ≤ ‖𝔼 u ∈ S, g u *
      mixedParallelogramProduct V (D.translationCoordinates k t) ![h₁, h₂, h₃, n u]‖ := by
    simpa only [g, untranslatedMixedProduct_eq V (D.translationCoordinates k t)
      h₁ h₂ h₃ h₄ _ hrel] using ht
  obtain ⟨j, hj⟩ := (D.parallelogram (D.translationCoordinates k t)).select_sample_product_correlation
    S (fun u => ![h₁, h₂, h₃, n u]) g hg
  refine ⟨⟨t, j⟩, c, ?_⟩
  rw [show (q + 6 * P) + P = q + 7 * P by ring] at hj
  have hglobal (u : X) : D.globalError k ⟨t, j⟩ ![h₁, h₂, h₃, n u, δ] =
      D.translationGlobal k t ![h₁, h₂, h₃, n u, δ] *
        ((D.parallelogram (D.translationCoordinates k t)).test j).eval ![h₁, h₂, h₃, n u] := rfl
  simpa only [hglobal, g, mul_assoc, mul_left_comm, mul_comm] using hj

end Erdos3.NativeMixedReductionData

end

section

namespace Erdos3.NativeMixedReductionData

open scoped BigOperators

variable {s : ℕ} {p P : ℝ}
  {V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p}
  (D : NativeMixedReductionData V P)

theorem reduce_family {I X : Type*} (H : Finset I) (hH : H.Nonempty)
    (S : I → Finset X) (n : I → X → ℤ) (h₁ h₂ h₃ h₄ δ : I → ℤ)
    (k : Fin 4 → Fin V.outputDim) (f : I → X → ℂ) (q : ℝ)
    (hrel : ∀ i ∈ H, -h₁ i + h₂ i + h₃ i - h₄ i = 0)
    (hcorr : ∀ i ∈ H, Real.exp (-q) ≤
      ‖𝔼 u ∈ S i, f i u * translatedMixedProduct V k (h₁ i) (h₂ i) (h₃ i) (h₄ i) (δ i) (n i u)‖) :
    ∃ (a : D.ReductionCode k) (Q : Finset I), Q ⊆ H ∧ Q.Nonempty ∧
      Real.exp (-(5 * P)) * (H.card : ℝ) ≤ (Q.card : ℝ) ∧
      ∀ i ∈ Q, ∃ c : D.LowerCode a.translations (h₂ i) (h₄ i) (δ i),
        Real.exp (-(q + 7 * P)) ≤ ‖𝔼 u ∈ S i,
          f i u * D.globalError k a ![h₁ i, h₂ i, h₃ i, n i u, δ i] *
            D.translationLower a.translations (h₂ i) (h₄ i) (δ i) c (n i u)‖ := by
  let rel (i : I) (_ : Unit) (a : D.ReductionCode k) : Prop :=
    ∃ c : D.LowerCode a.translations (h₂ i) (h₄ i) (δ i),
      Real.exp (-(q + 7 * P)) ≤ ‖𝔼 u ∈ S i,
        f i u * D.globalError k a ![h₁ i, h₂ i, h₃ i, n i u, δ i] *
          D.translationLower a.translations (h₂ i) (h₄ i) (δ i) c (n i u)‖
  have hchoice : ∀ i ∈ H, ∀ b, ∃ a, rel i b a := by
    intro i hi _
    exact D.reduce_quadruple (h₁ i) (h₂ i) (h₃ i) (h₄ i) (δ i) (hrel i hi)
      (S i) (n i) k (f i) q (hcorr i hi)
  obtain ⟨a, Q, hsub, hQ, hsize, hfixed⟩ :=
    exists_large_fixed_choices H hH rel hchoice (D.reductionCode_card k)
  refine ⟨a (), Q, hsub, hQ, ?_, fun i hi => hfixed i hi ()⟩
  simpa only [Fintype.card_unit, Nat.cast_one, mul_one] using hsize

end Erdos3.NativeMixedReductionData

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativeRetainedIntegerMultilinearQuadruples
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def cyclicBranchOffset {N : ℕ} (h : ZMod N) (branch : Bool) : ℤ :=
  (h.val : ℤ) - if branch then (N : ℤ) else 0

theorem cyclicTranslationOffset_eq_branch {N : ℕ} (h : ZMod N) (a : ℕ) :
    cyclicTranslationOffset h a = cyclicBranchOffset h (decide (N - h.val ≤ a)) := by
  by_cases hwrap : N - h.val ≤ a <;> simp [cyclicTranslationOffset, cyclicBranchOffset, hwrap]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_fourPoint_integer_interval {N : ℕ} [NeZero N]
    (f₁ f₂ f₃ f₄ : ℤ → ℂ) (a : ZMod N) {ρ B : ℝ}
    (hρ : 0 < ρ) (hB : 0 < B)
    (hbound : ∀ x : ZMod N,
      ‖fourPointProduct (fun x : ZMod N => f₁ x.val) (fun x : ZMod N => f₂ x.val)
        (fun x : ZMod N => f₃ x.val) (fun x : ZMod N => f₄ x.val) a x‖ ≤ B)
    (hcorr : ρ ≤ ‖𝔼 x : ZMod N,
      fourPointProduct (fun x : ZMod N => f₁ x.val) (fun x : ZMod N => f₂ x.val)
        (fun x : ZMod N => f₃ x.val) (fun x : ZMod N => f₄ x.val) a x‖) :
    ∃ (branch : Bool) (c len : ℕ), 0 < len ∧ c + len ≤ N ∧
      2 * ((len : ℤ) - 1) < N ∧
      ρ / 20 ≤ ‖𝔼 n ∈ Finset.Ico (c : ℤ) (c + len),
        fourPointProduct f₁ f₂ f₃ f₄ (cyclicBranchOffset a branch) n‖ ∧
      ρ / (20 * B) ≤ (len : ℝ) / N := by
  let shifts : Fin 2 → ZMod N := ![0, a]
  let u : Fin 2 → ℤ → ℂ := ![(fun n => f₁ n * star (f₃ n)), (fun n => star (f₂ n) * f₄ n)]
  have heval (x : ZMod N) : star (translatedCyclicProduct shifts u x) =
      fourPointProduct (fun x : ZMod N => f₁ x.val) (fun x : ZMod N => f₂ x.val)
        (fun x : ZMod N => f₃ x.val) (fun x : ZMod N => f₄ x.val) a x := by
    simp only [translatedCyclicProduct, shifts, u, Fin.prod_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, zero_add, star_mul, star_star,
      fourPointProduct, add_comm a x]
    ring
  have hu (x : ZMod N) : ‖translatedCyclicProduct shifts u x‖ ≤ B := by
    rw [← norm_star, heval]
    exact hbound x
  have hc : ρ ≤ ‖finiteCorrelation Finset.univ (fun _ : ZMod N => (1 : ℂ))
      (translatedCyclicProduct shifts u)‖ := by
    simpa only [finiteCorrelation, one_mul, heval] using hcorr
  obtain ⟨c, hlen, hN, hshort, hcor, hvol⟩ := exists_correlating_integer_product_interval
    shifts u (fun _ : ZMod N => (1 : ℂ)) hρ hB (fun _ => by norm_num) hu hc
  norm_num only [Fintype.card_fin, Nat.cast_ofNat] at hcor hvol
  let len := intervalCutUpper (commonCyclicCuts shifts) N c.val - c.val
  have hcN : c.val < N := by omega
  have hoff : cyclicTranslationOffset (shifts 0) c.val = 0 := by
    simp [shifts, cyclicTranslationOffset, Nat.not_le.mpr hcN]
  let branch := decide (N - a.val ≤ c.val)
  have hprod (n : ℤ) : star (∏ i, u i (n + cyclicTranslationOffset (shifts i) c.val)) =
      fourPointProduct f₁ f₂ f₃ f₄ (cyclicBranchOffset a branch) n := by
    rw [Fin.prod_univ_two, hoff]
    simp only [u, shifts, Matrix.cons_val_zero, Matrix.cons_val_one, add_zero,
      cyclicTranslationOffset_eq_branch, star_mul, star_star, fourPointProduct, branch]
    ring
  refine ⟨branch, c.val, len, hlen, hN, hshort, ?_, ?_⟩
  · simpa only [finiteCorrelation, one_mul, hprod] using hcor
  · exact hvol

end Erdos3

end

section

namespace Erdos3.NativeCrossWitnesses

open scoped BigOperators TensorProduct

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

variable {s N : ℕ} [NeZero N] {p : ℝ} {f₀ f₁ : ZMod N → ℂ}
  {m : ZMod N → ZMod N → ℂ} {H : Finset (ZMod N)}
  (U : NativeCrossWitnesses s N p f₀ f₁ m H)

noncomputable def integerLower (h : H) (n : ℤ) : ℂ := (U h).test.eval (fun _ => n)

noncomputable def integerProduct (M : ZMod N → ℤ → ℂ) (h : H) (n : ℤ) : ℂ :=
  M h.val n * U.integerLower h n

theorem integerLower_val (h : H) (x : ZMod N) : U.integerLower h x.val = U.lower h x := rfl

theorem integerProduct_val (M : ZMod N → ℤ → ℂ)
    (hM : ∀ h x, m h x = M h x.val) (h : H) (x : ZMod N) :
    U.integerProduct M h x.val = U.product h x := by
  rw [integerProduct, integerLower_val, product, hM]
  rfl

theorem extension_quadruple_integer (M : ZMod N → ℤ → ℂ)
    (hM : ∀ h x, m h x = M h x.val) (a h k : ZMod N)
    (h₁ : h ∈ H) (h₂ : h - a ∈ H) (h₃ : k ∈ H) (h₄ : k - a ∈ H) :
    additiveQuadrupleCorrelation U.extension a h k =
      ‖𝔼 x : ZMod N,
        fourPointProduct (fun x : ZMod N => U.integerProduct M ⟨h, h₁⟩ x.val)
          (fun x : ZMod N => U.integerProduct M ⟨h - a, h₂⟩ x.val)
          (fun x : ZMod N => U.integerProduct M ⟨k, h₃⟩ x.val)
          (fun x : ZMod N => U.integerProduct M ⟨k - a, h₄⟩ x.val) a x‖ := by
  simp only [additiveQuadrupleCorrelation, fourPointProduct, U.integerProduct_val M hM,
    U.extension_of_mem h h₁, U.extension_of_mem (h - a) h₂,
    U.extension_of_mem k h₃, U.extension_of_mem (k - a) h₄]

theorem exists_integer_quadruple_interval (M : ZMod N → ℤ → ℂ)
    (hM : ∀ h x, m h x = M h x.val) (hm : ∀ h x, ‖m h x‖ ≤ 1)
    (a h k : ZMod N) (h₁ : h ∈ H) (h₂ : h - a ∈ H) (h₃ : k ∈ H) (h₄ : k - a ∈ H)
    {ρ : ℝ} (hρ : 0 < ρ) (hcorr : ρ ≤ additiveQuadrupleCorrelation U.extension a h k) :
    ∃ (branch : Bool) (c len : ℕ), 0 < len ∧ c + len ≤ N ∧
      2 * ((len : ℤ) - 1) < N ∧
      ρ / 20 ≤ ‖𝔼 n ∈ Finset.Ico (c : ℤ) (c + len),
        fourPointProduct (U.integerProduct M ⟨h, h₁⟩) (U.integerProduct M ⟨h - a, h₂⟩)
          (U.integerProduct M ⟨k, h₃⟩) (U.integerProduct M ⟨k - a, h₄⟩)
          (cyclicBranchOffset a branch) n‖ ∧
      ρ / (20 * Real.exp (4 * p)) ≤ (len : ℝ) / N := by
  apply exists_fourPoint_integer_interval _ _ _ _ a hρ (Real.exp_pos _)
  · intro x
    simp only [fourPointProduct, U.integerProduct_val M hM, norm_mul, norm_star]
    calc
      _ ≤ Real.exp p * Real.exp p * Real.exp p * Real.exp p :=
        mul_le_mul (mul_le_mul (mul_le_mul (U.product_norm hm _ _) (U.product_norm hm _ _)
          (norm_nonneg _) (Real.exp_nonneg _)) (U.product_norm hm _ _)
          (norm_nonneg _) (by positivity)) (U.product_norm hm _ _) (norm_nonneg _) (by positivity)
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  · rwa [← U.extension_quadruple_integer M hM a h k h₁ h₂ h₃ h₄]

theorem integerProduct_fourPoint_factorization (A B : ZMod N → ℤ → ℂ)
    (h₁ h₂ h₃ h₄ : H) (a n : ℤ) :
    fourPointProduct (U.integerProduct (fun h x => A h x * B h x) h₁)
      (U.integerProduct (fun h x => A h x * B h x) h₂)
      (U.integerProduct (fun h x => A h x * B h x) h₃)
      (U.integerProduct (fun h x => A h x * B h x) h₄) a n =
      fourPointProduct (A h₁) (A h₂) (A h₃) (A h₄) a n *
      fourPointProduct (B h₁) (B h₂) (B h₃) (B h₄) a n *
      fourPointProduct (U.integerLower h₁) (U.integerLower h₂)
        (U.integerLower h₃) (U.integerLower h₄) a n := by
  simp only [fourPointProduct, integerProduct, star_mul]
  ring

theorem exists_integer_quadruple_interval_budget (M : ZMod N → ℤ → ℂ)
    (hM : ∀ h x, m h x = M h x.val) (hm : ∀ h x, ‖m h x‖ ≤ 1)
    (a h k : ZMod N) (h₁ : h ∈ H) (h₂ : h - a ∈ H) (h₃ : k ∈ H) (h₄ : k - a ∈ H)
    {b : ℝ} (hcorr : Real.exp (-b) ≤ additiveQuadrupleCorrelation U.extension a h k) :
    ∃ (branch : Bool) (c len : ℕ), 0 < len ∧ c + len ≤ N ∧
      2 * ((len : ℤ) - 1) < N ∧
      Real.exp (-(b + 4 * p + 5)) ≤ ‖𝔼 n ∈ Finset.Ico (c : ℤ) (c + len),
        fourPointProduct (U.integerProduct M ⟨h, h₁⟩) (U.integerProduct M ⟨h - a, h₂⟩)
          (U.integerProduct M ⟨k, h₃⟩) (U.integerProduct M ⟨k - a, h₄⟩)
          (cyclicBranchOffset a branch) n‖ ∧
      Real.exp (-(b + 4 * p + 5)) ≤ (len : ℝ) / N := by
  have hp : 0 ≤ p := (Nat.cast_nonneg (U ⟨h, h₁⟩).dim).trans (U ⟨h, h₁⟩).complexity.1.1
  have h20 : (20 : ℝ) ≤ Real.exp 5 :=
    (by norm_num : (20 : ℝ) ≤ 2 ^ 5).trans (two_pow_le_exp_of_le 5 le_rfl)
  have hfrac : Real.exp (-(b + 4 * p + 5)) ≤ Real.exp (-b) / (20 * Real.exp (4 * p)) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 20 * Real.exp (4 * p))).mpr
    calc
      _ ≤ Real.exp (-(b + 4 * p + 5)) * (Real.exp 5 * Real.exp (4 * p)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h20 (Real.exp_nonneg _))
          (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hone : 1 ≤ Real.exp (4 * p) := Real.one_le_exp_iff.mpr (by positivity)
  have hfrac' : Real.exp (-(b + 4 * p + 5)) ≤ Real.exp (-b) / 20 :=
    hfrac.trans (div_le_div_of_nonneg_left (Real.exp_nonneg _) (by norm_num)
      (by nlinarith only [hone]))
  obtain ⟨branch, c, len, hlen, hN, hshort, hc, hvol⟩ := U.exists_integer_quadruple_interval
    M hM hm a h k h₁ h₂ h₃ h₄ (Real.exp_pos (-b)) hcorr
  exact ⟨branch, c, len, hlen, hN, hshort, hfrac'.trans hc, hfrac.trans hvol⟩

end Erdos3.NativeCrossWitnesses

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

namespace NativeCorrelationStructure

noncomputable def multilinearFactor {s r N : ℕ} [NeZero N] {p q : ℝ} {f : ZMod N → ℂ}
    (W : NativeCorrelationStructure s r N p f)
    (V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) q)
    (k : Fin V.outputDim) (i : Fin W.family.outputDim) (h : ZMod N) (n : ℤ) : ℂ :=
  V.eval k (fun j => correlationInput (h.val : ℤ) n j.1) * W.family.eval i h n

end NativeCorrelationStructure

theorem exists_integer_multilinear_quadruples (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p f), (∀ x, ‖f x‖ ≤ 1) →
      ∃ V : NativeMultidegreeNilcharacter
          (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) ((p + C) ^ C),
        V.dim ≤ 2 ^ (s + 1) * W.mixed.dim ∧
        (∀ (e : ReplicatedPermutation (mixedCorrelationDegree s)) k x,
          V.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree s) e).symm j)) =
            V.eval k x) ∧
        ∃ (k : Fin V.outputDim) (i : Fin W.family.outputDim) (weight : ZMod N → ℂ)
          (H : Finset (ZMod N)), (∀ x, ‖weight x‖ ≤ 1) ∧ H ⊆ W.shifts ∧ H.Nonempty ∧
          CyclicShortShiftSet H ∧
          Real.exp (-((p + C) ^ C)) * Fintype.card (ZMod N) ≤ (H.card : ℝ) ∧
          ∃ U : NativeCrossWitnesses (s - 1) N ((p + C) ^ C)
              (fun x => f x * star (weight x)) f
              (fun h x => W.multilinearFactor V k i h x.val) H,
            ∃ Q : Finset (ZMod N × ZMod N × ZMod N), Q.Nonempty ∧
              Real.exp (-((p + C) ^ C)) * (Fintype.card (ZMod N) : ℝ) ^ 3 ≤ (Q.card : ℝ) ∧
              ∀ t ∈ Q, ∃ (h₁ : t.2.1 ∈ H) (h₂ : t.2.1 - t.1 ∈ H)
                (h₃ : t.2.2 ∈ H) (h₄ : t.2.2 - t.1 ∈ H),
                -(t.2.1.val : ℤ) + (t.2.1 - t.1).val + t.2.2.val - (t.2.2 - t.1).val = 0 ∧
                Real.exp (-((p + C) ^ C)) ≤
                  additiveQuadrupleCorrelation U.extension t.1 t.2.1 t.2.2 ∧
                ∃ (branch : Bool) (c len : ℕ), 0 < len ∧ c + len ≤ N ∧
                  2 * ((len : ℤ) - 1) < N ∧
                  Real.exp (-((p + C) ^ C)) ≤ ‖𝔼 n ∈ Finset.Ico (c : ℤ) (c + len),
                    fourPointProduct
                      (U.integerProduct (W.multilinearFactor V k i) ⟨t.2.1, h₁⟩)
                      (U.integerProduct (W.multilinearFactor V k i) ⟨t.2.1 - t.1, h₂⟩)
                      (U.integerProduct (W.multilinearFactor V k i) ⟨t.2.2, h₃⟩)
                      (U.integerProduct (W.multilinearFactor V k i) ⟨t.2.2 - t.1, h₄⟩)
                      (cyclicBranchOffset t.1 branch) n‖ ∧
                  Real.exp (-((p + C) ^ C)) ≤ (len : ℝ) / N := by
  obtain ⟨a, _, hmulti⟩ := exists_multilinear_quadruples s
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (17 * (X + Polynomial.C a) ^ a + 20)
  refine ⟨C, hC, ?_⟩
  intro r N _ p f W hf
  have hp : 0 ≤ p := (Nat.cast_nonneg W.mixed.dim).trans W.mixed.complexity.1.1
  let q := (p + a) ^ a
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hcost : 17 * q + 20 ≤ (p + C) ^ C := by
    simpa [X, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith only [hq, hcost]
  have hHC : q + 1 ≤ (p + C) ^ C := by linarith only [hq, hcost]
  have hQC : 13 * (q + 1) + 2 ≤ (p + C) ^ C := by linarith only [hq, hcost]
  have hIC : 13 * (q + 1) + 2 + 4 * q + 5 ≤ (p + C) ^ C := by linarith only [hcost]
  obtain ⟨V, hdim, hsymm, k, i, weight, H, hweight, hsub, hH, hdense, U, _⟩ := hmulti W hf
  let M := W.multilinearFactor V k i
  have hm (h x : ZMod N) : ‖M h x.val‖ ≤ 1 := by
    dsimp only [M, NativeCorrelationStructure.multilinearFactor]
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (V.norm_eval k _)).trans
      (W.family.norm_eval i h (x.val : ℤ))
  have hf₀ (x : ZMod N) : ‖f x * star (weight x)‖ ≤ 1 := by
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hf x)).trans (hweight x)
  obtain ⟨S, hSH, hS, hshort, hSsize, Q, hQ, hQsize, hquad⟩ :=
    U.exists_short_quadruples hH hf₀ hf hm hdense
  refine ⟨V.mono hqC, hdim, hsymm, k, i, weight, S, hweight,
    fun x hx => hsub (hSH hx), hS, hshort, ?_, (U.restrict hSH).mono hqC, Q, hQ, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hHC))
      (Nat.cast_nonneg _)).trans hSsize
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hQC))
      (by positivity)).trans hQsize
  · intro t ht
    obtain ⟨h₁, h₂, h₃, h₄, hrel, hc⟩ := hquad t ht
    obtain ⟨branch, c, len, hlen, hN, hlenShort, hcor, hvol⟩ :=
      U.exists_integer_quadruple_interval_budget M (fun _ _ => rfl) hm
        t.1 t.2.1 t.2.2 (hSH h₁) (hSH h₂) (hSH h₃) (hSH h₄) hc
    refine ⟨h₁, h₂, h₃, h₄, hrel, ?_, branch, c, len, hlen, hN, hlenShort, ?_, ?_⟩
    · change Real.exp (-((p + C) ^ C)) ≤
        additiveQuadrupleCorrelation (U.restrict hSH).extension t.1 t.2.1 t.2.2
      rw [U.restrict_quadruple hSH t.1 t.2.1 t.2.2 h₁ h₂ h₃ h₄]
      exact (Real.exp_le_exp.mpr (neg_le_neg hQC)).trans hc
    · change Real.exp (-((p + C) ^ C)) ≤ ‖𝔼 n ∈ Finset.Ico (c : ℤ) (c + len),
        fourPointProduct (U.integerProduct M ⟨t.2.1, hSH h₁⟩)
          (U.integerProduct M ⟨t.2.1 - t.1, hSH h₂⟩)
          (U.integerProduct M ⟨t.2.2, hSH h₃⟩)
          (U.integerProduct M ⟨t.2.2 - t.1, hSH h₄⟩) (cyclicBranchOffset t.1 branch) n‖
      exact (Real.exp_le_exp.mpr (neg_le_neg hIC)).trans hcor
    · exact (Real.exp_le_exp.mpr (neg_le_neg hIC)).trans hvol

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_integer_multilinear_quadruples_with_equivalence (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p f), (∀ x, ‖f x‖ ≤ 1) →
      ∃ V : NativeMultidegreeNilcharacter
          (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) ((p + C) ^ C),
        V.dim ≤ 2 ^ (s + 1) * W.mixed.dim ∧
        (∀ (e : ReplicatedPermutation (mixedCorrelationDegree s)) k x,
          V.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree s) e).symm j)) =
            V.eval k x) ∧
        NativeIntegerVectorEquivalence s ((p + C) ^ C) W.mixed.eval
          (fun k x => V.eval k (fun j => x j.1)) ∧
        ∃ (k : Fin V.outputDim) (i : Fin W.family.outputDim) (weight : ZMod N → ℂ)
          (H : Finset (ZMod N)), (∀ x, ‖weight x‖ ≤ 1) ∧ H ⊆ W.shifts ∧ H.Nonempty ∧
          CyclicShortShiftSet H ∧
          Real.exp (-((p + C) ^ C)) * Fintype.card (ZMod N) ≤ (H.card : ℝ) ∧
          ∃ U : NativeCrossWitnesses (s - 1) N ((p + C) ^ C)
              (fun x => f x * star (weight x)) f
              (fun h x => W.multilinearFactor V k i h x.val) H,
            ∃ Q : Finset (ZMod N × ZMod N × ZMod N), Q.Nonempty ∧
              Real.exp (-((p + C) ^ C)) * (Fintype.card (ZMod N) : ℝ) ^ 3 ≤ (Q.card : ℝ) ∧
              ∀ t ∈ Q, ∃ (h₁ : t.2.1 ∈ H) (h₂ : t.2.1 - t.1 ∈ H)
                (h₃ : t.2.2 ∈ H) (h₄ : t.2.2 - t.1 ∈ H),
                -(t.2.1.val : ℤ) + (t.2.1 - t.1).val + t.2.2.val - (t.2.2 - t.1).val = 0 ∧
                Real.exp (-((p + C) ^ C)) ≤
                  additiveQuadrupleCorrelation U.extension t.1 t.2.1 t.2.2 ∧
                ∃ (branch : Bool) (c len : ℕ), 0 < len ∧ c + len ≤ N ∧
                  2 * ((len : ℤ) - 1) < N ∧
                  Real.exp (-((p + C) ^ C)) ≤ ‖𝔼 n ∈ Finset.Ico (c : ℤ) (c + len),
                    fourPointProduct
                      (U.integerProduct (W.multilinearFactor V k i) ⟨t.2.1, h₁⟩)
                      (U.integerProduct (W.multilinearFactor V k i) ⟨t.2.1 - t.1, h₂⟩)
                      (U.integerProduct (W.multilinearFactor V k i) ⟨t.2.2, h₃⟩)
                      (U.integerProduct (W.multilinearFactor V k i) ⟨t.2.2 - t.1, h₄⟩)
                      (cyclicBranchOffset t.1 branch) n‖ ∧
                  Real.exp (-((p + C) ^ C)) ≤ (len : ℝ) / N := by
  obtain ⟨a, _, hmulti⟩ := exists_multilinear_quadruples_with_equivalence s
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (17 * (X + Polynomial.C a) ^ a + 20)
  refine ⟨C, hC, ?_⟩
  intro r N _ p f W hf
  have hp : 0 ≤ p := (Nat.cast_nonneg W.mixed.dim).trans W.mixed.complexity.1.1
  let q := (p + a) ^ a
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hcost : 17 * q + 20 ≤ (p + C) ^ C := by
    simpa [X, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith only [hq, hcost]
  have hHC : q + 1 ≤ (p + C) ^ C := by linarith only [hq, hcost]
  have hQC : 13 * (q + 1) + 2 ≤ (p + C) ^ C := by linarith only [hq, hcost]
  have hIC : 13 * (q + 1) + 2 + 4 * q + 5 ≤ (p + C) ^ C := by linarith only [hcost]
  obtain ⟨V, hdim, hsymm, E, k, i, weight, H, hweight, hsub, hH, hdense, U, _⟩ := hmulti W hf
  let M := W.multilinearFactor V k i
  have hm (h x : ZMod N) : ‖M h x.val‖ ≤ 1 := by
    dsimp only [M, NativeCorrelationStructure.multilinearFactor]
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (V.norm_eval k _)).trans
      (W.family.norm_eval i h (x.val : ℤ))
  have hf₀ (x : ZMod N) : ‖f x * star (weight x)‖ ≤ 1 := by
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hf x)).trans (hweight x)
  obtain ⟨S, hSH, hS, hshort, hSsize, Q, hQ, hQsize, hquad⟩ :=
    U.exists_short_quadruples hH hf₀ hf hm hdense
  refine ⟨V.mono hqC, hdim, hsymm, E.mono hqC, k, i, weight, S, hweight,
    fun x hx => hsub (hSH hx), hS, hshort, ?_, (U.restrict hSH).mono hqC, Q, hQ, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hHC))
      (Nat.cast_nonneg _)).trans hSsize
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hQC))
      (by positivity)).trans hQsize
  · intro t ht
    obtain ⟨h₁, h₂, h₃, h₄, hrel, hc⟩ := hquad t ht
    obtain ⟨branch, c, len, hlen, hN, hlenShort, hcor, hvol⟩ :=
      U.exists_integer_quadruple_interval_budget M (fun _ _ => rfl) hm
        t.1 t.2.1 t.2.2 (hSH h₁) (hSH h₂) (hSH h₃) (hSH h₄) hc
    refine ⟨h₁, h₂, h₃, h₄, hrel, ?_, branch, c, len, hlen, hN, hlenShort, ?_, ?_⟩
    · change Real.exp (-((p + C) ^ C)) ≤
        additiveQuadrupleCorrelation (U.restrict hSH).extension t.1 t.2.1 t.2.2
      rw [U.restrict_quadruple hSH t.1 t.2.1 t.2.2 h₁ h₂ h₃ h₄]
      exact (Real.exp_le_exp.mpr (neg_le_neg hQC)).trans hc
    · change Real.exp (-((p + C) ^ C)) ≤ ‖𝔼 n ∈ Finset.Ico (c : ℤ) (c + len),
        fourPointProduct (U.integerProduct M ⟨t.2.1, hSH h₁⟩)
          (U.integerProduct M ⟨t.2.1 - t.1, hSH h₂⟩)
          (U.integerProduct M ⟨t.2.2, hSH h₃⟩)
          (U.integerProduct M ⟨t.2.2 - t.1, hSH h₄⟩) (cyclicBranchOffset t.1 branch) n‖
      exact (Real.exp_le_exp.mpr (neg_le_neg hIC)).trans hcor
    · exact (Real.exp_le_exp.mpr (neg_le_neg hIC)).trans hvol

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.IntervalSplitPolynomialBudget
namespace OAI

section

namespace Erdos3

theorem exists_interval_split_budget (c : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ K : ℝ, 0 ≤ K →
      2 * K + intervalSplitTermBudget c K ≤ (K + C) ^ C ∧
      intervalSplitLocalBudget c K ≤ (K + C) ^ C := by
  obtain ⟨a, _, ha⟩ := exists_interval_error_budget
  obtain ⟨b, _, hb⟩ := exists_mixed_error_budget
  let X : Polynomial ℕ := Polynomial.X
  let Y := (X + Polynomial.C a) ^ a
  let V := (2 * X + 2 * Y + 2 + Polynomial.C c) ^ c
  let Z := (Y + V + 2 + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (2 * X + V + Z)
  refine ⟨C, hC, fun K hK => ?_⟩
  have hL : 0 ≤ intervalErrorBudget K := intervalErrorBudget_nonneg hK
  have hI : 0 ≤ intervalSplitInput K := le_trans (by norm_num) (intervalSplitInput_bounds hK).1
  have hF : 0 ≤ intervalSplitTermBudget c K := by unfold intervalSplitTermBudget; positivity
  have hi : intervalSplitInput K ≤ 2 * K + 2 * (K + a) ^ a + 2 := by
    unfold intervalSplitInput
    gcongr
    exact ha K hK
  have hv : intervalSplitTermBudget c K ≤ (2 * K + 2 * (K + a) ^ a + 2 + c) ^ c := by
    unfold intervalSplitTermBudget
    gcongr
  have hm : 0 ≤ intervalErrorBudget K + intervalSplitTermBudget c K + 2 := by positivity
  have hz : intervalSplitLocalBudget c K ≤
      ((K + a) ^ a + (2 * K + 2 * (K + a) ^ a + 2 + c) ^ c + 2 + b) ^ b := by
    apply (hb _ hm).1.trans
    gcongr
    exact ha K hK
  have hZ : 0 ≤ ((K + a) ^ a + (2 * K + 2 * (K + a) ^ a + 2 + c) ^ c + 2 + b) ^ b := by
    positivity
  have hbound : 2 * K + (2 * K + 2 * (K + a) ^ a + 2 + c) ^ c +
      ((K + a) ^ a + (2 * K + 2 * (K + a) ^ a + 2 + c) ^ c + 2 + b) ^ b ≤ (K + C) ^ C := by
    simpa [X, Y, V, Z, Polynomial.eval₂_pow] using hbudget K hK
  constructor
  · linarith only [hv, hZ, hbound]
  · have hv0 : 0 ≤ (2 * K + 2 * (K + a) ^ a + 2 + c) ^ c := by positivity
    linarith only [hz, hK, hv0, hbound]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeIntervalWeightPairs
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem native_interval_weight_pairs {I : Type} [Fintype I] [Nonempty I]
    {s r d N : ℕ} [NeZero N] {p b : ℝ}
    (W : NativeDegreeRankFamily s r (ZMod N) b) (out : Fin W.outputDim)
    (a k : ZMod N) (δ : ℤ) (h : I → ZMod N) (c len : I → ℕ)
    (weight : ℤ → ℂ) (v : I → ℤ → ℂ)
    (E : ∀ i, NativeIntegerExpansion (fun _ : Unit => 1) d p (fun x => v i (x ())))
    (hp : 2 ≤ p) (hw : ∀ n, ‖weight n‖ ≤ 1)
    (hN : ∀ i, c i + len i ≤ N) (hshort : ∀ i, 2 * ((len i : ℤ) - 1) < N)
    (hsize : ∀ i, Real.exp (-p) ≤ (len i : ℝ) / N)
    (hcorr : ∀ i, Real.exp (-p) ≤ ‖𝔼 n ∈ Finset.Ico (c i : ℤ) (c i + len i),
      fourPointProduct (W.eval out (h i)) (W.eval out (h i - a))
        (W.eval out k) (W.eval out (k - a)) δ n * weight n * v i n‖) :
    ∃ Q : Finset (I × I), Q.Nonempty ∧
      Real.exp (-(8 * p + 1)) * (Fintype.card I : ℝ) ^ 2 ≤ (Q.card : ℝ) ∧
      ∀ t ∈ Q, ∃ c' len' : ℕ, 0 < len' ∧ c' + len' ≤ N ∧
        2 * ((len' : ℤ) - 1) < N ∧ Real.exp (-(8 * p + 1)) ≤ (len' : ℝ) / N ∧
        Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) d (mixedErrorPairBudget p)
          (fun x => v t.1 (x ()) * star (v t.2 (x ())))) ∧
        Real.exp (-(8 * p + 1)) ≤ ‖𝔼 n ∈ Finset.Ico (c' : ℤ) (c' + len'),
          fourPointProduct (W.eval out (h t.1)) (W.eval out (h t.1 - a))
            (W.eval out (h t.2)) (W.eval out (h t.2 - a)) δ n * (v t.1 n * star (v t.2 n))‖ := by
  let A := Finset.Ico (0 : ℤ) N
  let S (i : I) := Finset.Ico (c i : ℤ) (c i + len i)
  let B (n : ℤ) := weight n * star (W.shiftPair out a k δ n)
  have hA : A.Nonempty := by
    exact ⟨0, Finset.mem_Ico.mpr ⟨le_rfl, by exact_mod_cast NeZero.pos N⟩⟩
  have hAcard : A.card = N := by simpa only [A, Nat.cast_zero, zero_add] using integerIco_card 0 N
  have hB (n : ℤ) (_ : n ∈ A) : ‖B n‖ ≤ 1 := by
    dsimp only [B]
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hw n)).trans (W.shiftPair_norm out a k δ n)
  have hcor (i : I) : Real.exp (-p) ≤ ‖𝔼 n ∈ S i, B n * (W.shiftPair out a (h i) δ n * v i n)‖ := by
    simpa only [S, B, W.quadruple_common_anchor] using hcorr i
  have hvol (i : I) : Real.exp (-p) ≤ (S i).card / (A.card : ℝ) := by
    simpa only [S, integerIco_card, hAcard] using hsize i
  obtain ⟨Q, hQ, hQsize, hpairs⟩ := native_weight_pair_removal hp A hA S
    (fun i => integerIco_subset_range (c i) (len i) N (hN i)) B
    (fun i => W.shiftPair out a (h i) δ) v E hB
    (fun i n _ => W.shiftPair_norm out a (h i) δ n) hvol hcor
  refine ⟨Q, hQ, hQsize, ?_⟩
  intro t ht
  obtain ⟨hJ, hJvol, hE, hJcor⟩ := hpairs t ht
  obtain ⟨c', len', hlen', hN', hle, _, heq⟩ := integerIco_intersection
    (c t.1) (len t.1) (c t.2) (len t.2) N (hN t.1) (hN t.2) hJ
  refine ⟨c', len', hlen', hN', ?_, ?_, hE, ?_⟩
  · have hs := hshort t.1
    omega
  · simpa only [S, heq, integerIco_card, hAcard] using hJvol
  · simpa only [S, heq, W.shiftPair_mul_star] using hJcor

end Erdos3

end

end OAI

end


