-- Prove2me | Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SumComplexEmbeddingsEqSumInfinitePlace
-- name    : Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SumComplexEmbeddingsEqSumInfinitePlace
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:25:15.724069+00:00
-- url     : https://prove2.me/theorems/13d89726-6219-4b97-9c57-8510bb57c95b
-- title:
--   Sum Complex Embeddings Eq Sum Infinite Place
-- statement:
--   Definitions and structural lemmas for Sum Complex Embeddings Eq Sum Infinite Place, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SumComplexEmbeddingsEqSumInfinitePlace.lean

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
namespace Formalism.HermitianLatticeCounting.P
open NumberField
open NumberField
section Cov
variable {E : Type} [Field E] [NumberField E]
abbrev s5bV (E : Type) [Field E] [NumberField E] := EuclideanSpace ℂ (InfinitePlace E)
noncomputable def complexEmbeddingVector (a : E) : s5bV E := WithLp.toLp 2 (fun w => w.embedding a)
noncomputable def complexSpaceMixedLinearEquiv (hc : ∀ w : InfinitePlace E, w.IsComplex) :
    s5bV E ≃ₗ[ℝ] mixedEmbedding.mixedSpace E :=
  haveI : IsEmpty {w : InfinitePlace E // w.IsReal} :=
    ⟨fun w => (InfinitePlace.not_isReal_iff_isComplex.mpr (hc w.1)) w.2⟩
  { toFun := fun x => (0, fun w => x w.1)
    map_add' := by intro x y; exact Prod.ext (by simp) (by funext w; rfl)
    map_smul' := by intro c x; exact Prod.ext (by simp) (by funext w; rfl)
    invFun := fun p => WithLp.toLp 2 (fun w => p.2 ⟨w, hc w⟩)
    left_inv := fun x => by ext w; rfl
    right_inv := fun p => Prod.ext (Subsingleton.elim _ _) (by funext w; rfl) }
open scoped Classical in
noncomputable def complexSpaceMixedEquivCLM (hc : ∀ w : InfinitePlace E, w.IsComplex) :
    s5bV E ≃L[ℝ] mixedEmbedding.mixedSpace E := (complexSpaceMixedLinearEquiv hc).toContinuousLinearEquiv
open scoped Classical in
noncomputable def integerEmbeddingLattice (hc : ∀ w : InfinitePlace E, w.IsComplex) : Submodule ℤ (s5bV E) :=
  ZLattice.comap ℝ (mixedEmbedding.integerLattice E) (complexSpaceMixedEquivCLM hc).toLinearMap
instance (hc : ∀ w : InfinitePlace E, w.IsComplex) : DiscreteTopology (integerEmbeddingLattice hc) := by
  rw [integerEmbeddingLattice]; infer_instance
open scoped Classical in
instance (hc : ∀ w : InfinitePlace E, w.IsComplex) : IsZLattice ℝ (integerEmbeddingLattice hc) := by
  simp_rw [integerEmbeddingLattice]; infer_instance
end Cov
open NumberField
section Cov2
variable {E : Type} [Field E] [NumberField E]
end Cov2
end Formalism.HermitianLatticeCounting.P


