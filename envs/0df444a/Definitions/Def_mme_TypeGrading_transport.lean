-- Prove2me | Definitions.Def_mme_TypeGrading_transport
-- name    : mme_TypeGrading_transport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-25T02:56:41.271818+00:00
-- url     : https://prove2.me/theorems/fa8e54ee-808a-491f-9c16-4d77568889e6
-- title:
--   Transport a tensor type grading across modewise linear equivalences
-- statement:
--   Let $T$ and $U$ be order-$d$ tensor objects whose corresponding mode spaces are linearly equivalent. Any $t$-class type grading of $T$ transports to a $t$-class type grading of $U$ by mapping every grading subspace through the corresponding equivalence. The transported classes remain independent and span each whole mode space.
--
--   This is a structural utility for laser-method formalizations. It carries a grading through modewise changes of coordinates and tensor-product reassociations without rebuilding the internal-direct-sum proof each time. Relabeling the modes themselves is a distinct construction.
-- source:
--   Standard finite-dimensional linear algebra: internal direct sums are invariant under linear equivalence.

import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Definitions.Def_mme_tensor_type_grading

universe u

namespace MME
namespace TensorObj.TypeGrading

variable {K : Type u} [Field K] {d t : ℕ}

noncomputable def transport
    {T U : TensorObj K d} (G : T.TypeGrading t)
    (e : ∀ i : Fin d, T.V i ≃ₗ[K] U.V i) : U.TypeGrading t where
  decomp i a := (G.decomp i a).map (e i).toLinearMap
  is_internal i := by
    rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
    constructor
    · exact LinearMap.iSupIndep_map (e i).toLinearMap (e i).injective
        (G.is_internal i).submodule_iSupIndep
    · rw [← Submodule.map_iSup,
          (G.is_internal i).submodule_iSup_eq_top,
          Submodule.map_top,
          LinearMap.range_eq_top]
      exact (e i).surjective

end TensorObj.TypeGrading
end MME


