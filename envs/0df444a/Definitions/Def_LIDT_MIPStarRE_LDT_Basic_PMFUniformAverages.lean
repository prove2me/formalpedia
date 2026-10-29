-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFUniformAverages
-- name    : LIDT_MIPStarRE_LDT_Basic_PMFUniformAverages
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T10:51:09.617573+00:00
-- url     : https://prove2.me/theorems/9bccbd10-0469-4170-90b7-8fbfd7f5ae8a
-- title:
--   LIDT definitions: LDT / Basic / PMFUniformAverages
-- statement:
--   This bundle gives PMF-level versions of the finite uniform-average identities. It connects the weighted finite-distribution API to Mathlib's uniform PMFs and supports product reindexing, coordinate swaps, and marginalization.
--
--   Principal definitions:
--   - `realWeightedSum_uniformOfFintype_comm`: Exchanges two nested uniform real weighted sums.
--   - `realWeightedSum_uniformOfFintype_equiv_prod`: Transports a uniform sum through an equivalence and decomposes it over a product.
--   - `realWeightedSum_uniformOfFintype_equiv_prod_swap`: Gives the same product decomposition with the second coordinate averaged first.
--   - `realWeightedSum_uniformOfFintype_equiv_fst`: Marginalizes a function depending only on the first coordinate.
--   - `realWeightedSum_uniformOfFintype_equiv_snd`: Marginalizes a function depending only on the second coordinate.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Basic/PMFUniformAverages.lean#L40-L140

-- Generated from MIPStarRE/LDT/Basic/PMFUniformAverages.lean by skeleton subtraction.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace LIDT

/-!
# Uniform PMF finite-expectation identities

This module contains high-level uniform-expectation identities for Mathlib
probability mass functions.  The statements are phrased in terms of
`PMF.realWeightedSum`, rather than finite sums, so that product,
marginalization, equivalence-transport, and finite push-forward arguments can
be carried out directly in the probability-mass-function language.

## Main declarations

* `PMF.realWeightedSum_uniformOfFintype_comm`
* `PMF.realWeightedSum_uniformOfFintype_prod_swap`
* `PMF.realWeightedSum_uniformOfFintype_equiv_prod`
* `PMF.realWeightedSum_uniformOfFintype_equiv_prod_swap`
* `PMF.realWeightedSum_uniformOfFintype_equiv_fst`
* `PMF.realWeightedSum_uniformOfFintype_equiv_snd`
* `PMF.realWeightedSum_uniformOfFintype_fst`
* `PMF.realWeightedSum_uniformOfFintype_snd`
* `PMF.realWeightedSum_map_uniformOfFintype_factor_equiv`
* `PMF.realWeightedSum_map_uniformOfFintype_factor_equiv_fst`
* `PMF.realWeightedSum_map_uniformOfFintype_factor_equiv_snd`

## References

These are formalization-internal finite probability lemmas for the low
individual degree test development.
-/

@[expose] public section

open scoped BigOperators

namespace PMF

/-- Swap two nested finite expectations against uniform probability mass
functions. -/
theorem realWeightedSum_uniformOfFintype_comm {α β M : Type*}
    [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    [AddCommMonoid M] [Module MIPStarRE.LDT.Error M]
    (f : α → β → M) :
    realWeightedSum (PMF.uniformOfFintype α)
        (fun a => realWeightedSum (PMF.uniformOfFintype β) (fun b => f a b)) =
      realWeightedSum (PMF.uniformOfFintype β)
        (fun b => realWeightedSum (PMF.uniformOfFintype α) (fun a => f a b)) := by
  calc
    realWeightedSum (PMF.uniformOfFintype α)
        (fun a => realWeightedSum (PMF.uniformOfFintype β) (fun b => f a b))
        = realWeightedSum (PMF.uniformOfFintype (α × β))
            (fun ab => f ab.1 ab.2) := by
          exact (realWeightedSum_uniformOfFintype_prod (f := f)).symm
    _ = realWeightedSum (PMF.uniformOfFintype (β × α))
          (fun ba => f ba.2 ba.1) := by
          exact realWeightedSum_uniformOfFintype_equiv
            (e := Equiv.prodComm α β) (f := fun ab : α × β => f ab.1 ab.2)
    _ = realWeightedSum (PMF.uniformOfFintype β)
          (fun b => realWeightedSum (PMF.uniformOfFintype α) (fun a => f a b)) := by
          exact realWeightedSum_uniformOfFintype_prod
            (α := β) (β := α) (f := fun b a => f a b)



/-- Transport a finite expectation against a uniform PMF through an equivalence
whose target is a product, then split the product expectation. -/
theorem realWeightedSum_uniformOfFintype_equiv_prod {γ α β M : Type*}
    [Fintype γ] [Nonempty γ]
    [Fintype α] [Nonempty α]
    [Fintype β] [Nonempty β]
    [AddCommMonoid M] [Module MIPStarRE.LDT.Error M]
    (e : γ ≃ α × β) (f : γ → M) :
    realWeightedSum (PMF.uniformOfFintype γ) f =
      realWeightedSum (PMF.uniformOfFintype α)
        (fun a => realWeightedSum (PMF.uniformOfFintype β)
          (fun b => f (e.symm (a, b)))) := by
  calc
    realWeightedSum (PMF.uniformOfFintype γ) f =
        realWeightedSum (PMF.uniformOfFintype (α × β))
          (fun ab => f (e.symm ab)) := by
          exact realWeightedSum_uniformOfFintype_equiv (e := e) (f := f)
    _ = realWeightedSum (PMF.uniformOfFintype α)
          (fun a => realWeightedSum (PMF.uniformOfFintype β)
            (fun b => f (e.symm (a, b)))) := by
          exact realWeightedSum_uniformOfFintype_prod
            (f := fun a b => f (e.symm (a, b)))

/-- Transport a finite expectation against a uniform PMF through an equivalence
whose target is a product, then split the product expectation with the second
coordinate averaged first. -/
theorem realWeightedSum_uniformOfFintype_equiv_prod_swap {γ α β M : Type*}
    [Fintype γ] [Nonempty γ]
    [Fintype α] [Nonempty α]
    [Fintype β] [Nonempty β]
    [AddCommMonoid M] [Module MIPStarRE.LDT.Error M]
    (e : γ ≃ α × β) (f : γ → M) :
    realWeightedSum (PMF.uniformOfFintype γ) f =
      realWeightedSum (PMF.uniformOfFintype β)
        (fun b => realWeightedSum (PMF.uniformOfFintype α)
          (fun a => f (e.symm (a, b)))) := by
  rw [realWeightedSum_uniformOfFintype_equiv_prod (e := e) (f := f)]
  exact realWeightedSum_uniformOfFintype_comm (fun a b => f (e.symm (a, b)))

/-- A finite expectation against a uniform PMF marginalizes a function depending
only on the first coordinate of a product equivalence. -/
theorem realWeightedSum_uniformOfFintype_equiv_fst {γ α β M : Type*}
    [Fintype γ] [Nonempty γ]
    [Fintype α] [Nonempty α]
    [Finite β] [Nonempty β]
    [AddCommMonoid M] [Module MIPStarRE.LDT.Error M]
    (e : γ ≃ α × β) (f : α → M) :
    realWeightedSum (PMF.uniformOfFintype γ) (fun x => f (e x).1) =
      realWeightedSum (PMF.uniformOfFintype α) f := by
  simpa [realWeightedSum] using
    uniformOfFintype_sum_equiv_fst_smul (e := e) (f := f)

/-- A finite expectation against a uniform PMF marginalizes a function depending
only on the second coordinate of a product equivalence. -/
theorem realWeightedSum_uniformOfFintype_equiv_snd {γ α β M : Type*}
    [Fintype γ] [Nonempty γ]
    [Finite α] [Nonempty α]
    [Fintype β] [Nonempty β]
    [AddCommMonoid M] [Module MIPStarRE.LDT.Error M]
    (e : γ ≃ α × β) (f : β → M) :
    realWeightedSum (PMF.uniformOfFintype γ) (fun x => f (e x).2) =
      realWeightedSum (PMF.uniformOfFintype β) f := by
  simpa [realWeightedSum] using
    uniformOfFintype_sum_equiv_snd_smul (e := e) (f := f)











end PMF

end

end LIDT


