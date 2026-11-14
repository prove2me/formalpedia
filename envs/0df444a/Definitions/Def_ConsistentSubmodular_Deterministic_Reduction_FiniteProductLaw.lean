-- Prove2me | Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_FiniteProductLaw
-- name    : ConsistentSubmodular_Deterministic_Reduction_FiniteProductLaw
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:09:04.705021+00:00
-- url     : https://prove2.me/theorems/d42a595e-5ab8-4de8-bc09-b692eb53c6ce
-- title:
--   Finite product laws and selected sets
-- statement:
--   Let $\kappa$ be a finite index type and, for each $i\in\kappa$, let $\mu_i$ be a finite law on a finite type $A_i$ (weights $\mu_i(a)\ge0$ summing to $1$).
--
--   - `ConsistentSubmodular.FiniteLaw.product` $(\mu)$: the product law on $\prod_{i\in\kappa}A_i$ with weights
--   $$\Big(\bigotimes_i\mu_i\Big)(\omega)=\prod_{i\in\kappa}\mu_i(\omega_i),$$
--   which are nonnegative and sum to $1$ (the sum factorizes as a product of sums, each equal to $1$), so the product is again a finite law, under which the coordinates are independent.
--   - `ConsistentSubmodular.FiniteLaw.selectedSet` $(\mathrm{sel},\omega)$: given predicates $\mathrm{sel}_i : A_i\to\mathrm{Prop}$ and an outcome $\omega$, the set of selected indices
--   $$\{\,i\in\kappa : \mathrm{sel}_i(\omega_i)\,\}.$$
--
--   Together they describe random subsets of a finite index set in which each index is selected through its own independent experiment. They are used to realize product-form samples (independent inclusion of elements) as explicit finite experiments in the sampling and rounding arguments of Appendix B.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/FiniteProductLaw.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_FiniteProbability
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_SamplingOperators

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.FiniteLaw

variable {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω)

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

variable {A : κ → Type*} [∀ i, Fintype (A i)]

def product (laws : ∀ i, FiniteLaw (A i)) : FiniteLaw (∀ i, A i) where
  weight ω := ∏ i, (laws i).weight (ω i)
  nonnegative ω := Finset.prod_nonneg (fun i _ => (laws i).nonnegative (ω i))
  sum_one := by
    rw [← Fintype.prod_sum]
    simp only [(laws _).sum_one, Finset.prod_const_one]

def selectedSet (select : ∀ i, A i → Prop) (ω : ∀ i, A i) : Finset κ := by
  classical
  exact Finset.univ.filter (fun i => select i (ω i))

end ConsistentSubmodular.FiniteLaw

end


