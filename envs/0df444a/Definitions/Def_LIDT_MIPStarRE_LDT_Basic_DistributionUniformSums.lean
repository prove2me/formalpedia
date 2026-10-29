-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
-- name    : LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T10:53:00.667335+00:00
-- url     : https://prove2.me/theorems/6a59d006-1420-42f6-a5e3-fb9fb35e14e8
-- title:
--   LIDT definitions: LDT / Basic / DistributionUniformSums
-- statement:
--   This bundle establishes reindexing, product decomposition, and commutation rules for uniform finite averages of module-valued functions. These identities let later LDT arguments move between probability-mass weights, equivalent finite sample spaces, and iterated averages without introducing measurable-space assumptions.
--
--   Principal definitions:
--   - `sum_smul_eq_toPMF_support_sum`: rewrites a weighted finite sum using the probability mass function on its stored support.
--   - `sum_smul_eq_toPMF_sum`: rewrites the same weighted sum as a full finite sum.
--   - `uniformDistribution_sum_smul_eq_pmf_sum`: expresses a uniform average through uniform PMF weights.
--   - `uniformOnFinset_sum_smul_eq_pmf_sum`: expresses a finite-support uniform average through its PMF.
--   - `uniformDistribution_sum_smul_equiv`: transports a uniform average along an equivalence.
--   - `uniformDistribution_sum_smul_prod`: splits a product average into iterated averages.
--   - `uniformDistribution_sum_smul_comm`: commutes two nested uniform averages.
--   - `uniformDistribution_sum_smul_equiv_prod_swap`: transports and splits an average in the swapped product order.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Basic/DistributionUniformSums.lean#L45-L467

-- Generated from MIPStarRE/LDT/Basic/DistributionUniformSums.lean by skeleton subtraction.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFUniformAverages
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
# Module-valued uniform finite sums for project distributions

This module contains the module-valued finite-sum algebra for the project
`Distribution` type.  The statements keep the paper-facing
`uniformDistribution` notation, but their proofs reduce the probability
calculation to the finite-expectation API for Mathlib probability mass
functions.

## Main declarations

* `Distribution.sum_smul_eq_toPMF_support_sum`
* `Distribution.sum_smul_eq_toPMF_sum`
* `uniformDistribution_sum_smul_eq_pmf_sum`
* `uniformDistribution_sum_smul_equiv`
* `uniformDistribution_sum_smul_prod`
* `uniformDistribution_sum_smul_comm`
* `uniformDistribution_sum_smul_prod_swap`
* `uniformDistribution_sum_smul_equiv_prod`
* `uniformDistribution_sum_smul_equiv_fst`
* `uniformDistribution_sum_smul_equiv_snd`
* `uniformDistribution_map_sum_smul_eq_uniform_of_factor_equiv`
* `uniformOnFinset_sum_smul_eq_subtype`
* `uniformOnFinset_filter_sum_smul_equiv`

## References

These are formalization-internal finite probability lemmas for the low
individual degree test development.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.LDT

namespace Distribution

/-- A module-valued finite weighted sum against a probabilistic project
distribution may be written with the real weights of the associated Mathlib
probability mass function, over the stored support. -/
theorem sum_smul_eq_toPMF_support_sum {α M : Type*}
    [AddCommMonoid M] [Module Error M]
    (𝒟 : Distribution α) (h𝒟 : 𝒟.IsProbability) (f : α → M) :
    ∑ a ∈ 𝒟.support, 𝒟.weight a • f a =
      ∑ a ∈ 𝒟.support, (𝒟.toPMF h𝒟 a).toReal • f a := by
  exact Finset.sum_congr rfl fun a _ => by
    rw [Distribution.toPMF_apply_toReal]

/-- A module-valued finite weighted sum against a probabilistic project
distribution may be written as a full finite sum with the real weights of the
associated Mathlib probability mass function. -/
theorem sum_smul_eq_toPMF_sum {α M : Type*} [Fintype α]
    [AddCommMonoid M] [Module Error M]
    (𝒟 : Distribution α) (h𝒟 : 𝒟.IsProbability) (f : α → M) :
    ∑ a ∈ 𝒟.support, 𝒟.weight a • f a =
      ∑ a : α, (𝒟.toPMF h𝒟 a).toReal • f a := by
  rw [Distribution.sum_smul_eq_toPMF_support_sum 𝒟 h𝒟 f]
  exact (Distribution.sum_univ_eq_sum_support 𝒟
    (fun a => (𝒟.toPMF h𝒟 a).toReal • f a)
    (by
      intro a ha
      rw [Distribution.toPMF_apply_of_notMem 𝒟 h𝒟 ha]
      simp)).symm

end Distribution

/-- Module-valued finite-sum expression for the uniform distribution, stated
without measurable-space assumptions. -/
theorem uniformDistribution_sum_smul_eq_pmf_sum {α M : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [AddCommMonoid M] [Module Error M] (f : α → M) :
    ∑ a ∈ (uniformDistribution α).support, (uniformDistribution α).weight a • f a =
      ∑ a : α, (PMF.uniformOfFintype α a).toReal • f a := by
  rw [Distribution.sum_smul_eq_toPMF_sum
    (uniformDistribution α) (uniformDistribution_isProbability α)]
  rw [uniformDistribution_toPMF]

/-- A finite-support uniform weighted sum is the corresponding Mathlib uniform
PMF-weighted sum. -/
theorem uniformOnFinset_sum_smul_eq_pmf_sum {α M : Type*}
    [AddCommMonoid M] [Module Error M]
    (s : Finset α) (hs : s.Nonempty) (f : α → M) :
    ∑ a ∈ (Distribution.uniformOnFinset s).support,
        (Distribution.uniformOnFinset s).weight a • f a =
      ∑ a ∈ s, (PMF.uniformOfFinset s hs a).toReal • f a := by
  rw [Distribution.sum_smul_eq_toPMF_support_sum
    (Distribution.uniformOnFinset s)
    (Distribution.uniformOnFinset_isProbability s hs)]
  rw [Distribution.uniformOnFinset_support, Distribution.uniformOnFinset_toPMF]



/-- Reindex a uniform module-valued average along an equivalence. -/
theorem uniformDistribution_sum_smul_equiv {α β M : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    [AddCommMonoid M] [Module Error M]
    (e : α ≃ β) (f : α → M) :
    ∑ a ∈ (uniformDistribution α).support, (uniformDistribution α).weight a • f a =
      ∑ b ∈ (uniformDistribution β).support,
        (uniformDistribution β).weight b • f (e.symm b) := by
  rw [uniformDistribution_sum_smul_eq_pmf_sum (α := α)]
  rw [uniformDistribution_sum_smul_eq_pmf_sum (α := β)]
  simpa [PMF.realWeightedSum] using
    PMF.realWeightedSum_uniformOfFintype_equiv (e := e) (f := f)

/-- Split a uniform module-valued average over a product into iterated uniform
module-valued averages. -/
theorem uniformDistribution_sum_smul_prod {α β M : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    [AddCommMonoid M] [Module Error M]
    (f : α → β → M) :
    ∑ ab ∈ (uniformDistribution (α × β)).support,
        (uniformDistribution (α × β)).weight ab • f ab.1 ab.2 =
      ∑ a ∈ (uniformDistribution α).support, (uniformDistribution α).weight a •
        ∑ b ∈ (uniformDistribution β).support,
          (uniformDistribution β).weight b • f a b := by
  rw [uniformDistribution_sum_smul_eq_pmf_sum (α := α × β)]
  rw [uniformDistribution_sum_smul_eq_pmf_sum (α := α)]
  simp_rw [uniformDistribution_sum_smul_eq_pmf_sum (α := β)]
  simpa [PMF.realWeightedSum] using
    PMF.realWeightedSum_uniformOfFintype_prod (f := f)

/-- Swap two nested uniform module-valued averages over finite nonempty types. -/
theorem uniformDistribution_sum_smul_comm {α β M : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    [AddCommMonoid M] [Module Error M]
    (f : α → β → M) :
    ∑ a ∈ (uniformDistribution α).support, (uniformDistribution α).weight a •
        ∑ b ∈ (uniformDistribution β).support, (uniformDistribution β).weight b • f a b =
      ∑ b ∈ (uniformDistribution β).support, (uniformDistribution β).weight b •
        ∑ a ∈ (uniformDistribution α).support,
          (uniformDistribution α).weight a • f a b := by
  rw [uniformDistribution_sum_smul_eq_pmf_sum (α := α)]
  simp_rw [uniformDistribution_sum_smul_eq_pmf_sum (α := β)]
  simp_rw [uniformDistribution_sum_smul_eq_pmf_sum (α := α)]
  simpa [PMF.realWeightedSum] using
    PMF.realWeightedSum_uniformOfFintype_comm (f := f)





/-- Transport a uniform module-valued average through an equivalence whose
target is a product, then split the product average in the other order. -/
theorem uniformDistribution_sum_smul_equiv_prod_swap {γ α β M : Type*}
    [Fintype γ] [DecidableEq γ] [Nonempty γ]
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    [AddCommMonoid M] [Module Error M]
    (e : γ ≃ α × β) (f : γ → M) :
    ∑ x ∈ (uniformDistribution γ).support, (uniformDistribution γ).weight x • f x =
      ∑ b ∈ (uniformDistribution β).support, (uniformDistribution β).weight b •
        ∑ a ∈ (uniformDistribution α).support,
          (uniformDistribution α).weight a • f (e.symm (a, b)) := by
  rw [uniformDistribution_sum_smul_eq_pmf_sum (α := γ)]
  rw [uniformDistribution_sum_smul_eq_pmf_sum (α := β)]
  simp_rw [uniformDistribution_sum_smul_eq_pmf_sum (α := α)]
  simpa [PMF.realWeightedSum] using
    PMF.realWeightedSum_uniformOfFintype_equiv_prod_swap (e := e) (f := f)

/-- A function depending only on the first coordinate of a product equivalence
has the first-coordinate uniform module-valued marginal. -/
theorem uniformDistribution_sum_smul_equiv_fst {γ α β M : Type*}
    [Fintype γ] [DecidableEq γ] [Nonempty γ]
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Finite β] [Nonempty β]
    [AddCommMonoid M] [Module Error M]
    (e : γ ≃ α × β) (f : α → M) :
    ∑ x ∈ (uniformDistribution γ).support,
        (uniformDistribution γ).weight x • f (e x).1 =
      ∑ a ∈ (uniformDistribution α).support, (uniformDistribution α).weight a • f a := by
  classical
  have := Fintype.ofFinite β
  rw [uniformDistribution_sum_smul_eq_pmf_sum (α := γ)]
  rw [uniformDistribution_sum_smul_eq_pmf_sum (α := α)]
  simpa [PMF.realWeightedSum] using
    PMF.realWeightedSum_uniformOfFintype_equiv_fst (e := e) (f := f)

/-- A function depending only on the second coordinate of a product equivalence
has the second-coordinate uniform module-valued marginal. -/
theorem uniformDistribution_sum_smul_equiv_snd {γ α β M : Type*}
    [Fintype γ] [DecidableEq γ] [Nonempty γ]
    [Finite α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    [AddCommMonoid M] [Module Error M]
    (e : γ ≃ α × β) (f : β → M) :
    ∑ x ∈ (uniformDistribution γ).support,
        (uniformDistribution γ).weight x • f (e x).2 =
      ∑ b ∈ (uniformDistribution β).support, (uniformDistribution β).weight b • f b := by
  classical
  have := Fintype.ofFinite α
  rw [uniformDistribution_sum_smul_eq_pmf_sum (α := γ)]
  rw [uniformDistribution_sum_smul_eq_pmf_sum (α := β)]
  simpa [PMF.realWeightedSum] using
    PMF.realWeightedSum_uniformOfFintype_equiv_snd (e := e) (f := f)













/-- A finite-support uniform module-valued average is the corresponding uniform
average over the support subtype. -/
theorem uniformOnFinset_sum_smul_eq_subtype {α M : Type*} [DecidableEq α]
    [AddCommMonoid M] [Module Error M]
    (s : Finset α) [Nonempty {a : α // a ∈ s}] (f : α → M) :
    ∑ a ∈ (Distribution.uniformOnFinset s).support,
        (Distribution.uniformOnFinset s).weight a • f a =
      ∑ a ∈ (uniformDistribution {a : α // a ∈ s}).support,
        (uniformDistribution {a : α // a ∈ s}).weight a • f a.1 := by
  classical
  have hs : s.Nonempty := by
    rcases (inferInstance : Nonempty {a : α // a ∈ s}) with ⟨a⟩
    exact ⟨a.1, a.2⟩
  have hcard : (s.card : Error) = (Fintype.card {a : α // a ∈ s} : Error) := by
    rw [Fintype.card_coe s]
  rw [uniformOnFinset_sum_smul_eq_pmf_sum s hs, uniformDistribution_sum_smul_eq_pmf_sum]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  rw [← hcard]
  calc
    ∑ x ∈ s, (PMF.uniformOfFinset s hs x).toReal • f x
        = ∑ x ∈ s, (s.card : Error)⁻¹ • f x := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          simp [PMF.uniformOfFinset_apply, hx, ENNReal.toReal_inv,
            ENNReal.toReal_natCast]
    _ = ∑ x ∈ s.attach, (s.card : Error)⁻¹ • f x.1 := by
          exact (Finset.sum_attach s (fun x : α => (s.card : Error)⁻¹ • f x)).symm
    _ = ∑ x : {x : α // x ∈ s}, (s.card : Error)⁻¹ • f x.1 := by
          rw [Finset.attach_eq_univ]



/-- A uniform module-valued average over a filtered finite support is the uniform
average over the finite subtype satisfying the predicate. -/
theorem uniformOnFinset_filter_sum_smul_eq_subtype {α M : Type*}
    [Fintype α] [DecidableEq α]
    (p : α → Prop) [DecidablePred p] [Nonempty {a : α // p a}]
    [AddCommMonoid M] [Module Error M] (f : α → M) :
    ∑ a ∈ (Distribution.uniformOnFinset (Finset.univ.filter p)).support,
        (Distribution.uniformOnFinset (Finset.univ.filter p)).weight a • f a =
      ∑ a ∈ (uniformDistribution {a : α // p a}).support,
        (uniformDistribution {a : α // p a}).weight a • f a.1 := by
  classical
  let support : Finset α := Finset.univ.filter p
  let e : {a : α // a ∈ support} ≃ {a : α // p a} :=
    { toFun := fun a => ⟨a.1, (Finset.mem_filter.mp a.2).2⟩
      invFun := fun a =>
        ⟨a.1, Finset.mem_filter.mpr ⟨Finset.mem_univ a.1, a.2⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have : Nonempty {a : α // a ∈ support} := by
    rcases (inferInstance : Nonempty {a : α // p a}) with ⟨a⟩
    exact ⟨⟨a.1, Finset.mem_filter.mpr ⟨Finset.mem_univ a.1, a.2⟩⟩⟩
  calc
    ∑ a ∈ (Distribution.uniformOnFinset (Finset.univ.filter p)).support,
        (Distribution.uniformOnFinset (Finset.univ.filter p)).weight a • f a =
        ∑ a ∈ (Distribution.uniformOnFinset support).support,
          (Distribution.uniformOnFinset support).weight a • f a := by
          rfl
    _ = ∑ a ∈ (uniformDistribution {a : α // a ∈ support}).support,
          (uniformDistribution {a : α // a ∈ support}).weight a • f a.1 := by
          exact uniformOnFinset_sum_smul_eq_subtype support f
    _ = ∑ a ∈ (uniformDistribution {a : α // p a}).support,
          (uniformDistribution {a : α // p a}).weight a • f a.1 := by
          simpa [e] using
            (uniformDistribution_sum_smul_equiv (e := e)
              (f := fun a : {a : α // a ∈ support} => f a.1))

/-- A uniform module-valued average over a filtered finite type may be reindexed
by any finite seed type equivalent to the predicate subtype. -/
theorem uniformOnFinset_filter_sum_smul_equiv {α β M : Type*}
    [Fintype α] (p : α → Prop) [DecidablePred p]
    [Fintype β] [DecidableEq β] [Nonempty β]
    [AddCommMonoid M] [Module Error M]
    (e : β ≃ {a : α // p a}) (f : α → M) :
    ∑ a ∈ (Distribution.uniformOnFinset (Finset.univ.filter p)).support,
        (Distribution.uniformOnFinset (Finset.univ.filter p)).weight a • f a =
      ∑ b ∈ (uniformDistribution β).support,
        (uniformDistribution β).weight b • f (e b).1 := by
  classical
  have : Nonempty {a : α // p a} :=
    ⟨e (Classical.choice (inferInstance : Nonempty β))⟩
  calc
    ∑ a ∈ (Distribution.uniformOnFinset (Finset.univ.filter p)).support,
        (Distribution.uniformOnFinset (Finset.univ.filter p)).weight a • f a =
        ∑ a ∈ (uniformDistribution {a : α // p a}).support,
          (uniformDistribution {a : α // p a}).weight a • f a.1 := by
          exact uniformOnFinset_filter_sum_smul_eq_subtype p f
    _ = ∑ b ∈ (uniformDistribution β).support,
          (uniformDistribution β).weight b • f (e b).1 := by
          simpa using
            (uniformDistribution_sum_smul_equiv (e := e.symm)
              (f := fun a : {a : α // p a} => f a.1))

end MIPStarRE.LDT

end

end LIDT


