-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
-- name    : LIDT_MIPStarRE_LDT_Basic_DistributionAvg
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T10:54:11.12787+00:00
-- url     : https://prove2.me/theorems/20c0da3a-ac91-4e71-955b-0a1c8525f59d
-- title:
--   LIDT definitions: LDT / Basic / DistributionAvg
-- statement:
--   This bundle develops finite-support scalar averaging and its uniform marginalization rules. The identities provide the linear, order, Fubini, product, and supportwise manipulations used throughout test averages and induction estimates.
--
--   Principal definitions:
--   - `avgOver`: The weighted finite average of a scalar function over a finite-support distribution.
--   - `avgOver_mono`: A pointwise inequality is preserved by averaging with nonnegative weights.
--   - `avgOver_nonneg`: A pointwise nonnegative function has nonnegative average.
--   - `avgOver_add` and `avgOver_sub`: Averaging commutes with addition and subtraction.
--   - `avgOver_sum` and `avgOver_finset_sum`: Averaging commutes with finite sums over outcomes or indices.
--   - `avgOver_comm`: Two finite-support averages may be exchanged.
--   - `avgOver_uniform_prod`: Uniform averaging over a product factors into nested uniform averages.
--   - `avgOver_uniform_fst` and `avgOver_uniform_snd`: A function depending on one coordinate reduces to the corresponding uniform marginal average.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Basic/DistributionAvg.lean#L38-L762

-- Generated from MIPStarRE/LDT/Basic/DistributionAvg.lean by skeleton subtraction.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
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
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace LIDT

/-!
# Average lemmas for finite-support distributions

This module contains the finite-sum and uniform-average lemmas for the project
`Distribution` type.  The primitive distribution definitions, uniform
distributions, and total variation distance live in
`MIPStarRE.LDT.Basic.Distribution`.

## Main declarations

The main results are the algebraic rules for `avgOver`, scalar and
operator-valued forms of the module-valued finite-sum rules for uniform
distributions, and the comparison between finite uniform averages and Mathlib
uniform probability mass functions.

## References

These are formalization-internal finite probability lemmas for the low
individual degree test development.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT

/-! ### Averaging infrastructure

Linearity proofs use `Distribution.weightedSumLinearMap`; order and support
estimates use Mathlib's `Finset.sum` API. -/

/-- Averaging the zero function gives zero. -/
theorem avgOver_zero {α : Type*} (𝒟 : Distribution α) :
    avgOver 𝒟 (fun _ => 0) = 0 := by
  simp [Distribution.avgOver_eq_weightedSumLinearMap]

/-- Averaging preserves order when weights are nonneg. -/
theorem avgOver_mono {α : Type*} (𝒟 : Distribution α) (f g : α → Error)
    (hfg : ∀ a, f a ≤ g a) :
    avgOver 𝒟 f ≤ avgOver 𝒟 g := by
  simp only [avgOver]
  exact Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hfg a) (𝒟.nonnegative a)

/-- Averaging a nonneg function with nonneg weights gives a nonneg result. -/
theorem avgOver_nonneg {α : Type*} (𝒟 : Distribution α) (f : α → Error)
    (hf : ∀ a, 0 ≤ f a) :
    0 ≤ avgOver 𝒟 f := by
  simpa [avgOver_zero] using avgOver_mono 𝒟 (fun _ => 0) f hf

/-- Averaging distributes over addition. -/
theorem avgOver_add {α : Type*} (𝒟 : Distribution α) (f g : α → Error) :
    avgOver 𝒟 (fun a => f a + g a) =
      avgOver 𝒟 f + avgOver 𝒟 g := by
  change avgOver 𝒟 (f + g) = avgOver 𝒟 f + avgOver 𝒟 g
  simpa [Distribution.avgOver_eq_weightedSumLinearMap] using
    map_add (𝒟.weightedSumLinearMap Error) f g

/-- Averaging distributes over subtraction. -/
theorem avgOver_sub {α : Type*} (𝒟 : Distribution α) (f g : α → Error) :
    avgOver 𝒟 (fun a => f a - g a) =
      avgOver 𝒟 f - avgOver 𝒟 g := by
  change avgOver 𝒟 (f - g) = avgOver 𝒟 f - avgOver 𝒟 g
  simpa [Distribution.avgOver_eq_weightedSumLinearMap] using
    map_sub (𝒟.weightedSumLinearMap Error) f g

/-- Averaging commutes with scalar multiplication. -/
theorem avgOver_const_mul {α : Type*} (𝒟 : Distribution α)
    (c : Error) (f : α → Error) :
    avgOver 𝒟 (fun a => c * f a) =
      c * avgOver 𝒟 f := by
  change avgOver 𝒟 (c • f) = c • avgOver 𝒟 f
  simp [Distribution.avgOver_eq_weightedSumLinearMap, smul_eq_mul]

/-- Averaging commutes with scalar multiplication on the right. -/
theorem avgOver_mul_const {α : Type*} (𝒟 : Distribution α)
    (f : α → Error) (c : Error) :
    avgOver 𝒟 (fun a => f a * c) = avgOver 𝒟 f * c := by
  unfold avgOver
  calc
    ∑ a ∈ 𝒟.support, 𝒟.weight a * (f a * c)
      = ∑ a ∈ 𝒟.support, (𝒟.weight a * f a) * c := by
          refine Finset.sum_congr rfl ?_
          intro a _
          ring
    _ = (∑ a ∈ 𝒟.support, 𝒟.weight a * f a) * c := by
          rw [Finset.sum_mul]

/-- Pull a finite outcome sum through an average. -/
theorem avgOver_sum {α β : Type*} [Fintype β]
    (𝒟 : Distribution α) (f : α → β → Error) :
    avgOver 𝒟 (fun a => ∑ b : β, f a b) =
      ∑ b : β, avgOver 𝒟 (fun a => f a b) := by
  rw [show (fun a => ∑ b : β, f a b) = ∑ b : β, fun a => f a b by
    ext a
    simp]
  simp [Distribution.avgOver_eq_weightedSumLinearMap]

/-- Pull a finite-set sum through an average. -/
theorem avgOver_finset_sum {α β : Type*}
    (𝒟 : Distribution α) (s : Finset β) (f : α → β → Error) :
    avgOver 𝒟 (fun a => ∑ b ∈ s, f a b) =
      ∑ b ∈ s, avgOver 𝒟 (fun a => f a b) := by
  rw [show (fun a => ∑ b ∈ s, f a b) = ∑ b ∈ s, fun a => f a b by
    ext a
    simp]
  simp [Distribution.avgOver_eq_weightedSumLinearMap]

/-- Fubini swap for two nested finite-support distribution averages. -/
theorem avgOver_comm {α β : Type*} (𝒟α : Distribution α) (𝒟β : Distribution β)
    (f : α → β → Error) :
    avgOver 𝒟α (fun a => avgOver 𝒟β (f a)) =
      avgOver 𝒟β (fun b => avgOver 𝒟α (fun a => f a b)) := by
  unfold avgOver
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro b _
  refine Finset.sum_congr rfl ?_
  intro a _
  ring

/-- If `f = g` pointwise, their averages agree. -/
theorem avgOver_congr {α : Type*} (𝒟 : Distribution α)
    (f g : α → Error) (h : ∀ a, f a = g a) :
    avgOver 𝒟 f = avgOver 𝒟 g := by
  exact Finset.sum_congr rfl fun a _ => by rw [h a]

/-- If two scalar functions agree on a distribution's explicit support, their
averages agree.  This support-restricted form is useful for distributions whose
support carries an invariant not available for all ambient values. -/
theorem avgOver_congr_on_support {α : Type*} (𝒟 : Distribution α)
    (f g : α → Error) (h : ∀ a, a ∈ 𝒟.support → f a = g a) :
    avgOver 𝒟 f = avgOver 𝒟 g := by
  simp only [avgOver]
  exact Finset.sum_congr rfl fun a ha => by rw [h a ha]

/-- Averaging preserves supportwise order when weights are nonnegative.  This is
the support-restricted analogue of `avgOver_mono`. -/
theorem avgOver_mono_on_support {α : Type*} (𝒟 : Distribution α)
    (f g : α → Error) (h : ∀ a, a ∈ 𝒟.support → f a ≤ g a) :
    avgOver 𝒟 f ≤ avgOver 𝒟 g := by
  unfold avgOver
  exact Finset.sum_le_sum fun a ha =>
    mul_le_mul_of_nonneg_left (h a ha) (𝒟.nonnegative a)

/-- The average of a constant scalar is the total mass times that scalar. -/
theorem avgOver_const {α : Type*} (𝒟 : Distribution α) (c : Error) :
    avgOver 𝒟 (fun _ : α => c) =
      (∑ a ∈ 𝒟.support, 𝒟.weight a) * c := by
  unfold avgOver
  rw [Finset.sum_mul]

/-- Averaging a constant against a probability distribution returns that constant. -/
theorem avgOver_const_of_isProbability {α : Type*} (𝒟 : Distribution α)
    (h𝒟 : 𝒟.IsProbability) (c : Error) :
    avgOver 𝒟 (fun _ : α => c) = c := by
  rw [avgOver_const, h𝒟.weight_sum_eq_one, one_mul]















namespace Distribution.IsProbability

/-- A supportwise upper bound also bounds the average of a probability distribution.
This packages the paper convention that expectations are taken against genuine
probability distributions, while still allowing `Distribution` itself to carry a
larger ambient type than its explicit support. -/
theorem avgOver_le_of_forall_le_on_support {α : Type*} {𝒟 : Distribution α}
    (h𝒟 : 𝒟.IsProbability) (f : α → Error) (δ : Error)
    (hf : ∀ a, a ∈ 𝒟.support → f a ≤ δ) :
    avgOver 𝒟 f ≤ δ := by
  calc
    avgOver 𝒟 f ≤ avgOver 𝒟 (fun _ : α => δ) :=
      avgOver_mono_on_support 𝒟 f (fun _ : α => δ) hf
    _ = δ := avgOver_const_of_isProbability 𝒟 h𝒟 δ

end Distribution.IsProbability





/-- Averaging a constant against the uniform distribution on a nonempty finite type
returns that constant. -/
theorem avgOver_uniform_const {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α] (c : Error) :
    avgOver (uniformDistribution α) (fun _ : α => c) = c := by
  exact avgOver_const_of_isProbability
    (uniformDistribution α) (uniformDistribution_isProbability α) c

/-- Finite-sum expression for the uniform average, stated without measurable-space
assumptions. -/
theorem avgOver_uniform_eq_pmf_sum {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α] (f : α → Error) :
    avgOver (uniformDistribution α) f =
      ∑ a : α, (PMF.uniformOfFintype α a).toReal * f a := by
  simpa [avgOver, smul_eq_mul] using
    uniformDistribution_sum_smul_eq_pmf_sum (α := α) (f := f)























/-- A uniform average of effects is again bounded above by the identity operator. -/
theorem averageOperatorOverDistribution_uniform_le_one {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : α → MIPStarRE.Quantum.Op ι) (hf : ∀ a, f a ≤ 1) :
    averageOperatorOverDistribution (uniformDistribution α) f ≤ 1 :=
  averageOperatorOverDistribution_le_one_of_isProbability
    (uniformDistribution α) (uniformDistribution_isProbability α) f hf

/-- A uniform average is bounded by any supportwise upper bound. -/
theorem avgOver_uniform_le_of_forall_le_on_support {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    (f : α → Error) (δ : Error)
    (hf : ∀ a, a ∈ (uniformDistribution α).support → f a ≤ δ) :
    avgOver (uniformDistribution α) f ≤ δ :=
  Distribution.IsProbability.avgOver_le_of_forall_le_on_support
    (uniformDistribution_isProbability α) f δ hf

/-- A uniform average is bounded by any pointwise upper bound. -/
theorem avgOver_uniform_le_const {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    (f : α → Error) (δ : Error) (hf : ∀ a, f a ≤ δ) :
    avgOver (uniformDistribution α) f ≤ δ :=
  avgOver_uniform_le_of_forall_le_on_support f δ fun a _ => hf a

/-- Reindexing a uniform average along an equivalence preserves its value. -/
theorem avgOver_uniform_equiv
    {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (e : α ≃ β) (f : α → Error) :
    avgOver (uniformDistribution α) f =
      avgOver (uniformDistribution β) (fun b => f (e.symm b)) := by
  simpa [avgOver, smul_eq_mul] using
    (uniformDistribution_sum_smul_equiv (M := Error) (e := e) (f := f))





/-- A uniform average over a filtered finite type may be reindexed by any finite
seed type equivalent to the predicate subtype. -/
theorem avgOver_uniformOnFinset_filter_equiv {α β : Type*}
    [Fintype α] (p : α → Prop) [DecidablePred p]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (e : β ≃ {a : α // p a}) (f : α → Error) :
    avgOver (Distribution.uniformOnFinset (Finset.univ.filter p)) f =
      avgOver (uniformDistribution β) (fun b => f (e b).1) := by
  simpa [avgOver, smul_eq_mul] using
    uniformOnFinset_filter_sum_smul_equiv (p := p) (e := e) f

/-- Split a uniform average over a product into iterated uniform averages. -/
theorem avgOver_uniform_prod
    {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (f : α → β → Error) :
    avgOver (uniformDistribution (α × β)) (fun ab => f ab.1 ab.2) =
      avgOver (uniformDistribution α)
        (fun a => avgOver (uniformDistribution β) (fun b => f a b)) := by
  simpa [avgOver, smul_eq_mul] using
    (uniformDistribution_sum_smul_prod (M := Error) (f := f))

/-- Swap two nested uniform averages over finite nonempty types. -/
theorem avgOver_uniform_comm
    {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (f : α → β → Error) :
    avgOver (uniformDistribution α) (fun a => avgOver (uniformDistribution β) (f a)) =
      avgOver (uniformDistribution β) (fun b => avgOver (uniformDistribution α)
        (fun a => f a b)) := by
  simpa [avgOver, smul_eq_mul] using
    (uniformDistribution_sum_smul_comm (M := Error) (f := f))







/-- Transport a uniform average through an equivalence whose target is a product,
then split the product average with the second coordinate averaged first. -/
theorem avgOver_uniform_equiv_prod_swap
    {γ α β : Type*}
    [Fintype γ] [DecidableEq γ] [Nonempty γ]
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (e : γ ≃ α × β) (f : γ → Error) :
    avgOver (uniformDistribution γ) f =
      avgOver (uniformDistribution β)
        (fun b => avgOver (uniformDistribution α) (fun a => f (e.symm (a, b)))) := by
  simpa [avgOver, smul_eq_mul] using
    (uniformDistribution_sum_smul_equiv_prod_swap (M := Error) (e := e) (f := f))

/-- A function depending only on the first coordinate of a product equivalence
has the corresponding first-coordinate uniform marginal. -/
theorem avgOver_uniform_equiv_fst
    {γ α β : Type*}
    [Fintype γ] [DecidableEq γ] [Nonempty γ]
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Finite β] [Nonempty β]
    (e : γ ≃ α × β) (f : α → Error) :
    avgOver (uniformDistribution γ) (fun x => f (e x).1) =
      avgOver (uniformDistribution α) f := by
  simpa [avgOver, smul_eq_mul] using
    (uniformDistribution_sum_smul_equiv_fst (M := Error) (e := e) (f := f))

/-- A function depending only on the second coordinate of a product equivalence
has the corresponding second-coordinate uniform marginal. -/
theorem avgOver_uniform_equiv_snd
    {γ α β : Type*}
    [Fintype γ] [DecidableEq γ] [Nonempty γ]
    [Finite α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (e : γ ≃ α × β) (f : β → Error) :
    avgOver (uniformDistribution γ) (fun x => f (e x).2) =
      avgOver (uniformDistribution β) f := by
  simpa [avgOver, smul_eq_mul] using
    (uniformDistribution_sum_smul_equiv_snd (M := Error) (e := e) (f := f))

/-- Averaging a function depending only on the first coordinate marginalizes a uniform product. -/
theorem avgOver_uniform_fst {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (f : α → Error) :
    avgOver (uniformDistribution (α × β)) (fun ab => f ab.1) =
      avgOver (uniformDistribution α) f := by
  simpa using (avgOver_uniform_equiv_fst (e := Equiv.refl (α × β)) (f := f))

/-- Averaging a function depending only on the second coordinate marginalizes a uniform product. -/
theorem avgOver_uniform_snd {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (f : β → Error) :
    avgOver (uniformDistribution (α × β)) (fun ab => f ab.2) =
      avgOver (uniformDistribution β) f := by
  simpa using (avgOver_uniform_equiv_snd (e := Equiv.refl (α × β)) (f := f))

end MIPStarRE.LDT

end

end LIDT


