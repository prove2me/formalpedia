-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
-- name    : LIDT_MIPStarRE_LDT_Basic_Distribution
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T10:48:52.275092+00:00
-- url     : https://prove2.me/theorems/b885864a-ad68-4782-a5c4-81ce9e680936
-- title:
--   LIDT definitions: LDT / Basic / Distribution
-- statement:
--   This bundle sets up the finite-support weighted distributions used throughout the LDT. It provides scalar and operator averaging, push-forward distributions, and the bridge to finite probability mass functions.
--
--   Principal definitions:
--   - `Distribution`: a finite-support family of nonnegative real weights, with weights zero outside the stored support.
--   - `Distribution.totalWeight`: the total weight on the explicit support.
--   - `Distribution.IsProbability`: the predicate that the total weight is one.
--   - `Distribution.map`: the push-forward distribution along a function, collecting weights over fibers.
--   - `Distribution.toPMF`: the associated Mathlib probability mass function when the distribution has total mass one.
--   - `avgOver`: the weighted finite average of a scalar family.
--   - `Distribution.weightedSumLinearMap`: the corresponding module-valued weighted sum as a linear map.
--   - `averageOperatorOverDistribution`: the weighted average of a family of operators.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Basic/Distribution.lean#L26-L530

-- Generated from MIPStarRE/LDT/Basic/Distribution.lean by skeleton subtraction.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib

namespace LIDT

/-!
# Distribution infrastructure for the low individual degree test

Shared distribution definitions: finite-support weighted distributions,
a probability predicate, push-forward distributions, weighted-sum linear maps,
averaging, uniform distribution, and outcome summation.

Note: this module contributes declarations to the comparator statement closure
of `mainFormal`, which must elaborate in the same environment as the
Mathlib-only `Challenge.lean`.  Keep the full `import Mathlib`; do not narrow
it.  See `docs/comparator.md`, "Environment alignment".
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT

/-- A finite-support weighted distribution with nonnegative real-valued weights. -/
structure Distribution (α : Type*) where
  support : Finset α := ∅
  weight : α → Error := fun _ => 0
  nonnegative : ∀ a, 0 ≤ weight a := by intro _; positivity
  outsideSupport : ∀ a, a ∉ support → weight a = 0 := by intro _ _; rfl

namespace Distribution

/-- The total mass carried by the explicit support of a distribution. -/
def totalWeight {α : Type*} (𝒟 : Distribution α) : Error :=
  ∑ a ∈ 𝒟.support, 𝒟.weight a

/-- A `Distribution` is probabilistic when its total mass is exactly `1`. -/
def IsProbability {α : Type*} (𝒟 : Distribution α) : Prop :=
  𝒟.totalWeight = 1

/-- Push a finite-support distribution forward along a map.

This is the project `Distribution` analogue of `PMF.map`.  The support is the
image of the original finite support, and each new weight is the sum of the
weights in the corresponding fiber. -/
noncomputable def map {α β : Type*} [DecidableEq β]
    (𝒟 : Distribution α) (e : α → β) : Distribution β where
  support := 𝒟.support.image e
  weight := fun b => ∑ a ∈ 𝒟.support.filter (fun a => e a = b), 𝒟.weight a
  nonnegative := fun _ => Finset.sum_nonneg fun a _ => 𝒟.nonnegative a
  outsideSupport := fun _ hb =>
    Finset.sum_eq_zero fun a ha =>
      (hb (Finset.mem_image.mpr
        ⟨a, (Finset.mem_filter.mp ha).1, (Finset.mem_filter.mp ha).2⟩)).elim

@[simp]
theorem map_support {α β : Type*} [DecidableEq β]
    (𝒟 : Distribution α) (e : α → β) :
    (𝒟.map e).support = 𝒟.support.image e := rfl

@[simp]
theorem map_weight {α β : Type*} [DecidableEq β]
    (𝒟 : Distribution α) (e : α → β) (b : β) :
    (𝒟.map e).weight b =
      ∑ a ∈ 𝒟.support.filter (fun a => e a = b), 𝒟.weight a := rfl



/-- A finite weighted sum over a push-forward distribution is the corresponding
weighted sum of the pulled-back family.  This is the `Distribution` analogue of
the finite-sum form of `PMF.map`. -/
theorem map_sum_smul {α β M : Type*} [DecidableEq β]
    [AddCommMonoid M] [Module Error M]
    (𝒟 : Distribution α) (e : α → β) (f : β → M) :
    ∑ b ∈ (𝒟.map e).support, (𝒟.map e).weight b • f b =
      ∑ a ∈ 𝒟.support, 𝒟.weight a • f (e a) := by
  classical
  calc
    ∑ b ∈ 𝒟.support.image e,
        (∑ a ∈ 𝒟.support.filter (fun a => e a = b), 𝒟.weight a) • f b
        = ∑ b ∈ 𝒟.support.image e,
            ∑ a ∈ 𝒟.support.filter (fun a => e a = b), 𝒟.weight a • f (e a) := by
          refine Finset.sum_congr rfl ?_
          intro b _
          rw [Finset.sum_smul]
          refine Finset.sum_congr rfl ?_
          intro a ha
          exact congrArg (fun x => 𝒟.weight a • f x) (Finset.mem_filter.mp ha).2.symm
    _ = ∑ a ∈ 𝒟.support, 𝒟.weight a • f (e a) := by
          exact Finset.sum_fiberwise_of_maps_to
            (s := 𝒟.support) (t := 𝒟.support.image e) (g := e)
            (fun a ha => Finset.mem_image.mpr ⟨a, ha, rfl⟩)
            (fun a => 𝒟.weight a • f (e a))

end Distribution

/-- On a finite ambient type, a summand that vanishes outside a distribution's
explicit support has the same total sum over all ambient values as over that support.

This is a project-local explicit-support adapter around Mathlib's `Finset.sum_subset`:
Mathlib supplies the finite-sum theorem, while this lemma packages the common shape used
when paper expressions sum over a whole question set but the repository stores a smaller
`Distribution.support`.  It is not intended to replace Mathlib probability theory. -/
theorem Distribution.sum_univ_eq_sum_support {α β : Type*} [Fintype α]
    [AddCommMonoid β] (𝒟 : Distribution α) (f : α → β)
    (hf : ∀ a, a ∉ 𝒟.support → f a = 0) :
    (∑ a : α, f a) = ∑ a ∈ 𝒟.support, f a := by
  classical
  simpa using
    (Finset.sum_subset (Finset.subset_univ 𝒟.support)
      (fun a _ ha => hf a ha)).symm

namespace Distribution.IsProbability

/-- Unpack the equality form of the probability invariant. -/
theorem weight_sum_eq_one {α : Type*}
    {𝒟 : Distribution α} (h𝒟 : 𝒟.IsProbability) :
    ∑ a ∈ 𝒟.support, 𝒟.weight a = 1 := by
  simpa [Distribution.IsProbability, Distribution.totalWeight] using h𝒟



/-- A probability distribution has total weight at most `1`. -/
theorem weight_sum_le_one {α : Type*}
    {𝒟 : Distribution α} (h𝒟 : 𝒟.IsProbability) :
    ∑ a ∈ 𝒟.support, 𝒟.weight a ≤ 1 :=
  le_of_eq h𝒟.weight_sum_eq_one



end Distribution.IsProbability

namespace Distribution

/-- The Mathlib probability mass function associated to a project `Distribution`
whose total mass is one.

The construction sends each nonnegative real weight to `ℝ≥0∞` by
`ENNReal.ofReal`; the hypotheses of `PMF.ofFinset` are exactly the project
probability invariant and the stored zero-off-support condition. -/
noncomputable def toPMF {α : Type*} (𝒟 : Distribution α)
    (h𝒟 : 𝒟.IsProbability) : PMF α :=
  PMF.ofFinset (fun a => ENNReal.ofReal (𝒟.weight a)) 𝒟.support
    (by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => 𝒟.nonnegative a),
        h𝒟.weight_sum_eq_one]
      simp)
    (by
      intro a ha
      rw [𝒟.outsideSupport a ha]
      simp)

@[simp]
theorem toPMF_apply {α : Type*} (𝒟 : Distribution α)
    (h𝒟 : 𝒟.IsProbability) (a : α) :
    𝒟.toPMF h𝒟 a = ENNReal.ofReal (𝒟.weight a) := rfl

@[simp]
theorem toPMF_apply_toReal {α : Type*} (𝒟 : Distribution α)
    (h𝒟 : 𝒟.IsProbability) (a : α) :
    (𝒟.toPMF h𝒟 a).toReal = 𝒟.weight a := by
  rw [toPMF_apply, ENNReal.toReal_ofReal (𝒟.nonnegative a)]

/-- The associated PMF has zero mass outside the stored support of the project
distribution. -/
theorem toPMF_apply_of_notMem {α : Type*} (𝒟 : Distribution α)
    (h𝒟 : 𝒟.IsProbability) {a : α} (ha : a ∉ 𝒟.support) :
    𝒟.toPMF h𝒟 a = 0 := by
  rw [toPMF_apply, 𝒟.outsideSupport a ha]
  simp



end Distribution

/-- Average a scalar function against the stored finite support of a distribution. -/
def avgOver {α : Type*} (𝒟 : Distribution α) (f : α → Error) : Error :=
  ∑ a ∈ 𝒟.support, 𝒟.weight a * f a

namespace Distribution

/-- The module-valued weighted finite sum associated to a finite-support `Distribution`,
as a linear map in the averaged family.

This packages the finite-support expression underlying both scalar averages and
operator averages.  It keeps the explicit support carried by `Distribution`,
while exposing the `Error`-module structure of the weighted sum. -/
noncomputable def weightedSumLinearMap (M : Type*) [AddCommMonoid M] [Module Error M]
    {α : Type*} (𝒟 : Distribution α) : (α → M) →ₗ[Error] M where
  toFun := fun f => ∑ a ∈ 𝒟.support, 𝒟.weight a • f a
  map_add' := fun f g => by
    simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib]
  map_smul' := fun c f => by
    simp only [Pi.smul_apply]
    calc
      ∑ a ∈ 𝒟.support, 𝒟.weight a • c • f a =
          ∑ a ∈ 𝒟.support, c • (𝒟.weight a • f a) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            rw [smul_smul, smul_smul, mul_comm]
      _ = c • ∑ a ∈ 𝒟.support, 𝒟.weight a • f a := by
            rw [Finset.smul_sum]

@[simp]
theorem weightedSumLinearMap_apply (M : Type*) [AddCommMonoid M] [Module Error M]
    {α : Type*} (𝒟 : Distribution α) (f : α → M) :
    𝒟.weightedSumLinearMap M f = ∑ a ∈ 𝒟.support, 𝒟.weight a • f a :=
  rfl

/-- The scalar average is the weighted finite-sum linear map applied to a scalar
family. -/
theorem avgOver_eq_weightedSumLinearMap {α : Type*}
    (𝒟 : Distribution α) (f : α → Error) :
    avgOver 𝒟 f = 𝒟.weightedSumLinearMap Error f := by
  simp [avgOver, smul_eq_mul]

/-- Averaging against a pushed-forward distribution is averaging the pulled-back
function against the original distribution. -/
theorem avgOver_map {α β : Type*} [DecidableEq β]
    (𝒟 : Distribution α) (e : α → β) (f : β → Error) :
    avgOver (𝒟.map e) f = avgOver 𝒟 (fun a => f (e a)) := by
  simpa [avgOver, smul_eq_mul] using
    Distribution.map_sum_smul (𝒟 := 𝒟) e f

end Distribution

/-- Weighted sum of operators over a distribution's finite support, using the same
`support`/`weight` data as the scalar `avgOver`.

This is a project-local adapter around Mathlib finite sums for the LDT
`Distribution` representation and `Quantum.Op` scalar action, not a replacement for
Mathlib's probability theory APIs. -/
noncomputable def averageOperatorOverDistribution {α : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (𝒟 : Distribution α) (f : α → MIPStarRE.Quantum.Op ι) : MIPStarRE.Quantum.Op ι :=
  ∑ a ∈ 𝒟.support, 𝒟.weight a • f a

namespace Distribution

/-- Operator averaging is the weighted finite-sum linear map applied to an
operator-valued family. -/
theorem averageOperatorOverDistribution_eq_weightedSumLinearMap {α : Type*}
    (𝒟 : Distribution α)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : α → MIPStarRE.Quantum.Op ι) :
    averageOperatorOverDistribution 𝒟 f =
      𝒟.weightedSumLinearMap (MIPStarRE.Quantum.Op ι) f :=
  rfl



end Distribution

/-- If two operator-valued families agree pointwise, their averages agree. -/
theorem averageOperatorOverDistribution_congr {α : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (𝒟 : Distribution α) (A B : α → MIPStarRE.Quantum.Op ι)
    (h : ∀ a, A a = B a) :
    averageOperatorOverDistribution 𝒟 A = averageOperatorOverDistribution 𝒟 B := by
  exact Finset.sum_congr rfl fun a _ => by rw [h a]

/-- Pull a finite outcome sum through an operator-valued average. -/
theorem averageOperatorOverDistribution_sum {α β : Type*} [Fintype β]
    (𝒟 : Distribution α)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : α → β → MIPStarRE.Quantum.Op ι) :
    averageOperatorOverDistribution 𝒟 (fun a => ∑ b : β, f a b) =
      ∑ b : β, averageOperatorOverDistribution 𝒟 (fun a => f a b) := by
  rw [show (fun a => ∑ b : β, f a b) = ∑ b : β, fun a => f a b by
    ext a
    simp]
  simp [Distribution.averageOperatorOverDistribution_eq_weightedSumLinearMap]



/-- Operator averages preserve positivity. -/
theorem averageOperatorOverDistribution_nonneg {α : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (𝒟 : Distribution α) (f : α → MIPStarRE.Quantum.Op ι)
    (hf : ∀ a, 0 ≤ f a) :
    0 ≤ averageOperatorOverDistribution 𝒟 f := by
  unfold averageOperatorOverDistribution
  exact Finset.sum_nonneg fun a _ => smul_nonneg (𝒟.nonnegative a) (hf a)

/-- Operator averages preserve pointwise order. -/
theorem averageOperatorOverDistribution_mono {α : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (𝒟 : Distribution α) (f g : α → MIPStarRE.Quantum.Op ι)
    (hfg : ∀ a, f a ≤ g a) :
    averageOperatorOverDistribution 𝒟 f ≤ averageOperatorOverDistribution 𝒟 g := by
  unfold averageOperatorOverDistribution
  exact Finset.sum_le_sum fun a _ =>
    smul_le_smul_of_nonneg_left (hfg a) (𝒟.nonnegative a)

/-- The average of a constant operator is the total mass times that operator. -/
theorem averageOperatorOverDistribution_const {α : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (𝒟 : Distribution α) (A : MIPStarRE.Quantum.Op ι) :
    averageOperatorOverDistribution 𝒟 (fun _ : α => A) =
      (∑ a ∈ 𝒟.support, 𝒟.weight a) • A := by
  unfold averageOperatorOverDistribution
  rw [Finset.sum_smul]



/-- An average of effects against a sub-probability distribution is again bounded
above by the identity operator. -/
theorem averageOperatorOverDistribution_le_one_of_weight_sum_le_one {α : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (𝒟 : Distribution α) (f : α → MIPStarRE.Quantum.Op ι)
    (h𝒟 : ∑ a ∈ 𝒟.support, 𝒟.weight a ≤ 1)
    (hf : ∀ a, f a ≤ 1) :
    averageOperatorOverDistribution 𝒟 f ≤ 1 := by
  calc
    averageOperatorOverDistribution 𝒟 f
        ≤ averageOperatorOverDistribution 𝒟 (fun _ : α => 1) := by
          exact averageOperatorOverDistribution_mono 𝒟 f (fun _ : α => 1) hf
    _ = (∑ a ∈ 𝒟.support, 𝒟.weight a) • (1 : MIPStarRE.Quantum.Op ι) := by
          exact averageOperatorOverDistribution_const 𝒟 1
    _ ≤ (1 : Error) • (1 : MIPStarRE.Quantum.Op ι) := by
          exact smul_le_smul_of_nonneg_right h𝒟 zero_le_one
    _ = 1 := by simp

/-- An average of effects against a probability distribution is again bounded
above by the identity operator. -/
theorem averageOperatorOverDistribution_le_one_of_isProbability {α : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (𝒟 : Distribution α) (h𝒟 : 𝒟.IsProbability)
    (f : α → MIPStarRE.Quantum.Op ι) (hf : ∀ a, f a ≤ 1) :
    averageOperatorOverDistribution 𝒟 f ≤ 1 :=
  averageOperatorOverDistribution_le_one_of_weight_sum_le_one 𝒟 f h𝒟.weight_sum_le_one hf

namespace Distribution

/-- The uniform distribution on a specified finite support.

The stored support is `s`, and the weight of a point is the elementary finite
uniform weight `1 / s.card` on `s` and `0` off `s`.  When the support is empty
this gives the zero sub-probability distribution, matching the convention used
for degenerate filtered supports in the LDT development. -/
noncomputable def uniformOnFinset {α : Type*} (s : Finset α) : Distribution α :=
  letI := Classical.decEq α
  { support := s
    weight := fun a => if a ∈ s then 1 / (s.card : Error) else 0
    nonnegative := fun _ => by
      split_ifs <;> positivity
    outsideSupport := fun _ ha => by
      simp [ha] }

@[simp]
theorem uniformOnFinset_support {α : Type*} (s : Finset α) :
    (uniformOnFinset s).support = s := rfl

@[simp]
theorem uniformOnFinset_weight {α : Type*} [DecidableEq α] (s : Finset α) (a : α) :
    (uniformOnFinset s).weight a =
      if a ∈ s then 1 / (s.card : Error) else 0 := by
  by_cases ha : a ∈ s
  · simp [uniformOnFinset, ha]
  · simp [uniformOnFinset, ha]

/-- A nonempty finite support gives a probability distribution. -/
theorem uniformOnFinset_isProbability {α : Type*} (s : Finset α) (hs : s.Nonempty) :
    (uniformOnFinset s).IsProbability := by
  classical
  dsimp [IsProbability, totalWeight]
  simp_rw [uniformOnFinset_weight]
  have hcard_nat : s.card ≠ 0 := Finset.card_ne_zero.mpr hs
  have hcard : (s.card : Error) ≠ 0 := by
    exact_mod_cast hcard_nat
  have hsum :
      (∑ a ∈ s, if a ∈ s then 1 / (s.card : Error) else 0) =
        ∑ _a ∈ s, 1 / (s.card : Error) := by
    refine Finset.sum_congr rfl ?_
    intro a ha
    simp [ha]
  rw [hsum]
  simp [Finset.sum_const, hcard]

/-- The uniform distribution on any finite support is a sub-probability
distribution.  It has mass `1` on nonempty support and mass `0` on empty
support. -/
theorem uniformOnFinset_weight_sum_le_one {α : Type*} (s : Finset α) :
    ∑ a ∈ (uniformOnFinset s).support, (uniformOnFinset s).weight a ≤ 1 := by
  classical
  by_cases hs : s.Nonempty
  · exact (uniformOnFinset_isProbability s hs).weight_sum_le_one
  · have hsempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [hsempty]

/-- The project uniform distribution on a nonempty finite support is Mathlib's
uniform probability mass function on that support. -/
theorem uniformOnFinset_toPMF
    {α : Type*} (s : Finset α) (hs : s.Nonempty) :
    (uniformOnFinset s).toPMF (uniformOnFinset_isProbability s hs) =
      PMF.uniformOfFinset s hs := by
  ext a
  rw [toPMF_apply]
  rw [show (uniformOnFinset s).weight a =
      (PMF.uniformOfFinset s hs a).toReal by
        classical
        by_cases ha : a ∈ s
        · simp [uniformOnFinset_weight, PMF.uniformOfFinset_apply, ha,
            ENNReal.toReal_inv, ENNReal.toReal_natCast]
        · simp [uniformOnFinset_weight, PMF.uniformOfFinset_apply, ha]]
  exact ENNReal.ofReal_toReal ((PMF.uniformOfFinset s hs).apply_ne_top a)

end Distribution

/-- The uniform distribution on a nonempty finite type. -/
noncomputable def uniformDistribution (α : Type*)
    [Fintype α] [DecidableEq α] [Nonempty α] : Distribution α :=
  Distribution.uniformOnFinset Finset.univ

/-- The uniform distribution on a finite type has full support. -/
@[simp]
theorem uniformDistribution_support (α : Type*)
    [Fintype α] [DecidableEq α] [Nonempty α] :
    (uniformDistribution α).support = Finset.univ := rfl

/-- The weights of a uniform distribution sum to exactly `1`. -/
theorem uniformDistribution_weight_sum_eq_one (α : Type*)
    [Fintype α] [DecidableEq α] [Nonempty α] :
    ∑ a ∈ (uniformDistribution α).support, (uniformDistribution α).weight a = 1 := by
  have h : (uniformDistribution α).IsProbability := by
    simpa [uniformDistribution] using
      Distribution.uniformOnFinset_isProbability (Finset.univ : Finset α)
        Finset.univ_nonempty
  exact h.weight_sum_eq_one

/-- The uniform distribution is a genuine probability distribution. -/
theorem uniformDistribution_isProbability (α : Type*)
    [Fintype α] [DecidableEq α] [Nonempty α] :
    (uniformDistribution α).IsProbability := by
  simpa [uniformDistribution] using
    Distribution.uniformOnFinset_isProbability (Finset.univ : Finset α) Finset.univ_nonempty

/-- The weights of a uniform distribution sum to at most `1`. -/
theorem uniformDistribution_weight_sum_le_one (α : Type*)
    [Fintype α] [DecidableEq α] [Nonempty α] :
    ∑ a ∈ (uniformDistribution α).support, (uniformDistribution α).weight a ≤ 1 :=
  le_of_eq (uniformDistribution_weight_sum_eq_one α)

/-- The project uniform distribution on a nonempty finite type is Mathlib's
uniform probability mass function on that type. -/
theorem uniformDistribution_toPMF
    (α : Type*) [Fintype α] [DecidableEq α] [Nonempty α] :
    (uniformDistribution α).toPMF (uniformDistribution_isProbability α) =
      PMF.uniformOfFintype α := by
  simpa [uniformDistribution, PMF.uniformOfFintype] using
    Distribution.uniformOnFinset_toPMF (Finset.univ : Finset α) Finset.univ_nonempty

/-- Total variation distance between two distributions:
`TV(μ, ν) = ½ ∑_a |μ(a) - ν(a)|` over the union of supports. -/
noncomputable def totalVariationDistance {α : Type*} [DecidableEq α]
    (μ ν : Distribution α) : Error :=
  (1 / 2) * ∑ a ∈ (μ.support ∪ ν.support), |μ.weight a - ν.weight a|





end MIPStarRE.LDT

end

end LIDT


