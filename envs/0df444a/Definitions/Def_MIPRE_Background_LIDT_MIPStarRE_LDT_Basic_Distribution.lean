-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_Distribution
-- name    : MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_Distribution
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T23:13:52.774259+00:00
-- url     : https://prove2.me/theorems/8910f770-c758-4337-9df6-173993b1b12f
-- title:
--   Definitions of Distribution: Distribution infrastructure for the low individual degree test Shared distribution definitions: finite-support weighted…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Basic.Distribution` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Distribution infrastructure for the low individual degree test. Shared distribution definitions: finite-support weighted distributions, a probability predicate, push-forward distributions, weighted-sum linear maps, averaging, uniform distribution, and outcome summation. Note: this module contributes declarations to the comparator statement closure of `mainFormal`, which must elaborate in the same environment as the Mathlib-only `Challenge.lean`. Keep the full `import Mathlib`; do not narrow it. See `docs/comparator.md`, "Environment alignment".
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   **Definitions** (11): `MIPStarRE.LDT.Distribution` (A finite-support weighted distribution with nonnegative real-valued weights.); `MIPStarRE.LDT.Distribution.IsProbability` (A `Distribution` is probabilistic when its total mass is exactly `1`.); `MIPStarRE.LDT.Distribution.map` (Push a finite-support distribution forward along a map.); `MIPStarRE.LDT.Distribution.toPMF` (The Mathlib probability mass function associated to a project `Distribution` whose total mass is one.); `MIPStarRE.LDT.Distribution.totalWeight` (The total mass carried by the explicit support of a distribution.); `MIPStarRE.LDT.Distribution.uniformOnFinset` (The uniform distribution on a specified finite support.); `MIPStarRE.LDT.Distribution.weightedSumLinearMap` (The module-valued weighted finite sum associated to a finite-support `Distribution`, as a linear map in the averaged family.); `MIPStarRE.LDT.averageOperatorOverDistribution` (Weighted sum of operators over a distribution's finite support, using the same `support`/`weight` data as the scalar `avgOver`.); `MIPStarRE.LDT.avgOver` (Average a scalar function against the stored finite support of a distribution.); `MIPStarRE.LDT.totalVariationDistance` (Total variation distance between two distributions: `TV(μ, ν) = ½ ∑_a |μ(a) - ν(a)|` over the union of supports.); `MIPStarRE.LDT.uniformDistribution` (The uniform distribution on a nonempty finite type.).
--
--   **Embedded lemmas** (13): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `weight_sum_eq_one`, `map_support`, `map_weight`, `toPMF_apply`, `toPMF_apply_toReal`, `uniformOnFinset_isProbability`, `uniformOnFinset_support`, `uniformOnFinset_weight`, `weightedSumLinearMap_apply`, `uniformDistribution_isProbability`, ….
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Basic.Distribution` (`MIPRE/Background/LIDT/MIPStarRE/LDT/Basic/Distribution.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 6 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/LDT/Basic/Distribution.lean

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Basic/Distribution.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/Basic/Distribution.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Spectrum.Quasispectrum
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.CharP.Invertible
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Finsupp
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Invertible.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.Group.Subsemigroup.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Hom
import Mathlib.Algebra.GroupWithZero.Invertible
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Opposites
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Nonneg.Basic
import Mathlib.Algebra.Order.Nonneg.Module
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.CStarAlgebra.Module.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.List.Nodup
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Multiset.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Star
import Mathlib.Data.Set.Defs
import Mathlib.Data.SetLike.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Logic.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Nonempty
import Mathlib.Order.Basic
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.RelClasses
import Mathlib.Order.SetNotation
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
import Mathlib.Topology.Algebra.Module.ClosedSubmodule
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Algebra.Star.Real
import Mathlib.Topology.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Continuous
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.Real
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.UniformSpace.Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace

set_option backward.isDefEq.respectTransparency false

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

open scoped BigOperators MatrixOrder Matrix ComplexOrder

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

end Distribution

namespace Distribution.IsProbability

/-- Unpack the equality form of the probability invariant. -/
theorem weight_sum_eq_one {α : Type*}
    {𝒟 : Distribution α} (h𝒟 : 𝒟.IsProbability) :
    ∑ a ∈ 𝒟.support, 𝒟.weight a = 1 := by
  simpa [Distribution.IsProbability, Distribution.totalWeight] using h𝒟

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

end Distribution

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

/-- Total variation distance between two distributions:
`TV(μ, ν) = ½ ∑_a |μ(a) - ν(a)|` over the union of supports. -/
noncomputable def totalVariationDistance {α : Type*} [DecidableEq α]
    (μ ν : Distribution α) : Error :=
  (1 / 2) * ∑ a ∈ (μ.support ∪ ν.support), |μ.weight a - ν.weight a|

end MIPStarRE.LDT


