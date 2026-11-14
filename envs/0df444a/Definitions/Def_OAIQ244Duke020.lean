-- Prove2me | Definitions.Def_OAIQ244Duke020
-- name    : OAIQ244Duke020
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T06:17:38.873377+00:00
-- url     : https://prove2.me/theorems/f3284710-14fe-4bc1-9911-a482ec7cd25e
-- title:
--   Definitions bundle OAIQ244Duke020 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 72 declarations of OpenAI's Lean: 23 definitions, 6 instances and 43 theorems. The definitions and types are `GlobalClassFieldTheory.Reciprocity.finitePlaceNormUpperNontriviallyNormedField`, `KummerTheory.nthRootsSubgroupEquivOfPrimitiveRoots`, `KummerTheory.nthRootsSubgroupMap`, `KummerTheory.unitCharactersEquivNthRoots`, `LocalFieldTheory.galoisGroupPrincipalUnitsMapEquivHomOfIsIntegralClosure`, `LocalFieldTheory.galoisGroupPrincipalUnitsMapEquivOfIsIntegralClosure`, `LocalFieldTheory.localBaseUnitSubgroup`, `LocalFieldTheory.maximalIdealPowMapEquivOfIntegerRingEquiv`, `LocalFieldTheory.maximalIdealPowSuccQuotMapEquivOfIntegerRingEquiv`, `LocalFieldTheory.maximalIdealPowSuccQuotMapOfIntegerRingEquiv`, `LocalFieldTheory.maximalIdealPowSuccQuotMultiplicativeMapEquivOfIntegerRingEquiv`, `OAI.PrimeDegreePackets.rootCanonicalFlow`, `SUnitGroup.LogHyperplane`, `SUnitGroup.coordinateSum`, `SUnitGroup.forgetDistinguishedLog`, `SUnitGroup.fullLog`, `SUnitGroup.fullLogLattice`, `SUnitGroup.logHyperplaneContinuousEquivReduced`, `SUnitGroup.logHyperplaneEquivReduced`, `SUnitGroup.reducedLogLattice`, `SUnitGroup.reducedLogLinearMap`, `finitePlaceCompletionAlgEquiv`, `ramifiedBaseFinitePlaces`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `AlgebraicNumberTheory_Idele_Cohomology_SupportedBridge`, `AlgebraicNumberTheory_Idele_Relative_FinitePlaceTensorNorm`, `AlgebraicNumberTheory_SUnit_GaloisAction`, `AlgebraicNumberTheory_SUnit_LogLattice`, `AlgebraicNumberTheory_SUnit_Rank`, `GlobalClassFieldTheory_Reciprocity_FinitePlaceArtin_NormRestriction`, `KummerTheory_Concrete_CyclotomicPrimeBaseChange`, `Kummer_Concrete_FiniteDualSeparation`, `Kummer_Concrete_InfiniteContinuity`, `Kummer_Concrete_RestrictedFinite`, `LocalClassFieldTheory_ClassFormation_LocalizedCompletionCohomology_CompMulEquiv`, `LocalClassFieldTheory_Finite_Unramified_PrincipalUnits_NormSide`, `LocalField_NonarchimedeanLocalField_GaloisIntegerRing`, `LocalField_NonarchimedeanLocalField_Norm`, `LocalField_NonarchimedeanLocalField_NormContinuity`, `LocalField_NonarchimedeanLocalField_PrincipalUnitActions`, `LocalField_NonarchimedeanLocalField_PrincipalUnitQuotients`, `LocalField_NonarchimedeanLocalField_ResidueExtension`, `LocalField_NonarchimedeanLocalField_ResidueUnits`, `LocalField_NonarchimedeanLocalField_UnitTopology`, `PrimePackets_ScalingCovariance`, `Valuation_Completion_FiniteProductNormTrace`.
--
--   **Imports.** It imports the published bundle `Def_DukePrimeDegree`; the bundles `OAIQ244Duke000`, `OAIQ244Duke001`, `OAIQ244Duke002`, `OAIQ244Duke003`, `OAIQ244Duke004`, `OAIQ244Duke006`, `OAIQ244Duke007`, `OAIQ244Duke008`, `OAIQ244Duke011` and `OAIQ244Duke012` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke027`, `OAIQ244Duke031`, `OAIQ244Duke032`, `OAIQ244Duke033` and `OAIQ244Duke036`.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.CharP.Subring
import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.Group.Int.TypeTags
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Algebra.Group.Submonoid.Units
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Algebra.GroupWithZero.Action.Prod
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Module.LinearMap.Polynomial
import Mathlib.Algebra.Module.PID
import Mathlib.Algebra.Module.Shrink
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Algebra.Order.Hom.Units
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.Algebra.Order.WithTop.Untop0
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Normed.Algebra.GelfandMazur
import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.Analysis.Normed.Field.ProperSpace
import Mathlib.Analysis.Normed.Field.WithAbs
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.FieldTheory.Galois.Notation
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.DoubleCoset
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.QuotientGroup.Finite
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Transfer
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.Trace
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances
import Mathlib.NumberTheory.NumberField.Completion.Ramification
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.NumberTheory.NumberField.Units.Regulator
import Mathlib.NumberTheory.Ostrowski
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.NumberTheory.RamificationInertia.Valuation
import Mathlib.RepresentationTheory.Homological.FiniteCyclic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Mathlib.RepresentationTheory.Homological.GroupHomology.FiniteCyclic
import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.Adjoin.PowerBasis
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.AlgebraTower
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.ClassGroup.ExtendedHom
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.SInteger
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.FractionalIdeal.Norm
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.IsPrincipalPowQuotient
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Invariant.Profinite
import Mathlib.RingTheory.IsTensorProduct
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Polynomial.ContentIdeal
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.Group.SubmonoidClosure
import Mathlib.Topology.Algebra.Group.TopologicalAbelianization
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.IsOpenUnits
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Compact
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.Topology.Algebra.Valued.ValuativeRel
import Mathlib.Topology.Algebra.Valued.ValuedField
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Sign
import Mathlib.Topology.Instances.ZMod
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.UniformSpace.AbsoluteValue
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke000
import Definitions.Def_OAIQ244Duke001
import Definitions.Def_OAIQ244Duke002
import Definitions.Def_OAIQ244Duke003
import Definitions.Def_OAIQ244Duke004
import Definitions.Def_OAIQ244Duke006
import Definitions.Def_OAIQ244Duke007
import Definitions.Def_OAIQ244Duke008
import Definitions.Def_OAIQ244Duke011
import Definitions.Def_OAIQ244Duke012

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_Norm
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
/-!
# Norms in valued field extensions

Packages field norms as homomorphisms on units and restricts them to valuation
rings and their unit groups under the appropriate integral hypotheses.
-/

set_option autoImplicit false

namespace LocalFieldTheory

noncomputable section

universe u v

namespace IsNonarchimedeanLocalField

open scoped BigOperators ValuativeRel

variable {K : Type u} {L : Type v}

section UnitNorm

variable [Field K] [Field L] [Algebra K L]

/-- The unit norm of an embedded base unit is the degree-th power of that base unit. -/
lemma normUnits_algebraMap_base (x : Kˣ) :
    normUnits K L (mapBaseUnitsToExtensionUnits K L x) =
      Units.map (MonoidHom.id K) (x ^ Module.finrank K L) := by
  ext
  simp [normUnits, mapBaseUnitsToExtensionUnits, Algebra.norm_algebraMap]

/-- Coercing the integer-unit norm to the base field yields the algebra norm of the original unit. -/
lemma normIntegerUnits_apply_coe [ValuativeRel K] [ValuativeRel L]
    [LocalFieldTheory.ValuativeExtension K L] (x : 𝒪[L]ˣ) :
    (((normIntegerUnits K L x : 𝒪[K]ˣ) : 𝒪[K]) : K) =
      Algebra.norm K (((x : 𝒪[L]ˣ) : 𝒪[L]) : L) :=
  rfl

end UnitNorm

section Valuation

variable [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
variable [Algebra K L]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] in
/-- For a finite Galois extension, embedding the unit norm back into the extension equals the
product of all Galois conjugates. -/
lemma mapBaseUnits_normUnits_eq_prod_gal [FiniteDimensional K L] [IsGalois K L]
    (x : Lˣ) :
    mapBaseUnitsToExtensionUnits K L (normUnits K L x) =
      ∏ σ : L ≃ₐ[K] L, Units.mapEquiv σ.toMulEquiv x := by
  ext
  simp [mapBaseUnitsToExtensionUnits, normUnits, Algebra.norm_eq_prod_automorphisms]

end Valuation

end IsNonarchimedeanLocalField

end
end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_PrincipalUnitQuotients
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.integerUnitsModPrincipalUnitsConcreteEquiv_mk _root_.LocalFieldTheory.integerUnitsModPrincipalUnitsLift_mk _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
/-!
# Successive principal-unit quotients

Develops `U^n/U^(n+1)` and identifies it with the additive ideal quotient
`𝓂^n/𝓂^(n+1)` through the first-order map `a ↦ 1 + a`.
-/

set_option autoImplicit false

namespace LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

open Filter

/-! ### Separatedness of the principal-unit filtration -/

/-! ### Maximal-ideal powers as local neighborhoods -/

/-! ### Finite correction products for complete lifting -/

/-- If a principal unit has the same first-order term as `1 + a` modulo
`𝓂^(n+1)`, then it has the same class in `U^n/U^(n+1)`. -/
theorem principalUnitsSuccQuotMk_eq_oneAdd_of_sub_one_sub_mem_succ
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) (hn : 1 ≤ n)
    (u : principalUnits K n) (a : (𝓂[K] ^ n : Ideal 𝒪[K]))
    (h : (((u : 𝒪[K]ˣ) : 𝒪[K]) - 1 - (a : 𝒪[K])) ∈
      (𝓂[K] ^ (n + 1) : Ideal 𝒪[K])) :
    principalUnitsSuccQuotMk K n u =
      principalUnitsSuccQuotOfIdealPow K n hn a := by
  rw [principalUnitsSuccQuotOfIdealPow_apply]
  apply (principalUnitsSuccQuotMk_eq_iff_div_mem K n _ _).2
  rw [mem_principalUnits_succ_subgroupOf_iff]
  change ((((u : 𝒪[K]ˣ) /
        principalUnitOneAddOfMemPow K hn (a : 𝒪[K]) a.2 : 𝒪[K]ˣ) : 𝒪[K]) - 1) ∈
    (𝓂[K] ^ (n + 1) : Ideal 𝒪[K])
  rw [show ((((u : 𝒪[K]ˣ) /
        principalUnitOneAddOfMemPow K hn (a : 𝒪[K]) a.2 : 𝒪[K]ˣ) : 𝒪[K]) - 1) =
      (((u : 𝒪[K]ˣ) : 𝒪[K]) - 1 - (a : 𝒪[K])) *
        ↑(principalUnitOneAddOfMemPow K hn (a : 𝒪[K]) a.2)⁻¹ by
    simp only [div_eq_mul_inv, Units.val_mul]
    have hunit :
        ((principalUnitOneAddOfMemPow K hn (a : 𝒪[K]) a.2 : 𝒪[K]ˣ) : 𝒪[K]) *
          ↑(principalUnitOneAddOfMemPow K hn (a : 𝒪[K]) a.2)⁻¹ = 1 := by
      simp
    calc
      ((u : 𝒪[K]ˣ) : 𝒪[K]) *
            ↑(principalUnitOneAddOfMemPow K hn (a : 𝒪[K]) a.2)⁻¹ - 1 =
          ((u : 𝒪[K]ˣ) : 𝒪[K]) *
              ↑(principalUnitOneAddOfMemPow K hn (a : 𝒪[K]) a.2)⁻¹ -
            ((principalUnitOneAddOfMemPow K hn (a : 𝒪[K]) a.2 : 𝒪[K]ˣ) : 𝒪[K]) *
              ↑(principalUnitOneAddOfMemPow K hn (a : 𝒪[K]) a.2)⁻¹ := by
        rw [hunit]
      _ = (((u : 𝒪[K]ˣ) : 𝒪[K]) - 1 - (a : 𝒪[K])) *
          ↑(principalUnitOneAddOfMemPow K hn (a : 𝒪[K]) a.2)⁻¹ := by
        rw [principalUnitOneAddOfMemPow_val K hn (a : 𝒪[K]) a.2]
        ring]
  exact (𝓂[K] ^ (n + 1) : Ideal 𝒪[K]).mul_mem_right _ h

/-- If every `aᵢ` lies in `𝓂^n` with `n ≥ 1`, then
`∏ᵢ (1 + aᵢ) - 1` lies in the maximal ideal. -/
theorem finset_prod_one_add_sub_one_mem_maximalIdeal_of_mem_pow
    (K : Type u) [Field K] [ValuativeRel K] {ι : Type*}
    (s : Finset ι) (n : Nat) (hn : 1 ≤ n) (a : ι → 𝒪[K])
    (ha : ∀ i ∈ s, a i ∈ (𝓂[K] ^ n : Ideal 𝒪[K])) :
    (s.prod fun i => 1 + a i) - 1 ∈ (𝓂[K] : Ideal 𝒪[K]) := by
  classical
  revert a
  refine Finset.induction_on s ?base ?step
  · intro a ha
    simp
  · intro i s hi ih a ha
    have hai_pow : a i ∈ (𝓂[K] ^ n : Ideal 𝒪[K]) := ha i (by simp [hi])
    have hai : a i ∈ (𝓂[K] : Ideal 𝒪[K]) := by
      have hle : (𝓂[K] ^ n : Ideal 𝒪[K]) ≤ (𝓂[K] ^ 1 : Ideal 𝒪[K]) :=
        Ideal.pow_le_pow_right hn
      simpa using hle hai_pow
    have hs : ∀ j ∈ s, a j ∈ (𝓂[K] ^ n : Ideal 𝒪[K]) := by
      intro j hj
      exact ha j (by simp [hj])
    have hprod : (s.prod fun j => 1 + a j) - 1 ∈ (𝓂[K] : Ideal 𝒪[K]) :=
      ih a hs
    have hterm : a i * (s.prod fun j => 1 + a j) ∈ (𝓂[K] : Ideal 𝒪[K]) :=
      (𝓂[K] : Ideal 𝒪[K]).mul_mem_right _ hai
    rw [Finset.prod_insert hi]
    rw [show (1 + a i) * (s.prod fun j => 1 + a j) - 1 =
        ((s.prod fun j => 1 + a j) - 1) +
          a i * (s.prod fun j => 1 + a j) by
      ring]
    exact (𝓂[K] : Ideal 𝒪[K]).add_mem hprod hterm

/-- First-order expansion of products in the principal-unit filtration:
if every `aᵢ ∈ 𝓂^n` and `n ≥ 1`, then
`∏ᵢ (1 + aᵢ) ≡ 1 + Σᵢ aᵢ mod 𝓂^(n+1)`. -/
theorem finset_prod_one_add_sub_one_sub_sum_mem_maximalIdeal_pow_succ
    (K : Type u) [Field K] [ValuativeRel K] {ι : Type*}
    (s : Finset ι) (n : Nat) (hn : 1 ≤ n) (a : ι → 𝒪[K])
    (ha : ∀ i ∈ s, a i ∈ (𝓂[K] ^ n : Ideal 𝒪[K])) :
    (s.prod fun i => 1 + a i) - 1 - (s.sum fun i => a i) ∈
      (𝓂[K] ^ (n + 1) : Ideal 𝒪[K]) := by
  classical
  revert a
  refine Finset.induction_on s ?base ?step
  · intro a ha
    simp
  · intro i s hi ih a ha
    have hai : a i ∈ (𝓂[K] ^ n : Ideal 𝒪[K]) := ha i (by simp [hi])
    have hs : ∀ j ∈ s, a j ∈ (𝓂[K] ^ n : Ideal 𝒪[K]) := by
      intro j hj
      exact ha j (by simp [hj])
    have hind :
        (s.prod fun j => 1 + a j) - 1 - (s.sum fun j => a j) ∈
          (𝓂[K] ^ (n + 1) : Ideal 𝒪[K]) :=
      ih a hs
    have hprod :
        (s.prod fun j => 1 + a j) - 1 ∈ (𝓂[K] : Ideal 𝒪[K]) :=
      finset_prod_one_add_sub_one_mem_maximalIdeal_of_mem_pow K s n hn a hs
    have hmul_raw :
        a i * ((s.prod fun j => 1 + a j) - 1) ∈
          (𝓂[K] ^ n : Ideal 𝒪[K]) * (𝓂[K] : Ideal 𝒪[K]) :=
      Ideal.mul_mem_mul hai hprod
    have hmul :
        a i * ((s.prod fun j => 1 + a j) - 1) ∈
          (𝓂[K] ^ (n + 1) : Ideal 𝒪[K]) := by
      simpa [pow_add] using hmul_raw
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    rw [show (1 + a i) * (s.prod fun j => 1 + a j) - 1 -
          (a i + (s.sum fun j => a j)) =
        ((s.prod fun j => 1 + a j) - 1 - (s.sum fun j => a j)) +
          a i * ((s.prod fun j => 1 + a j) - 1) by
      ring]
    exact (𝓂[K] ^ (n + 1) : Ideal 𝒪[K]).add_mem hind hmul

end
end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_PrincipalUnitActions
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
/-!
# Actions on principal-unit quotients

Transports valuation-ring automorphisms to maximal-ideal powers, principal
units, and their successive quotients, together with the resulting actions.
-/

set_option autoImplicit false

namespace LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

/-- The induced additive equivalence on the ideal power `𝓂^n`. -/
def maximalIdealPowMapEquivOfIntegerRingEquiv
    (K : Type u) [Field K] [ValuativeRel K]
    (n : Nat) (e : 𝒪[K] ≃+* 𝒪[K]) :
    ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u) ≃+
      ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u) where
  toFun a := ⟨e (a : 𝒪[K]), (integerRingEquiv_mem_maximalIdeal_pow K e n a).2 a.2⟩
  invFun a :=
    ⟨e.symm (a : 𝒪[K]), (integerRingEquiv_mem_maximalIdeal_pow K e.symm n a).2 a.2⟩
  left_inv := by
    intro a
    ext
    simp
  right_inv := by
    intro a
    ext
    simp
  map_add' := by
    intro a b
    ext
    simp

theorem maximalIdealPowSuccQuotMapOfIntegerRingEquiv_respects
    (K : Type u) [Field K] [ValuativeRel K]
    (n : Nat) (e : 𝒪[K] ≃+* 𝒪[K])
    (a b : ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u))
    (hab : a - b ∈ maximalIdealPowSuccSubmodule K n) :
    maximalIdealPowSuccQuotMk K n
        (maximalIdealPowMapEquivOfIntegerRingEquiv K n e a) =
      maximalIdealPowSuccQuotMk K n
        (maximalIdealPowMapEquivOfIntegerRingEquiv K n e b) := by
  apply (maximalIdealPowSuccQuotMk_eq_iff K n _ _).2
  rw [mem_maximalIdealPowSuccSubmodule_iff]
  change e (a : 𝒪[K]) - e (b : 𝒪[K]) ∈
    (𝓂[K] ^ (n + 1) : Ideal 𝒪[K])
  rw [← map_sub]
  exact (integerRingEquiv_mem_maximalIdeal_pow K e (n + 1)
    ((a - b : (𝓂[K] ^ n : Ideal 𝒪[K])) : 𝒪[K])).2
      ((mem_maximalIdealPowSuccSubmodule_iff K n (a - b)).1 hab)

/-- The induced additive homomorphism on `𝓂^n/𝓂^(n+1)`. -/
def maximalIdealPowSuccQuotMapOfIntegerRingEquiv
    (K : Type u) [Field K] [ValuativeRel K]
    (n : Nat) (e : 𝒪[K] ≃+* 𝒪[K]) :
    MaximalIdealPowSuccQuot K n →+ MaximalIdealPowSuccQuot K n := by
  let f : MaximalIdealPowSuccQuot K n → MaximalIdealPowSuccQuot K n :=
    maximalIdealPowSuccQuotLift n
      (fun a => maximalIdealPowSuccQuotMk K n
        (maximalIdealPowMapEquivOfIntegerRingEquiv K n e a))
      (maximalIdealPowSuccQuotMapOfIntegerRingEquiv_respects K n e)
  refine
    { toFun := f
      map_zero' := ?_
      map_add' := ?_ }
  · change f 0 = 0
    rw [← map_zero (maximalIdealPowSuccQuotMk K n)]
    dsimp only [f]
    rw [maximalIdealPowSuccQuotLift_mk, map_zero, map_zero]
  · intro x y
    change f (x + y) = f x + f y
    refine MaximalIdealPowSuccQuot.inductionOn₂ n
      (motive := fun x' y' => f (x' + y') = f x' + f y') x y ?_
    intro a b
    rw [← map_add (maximalIdealPowSuccQuotMk K n)]
    dsimp only [f]
    rw [maximalIdealPowSuccQuotLift_mk,
      maximalIdealPowSuccQuotLift_mk,
      maximalIdealPowSuccQuotLift_mk, map_add, map_add]

/-- The map on successive maximal-ideal quotients sends a representative to the class of its image
under the ring equivalence. -/
theorem maximalIdealPowSuccQuotMapOfIntegerRingEquiv_mk
    (K : Type u) [Field K] [ValuativeRel K]
    (n : Nat) (e : 𝒪[K] ≃+* 𝒪[K])
    (a : ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u)) :
    maximalIdealPowSuccQuotMapOfIntegerRingEquiv K n e
        (maximalIdealPowSuccQuotMk K n a) =
      maximalIdealPowSuccQuotMk K n
        (maximalIdealPowMapEquivOfIntegerRingEquiv K n e a) := by
  change maximalIdealPowSuccQuotLift n
      (fun b => maximalIdealPowSuccQuotMk K n
        (maximalIdealPowMapEquivOfIntegerRingEquiv K n e b))
      (maximalIdealPowSuccQuotMapOfIntegerRingEquiv_respects K n e)
      (maximalIdealPowSuccQuotMk K n a) =
    maximalIdealPowSuccQuotMk K n
      (maximalIdealPowMapEquivOfIntegerRingEquiv K n e a)
  exact maximalIdealPowSuccQuotLift_mk n _ _ a

/-- The induced additive equivalence on `𝓂^n/𝓂^(n+1)`. -/
def maximalIdealPowSuccQuotMapEquivOfIntegerRingEquiv
    (K : Type u) [Field K] [ValuativeRel K]
    (n : Nat) (e : 𝒪[K] ≃+* 𝒪[K]) :
    MaximalIdealPowSuccQuot K n ≃+ MaximalIdealPowSuccQuot K n where
  toFun := maximalIdealPowSuccQuotMapOfIntegerRingEquiv K n e
  invFun := maximalIdealPowSuccQuotMapOfIntegerRingEquiv K n e.symm
  left_inv := by
    intro x
    refine MaximalIdealPowSuccQuot.inductionOn n
      (motive := fun x' =>
        maximalIdealPowSuccQuotMapOfIntegerRingEquiv K n e.symm
            (maximalIdealPowSuccQuotMapOfIntegerRingEquiv K n e x') = x')
      x ?_
    intro a
    rw [maximalIdealPowSuccQuotMapOfIntegerRingEquiv_mk,
      maximalIdealPowSuccQuotMapOfIntegerRingEquiv_mk]
    have h := (maximalIdealPowMapEquivOfIntegerRingEquiv K n e).left_inv a
    exact congrArg (maximalIdealPowSuccQuotMk K n) h
  right_inv := by
    intro x
    refine MaximalIdealPowSuccQuot.inductionOn n
      (motive := fun x' =>
        maximalIdealPowSuccQuotMapOfIntegerRingEquiv K n e
            (maximalIdealPowSuccQuotMapOfIntegerRingEquiv K n e.symm x') = x')
      x ?_
    intro a
    rw [maximalIdealPowSuccQuotMapOfIntegerRingEquiv_mk,
      maximalIdealPowSuccQuotMapOfIntegerRingEquiv_mk]
    have h := (maximalIdealPowMapEquivOfIntegerRingEquiv K n e).right_inv a
    exact congrArg (maximalIdealPowSuccQuotMk K n) h
  map_add' := by
    intro x y
    exact map_add (maximalIdealPowSuccQuotMapOfIntegerRingEquiv K n e) x y

/-- Multiplicative form of the induced equivalence on
`𝓂^n/𝓂^(n+1)`. -/
def maximalIdealPowSuccQuotMultiplicativeMapEquivOfIntegerRingEquiv
    (K : Type u) [Field K] [ValuativeRel K]
    (n : Nat) (e : 𝒪[K] ≃+* 𝒪[K]) :
    Multiplicative (MaximalIdealPowSuccQuot K n) ≃*
      Multiplicative (MaximalIdealPowSuccQuot K n) where
  toFun x :=
    Multiplicative.ofAdd
      (maximalIdealPowSuccQuotMapEquivOfIntegerRingEquiv K n e
        (Multiplicative.toAdd x))
  invFun x :=
    Multiplicative.ofAdd
      (maximalIdealPowSuccQuotMapEquivOfIntegerRingEquiv K n e.symm
        (Multiplicative.toAdd x))
  left_inv := by
    intro x
    change Multiplicative.ofAdd
        (maximalIdealPowSuccQuotMapEquivOfIntegerRingEquiv K n e.symm
          (maximalIdealPowSuccQuotMapEquivOfIntegerRingEquiv K n e
            (Multiplicative.toAdd x))) =
      Multiplicative.ofAdd (Multiplicative.toAdd x)
    exact congrArg Multiplicative.ofAdd
      ((maximalIdealPowSuccQuotMapEquivOfIntegerRingEquiv K n e).left_inv
        (Multiplicative.toAdd x))
  right_inv := by
    intro x
    change Multiplicative.ofAdd
        (maximalIdealPowSuccQuotMapEquivOfIntegerRingEquiv K n e
          (maximalIdealPowSuccQuotMapEquivOfIntegerRingEquiv K n e.symm
            (Multiplicative.toAdd x))) =
      Multiplicative.ofAdd (Multiplicative.toAdd x)
    exact congrArg Multiplicative.ofAdd
      ((maximalIdealPowSuccQuotMapEquivOfIntegerRingEquiv K n e).right_inv
        (Multiplicative.toAdd x))
  map_mul' := by
    intro x y
    change Multiplicative.ofAdd
        (maximalIdealPowSuccQuotMapEquivOfIntegerRingEquiv K n e
          (Multiplicative.toAdd (x * y))) =
      Multiplicative.ofAdd
        (maximalIdealPowSuccQuotMapEquivOfIntegerRingEquiv K n e
          (Multiplicative.toAdd x) +
        maximalIdealPowSuccQuotMapEquivOfIntegerRingEquiv K n e
          (Multiplicative.toAdd y))
    rw [show Multiplicative.toAdd (x * y) =
        Multiplicative.toAdd x + Multiplicative.toAdd y from rfl]
    rw [map_add]

end
end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_ResidueUnits
attribute [-instance] _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
/-!
# Residue units

Constructs the quotient of valuation-ring units by first principal units and
identifies it, multiplicatively and additively, with the residue-field units.
-/

set_option autoImplicit false

namespace LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

/-- Eliminate a quotient class through the canonical class map. -/
protected theorem IntegerUnitsModPrincipalUnits.inductionOn
    {K : Type u} [Field K] [ValuativeRel K]
    {motive : IntegerUnitsModPrincipalUnits K → Prop}
    (q : IntegerUnitsModPrincipalUnits K)
    (h : ∀ x : 𝒪[K]ˣ, motive (integerUnitsModPrincipalUnitsMk K x)) :
    motive q := by
  change motive (show 𝒪[K]ˣ ⧸ principalUnits K 1 from q)
  refine QuotientGroup.induction_on q ?_
  intro x
  exact h x

/-- Equality in `𝒪[K]ˣ / U¹`, expressed by a first-principal-unit quotient. -/
theorem IntegerUnitsModPrincipalUnits_mk_eq_mk_iff
    (K : Type u) [Field K] [ValuativeRel K] (x y : 𝒪[K]ˣ) :
    integerUnitsModPrincipalUnitsMk K x =
        integerUnitsModPrincipalUnitsMk K y ↔
      x / y ∈ principalUnits K 1 :=
  by
    change (QuotientGroup.mk x : 𝒪[K]ˣ ⧸ principalUnits K 1) =
      QuotientGroup.mk y ↔ _
    exact QuotientGroup.eq_iff_div_mem (N := principalUnits K 1)

end
end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_ResidueExtension
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
/-!
# Residue extensions

Constructs the maps induced on valuation rings, residue fields, and residue
units by a valued extension, with degree, trace, norm, and Frobenius results.
-/

set_option autoImplicit false

namespace LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

/-- The map between residue fields induced by a valued extension agrees with the residue-field
algebra map. -/
theorem residueFieldMapOfValuationExtension_eq_algebraMap (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] :
    residueFieldMapOfValuationExtension K L = algebraMap 𝓀[K] 𝓀[L] :=
  rfl

/-- The induced map on residue-field unit groups is injective. -/
theorem residueUnitsMapOfValuationExtension_injective (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] :
    Function.Injective (residueUnitsMapOfValuationExtension K L) :=
  Units.map_injective (RingHom.injective (residueFieldMapOfValuationExtension K L))

end
end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_GaloisIntegerRing
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
/-!
# Galois actions on valuation rings

Restricts Galois automorphisms to valuation rings and transports their action
to ideals, ideal-power quotients, principal units, and successive quotients.
-/

set_option autoImplicit false

namespace LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

/-- Actual integral-closure real Galois action on the `n`-th principal-unit
group. -/
def galoisGroupPrincipalUnitsMapEquivOfIsIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (n : Nat) (σ : Gal(L / K)) :
    principalUnits L n ≃* principalUnits L n :=
  principalUnitsMapEquivOfIntegerRingEquiv L n
    (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ)

/-- The induced equivalence on principal units applies the restricted Galois automorphism to the
underlying unit. -/
theorem galoisGroupPrincipalUnitsMapEquivOfIsIntegralClosure_apply
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (n : Nat) (σ : Gal(L / K)) (u : principalUnits L n) :
    ((galoisGroupPrincipalUnitsMapEquivOfIsIntegralClosure K L n σ u :
        principalUnits L n) : 𝒪[L]ˣ) =
      Units.mapEquiv
        (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ).toMulEquiv u.1 :=
  rfl

/-- Integral-closure Galois action on principal units as a group
homomorphism. -/
def galoisGroupPrincipalUnitsMapEquivHomOfIsIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (n : Nat) :
    Gal(L / K) →* (principalUnits L n ≃* principalUnits L n) where
  toFun := galoisGroupPrincipalUnitsMapEquivOfIsIntegralClosure K L n
  map_one' := by
    ext u
    rfl
  map_mul' := by
    intro σ τ
    ext u
    rfl

/-- Actual integral-closure first-order expansion of the real Galois product
attached to a principal-unit representative. -/
theorem galoisGroup_prod_one_add_sub_one_sub_sum_mem_maximalIdeal_pow_succ_of_isIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (n : Nat) (hn : 1 ≤ n) (a : (𝓂[L] ^ n : Ideal 𝒪[L])) :
    (Finset.univ.prod fun σ : Gal(L / K) =>
        1 + galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ (a : 𝒪[L])) - 1 -
      (Finset.univ.sum fun σ : Gal(L / K) =>
        galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ (a : 𝒪[L])) ∈
        (𝓂[L] ^ (n + 1) : Ideal 𝒪[L]) := by
  classical
  refine finset_prod_one_add_sub_one_sub_sum_mem_maximalIdeal_pow_succ L
    (Finset.univ : Finset (Gal(L / K))) n hn
    (fun σ => galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ (a : 𝒪[L])) ?_
  intro σ _
  exact (integerRingEquiv_mem_maximalIdeal_pow L
    (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ) n (a : 𝒪[L])).2 a.2

end
end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_Completion_FiniteProductNormTrace
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Norms and traces on finite dependent products

These algebraic lemmas are the finite-product linear algebra used in
tensor-product norm and trace formulas.  Mathlib has the binary trace formula and the
determinant of a binary product map; the dependent finite-product versions
are recorded here so that the local factors are allowed to have different
field degrees.
-/

noncomputable section

namespace ValuationTheory
namespace Completion

universe u v w

open Module

/-- The algebra norm of an element of a finite dependent product is the
product of its component norms. -/
theorem algebra_norm_pi_apply
    {R : Type u} [CommRing R]
    {ι : Type v} [Fintype ι]
    (A : ι → Type w) [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    [∀ i, Module.Free R (A i)] [∀ i, Module.Finite R (A i)]
    (x : ∀ i, A i) :
    Algebra.norm R x = ∏ i, Algebra.norm R (x i) := by
  classical
  let P : ∀ (ι : Type v) [Fintype ι], Prop :=
    fun ι _ =>
      ∀ (A : ι → Type w) [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
        [∀ i, Module.Free R (A i)] [∀ i, Module.Finite R (A i)]
        (x : ∀ i, A i),
        Algebra.norm R x = ∏ i, Algebra.norm R (x i)
  apply Fintype.induction_empty_option (P := P)
  · intro α β _ e h A _ _ _ _ x
    let : Fintype α := Fintype.ofEquiv β e.symm
    let E := piCongrLeftAlgEquiv (R := R) A e
    let x' : ∀ i : α, A (e i) := fun i => x (e i)
    have hEx : E x' = x := by
      apply E.symm.injective
      rw [E.symm_apply_apply]
      funext i
      rfl
    calc
      Algebra.norm R x = Algebra.norm R (E x') := congrArg _ hEx.symm
      _ = Algebra.norm R x' := Algebra.norm_eq_of_algEquiv E x'
      _ = ∏ i : α, Algebra.norm R (x' i) := h _ _
      _ = ∏ j : β, Algebra.norm R (x j) := by
        exact Fintype.prod_equiv e _ _ (fun i => rfl)
  · intro A _ _ _ _ x
    simp only [Fintype.prod_empty]
    rw [Algebra.norm_apply]
    exact LinearMap.det_eq_one_of_subsingleton _
  · intro α _ h A _ _ _ _ x
    let E := piOptionEquivProdAlgEquiv (R := R) A
    let y : A none × ((i : α) → A (some i)) := E x
    calc
      Algebra.norm R x = Algebra.norm R y :=
        (Algebra.norm_eq_of_algEquiv E x).symm
      _ = Algebra.norm R y.1 * Algebra.norm R y.2 :=
        algebra_norm_prod_apply y
      _ = Algebra.norm R (x none) *
          ∏ i : α, Algebra.norm R (x (some i)) := by
        rw [h]
        rfl
      _ = ∏ i : Option α, Algebra.norm R (x i) := by
        rw [Fintype.prod_option]

end Completion
end ValuationTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_LocalizedCompletionCohomology_CompMulEquiv
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.adicCompletionProperSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The local class-field axiom for decomposition-group blocks

This file supplies the localized-completion input for the class formation. First it
proves change-of-group equivalences for low-degree multiplicative Tate
cohomology. It then applies the canonical algebraic-localization results:
the algebraic localization of a finite Galois extension is finite Galois over
the completed base, and the localization equivalence identifies its Galois group with the
decomposition group.

For a nonarchimedean locally compact base completion, the concrete local
class-field axiom then gives:

* `H⁰` is the actual field-norm quotient;
* `H⁻¹` is trivial;
* the cardinality and Herbrand quotient equal the local degree.
-/

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory
open CyclicCohomology
open CyclicCohomology.ProfiniteCohomology.Herbrand
open scoped TensorProduct

noncomputable section

namespace LocalClassFieldTheory

universe uH uG uA

variable {H : Type uH} {G : Type uG} {A : Type uA}
    [Group H] [Fintype H] [Group G] [Fintype G]
    [CommGroup A] [MulDistribMulAction G A]

theorem tateNorm_compMulEquiv (e : H ≃* G) (a : A) :
    letI := MulDistribMulAction.compHom A e.toMonoidHom
    tateNorm H A a = tateNorm G A a := by
  let := MulDistribMulAction.compHom A e.toMonoidHom
  change (∏ h : H, e h • a) = ∏ g : G, g • a
  exact e.toEquiv.prod_comp fun g ↦ g • a

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_NormContinuity
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xT2Space _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Continuity of finite field norms

This module records the analytic input used by the topological finite local
reciprocity law: on a finite-dimensional normed algebra, the field norm is a
determinant and is therefore continuous.  It also bundles the corresponding
statements for field units and valuation-ring units.
-/

noncomputable section

universe u v

namespace LocalFieldTheory

open scoped ValuativeRel
open _root_.LocalFieldTheory.IsNonarchimedeanLocalField

/-- The field norm of a finite-dimensional normed algebra over a complete
nontrivially normed field is continuous. -/
theorem algebraNorm_continuous_of_finiteDimensional
    (K : Type u) (L : Type v)
    [NontriviallyNormedField K] [NormedField L]
    [Algebra K L] [FiniteDimensional K L] [CompleteSpace K]
    [ContinuousSMul K L] :
    Continuous (Algebra.norm K : L → K) := by
  classical
  let b := Module.Free.chooseBasis K L
  rw [show (Algebra.norm K : L → K) =
      fun x => (Algebra.leftMulMatrix b x).det by
    funext x
    exact Algebra.norm_eq_matrix_det b x]
  apply Continuous.matrix_det
  exact (Algebra.leftMulMatrix b).toLinearMap.continuous_of_finiteDimensional

/-- The field norm induced on unit groups is continuous. -/
theorem normUnits_continuous_of_finiteDimensional
    (K : Type u) (L : Type v)
    [NontriviallyNormedField K] [NormedField L]
    [Algebra K L] [FiniteDimensional K L] [CompleteSpace K]
    [ContinuousSMul K L] :
    Continuous (normUnits K L) := by
  unfold normUnits
  exact Continuous.units_map (Algebra.norm K : L →* K)
    (algebraNorm_continuous_of_finiteDimensional K L)

/-- The canonical inclusion from valuation-ring units to field units is
continuous for the subtype topologies. -/
theorem integerUnitsToFieldUnits_continuous
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] :
    Continuous (integerUnitsToFieldUnits K) := by
  unfold IsNonarchimedeanLocalField.integerUnitsToFieldUnits
  exact Continuous.units_map
    ((algebraMap 𝒪[K] K).toMonoidHom) continuous_subtype_val

end LocalFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_UnitTopology
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The unit subgroup of a nonarchimedean local field

This module identifies the image of valuation-ring units in the field unit
group with the valuation-one sphere and records that this subgroup is open in
the native topology of a nonarchimedean local field.
-/

noncomputable section

universe u

namespace LocalFieldTheory

open scoped ValuativeRel
open _root_.LocalFieldTheory.IsNonarchimedeanLocalField

/-- The image of valuation-ring units in the field unit group. -/
def localBaseUnitSubgroup
    (K : Type u) [Field K] [ValuativeRel K] : Subgroup Kˣ :=
  MonoidHom.range (integerUnitsToFieldUnits K)

end LocalFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Relative_FinitePlaceTensorNorm
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Tensor norm images at actual finite places

This file specializes the local tensor norm calculation to a height-one
prime of a number field.  The canonical comparison

`(K, |·|_v)^∧ ≃ K_v`

identifies the determinant norm on
`(K, |·|_v)^∧ ⊗[K] L` with the determinant norm on the concrete tensor
factor `K_v ⊗[K] L` used by relative ideles.  Consequently its image is
the chosen open local norm subgroup from `LocalNormApproximation`.

The finite component of every global relative-idele norm therefore lies
in that subgroup, and its corresponding local quotient class is one.
-/

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain

noncomputable section

open LocalClassFieldTheory


open AlgebraicNumberTheory.Valuations
open LocalFieldTheory

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- The canonical completion comparison as a `K`-algebra
equivalence. -/
noncomputable def finitePlaceCompletionAlgEquiv
    (v : HeightOneSpectrum (𝓞 K)) :
    (NumberField.HeightOneSpectrum.adicAbv K v).Completion ≃ₐ[K]
      v.adicCompletion K where
  __ := finitePlaceCompletionRingEquiv v
  commutes' x := by
    change
      finitePlaceCompletionRingHom v
          (((WithAbs.equiv
            (NumberField.HeightOneSpectrum.adicAbv K v)).symm x :
              WithAbs
                (NumberField.HeightOneSpectrum.adicAbv K v)) :
            (NumberField.HeightOneSpectrum.adicAbv K v).Completion) =
        algebraMap K (v.adicCompletion K) x
    rw [finitePlaceCompletionRingHom_coe]
    rfl
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_SUnit_Rank
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.DiscreteValuationField.finite_nsmulAddKernel_padicInt_pi _root_.LocalFieldTheory.finite_multiplicative_nthPowerKernel _root_.LocalFieldTheory.finite_nsmulAddKernel_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.KummerTheory.mem_sUnitFiniteKummerRadical_iff _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.SUnitGroup.fullLogAmbient_finite _root_.SUnitGroup.fullLogAmbient_infinite _root_.SUnitGroup.reducedLog_fst_fromNumberFieldUnits _root_.SUnitGroup.reducedLog_snd_fromNumberFieldUnits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Torsion and rank sources for `S`-units

This file supplies the algebraic rank and torsion input for `S`-units.
The finite set `S` contains the finite places; all infinite places are
understood to be present.
-/

noncomputable section

open IsDedekindDomain
open scoped NumberField nonZeroDivisors


variable {K : Type*} [Field K] [NumberField K]

namespace SUnitGroup

/-- Torsion in an `S`-unit group consists exactly of the ordinary roots of
unity. -/
theorem torsion_eq_rootsOfUnity_range
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    CommGroup.torsion (SUnitGroup (K := K) S) =
      Subgroup.map (fromNumberFieldUnits (K := K) S)
        (NumberField.Units.torsion K) := by
  ext x
  constructor
  · intro hx
    have hxfin : IsOfFinOrder x :=
      (CommGroup.mem_torsion (G := SUnitGroup (K := K) S) x).mp hx
    obtain ⟨n, hnpos, hxpow⟩ := hxfin.exists_pow_eq_one
    have hxK : (((x : Kˣ) : K) ^ n) = 1 := by
      simpa using congrArg
        (fun y : SUnitGroup (K := K) S => ((y : Kˣ) : K)) hxpow
    let y : ((∅ : Set (HeightOneSpectrum (𝓞 K))).unit K) :=
      ⟨(x : Kˣ), fun v _ => by
        have hvpow :
            (v.valuation K ((x : Kˣ) : K)) ^ n = 1 := by
          rw [← map_pow, hxK, map_one]
        exact (pow_eq_one_iff_left
          (a := v.valuation K ((x : Kˣ) : K))
          (Nat.ne_of_gt hnpos)).mp hvpow⟩
    let u : (𝓞 K)ˣ := emptyEquivNumberFieldUnits y
    have hufin : IsOfFinOrder u := by
      exact (emptyEquivNumberFieldUnits (K := K)).toMonoidHom.isOfFinOrder
        ((show IsOfFinOrder y from by
          refine isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hnpos, ?_⟩
          ext
          exact hxK))
    refine ⟨u, ?_, ?_⟩
    · exact (CommGroup.mem_torsion (G := (𝓞 K)ˣ) u).2 hufin
    · ext
      change
        (((emptyEquivNumberFieldUnits (K := K)).symm
          (emptyEquivNumberFieldUnits (K := K) y) : Kˣ) : K) =
            ((x : Kˣ) : K)
      rw [MulEquiv.symm_apply_apply]
  · rintro ⟨u, hu, rfl⟩
    exact (CommGroup.mem_torsion
      (G := SUnitGroup (K := K) S)
      (fromNumberFieldUnits (K := K) S u)).2
        ((fromNumberFieldUnits (K := K) S).isOfFinOrder
          ((CommGroup.mem_torsion (G := (𝓞 K)ˣ) u).1 hu))

section Rank

variable (S : Finset (HeightOneSpectrum (𝓞 K)))

/-- The additive group of `S`-units is finitely generated over `ℤ`. -/
theorem moduleFinite :
    Module.Finite ℤ (Additive (SUnitGroup (K := K) S)) := by
  let : Module.Finite ℤ (S → ℤ) := inferInstance
  have : Module.Finite ℤ
      (LinearMap.range (divisorLinearMap (K := K) S)) :=
    Module.Finite.of_fg
      (IsNoetherian.noetherian
        (LinearMap.range (divisorLinearMap (K := K) S)))
  rw [Module.finite_def]
  refine Submodule.fg_of_fg_map_of_fg_inf_ker
    (divisorLinearMap (K := K) S) ?_ ?_
  · rw [Submodule.map_top]
    exact IsNoetherian.noetherian
      (LinearMap.range (divisorLinearMap (K := K) S))
  · rw [inf_of_le_right le_top,
      ← range_fromNumberFieldUnitsLinearMap_eq_ker_divisorLinearMap
        (K := K) S]
    exact Submodule.fg_range
      (fromNumberFieldUnitsLinearMap (K := K) S)

end Rank

end SUnitGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_SUnit_LogLattice
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.DiscreteValuationField.finite_nsmulAddKernel_padicInt_pi _root_.LocalFieldTheory.finite_multiplicative_nthPowerKernel _root_.LocalFieldTheory.finite_nsmulAddKernel_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xT2Space _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.KummerTheory.mem_sUnitFiniteKummerRadical_iff _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The logarithmic lattice of `S`-units

This file develops the logarithmic lattice of `S`-units. The
finite set `S` consists of the finite places; all infinite places are
understood to belong to the set of places used in the theorem.

The first construction uses the usual reduced archimedean logarithmic
space (one infinite coordinate is omitted) together with the integral
principal-divisor coordinates at `S`.  Its image is proved directly to
be a complete `ℤ`-lattice.  The normalized, all-place logarithmic map
and its coordinate-sum-zero hyperplane are constructed below from this
lattice.
-/

noncomputable section

open IsDedekindDomain Module
open scoped Classical NumberField nonZeroDivisors


variable {K : Type*} [Field K] [NumberField K]

namespace SUnitGroup

variable (S : Finset (HeightOneSpectrum (𝓞 K)))

/-- The normalized finite absolute value is the norm of the prime
raised to minus the corresponding principal-divisor exponent. -/
theorem adicAbv_eq_zpow_neg_divisorCoordinate
    (x : SUnitGroup (K := K) S) (v : S) :
    NumberField.HeightOneSpectrum.adicAbv K
        (v : HeightOneSpectrum (𝓞 K)) (((x : Kˣ) : K)) =
      (Ideal.absNorm
        (v : HeightOneSpectrum (𝓞 K)).asIdeal : ℝ) ^
          (-divisorCoordinate (K := K) S x v) := by
  rw [NumberField.HeightOneSpectrum.adicAbv_def,
    valuation_eq_exp_neg_count (K := K)]
  rw [WithZeroMulInt.toNNReal_neg_apply]
  · norm_cast
  · simp

/-- The logarithm of a normalized finite absolute value is the divisor
coordinate times `-log Nv`. -/
theorem log_adicAbv_eq_neg_divisorCoordinate_mul_log_absNorm
    (x : SUnitGroup (K := K) S) (v : S) :
    Real.log
        (NumberField.HeightOneSpectrum.adicAbv K
          (v : HeightOneSpectrum (𝓞 K)) (((x : Kˣ) : K))) =
      -(divisorCoordinate (K := K) S x v : ℝ) *
        Real.log
          (Ideal.absNorm
            (v : HeightOneSpectrum (𝓞 K)).asIdeal : ℝ) := by
  rw [adicAbv_eq_zpow_neg_divisorCoordinate (K := K) S,
    Real.log_zpow]
  push_cast
  ring

/-- The `ℤ`-linear form of the reduced logarithmic embedding. -/
noncomputable def reducedLogLinearMap :
    Additive (SUnitGroup (K := K) S) →ₗ[ℤ]
      ReducedLogSpace (K := K) S :=
  (reducedLog (K := K) S).toIntLinearMap

/-- The reduced `S`-unit lattice. -/
noncomputable def reducedLogLattice :
    Submodule ℤ (ReducedLogSpace (K := K) S) :=
  LinearMap.range (reducedLogLinearMap (K := K) S)

section FullLogarithmicSpace

/-- Sum of all logarithmic coordinates. -/
noncomputable def coordinateSum :
    FullLogSpace (K := K) S →ₗ[ℝ] ℝ where
  toFun z := ∑ p, z p
  map_add' x y := by
    simp [Finset.sum_add_distrib]
  map_smul' c x := by
    change
      (∑ p : LogPlace (K := K) S, c * x p) =
        c * ∑ p : LogPlace (K := K) S, x p
    rw [Finset.mul_sum]

/-- The coordinate-sum-zero hyperplane in the full logarithmic
space. -/
abbrev LogHyperplane :=
  LinearMap.ker (coordinateSum (K := K) S)

/-- For an `S`-unit the finite part of the global product formula is
the product over the finite places in `S`. -/
theorem finprod_finitePlace_eq_prod_adicAbv
    (x : SUnitGroup (K := K) S) :
    (∏ᶠ w : NumberField.FinitePlace K,
        w (((x : Kˣ) : K))) =
      ∏ v : S,
        NumberField.HeightOneSpectrum.adicAbv K
          (v : HeightOneSpectrum (𝓞 K))
          (((x : Kˣ) : K)) := by
  rw [← finprod_comp_equiv
    NumberField.FinitePlace.equivHeightOneSpectrum.symm]
  simp_rw
    [NumberField.FinitePlace.equivHeightOneSpectrum_symm_apply,
      NumberField.FinitePlace.norm_embedding,
      NumberField.HeightOneSpectrum.adicAbv_def]
  rw [finprod_eq_prod_of_mulSupport_subset
    (s := S)]
  · exact
      (Finset.prod_coe_sort
        (s := S)
        (f := fun v : HeightOneSpectrum (𝓞 K) =>
          (NumberField.HeightOneSpectrum.adicAbv K v
            (((x : Kˣ) : K))))).symm
  · intro v hv
    by_contra hnot
    apply hv
    simp [x.property v hnot]

/-- Logarithmic form of the product formula, restricted to the places
of the `S`-unit theorem. -/
theorem sum_log_absoluteValues_eq_zero
    (x : SUnitGroup (K := K) S) :
    (∑ w : NumberField.InfinitePlace K,
        w.mult * Real.log (w (((x : Kˣ) : K)))) +
      ∑ v : S,
        Real.log
          (NumberField.HeightOneSpectrum.adicAbv K
            (v : HeightOneSpectrum (𝓞 K))
            (((x : Kˣ) : K))) = 0 := by
  have hx0 : (((x : Kˣ) : K)) ≠ 0 :=
    Units.ne_zero (x : Kˣ)
  have hprod := NumberField.prod_abs_eq_one hx0
  rw [finprod_finitePlace_eq_prod_adicAbv
    (K := K) S x] at hprod
  calc
    (∑ w : NumberField.InfinitePlace K,
        w.mult * Real.log (w (((x : Kˣ) : K)))) +
      ∑ v : S,
        Real.log
          (NumberField.HeightOneSpectrum.adicAbv K
            (v : HeightOneSpectrum (𝓞 K))
            (((x : Kˣ) : K))) =
        Real.log
            (∏ w : NumberField.InfinitePlace K,
              w (((x : Kˣ) : K)) ^ w.mult) +
          Real.log
            (∏ v : S,
              NumberField.HeightOneSpectrum.adicAbv K
                (v : HeightOneSpectrum (𝓞 K))
                (((x : Kˣ) : K))) := by
      congr 1
      · rw [Real.log_prod]
        · apply Finset.sum_congr rfl
          intro w _
          rw [Real.log_pow]
        · intro w _
          exact pow_ne_zero _ ((w.pos_iff.mpr hx0).ne')
      · rw [Real.log_prod]
        intro v _
        exact
          ((NumberField.HeightOneSpectrum.adicAbv K
            (v : HeightOneSpectrum (𝓞 K))).pos_iff.mpr hx0).ne'
    _ = Real.log
        ((∏ w : NumberField.InfinitePlace K,
            w (((x : Kˣ) : K)) ^ w.mult) *
          ∏ v : S,
            NumberField.HeightOneSpectrum.adicAbv K
              (v : HeightOneSpectrum (𝓞 K))
              (((x : Kˣ) : K))) := by
      rw [Real.log_mul]
      · exact Finset.prod_ne_zero_iff.mpr fun w _ ↦
          pow_ne_zero _ ((w.pos_iff.mpr hx0).ne')
      · exact Finset.prod_ne_zero_iff.mpr fun v _ ↦
          ((NumberField.HeightOneSpectrum.adicAbv K
            (v : HeightOneSpectrum (𝓞 K))).pos_iff.mpr hx0).ne'
    _ = 0 := by
      rw [hprod, Real.log_one]

theorem fullLogAmbient_mem_logHyperplane
    (x : Additive (SUnitGroup (K := K) S)) :
    fullLogAmbient (K := K) S x ∈
      LogHyperplane (K := K) S := by
  apply LinearMap.mem_ker.mpr
  change
    ∑ p : LogPlace (K := K) S,
      fullLogAmbient (K := K) S x p = 0
  rw [Fintype.sum_sum_type]
  exact
    sum_log_absoluteValues_eq_zero (K := K) S
      (Additive.toMul x)

/-- The normalized all-place logarithmic map with codomain restricted
to the coordinate-sum-zero hyperplane. -/
noncomputable def fullLog :
    Additive (SUnitGroup (K := K) S) →+
      LogHyperplane (K := K) S :=
  (fullLogAmbient (K := K) S).codRestrict
    (LogHyperplane (K := K) S)
    (fullLogAmbient_mem_logHyperplane (K := K) S)

/-- Forget the distinguished infinite coordinate and divide the finite
logarithmic coordinates by their nonzero normalizing weights. -/
noncomputable def forgetDistinguishedLog :
    LogHyperplane (K := K) S →ₗ[ℝ]
      ReducedLogSpace (K := K) S where
  toFun z :=
    (fun w => (z : FullLogSpace (K := K) S) (Sum.inl w.1),
      fun v =>
        (z : FullLogSpace (K := K) S) (Sum.inr v) /
          finiteLogWeight (K := K) S v)
  map_add' x y := by
    apply Prod.ext
    · ext w
      rfl
    · ext v
      simp [add_div]
  map_smul' c x := by
    apply Prod.ext
    · ext w
      rfl
    · ext v
      change
        (c *
            (x : FullLogSpace (K := K) S) (Sum.inr v)) /
            finiteLogWeight (K := K) S v =
          c *
            ((x : FullLogSpace (K := K) S) (Sum.inr v) /
              finiteLogWeight (K := K) S v)
      ring

/-- Forgetting the distinguished logarithmic coordinate is injective on
the product-formula hyperplane. -/
theorem forgetDistinguishedLog_injective :
    Function.Injective (forgetDistinguishedLog (K := K) S) := by
  intro x y hxy
  have hinf :
      ∀ w :
          {w : NumberField.InfinitePlace K //
            w ≠
              NumberField.Units.dirichletUnitTheorem.w₀},
        (x : FullLogSpace (K := K) S) (Sum.inl w.1) =
          (y : FullLogSpace (K := K) S) (Sum.inl w.1) := by
    intro w
    exact congrFun (congrArg Prod.fst hxy) w
  have hfin :
      ∀ v : S,
        (x : FullLogSpace (K := K) S) (Sum.inr v) =
          (y : FullLogSpace (K := K) S) (Sum.inr v) := by
    intro v
    have hv := congrFun (congrArg Prod.snd hxy) v
    exact
      (div_left_inj'
        (finiteLogWeight_ne_zero (K := K) S v)).mp hv
  apply Subtype.ext
  funext p
  cases p with
  | inr v => exact hfin v
  | inl w =>
      by_cases hw :
          w =
            NumberField.Units.dirichletUnitTheorem.w₀
      · subst w
        have hxsum :
            (x : FullLogSpace (K := K) S)
                (Sum.inl
                  NumberField.Units.dirichletUnitTheorem.w₀) +
                (∑ v :
                    {w : NumberField.InfinitePlace K //
                      w ≠
                        NumberField.Units.dirichletUnitTheorem.w₀},
                  (x : FullLogSpace (K := K) S)
                    (Sum.inl v.1)) +
              ∑ v : S,
                (x : FullLogSpace (K := K) S)
                  (Sum.inr v) = 0 := by
          have hxker := LinearMap.mem_ker.mp x.property
          change
            ∑ p : LogPlace (K := K) S,
              (x : FullLogSpace (K := K) S) p = 0 at hxker
          rw [Fintype.sum_sum_type,
            Fintype.sum_eq_add_sum_subtype_ne _
              NumberField.Units.dirichletUnitTheorem.w₀] at hxker
          exact hxker
        have hysum :
            (y : FullLogSpace (K := K) S)
                (Sum.inl
                  NumberField.Units.dirichletUnitTheorem.w₀) +
                (∑ v :
                    {w : NumberField.InfinitePlace K //
                      w ≠
                        NumberField.Units.dirichletUnitTheorem.w₀},
                  (y : FullLogSpace (K := K) S)
                    (Sum.inl v.1)) +
              ∑ v : S,
                (y : FullLogSpace (K := K) S)
                  (Sum.inr v) = 0 := by
          have hyker := LinearMap.mem_ker.mp y.property
          change
            ∑ p : LogPlace (K := K) S,
              (y : FullLogSpace (K := K) S) p = 0 at hyker
          rw [Fintype.sum_sum_type,
            Fintype.sum_eq_add_sum_subtype_ne _
              NumberField.Units.dirichletUnitTheorem.w₀] at hyker
          exact hyker
        have hsuminf :
            (∑ v :
                {w : NumberField.InfinitePlace K //
                  w ≠
                    NumberField.Units.dirichletUnitTheorem.w₀},
              (x : FullLogSpace (K := K) S)
                (Sum.inl v.1)) =
              ∑ v :
                {w : NumberField.InfinitePlace K //
                  w ≠
                    NumberField.Units.dirichletUnitTheorem.w₀},
                (y : FullLogSpace (K := K) S)
                  (Sum.inl v.1) := by
          apply Finset.sum_congr rfl
          intro v _
          exact hinf v
        have hsumfin :
            (∑ v : S,
              (x : FullLogSpace (K := K) S)
                (Sum.inr v)) =
              ∑ v : S,
                (y : FullLogSpace (K := K) S)
                  (Sum.inr v) := by
          apply Finset.sum_congr rfl
          intro v _
          exact hfin v
        linarith
      · exact hinf ⟨w, hw⟩

/-- Every reduced logarithmic vector has a lift to the product-formula
hyperplane. -/
theorem forgetDistinguishedLog_surjective :
    Function.Surjective (forgetDistinguishedLog (K := K) S) := by
  intro z
  let completed : FullLogSpace (K := K) S :=
    fun p =>
      match p with
      | Sum.inl w =>
          if hw :
              w =
                NumberField.Units.dirichletUnitTheorem.w₀ then
            -(∑ v :
                {w : NumberField.InfinitePlace K //
                  w ≠
                    NumberField.Units.dirichletUnitTheorem.w₀},
                z.1 v) -
              ∑ v : S,
                finiteLogWeight (K := K) S v * z.2 v
          else
            z.1 ⟨w, hw⟩
      | Sum.inr v =>
          finiteLogWeight (K := K) S v * z.2 v
  have hcompleted :
      completed ∈ LogHyperplane (K := K) S := by
    apply LinearMap.mem_ker.mpr
    change
      ∑ p : LogPlace (K := K) S, completed p = 0
    rw [Fintype.sum_sum_type,
      Fintype.sum_eq_add_sum_subtype_ne _
        NumberField.Units.dirichletUnitTheorem.w₀]
    have hw0 :
        completed
            (Sum.inl
              NumberField.Units.dirichletUnitTheorem.w₀) =
          -(∑ v :
              {w : NumberField.InfinitePlace K //
                w ≠
                  NumberField.Units.dirichletUnitTheorem.w₀},
              z.1 v) -
            ∑ v : S,
              finiteLogWeight (K := K) S v * z.2 v := by
      simp [completed]
    have hinf :
        (∑ v :
            {w : NumberField.InfinitePlace K //
              w ≠
                NumberField.Units.dirichletUnitTheorem.w₀},
          completed (Sum.inl v.1)) =
          ∑ v :
            {w : NumberField.InfinitePlace K //
              w ≠
                NumberField.Units.dirichletUnitTheorem.w₀},
            z.1 v := by
      apply Finset.sum_congr rfl
      intro v _
      simp [completed, v.property]
    have hfin :
        (∑ v : S, completed (Sum.inr v)) =
          ∑ v : S,
            finiteLogWeight (K := K) S v * z.2 v := by
      rfl
    rw [hw0, hinf, hfin]
    ring
  let y : LogHyperplane (K := K) S :=
    ⟨completed, hcompleted⟩
  refine ⟨y, ?_⟩
  apply Prod.ext
  · ext w
    simp [forgetDistinguishedLog, y, completed, w.property]
  · ext v
    simp [forgetDistinguishedLog, y, completed,
      finiteLogWeight_ne_zero (K := K) S v]

/-- Removing the distinguished infinite coordinate and rescaling the
finite coordinates is a real linear equivalence. -/
noncomputable def logHyperplaneEquivReduced :
    LogHyperplane (K := K) S ≃ₗ[ℝ]
      ReducedLogSpace (K := K) S :=
  LinearEquiv.ofBijective
    (forgetDistinguishedLog (K := K) S)
    ⟨forgetDistinguishedLog_injective (K := K) S,
      forgetDistinguishedLog_surjective (K := K) S⟩

/-- Under the coordinate equivalence, the normalized all-place
logarithm is exactly the reduced logarithm. -/
theorem logHyperplaneEquivReduced_fullLog
    (x : Additive (SUnitGroup (K := K) S)) :
    logHyperplaneEquivReduced (K := K) S
        (fullLog (K := K) S x) =
      reducedLog (K := K) S x := by
  apply Prod.ext
  · ext w
    rfl
  · ext v
    have hlog :
        Real.log
          (Ideal.absNorm
            (v : HeightOneSpectrum (𝓞 K)).asIdeal : ℝ) ≠ 0 :=
      neg_ne_zero.mp
        (finiteLogWeight_ne_zero (K := K) S v)
    change
      Real.log
          (NumberField.HeightOneSpectrum.adicAbv K
            (v : HeightOneSpectrum (𝓞 K))
            (((Additive.toMul x :
              SUnitGroup (K := K) S) : Kˣ) : K)) /
          finiteLogWeight (K := K) S v =
        (divisorCoordinate (K := K) S
          (Additive.toMul x) v : ℝ)
    rw [log_adicAbv_eq_neg_divisorCoordinate_mul_log_absNorm
      (K := K) S]
    dsimp [finiteLogWeight]
    field_simp [hlog]

/-- The coordinate equivalence as a continuous linear equivalence
(both spaces are finite-dimensional). -/
noncomputable def logHyperplaneContinuousEquivReduced :
    LogHyperplane (K := K) S ≃L[ℝ]
      ReducedLogSpace (K := K) S :=
  (logHyperplaneEquivReduced (K := K) S).toContinuousLinearEquiv

/-- The complete lattice in the coordinate-sum-zero hyperplane. -/
noncomputable def fullLogLattice :
    Submodule ℤ (LogHyperplane (K := K) S) :=
  ZLattice.comap ℝ
    (reducedLogLattice (K := K) S)
    (logHyperplaneContinuousEquivReduced
      (K := K) S).toLinearMap

/-- The complete lattice just defined is exactly the image of the
normalized all-place logarithmic map. -/
theorem fullLogLattice_eq_range :
    fullLogLattice (K := K) S =
      LinearMap.range
        (fullLog (K := K) S).toIntLinearMap := by
  ext z
  constructor
  · intro hz
    change
      logHyperplaneEquivReduced (K := K) S z ∈
        reducedLogLattice (K := K) S at hz
    obtain ⟨x, hx⟩ := hz
    refine ⟨x, ?_⟩
    apply (logHyperplaneEquivReduced (K := K) S).injective
    change
      logHyperplaneEquivReduced (K := K) S
          (fullLog (K := K) S x) =
        logHyperplaneEquivReduced (K := K) S z
    rw [logHyperplaneEquivReduced_fullLog]
    exact hx
  · rintro ⟨x, rfl⟩
    change
      logHyperplaneEquivReduced (K := K) S
          (fullLog (K := K) S x) ∈
        reducedLogLattice (K := K) S
    rw [logHyperplaneEquivReduced_fullLog]
    exact LinearMap.mem_range_self _ x

end FullLogarithmicSpace

section Decomposition

local instance instModuleFinite_additiveSUnit :
    Module.Finite ℤ (Additive (SUnitGroup (K := K) S)) :=
  moduleFinite (K := K) S

end Decomposition

end SUnitGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_SUnit_GaloisAction
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Galois actions on `S`-units and their logarithmic lattice

This file supplies the equivariant input for the `S`-unit calculation. A Galois
automorphism acts on finite places through its restriction to the ring of
integers, on infinite places by precomposition, and on field units in the
usual way.  For a stable finite set of finite places these actions restrict
to the actual `S`-unit group.
-/

open scoped BigOperators Classical NumberField nonZeroDivisors
open IsDedekindDomain Module
open CyclicCohomology.ProfiniteCohomology.Herbrand
open CyclicCohomology

noncomputable section

variable
    (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]

omit [NumberField K] [NumberField L] in
/-- Archimedean multiplicities are constant on Galois orbits. -/
@[simp]
theorem infinitePlace_mult_smul
    (σ : L ≃ₐ[K] L)
    (w : NumberField.InfinitePlace L) :
    (σ • w).mult = w.mult := by
  unfold NumberField.InfinitePlace.mult
  rw [NumberField.InfinitePlace.isReal_smul_iff]
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_Unramified_PrincipalUnits_NormSide
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalClassFieldTheory.galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure_smul _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false
/-! Provides the public declarations in the `LocalClassFieldTheory.Finite.Unramified.PrincipalUnits.NormSide` Lean module. -/

noncomputable section

universe u

namespace LocalClassFieldTheory

open scoped ValuativeRel
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

/-- The product of actual integral-closure Galois conjugates preserves every
principal-unit level. -/
theorem galoisGroup_prod_mem_principalUnits_of_isIntegralClosure (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (n : Nat) (u : 𝒪[L]ˣ) (hu : u ∈ principalUnits L n) :
    Finset.univ.prod (fun σ : Gal(L / K) =>
      Units.mapEquiv
        (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ).toMulEquiv u) ∈
        principalUnits L n := by
  simpa using (Subgroup.prod_mem (principalUnits L n) (t := Finset.univ)
    (f := fun σ : Gal(L / K) =>
      Units.mapEquiv
        (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ).toMulEquiv u)
    (fun σ _ =>
      principalUnits_integerRingEquiv_mem_self L n
        (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ) u hu))

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Cohomology_SupportedBridge
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable
attribute [-simp] _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# A sufficiently large unramified support for the idele-class calculation

This file constructs the finite set used in the idele-class Herbrand calculation.  It
contains the contractions of a sufficiently large set of places of `L`
and every finite place of `K` at which some place of `L` ramifies.

It also compares the concrete tensor-coordinate supported subgroup of
relative ideles with the ordinary supported idele subgroup of `L`.
-/

open scoped Classical NumberField TensorProduct
open NumberField IsDedekindDomain

noncomputable section


variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- The finite base places at which at least one extension prime is
ramified. -/
noncomputable def ramifiedBaseFinitePlaces :
    Finset (HeightOneSpectrum (𝓞 K)) :=
  (AlgebraicNumberTheory.Ramification.finite_ramified_base_heightOne_primes
      (𝓞 K) (𝓞 L)).toFinset

omit [FiniteDimensional K L] [IsGalois K L] in
@[simp]
theorem mem_ramifiedBaseFinitePlaces_iff
    (v : HeightOneSpectrum (𝓞 K)) :
    v ∈ ramifiedBaseFinitePlaces (K := K) (L := L) ↔
      ∃ W : HeightOneSpectrum (𝓞 L),
        W.asIdeal.LiesOver v.asIdeal ∧
          ¬ Algebra.IsUnramifiedAt (𝓞 K) W.asIdeal := by
  simp [ramifiedBaseFinitePlaces]
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_FinitePlaceArtin_NormRestriction
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.gLocallyCompact _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Norm--restriction for finite-place Artin homomorphisms

This module proves norm--restriction naturality for finite-place Artin maps in an actual square of number fields and their chosen completed local extensions.
-/

open scoped Classical IsMulCommutative NNReal NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]

section FinitePlaceNormRestrictionInstances

variable {K' L' : Type}
    [Field K'] [NumberField K']
    [Field L'] [NumberField L']
    [Algebra K K'] [Algebra K' L'] [Algebra K L']
    [IsScalarTower K K' L']
    [Algebra L L'] [IsScalarTower K L L']
    [IsAbelianGalois K' L']
    (v : HeightOneSpectrum (𝓞 K))
    (W : HeightOneSpectrum (𝓞 K'))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (w' : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K' W) L')

local notation "vKₙ" =>
  NumberField.HeightOneSpectrum.adicAbv K v
local notation "vKₙ'" =>
  NumberField.HeightOneSpectrum.adicAbv K' W
local notation "Cₙ" =>
  finitePlaceNormCompletion K v
local notation "Dₙ" =>
  finitePlaceNormCompletion K' W

local instance finitePlaceNormLowerExtensionAlgebra_r0b09d5_1 :
    Algebra K w.1.Completion :=
  AbsoluteValue.extensionCompletionAlgebra
    (K := K) w.1
local instance finitePlaceNormLowerCompletionAlgebra_r0b09d5_1 :
    Algebra Cₙ w.1.Completion :=
  AbsoluteValue.completionAlgebra vKₙ w.1 w.2
local instance finitePlaceNormUpperExtensionAlgebra_r0b09d5_1 :
    Algebra K' w'.1.Completion :=
  AbsoluteValue.extensionCompletionAlgebra
    (K := K') w'.1
local instance finitePlaceNormUpperCompletionAlgebra_r0b09d5_1 :
    Algebra Dₙ w'.1.Completion :=
  AbsoluteValue.completionAlgebra vKₙ' w'.1 w'.2
local instance finitePlaceNormLowerNontriviallyNormedField_r0b09d5_1 :
    NontriviallyNormedField Cₙ :=
  absoluteValueExtension_completionNontriviallyNormedField
    vKₙ (RayClass.adicAbv_isNontrivial v)
local instance finitePlaceNormLowerLocallyCompactSpace_r0b09d5_1 :
    LocallyCompactSpace Cₙ :=
  AbsoluteValue.Completion.locallyCompactSpace
    (finitePlaceCompletionBaseMap_isometry v)
local instance finitePlaceNormUpperNontriviallyNormedField :
    NontriviallyNormedField Dₙ :=
  absoluteValueExtension_completionNontriviallyNormedField
    vKₙ' (RayClass.adicAbv_isNontrivial W)

local instance finitePlaceNormUpperLocallyCompactSpace :
    LocallyCompactSpace Dₙ :=
  AbsoluteValue.Completion.locallyCompactSpace
    (finitePlaceCompletionBaseMap_isometry W)

end FinitePlaceNormRestrictionInstances

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.KummerTheory_Concrete_CyclotomicPrimeBaseChange
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Prime cyclotomic base change

This file constructs the roots-of-unity base change for a prime-degree
extension.  If `L / K` has prime degree `p`, the
cyclotomic extension `K(μ_p) / K` has degree strictly smaller than `p`.
The two degrees are therefore coprime, and

`K(μ_p) ⊗[K] L`

is an actual field, Galois of degree `p` over `K(μ_p)`.
-/

open scoped NumberField TensorProduct
open NumberField

noncomputable section

namespace KummerTheory

universe u

variable
    (K L : Type u)
    [Field K] [NumberField K]
    [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L]

noncomputable instance primeCyclotomicBaseFiniteDimensional
    (p : ℕ) [NeZero p] :
    FiniteDimensional K (PrimeCyclotomicBase K p) :=
  IsCyclotomicExtension.finiteDimensional
    {p} K (PrimeCyclotomicBase K p)

noncomputable instance primeCyclotomicBaseIsGalois
    (p : ℕ) [NeZero p] :
    IsGalois K (PrimeCyclotomicBase K p) :=
  IsCyclotomicExtension.isGalois
    {p} K (PrimeCyclotomicBase K p)

noncomputable instance primeCyclotomicBaseNumberField
    (p : ℕ) [NeZero p] :
    NumberField (PrimeCyclotomicBase K p) :=
  NumberField.of_module_finite K
    (PrimeCyclotomicBase K p)

end KummerTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.Kummer_Concrete_FiniteDualSeparation
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# finite Kummer dual separation

This file supplies the first missing finite-duality source for the full
subgroup/extension correspondence in the Kummer correspondence.  Characters of a finite
abelian group killed by `n` can be chosen with values in `μₙ`, and these
characters separate points.  Consequently, the transpose of a character
equivalence `R ≃ Hom(G, μₙ)` is injective.

No lattice correspondence or infinite Kummer endpoint is asserted here.
-/

noncomputable section

namespace KummerTheory

/-- Algebraic extension maps carry `μₙ(K)` injectively into `μₙ(L)`. -/
def nthRootsSubgroupMap
    (K L : Type*) [Field K] [Field L] [Algebra K L] (n : ℕ) :
    nthRootsSubgroup K n →* nthRootsSubgroup L n where
  toFun z :=
    ⟨Units.map (algebraMap K L).toMonoidHom z.1, by
      calc
        Units.map (algebraMap K L).toMonoidHom z.1 ^ n =
            Units.map (algebraMap K L).toMonoidHom (z.1 ^ n) :=
          (map_pow (Units.map (algebraMap K L).toMonoidHom) z.1 n).symm
        _ = 1 := by rw [z.2, map_one]⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (Units.map (algebraMap K L).toMonoidHom)
  map_mul' := by
    intro z w
    apply Subtype.ext
    exact map_mul (Units.map (algebraMap K L).toMonoidHom) z.1 w.1

/-- The canonical map from roots of unity into the `n`th-roots subgroup is injective. -/
theorem nthRootsSubgroupMap_injective
    (K L : Type*) [Field K] [Field L] [Algebra K L] (n : ℕ) :
    Function.Injective (nthRootsSubgroupMap K L n) := by
  intro z w h
  apply Subtype.ext
  apply (Units.map_injective (f := (algebraMap K L).toMonoidHom)
    (algebraMap K L).injective)
  exact congrArg Subtype.val h

/-- If `K` contains a primitive `n`-th root, extension of scalars identifies
the `n`-th roots of unity in `K` and in every extension field `L`. -/
def nthRootsSubgroupEquivOfPrimitiveRoots
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    nthRootsSubgroup K (n : ℕ) ≃* nthRootsSubgroup L (n : ℕ) :=
  MulEquiv.ofBijective (nthRootsSubgroupMap K L (n : ℕ))
    ⟨nthRootsSubgroupMap_injective K L (n : ℕ), by
      intro u
      obtain ⟨zeta, hzeta⟩ :=
        nthRootsOfUnityInBase_of_primitiveRoots
          (K := K) (L := L) n hmu u.1 u.2
      have hzeta_pow : zeta ^ (n : ℕ) = 1 := by
        apply (Units.map_injective (f := (algebraMap K L).toMonoidHom)
          (algebraMap K L).injective)
        calc
          Units.map (algebraMap K L).toMonoidHom (zeta ^ (n : ℕ)) =
              (Units.map (algebraMap K L).toMonoidHom zeta) ^ (n : ℕ) :=
            map_pow (Units.map (algebraMap K L).toMonoidHom) zeta (n : ℕ)
          _ = u.1 ^ (n : ℕ) := by rw [hzeta]
          _ = 1 := u.2
          _ = Units.map (algebraMap K L).toMonoidHom 1 :=
            (map_one (Units.map (algebraMap K L).toMonoidHom)).symm
      exact ⟨⟨zeta, hzeta_pow⟩, Subtype.ext hzeta⟩⟩

/-- For a group killed by `n`, restricting a `Kˣ`-valued character to
`μₙ(K)` loses no information. -/
def unitCharactersEquivNthRoots
    {G K : Type*} [CommGroup G] [Field K]
    (n : ℕ+) (hexponent : ∀ g : G, g ^ (n : ℕ) = 1) :
    (G →* Kˣ) ≃* (G →* nthRootsSubgroup K (n : ℕ)) where
  toFun := characterToNthRoots n hexponent
  invFun χ := (nthRootsSubgroup K (n : ℕ)).subtype.comp χ
  left_inv φ := by
    apply MonoidHom.ext
    intro g
    rfl
  right_inv χ := by
    apply MonoidHom.ext
    intro g
    apply Subtype.ext
    rfl
  map_mul' φ ψ := by
    apply MonoidHom.ext
    intro g
    apply Subtype.ext
    rfl

/-- Finite abelian duality with the character codomain restricted to the
actual `n`-th roots of unity in an extension field. -/
theorem finiteNthRootsCharacterDuality
    {G K L : Type*} [CommGroup G] [Finite G]
    [Field K] [Field L] [Algebra K L]
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hexponent : ∀ g : G, g ^ (n : ℕ) = 1) :
    Nonempty ((G →* nthRootsSubgroup L (n : ℕ)) ≃* G) := by
  let rootsEquiv := nthRootsSubgroupEquivOfPrimitiveRoots K L n hmu
  let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  obtain ⟨zeta, hzeta⟩ := hmu
  have hzeta_primitive : IsPrimitiveRoot zeta (n : ℕ) :=
    (mem_primitiveRoots n.pos).1 hzeta
  let : HasEnoughRootsOfUnity K (n : ℕ) :=
    { prim := ⟨zeta, hzeta_primitive⟩
      cyc := rootsOfUnity.isCyclic K (n : ℕ) }
  have hexponent_dvd : Monoid.exponent G ∣ (n : ℕ) :=
    Monoid.exponent_dvd_of_forall_pow_eq_one (fun g => by
      simpa only using hexponent g)
  let : HasEnoughRootsOfUnity K (Monoid.exponent G) :=
    HasEnoughRootsOfUnity.of_dvd K hexponent_dvd
  obtain ⟨dual⟩ := CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity G K
  exact ⟨(rootsEquiv.monoidHomCongrRight (M := G)).symm |>.trans
    (unitCharactersEquivNthRoots n hexponent).symm |>.trans dual⟩

end KummerTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.Kummer_Concrete_InfiniteContinuity
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# continuity of Kummer characters for infinite extensions

For an infinite Galois extension `Ω/K`, a Kummer character attached to a
chosen root `β` is already determined on the finite Galois normal closure of
`K(β)`.  Equivalently, its kernel contains the fixing subgroup of that finite
Galois intermediate field.  This makes the kernel open in the Krull topology
and proves continuity into the discrete group of `n`-th roots of unity.

The final construction descends these continuous characters through the
ambient-power quotient `Δ / (Δ ∩ Kˣⁿ)`.  No surjectivity or lattice correspondence is
asserted here.
-/

noncomputable section

namespace KummerTheory

open scoped Topology
open Filter

namespace DiscreteNthRootsSubgroup

variable (L : Type*) [Field L] (n : ℕ)

/-- The discrete copy of the roots-of-unity subgroup retains its commutative group structure. -/
instance instCommGroupSubtypeUnitsMemSubgroup : CommGroup (DiscreteNthRootsSubgroup L n) :=
  inferInstanceAs (CommGroup (nthRootsSubgroup L n))

/-- The discrete roots-of-unity copy is equipped with the bottom topology. -/
instance instTopologicalSpaceSubtypeUnitsMemSubgroup : TopologicalSpace (DiscreteNthRootsSubgroup L n) := ⊥

/-- The bottom topology makes the roots-of-unity copy discrete. -/
instance instDiscreteTopologySubtypeUnitsMemSubgroup : DiscreteTopology (DiscreteNthRootsSubgroup L n) :=
  discreteTopology_bot _

end DiscreteNthRootsSubgroup

end KummerTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.Kummer_Concrete_RestrictedFinite
attribute [-instance] _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.KummerTheory.DiscreteNthRootsSubgroup.instCommGroupSubtypeUnitsMemSubgroup _root_.KummerTheory.finiteSupportKummerQuotient_commGroupInstance _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.KummerTheory.finiteSupportKummerQuotientLift_mk _root_.KummerTheory.finiteSupportKummerQuotientMk_eq_iff _root_.KummerTheory.finiteSupportKummerQuotientMk_eq_one_iff _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# finite restricted Kummer pairing

Let `Delta ≤ Kˣ` contain `Kˣ^n`, and suppose every element of `Delta` has
an `n`-th root in a finite Galois extension `L/K`.  This file restricts the
actual finite Kummer character to

`Delta / Kˣ^n → Hom(Gal(L/K), μₙ(L))`.

The exact kernel theorem for the actual radical subgroup proves this
restricted map injective.  We then transpose the pairing.  If `L` is
generated by the roots belonging to `Delta`, the transpose is injective
because an automorphism in its kernel fixes every generator.

No character-surjectivity or lattice-correspondence conclusion is assumed.
-/

noncomputable section

namespace KummerTheory

section RestrictedFiniteKummer

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- Every restricted radical class has a representative in `Delta`. -/
theorem restrictedRadicalQuotientMk_surjective
    (n : ℕ+) (Delta : KummerSubgroup K n) :
    Function.Surjective (restrictedRadicalQuotientMk n Delta) := by
  change Function.Surjective
    (QuotientGroup.mk' (restrictedNthPowersSubgroup n Delta))
  exact QuotientGroup.mk'_surjective _

/-- Eliminate a restricted radical quotient through canonical
representatives. -/
theorem restrictedRadicalQuotient_inductionOn
    (n : ℕ+) (Delta : KummerSubgroup K n)
    {motive : RestrictedRadicalQuotient n Delta → Prop}
    (q : RestrictedRadicalQuotient n Delta)
    (mk : ∀ a : Delta.1,
      motive (restrictedRadicalQuotientMk n Delta a)) :
    motive q := by
  exact QuotientGroup.induction_on' q mk

/-- Exactness of the subgroup-level kernel makes the restricted quotient character
injective. -/
theorem restrictedQuotientKummerCharacter_injective
    [IsGalois K L]
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (Delta : KummerSubgroup K n)
    (hDelta : Delta.1 ≤ finiteKummerRadicalSubgroup (K := K) (L := L) n) :
    Function.Injective (restrictedQuotientKummerCharacter n hmu Delta hDelta) := by
  intro q r hqr
  revert hqr
  refine restrictedRadicalQuotient_inductionOn
    (motive := fun q =>
      restrictedQuotientKummerCharacter n hmu Delta hDelta q =
          restrictedQuotientKummerCharacter n hmu Delta hDelta r →
        q = r)
    n Delta q ?_
  intro a
  refine restrictedRadicalQuotient_inductionOn
    (motive := fun r =>
      restrictedQuotientKummerCharacter n hmu Delta hDelta
          (restrictedRadicalQuotientMk n Delta a) =
          restrictedQuotientKummerCharacter n hmu Delta hDelta r →
        restrictedRadicalQuotientMk n Delta a = r)
    n Delta r ?_
  intro b hab
  apply (restrictedRadicalQuotientMk_eq_iff n Delta a b).2
  rw [← ker_restrictedSubgroupKummerCharacter n hmu Delta hDelta]
  have hab' :
      restrictedSubgroupKummerCharacter n hmu Delta hDelta a =
        restrictedSubgroupKummerCharacter n hmu Delta hDelta b := by
    exact hab
  rw [MonoidHom.mem_ker, map_div, hab']
  exact div_self' (restrictedSubgroupKummerCharacter n hmu Delta hDelta b)

/-- If the transposed character of `sigma` is trivial, then `sigma` fixes
every actual `n`-th root belonging to `Delta`.  Independence of the root
choice follows from the fact that all `n`-th roots of unity lie in `K`. -/
theorem restrictedKummerTranspose_fixes_root
    [IsGalois K L]
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (Delta : KummerSubgroup K n)
    (hDelta : Delta.1 ≤ finiteKummerRadicalSubgroup (K := K) (L := L) n)
    (sigma : Gal(L/K))
    (hsigma : restrictedKummerTranspose n hmu Delta hDelta sigma = 1)
    {beta : L}
    (hbeta : beta ∈ kummerRootSet (K := K) (Omega := L) n Delta.1) :
    sigma beta = beta := by
  let D := chosenFiniteKummerRadicalDatum (K := K) (L := L) n
  let hfixed := restrictedKummerFixed (K := K) (L := L) n hmu
  have hbetaNe : beta ≠ 0 := kummerRootSet_ne_zero n Delta.1 hbeta
  obtain ⟨a, ha⟩ := hbeta
  let aD : D.carrier := restrictedRadicalInclusion n Delta hDelta a
  let betaUnit : Lˣ := Units.mk0 beta hbetaNe
  have hbetaPow : betaUnit ^ (n : ℕ) =
      Units.map (algebraMap K L).toMonoidHom aD.1 := by
    apply Units.ext
    exact ha
  let q : RestrictedRadicalQuotient n Delta :=
    restrictedRadicalQuotientMk n Delta a
  have hvalue : restrictedQuotientKummerCharacter n hmu Delta hDelta q sigma = 1 := by
    have happ := congrArg
      (fun chi : RestrictedRadicalQuotient n Delta →* nthRootsSubgroup L (n : ℕ) =>
        chi q) hsigma
    exact happ
  have hraw : restrictedSubgroupKummerCharacter n hmu Delta hDelta a sigma = 1 := by
    exact hvalue
  have hchosen : D.rootCharacterToMuWithoutSection aD hfixed sigma = 1 := by
    change D.rootCharacterToMuWithoutSection aD hfixed sigma = 1 at hraw
    exact hraw
  have hchosenVal : D.rootCocycle aD sigma = 1 := by
    have hval := congrArg Subtype.val hchosen
    simpa [RadicalDatum.rootCharacterToMuWithoutSection_apply,
      RadicalDatum.rootCharacter_apply] using hval
  have hquotient : rootQuotient (K := K) (L := L) betaUnit sigma = 1 := by
    rw [D.rootQuotient_eq_rootCocycle_of_same_pow hfixed aD hbetaPow sigma]
    exact hchosenVal
  have hunit : sigma • betaUnit = betaUnit :=
    (rootQuotient_eq_one_iff (K := K) (L := L) betaUnit sigma).1 hquotient
  exact congrArg Units.val hunit

/-- If the roots attached to `Delta` generate `L`, the transposed restricted
Kummer pairing is nondegenerate on the Galois side. -/
theorem restrictedKummerTranspose_injective_of_adjoin
    [IsGalois K L]
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (Delta : KummerSubgroup K n)
    (hDelta : Delta.1 ≤ finiteKummerRadicalSubgroup (K := K) (L := L) n)
    (hgenerate : IntermediateField.adjoin K
      (kummerRootSet (K := K) (Omega := L) n Delta.1) = ⊤) :
    Function.Injective (restrictedKummerTranspose n hmu Delta hDelta) := by
  intro sigma tau hsigmaTau
  apply div_eq_one.mp
  let rho : Gal(L/K) := sigma / tau
  have hrhoTranspose : restrictedKummerTranspose n hmu Delta hDelta rho = 1 := by
    rw [show rho = sigma / tau from rfl, map_div, hsigmaTau]
    exact div_self' (restrictedKummerTranspose n hmu Delta hDelta tau)
  have hrho : rho = 1 := by
    apply AlgEquiv.ext
    intro x
    change rho x = x
    have hx : x ∈ IntermediateField.adjoin K
        (kummerRootSet (K := K) (Omega := L) n Delta.1) := by
      rw [hgenerate]
      exact IntermediateField.mem_top
    induction hx using IntermediateField.adjoin_induction with
    | mem x hx =>
        exact restrictedKummerTranspose_fixes_root n hmu Delta hDelta rho
          hrhoTranspose hx
    | algebraMap x =>
        exact rho.commutes x
    | add x y hx hy ihx ihy =>
        rw [map_add, ihx, ihy]
    | inv x hx ihx =>
        rw [map_inv₀, ihx]
    | mul x y hx hy ihx ihy =>
        rw [map_mul, ihx, ihy]
  exact hrho

/-- The subgroup quotient `Delta / Kˣ^n` is killed by `n`. -/
theorem restrictedRadicalQuotient_pow_eq_one
    (n : ℕ+) (Delta : KummerSubgroup K n)
    (q : RestrictedRadicalQuotient n Delta) :
    q ^ (n : ℕ) = 1 := by
  refine restrictedRadicalQuotient_inductionOn
    (motive := fun q => q ^ (n : ℕ) = 1) n Delta q ?_
  intro a
  rw [← map_pow]
  exact (restrictedRadicalQuotientMk_eq_one_iff
    n Delta (a ^ (n : ℕ))).2
      ((mem_restrictedNthPowersSubgroup_iff n Delta).2 ⟨a.1, rfl⟩)

end RestrictedFiniteKummer

end KummerTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ScalingCovariance
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology
open Set
open Filter Set Module MeasureTheory
open scoped Topology NumberField
open Filter Set Module MeasureTheory WithLp
open scoped Topology NumberField BigOperators nonZeroDivisors
open scoped Topology NumberField BigOperators nonZeroDivisors ComplexConjugate
open MeasureTheory Set Filter Module WithLp
open scoped Topology BigOperators NumberField nonZeroDivisors
open Complex Set Filter Module
open Complex
open Complex Set Filter
open scoped Topology NumberField ComplexConjugate
open scoped Topology NumberField ComplexConjugate Classical
open Filter Set Topology Module
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal NNReal ProbabilityTheory
open scoped Matrix Topology Classical ENNReal
open scoped Topology ENNReal
open scoped Matrix Topology ENNReal ProbabilityTheory


namespace PrimeDegreePackets

def rootCanonicalFlow (d : ℕ) (j : Fin (d+1)) (t : ℝ) : G (d+1) :=
  diagonalOneParameter (rootCanonicalWeights d j) (rootCanonicalWeights_sum d j) t

end PrimeDegreePackets


end
end

end OAI
end


