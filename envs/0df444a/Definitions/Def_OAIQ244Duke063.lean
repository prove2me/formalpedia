-- Prove2me | Definitions.Def_OAIQ244Duke063
-- name    : OAIQ244Duke063
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T22:35:54.875797+00:00
-- url     : https://prove2.me/theorems/1d3efc3b-dff0-4832-a53f-55fc3b831762
-- title:
--   Definitions bundle OAIQ244Duke063 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 37 declarations of OpenAI's Lean: 12 definitions and 25 theorems. The definitions and types are `GlobalClassFieldTheory.ClassFieldAxiom.sUnitKummerCoordinateFixedField`, `GlobalClassFieldTheory.ClassFieldAxiom.sUnitKummerKernelGenerator`, `IdeleGroup.openAllLocalCosetTarget`, `IdeleGroup.openLocalCosetTarget`, `IdeleGroup.openLocalCosetTargetPoint`, `KummerTheory.chosenEnlargedSUnitKummerRestrictionKernelEquivPiZMod`, `KummerTheory.enlargedSUnitKummerEmbeddedExtension`, `LocalClassFieldTheory.finiteFixedField`, `LocalClassFieldTheory.finiteFixedFieldSeparableClosureAlgebra`, `relativeIdeleSupportedEquivUnrestrictedProdOutside`, `relativeIdeleSupportedHerbrandH0EquivUnrestrictedProdOutside`, `relativeIdeleSupportedHerbrandHMinusOneEquivUnrestrictedProdOutside`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `AlgebraicNumberTheory_Idele_Cohomology_SPlaces_Reassociation`, `AlgebraicNumberTheory_Idele_Norm`, `AlgebraicNumberTheory_Idele_Relative_FiniteIntegralNormPreimage`, `AlgebraicNumberTheory_RayClass_Approximation`, `GlobalClassFieldTheory_ClassFieldAxiom_SUnitKummerPrimeSelection_RestrictionKernel`, `KummerTheory_Concrete_SUnitPreparation_Core`, `KummerTheory_Concrete_SUnitPreparation_EnlargedSUnitRestriction`, `LocalClassFieldTheory_Finite_LocalReciprocity_FixedFieldLocalData`, `LocalClassFieldTheory_Finite_LocalReciprocity_TopologicalReciprocity`, `LocalClassFieldTheory_Finite_Unramified_Cohomology`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke053`, `OAIQ244Duke054`, `OAIQ244Duke055`, `OAIQ244Duke056`, `OAIQ244Duke057` and `OAIQ244Duke058` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke069` and `OAIQ244Duke070`.
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
import Mathlib.Algebra.Group.Equiv.TypeTags
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
import Mathlib.Algebra.Module.ZMod
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
import Mathlib.Data.Finsupp.Fintype
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
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.KrullTopology
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
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances
import Mathlib.NumberTheory.NumberField.Completion.Ramification
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.NumberTheory.NumberField.Units.Regulator
import Mathlib.NumberTheory.Ostrowski
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.RamificationInertia.Ramification
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
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.DedekindDomain.Factorization
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
import Mathlib.RingTheory.LocalRing.Module
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
import Definitions.Def_OAIQ244Duke053
import Definitions.Def_OAIQ244Duke054
import Definitions.Def_OAIQ244Duke055
import Definitions.Def_OAIQ244Duke056
import Definitions.Def_OAIQ244Duke057
import Definitions.Def_OAIQ244Duke058

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_RayClass_Approximation
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.nthRootsSubgroupFintype _root_.LocalClassFieldTheory.localDecompositionResidueFinite _root_.LocalClassFieldTheory.localDecompositionResidueFintype _root_.LocalClassFieldTheory.localSelectedResidueIsAlgClosed _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.finite_nsmulAddKernel_padicInt_pi _root_.LocalFieldTheory.DiscreteValuationField.finite_principalUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_residueRootsOfUnityGroup _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerKernel _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerKernel _root_.LocalFieldTheory.finite_nsmulAddKernel_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.chosenFinitePlaceBaseValued _root_.chosenFinitePlaceCompletionAlgebra _root_.scaledRelativeIntegerLatticeQuotientFinite
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IdeleGroup.extension_finiteComponent _root_.IdeleGroup.extension_principalIdele _root_.IdeleGroup.extension_self _root_.IdeleGroup.norm_principalIdele _root_.IdeleGroup.norm_relativeIdeleBaseChangeMulEquiv _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.finiteIdeleOfSPlaceFactors_apply_mem _root_.finiteIdeleOfSPlaceFactors_apply_notMem _root_.ideleClassCongr_mk _root_.ideleClassExtension_mk _root_.ideleClassExtension_self _root_.ideleClassNorm_mk _root_.ideleCongr_finiteComponent _root_.ideleCongr_principalIdele _root_.ideleSupportedAtEquivSPlaceFactors_infinite _root_.ideleSupportedAtEquivSPlaceFactors_inside _root_.ideleSupportedAtEquivSPlaceFactors_outside_coe _root_.infinitePlace_mult_smul _root_.ordinaryIdeleClassNorm_relativeIdeleClassBaseChange _root_.principalLocalNormQuotientMap_apply _root_.relativeFiniteIdeleMulEquiv_apply _root_.relativeFiniteIdeleToFiniteIdele_apply _root_.relativeIdeleBaseChangeMulEquiv_finite _root_.relativeIdeleBaseChangeMulEquiv_infinite _root_.relativeIdeleBaseChangeMulEquiv_principalIdele _root_.relativeIdeleClassBaseChangeMulEquiv_classInclusion _root_.relativeIdeleClassBaseChangeMulEquiv_mk _root_.relativeIdeleClassCongr_ideleClassNorm _root_.relativeIdeleCongr_norm _root_.towerRelativeIdeleViaOrdinaryMulEquiv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Multiplicative weak approximation for ideles

This file extracts the simultaneous approximation statement needed for ray
class groups. At finitely many
finite places one may prescribe an arbitrary open multiplicative coset and
move a given idele into all of those cosets by a single principal idele.
-/

open scoped NumberField Classical
open NumberField IsDedekindDomain

noncomputable section


variable {K : Type*} [Field K] [NumberField K]

namespace IdeleGroup

/-- The product of the prescribed finite local cosets and harmless
nonzero cosets at the infinite places.  The latter ensure that the global
approximating element is nonzero. -/
def openLocalCosetTarget
    (m : RayClass.Modulus K) (a : IdeleGroup K)
    (U : ∀ v : ↥m.finitePart.support,
      Subgroup (v.1.adicCompletion K)ˣ) :
    ∀ i : RayClass.ApproximationPlace m,
      Set (RayClass.approximationCompletion m i)
  | Sum.inl v => RayClass.unitRatioSet (a.2 v.1) (U v)
  | Sum.inr w =>
      RayClass.unitRatioSet
        (ContinuousMulEquiv.piUnits a.1 w) ⊤

/-- The given idele supplies a point in the product of the prescribed
local cosets. -/
def openLocalCosetTargetPoint
    (m : RayClass.Modulus K) (a : IdeleGroup K) :
    (i : RayClass.ApproximationPlace m) →
      RayClass.approximationCompletion m i
  | Sum.inl v => (a.2 v.1 : v.1.adicCompletion K)
  | Sum.inr w =>
      (ContinuousMulEquiv.piUnits a.1 w : w.Completion)

/-- The product of prescribed open multiplicative cosets at every
archimedean place and at the finite places in a modulus. -/
def openAllLocalCosetTarget
    (m : RayClass.Modulus K) (a : IdeleGroup K)
    (U : ∀ v : ↥m.finitePart.support,
      Subgroup (v.1.adicCompletion K)ˣ)
    (V : ∀ w : InfinitePlace K,
      Subgroup w.Completionˣ) :
    ∀ i : RayClass.ApproximationPlace m,
      Set (RayClass.approximationCompletion m i)
  | Sum.inl v => RayClass.unitRatioSet (a.2 v.1) (U v)
  | Sum.inr w =>
      RayClass.unitRatioSet
        (IdeleGroup.infiniteComponent w a) (V w)

/-- Every coordinate of the all-place multiplicative target is open. -/
theorem isOpen_openAllLocalCosetTarget
    (m : RayClass.Modulus K) (a : IdeleGroup K)
    (U : ∀ v : ↥m.finitePart.support,
      Subgroup (v.1.adicCompletion K)ˣ)
    (V : ∀ w : InfinitePlace K,
      Subgroup w.Completionˣ)
    (hU : ∀ v, IsOpen
      (U v : Set (v.1.adicCompletion K)ˣ))
    (hV : ∀ w, IsOpen
      (V w : Set w.Completionˣ)) :
    ∀ i, IsOpen
      (openAllLocalCosetTarget m a U V i)
  | Sum.inl v => by
      change IsOpen
        (RayClass.unitRatioSet (a.2 v.1) (U v))
      exact RayClass.isOpen_unitRatioSet _ _ (hU v)
  | Sum.inr w => by
      change IsOpen
        (RayClass.unitRatioSet
          (IdeleGroup.infiniteComponent w a) (V w))
      exact RayClass.isOpen_unitRatioSet _ _ (hV w)

/-- The given idele supplies a point in the simultaneous all-place
multiplicative target. -/
theorem openLocalCosetTargetPoint_mem_all
    (m : RayClass.Modulus K) (a : IdeleGroup K)
    (U : ∀ v : ↥m.finitePart.support,
      Subgroup (v.1.adicCompletion K)ˣ)
    (V : ∀ w : InfinitePlace K,
      Subgroup w.Completionˣ) :
    openLocalCosetTargetPoint m a ∈
      Set.univ.pi
        (openAllLocalCosetTarget m a U V) := by
  intro i _hi
  cases i with
  | inl v =>
      exact RayClass.val_mem_unitRatioSet _ _
  | inr w =>
      exact RayClass.val_mem_unitRatioSet _ _

/-- Multiplicative weak approximation simultaneously at all
archimedean places and at the finite support of a modulus.

For prescribed open subgroups `U_v ≤ K_vˣ` and
`V_w ≤ K_wˣ`, one global `x ∈ Kˣ` makes every quotient
`a_v / x` lie in the corresponding subgroup. -/
theorem exists_principal_quotient_mem_openAllLocalSubgroups
    (m : RayClass.Modulus K) (a : IdeleGroup K)
    (U : ∀ v : ↥m.finitePart.support,
      Subgroup (v.1.adicCompletion K)ˣ)
    (V : ∀ w : InfinitePlace K,
      Subgroup w.Completionˣ)
    (hU : ∀ v, IsOpen
      (U v : Set (v.1.adicCompletion K)ˣ))
    (hV : ∀ w, IsOpen
      (V w : Set w.Completionˣ)) :
    ∃ x : Kˣ,
      (∀ v : ↥m.finitePart.support,
        a.2 v.1 *
            ((principalIdele K x).2 v.1)⁻¹ ∈ U v) ∧
      (∀ w : InfinitePlace K,
        IdeleGroup.infiniteComponent w a *
            (IdeleGroup.infiniteComponent w
              (principalIdele K x))⁻¹ ∈ V w) := by
  let W : Set
      ((i : RayClass.ApproximationPlace m) →
        RayClass.approximationCompletion m i) :=
    Set.univ.pi (openAllLocalCosetTarget m a U V)
  have hWOpen : IsOpen W := by
    exact isOpen_set_pi Set.finite_univ fun i _hi =>
      isOpen_openAllLocalCosetTarget
        m a U V hU hV i
  have hWNonempty : W.Nonempty :=
    ⟨openLocalCosetTargetPoint m a,
      openLocalCosetTargetPoint_mem_all m a U V⟩
  obtain ⟨x, hx⟩ :=
    (RayClass.denseRange_approximationEmbedding m).exists_mem_open
      hWOpen hWNonempty
  let w₀ : InfinitePlace K := Classical.choice inferInstance
  have hxw₀ :=
    hx (Sum.inr w₀) (Set.mem_univ (Sum.inr w₀))
  change
    (x : w₀.Completion) ∈
      RayClass.unitRatioSet
        (IdeleGroup.infiniteComponent w₀ a)
        (V w₀) at hxw₀
  obtain ⟨y₀, _hy₀, hy₀x⟩ := hxw₀
  have hx0 : x ≠ 0 := by
    intro hxzero
    apply Units.ne_zero y₀
    rw [hy₀x, hxzero,
      NumberField.InfinitePlace.Completion.coe_zero]
  let xu : Kˣ := Units.mk0 x hx0
  refine ⟨xu, ?_, ?_⟩
  · intro v
    have hvx :=
      hx (Sum.inl v) (Set.mem_univ (Sum.inl v))
    change
      FinitePlace.embedding v.1 x ∈
        RayClass.unitRatioSet (a.2 v.1) (U v) at hvx
    obtain ⟨y, hy, hyx⟩ := hvx
    have hprincipal :
        (principalIdele K xu).2 v.1 = y := by
      apply Units.ext
      calc
        (((principalIdele K xu).2 v.1 :
            (v.1.adicCompletion K)ˣ) :
            v.1.adicCompletion K) =
            (xu : K) :=
          finiteComponent_principalIdele xu v.1
        _ = (x : K) := rfl
        _ = (y : v.1.adicCompletion K) := hyx.symm
    rw [hprincipal]
    exact hy
  · intro w
    have hwx :=
      hx (Sum.inr w) (Set.mem_univ (Sum.inr w))
    change
      (x : w.Completion) ∈
        RayClass.unitRatioSet
          (IdeleGroup.infiniteComponent w a)
          (V w) at hwx
    obtain ⟨y, hy, hyx⟩ := hwx
    have hprincipal :
        IdeleGroup.infiniteComponent w
            (principalIdele K xu) = y := by
      apply Units.ext
      calc
        ((IdeleGroup.infiniteComponent w
            (principalIdele K xu) : w.Completionˣ) :
            w.Completion) =
            (xu : K) :=
          infiniteComponent_principalIdele xu w
        _ = (x : K) := rfl
        _ = (y : w.Completion) := hyx.symm
    rw [hprincipal]
    exact hy

/-- Finset-indexed simultaneous finite-and-infinite multiplicative weak
approximation. -/
theorem exists_principal_quotient_mem_openAllLocalSubgroups_finset
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a : IdeleGroup K)
    (U : ∀ v : ↥S,
      Subgroup (v.1.adicCompletion K)ˣ)
    (V : ∀ w : InfinitePlace K,
      Subgroup w.Completionˣ)
    (hU : ∀ v, IsOpen
      (U v : Set (v.1.adicCompletion K)ˣ))
    (hV : ∀ w, IsOpen
      (V w : Set w.Completionˣ)) :
    ∃ x : Kˣ,
      (∀ v : ↥S,
        a.2 v.1 *
            ((principalIdele K x).2 v.1)⁻¹ ∈ U v) ∧
      (∀ w : InfinitePlace K,
        IdeleGroup.infiniteComponent w a *
            (IdeleGroup.infiniteComponent w
              (principalIdele K x))⁻¹ ∈ V w) := by
  let m : RayClass.Modulus K := modulusOfFinset S
  have hm : m.finitePart.support = S := by
    simp [m]
  let U' : ∀ v : ↥m.finitePart.support,
      Subgroup (v.1.adicCompletion K)ˣ :=
    fun v => U ⟨v.1, hm ▸ v.2⟩
  have hU' :
      ∀ v, IsOpen (U' v : Set (v.1.adicCompletion K)ˣ) :=
    fun v => hU ⟨v.1, hm ▸ v.2⟩
  obtain ⟨x, hfinite, hinfinite⟩ :=
    exists_principal_quotient_mem_openAllLocalSubgroups
      m a U' V hU' hV
  refine ⟨x, ?_, hinfinite⟩
  intro v
  have hv : v.1 ∈ m.finitePart.support := hm.symm ▸ v.2
  exact hfinite ⟨v.1, hv⟩

end IdeleGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_TopologicalReciprocity
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_finite_residue _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.scaledRelativeIntegerLatticeQuotientFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Topological finite local reciprocity

This module upgrades the algebraic finite local reciprocity isomorphism to a
homeomorphic group isomorphism.  The key input is that the norm subgroup of a
finite Galois extension is open.  Consequently its quotient is discrete, as
is the topological abelianization of the finite Krull Galois group.
-/

noncomputable section

namespace LocalClassFieldTheory

open scoped NNReal ValuativeRel
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

section NormSubgroupTopology

universe u

theorem integerUnitNormSubgroup_eq_localNormSubgroup_inf_baseUnits
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    integerUnitNormSubgroup K L =
      localNormSubgroup K L ⊓ localBaseUnitSubgroup K := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨⟨integerUnitsToFieldUnits L a, rfl⟩, ?_⟩
    refine ⟨normIntegerUnits K L a, ?_⟩
    apply Units.ext
    rfl
  · rintro ⟨⟨y, hy⟩, ⟨a, ha⟩⟩
    have hxv : v K (Additive.ofMul x) = 0 := by
      rw [← ha]
      exact v_integerUnitsToFieldUnits K a
    have hnorm := v_normUnits_eq_residue_finrank_mul_of_isSeparable K L y
    change v K (Additive.ofMul (LocalFieldTheory.normUnits K L y)) =
      (@Module.finrank 𝓀[K] 𝓀[L] _ _
        (IsLocalRing.ResidueField.instModule (R := 𝒪[K]) (S := 𝒪[L])) : Int) *
        v L (Additive.ofMul y) at hnorm
    have hproduct :
        (@Module.finrank 𝓀[K] 𝓀[L] _ _
          (IsLocalRing.ResidueField.instModule (R := 𝒪[K]) (S := 𝒪[L])) : Int) *
          v L (Additive.ofMul y) = 0 := by
      rw [← hnorm, hy]
      exact hxv
    have hfinrank :
        (@Module.finrank 𝓀[K] 𝓀[L] _ _
          (IsLocalRing.ResidueField.instModule (R := 𝒪[K]) (S := 𝒪[L])) : Int) ≠ 0 := by
      have hnat :
          @Module.finrank 𝓀[K] 𝓀[L] _ _
            (IsLocalRing.ResidueField.instModule (R := 𝒪[K]) (S := 𝒪[L])) ≠ 0 :=
        Nat.ne_of_gt Module.finrank_pos
      exact_mod_cast hnat
    have hyv : v L (Additive.ofMul y) = 0 :=
      (mul_eq_zero.mp hproduct).resolve_left hfinrank
    have hyvaluation : valuationMap L (Additive.ofMul y) = 0 := by
      rw [valuationMap_apply]
      exact hyv
    obtain ⟨b, hb⟩ :=
      (integerUnitsToFieldUnits_mem_range_iff_valuationMap_eq_zero L y).2 hyvaluation
    refine ⟨b, ?_⟩
    change LocalFieldTheory.normUnits K L (integerUnitsToFieldUnits L b) = x
    rw [hb, hy]

end NormSubgroupTopology

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_Unramified_Cohomology
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.localDecompositionResidueFintype _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Tate cohomology of units in unramified extensions

For an unramified extension of local fields the actual low-degree Tate
cohomology of the integer units and of every principal-unit group is trivial.
The norm statements are the corresponding actual norm surjections.
-/

noncomputable section

universe u

namespace LocalClassFieldTheory

open scoped ValuativeRel
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField
open CyclicCohomology
open CyclicCohomology.ProfiniteCohomology.Herbrand

/-- The unramified unit-cohomology theorem for the actual integer-unit module: both low-degree Tate
groups are trivial in an unramified extension. -/
theorem unramified_integerUnits_herbrand_subsingleton
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [UniformSpace L] [IsUniformAddGroup L]
    [IsNonarchimedeanLocalField L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [IsUnramifiedValuedExtension K L]
    (g : Gal(L / K)) (hg : ∀ sigma : Gal(L / K), sigma ∈ Subgroup.zpowers g) :
    letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
    Subsingleton (HerbrandH0 Gal(L / K) 𝒪[L]ˣ) ∧
      Subsingleton (HerbrandHMinusOne Gal(L / K) 𝒪[L]ˣ g) := by
  let := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  rcases integerUnits_herbrandQuotient_eq_one K L g hg with
    ⟨hU, hUone⟩
  let : Finite (HerbrandH0 Gal(L / K) 𝒪[L]ˣ) := hU.1
  let : Finite (HerbrandHMinusOne Gal(L / K) 𝒪[L]ˣ g) := hU.2
  have hfixed : fixedSubgroup Gal(L / K) 𝒪[L]ˣ ≤
      tateNormSubgroup Gal(L / K) 𝒪[L]ˣ := by
    intro a ha
    rcases exists_integerUnit_map_eq_of_galoisGroup_fixed K L a ha with
      ⟨b, hb⟩
    rcases normIntegerUnits_surjective_unramified_of_isIntegralClosure K L b with
      ⟨z, hz⟩
    refine ⟨z, ?_⟩
    calc
      tateNorm Gal(L / K) 𝒪[L]ˣ z =
          Finset.univ.prod (fun sigma : Gal(L / K) =>
            Units.mapEquiv
              (galoisGroupIntegerRingEquivOfIsIntegralClosure K L sigma).toMulEquiv z) := rfl
      _ = integerUnitsMapOfValuationExtension K L (normIntegerUnits K L z) :=
        (integerUnitsMap_normIntegerUnits_eq_galoisGroup_prod_of_isIntegralClosure K L z).symm
      _ = integerUnitsMapOfValuationExtension K L b := by rw [hz]
      _ = a := hb
  let : Subsingleton (HerbrandH0 Gal(L / K) 𝒪[L]ˣ) :=
    herbrandH0_subsingleton_of_fixed_le_tateNormSubgroup hfixed
  exact ⟨inferInstance,
    herbrandHMinusOne_subsingleton_of_h0_subsingleton_of_quotient_eq_one
      Gal(L / K) 𝒪[L]ˣ g hUone⟩

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Cohomology_SPlaces_Reassociation
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instCommGroupSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Reassociation of supported relative-idele factors

The factor model of a supported relative idele is reassociated into the
finite family of unrestricted places and the product of integral factors
outside the support.  The comparison respects the concrete Galois
actions.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section


open CyclicCohomology.ProfiniteCohomology.Herbrand
open CyclicCohomology

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- The complete supported relative-idele group, with its restricted-product
condition already built into the subtype, is the product of the unrestricted
local factors in `S` and the integral local factors outside `S`. -/
noncomputable def
    relativeIdeleSupportedEquivUnrestrictedProdOutside
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    relativeIdeleLocalTensorDecompositionSupportedSubgroup
          (K := K) (L := L) S ≃*
      RelativeUnrestrictedSPlaceFactors
          (K := K) (L := L) S ×
        RelativeOutsideSPlaceFactors
          (K := K) (L := L) S :=
  (relativeIdeleSupportedEquivSPlaceFactors
      (K := K) (L := L) S).trans
    (relativeIdeleSPlaceFactorsEquivUnrestrictedProdOutside
      (K := K) (L := L) S)

omit [IsGalois K L] in
/-- The supported relative-idele decomposition is equivariant for the
concrete Galois action on every factor. -/
theorem
    relativeIdeleSupportedEquivUnrestrictedProdOutside_smul
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (σ : L ≃ₐ[K] L)
    (z : relativeIdeleLocalTensorDecompositionSupportedSubgroup
      (K := K) (L := L) S) :
    relativeIdeleSupportedEquivUnrestrictedProdOutside
        (K := K) (L := L) S
        ((relativeIdeleLocalTensorDecompositionSupportedSubgroupAction
          (K := K) (L := L) S).smul σ z) =
      (relativeUnrestrictedProdOutsideAction
        (K := K) (L := L) S).smul σ
        (relativeIdeleSupportedEquivUnrestrictedProdOutside
          (K := K) (L := L) S z) := by
  apply Prod.ext
  · funext i
    cases i with
    | inl w =>
        let :=
          scalarTensorUnitsAction
            (K := K) (L := L) (A := w.Completion)
        exact
          RelativeIdeleGroup.infiniteComponent_smul
            (K := K) (L := L) w σ z
    | inr w =>
        let :=
          scalarTensorUnitsAction
            (K := K) (L := L)
            (A := w.1.adicCompletion K)
        exact
          RelativeIdeleGroup.finiteComponent_smul
            (K := K) (L := L) w.1 σ z
  · funext w
    apply Subtype.ext
    let :=
      scalarTensorUnitsAction
        (K := K) (L := L)
        (A := w.1.adicCompletion K)
    exact
      RelativeIdeleGroup.finiteComponent_smul
        (K := K) (L := L) w.1 σ z

/-- Transport of degree-zero Tate cohomology from the actual
supported relative ideles to the unrestricted and outside-integral
factorization. -/
noncomputable def
    relativeIdeleSupportedHerbrandH0EquivUnrestrictedProdOutside
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    letI :=
      relativeIdeleLocalTensorDecompositionSupportedSubgroupAction
        (K := K) (L := L) S
    letI :=
      relativeUnrestrictedProdOutsideAction
        (K := K) (L := L) S
    HerbrandH0 (L ≃ₐ[K] L)
        (relativeIdeleLocalTensorDecompositionSupportedSubgroup
          (K := K) (L := L) S) ≃*
      HerbrandH0 (L ≃ₐ[K] L)
        (RelativeUnrestrictedSPlaceFactors
            (K := K) (L := L) S ×
          RelativeOutsideSPlaceFactors
            (K := K) (L := L) S) := by
  letI :=
    relativeIdeleLocalTensorDecompositionSupportedSubgroupAction
      (K := K) (L := L) S
  letI :=
    relativeUnrestrictedProdOutsideAction
      (K := K) (L := L) S
  exact
    herbrandH0EquivariantMulEquiv
      (relativeIdeleSupportedEquivUnrestrictedProdOutside
        (K := K) (L := L) S)
      (relativeIdeleSupportedEquivUnrestrictedProdOutside_smul
        (K := K) (L := L) S)

/-- Transport of degree-minus-one Tate cohomology from the
actual supported relative ideles to the unrestricted and outside-integral
factorization. -/
noncomputable def
    relativeIdeleSupportedHerbrandHMinusOneEquivUnrestrictedProdOutside
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (σ : L ≃ₐ[K] L) :
    letI :=
      relativeIdeleLocalTensorDecompositionSupportedSubgroupAction
        (K := K) (L := L) S
    letI :=
      relativeUnrestrictedProdOutsideAction
        (K := K) (L := L) S
    HerbrandHMinusOne (L ≃ₐ[K] L)
        (relativeIdeleLocalTensorDecompositionSupportedSubgroup
          (K := K) (L := L) S) σ ≃*
      HerbrandHMinusOne (L ≃ₐ[K] L)
        (RelativeUnrestrictedSPlaceFactors
            (K := K) (L := L) S ×
          RelativeOutsideSPlaceFactors
            (K := K) (L := L) S) σ := by
  letI :=
    relativeIdeleLocalTensorDecompositionSupportedSubgroupAction
      (K := K) (L := L) S
  letI :=
    relativeUnrestrictedProdOutsideAction
      (K := K) (L := L) S
  exact
    herbrandHMinusOneEquivariantMulEquiv
      (relativeIdeleSupportedEquivUnrestrictedProdOutside
        (K := K) (L := L) S)
      (relativeIdeleSupportedEquivUnrestrictedProdOutside_smul
        (K := K) (L := L) S) σ
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Relative_FiniteIntegralNormPreimage
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.gLocallyCompact _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.relativeUnrestrictedSPlaceFactorCommGroup
attribute [-simp] _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicGlobalToLocalizedAlgHom_apply _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicGlobalToLocalizedAlgHom_primitiveRoot _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.chosenFinitePlaceIntegerToLocalizedCompletion_coe _root_.chosenFinitePlaceLocalizedResidueEquiv_apply_mk _root_.doubleCosetExtension_mk _root_.extendAbsoluteValueExtensionFromIntermediate_apply _root_.finitePlaceBelow_finitePlaceExtensionCentre _root_.finitePlaceExtensionAdicCompletionRingEquiv_toCompletion _root_.finitePlaceExtensionCentreInFibre_coe _root_.finitePlaceExtensionCentre_asIdeal _root_.finitePlaceExtensionCompletionRingEquiv_toCompletion _root_.finitePlaceExtensionEquivAbove_coe _root_.finitePlaceTensorRingEquivAboveAdic_apply_extension _root_.finitePlaceTensorUnitsEquivAboveAdic_apply_extension _root_.infinitePlaceAboveEquivExtension_apply_val _root_.infinitePlaceTensorRingEquivAbove_apply _root_.infinitePlaceTensorUnitsEquivAbove_apply _root_.infinitePlace_mult_smul _root_.mem_finitePlaceDecompositionGroup_iff _root_.relativeIdeleOfSPlaceFactors_finiteComponent_inside _root_.relativeIdeleOfSPlaceFactors_finiteComponent_outside _root_.relativeIdeleSupportedComponents_infinite _root_.relativeIdeleSupportedComponents_inside _root_.relativeIdeleSupportedComponents_outside_coe _root_.relativeLocalIdeleDataOfSPlaceFactors_finite_inside _root_.relativeLocalIdeleDataOfSPlaceFactors_finite_outside _root_.restrictAbsoluteValueExtensionToIntermediate_apply _root_.ringOfIntegersToFinitePlaceExtensionValuationSubring_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Integral finite-place preimages of local tensor norms

If a finite local component is both a determinant norm and a local
integer unit, its determinant-norm preimage can be chosen integral in
every factor of the canonical local tensor decomposition.  This is the local restricted-product
input needed to assemble pointwise local norm preimages globally.
-/

open scoped NumberField TensorProduct ValuativeRel NNReal
open NumberField IsDedekindDomain

noncomputable section


open AlgebraicNumberTheory.Valuations
open LocalClassFieldTheory
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField
open ValuationTheory.Completion

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

universe u

omit [NumberField L] [IsGalois K L] in
/-- The component of a singly supported integral tensor unit is the
corresponding member of its defining completion-unit family. -/
theorem finitePlaceLocalTensorDecompositionUnitsComponent_single
    (v₀ : HeightOneSpectrum (𝓞 K))
    (w :
      AbsoluteValueExtension
        (HeightOneSpectrum.adicAbv K v₀) L)
    (y :
      (absoluteValueCompletionIntegers w.1
        (absoluteValueExtension_isNonarchimedean
          (HeightOneSpectrum.adicAbv K v₀)
          (HeightOneSpectrum.isNonarchimedean_adicAbv K v₀)
          w))ˣ)
    (u :
      AbsoluteValueExtension
        (HeightOneSpectrum.adicAbv K v₀) L) :
    finitePlaceLocalTensorDecompositionUnitsComponent
        (K := K) (L := L) v₀ u
        (singleRelativeLocalTensorDecompositionIntegralUnit
          (K := K) (L := L) v₀ w y) =
      Units.map
        (absoluteValueCompletionIntegers u.1
          (absoluteValueExtension_isNonarchimedean
            (HeightOneSpectrum.adicAbv K v₀)
            (HeightOneSpectrum.isNonarchimedean_adicAbv K v₀)
            u)).subtype
        (singleFinitePlaceIntegralUnitFamily
          (K := K) (L := L) v₀ w y u) := by
  have h :=
    congrFun
      ((relativeLocalTensorDecompositionIntegralUnitSubgroupEquivPiUnits
        (K := K) (L := L) v₀).apply_symm_apply
          (singleFinitePlaceIntegralUnitFamily
            (K := K) (L := L) v₀ w y)) u
  apply Units.ext
  exact congrArg Subtype.val
    (congrArg Units.val h)

omit [NumberField L] [IsGalois K L] in
/-- A singly supported integral tensor unit is integral in every completion
factor, together with its inverse. -/
theorem singleRelativeLocalTensorDecompositionIntegralUnit_isIntegral
    (v₀ : HeightOneSpectrum (𝓞 K))
    (w :
      AbsoluteValueExtension
        (HeightOneSpectrum.adicAbv K v₀) L)
    (y :
      (absoluteValueCompletionIntegers w.1
        (absoluteValueExtension_isNonarchimedean
          (HeightOneSpectrum.adicAbv K v₀)
          (HeightOneSpectrum.isNonarchimedean_adicAbv K v₀)
          w))ˣ) :
    RelativeLocalTensorDecompositionIntegralUnitAt
      (K := K) (L := L) v₀
      (singleRelativeLocalTensorDecompositionIntegralUnit
        (K := K) (L := L) v₀ w y) :=
  (mem_relativeLocalTensorDecompositionIntegralUnitSubgroup_iff
    (K := K) (L := L) v₀
    (singleRelativeLocalTensorDecompositionIntegralUnit
      (K := K) (L := L) v₀ w y)).1
    (singleRelativeLocalTensorDecompositionIntegralUnit
      (K := K) (L := L) v₀ w y).property

omit [NumberField L] [IsGalois K L] in
/-- The product of component norms of a singly supported integral tensor
unit is the norm of its supported component. -/
theorem prod_norm_finitePlaceLocalTensorDecompositionUnitsComponent_single_eq
    (v₀ : HeightOneSpectrum (𝓞 K))
    (w :
      AbsoluteValueExtension
        (HeightOneSpectrum.adicAbv K v₀) L)
    (y :
      (absoluteValueCompletionIntegers w.1
        (absoluteValueExtension_isNonarchimedean
          (HeightOneSpectrum.adicAbv K v₀)
          (HeightOneSpectrum.isNonarchimedean_adicAbv K v₀)
          w))ˣ)
    (x₀ :
      (HeightOneSpectrum.adicAbv K v₀).Completionˣ)
    [Fintype
      (AbsoluteValueExtension
        (HeightOneSpectrum.adicAbv K v₀) L)]
    [∀ u :
        AbsoluteValueExtension
          (HeightOneSpectrum.adicAbv K v₀) L,
      Algebra
        (HeightOneSpectrum.adicAbv K v₀).Completion
        u.1.Completion]
    [∀ u :
        AbsoluteValueExtension
          (HeightOneSpectrum.adicAbv K v₀) L,
      Module.Finite
        (HeightOneSpectrum.adicAbv K v₀).Completion
        u.1.Completion]
    (hNorm :
      Algebra.norm
          (HeightOneSpectrum.adicAbv K v₀).Completion
          ((Units.map
            (absoluteValueCompletionIntegers w.1
              (absoluteValueExtension_isNonarchimedean
                (HeightOneSpectrum.adicAbv K v₀)
                (HeightOneSpectrum.isNonarchimedean_adicAbv K v₀)
                w)).subtype y :
              w.1.Completionˣ) :
            w.1.Completion) =
        (x₀ : (HeightOneSpectrum.adicAbv K v₀).Completion)) :
    (∏ u :
        AbsoluteValueExtension
          (HeightOneSpectrum.adicAbv K v₀) L,
      Algebra.norm
        (HeightOneSpectrum.adicAbv K v₀).Completion
        (finitePlaceLocalTensorDecompositionUnitsComponent
          (K := K) (L := L) v₀ u
          (singleRelativeLocalTensorDecompositionIntegralUnit
            (K := K) (L := L) v₀ w y) :
          u.1.Completion)) =
      (x₀ : (HeightOneSpectrum.adicAbv K v₀).Completion) := by
  classical
  let vK := HeightOneSpectrum.adicAbv K v₀
  let hvKna : IsNonarchimedean (vK : K → ℝ) :=
    HeightOneSpectrum.isNonarchimedean_adicAbv K v₀
  let z :
      (v₀.adicCompletion K ⊗[K] L)ˣ :=
    singleRelativeLocalTensorDecompositionIntegralUnit
      (K := K) (L := L) v₀ w y
  have hComponents :
      ∀ u : AbsoluteValueExtension vK L,
        finitePlaceLocalTensorDecompositionUnitsComponent
            (K := K) (L := L) v₀ u z =
          Units.map
            (absoluteValueCompletionIntegers u.1
              (absoluteValueExtension_isNonarchimedean
                vK hvKna u)).subtype
            (singleFinitePlaceIntegralUnitFamily
              (K := K) (L := L) v₀ w y u) :=
    finitePlaceLocalTensorDecompositionUnitsComponent_single
      (K := K) (L := L) v₀ w y
  rw [Finset.prod_eq_single w]
  · rw [hComponents]
    have hSelf :
        singleFinitePlaceIntegralUnitFamily
            (K := K) (L := L) v₀ w y w =
          y := by
      change
        dite (w = w)
            (fun h => h ▸ y)
            (fun _ => 1) =
          y
      rw [dite_eq_left rfl]
    rw [hSelf]
    exact hNorm
  · intro u _ hu
    rw [hComponents]
    have hwu : w ≠ u := Ne.symm hu
    have hAway :
        singleFinitePlaceIntegralUnitFamily
            (K := K) (L := L) v₀ w y u =
          1 := by
      change
        dite (w = u)
            (fun h => h ▸ y)
            (fun _ => 1) =
          1
      rw [dite_eq_right hwu]
    rw [hAway]
    simp
  · intro hw
    exact (hw (Finset.mem_univ w)).elim

omit [NumberField L] in
/-- The determinant norm of a singly supported integral tensor unit is the
norm of its unique nontrivial completion component. -/
theorem localTensorDetNorm_singleRelativeLocalTensorDecompositionIntegralUnit_eq
    (v₀ : HeightOneSpectrum (𝓞 K))
    (w :
      AbsoluteValueExtension
        (HeightOneSpectrum.adicAbv K v₀) L)
    (y :
      (absoluteValueCompletionIntegers w.1
        (absoluteValueExtension_isNonarchimedean
          (HeightOneSpectrum.adicAbv K v₀)
          (HeightOneSpectrum.isNonarchimedean_adicAbv K v₀)
          w))ˣ)
    (x₀ :
      (HeightOneSpectrum.adicAbv K v₀).Completionˣ)
    (hNorm :
      let vK := HeightOneSpectrum.adicAbv K v₀
      letI hK :=
        AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
      letI : SMul K w.1.Completion := hK.toSMul
      letI : Algebra vK.Completion w.1.Completion :=
        AbsoluteValue.completionAlgebra vK w.1 w.2
      Algebra.norm vK.Completion
        ((Units.map
          (absoluteValueCompletionIntegers w.1
            (absoluteValueExtension_isNonarchimedean
              vK
              (HeightOneSpectrum.isNonarchimedean_adicAbv K v₀)
              w)).subtype y :
            w.1.Completionˣ) :
          w.1.Completion) =
        (x₀ : vK.Completion)) :
    localTensorDetNorm
        (K := K) (L := L)
        (HeightOneSpectrum.adicAbv K v₀)
        ((finitePlaceLocalTensorUnitsEquiv
          (K := K) (L := L) v₀).symm
          (singleRelativeLocalTensorDecompositionIntegralUnit
            (K := K) (L := L) v₀ w y)) =
      x₀ := by
  classical
  let vK := HeightOneSpectrum.adicAbv K v₀
  let hvK := RayClass.adicAbv_isNontrivial v₀
  let hK :=
    AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  dsimp only at hNorm
  let :=
    completionTensorDecomposition_extensionFintype
      (K := K) (L := L) vK hvK
  let : ∀ u : AbsoluteValueExtension vK L,
      Algebra vK.Completion u.1.Completion :=
    fun u =>
      AbsoluteValue.completionAlgebra vK u.1 u.2
  let : ∀ u : AbsoluteValueExtension vK L,
      Module.Finite vK.Completion u.1.Completion :=
    fun u =>
      completionModuleFinite vK hvK u
  let z :
      (v₀.adicCompletion K ⊗[K] L)ˣ :=
    singleRelativeLocalTensorDecompositionIntegralUnit
      (K := K) (L := L) v₀ w y
  let zA :
      (LocalTensorAlgebra (L := L) vK)ˣ :=
    (finitePlaceLocalTensorUnitsEquiv
      (K := K) (L := L) v₀).symm z
  have hNormProduct :=
    RelativeIdeleGroup.localNorm_units_eq_prod
      vK hvK zA
  have hProduct :
      (∏ u : AbsoluteValueExtension vK L,
        Algebra.norm vK.Completion
          (finitePlaceLocalTensorDecompositionUnitsComponent
            (K := K) (L := L) v₀ u z :
              u.1.Completion)) =
        (x₀ : vK.Completion) :=
    prod_norm_finitePlaceLocalTensorDecompositionUnitsComponent_single_eq
      (K := K) (L := L) v₀ w y x₀ hNorm
  apply Units.ext
  change
    ((Units.map (Algebra.norm vK.Completion) zA :
        vK.Completionˣ) : vK.Completion) =
      (x₀ : vK.Completion)
  rw [hNormProduct]
  have hComponentEq :
      ∀ u : AbsoluteValueExtension vK L,
        completionTensorDecomposition_left
              (K := K) (L := L) vK hvK
              (zA : LocalTensorAlgebra (L := L) vK) u =
          (finitePlaceLocalTensorDecompositionUnitsComponent
            (K := K) (L := L) v₀ u z :
              u.1.Completion) := by
    intro u
    rfl
  simpa only [hComponentEq] using hProduct

omit [NumberField L] in
theorem exists_localizedCompletionNormPreimage_with_norm_bounds
    (v₀ : HeightOneSpectrum (𝓞 K))
    (x : (v₀.adicCompletion K)ˣ)
    (hxNorm :
      x ∈ (_root_.localTensorNorm
        (K := K) (L := L) v₀).range)
    (hxUnit :
      x ∈ (v₀.adicCompletionIntegers K).units) :
    let vK := HeightOneSpectrum.adicAbv K v₀
    let w := chosenFinitePlaceExtension (L := L) v₀
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI : Algebra vK.Completion w.1.Completion :=
      AbsoluteValue.completionAlgebra vK w.1 w.2
    let E := LocalizedCompletion vK w
    ∃ x₀ : vK.Completionˣ,
      ∃ y : Eˣ,
        LocalFieldTheory.normUnits vK.Completion E y = x₀ ∧
          finitePlaceCompletionUnitsContinuousMulEquiv v₀ x₀ = x ∧
            ‖(y : E)‖ ≤ 1 ∧
              ‖((y⁻¹ : Eˣ) : E)‖ ≤ 1 := by
  classical
  let vK := HeightOneSpectrum.adicAbv K v₀
  let w := chosenFinitePlaceExtension (L := L) v₀
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v₀
  let hvKna : IsNonarchimedean (vK : K → ℝ) :=
    HeightOneSpectrum.isNonarchimedean_adicAbv K v₀
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  let E := LocalizedCompletion vK w
  let : FiniteDimensional vK.Completion E :=
    localizedCompletionModuleFinite vK hvK w
  let : IsGalois vK.Completion E :=
    HilbertRamification.algebraicLocalization_isGalois vK w
  let : NontriviallyNormedField vK.Completion :=
    absoluteValueExtension_completionNontriviallyNormedField vK hvK
  let : LocallyCompactSpace vK.Completion :=
    AbsoluteValue.Completion.locallyCompactSpace
      (finitePlaceCompletionBaseMap_isometry v₀)
  let : IsUltrametricDist vK.Completion :=
    completionIsUltrametricDist vK hvKna
  let : Valued vK.Completion ℝ≥0 :=
    finitePlaceCompletionValued vK hvKna
  let vC : Valuation vK.Completion ℝ≥0 := Valued.v
  let : vC.IsNontrivial :=
    (inferInstance :
      (NormedField.valuation (K := vK.Completion)).IsNontrivial)
  let : ValuativeRel vK.Completion :=
    finitePlaceCompletionValuativeRel vK hvKna
  let : vC.Compatible :=
    Valuation.Compatible.ofValuation vC
  let : ValuativeRel.IsNontrivial vK.Completion :=
    (ValuativeRel.isNontrivial_iff_isNontrivial vC).2 inferInstance
  let vB := ValuativeRel.valuation vK.Completion
  let : vB.IsNontrivial := inferInstance
  let : IsValuativeTopology vK.Completion :=
    isValuativeTopology_of_valued_ofValuation
      vK.Completion ℝ≥0
  let : IsNonarchimedeanLocalField vK.Completion :=
    { toIsValuativeTopology := inferInstance
      toLocallyCompactSpace := inferInstance
      toIsNontrivial := inferInstance }
  let : FiniteDimensional vK.Completion w.1.Completion :=
    completionModuleFinite vK hvK w
  let : ContinuousSMul vK.Completion w.1.Completion :=
    continuousSMul_of_algebraMap _ _
      (AbsoluteValue.completionMap_isometry vK w.1 w.2).continuous
  let : LocallyCompactSpace w.1.Completion :=
    LocallyCompactSpace.of_finiteDimensional_of_complete
      vK.Completion w.1.Completion
  let eE : E ≃ᵢ w.1.Completion :=
    { toEquiv :=
        (localizedCompletionEquivCompletion vK hvK w).toEquiv
      isometry_toFun := Isometry.of_dist_eq fun _ _ => rfl }
  let : LocallyCompactSpace E :=
    (eE.toHomeomorph.locallyCompactSpace_iff).2 inferInstance
  let : IsUltrametricDist E :=
    localizedCompletionIsUltrametricDist vK w hvKna
  let : Valued E ℝ≥0 :=
    localizedCompletionFinitePlaceValued vK w hvKna
  let : ValuativeRel E :=
    localizedCompletionFinitePlaceValuativeRel vK w hvKna
  let vENorm : Valuation E ℝ≥0 := Valued.v
  let : vENorm.Compatible :=
    Valuation.Compatible.ofValuation vENorm
  let vE := ValuativeRel.valuation E
  let : Valuation.HasExtension vB vE :=
    localizedCompletionValuationHasExtension vK w hvKna
  let : vE.IsNontrivial :=
    Valuation.IsNontrivial.of_hasExtension vB vE
  let : ValuativeRel.IsNontrivial E :=
    (ValuativeRel.isNontrivial_iff_isNontrivial vE).2 inferInstance
  let : IsValuativeTopology E :=
    isValuativeTopology_of_valued_ofValuation E ℝ≥0
  let : IsNonarchimedeanLocalField E :=
    { toIsValuativeTopology := inferInstance
      toLocallyCompactSpace := inferInstance
      toIsNontrivial := inferInstance }
  let : Algebra 𝒪[vK.Completion] E :=
    Algebra.ofSubsemiring 𝒪[vK.Completion]
  let : IsIntegralClosure 𝒪[E] 𝒪[vK.Completion] E :=
    localizedCompletionIsIntegralClosureWithExtension
      vK w hvK hvKna
  let : Module.Finite 𝒪[vK.Completion] 𝒪[E] :=
    integerRing_moduleFinite_of_isIntegralClosure
      vK.Completion E
  let e :=
    finitePlaceCompletionUnitsContinuousMulEquiv v₀
  have hxChosen :
      x ∈ chosenFinitePlaceLocalNormSubgroup
        (K := K) (L := L) v₀ := by
    rw [← finitePlaceLocalTensorNorm_range_eq_chosenLocalNormSubgroup
      (K := K) (L := L) v₀]
    exact hxNorm
  change
    x ∈ (localNormSubgroup vK.Completion E).map
      e.toMonoidHom at hxChosen
  rcases hxChosen with ⟨x₀, hx₀, hx₀map⟩
  have hx₀' :
      x₀ ∈ localNormSubgroup vK.Completion E :=
    hx₀
  rcases
      MonoidHom.mem_range.mp hx₀' with
    ⟨y, hy⟩
  have hx₀val :
      e x₀ = x :=
    hx₀map
  obtain ⟨x₀O, hx₀O⟩ :=
    exists_finitePlaceCompletionIntegerUnit_of_unitsEquiv_eq
      (K := K) v₀ x₀ x hx₀val hxUnit
  have hyValuation :
      v E (Additive.ofMul y) = 0 := by
    apply
      v_eq_zero_of_normUnits_eq_integerUnitsToFieldUnits
        vK.Completion E x₀O y
    exact hy.trans hx₀O.symm
  have hyValuationMap :
      valuationMap E (Additive.ofMul y) = 0 :=
    hyValuation
  let yO : 𝒪[E]ˣ :=
    integerUnitOfValuationMapZero E y hyValuationMap
  have hyO :
      integerUnitsToFieldUnits E yO = y :=
    integerUnitOfValuationMapZero_spec E y hyValuationMap
  have hyMem : (y : E) ∈ 𝒪[E] := by
    have hval :=
      congrArg (fun q : Eˣ => (q : E)) hyO
    rw [← hval]
    exact yO.val.property
  have hyInvMem :
      ((y⁻¹ : Eˣ) : E) ∈ 𝒪[E] := by
    have hInv :
        integerUnitsToFieldUnits E (yO⁻¹) = y⁻¹ := by
      rw [map_inv, hyO]
    have hval :=
      congrArg (fun q : Eˣ => (q : E)) hInv
    rw [← hval]
    exact (yO⁻¹).val.property
  have hyNorm : ‖(y : E)‖ ≤ 1 :=
    (localizedCompletion_mem_integers_iff_norm_le_one
      vK w hvKna (y : E)).1 hyMem
  have hyInvNorm : ‖((y⁻¹ : Eˣ) : E)‖ ≤ 1 :=
    (localizedCompletion_mem_integers_iff_norm_le_one
      vK w hvKna _).1 hyInvMem
  exact ⟨x₀, y, hy, hx₀val, hyNorm, hyInvNorm⟩

omit [NumberField L] in
theorem exists_singleFinitePlaceIntegralUnit_norm_eq
    (v₀ : HeightOneSpectrum (𝓞 K))
    (x : (v₀.adicCompletion K)ˣ)
    (hxNorm :
      x ∈ (_root_.localTensorNorm
        (K := K) (L := L) v₀).range)
    (hxUnit :
      x ∈ (v₀.adicCompletionIntegers K).units) :
    let vK := HeightOneSpectrum.adicAbv K v₀
    let w := chosenFinitePlaceExtension (L := L) v₀
    let hvKna : IsNonarchimedean (vK : K → ℝ) :=
      HeightOneSpectrum.isNonarchimedean_adicAbv K v₀
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI : Algebra vK.Completion w.1.Completion :=
      AbsoluteValue.completionAlgebra vK w.1 w.2
    ∃ x₀ : vK.Completionˣ,
      ∃ yO :
          (absoluteValueCompletionIntegers w.1
            (absoluteValueExtension_isNonarchimedean
              vK hvKna w))ˣ,
        Algebra.norm vK.Completion
            ((Units.map
              (absoluteValueCompletionIntegers w.1
                (absoluteValueExtension_isNonarchimedean
                  vK hvKna w)).subtype yO :
                w.1.Completionˣ) :
              w.1.Completion) =
            (x₀ : vK.Completion) ∧
          finitePlaceCompletionUnitsContinuousMulEquiv v₀ x₀ = x := by
  classical
  let vK := HeightOneSpectrum.adicAbv K v₀
  let w := chosenFinitePlaceExtension (L := L) v₀
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v₀
  let hvKna : IsNonarchimedean (vK : K → ℝ) :=
    HeightOneSpectrum.isNonarchimedean_adicAbv K v₀
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  let E := LocalizedCompletion vK w
  obtain ⟨x₀, y, hy, hx₀val, hyNorm, hyInvNorm⟩ :=
    exists_localizedCompletionNormPreimage_with_norm_bounds
      (K := K) (L := L) v₀ x hxNorm hxUnit
  obtain ⟨yO, hyO⟩ :=
    exists_absoluteValueCompletionIntegerUnit_of_localizedCompletion_norm_bounds
      (K := K) (L := L) vK hvK hvKna w y hyNorm hyInvNorm
  let eW :=
    localizedCompletionEquivCompletion vK hvK w
  have hNormTransport :
      Algebra.norm vK.Completion
          ((y : E) : w.1.Completion) =
        (x₀ : vK.Completion) := by
    change
      Algebra.norm vK.Completion
          (eW (y : E)) =
        (x₀ : vK.Completion)
    rw [Algebra.norm_eq_of_algEquiv eW]
    exact congrArg Units.val hy
  have hNorm :
      Algebra.norm vK.Completion
          ((Units.map
            (absoluteValueCompletionIntegers w.1
              (absoluteValueExtension_isNonarchimedean
                vK hvKna w)).subtype yO :
              w.1.Completionˣ) :
            w.1.Completion) =
        (x₀ : vK.Completion) := by
    calc
      _ = Algebra.norm vK.Completion
          ((y : E) : w.1.Completion) :=
        congrArg (Algebra.norm vK.Completion) hyO
      _ = (x₀ : vK.Completion) := hNormTransport
  exact ⟨x₀, yO, hNorm, hx₀val⟩

omit [NumberField L] in
/-- A local integer unit in the finite tensor-norm image has a preimage
which is integral, together with its inverse, in every factor of the
canonical local tensor decomposition. -/
theorem exists_localTensorDecompositionIntegralUnit_localTensorNorm_eq
    (v₀ : HeightOneSpectrum (𝓞 K))
    (x : (v₀.adicCompletion K)ˣ)
    (hxNorm :
      x ∈ (_root_.localTensorNorm
        (K := K) (L := L) v₀).range)
    (hxUnit :
      x ∈ (v₀.adicCompletionIntegers K).units) :
    ∃ z : (v₀.adicCompletion K ⊗[K] L)ˣ,
      _root_.localTensorNorm
          (K := K) (L := L) v₀ z = x ∧
        RelativeLocalTensorDecompositionIntegralUnitAt
          (K := K) (L := L) v₀ z := by
  classical
  let vK := HeightOneSpectrum.adicAbv K v₀
  let w := chosenFinitePlaceExtension (L := L) v₀
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v₀
  let hvKna : IsNonarchimedean (vK : K → ℝ) :=
    HeightOneSpectrum.isNonarchimedean_adicAbv K v₀
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  obtain ⟨x₀, yWO, hNorm, hx₀val⟩ :=
    exists_singleFinitePlaceIntegralUnit_norm_eq
      (K := K) (L := L) v₀ x hxNorm hxUnit
  let z : (v₀.adicCompletion K ⊗[K] L)ˣ :=
    singleRelativeLocalTensorDecompositionIntegralUnit
      (K := K) (L := L) v₀ w yWO
  have hzIntegral :
      RelativeLocalTensorDecompositionIntegralUnitAt
        (K := K) (L := L) v₀ z :=
    singleRelativeLocalTensorDecompositionIntegralUnit_isIntegral
      (K := K) (L := L) v₀ w yWO
  refine ⟨z, ?_, hzIntegral⟩
  let zA :
      (LocalTensorAlgebra (L := L) vK)ˣ :=
    (finitePlaceLocalTensorUnitsEquiv
      (K := K) (L := L) v₀).symm z
  have hTensorNormSingle :
      localTensorDetNorm
          (K := K) (L := L) vK
          ((finitePlaceLocalTensorUnitsEquiv
            (K := K) (L := L) v₀).symm
            (singleRelativeLocalTensorDecompositionIntegralUnit
              (K := K) (L := L) v₀ w yWO)) =
        x₀ :=
      localTensorDetNorm_singleRelativeLocalTensorDecompositionIntegralUnit_eq
        (K := K) (L := L) v₀ w yWO x₀ hNorm
  have hTensorNorm :
      localTensorDetNorm
          (K := K) (L := L) vK zA = x₀ := by
    simpa only [zA, z] using hTensorNormSingle
  let e :=
    finitePlaceCompletionUnitsContinuousMulEquiv v₀
  calc
    _root_.localTensorNorm
        (K := K) (L := L) v₀ z =
      _root_.localTensorNorm
          (K := K) (L := L) v₀
          (finitePlaceLocalTensorUnitsEquiv
            (K := K) (L := L) v₀ zA) := by
        congr 1
        exact
          ((finitePlaceLocalTensorUnitsEquiv
            (K := K) (L := L) v₀).apply_symm_apply z).symm
    _ =
      e
        (localTensorDetNorm
          (K := K) (L := L) vK zA) :=
      (finitePlaceLocalTensorNorm_commutes
        (K := K) (L := L) v₀ zA).symm
    _ = e x₀ := congrArg e hTensorNorm
    _ = x := hx₀val
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Norm
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
attribute [-simp] _root_.IdeleGroup.extension_finiteComponent _root_.IdeleGroup.extension_principalIdele _root_.IdeleGroup.extension_self _root_.IdeleGroup.norm_principalIdele _root_.IdeleGroup.norm_relativeIdeleBaseChangeMulEquiv _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RelativeIdeleGroup.classEmbedding_mk _root_.relativeAdeleMapOfCompatibleEquiv_tmul _root_.adeleToRelativeAdele_finiteComponent _root_.adeleToRelativeAdele_infiniteComponent _root_.ideleClassCongr_mk _root_.ideleClassExtension_mk _root_.ideleClassExtension_self _root_.ideleClassNorm_mk _root_.ideleCongr_finiteComponent _root_.ideleCongr_principalIdele _root_.ordinaryIdeleClassNorm_relativeIdeleClassBaseChange _root_.relativeAdeleBaseChangeRingEquiv_finiteComponent_tmul _root_.relativeAdeleBaseChangeRingEquiv_infiniteComponent_tmul _root_.relativeAdeleCongr_tmul _root_.relativeAdeleToAdele_finite _root_.relativeAdeleToAdele_infinite _root_.relativeIdeleBaseChangeMulEquiv_principalIdele _root_.relativeIdeleClassBaseChangeMulEquiv_classInclusion _root_.relativeIdeleClassBaseChangeMulEquiv_mk _root_.relativeIdeleClassCongr_ideleClassNorm _root_.relativeIdeleClassCongr_mk _root_.relativeIdeleCongr_coe _root_.relativeIdeleCongr_norm _root_.relativeIdeleCongr_principalIdele _root_.towerActualRelativeAdeleRingEquiv_tmul _root_.towerRelativeIdeleBaseChangeMulEquiv_principalIdele _root_.towerRelativeIdeleClassBaseChangeMulEquiv_mk _root_.towerRelativeIdeleViaOrdinaryMulEquiv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Absolute and relative norms of ideles

This module exposes the absolute norm on the idele group and assembles
compatible local determinant-norm preimages into a global relative idele.
-/

open scoped NumberField TensorProduct RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section


variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

omit [NumberField L] [IsGalois K L] in
/-- Assemble compatible local determinant-norm preimages into an actual
relative idele.  The only restricted-product input is simultaneous
basis-integrality of the finite preimage and its inverse at almost every
finite place. -/
theorem exists_relativeIdele_norm_eq_of_localTensorPreimages
    (a : IdeleGroup K)
    (zInfinite :
      ∀ w : InfinitePlace K,
        (w.Completion ⊗[K] L)ˣ)
    (zFinite :
      ∀ w : HeightOneSpectrum (𝓞 K),
        (w.adicCompletion K ⊗[K] L)ˣ)
    (hInfinite :
      ∀ w : InfinitePlace K,
        infiniteTensorDetNorm (K := K) (L := L) w
            (zInfinite w) =
          IdeleGroup.infiniteComponent w a)
    (hFinite :
      ∀ w : HeightOneSpectrum (𝓞 K),
        _root_.localTensorNorm
            (K := K) (L := L) w (zFinite w) =
          IdeleGroup.finiteComponent w a)
    (hIntegral :
      ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
        RelativeBasisIntegralUnitAt
          (K := K) (L := L) w (zFinite w)) :
    ∃ z : RelativeIdeleGroup K L,
      RelativeIdeleGroup.norm K L z = a := by
  let d : RelativeLocalIdeleData (K := K) (L := L) :=
    { infinite := zInfinite
      finite := zFinite
      eventually_integral := fun i =>
        hIntegral.mono fun w hw =>
          relativeBasisIntegralAt_repr_mem
            (K := K) (L := L) w _ hw.1 i
      eventually_inverse_integral := fun i =>
        hIntegral.mono fun w hw =>
          relativeBasisIntegralAt_repr_mem
            (K := K) (L := L) w _ hw.2 i }
  refine
    ⟨relativeIdeleOfLocalData (K := K) (L := L) d, ?_⟩
  apply Prod.ext
  · apply ContinuousMulEquiv.piUnits.injective
    funext w
    change
      IdeleGroup.infiniteComponent w
          (RelativeIdeleGroup.norm K L
            (relativeIdeleOfLocalData
              (K := K) (L := L) d)) =
        IdeleGroup.infiniteComponent w a
    rw [RelativeIdeleGroup.infiniteComponent_norm,
      relativeIdeleOfLocalData_infiniteComponent]
    exact hInfinite w
  · apply RestrictedProduct.ext
    intro w
    change
      IdeleGroup.finiteComponent w
          (RelativeIdeleGroup.norm K L
            (relativeIdeleOfLocalData
              (K := K) (L := L) d)) =
        IdeleGroup.finiteComponent w a
    rw [RelativeIdeleGroup.finiteComponent_norm,
      relativeIdeleOfLocalData_finiteComponent]
    exact hFinite w

omit [NumberField L] [IsGalois K L] in
/-- Membership in every local norm image, together with a restricted
choice of finite local preimages, implies membership in the image of the
global relative-idele norm. -/
theorem idele_mem_relativeNorm_range_of_localNorms_with_integralPreimages
    (a : IdeleGroup K)
    (hInfinite :
      ∀ w : InfinitePlace K,
        IdeleGroup.infiniteComponent w a ∈
          infiniteTensorNormSubgroup
            (K := K) (L := L) w)
    (zFinite :
      ∀ w : HeightOneSpectrum (𝓞 K),
        (w.adicCompletion K ⊗[K] L)ˣ)
    (hFinite :
      ∀ w : HeightOneSpectrum (𝓞 K),
        _root_.localTensorNorm
            (K := K) (L := L) w (zFinite w) =
          IdeleGroup.finiteComponent w a)
    (hIntegral :
      ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
        RelativeBasisIntegralUnitAt
          (K := K) (L := L) w (zFinite w)) :
    a ∈ (RelativeIdeleGroup.norm K L).range := by
  have hInfinite' :
      ∀ w : InfinitePlace K,
        ∃ z : (w.Completion ⊗[K] L)ˣ,
          infiniteTensorDetNorm (K := K) (L := L) w z =
            IdeleGroup.infiniteComponent w a := by
    intro w
    simpa [infiniteTensorNormSubgroup] using hInfinite w
  choose zInfinite hNorm using hInfinite'
  obtain ⟨z, hz⟩ :=
    exists_relativeIdele_norm_eq_of_localTensorPreimages
      (K := K) (L := L) a zInfinite zFinite hNorm hFinite hIntegral
  exact ⟨z, hz⟩

omit [NumberField L] [IsGalois K L] in
/-- Every global relative-idele norm belongs to each finite local
determinant-norm image. -/
theorem finiteComponent_mem_localTensorNorm_range_of_mem_relativeNorm_range
    (a : IdeleGroup K)
    (ha : a ∈ (RelativeIdeleGroup.norm K L).range)
    (w : HeightOneSpectrum (𝓞 K)) :
    IdeleGroup.finiteComponent w a ∈
      (_root_.localTensorNorm
        (K := K) (L := L) w).range := by
  obtain ⟨z, rfl⟩ := ha
  exact
    ⟨RelativeIdeleGroup.finiteComponent
        (K := K) (L := L) w z,
      (RelativeIdeleGroup.finiteComponent_norm
        (K := K) (L := L) w z).symm⟩

omit [NumberField L] [IsGalois K L] in
/-- Every global relative-idele norm belongs to each infinite local
determinant-norm image. -/
theorem infiniteComponent_mem_infiniteTensorNormSubgroup_of_mem_relativeNorm_range
    (a : IdeleGroup K)
    (ha : a ∈ (RelativeIdeleGroup.norm K L).range)
    (w : InfinitePlace K) :
    IdeleGroup.infiniteComponent w a ∈
      infiniteTensorNormSubgroup
        (K := K) (L := L) w := by
  obtain ⟨z, rfl⟩ := ha
  exact
    ⟨RelativeIdeleGroup.infiniteComponent
        (K := K) (L := L) w z,
      (RelativeIdeleGroup.infiniteComponent_norm
        (K := K) (L := L) w z).symm⟩

/-- **Local-to-global norm criterion for ideles.**  An idele is an
actual global relative-idele norm if and only if all of its finite and
infinite components belong to the corresponding determinant-norm
images.  The restrictedness of the global preimage is automatic: at the
cofinitely many places where the given idele is a local integer unit, the
finite local preimage is chosen valuation-integral and is therefore
basis-integral away from the fixed discriminant support. -/
theorem mem_relativeIdeleNorm_range_iff_localTensorNorms
    (a : IdeleGroup K) :
    a ∈ (RelativeIdeleGroup.norm K L).range ↔
      (∀ w : InfinitePlace K,
        IdeleGroup.infiniteComponent w a ∈
          infiniteTensorNormSubgroup
            (K := K) (L := L) w) ∧
      (∀ w : HeightOneSpectrum (𝓞 K),
        IdeleGroup.finiteComponent w a ∈
          (_root_.localTensorNorm
            (K := K) (L := L) w).range) := by
  constructor
  · intro ha
    exact
      ⟨fun w =>
          infiniteComponent_mem_infiniteTensorNormSubgroup_of_mem_relativeNorm_range
            (K := K) (L := L) a ha w,
        fun w =>
          finiteComponent_mem_localTensorNorm_range_of_mem_relativeNorm_range
            (K := K) (L := L) a ha w⟩
  · rintro ⟨hInfinite, hFinite⟩
    have hChoice :
        ∀ w : HeightOneSpectrum (𝓞 K),
          ∃ z : (w.adicCompletion K ⊗[K] L)ˣ,
            _root_.localTensorNorm
                (K := K) (L := L) w z =
              IdeleGroup.finiteComponent w a ∧
            (IdeleGroup.finiteComponent w a ∈
                (w.adicCompletionIntegers K).units →
              RelativeLocalTensorDecompositionIntegralUnitAt
                (K := K) (L := L) w z) := by
      intro w
      by_cases hwUnit :
          IdeleGroup.finiteComponent w a ∈
            (w.adicCompletionIntegers K).units
      · obtain ⟨z, hz, hzIntegral⟩ :=
          exists_localTensorDecompositionIntegralUnit_localTensorNorm_eq
            (K := K) (L := L) w
            (IdeleGroup.finiteComponent w a)
            (hFinite w) hwUnit
        exact ⟨z, hz, fun _ => hzIntegral⟩
      · obtain ⟨z, hz⟩ := hFinite w
        exact ⟨z, hz, fun h => (hwUnit h).elim⟩
    choose zFinite hFiniteNorm hFiniteIntegral using hChoice
    have hEventuallyUnit :
        ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
          IdeleGroup.finiteComponent w a ∈
            (w.adicCompletionIntegers K).units := by
      simpa [IdeleGroup.finiteComponent_apply] using
        FiniteIdeleGroup.eventually_mem_localUnits a.2
    have hIntegral :
        ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
          RelativeBasisIntegralUnitAt
            (K := K) (L := L) w (zFinite w) := by
      filter_upwards [
        hEventuallyUnit,
        (integralTensorComparisonBadPlaces
          (K := K) (L := L)).eventually_cofinite_notMem] with
          w hwUnit hwBad
      exact
        localTensorDecompositionIntegralUnit_imp_relativeBasisIntegralUnitAt_of_notMem
          (K := K) (L := L) w hwBad
          (hFiniteIntegral w hwUnit)
    exact
      idele_mem_relativeNorm_range_of_localNorms_with_integralPreimages
        (K := K) (L := L) a hInfinite zFinite hFiniteNorm hIntegral
end
end

section
-- module Solutions.OAIQ244_DUKE.KummerTheory_Concrete_SUnitPreparation_EnlargedSUnitRestriction
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.chosenFinitePlaceCompletionAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option synthInstance.maxHeartbeats 400000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Restriction from an enlarged S-unit Kummer extension

The concrete embedding and Galois restriction map, its fixing subgroup, and the cyclic fixed fields attached to kernel elements.
-/

open scoped NumberField Classical IsMulCommutative NNReal ValuativeRel
open NumberField IsDedekindDomain
open LocalFieldTheory

noncomputable section

namespace KummerTheory

variable {K : Type*} [Field K]
    [numberFieldK : NumberField K]

/-- The actual embedded copy of `E` inside the full `S`-unit Kummer
extension `N`. -/
noncomputable def enlargedSUnitKummerEmbeddedExtension
    {Omega : Type*} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hexponent : ∀ sigma : Gal(E/K), sigma ^ (n : ℕ) = 1)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    IntermediateField K
      (fullSUnitKummerExtension
        (K := K) (Omega := Omega) n
        (enlargeByFiniteKummerRadicalSupport
          (K := K) (L := E) n hmu S)) := by
  let N :=
    fullSUnitKummerExtension
      (K := K) (Omega := Omega) n
      (enlargeByFiniteKummerRadicalSupport
        (K := K) (L := E) n hmu S)
  let : Algebra E N :=
    enlargedSUnitKummerAlgebra
      (K := K) (Omega := Omega) E n hmu hexponent S
  let : IsScalarTower K E N := by infer_instance
  exact (IsScalarTower.toAlgHom K E N).fieldRange

/-- The relative degree of `N/N_sigma` is the order of `sigma`. -/
theorem enlargedSUnitKummerCyclicFixedField_finrank
    {Omega : Type*} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hexponent : ∀ sigma : Gal(E/K), sigma ^ (n : ℕ) = 1)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (sigma :
      (enlargedSUnitKummerRestrictionHom
        (K := K) (Omega := Omega) E n hmu
        hexponent S).ker) :
    Module.finrank
        (enlargedSUnitKummerCyclicFixedField
          (K := K) (Omega := Omega) E n hmu
          hexponent S sigma)
        (fullSUnitKummerExtension
          (K := K) (Omega := Omega) n
          (enlargeByFiniteKummerRadicalSupport
            (K := K) (L := E) n hmu S)) =
      orderOf
        (sigma :
          Gal(fullSUnitKummerExtension
            (K := K) (Omega := Omega) n
            (enlargeByFiniteKummerRadicalSupport
              (K := K) (L := E) n hmu S)/K)) := by
  let S' :=
    enlargeByFiniteKummerRadicalSupport
      (K := K) (L := E) n hmu S
  let N :=
    fullSUnitKummerExtension
      (K := K) (Omega := Omega) n S'
  have hnK : ((n : ℕ) : K) ≠ 0 := by
    exact_mod_cast n.ne_zero
  let : FiniteDimensional K N :=
    fullSUnitKummerExtension_finiteDimensional
      (K := K) (Omega := Omega) n hnK hmu S'
  change
    Module.finrank
        (IntermediateField.fixedField
          (Subgroup.zpowers (sigma : Gal(N/K)))) N =
      orderOf (sigma : Gal(N/K))
  rw [IntermediateField.finrank_fixedField_eq_card,
    Nat.card_zpowers]

end KummerTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.KummerTheory_Concrete_SUnitPreparation_Core
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.DegreeData.finiteReciprocityNaturalityFiniteAbstractConjugate_normal _root_.ClassFormation.DegreeData.finiteReciprocityNaturalityFiniteResidueConjugate_normal _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.abelianIntermediateField_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteIntermediateField.galoisRefinement_normal _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalClassFieldTheory.localDecompositionResidueFinite _root_.LocalClassFieldTheory.localDecompositionResidueFintype _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.chosenFinitePlaceCompletionAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Rank and kernel coordinates for S-unit preparation

The endpoint of the S-unit preparation construction: the rank bound, the exact restriction-kernel cardinality, and prime-power coordinates.
-/

open scoped NumberField Classical IsMulCommutative NNReal ValuativeRel
open NumberField IsDedekindDomain
open LocalFieldTheory

noncomputable section

namespace KummerTheory

variable {K : Type*} [Field K]
    [numberFieldK : NumberField K]

/-- The cardinal comparison in the finite S-unit preparation argument: if
`Gal(E/K) ≃ (Z/nZ)^r`, then `r ≤ s` for the source-produced enlarged
set of places. -/
theorem galoisRank_le_totalPlaceCard_enlargedS
    {Omega : Type*} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+) (hn : 1 < (n : ℕ))
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (r : ℕ)
    (eG :
      Gal(E/K) ≃*
        (Fin r → Multiplicative (ZMod (n : ℕ))))
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    r ≤
      totalPlaceCard (K := K)
        (enlargeByFiniteKummerRadicalSupport
          (K := K) (L := E) n hmu S) := by
  let S' :=
    enlargeByFiniteKummerRadicalSupport
      (K := K) (L := E) n hmu S
  let N :=
    fullSUnitKummerExtension
      (K := K) (Omega := Omega) n S'
  have hnK : ((n : ℕ) : K) ≠ 0 := by
    exact_mod_cast n.ne_zero
  let : IsGalois K N :=
    fullSUnitKummerExtension_isGalois
      (K := K) (Omega := Omega) n S'
  let : Finite Gal(N/K) :=
    finite_fullSUnitKummerExtension_galois
      (K := K) (Omega := Omega) n hnK hmu S'
  have hcardE :
      Nat.card Gal(E/K) = (n : ℕ) ^ r := by
    rw [Nat.card_congr eG.toEquiv, Nat.card_pi]
    simp
  have hcardN :
      Nat.card Gal(N/K) =
        (n : ℕ) ^ totalPlaceCard (K := K) S' :=
    card_fullSUnitKummerExtension_galois
      (K := K) (Omega := Omega) n hnK hmu S'
  have hexponentE :
      ∀ sigma : Gal(E/K), sigma ^ (n : ℕ) = 1 :=
    galois_pow_eq_one_of_equiv_pi_zmod E n r eG
  have hcardLe :
      Nat.card Gal(E/K) ≤ Nat.card Gal(N/K) :=
    Nat.card_le_card_of_surjective
      (enlargedSUnitKummerRestrictionHom
        (K := K) (Omega := Omega) E n hmu
        hexponentE S)
      (enlargedSUnitKummerRestrictionHom_surjective
        (K := K) (Omega := Omega) E n hmu
        hexponentE S)
  rw [hcardE, hcardN] at hcardLe
  exact (Nat.pow_le_pow_iff_right hn).mp hcardLe

/-- The restriction kernel in the finite S-unit preparation argument has the expected
cardinality `n ^ (s - r)`.  Both fields and the restriction map are the
concrete objects constructed above. -/
theorem card_enlargedSUnitKummerRestrictionHom_ker
    {Omega : Type*} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+) (hn : 1 < (n : ℕ))
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (r : ℕ)
    (eG :
      Gal(E/K) ≃*
        (Fin r → Multiplicative (ZMod (n : ℕ))))
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Nat.card
        (enlargedSUnitKummerRestrictionHom
          (K := K) (Omega := Omega) E n hmu
          (galois_pow_eq_one_of_equiv_pi_zmod E n r eG)
          S).ker =
      (n : ℕ) ^
        (totalPlaceCard (K := K)
            (enlargeByFiniteKummerRadicalSupport
              (K := K) (L := E) n hmu S) - r) := by
  let S' :=
    enlargeByFiniteKummerRadicalSupport
      (K := K) (L := E) n hmu S
  let N :=
    fullSUnitKummerExtension
      (K := K) (Omega := Omega) n S'
  have hnK : ((n : ℕ) : K) ≠ 0 := by
    exact_mod_cast n.ne_zero
  let : IsGalois K N :=
    fullSUnitKummerExtension_isGalois
      (K := K) (Omega := Omega) n S'
  let : Finite Gal(N/K) :=
    finite_fullSUnitKummerExtension_galois
      (K := K) (Omega := Omega) n hnK hmu S'
  have hexponentE :
      ∀ sigma : Gal(E/K), sigma ^ (n : ℕ) = 1 :=
    galois_pow_eq_one_of_equiv_pi_zmod E n r eG
  let f : Gal(N/K) →* Gal(E/K) :=
    enlargedSUnitKummerRestrictionHom
      (K := K) (Omega := Omega) E n hmu hexponentE S
  have hf :
      Function.Surjective f :=
    enlargedSUnitKummerRestrictionHom_surjective
      (K := K) (Omega := Omega) E n hmu hexponentE S
  have hcardE :
      Nat.card Gal(E/K) = (n : ℕ) ^ r := by
    rw [Nat.card_congr eG.toEquiv, Nat.card_pi]
    simp
  have hcardN :
      Nat.card Gal(N/K) =
        (n : ℕ) ^ totalPlaceCard (K := K) S' :=
    card_fullSUnitKummerExtension_galois
      (K := K) (Omega := Omega) n hnK hmu S'
  have hquotient :
      Nat.card (Gal(N/K) ⧸ f.ker) =
        Nat.card Gal(E/K) :=
    Nat.card_congr
      (QuotientGroup.quotientKerEquivOfSurjective
        f hf).toEquiv
  have hfactor :
      (n : ℕ) ^ totalPlaceCard (K := K) S' =
        (n : ℕ) ^ r * Nat.card f.ker := by
    rw [← hcardN, ← hcardE, ← hquotient]
    exact
      Subgroup.card_eq_card_quotient_mul_card_subgroup
        f.ker
  have hr :
      r ≤ totalPlaceCard (K := K) S' :=
    galoisRank_le_totalPlaceCard_enlargedS
      (K := K) (Omega := Omega) E n hn hmu r eG S
  have hsplit :
      (n : ℕ) ^ totalPlaceCard (K := K) S' =
        (n : ℕ) ^ r *
          (n : ℕ) ^
            (totalPlaceCard (K := K) S' - r) := by
    rw [← pow_add, Nat.add_sub_of_le hr]
  have hcancel :
      (n : ℕ) ^ r * Nat.card f.ker =
        (n : ℕ) ^ r *
          (n : ℕ) ^
            (totalPlaceCard (K := K) S' - r) :=
    hfactor.symm.trans hsplit
  exact Nat.eq_of_mul_eq_mul_left
    (pow_pos n.pos r) hcancel

/-- In the prime-power case, the actual relative Galois group
`Gal(N/E)` is a free `ZMod n`-module of rank `s - r`.  This is the
concrete basis source used to choose the fields `N_i` in the finite S-unit preparation argument. -/
theorem
    exists_enlargedSUnitKummerRestrictionKernelEquivPiZMod
    {Omega : Type*} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (p v : ℕ) (hp : p.Prime) (hv : 0 < v)
    (hn : (n : ℕ) = p ^ v)
    (r : ℕ)
    (eG :
      Gal(E/K) ≃*
        (Fin r → Multiplicative (ZMod (n : ℕ))))
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Nonempty
      ((enlargedSUnitKummerRestrictionHom
          (K := K) (Omega := Omega) E n hmu
          (galois_pow_eq_one_of_equiv_pi_zmod E n r eG)
          S).ker ≃*
        (Fin
            (totalPlaceCard (K := K)
              (enlargeByFiniteKummerRadicalSupport
                (K := K) (L := E) n hmu S) - r) →
          Multiplicative (ZMod (n : ℕ)))) := by
  let S' :=
    enlargeByFiniteKummerRadicalSupport
      (K := K) (L := E) n hmu S
  let N :=
    fullSUnitKummerExtension
      (K := K) (Omega := Omega) n S'
  let G := Gal(N/K)
  let H := Gal(E/K)
  have hnK : ((n : ℕ) : K) ≠ 0 := by
    exact_mod_cast n.ne_zero
  have hnOne : 1 < (n : ℕ) := by
    rw [hn]
    calc
      1 < p := hp.one_lt
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ v :=
        Nat.pow_le_pow_right hp.pos
          (Nat.succ_le_iff.mpr hv)
  have hexponentE :
      ∀ sigma : H, sigma ^ (n : ℕ) = 1 :=
    galois_pow_eq_one_of_equiv_pi_zmod E n r eG
  let : IsGalois K N :=
    fullSUnitKummerExtension_isGalois
      (K := K) (Omega := Omega) n S'
  let : Finite G :=
    finite_fullSUnitKummerExtension_galois
      (K := K) (Omega := Omega) n hnK hmu S'
  let : IsMulCommutative G :=
    KummerTheory.kummerRadicalExtension_isMulCommutative
      n hmu (fullSUnitKummerSubgroup (K := K) n S').1
  let : Module (ZMod (n : ℕ)) (Additive G) :=
    additiveZModModuleOfPowEqOne (n : ℕ)
      (fullSUnitKummerExtension_galois_pow_eq_one
        (K := K) (Omega := Omega) n hmu S')
  let : Module (ZMod (n : ℕ)) (Additive H) :=
    additiveZModModuleOfPowEqOne (n : ℕ) hexponentE
  have hfreeG : Module.Free (ZMod (n : ℕ)) (Additive G) :=
    fullSUnitKummerExtension_galois_moduleFree
      (K := K) (Omega := Omega) n hnK hmu S'
  let eH :
      Additive H ≃ₗ[ZMod (n : ℕ)]
        (Fin r → ZMod (n : ℕ)) :=
    additivePiLinearEquiv (n : ℕ) eG
  have hfreeH : Module.Free (ZMod (n : ℕ)) (Additive H) :=
    Module.Free.of_equiv eH.symm
  let f : G →* H :=
    enlargedSUnitKummerRestrictionHom
      (K := K) (Omega := Omega) E n hmu
        hexponentE S
  have hf : Function.Surjective f :=
    enlargedSUnitKummerRestrictionHom_surjective
      (K := K) (Omega := Omega) E n hmu
        hexponentE S
  have hcard :
      Nat.card f.ker =
        (n : ℕ) ^
          (totalPlaceCard (K := K) S' - r) :=
    card_enlargedSUnitKummerRestrictionHom_ker
      (K := K) (Omega := Omega) E n hnOne
        hmu r eG S
  exact
    exists_kernelMulEquiv_pi_zmod_of_primePower
      (G := G) (H := H)
      (n : ℕ) p v
      (totalPlaceCard (K := K) S' - r)
      hp hv hn hfreeG hfreeH f hf hcard

/-- A chosen coordinate equivalence for the actual relative Galois
group in the finite S-unit preparation argument. -/
noncomputable def
    chosenEnlargedSUnitKummerRestrictionKernelEquivPiZMod
    {Omega : Type*} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (p v : ℕ) (hp : p.Prime) (hv : 0 < v)
    (hn : (n : ℕ) = p ^ v)
    (r : ℕ)
    (eG :
      Gal(E/K) ≃*
        (Fin r → Multiplicative (ZMod (n : ℕ))))
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (enlargedSUnitKummerRestrictionHom
        (K := K) (Omega := Omega) E n hmu
        (galois_pow_eq_one_of_equiv_pi_zmod E n r eG)
        S).ker ≃*
      (Fin
          (totalPlaceCard (K := K)
            (enlargeByFiniteKummerRadicalSupport
              (K := K) (L := E) n hmu S) - r) →
        Multiplicative (ZMod (n : ℕ))) :=
  Classical.choice
    (exists_enlargedSUnitKummerRestrictionKernelEquivPiZMod
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S)

end KummerTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_ClassFieldAxiom_SUnitKummerPrimeSelection_RestrictionKernel
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.chosenFinitePlaceCompletionAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Restriction kernels of S-unit Kummer extensions

This file specializes the chosen restriction-kernel coordinates of an
enlarged S-unit Kummer extension to coordinate generators, their required
number, and their cyclic fixed fields.
-/

open scoped NumberField Classical IsMulCommutative
open NumberField IsDedekindDomain
open KummerTheory

noncomputable section

namespace GlobalClassFieldTheory.ClassFieldAxiom

section GeneralKummer

variable {K : Type*} [Field K]
    [NumberField K]

/-- The `i`-th standard generator of the actual restriction kernel
`Gal(N/E)`. -/
noncomputable def sUnitKummerKernelGenerator
    {Omega : Type*} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (p v : ℕ) (hp : p.Prime) (hv : 0 < v)
    (hn : (n : ℕ) = p ^ v)
    (r : ℕ)
    (eG :
      Gal(E/K) ≃*
        (Fin r → Multiplicative (ZMod (n : ℕ))))
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (i : Fin
      (sUnitKummerPrimeCount
        (K := K) E n hmu r S)) :=
  (chosenEnlargedSUnitKummerRestrictionKernelEquivPiZMod
    (K := K) (Omega := Omega) E n hmu
    p v hp hv hn r eG S).symm
      (Pi.mulSingle i
        (Multiplicative.ofAdd (1 : ZMod (n : ℕ))))

/-- Every standard restriction-kernel generator has exact order `n`. -/
theorem orderOf_sUnitKummerKernelGenerator
    {Omega : Type*} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (p v : ℕ) (hp : p.Prime) (hv : 0 < v)
    (hn : (n : ℕ) = p ^ v)
    (r : ℕ)
    (eG :
      Gal(E/K) ≃*
        (Fin r → Multiplicative (ZMod (n : ℕ))))
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (i : Fin
      (sUnitKummerPrimeCount
        (K := K) E n hmu r S)) :
    orderOf
        (sUnitKummerKernelGenerator
          (K := K) (Omega := Omega) E n hmu
          p v hp hv hn r eG S i) =
      (n : ℕ) := by
  let e :=
    chosenEnlargedSUnitKummerRestrictionKernelEquivPiZMod
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S
  let I := Fin
    (totalPlaceCard (K := K)
      (enlargeByFiniteKummerRadicalSupport (K := K) (L := E) n hmu S) - r)
  let j : I := i
  let c : I → Multiplicative (ZMod (n : ℕ)) :=
    Pi.mulSingle j (Multiplicative.ofAdd (1 : ZMod (n : ℕ)))
  change orderOf (e.symm c) = (n : ℕ)
  have hone : orderOf (Multiplicative.ofAdd (1 : ZMod (n : ℕ))) = (n : ℕ) :=
    (orderOf_ofAdd_eq_addOrderOf (1 : ZMod (n : ℕ))).trans
      (ZMod.addOrderOf_one (n : ℕ))
  have hc : orderOf c = (n : ℕ) :=
    (orderOf_piMulSingle
      (M := fun _ : I => Multiplicative (ZMod (n : ℕ)))
      j (Multiplicative.ofAdd (1 : ZMod (n : ℕ)))).trans hone
  exact (e.symm.orderOf_eq c).trans hc

/-- The cyclic fixed field attached to the `i`-th coordinate of the
actual relative Galois group `Gal(N/E)`. -/
noncomputable def sUnitKummerCoordinateFixedField
    {Omega : Type*} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (p v : ℕ) (hp : p.Prime) (hv : 0 < v)
    (hn : (n : ℕ) = p ^ v)
    (r : ℕ)
    (eG :
      Gal(E/K) ≃*
        (Fin r → Multiplicative (ZMod (n : ℕ))))
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (i : Fin
      (sUnitKummerPrimeCount
        (K := K) E n hmu r S)) :=
  enlargedSUnitKummerCyclicFixedField
    (K := K) (Omega := Omega) E n hmu
    (galois_pow_eq_one_of_equiv_pi_zmod
      (K := K) E n r eG) S
    (sUnitKummerKernelGenerator
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S i)

/-- Each coordinate fixed field has relative degree exactly `n` in
the full `S`-unit Kummer field. -/
theorem sUnitKummerCoordinateFixedField_finrank
    {Omega : Type*} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (p v : ℕ) (hp : p.Prime) (hv : 0 < v)
    (hn : (n : ℕ) = p ^ v)
    (r : ℕ)
    (eG :
      Gal(E/K) ≃*
        (Fin r → Multiplicative (ZMod (n : ℕ))))
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (i : Fin
      (sUnitKummerPrimeCount
        (K := K) E n hmu r S)) :
    Module.finrank
        (sUnitKummerCoordinateFixedField
          (K := K) (Omega := Omega) E n hmu
          p v hp hv hn r eG S i)
        (fullSUnitKummerExtension
          (K := K) (Omega := Omega) n
          (enlargeByFiniteKummerRadicalSupport
            (K := K) (L := E) n hmu S)) =
      (n : ℕ) := by
  unfold sUnitKummerCoordinateFixedField
  rw [enlargedSUnitKummerCyclicFixedField_finrank
      (K := K) (Omega := Omega) E n hmu
      (galois_pow_eq_one_of_equiv_pi_zmod
        (K := K) E n r eG) S
      (sUnitKummerKernelGenerator
        (K := K) (Omega := Omega) E n hmu
        p v hp hv hn r eG S i),
    Subgroup.orderOf_coe,
    orderOf_sUnitKummerKernelGenerator
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S i]

end GeneralKummer

end GlobalClassFieldTheory.ClassFieldAxiom
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_FixedFieldLocalData
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Canonical local data on finite fixed fields

This file compares the normalized valuation induced on a finite abstract
field by the local class formation with the ordinary normalized valuation
of its concrete fixed field.  The concrete field is equipped with the
canonical spectral extension of the topology on the original local field.
-/

noncomputable section

namespace LocalClassFieldTheory

open scoped NNReal Pointwise ValuativeRel
open ClassFormation LocalFieldTheory RamificationTheory CyclicCohomology
open RamificationTheory.HilbertRamification.ValuationSubring

abbrev finiteFixedField
    (K : Type) [Field K]
    (H : FiniteAbstractField (Gal(SeparableClosure K / K))) :
    Type :=
  abstractFixedField K (SeparableClosure K) H.field

local instance finiteFixedFieldSeparableClosureAlgebra
    (K : Type) [Field K]
    (H : FiniteAbstractField (Gal(SeparableClosure K / K))) :
    Algebra (finiteFixedField K H)
      (SeparableClosure (finiteFixedField K H)) :=
  (separableClosure (finiteFixedField K H)
    (AlgebraicClosure (finiteFixedField K H))).algebra


end LocalClassFieldTheory
end
end


