-- Prove2me | Definitions.Def_OAIQ244Duke028
-- name    : OAIQ244Duke028
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T06:28:26.317207+00:00
-- url     : https://prove2.me/theorems/320ada04-6bfc-4774-94c0-2f8ff924ad98
-- title:
--   Definitions bundle OAIQ244Duke028 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 135 declarations of OpenAI's Lean: 49 definitions, 1 inductive type or structure, 2 instances and 83 theorems. The definitions and types are `CyclicCohomology.piHerbrandHMinusOneEquivProd`, `FiniteIdeleGroup.absoluteNorm`, `FiniteIdeleGroup.divisorNorm`, `FiniteIdeleGroup.integralStructureMap`, `FiniteIdeleGroup.primeNormPowerHom`, `FractionalIdealGroup.absoluteNorm`, `FractionalIdealGroup.extension`, `IdeleClassGroup.absoluteNorm`, `IdeleClassGroup.normOneSubgroup`, `IdeleGroup.absoluteNorm`, `IdeleGroup.normOneSubgroup`, `InfiniteIdeleGroup.archimedeanNorm`, `InfiniteIdeleGroup.logNorm`, `RayClass.IdealRayClassGroup`, `RayClass.Modulus`, `RayClass.Modulus.eraseRealPlace`, `RayClass.Modulus.eraseRealPlaces`, `RayClass.Modulus.ideleCongruenceSubgroup`, `RayClass.Modulus.infiniteCongruenceSubgroup`, `RayClass.Modulus.localInfiniteCongruenceSubgroup`, `RayClass.Modulus.narrowOfFinite`, `RayClass.Modulus.ofFinite`, `RayClass.Modulus.replaceFinitePart`, `RayClass.congruenceSubgroupInPrimeTo`, `RayClass.finiteCongruenceSubgroup`, `RayClass.finitePrimeToModulusSubgroup`, `RayClass.idealRayProjection`, `RayClass.idelePrimeToModulusSubgroup`, `RayClass.narrowInfiniteCongruenceSubgroup`, `RayClass.primeToIdealMap`, `RayClass.primeToModulusIdeal`, `RayClass.primeToModulusIdeals`, `RayClass.principalRayIdealSubgroup`, `RayClass.principalSubgroupInPrimeTo`, `RayClass.quotientRaySubgroupEquivIdealRayClassGroup`, `RayClass.raySubgroupInPrimeTo`, `RayClass.valuationVectorSectionPrimeTo`, `RelativeIdeleGroup.Cohomology.baseIdeleClassEquivFixed`, `RelativeIdeleGroup.Cohomology.baseIdeleClassToFixed`, `baseChangedRelativeAdeleMap` and 10 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `AlgebraicNumberTheory_Adele_Coordinates`, `AlgebraicNumberTheory_Adele_IntegralTensorSupport_Lattice`, `AlgebraicNumberTheory_Idele_ClassGroup_BaseChange`, `AlgebraicNumberTheory_Idele_ClassGroup_Core`, `AlgebraicNumberTheory_Idele_ClassGroup_Tower`, `AlgebraicNumberTheory_Idele_Cohomology_Herbrand`, `AlgebraicNumberTheory_Idele_Extension_IdealClass`, `AlgebraicNumberTheory_Idele_IdealMap`, `AlgebraicNumberTheory_Idele_NormCore`, `AlgebraicNumberTheory_Idele_NormOneCompact`, `AlgebraicNumberTheory_Idele_PrincipalNorm`, `AlgebraicNumberTheory_RayClass_Basic`, `AlgebraicNumberTheory_RayClass_FullModulus`, `AlgebraicNumberTheory_RayClass_Ideal`, `Cyclic_Herbrand_HerbrandLowDegree_BinaryProduct`, `Cyclic_Herbrand_HerbrandLowDegree_Index`, `LocalField_NonarchimedeanLocalField_FiniteExtensionCompleteDVF`, `Valuation_DiscreteValuationField_FiniteExtension_Degree`, `Valuation_DiscreteValuationField_FiniteExtension_Uniqueness`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke015`, `OAIQ244Duke016`, `OAIQ244Duke017` and `OAIQ244Duke018` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke038`, `OAIQ244Duke039`, `OAIQ244Duke040`, `OAIQ244Duke042`, `OAIQ244Duke043` and `OAIQ244Duke044`.
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
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
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
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.QuotientGroup.Finite
import Mathlib.GroupTheory.SpecificGroups.Cyclic
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
import Definitions.Def_OAIQ244Duke015
import Definitions.Def_OAIQ244Duke016
import Definitions.Def_OAIQ244Duke017
import Definitions.Def_OAIQ244Duke018

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Adele_Coordinates
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.principalQuotientAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Coordinate assembly for relative adeles

The chosen finite `K`-basis of `L` identifies
`𝔸_K ⊗[K] L` with a finite family of base adeles.  The support file
constructs and controls the forward coefficients; this file supplies the
inverse assembly map.  It is the global reconstruction half needed when
local tensor components have first been chosen place by place.
-/

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain

noncomputable section


universe u v

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

/-- A relative adele is linearly equivalent to its finite family of
base-adele coefficients in the chosen extension basis. -/
noncomputable def relativeAdeleCoefficientLinearEquiv :
    RelativeAdeleRing K L ≃ₗ[
      NumberField.AdeleRing (𝓞 K) K]
      (RelativeAdeleBasisIndex (K := K) (L := L) →
        NumberField.AdeleRing (𝓞 K) K) :=
  (relativeAdeleBasis (K := K) (L := L)).equivFun
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_ClassGroup_Tower
attribute [-instance] _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.principalQuotientAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.RelativeIdeleGroup.Cohomology.ideleClassNorm_mk _root_.RelativeIdeleGroup.Cohomology.ideleClass_smul_mk _root_.RelativeIdeleGroup.Cohomology.relativeIdele_smul_def _root_.RelativeIdeleGroup.finiteComponent_coe _root_.RelativeIdeleGroup.finiteComponent_inclusion _root_.RelativeIdeleGroup.finiteComponent_norm _root_.RelativeIdeleGroup.finiteComponent_principalIdele _root_.RelativeIdeleGroup.infiniteComponent_coe _root_.RelativeIdeleGroup.infiniteComponent_inclusion _root_.RelativeIdeleGroup.infiniteComponent_norm _root_.RelativeIdeleGroup.infiniteComponent_principalIdele _root_.RelativeIdeleGroup.scalarConjugation_baseAdele_apply _root_.RelativeIdeleGroup.smul_class_mk _root_.mem_relativeAdeleCoefficientSupport_iff _root_.mem_relativeIdeleCoefficientSupport_iff _root_.relativeAdeleFiniteComponent_tmul _root_.relativeAdeleInfiniteComponent_tmul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Idele-class norms in a field tower

For a tower `K ⊂ M ⊂ L`, keep the bottom field `K` fixed and write

`𝔸_M = 𝔸_K ⊗[K] M`,
`𝔸_L = (𝔸_K ⊗[K] M) ⊗[M] L`.

This gives an actual norm `C_L → C_M` whose composite with
`C_M → C_K` is the tower norm.  The resulting three concrete norm
quotients form a natural right-exact sequence.
-/

open scoped NumberField TensorProduct
open NumberField

noncomputable section

universe u

variable
    (K M L : Type u)
    [Field K] [NumberField K]
    [Field M] [NumberField M]
    [Field L] [NumberField L]
    [Algebra K M] [Algebra M L] [Algebra K L]
    [IsScalarTower K M L]
    [FiniteDimensional K M] [FiniteDimensional M L]

/-- The flattening equivalence as an equivalence over the bottom adele
ring.  This is the form needed for invariance of determinant norms. -/
def towerRelativeAdeleAlgEquiv :
    TowerRelativeAdeleRing K M L ≃ₐ[
      NumberField.AdeleRing (𝓞 K) K]
      RelativeAdeleRing K L :=
  { towerRelativeAdeleRingEquiv K M L with
    commutes' := by
      intro a
      change
        towerRelativeAdeleFlatten K M L
            ((a ⊗ₜ[K] (1 : M)) ⊗ₜ[M] (1 : L)) =
          a ⊗ₜ[K] (1 : L)
      simp }

namespace TowerRelativeIdeleGroup

attribute [local instance] instIsMulCommutativeTowerRelativeIdeleGroup
attribute [local instance] instIsMulCommutativeClassGroup
attribute [local instance] instIsMulCommutativeIdeleClassGroup
omit [NumberField M] [NumberField L] in
/-- Transitivity of determinant norms, after flattening the tower
presentation to the one-step presentation. -/
theorem norm_transitive_flatten
    (a : TowerRelativeIdeleGroup K M L) :
    RelativeIdeleGroup.norm K M (norm K M L a) =
      RelativeIdeleGroup.norm K L
        (towerRelativeIdeleEquiv K M L a) := by
  apply
    (IdeleGroup.equivAdeleRingUnits (K := K)).injective
  apply Units.ext
  change
    Algebra.norm (NumberField.AdeleRing (𝓞 K) K)
        (Algebra.norm (RelativeAdeleRing K M)
          (a : TowerRelativeAdeleRing K M L)) =
      Algebra.norm (NumberField.AdeleRing (𝓞 K) K)
        (towerRelativeAdeleFlatten K M L
          (a : TowerRelativeAdeleRing K M L))
  calc
    _ = Algebra.norm (NumberField.AdeleRing (𝓞 K) K)
          (a : TowerRelativeAdeleRing K M L) :=
      Algebra.norm_norm
    _ = _ :=
      (Algebra.norm_eq_of_algEquiv
        (towerRelativeAdeleAlgEquiv K M L)
        (a : TowerRelativeAdeleRing K M L)).symm

end TowerRelativeIdeleGroup

section NormQuotientSequence

attribute [local instance] instIsMulCommutativeTowerRelativeIdeleGroup
attribute [local instance] instIsMulCommutativeClassGroup
attribute [local instance] instIsMulCommutativeIdeleClassGroup
omit [NumberField M] in
/-- After identifying the tower presentation with the one-step
presentation, the composite tower norm is the ordinary class norm from
`L` to `K`. -/
theorem towerCompositeClassNorm_eq_ideleClassNorm
    (c : TowerRelativeIdeleGroup.ClassGroup K M L) :
    towerCompositeClassNorm K M L c =
      RelativeIdeleGroup.classNorm K L
        (TowerRelativeIdeleGroup.classGroupEquiv K M L c) := by
  refine QuotientGroup.induction_on c ?_
  intro a
  simp only [towerCompositeClassNorm, MonoidHom.comp_apply]
  exact congrArg
    (QuotientGroup.mk'
      (IdeleGroup.principalSubgroup K))
    (TowerRelativeIdeleGroup.norm_transitive_flatten K M L a)

end NormQuotientSequence
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_ClassGroup_BaseChange
attribute [-instance] _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.principalQuotientAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.FiniteIdeleGroup.mem_integralSubgroup_iff _root_.FiniteIdeleGroup.mem_supportedAt_iff _root_.FiniteIdeleGroup.valuationVectorAdd_apply _root_.FiniteIdeleGroup.valuationVector_apply _root_.FiniteIdeleGroup.valuationVector_valuationVectorSection _root_.IdeleGroup.finiteComponentContinuous_apply _root_.IdeleGroup.infiniteComponentContinuous_apply _root_.IdeleGroup.mem_supportedAt_iff _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.RelativeIdeleGroup.Cohomology.ideleClassNorm_mk _root_.RelativeIdeleGroup.Cohomology.ideleClass_smul_mk _root_.RelativeIdeleGroup.Cohomology.relativeIdele_smul_def _root_.RelativeIdeleGroup.smul_class_mk _root_.mem_relativeAdeleCoefficientSupport_iff _root_.mem_relativeIdeleCoefficientSupport_iff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Base change of idele-class norms along a pushout square

For a pushout square of finite extensions

```
K  ─→  M
│       │
↓       ↓
L  ─→  N
```

this file constructs the maps on relative ideles and idele classes
that occur after adjoining roots of unity.
Keeping the bottom adele ring fixed makes the norm square an actual
determinant-norm base-change identity.
-/

open scoped NumberField TensorProduct
open NumberField

noncomputable section

universe u

variable
    (K M L N : Type u)
    [Field K] [NumberField K]
    [Field M] [NumberField M]
    [Field L] [NumberField L]
    [Field N] [NumberField N]
    [Algebra K M] [Algebra K L]
    [Algebra M N] [Algebra L N] [Algebra K N]
    [IsScalarTower K M N] [IsScalarTower K L N]
    [Algebra.IsPushout K M L N]
    [FiniteDimensional K M] [FiniteDimensional K L]
    [FiniteDimensional M N] [FiniteDimensional L N]

-- These canonical commutativity proofs are local to the imported tower
-- module; retain them here for the quotient-group instances.
local instance instIsMulCommutativeTowerRelativeIdeleGroup_1 (A B C : Type u) [Field A] [NumberField A]
    [Field B] [Field C] [Algebra A B] [Algebra B C] :
    IsMulCommutative (TowerRelativeIdeleGroup A B C) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

local instance instIsMulCommutativeClassGroup_1 (A B : Type u) [Field A] [NumberField A]
    [Field B] [Algebra A B] :
    IsMulCommutative (RelativeIdeleGroup.ClassGroup A B) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

local instance instIsMulCommutativeIdeleClassGroup_1 (A : Type u) [Field A] [NumberField A] :
    IsMulCommutative (IdeleClassGroup A) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

/-- For a pushout `N = M ⊗[K] L`, the tower presentation

`(𝔸_K ⊗[K] M) ⊗[M] N`

is canonically the scalar extension

`(𝔸_K ⊗[K] M) ⊗[K] L`.
-/
def pushoutTowerAdeleEquiv :
    TowerRelativeAdeleRing K M N ≃ₐ[
      RelativeAdeleRing K M]
      BaseChangedRelativeAdeleRing K M L := by
  letI : Algebra N (TowerRelativeAdeleRing K M N) :=
    Algebra.TensorProduct.rightAlgebra
  letI : Algebra L (BaseChangedRelativeAdeleRing K M L) :=
    Algebra.TensorProduct.rightAlgebra
  letI : Algebra.IsPushout K L M N :=
    Algebra.IsPushout.symm
      (inferInstance : Algebra.IsPushout K M L N)
  let e₁ :=
    (Algebra.TensorProduct.commRight
      M N (RelativeAdeleRing K M)).symm
  let e₂ :=
    Algebra.IsPushout.cancelBaseChangeAlg
      K L M N (RelativeAdeleRing K M)
  let e₃ :=
    Algebra.TensorProduct.commRight
      K L (RelativeAdeleRing K M)
  refine
    { e₁.toRingEquiv.trans
        (e₂.toRingEquiv.trans e₃.toRingEquiv) with
      commutes' := ?_ }
  intro a
  simp [e₁, e₂, e₃]

/-- Scalar extension of coefficients from the bottom adele ring to
`𝔸_K ⊗[K] M`, while retaining the top field `L`. -/
def baseChangedRelativeAdeleMap :
    RelativeAdeleRing K L →ₐ[K]
      BaseChangedRelativeAdeleRing K M L :=
  Algebra.TensorProduct.map
    (Algebra.TensorProduct.includeLeft
      (R := K) (S := K)
      (A := NumberField.AdeleRing (𝓞 K) K) (B := M))
    (AlgHom.id K L)

/-- Inclusion from the relative adeles of `L/K` to the tower
presentation of the relative adeles of `N/M`, induced by the pushout
square. -/
def pushoutTowerAdeleInclusion :
    RelativeAdeleRing K L →+*
      TowerRelativeAdeleRing K M N :=
  (pushoutTowerAdeleEquiv K M L N).symm.toRingHom.comp
    (baseChangedRelativeAdeleMap K M L).toRingHom

omit [NumberField M] [NumberField L] [NumberField N]
    [FiniteDimensional K M] [FiniteDimensional K L]
    [FiniteDimensional M N] [FiniteDimensional L N] in
@[simp]
theorem pushoutTowerAdeleInclusion_tmul
    (a : NumberField.AdeleRing (𝓞 K) K)
    (x : L) :
    pushoutTowerAdeleInclusion K M L N (a ⊗ₜ[K] x) =
      (a ⊗ₜ[K] (1 : M)) ⊗ₜ[M]
        algebraMap L N x := by
  let : Algebra N (RelativeAdeleRing K M ⊗[M] N) :=
    Algebra.TensorProduct.rightAlgebra
  let : Algebra L (RelativeAdeleRing K M ⊗[K] L) :=
    Algebra.TensorProduct.rightAlgebra
  have : Algebra.IsPushout K L M N :=
    Algebra.IsPushout.symm
      (inferInstance : Algebra.IsPushout K M L N)
  change
    Algebra.TensorProduct.commRight M N (RelativeAdeleRing K M)
        ((Algebra.IsPushout.cancelBaseChangeAlg
          K L M N (RelativeAdeleRing K M)).symm
          ((Algebra.TensorProduct.commRight
            K L (RelativeAdeleRing K M)).symm
            ((a ⊗ₜ[K] (1 : M)) ⊗ₜ[K] x))) =
      (a ⊗ₜ[K] (1 : M)) ⊗ₜ[M] algebraMap L N x
  simp only [Algebra.TensorProduct.commRight_symm_tmul,
    Algebra.IsPushout.cancelBaseChangeAlg_symm_tmul,
    Algebra.TensorProduct.commRight_tmul]

/-- Inclusion on unit groups induced by a pushout square of fields. -/
def pushoutTowerIdeleInclusion :
    RelativeIdeleGroup K L →*
      TowerRelativeIdeleGroup K M N :=
  Units.map (pushoutTowerAdeleInclusion K M L N)

omit [NumberField M] [NumberField L] [NumberField N]
    [FiniteDimensional K M] [FiniteDimensional K L]
    [FiniteDimensional M N] [FiniteDimensional L N] in
/-- The pushout inclusion sends a principal idele of `L` to the
principal idele of its image in `N`. -/
@[simp]
theorem pushoutTowerIdeleInclusion_principalIdele
    (x : Lˣ) :
    pushoutTowerIdeleInclusion K M L N
        (RelativeIdeleGroup.principalIdele K L x) =
      TowerRelativeIdeleGroup.principalIdele K M N
        (Units.map (algebraMap L N) x) := by
  apply Units.ext
  change
    pushoutTowerAdeleInclusion K M L N
        ((1 : NumberField.AdeleRing (𝓞 K) K) ⊗ₜ[K] (x : L)) =
      (1 : RelativeAdeleRing K M) ⊗ₜ[M]
        algebraMap L N (x : L)
  rw [pushoutTowerAdeleInclusion_tmul]
  rfl

omit [NumberField M] [NumberField L] [NumberField N]
    [FiniteDimensional K M] [FiniteDimensional M N]
    [FiniteDimensional L N] in
/-- Determinant norms commute with the pushout inclusion.  This is the
idele-level norm square used after adjoining roots of unity. -/
theorem pushoutTowerIdeleNorm_inclusion
    (a : RelativeIdeleGroup K L) :
    TowerRelativeIdeleGroup.norm K M N
        (pushoutTowerIdeleInclusion K M L N a) =
      RelativeIdeleGroup.inclusion K M
        (RelativeIdeleGroup.norm K L a) := by
  apply Units.ext
  let f :
      NumberField.AdeleRing (𝓞 K) K →ₐ[K]
        RelativeAdeleRing K M :=
    Algebra.TensorProduct.includeLeft
      (R := K) (S := K)
      (A := NumberField.AdeleRing (𝓞 K) K) (B := M)
  change
    Algebra.norm (RelativeAdeleRing K M)
        (pushoutTowerAdeleInclusion K M L N
          (a : RelativeAdeleRing K L)) =
      f (Algebra.norm
        (NumberField.AdeleRing (𝓞 K) K)
        (a : RelativeAdeleRing K L))
  calc
    _ = Algebra.norm (RelativeAdeleRing K M)
          (pushoutTowerAdeleEquiv K M L N
            (pushoutTowerAdeleInclusion K M L N
              (a : RelativeAdeleRing K L))) :=
      (Algebra.norm_eq_of_algEquiv
        (pushoutTowerAdeleEquiv K M L N)
        (pushoutTowerAdeleInclusion K M L N
          (a : RelativeAdeleRing K L))).symm
    _ = Algebra.norm (RelativeAdeleRing K M)
          (baseChangedRelativeAdeleMap K M L
            (a : RelativeAdeleRing K L)) := by
      simp [pushoutTowerAdeleInclusion]
    _ = f (Algebra.norm
          (NumberField.AdeleRing (𝓞 K) K)
          (a : RelativeAdeleRing K L)) :=
      (map_norm_tensorProduct_baseChange
        (K := K) (L := L) f
        (a : RelativeAdeleRing K L)).symm

/-- The pushout inclusion descended to relative idele class groups. -/
def pushoutTowerClassInclusion :
    RelativeIdeleGroup.ClassGroup K L →*
      TowerRelativeIdeleGroup.ClassGroup K M N :=
  QuotientGroup.map
    (RelativeIdeleGroup.principalSubgroup K L)
    (TowerRelativeIdeleGroup.principalSubgroup K M N)
    (pushoutTowerIdeleInclusion K M L N)
    (by
      rintro _ ⟨x, rfl⟩
      exact
        ⟨Units.map (algebraMap L N) x,
          (pushoutTowerIdeleInclusion_principalIdele
            K M L N x).symm⟩)

omit [NumberField M] [NumberField L] [NumberField N]
    [FiniteDimensional K M] [FiniteDimensional K L]
    [FiniteDimensional M N] [FiniteDimensional L N] in
@[simp]
theorem pushoutTowerClassInclusion_mk
    (a : RelativeIdeleGroup K L) :
    pushoutTowerClassInclusion K M L N
        (QuotientGroup.mk'
          (RelativeIdeleGroup.principalSubgroup K L) a) =
      QuotientGroup.mk'
        (TowerRelativeIdeleGroup.principalSubgroup K M N)
        (pushoutTowerIdeleInclusion K M L N a) :=
  rfl

omit [NumberField M] [NumberField L] [NumberField N]
    [FiniteDimensional K M] [FiniteDimensional L N] in
/-- The determinant-norm square after adjoining the pushout field,
descended to actual relative idele class groups. -/
theorem pushoutTowerClassNorm_inclusion
    (c : RelativeIdeleGroup.ClassGroup K L) :
    TowerRelativeIdeleGroup.classNorm K M N
        (pushoutTowerClassInclusion K M L N c) =
      RelativeIdeleGroup.classInclusion K M
        (RelativeIdeleGroup.classNorm K L c) := by
  refine QuotientGroup.induction_on c ?_
  intro a
  change
    QuotientGroup.mk'
        (RelativeIdeleGroup.principalSubgroup K M)
        (TowerRelativeIdeleGroup.norm K M N
          (pushoutTowerIdeleInclusion K M L N a)) =
      QuotientGroup.mk'
        (RelativeIdeleGroup.principalSubgroup K M)
        (RelativeIdeleGroup.inclusion K M
          (RelativeIdeleGroup.norm K L a))
  exact congrArg
    (QuotientGroup.mk'
      (RelativeIdeleGroup.principalSubgroup K M))
    (pushoutTowerIdeleNorm_inclusion K M L N a)

/-- The map on degree-zero class-norm quotients induced by the pushout
inclusion. -/
def pushoutNormQuotientMap :
    RelativeIdeleGroup.ClassNormQuotient K L →*
      IntermediateClassNormQuotient K M N :=
  QuotientGroup.map
    (RelativeIdeleGroup.classNorm K L).range
    (TowerRelativeIdeleGroup.classNorm K M N).range
    (RelativeIdeleGroup.classInclusion K M)
    (by
      rintro _ ⟨c, rfl⟩
      exact
        ⟨pushoutTowerClassInclusion K M L N c,
          pushoutTowerClassNorm_inclusion K M L N c⟩)

omit [NumberField M] [NumberField L] [NumberField N]
    [FiniteDimensional K M] [FiniteDimensional L N] in
@[simp]
theorem pushoutNormQuotientMap_mk
    (c : IdeleClassGroup K) :
    pushoutNormQuotientMap K M L N
        (QuotientGroup.mk' (RelativeIdeleGroup.classNorm K L).range c) =
      QuotientGroup.mk'
        (TowerRelativeIdeleGroup.classNorm K M N).range
        (RelativeIdeleGroup.classInclusion K M c) :=
  rfl

/-- Change the chosen intermediate field in the tower presentation of
the relative idele class group of `N`, keeping the bottom field `K`
fixed. -/
def changeIntermediateClassGroupEquiv :
    TowerRelativeIdeleGroup.ClassGroup K M N ≃*
      TowerRelativeIdeleGroup.ClassGroup K L N :=
  (TowerRelativeIdeleGroup.classGroupEquiv K M N).trans
    (TowerRelativeIdeleGroup.classGroupEquiv K L N).symm

omit [NumberField M] [NumberField L] [Algebra.IsPushout K M L N] in
/-- Changing the intermediate tower presentation does not change the
composite class norm to `K`. -/
theorem towerCompositeClassNorm_changeIntermediate
    (c : TowerRelativeIdeleGroup.ClassGroup K M N) :
    towerCompositeClassNorm K L N
        (changeIntermediateClassGroupEquiv K M L N c) =
      towerCompositeClassNorm K M N c := by
  rw [towerCompositeClassNorm_eq_ideleClassNorm,
    towerCompositeClassNorm_eq_ideleClassNorm]
  simp [changeIntermediateClassGroupEquiv]

omit [NumberField M] [NumberField L] [Algebra.IsPushout K M L N] in
/-- Every composite norm through `M` is, after changing the tower
presentation, already a norm through `L`. -/
theorem towerCompositeClassNorm_mem_ideleClassNormRange
    (c : TowerRelativeIdeleGroup.ClassGroup K M N) :
    towerCompositeClassNorm K M N c ∈
      (RelativeIdeleGroup.classNorm K L).range := by
  refine
    ⟨TowerRelativeIdeleGroup.classNorm K L N
        (changeIntermediateClassGroupEquiv K M L N c),
      ?_⟩
  exact towerCompositeClassNorm_changeIntermediate K M L N c

/-- Norm back from the pushout target quotient to the original
class-norm quotient. -/
def pushoutNormQuotientNormBack :
    IntermediateClassNormQuotient K M N →*
      RelativeIdeleGroup.ClassNormQuotient K L :=
  QuotientGroup.map
    (TowerRelativeIdeleGroup.classNorm K M N).range
    (RelativeIdeleGroup.classNorm K L).range
    (RelativeIdeleGroup.classNorm K M)
    (by
      rintro _ ⟨c, rfl⟩
      exact
        towerCompositeClassNorm_mem_ideleClassNormRange
          K M L N c)

omit [NumberField M] [NumberField L] [Algebra.IsPushout K M L N] in
@[simp]
theorem pushoutNormQuotientNormBack_mk
    (c : RelativeIdeleGroup.ClassGroup K M) :
    pushoutNormQuotientNormBack K M L N
        (QuotientGroup.mk'
          (TowerRelativeIdeleGroup.classNorm K M N).range c) =
      QuotientGroup.mk' (RelativeIdeleGroup.classNorm K L).range
        (RelativeIdeleGroup.classNorm K M c) :=
  rfl
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_IdealMap
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The ideal attached to an idele

This file formalizes the ideal map from ideles. Its construction
is explicit: local discrete valuations form a finitely supported integer
vector, and unique factorization of fractional ideals identifies that vector
with a nonzero fractional ideal.  We prove both stages surjective and identify
the kernel with the ideles integral at every finite place.
-/

open scoped NumberField RestrictedProduct WithZero
open NumberField IsDedekindDomain

noncomputable section


variable {K : Type*} [Field K] [NumberField K]

namespace IdeleGroup

theorem fractionalIdeal_ker :
    (fractionalIdeal (K := K)).ker = integralAtFinitePlaces := by
  ext a
  change FiniteIdeleGroup.fractionalIdeal a.2 = 1 ↔
    a.2 ∈ FiniteIdeleGroup.integralSubgroup
  rw [← MonoidHom.mem_ker,
    FiniteIdeleGroup.fractionalIdeal_ker]

end IdeleGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Cohomology_Herbrand
attribute [-instance] _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.CyclicCohomology.instMulDistribMulActionBinaryCoefficientFamily _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.FiniteIdeleGroup.mem_integralSubgroup_iff _root_.FiniteIdeleGroup.mem_supportedAt_iff _root_.FiniteIdeleGroup.valuationVectorAdd_apply _root_.FiniteIdeleGroup.valuationVector_apply _root_.FiniteIdeleGroup.valuationVector_valuationVectorSection _root_.IdeleGroup.finiteComponentContinuous_apply _root_.IdeleGroup.infiniteComponentContinuous_apply _root_.IdeleGroup.mem_supportedAt_iff _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalClassFieldTheory.fixedUnitToInvariantsNormQuotientMonoidHom_apply _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.RelativeIdeleGroup.finiteComponent_coe _root_.RelativeIdeleGroup.finiteComponent_inclusion _root_.RelativeIdeleGroup.finiteComponent_norm _root_.RelativeIdeleGroup.finiteComponent_principalIdele _root_.RelativeIdeleGroup.infiniteComponent_coe _root_.RelativeIdeleGroup.infiniteComponent_inclusion _root_.RelativeIdeleGroup.infiniteComponent_norm _root_.RelativeIdeleGroup.infiniteComponent_principalIdele _root_.TowerRelativeIdeleGroup.classGroupEquiv_mk _root_.TowerRelativeIdeleGroup.classNorm_mk _root_.TowerRelativeIdeleGroup.norm_principalIdele _root_.TowerRelativeIdeleGroup.towerRelativeIdeleEquiv_principalIdele _root_.bottomAdeleToTower_apply _root_.compositeToBaseNormQuotient_mk _root_.intermediateAdeleInclusion_tmul _root_.intermediateToCompositeNormQuotient_mk _root_.mem_relativeAdeleCoefficientSupport_iff _root_.mem_relativeIdeleCoefficientSupport_iff _root_.pushoutNormQuotientMap_mk _root_.pushoutNormQuotientNormBack_mk _root_.pushoutTowerAdeleInclusion_tmul _root_.pushoutTowerClassInclusion_mk _root_.pushoutTowerIdeleInclusion_principalIdele _root_.relativeAdeleFiniteComponent_tmul _root_.relativeAdeleInfiniteComponent_tmul _root_.topFieldToOneStep_apply _root_.topFieldToTower_apply _root_.towerRelativeAdeleFlatten_tmul _root_.towerRelativeAdeleUnflatten_tmul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Herbrand cohomology of the relative idele class group

This file realizes the low-degree exact sequence on the actual relative
idele group

`1 → Lˣ → I_L → C_L → 1`.

The Galois actions are the concrete conjugation actions from the
tensor-product model of relative adeles.  The class norm is descended from
the determinant norm on relative ideles, and its relation with the Tate
norm is proved from the Galois product formula.
-/

open scoped BigOperators NumberField
open NumberField

noncomputable section


open CyclicCohomology.ProfiniteCohomology.Herbrand
open CyclicCohomology

namespace RelativeIdeleGroup
namespace Cohomology

variable
    (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

section Actions

local instance instMulDistribMulActionAlgEquiv_r9fe581_1 :
    MulDistribMulAction (L ≃ₐ[K] L)
      (RelativeIdeleGroup K L) :=
  relativeIdeleMulDistribMulAction K L
attribute [local instance] RelativeIdeleGroup.Cohomology.instMulDistribMulActionAlgEquivClassGroup
local instance instMulDistribMulActionAlgEquivSubtypeMemSubgroupPrincipalSubgroup_r9fe581_1 :
    MulDistribMulAction (L ≃ₐ[K] L)
      (RelativeIdeleGroup.principalSubgroup K L) :=
  principalIdeleMulDistribMulAction K L
omit [NumberField L] [FiniteDimensional K L] [IsGalois K L] in
/-- The fixed subgroup used by Tate cohomology is the concrete
Galois-fixed subgroup from idele-class descent. -/
theorem ideleClass_fixedSubgroup_eq_galoisFixed :
    fixedSubgroup (L ≃ₐ[K] L)
        (RelativeIdeleGroup.ClassGroup K L) =
      RelativeIdeleGroup.galoisFixedClassSubgroup K L := by
  ext c
  constructor
  · intro hc σ
    exact hc σ
  · intro hc σ
    exact hc σ

/-- Galois descent as a homomorphism from the base idele class group to
the Tate fixed subgroup. -/
def baseIdeleClassToFixed :
    IdeleClassGroup K →*
      fixedSubgroup (L ≃ₐ[K] L)
        (RelativeIdeleGroup.ClassGroup K L) :=
  (RelativeIdeleGroup.classInclusion K L).codRestrict
    (fixedSubgroup (L ≃ₐ[K] L)
      (RelativeIdeleGroup.ClassGroup K L))
    (by
      intro c
      rw [ideleClass_fixedSubgroup_eq_galoisFixed K L]
      exact
        RelativeIdeleGroup.classInclusion_range_le_galoisFixed
          K L ⟨c, rfl⟩)

omit [NumberField L] [FiniteDimensional K L] [IsGalois K L] in
@[simp]
theorem baseIdeleClassToFixed_coe
    (c : IdeleClassGroup K) :
    ((baseIdeleClassToFixed K L c :
        fixedSubgroup (L ≃ₐ[K] L)
          (RelativeIdeleGroup.ClassGroup K L)) :
      RelativeIdeleGroup.ClassGroup K L) =
        RelativeIdeleGroup.classInclusion K L c :=
  rfl

/-- Galois descent packaged as the multiplicative equivalence
`C_K ≃ C_L^G` required by the `H⁰` calculation. -/
noncomputable def baseIdeleClassEquivFixed :
    IdeleClassGroup K ≃*
      fixedSubgroup (L ≃ₐ[K] L)
        (RelativeIdeleGroup.ClassGroup K L) :=
  MulEquiv.ofBijective
    (baseIdeleClassToFixed K L)
    ⟨by
      intro a b hab
      apply RelativeIdeleGroup.classInclusion_injective K L
      exact congrArg Subtype.val hab,
    by
      intro c
      have hc :
          (c : RelativeIdeleGroup.ClassGroup K L) ∈
            (RelativeIdeleGroup.classInclusion K L).range := by
        rw [
          RelativeIdeleGroup.classInclusion_range_eq_galoisFixedClassSubgroup
            K L,
          ← ideleClass_fixedSubgroup_eq_galoisFixed K L]
        exact c.property
      rcases hc with ⟨a, ha⟩
      exact ⟨a, Subtype.ext ha⟩⟩

omit [NumberField L] in
@[simp]
theorem baseIdeleClassEquivFixed_coe
    (c : IdeleClassGroup K) :
    ((baseIdeleClassEquivFixed K L c :
        fixedSubgroup (L ≃ₐ[K] L)
          (RelativeIdeleGroup.ClassGroup K L)) :
      RelativeIdeleGroup.ClassGroup K L) =
        RelativeIdeleGroup.classInclusion K L c :=
  rfl

end Actions

end Cohomology
end RelativeIdeleGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_ClassGroup_Core
attribute [-instance] _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.FiniteIdeleGroup.mem_supportedAt_iff _root_.IdeleGroup.finiteComponentContinuous_apply _root_.IdeleGroup.infiniteComponentContinuous_apply _root_.IdeleGroup.mem_supportedAt_iff _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The ordinary ideal class group as an idele quotient

This file proves that quotienting the idele group by the
ideles integral at every finite place and by the principal ideles gives the
ordinary ideal class group.
-/

open scoped NumberField RestrictedProduct WithZero
open NumberField IsDedekindDomain

noncomputable section


variable {K : Type*} [Field K] [NumberField K]

namespace IdeleGroup

/-- The fractional ideal map sends a principal idele to the corresponding
principal fractional ideal. -/
@[simp]
theorem fractionalIdeal_principalIdele (x : Kˣ) :
    fractionalIdeal (principalIdele K x) =
      toPrincipalIdeal (𝓞 K) K x := by
  apply FractionalIdealGroup.ext_count
  intro v
  rw [count_toPrincipalIdeal]
  change FractionalIdeal.count K v
      (((FractionalIdealGroup.factorization (K := K))
        (FiniteIdeleGroup.valuationVector
          (principalIdele K x).2) : FractionalIdealGroup K) :
        FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
      -WithZero.log (v.valuation K (x : K))
  rw [FractionalIdealGroup.count_factorization]
  change -WithZero.log
      (Valued.v (((principalIdele K x).2 v :
        (v.adicCompletion K)ˣ) : v.adicCompletion K)) =
      -WithZero.log (v.valuation K (x : K))
  rw [show ((((principalIdele K x).2 v :
      (v.adicCompletion K)ˣ) : v.adicCompletion K)) = (x : K) from rfl,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation']

theorem classGroup_mk_eq_one_iff
    (I : FractionalIdealGroup K) :
    ClassGroup.mk K I = 1 ↔
      I ∈ (toPrincipalIdeal (𝓞 K) K).range := by
  constructor
  · intro h
    have h' := congrArg (ClassGroup.equiv K) h
    simpa using h'
  · intro h
    apply (ClassGroup.equiv K).injective
    simpa using h

@[simp]
theorem idealClass_principalIdele (x : Kˣ) :
    idealClass (principalIdele K x) = 1 := by
  change ClassGroup.mk K
      (fractionalIdeal (principalIdele K x)) = 1
  rw [fractionalIdeal_principalIdele,
    classGroup_mk_eq_one_iff]
  exact ⟨x, rfl⟩

end IdeleGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_NormCore
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.FiniteIdeleGroup.mem_supportedAt_iff _root_.IdeleGroup.finiteComponentContinuous_apply _root_.IdeleGroup.fractionalIdeal_principalIdele _root_.IdeleGroup.idealClass_principalIdele _root_.IdeleGroup.infiniteComponentContinuous_apply _root_.IdeleGroup.mem_supportedAt_iff _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.RelativeIdeleGroup.finiteComponent_inclusion _root_.RelativeIdeleGroup.finiteComponent_norm _root_.RelativeIdeleGroup.infiniteComponent_inclusion _root_.RelativeIdeleGroup.infiniteComponent_norm _root_.compositeToBaseNormQuotient_mk _root_.intermediateToCompositeNormQuotient_mk _root_.pushoutNormQuotientMap_mk _root_.pushoutNormQuotientNormBack_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The absolute norm of an idele

This file constructs the homomorphism `𝓝 : I_K → ℝ₊ˣ`. At a finite place a uniformizer contributes the norm
of its prime ideal; at infinity we divide by the normalized archimedean
norm.  This is the convention for which principal ideles have norm one.
-/

open scoped NumberField RestrictedProduct NNReal
open NumberField IsDedekindDomain

noncomputable section


variable {K : Type*} [Field K] [NumberField K]

namespace InfiniteIdeleGroup

/-- The product of the normalized norms of all archimedean components. -/
def archimedeanNorm :
    InfiniteIdeleGroup K →* ℝ≥0ˣ where
  toFun a := ∏ w : InfinitePlace K,
    nnnormUnitHom w.Completion (component w a) ^ w.mult
  map_one' := by
    apply Finset.prod_eq_one
    intro w _
    rw [map_one, map_one, one_pow]
  map_mul' a b := by
    simp only [map_mul, Finset.prod_mul_distrib, mul_pow]

@[simp]
theorem archimedeanNorm_apply (a : InfiniteIdeleGroup K) :
    archimedeanNorm a =
      ∏ w : InfinitePlace K,
        nnnormUnitHom w.Completion (component w a) ^ w.mult :=
  rfl

end InfiniteIdeleGroup

namespace FiniteIdeleGroup

/-- The homomorphism sending an integer exponent to the corresponding
power of the absolute norm of a finite prime. -/
def primeNormPowerHom (v : HeightOneSpectrum (𝓞 K)) :
    Multiplicative ℤ →* ℝ≥0ˣ :=
  MonoidHom.mk' (fun n => primeNorm v ^ n.toAdd)
    fun m n => by simp [zpow_add]

/-- The norm of a finitely supported divisor. -/
def divisorNorm :
    Multiplicative (HeightOneSpectrum (𝓞 K) →₀ ℤ) →* ℝ≥0ˣ :=
  MonoidHom.mk' (fun exps =>
      exps.toAdd.prod fun v n =>
        primeNormPowerHom v (Multiplicative.ofAdd n))
    fun _ _ => Finsupp.prod_hom_add_index
      (fun v => primeNormPowerHom v)

/-- The finite part of the absolute idele norm. -/
def absoluteNorm :
    FiniteIdeleGroup K →* ℝ≥0ˣ :=
  (divisorNorm (K := K)).comp (valuationVector (K := K))

@[simp]
theorem absoluteNorm_apply (a : FiniteIdeleGroup K) :
    absoluteNorm a =
      (valuationVector a).toAdd.prod fun v n =>
        primeNorm v ^ n := by
  rfl

end FiniteIdeleGroup

namespace IdeleGroup

/-- The absolute norm on the idele group. -/
def absoluteNorm :
    IdeleGroup K →* ℝ≥0ˣ :=
  MonoidHom.mk'
    (fun a => FiniteIdeleGroup.absoluteNorm a.2 *
      (InfiniteIdeleGroup.archimedeanNorm a.1)⁻¹)
    fun a b => by
      simp only [map_mul, Prod.fst_mul, Prod.snd_mul, mul_inv_rev]
      ac_rfl

@[simp]
theorem absoluteNorm_apply (a : IdeleGroup K) :
    absoluteNorm a =
      FiniteIdeleGroup.absoluteNorm a.2 *
        (InfiniteIdeleGroup.archimedeanNorm a.1)⁻¹ :=
  rfl

/-- The norm-one ideles. -/
def normOneSubgroup : Subgroup (IdeleGroup K) :=
  (absoluteNorm (K := K)).ker

end IdeleGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_PrincipalNorm
attribute [-instance] _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.FiniteIdeleGroup.mem_supportedAt_iff _root_.IdeleGroup.finiteComponentContinuous_apply _root_.IdeleGroup.infiniteComponentContinuous_apply _root_.IdeleGroup.mem_supportedAt_iff _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The product formula for principal ideles

This file proves that the absolute idele norm is trivial on the diagonal
copy of `Kˣ`, and hence descends to the idele class group.
-/

open scoped NumberField RestrictedProduct NNReal WithZero
open NumberField IsDedekindDomain

noncomputable section


variable {K : Type*} [Field K] [NumberField K]

namespace InfiniteIdeleGroup

/-- The archimedean norm of a principal idele is the absolute field norm. -/
theorem archimedeanNorm_principalIdele (x : Kˣ) :
    ((archimedeanNorm
        (IdeleGroup.principalIdele K x).1 : ℝ≥0ˣ) : ℝ≥0) =
      ⟨|(Algebra.norm ℚ) (x : K)|, abs_nonneg _⟩ := by
  rw [archimedeanNorm_apply]
  simp only [Units.coe_prod, Units.val_pow_eq_pow_val,
    nnnormUnitHom_val]
  apply NNReal.eq
  simp only [NNReal.coe_prod, NNReal.coe_pow, coe_nnnorm]
  change (∏ w : InfinitePlace K,
      ‖((InfiniteIdeleGroup.component w
        (IdeleGroup.principalIdele K x).1 : w.Completionˣ) :
          w.Completion)‖ ^ w.mult) =
      |((Algebra.norm ℚ) (x : K) : ℝ)|
  simp_rw [show ∀ w : InfinitePlace K,
      ((InfiniteIdeleGroup.component w
        (IdeleGroup.principalIdele K x).1 : w.Completionˣ) :
          w.Completion) = (x : K) by
    intro w
    exact IdeleGroup.infiniteComponent_principalIdele x w]
  have hnorm (w : InfinitePlace K) :
      ‖((x : K) : w.Completion)‖ = w (x : K) := by
    change ‖(((WithAbs.equiv w.1).symm (x : K) :
      WithAbs w.1) : w.Completion)‖ = w (x : K)
    rw [InfinitePlace.Completion.norm_coe,
      (WithAbs.equiv w.1).apply_symm_apply]
  simp_rw [hnorm]
  have hproduct :=
    NumberField.prod_abs_eq_one (Units.ne_zero x)
  have hfinite :=
    FinitePlace.prod_eq_inv_abs_norm (Units.ne_zero x)
  rw [hfinite] at hproduct
  have hnorm_ne_zero :
      (Algebra.norm ℚ) (x : K) ≠ 0 :=
    Algebra.norm_ne_zero_iff.mpr (Units.ne_zero x)
  have habs_ne_zero :
      (|(Algebra.norm ℚ) (x : K)| : ℚ) ≠ 0 :=
    abs_ne_zero.mpr hnorm_ne_zero
  have hcast_ne_zero :
      ((|(Algebra.norm ℚ) (x : K)| : ℚ) : ℝ) ≠ 0 := by
    exact_mod_cast habs_ne_zero
  have hproduct' :
      (∏ w : InfinitePlace K, w (x : K) ^ w.mult) *
        ((|(Algebra.norm ℚ) (x : K)| : ℚ) : ℝ)⁻¹ = 1 := by
    simpa only [Rat.cast_inv] using hproduct
  have hresult :=
    (mul_inv_eq_one₀ hcast_ne_zero).mp hproduct'
  simpa only [Rat.cast_abs] using hresult

end InfiniteIdeleGroup

namespace FractionalIdealGroup

/-- The positive absolute norm of a nonzero fractional ideal. -/
def absoluteNorm :
    FractionalIdealGroup K →* ℝ≥0ˣ where
  toFun I :=
    Units.mk0
      ⟨(FractionalIdeal.absNorm
          (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : ℝ),
        Rat.cast_nonneg.mpr
          (FractionalIdeal.absNorm_nonneg
            (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K))⟩
      (by
        intro h
        have hr := congrArg (fun z : ℝ≥0 => z.1) h
        change
          ((FractionalIdeal.absNorm
            (I : FractionalIdeal
              (nonZeroDivisors (𝓞 K)) K) : ℚ) : ℝ) = 0 at hr
        have hq : FractionalIdeal.absNorm
            (I : FractionalIdeal
              (nonZeroDivisors (𝓞 K)) K) = 0 := by
          exact_mod_cast hr
        exact Units.ne_zero I
          (FractionalIdeal.absNorm_eq_zero_iff.mp hq))
  map_one' := by
    apply Units.ext
    apply NNReal.eq
    change
      ((FractionalIdeal.absNorm
        (1 : FractionalIdeal
          (nonZeroDivisors (𝓞 K)) K) : ℚ) : ℝ) = 1
    rw [FractionalIdeal.absNorm_one]
    norm_num
  map_mul' I J := by
    apply Units.ext
    change
      (⟨(FractionalIdeal.absNorm
          ((I * J : FractionalIdealGroup K) :
            FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : ℝ),
        Rat.cast_nonneg.mpr
          (FractionalIdeal.absNorm_nonneg
            ((I * J : FractionalIdealGroup K) :
              FractionalIdeal (nonZeroDivisors (𝓞 K)) K))⟩ : ℝ≥0) =
      ⟨(FractionalIdeal.absNorm
          (I : FractionalIdeal
            (nonZeroDivisors (𝓞 K)) K) : ℝ),
        Rat.cast_nonneg.mpr
          (FractionalIdeal.absNorm_nonneg
            (I : FractionalIdeal
              (nonZeroDivisors (𝓞 K)) K))⟩ *
      ⟨(FractionalIdeal.absNorm
          (J : FractionalIdeal
            (nonZeroDivisors (𝓞 K)) K) : ℝ),
        Rat.cast_nonneg.mpr
          (FractionalIdeal.absNorm_nonneg
            (J : FractionalIdeal
              (nonZeroDivisors (𝓞 K)) K))⟩
    apply NNReal.eq
    change
      ((FractionalIdeal.absNorm
        ((I * J : FractionalIdealGroup K) :
          FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : ℚ) : ℝ) =
      ((FractionalIdeal.absNorm
        (I : FractionalIdeal
          (nonZeroDivisors (𝓞 K)) K) : ℚ) : ℝ) *
      ((FractionalIdeal.absNorm
        (J : FractionalIdeal
          (nonZeroDivisors (𝓞 K)) K) : ℚ) : ℝ)
    norm_cast
    simpa only [Units.val_mul] using
      (map_mul FractionalIdeal.absNorm
        (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
        (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K))

@[simp]
theorem absoluteNorm_prime (v : HeightOneSpectrum (𝓞 K)) :
    absoluteNorm (prime v) = FiniteIdeleGroup.primeNorm v := by
  apply Units.ext
  apply NNReal.eq
  change
    ((FractionalIdeal.absNorm
      (v.asIdeal :
        FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : ℚ) : ℝ) =
      (v.asIdeal.absNorm : ℝ)
  rw [FractionalIdeal.coeIdeal_absNorm]
  norm_cast

/-- The explicit prime-factor norm commutes with the factorization of a
fractional ideal. -/
theorem absoluteNorm_factorization
    (e : Multiplicative
      (HeightOneSpectrum (𝓞 K) →₀ ℤ)) :
    absoluteNorm (factorization e) =
      FiniteIdeleGroup.divisorNorm e := by
  change absoluteNorm
      (e.toAdd.prod fun v n => primePowerHom v
        (Multiplicative.ofAdd n)) =
    e.toAdd.prod fun v n =>
      FiniteIdeleGroup.primeNormPowerHom v
        (Multiplicative.ofAdd n)
  rw [map_finsuppProd]
  apply Finsupp.prod_congr
  intro v hv
  change absoluteNorm (prime v ^ e.toAdd v) =
    FiniteIdeleGroup.primeNorm v ^ e.toAdd v
  rw [map_zpow, absoluteNorm_prime]

/-- The norm of the principal fractional ideal `(x)` is the absolute field
norm of `x`. -/
theorem absoluteNorm_toPrincipalIdeal (x : Kˣ) :
    ((absoluteNorm
      (toPrincipalIdeal (𝓞 K) K x) : ℝ≥0ˣ) : ℝ≥0) =
      ⟨|((Algebra.norm ℚ) (x : K) : ℝ)|, abs_nonneg _⟩ := by
  apply NNReal.eq
  change
    ((FractionalIdeal.absNorm
      ((toPrincipalIdeal (𝓞 K) K x :
        FractionalIdealGroup K) :
        FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : ℚ) : ℝ) =
      |((Algebra.norm ℚ) (x : K) : ℝ)|
  rw [coe_toPrincipalIdeal,
    FractionalIdeal.absNorm_span_singleton, Rat.cast_abs]

end FractionalIdealGroup

namespace FiniteIdeleGroup

/-- The finite idele norm is the absolute norm of its associated fractional
ideal. -/
theorem absoluteNorm_eq_fractionalIdealAbsoluteNorm
    (a : FiniteIdeleGroup K) :
    absoluteNorm a =
      FractionalIdealGroup.absoluteNorm (fractionalIdeal a) := by
  change divisorNorm (valuationVector a) =
    FractionalIdealGroup.absoluteNorm
      (FractionalIdealGroup.factorization (valuationVector a))
  exact (FractionalIdealGroup.absoluteNorm_factorization
    (valuationVector a)).symm

/-- The finite norm of a principal idele is the absolute field norm. -/
theorem absoluteNorm_principalIdele (x : Kˣ) :
    ((absoluteNorm
      (IdeleGroup.principalIdele K x).2 : ℝ≥0ˣ) : ℝ≥0) =
      ⟨|((Algebra.norm ℚ) (x : K) : ℝ)|, abs_nonneg _⟩ := by
  rw [absoluteNorm_eq_fractionalIdealAbsoluteNorm]
  have h :
      fractionalIdeal (IdeleGroup.principalIdele K x).2 =
        toPrincipalIdeal (𝓞 K) K x :=
    IdeleGroup.fractionalIdeal_principalIdele x
  rw [h, FractionalIdealGroup.absoluteNorm_toPrincipalIdeal]

end FiniteIdeleGroup

namespace IdeleGroup

/-- The finite and archimedean norm factors agree on a principal idele. -/
theorem finite_absoluteNorm_eq_archimedeanNorm_principalIdele
    (x : Kˣ) :
    FiniteIdeleGroup.absoluteNorm (principalIdele K x).2 =
      InfiniteIdeleGroup.archimedeanNorm
        (principalIdele K x).1 := by
  apply Units.ext
  exact (FiniteIdeleGroup.absoluteNorm_principalIdele x).trans
    (InfiniteIdeleGroup.archimedeanNorm_principalIdele x).symm

/-- The number-field product formula in idelic form: every principal idele
has global absolute norm one. -/
@[simp]
theorem absoluteNorm_principalIdele (x : Kˣ) :
    absoluteNorm (principalIdele K x) = 1 := by
  rw [absoluteNorm_apply,
    finite_absoluteNorm_eq_archimedeanNorm_principalIdele]
  exact mul_inv_cancel _

/-- Principal ideles lie in the norm-one subgroup. -/
theorem principalSubgroup_le_normOneSubgroup :
    principalSubgroup K ≤ normOneSubgroup (K := K) := by
  rintro a ⟨x, rfl⟩
  exact absoluteNorm_principalIdele x

end IdeleGroup

namespace IdeleClassGroup

/-- The absolute idele norm descended through `C_K = I_K / Kˣ`. -/
def absoluteNorm :
    IdeleClassGroup K →* ℝ≥0ˣ :=
  QuotientGroup.lift (IdeleGroup.principalSubgroup K)
    (IdeleGroup.absoluteNorm (K := K))
    (IdeleGroup.principalSubgroup_le_normOneSubgroup (K := K))

@[simp]
theorem absoluteNorm_mk (a : IdeleGroup K) :
    absoluteNorm
      (QuotientGroup.mk' (IdeleGroup.principalSubgroup K) a) =
        IdeleGroup.absoluteNorm a :=
  QuotientGroup.lift_mk _ _ _

/-- The norm-one idele classes. -/
def normOneSubgroup : Subgroup (IdeleClassGroup K) :=
  (absoluteNorm (K := K)).ker

@[simp]
theorem mk_mem_normOneSubgroup_iff (a : IdeleGroup K) :
    QuotientGroup.mk' (IdeleGroup.principalSubgroup K) a ∈
        normOneSubgroup (K := K) ↔
      a ∈ IdeleGroup.normOneSubgroup (K := K) := by
  change absoluteNorm
      (QuotientGroup.mk' (IdeleGroup.principalSubgroup K) a) = 1 ↔
    IdeleGroup.absoluteNorm a = 1
  rw [absoluteNorm_mk]

end IdeleClassGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_NormOneCompact
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Compactness of norm-one idele classes

This module combines local compactness, the logarithmic unit lattice, and the
principal-idele norm formula to prove compactness of the norm-one subgroup of
the idele class group.
-/

open scoped Classical NumberField Pointwise RestrictedProduct NNReal
open NumberField IsDedekindDomain
open NumberField.Units.dirichletUnitTheorem

noncomputable section


variable {K : Type*} [Field K] [NumberField K]

namespace FiniteIdeleGroup

/-- The product of all local integral-unit groups, embedded in the finite
idele group. -/
def integralStructureMap :
    (∀ v : HeightOneSpectrum (𝓞 K),
      (v.adicCompletionIntegers K).units) → FiniteIdeleGroup K :=
  RestrictedProduct.structureMap
    (fun v : HeightOneSpectrum (𝓞 K) ↦ (v.adicCompletion K)ˣ)
    (fun v : HeightOneSpectrum (𝓞 K) ↦
      (v.adicCompletionIntegers K).units)
    Filter.cofinite

theorem range_integralStructureMap :
    Set.range (integralStructureMap (K := K)) =
      (integralSubgroup (K := K) : Set (FiniteIdeleGroup K)) := by
  ext a
  constructor
  · rintro ⟨u, rfl⟩ v
    exact (u v).property
  · intro ha
    let u : ∀ v : HeightOneSpectrum (𝓞 K),
        (v.adicCompletionIntegers K).units :=
      fun v ↦ ⟨a v, ha v⟩
    exact ⟨u, rfl⟩

/-- The everywhere integral finite ideles form a compact group. -/
theorem isCompact_integralSubgroup :
    IsCompact
      ((integralSubgroup (K := K) :
        Subgroup (FiniteIdeleGroup K)) : Set (FiniteIdeleGroup K)) := by
  have hlocal :
      ∀ v : HeightOneSpectrum (𝓞 K),
        CompactSpace (v.adicCompletionIntegers K).units := by
    intro v
    exact isCompact_iff_compactSpace.mp
      (isCompact_finiteLocalUnits K v)
  let (v : HeightOneSpectrum (𝓞 K)) :
      CompactSpace (v.adicCompletionIntegers K).units :=
    hlocal v
  have hdomain :
      IsCompact
        (Set.univ : Set (∀ v : HeightOneSpectrum (𝓞 K),
          (v.adicCompletionIntegers K).units)) :=
    isCompact_univ
  rw [← range_integralStructureMap (K := K)]
  unfold integralStructureMap
  simpa only [Set.image_univ] using
    hdomain.image
      (RestrictedProduct.isEmbedding_structureMap.continuous :
        Continuous (integralStructureMap (K := K)))

end FiniteIdeleGroup

namespace InfiniteIdeleGroup

/-- The logarithms of the normalized archimedean absolute values, with the
distinguished place omitted as in Dirichlet's unit theorem. -/
def logNorm (a : InfiniteIdeleGroup K) :
    logSpace K :=
  fun w ↦ w.1.mult *
    Real.log ‖((component w.1 a : w.1.Completionˣ) : w.1.Completion)‖

@[simp]
theorem logNorm_mul (a b : InfiniteIdeleGroup K) :
    logNorm (a * b) = logNorm a + logNorm b := by
  ext w
  have ha :
      ‖((component w.1 a : w.1.Completionˣ) :
        w.1.Completion)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (component w.1 a).ne_zero
  have hb :
      ‖((component w.1 b : w.1.Completionˣ) :
        w.1.Completion)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (component w.1 b).ne_zero
  simp only [logNorm, Pi.add_apply, map_mul, Units.val_mul, norm_mul,
    Real.log_mul ha hb, mul_add]

end InfiniteIdeleGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_RayClass_Basic
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.FiniteIdeleGroup.absoluteNorm_apply _root_.IdeleClassGroup.absoluteNorm_mk _root_.IdeleClassGroup.mk_mem_normOneSubgroup_iff _root_.IdeleGroup.absoluteNorm_apply _root_.IdeleGroup.absoluteNorm_principalIdele _root_.InfiniteIdeleGroup.archimedeanNorm_apply _root_.InfiniteIdeleGroup.logNorm_mul _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Finite ray-modulus data

This file contains the finite local data used by ray congruence subgroups.
A full modulus, including a selected set of real places, is defined in
`AlgebraicNumberTheory.RayClass.FullModulus`.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section


variable {K : Type*} [Field K] [NumberField K]

namespace RayClass

/-- The finite idele congruence subgroup attached to a modulus. -/
def finiteCongruenceSubgroup (m : FiniteModulus K) :
    Subgroup (FiniteIdeleGroup K) where
  carrier := {a | ∀ v, a v ∈ localHigherUnitGroup v (m v)}
  one_mem' v := (localHigherUnitGroup v (m v)).one_mem
  mul_mem' ha hb v :=
    (localHigherUnitGroup v (m v)).mul_mem (ha v) (hb v)
  inv_mem' ha v :=
    (localHigherUnitGroup v (m v)).inv_mem (ha v)

@[simp]
theorem mem_finiteCongruenceSubgroup_iff
    (m : FiniteModulus K) (a : FiniteIdeleGroup K) :
    a ∈ finiteCongruenceSubgroup m ↔
      ∀ v, a v ∈ localHigherUnitGroup v (m v) :=
  Iff.rfl

/-- Ideles positive at every real infinite place. -/
def narrowInfiniteCongruenceSubgroup :
    Subgroup (InfiniteIdeleGroup K) :=
  Subgroup.comap ContinuousMulEquiv.piUnits.toMonoidHom
    (Subgroup.pi Set.univ (fun v => infinitePositiveSubgroup v))

omit [NumberField K] in
@[simp]
theorem mem_narrowInfiniteCongruenceSubgroup_iff
    (a : InfiniteIdeleGroup K) :
    a ∈ narrowInfiniteCongruenceSubgroup (K := K) ↔
      ∀ v, ContinuousMulEquiv.piUnits a v ∈
        infinitePositiveSubgroup v := by
  change ContinuousMulEquiv.piUnits a ∈
      Subgroup.pi Set.univ (fun v => infinitePositiveSubgroup v) ↔ _
  rw [Subgroup.mem_pi]
  simp only [Set.mem_univ, true_implies]

end RayClass
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_RayClass_FullModulus
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.FiniteIdeleGroup.absoluteNorm_apply _root_.IdeleClassGroup.absoluteNorm_mk _root_.IdeleClassGroup.mk_mem_normOneSubgroup_iff _root_.IdeleGroup.absoluteNorm_apply _root_.IdeleGroup.absoluteNorm_principalIdele _root_.InfiniteIdeleGroup.archimedeanNorm_apply _root_.InfiniteIdeleGroup.logNorm_mul _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Ray moduli with selected real places

A ray modulus consists of a finite modulus together with the real places at
which positivity is imposed.  This file defines the corresponding idèle and
idèle-class congruence subgroups without fixing an archimedean convention.
-/

open scoped Classical NumberField
open NumberField IsDedekindDomain

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

namespace RayClass

/-- A ray modulus consists of its finite part and the selected real places
at which the positivity condition is imposed. -/
structure Modulus (K : Type*) [Field K] [NumberField K] where
  /-- The finite prime-power part of the modulus. -/
  finitePart : FiniteModulus K
  /-- The real places at which positivity is imposed. -/
  infinitePart : Finset (RealPlace K)

namespace Modulus

/-- The full modulus with a prescribed finite part and no archimedean
positivity condition. -/
def ofFinite (m : FiniteModulus K) : Modulus K where
  finitePart := m
  infinitePart := ∅

/-- The full modulus with a prescribed finite part and positivity at every
real place. -/
noncomputable def narrowOfFinite (m : FiniteModulus K) : Modulus K where
  finitePart := m
  infinitePart := Finset.univ

instance instZero : Zero (Modulus K) where
  zero := ofFinite 0

@[simp]
theorem finitePart_ofFinite (m : FiniteModulus K) :
    (ofFinite m).finitePart = m :=
  rfl

@[simp]
theorem infinitePart_ofFinite (m : FiniteModulus K) :
    (ofFinite m).infinitePart = ∅ :=
  rfl

@[simp]
theorem finitePart_narrowOfFinite (m : FiniteModulus K) :
    (narrowOfFinite m).finitePart = m :=
  rfl

@[simp]
theorem infinitePart_narrowOfFinite (m : FiniteModulus K) :
    (narrowOfFinite m).infinitePart = Finset.univ :=
  rfl

@[simp]
theorem finitePart_zero :
    (0 : Modulus K).finitePart = 0 :=
  rfl

@[simp]
theorem infinitePart_zero :
    (0 : Modulus K).infinitePart = ∅ :=
  rfl

instance instLE : LE (Modulus K) where
  le m n :=
    m.finitePart ≤ n.finitePart ∧ m.infinitePart ⊆ n.infinitePart

@[simp]
theorem le_iff {m n : Modulus K} :
    m ≤ n ↔
      m.finitePart ≤ n.finitePart ∧ m.infinitePart ⊆ n.infinitePart :=
  Iff.rfl

/-- Replace the finite part of a full modulus while retaining exactly its
selected real places. -/
def replaceFinitePart
    (m : Modulus K) (f : FiniteModulus K) : Modulus K where
  finitePart := f
  infinitePart := m.infinitePart

@[simp]
theorem finitePart_replaceFinitePart
    (m : Modulus K) (f : FiniteModulus K) :
    (m.replaceFinitePart f).finitePart = f :=
  rfl

@[simp]
theorem infinitePart_replaceFinitePart
    (m : Modulus K) (f : FiniteModulus K) :
    (m.replaceFinitePart f).infinitePart = m.infinitePart :=
  rfl

/-- Remove the positivity condition at one real place. -/
noncomputable def eraseRealPlace
    (m : Modulus K) (v : RealPlace K) : Modulus K where
  finitePart := m.finitePart
  infinitePart := m.infinitePart.erase v

@[simp]
theorem finitePart_eraseRealPlace
    (m : Modulus K) (v : RealPlace K) :
    (m.eraseRealPlace v).finitePart = m.finitePart :=
  rfl

@[simp]
theorem infinitePart_eraseRealPlace
    (m : Modulus K) (v : RealPlace K) :
    (m.eraseRealPlace v).infinitePart = m.infinitePart.erase v :=
  rfl

/-- Remove the positivity conditions at a finite set of real places. -/
noncomputable def eraseRealPlaces
    (m : Modulus K) (s : Finset (RealPlace K)) : Modulus K where
  finitePart := m.finitePart
  infinitePart := m.infinitePart \ s

@[simp]
theorem finitePart_eraseRealPlaces
    (m : Modulus K) (s : Finset (RealPlace K)) :
    (m.eraseRealPlaces s).finitePart = m.finitePart :=
  rfl

@[simp]
theorem infinitePart_eraseRealPlaces
    (m : Modulus K) (s : Finset (RealPlace K)) :
    (m.eraseRealPlaces s).infinitePart = m.infinitePart \ s :=
  rfl

/-- The local infinite congruence condition at an infinite place.  It is the
positive subgroup exactly at a real place selected by the modulus, and the
whole local group otherwise. -/
noncomputable def localInfiniteCongruenceSubgroup (m : Modulus K)
    (w : InfinitePlace K) : Subgroup w.Completionˣ := by
  classical
  exact if hw : w.IsReal then
    if hmem : (⟨w, hw⟩ : RealPlace K) ∈ m.infinitePart then
      infinitePositiveSubgroup w
    else ⊤
  else ⊤

@[simp]
theorem localInfiniteCongruenceSubgroup_replaceFinitePart
    (m : Modulus K) (f : FiniteModulus K) (w : InfinitePlace K) :
    (m.replaceFinitePart f).localInfiniteCongruenceSubgroup w =
      m.localInfiniteCongruenceSubgroup w := by
  rfl

@[simp]
theorem localInfiniteCongruenceSubgroup_of_mem
    (m : Modulus K) (v : RealPlace K) (hv : v ∈ m.infinitePart) :
    m.localInfiniteCongruenceSubgroup v.1 = infinitePositiveSubgroup v.1 := by
  simp [localInfiniteCongruenceSubgroup, v.property, hv]

@[simp]
theorem localInfiniteCongruenceSubgroup_of_not_mem
    (m : Modulus K) (v : RealPlace K) (hv : v ∉ m.infinitePart) :
    m.localInfiniteCongruenceSubgroup v.1 = ⊤ := by
  simp [localInfiniteCongruenceSubgroup, v.property, hv]

@[simp]
theorem localInfiniteCongruenceSubgroup_of_not_isReal
    (m : Modulus K) (w : InfinitePlace K) (hw : ¬ w.IsReal) :
    m.localInfiniteCongruenceSubgroup w = ⊤ := by
  simp [localInfiniteCongruenceSubgroup, hw]

/-- The subgroup of infinite idèles positive at the real places selected by
the modulus. -/
def infiniteCongruenceSubgroup (m : Modulus K) :
    Subgroup (InfiniteIdeleGroup K) :=
  Subgroup.comap ContinuousMulEquiv.piUnits.toMonoidHom
    (Subgroup.pi Set.univ (fun w => m.localInfiniteCongruenceSubgroup w))

@[simp]
theorem mem_infiniteCongruenceSubgroup_iff_local
    (m : Modulus K) (a : InfiniteIdeleGroup K) :
    a ∈ m.infiniteCongruenceSubgroup ↔
      ∀ w, ContinuousMulEquiv.piUnits a w ∈ m.localInfiniteCongruenceSubgroup w := by
  change ContinuousMulEquiv.piUnits a ∈
      Subgroup.pi Set.univ (fun w => m.localInfiniteCongruenceSubgroup w) ↔ _
  rw [Subgroup.mem_pi]
  simp only [Set.mem_univ, true_implies]

@[simp]
theorem mem_infiniteCongruenceSubgroup_iff
    (m : Modulus K) (a : InfiniteIdeleGroup K) :
    a ∈ m.infiniteCongruenceSubgroup ↔
      ∀ v : RealPlace K, v ∈ m.infinitePart →
        ContinuousMulEquiv.piUnits a v.1 ∈ infinitePositiveSubgroup v.1 :=
  by
    rw [mem_infiniteCongruenceSubgroup_iff_local]
    constructor
    · intro ha v hv
      have hlocal := ha v.1
      rw [localInfiniteCongruenceSubgroup_of_mem m v hv] at hlocal
      exact hlocal
    · intro ha w
      by_cases hw : w.IsReal
      · by_cases hmem : (⟨w, hw⟩ : RealPlace K) ∈ m.infinitePart
        · simpa [localInfiniteCongruenceSubgroup, hw, hmem] using
            ha ⟨w, hw⟩ hmem
        · simp [localInfiniteCongruenceSubgroup, hw, hmem]
      · simp [localInfiniteCongruenceSubgroup, hw]

/-- The idèle congruence subgroup attached to a full ray modulus. -/
def ideleCongruenceSubgroup (m : Modulus K) :
    Subgroup (IdeleGroup K) :=
  m.infiniteCongruenceSubgroup.prod
    (finiteCongruenceSubgroup m.finitePart)

@[simp]
theorem mem_ideleCongruenceSubgroup_iff
    (m : Modulus K) (a : IdeleGroup K) :
    a ∈ m.ideleCongruenceSubgroup ↔
      a.1 ∈ m.infiniteCongruenceSubgroup ∧
        a.2 ∈ finiteCongruenceSubgroup m.finitePart :=
  Iff.rfl

end Modulus

end RayClass
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_RayClass_Ideal
attribute [-instance] _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.LubinTate.compatibleGroupFamiliesGroup _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Ideals prime to a ray-class modulus

This file defines the subgroup of fractional ideals prime to a modulus,
connects it with the corresponding finite-idele higher-unit conditions, and
develops the approximation maps used in ray-class ideal constructions.
-/

open scoped NumberField WithZero Classical
open NumberField IsDedekindDomain

noncomputable section


variable {K : Type*} [Field K] [NumberField K]

namespace RayClass

/-- Fractional ideals having valuation zero at every finite prime in the
support of the modulus. -/
def primeToModulusIdeals (m : Modulus K) :
    Subgroup (FractionalIdealGroup K) where
  carrier := {I | ∀ v, v ∈ m.finitePart.support →
    FractionalIdeal.count K v
      (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = 0}
  one_mem' v _ := FractionalIdeal.count_one K v
  mul_mem' {I J} hI hJ v hv := by
    rw [Units.val_mul,
      FractionalIdeal.count_mul K v (Units.ne_zero I) (Units.ne_zero J),
      hI v hv, hJ v hv, add_zero]
  inv_mem' {I} hI v hv := by
    rw [Units.val_inv_eq_inv_val, FractionalIdeal.count_inv K v,
      hI v hv, neg_zero]

@[simp]
theorem mem_primeToModulusIdeals_iff
    (m : Modulus K) (I : FractionalIdealGroup K) :
    I ∈ primeToModulusIdeals m ↔
      ∀ v, v ∈ m.finitePart.support →
        FractionalIdeal.count K v
          (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = 0 :=
  Iff.rfl

/-- A finite prime outside the support of `m`, regarded as an element of
the group of fractional ideals prime to `m`. -/
def primeToModulusIdeal
    (m : Modulus K)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ m.finitePart.support) :
    primeToModulusIdeals m :=
  ⟨FractionalIdealGroup.prime v, by
    intro w hw
    have hwv : w ≠ v := by
      intro h
      exact hv (h ▸ hw)
    change
      FractionalIdeal.count K w
          (v.asIdeal :
            FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
        0
    exact
      FractionalIdeal.count_maximal_coprime
        K w hwv.symm⟩

/-- Coercing a prime outside the modulus support recovers its prime
fractional ideal. -/
@[simp]
theorem primeToModulusIdeal_coe
    (m : Modulus K)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ m.finitePart.support) :
    (primeToModulusIdeal m v hv :
        FractionalIdealGroup K) =
      FractionalIdealGroup.prime v :=
  rfl

/-- Finite ideles satisfying the higher-unit condition at every prime in
the support of the modulus. -/
def finitePrimeToModulusSubgroup (m : Modulus K) :
    Subgroup (FiniteIdeleGroup K) where
  carrier := {a | ∀ v, v ∈ m.finitePart.support →
    a v ∈ localHigherUnitGroup v (m.finitePart v)}
  one_mem' v _ := (localHigherUnitGroup v (m.finitePart v)).one_mem
  mul_mem' ha hb v hv :=
    (localHigherUnitGroup v (m.finitePart v)).mul_mem (ha v hv) (hb v hv)
  inv_mem' ha v hv :=
    (localHigherUnitGroup v (m.finitePart v)).inv_mem (ha v hv)

/-- Ideles satisfying the infinite positivity and finite higher-unit
conditions of a modulus. -/
def idelePrimeToModulusSubgroup (m : Modulus K) :
    Subgroup (IdeleGroup K) :=
  m.infiniteCongruenceSubgroup.prod
    (finitePrimeToModulusSubgroup m)

theorem localHigherUnitGroup_le_integralUnits
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    localHigherUnitGroup v n ≤
      (v.adicCompletionIntegers K).units := by
  intro x hx
  rw [mem_localHigherUnitGroup_iff] at hx
  obtain ⟨y, rfl, _⟩ := hx
  exact y.property

theorem fractionalIdeal_mem_primeToModulusIdeals
    (m : Modulus K) (a : IdeleGroup K)
    (ha : a ∈ idelePrimeToModulusSubgroup m) :
    IdeleGroup.fractionalIdeal a ∈ primeToModulusIdeals m := by
  intro v hv
  change FractionalIdeal.count K v
      (((FractionalIdealGroup.factorization (K := K))
        (FiniteIdeleGroup.valuationVector a.2) :
          FractionalIdealGroup K) :
        FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = 0
  rw [FractionalIdealGroup.count_factorization,
    FiniteIdeleGroup.valuationVector_apply]
  apply (FiniteIdeleGroup.localOrder_eq_zero_iff v (a.2 v)).2
  exact localHigherUnitGroup_le_integralUnits v (m.finitePart v) (ha.2 v hv)

/-- The fractional-ideal map restricted to ideles prime to a modulus. -/
def primeToIdealMap (m : Modulus K) :
    idelePrimeToModulusSubgroup m →*
      primeToModulusIdeals m where
  toFun a :=
    ⟨IdeleGroup.fractionalIdeal a,
      fractionalIdeal_mem_primeToModulusIdeals m a a.property⟩
  map_one' := by
    apply Subtype.ext
    exact map_one _
  map_mul' a b := by
    apply Subtype.ext
    exact map_mul _ _ _

/-- A finite idele with a prescribed valuation vector away from the
support of a modulus and value one on its support. -/
def valuationVectorSectionPrimeTo
    (m : Modulus K)
  (e : HeightOneSpectrum (𝓞 K) →₀ ℤ) :
    FiniteIdeleGroup K :=
  ⟨fun v =>
      if v ∈ m.finitePart.support then 1
      else FiniteIdeleGroup.chosenLocalOrderSection v (e v), by
    filter_upwards
      [m.finitePart.support.eventually_cofinite_notMem,
        e.support.eventually_cofinite_notMem] with v hvm he
    simp only [hvm, ↓reduceIte]
    apply (FiniteIdeleGroup.localOrder_eq_zero_iff v _).1
    rw [FiniteIdeleGroup.localOrder_chosenLocalOrderSection,
      Finsupp.notMem_support_iff.mp he]⟩

theorem valuationVector_valuationVectorSectionPrimeTo
    (m : Modulus K)
    (e : HeightOneSpectrum (𝓞 K) →₀ ℤ)
    (he : ∀ v, v ∈ m.finitePart.support → e v = 0) :
    FiniteIdeleGroup.valuationVector
        (valuationVectorSectionPrimeTo m e) =
      Multiplicative.ofAdd e := by
  apply Multiplicative.ext
  ext v
  rw [FiniteIdeleGroup.valuationVector_apply]
  by_cases hv : v ∈ m.finitePart.support
  · change
      (FiniteIdeleGroup.localOrder v
        (if v ∈ m.finitePart.support then 1
          else FiniteIdeleGroup.chosenLocalOrderSection v (e v))).toAdd =
        e v
    rw [ite_eq_left hv, map_one]
    exact (he v hv).symm
  · change
      (FiniteIdeleGroup.localOrder v
        (if v ∈ m.finitePart.support then 1
          else FiniteIdeleGroup.chosenLocalOrderSection v (e v))).toAdd =
        e v
    rw [ite_eq_right hv,
      FiniteIdeleGroup.localOrder_chosenLocalOrderSection]

theorem primeToIdealMap_surjective (m : Modulus K) :
    Function.Surjective (primeToIdealMap m) := by
  intro I
  let e : HeightOneSpectrum (𝓞 K) →₀ ℤ :=
    FractionalIdealGroup.countVector (I : FractionalIdealGroup K)
  have he : ∀ v, v ∈ m.finitePart.support → e v = 0 := by
    intro v hv
    exact I.property v hv
  let a : IdeleGroup K :=
    (1, valuationVectorSectionPrimeTo m e)
  have ha : a ∈ idelePrimeToModulusSubgroup m := by
    constructor
    · exact m.infiniteCongruenceSubgroup.one_mem
    · intro v hv
      change
        (if v ∈ m.finitePart.support then 1
          else FiniteIdeleGroup.chosenLocalOrderSection v (e v)) ∈
            localHigherUnitGroup v (m.finitePart v)
      rw [ite_eq_left hv]
      exact (localHigherUnitGroup v (m.finitePart v)).one_mem
  refine ⟨⟨a, ha⟩, ?_⟩
  apply Subtype.ext
  apply FractionalIdealGroup.ext_count
  intro v
  change FractionalIdeal.count K v
      (((FractionalIdealGroup.factorization (K := K))
        (FiniteIdeleGroup.valuationVector
          (valuationVectorSectionPrimeTo m e)) :
          FractionalIdealGroup K) :
        FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
      FractionalIdeal.count K v
        ((I : FractionalIdealGroup K) :
          FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
  rw [valuationVector_valuationVectorSectionPrimeTo m e he,
    FractionalIdealGroup.count_factorization]
  exact FractionalIdealGroup.countVector_apply I v

/-- The congruence subgroup, viewed inside the subgroup of ideles prime
to the modulus. -/
def congruenceSubgroupInPrimeTo (m : Modulus K) :
    Subgroup (idelePrimeToModulusSubgroup m) :=
  m.ideleCongruenceSubgroup.subgroupOf
    (idelePrimeToModulusSubgroup m)

theorem primeToIdealMap_ker (m : Modulus K) :
    (primeToIdealMap m).ker =
      congruenceSubgroupInPrimeTo m := by
  ext a
  constructor
  · intro ha
    have hintegral :
        (a : IdeleGroup K) ∈
          IdeleGroup.integralAtFinitePlaces (K := K) := by
      rw [← IdeleGroup.fractionalIdeal_ker,
        MonoidHom.mem_ker]
      exact congrArg Subtype.val
        (MonoidHom.mem_ker.mp ha)
    constructor
    · exact a.property.1
    · intro v
      by_cases hv : v ∈ m.finitePart.support
      · exact a.property.2 v hv
      · rw [Finsupp.notMem_support_iff.mp hv,
          localHigherUnitGroup_zero]
        exact hintegral v
  · intro ha
    apply MonoidHom.mem_ker.mpr
    apply Subtype.ext
    change IdeleGroup.fractionalIdeal (a : IdeleGroup K) = 1
    rw [← MonoidHom.mem_ker,
      IdeleGroup.fractionalIdeal_ker]
    intro v
    exact localHigherUnitGroup_le_integralUnits v (m.finitePart v) (ha.2 v)

/-- Principal ideles satisfying the modulus conditions, considered inside
`I_K^(m)`. -/
def principalSubgroupInPrimeTo (m : Modulus K) :
    Subgroup (idelePrimeToModulusSubgroup m) :=
  Subgroup.comap (idelePrimeToModulusSubgroup m).subtype
    (IdeleGroup.principalSubgroup K)

/-- Principal ideals generated by a totally positive element congruent to
one modulo the finite modulus. -/
def principalRayIdealSubgroup (m : Modulus K) :
    Subgroup (primeToModulusIdeals m) :=
  Subgroup.map (primeToIdealMap m)
    (principalSubgroupInPrimeTo m)

/-- The ideal-theoretic ray class group `J_K^m / P_K^m`. -/
abbrev IdealRayClassGroup (m : Modulus K) :=
  primeToModulusIdeals m ⧸ principalRayIdealSubgroup m

/-- The canonical projection from ideles prime to the modulus to the
ideal-theoretic ray class group. -/
def idealRayProjection (m : Modulus K) :
    idelePrimeToModulusSubgroup m →*
      IdealRayClassGroup m :=
  (QuotientGroup.mk' (principalRayIdealSubgroup m)).comp
    (primeToIdealMap m)

/-- The subgroup generated by congruence ideles and principal ideles
inside the ideles prime to a modulus. -/
def raySubgroupInPrimeTo (m : Modulus K) :
    Subgroup (idelePrimeToModulusSubgroup m) :=
  congruenceSubgroupInPrimeTo m ⊔
    principalSubgroupInPrimeTo m

theorem idealRayProjection_surjective (m : Modulus K) :
    Function.Surjective (idealRayProjection m) := by
  intro c
  obtain ⟨I, rfl⟩ :=
    QuotientGroup.mk'_surjective
      (principalRayIdealSubgroup m) c
  obtain ⟨a, rfl⟩ := primeToIdealMap_surjective m I
  exact ⟨a, rfl⟩

theorem idealRayProjection_ker (m : Modulus K) :
    (idealRayProjection m).ker =
      raySubgroupInPrimeTo m := by
  ext a
  constructor
  · intro ha
    change QuotientGroup.mk'
        (principalRayIdealSubgroup m)
        (primeToIdealMap m a) = 1 at ha
    rw [QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at ha
    obtain ⟨p, hp, hpa⟩ := ha
    let n : idelePrimeToModulusSubgroup m := a * p⁻¹
    have hn : n ∈ congruenceSubgroupInPrimeTo m := by
      rw [← primeToIdealMap_ker m, MonoidHom.mem_ker]
      change primeToIdealMap m (a * p⁻¹) = 1
      rw [map_mul, map_inv, hpa]
      simp
    rw [raySubgroupInPrimeTo, Subgroup.mem_sup]
    refine ⟨n, hn, p, hp, ?_⟩
    dsimp [n]
    group
  · intro ha
    rw [raySubgroupInPrimeTo, Subgroup.mem_sup] at ha
    obtain ⟨n, hn, p, hp, rfl⟩ := ha
    change QuotientGroup.mk'
        (principalRayIdealSubgroup m)
        (primeToIdealMap m (n * p)) = 1
    rw [map_mul]
    have hn' : primeToIdealMap m n = 1 :=
      MonoidHom.mem_ker.mp
        ((primeToIdealMap_ker m).symm ▸ hn)
    rw [hn', one_mul]
    rw [QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    exact ⟨p, hp, rfl⟩

/-- The quotient of ideles prime to the modulus by the full ray subgroup,
identified with the ideal-theoretic ray class group. -/
def quotientRaySubgroupEquivIdealRayClassGroup
    (m : Modulus K) :
    idelePrimeToModulusSubgroup m ⧸
        raySubgroupInPrimeTo m ≃*
      IdealRayClassGroup m :=
  (QuotientGroup.quotientMulEquivOfEq
      (idealRayProjection_ker m).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (idealRayProjection m)
      (idealRayProjection_surjective m))

/-- The quotient equivalence induced by the ideal-ray projection evaluates on
the class of a prime-to-modulus idele as the original projection. -/
@[simp]
theorem quotientRaySubgroupEquivIdealRayClassGroup_mk
    (m : Modulus K) (a : idelePrimeToModulusSubgroup m) :
    quotientRaySubgroupEquivIdealRayClassGroup m
        (QuotientGroup.mk' (raySubgroupInPrimeTo m) a) =
      idealRayProjection m a := by
  rw [quotientRaySubgroupEquivIdealRayClassGroup,
    MulEquiv.trans_apply, QuotientGroup.mk'_apply,
    QuotientGroup.quotientMulEquivOfEq_mk]
  exact QuotientGroup.kerLift_mk (idealRayProjection m) a

/-! ### Simultaneous approximation at the places in a modulus -/

end RayClass
end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_DiscreteValuationField_FiniteExtension_Degree
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.residueField_charP_residueCharacteristic _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_mul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.Henselian.integralClosureValuationSubringIntegerMapOfMemOrInv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace ValuationTheory

/-!
# Finite valued extension consequences

This file collects theorem-level consequences around finite valued extensions:
canonical local-Dedekind degree formulas, uniqueness criteria for extended
valuations, and the algebra equivalence identifying an actual integral-closure
valuation ring with mathlib's `integralClosure`.
-/

noncomputable section

universe u v w x y

namespace DiscreteValuationField
namespace ValuedExtension

open ValuationTheory.DiscreteValuationField.Valuation

variable {K : Type u} {L : Type w} [Field K] [Field L]
variable [Algebra K L] [FiniteDimensional K L]
variable (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
variable [base.valuation.HasExtension target.valuation]

/-- In a finite separable extension, once the actual integral closure has the
valuation-ring dichotomy, the constructed integral-closure valuation ring has a
unique prime over the base maximal ideal.

The proof uses real structure, not a certificate: the constructed valuation
ring is the actual integral closure, hence Dedekind over the base DVR; a prime
whose contraction is the base maximal ideal is nonzero by injectivity of the
canonical integer map, hence maximal by the dimension-one property, and then
equal to the unique maximal ideal because the constructed ring is local. -/
theorem prime_eq_maximalIdeal_of_comap_integralClosureValuationSubringIntegerMap_eq_maximalIdeal
    (base : CompleteDVF.{u, v} K)
    [Algebra.IsSeparable K L]
    (hval :
      ∀ z : L,
        z ∈ (integralClosure base.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure base.valuationSubring L).toSubring)
    (P :
      Ideal
        (integralClosureValuationSubringOfMemOrInv
          (L := L) base.valuation hval))
    (hP : P.IsPrime)
    (hcomap :
      P.comap
          (integralClosureValuationSubringIntegerMapOfMemOrInv
            (K := K) (L := L) base hval) =
        base.maximalIdeal) :
    P =
      IsLocalRing.maximalIdeal
        (integralClosureValuationSubringOfMemOrInv
          (L := L) base.valuation hval) := by
  let B :=
    integralClosureValuationSubringOfMemOrInv
      (L := L) base.valuation hval
  let i : base.valuationSubring →+* B :=
    integralClosureValuationSubringIntegerMapOfMemOrInv
      (K := K) (L := L) base hval
  let : base.valuation.HasExtension B.valuation :=
    integralClosureValuationSubringOfMemOrInv_hasExtension
      (L := L) base.valuation hval
  let : IsFractionRing base.valuationSubring K :=
    base_valuationSubring_isFractionRing (K := K) base
  let : IsDiscreteValuationRing base.valuationSubring :=
    base.valuationSubring_isDiscreteValuationRing
  let : IsDedekindDomain base.valuationSubring := inferInstance
  let : Algebra base.valuationSubring B := RingHom.toAlgebra i
  let : IsScalarTower base.valuationSubring B L :=
    IsScalarTower.of_algebraMap_eq (by
      intro a
      rfl)
  let : IsIntegralClosure B base.valuationSubring L :=
    integralClosureValuationSubringOfMemOrInv_isIntegralClosure
      (L := L) base.valuation hval
  let : IsDedekindDomain B :=
    IsIntegralClosure.isDedekindDomain base.valuationSubring K L B
  have hi : Function.Injective i :=
    integralClosureValuationSubringIntegerMapOfMemOrInv_injective
      (K := K) (L := L) base hval
  have hP_ne_bot : P ≠ ⊥ := by
    have hnot_le_bot : ¬ base.maximalIdeal ≤ ⊥ := by
      intro hle
      exact base.maximalIdeal_ne_bot (le_antisymm hle bot_le)
    obtain ⟨a, ha_max, ha_not_bot⟩ := Set.not_subset.mp hnot_le_bot
    have ha_ne_zero : a ≠ 0 := by
      intro ha
      exact ha_not_bot (by simp [ha])
    intro hPbot
    have ha_comap : a ∈ P.comap i := by
      simpa [B, i, hcomap] using ha_max
    have hai_mem : i a ∈ P := by
      simpa [Ideal.mem_comap] using ha_comap
    have hai_zero : i a = 0 := by
      simpa [hPbot] using hai_mem
    exact ha_ne_zero (hi (by simpa using hai_zero))
  exact IsLocalRing.eq_maximalIdeal (hP.isMaximal hP_ne_bot)

end ValuedExtension
end DiscreteValuationField

end

end ValuationTheory
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_DiscreteValuationField_FiniteExtension_Uniqueness
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.HilbertRamification.Dedekind.basePrime_isPrime _root_.LocalFieldTheory.DiscreteValuationField.LocalField.residueField_charP_residueCharacteristic _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedMaximalIdeal.instIsMaximal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false
/-! Provides the public declarations in the `ValuationTheory.DiscreteValuationField.FiniteExtension.Uniqueness` Lean module. -/

namespace ValuationTheory

noncomputable section

universe u v w x y

namespace DiscreteValuationField
namespace ValuedExtension

variable {K : Type u} {L : Type w} [Field K] [Field L]
variable [Algebra K L] [FiniteDimensional K L]
variable (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
variable [base.valuation.HasExtension target.valuation]

/-- Finite-separable form of the Henselian uniqueness bridge.

After the Henselian part proves the valuative dichotomy for the actual
integral closure, finite separability supplies the prime uniqueness over the
base maximal ideal by Dedekind theory.  Thus no separate local-map, center
equality, integral-inclusion, or module-finiteness certificates are needed to
deduce uniqueness of the valuation extension. -/
theorem hasUniqueValuationExtension_of_integralClosure_mem_or_inv

    [Algebra.IsSeparable K L]
    (hval :
      ∀ z : L,
        z ∈ (integralClosure base.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure base.valuationSubring L).toSubring) :
    HasUniqueValuationExtension.{u, v, w, x, y} (base := base) (target := target) :=
  (hasUniqueValuationExtension_of_integralClosure_mem_or_inv_of_unique_primes_over_base_maximal base target)
    hval
    (by
      let B :=
        ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
          (L := L) base.valuation hval
      let i : base.valuationSubring →+* B :=
        integralClosureValuationSubringIntegerMapOfMemOrInv
          (K := K) (L := L) base hval
      change ∀ P : Ideal B, P.IsPrime → P.comap i = base.maximalIdeal →
        P = IsLocalRing.maximalIdeal B
      intro P hP hcomap
      exact
        prime_eq_maximalIdeal_of_comap_integralClosureValuationSubringIntegerMap_eq_maximalIdeal
          (K := K) (L := L) (base := base) hval P hP hcomap)

/-- Finite-separable uniqueness once the actual integral closure is local.

This is the sharpened Henselian frontier: after the Henselian argument proves
that the finite integral closure is a local ring, Dedekind theory makes it a
valuation ring and the valuative-dichotomy bridge above supplies uniqueness of
all valuation extensions. -/
theorem hasUniqueValuationExtension_of_integralClosure_isLocalRing

    [Algebra.IsSeparable K L]
    [IsLocalRing (integralClosureIntegers base target)] :
    HasUniqueValuationExtension.{u, v, w, x, y} (base := base) (target := target) :=
  (hasUniqueValuationExtension_of_integralClosure_mem_or_inv base target)
    (integralClosure_mem_or_inv_of_isLocalRing base target)

/-- Finite-separable uniqueness once the residue fiber over the base maximal
ideal has at most one prime.

The actual integral closure has a prime above the base maximal ideal by
going-up, and the fiber order-isomorphism identifies uniqueness in the fiber
with uniqueness of primes above the base maximal ideal.  The already-proved
singleton/local bridge then supplies valuation uniqueness. -/
theorem hasUniqueValuationExtension_of_integralClosure_base_maximal_fiber_subsingleton

    [Algebra.IsSeparable K L]
    [Subsingleton
      (PrimeSpectrum (base.maximalIdeal.Fiber (integralClosureIntegers base target)))] :
    HasUniqueValuationExtension.{u, v, w, x, y} (base := base) (target := target) := by
  let : IsLocalRing (integralClosureIntegers base target) :=
    (integralClosure_isLocalRing_of_base_maximal_fiber_subsingleton base target)
  exact
    (hasUniqueValuationExtension_of_integralClosure_isLocalRing
      (K := K) (L := L) (base := base) (target := target)  :
        HasUniqueValuationExtension.{u, v, w, x, y}
          (base := base) (target := target))

/-- Finite-separable uniqueness from the natural Henselian-pair ideal in the
actual integral closure.

The kernel computation for the residue-fiber includeRight map identifies its
kernel with base.maximalIdeal.map; hence a Henselian proof for that natural
ideal is enough to enter the finite-extension uniqueness bridge. -/
theorem hasUniqueValuationExtension_of_integralClosure_base_maximal_map_henselianRing

    [Algebra.IsSeparable K L]
    [HenselianRing (integralClosureIntegers base target)
      (base.maximalIdeal.map
        (algebraMap base.valuationSubring (integralClosureIntegers base target)))] :
    HasUniqueValuationExtension.{u, v, w, x, y} (base := base) (target := target) := by
  let : Subsingleton
      (PrimeSpectrum (base.maximalIdeal.Fiber (integralClosureIntegers base target))) :=
    (integralClosure_base_maximal_fiber_subsingleton_of_henselianRing_maximalIdeal_map base target)
  exact
    (hasUniqueValuationExtension_of_integralClosure_base_maximal_fiber_subsingleton
      (K := K) (L := L) (base := base) (target := target)  :
        HasUniqueValuationExtension.{u, v, w, x, y}
          (base := base) (target := target))


/-- Finite separable extensions of complete DVFs have a unique extension of the
base valuation, up to mathlib's valuation equivalence.

The proof routes through the actual integral closure: finite-module completeness
makes the ideal generated by the base maximal ideal Henselian there, and the
residue-fiber idempotent argument collapses the possible primes above the base
maximal ideal. -/
theorem hasUniqueValuationExtension_of_finite_separable

    [Algebra.IsSeparable K L] :
    HasUniqueValuationExtension.{u, v, w, x, y} (base := base) (target := target) := by
  let : HenselianRing (integralClosureIntegers base target)
      (base.maximalIdeal.map
        (algebraMap base.valuationSubring (integralClosureIntegers base target))) :=
    (integralClosure_base_maximal_map_henselianRing base target)
  exact
    (hasUniqueValuationExtension_of_integralClosure_base_maximal_map_henselianRing
      (K := K) (L := L) (base := base) (target := target)  :
        HasUniqueValuationExtension.{u, v, w, x, y}
          (base := base) (target := target))


/-- In a finite separable extension, any valuation subring whose valuation
extends the base valuation is the chosen target valuation ring. -/
theorem target_valuationSubring_eq_of_finite_separable

    [Algebra.IsSeparable K L]
    (B : ValuationSubring L) [base.valuation.HasExtension B.valuation] :
    target.valuation.valuationSubring = B := by
  exact target_valuationSubring_eq_of_hasUniqueValuationExtension
    (K := K) (L := L) (base := base) (target := target)
    ((hasUniqueValuationExtension_of_finite_separable base target) :
      HasUniqueValuationExtension.{u, v, w, x, w}
        (base := base) (target := target)) B

/-- In a finite separable extension, the chosen target valuation ring is the
actual integral closure of the base valuation ring in `L`. -/
theorem target_valuationSubring_isIntegralClosure_of_finite_separable

    [Algebra.IsSeparable K L]
    [IsScalarTower base.valuationSubring target.valuationSubring L] :
    IsIntegralClosure target.valuationSubring base.valuationSubring L := by
  let hval := (integralClosure_mem_or_inv_of_finite_separable base target)
  let B :=
    ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
      (L := L) base.valuation hval
  let : base.valuation.HasExtension B.valuation :=
    ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv_hasExtension
      (L := L) base.valuation hval
  have htarget_eq : target.valuation.valuationSubring = B :=
    (target_valuationSubring_eq_of_finite_separable base target) B
  have hB : IsIntegralClosure B base.valuationSubring L :=
    ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv_isIntegralClosure
      (L := L) base.valuation hval
  change IsIntegralClosure target.valuation.valuationSubring base.valuationSubring L
  rw [htarget_eq]
  exact hB

end ValuedExtension
end DiscreteValuationField

end

end ValuationTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_FiniteExtensionCompleteDVF
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.residueField_charP_residueCharacteristic _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Complete-DVF packages for local fields and their finite extensions

The canonical complete discrete valuation on a nonarchimedean local field,
and an integral-closure valuation chosen on each finite separable extension.
-/

noncomputable section

namespace LocalFieldTheory

open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension
open scoped ValuativeRel

universe u v y

/-! ## The canonical complete discrete valuation -/

/-- The valuation integer ring of a finite separable local extension is the
integral closure of the base valuation integer ring. -/
theorem localCompleteDVF_integerRing_isIntegralClosure
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)] :
    IsIntegralClosure 𝒪[L] 𝒪[K] L := by
  let : (localCompleteDVF K).valuation.HasExtension
      (localCompleteDVF L).valuation :=
    localCompleteDVFValuation_hasExtension K L
  let : IsScalarTower
      (localCompleteDVF K).valuationSubring
      (localCompleteDVF L).valuationSubring L :=
    Valuation.valuationSubring_isScalarTower_of_hasExtension
      (localCompleteDVF K).valuation (localCompleteDVF L).valuation
  exact
    target_valuationSubring_isIntegralClosure_of_finite_separable
      (K := K) (L := L) (localCompleteDVF K) (localCompleteDVF L)

/-! ## Chosen ramification data for an arbitrary finite local extension -/

end LocalFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Adele_IntegralTensorSupport_Lattice
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Integral lattices in relative tensor coordinates

This module chooses a common integral scale for a field basis, constructs the
associated integer lattice, and isolates the finite set of primes where its
local integrality properties can fail.
-/

open scoped NumberField TensorProduct NNReal
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations

universe u v

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

/-- The original integral scaling factor, now viewed in `𝓞 K`. -/
noncomputable def relativeBasisIntegralScaleInRingOfIntegers :
    𝓞 K :=
  algebraMap ℤ (𝓞 K)
    (chosenRelativeBasisIntegralScale (K := K) (L := L))
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Extension_IdealClass
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Extension of ideles and ideal classes

For a finite Galois extension of number fields, scalar extension of the
relative adele algebra followed by the relative-to-ordinary comparison
gives the usual extension map on ideles.  This file descends that map to
idele classes and compares it with extension of fractional ideals and
ideal classes.
-/

open scoped NumberField TensorProduct nonZeroDivisors
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations

universe u v w

variable
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

namespace FractionalIdealGroup

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Extension of nonzero fractional ideals along the inclusion of number
fields. -/
noncomputable def extension :
    FractionalIdealGroup K →* FractionalIdealGroup L :=
  Units.map
    (FractionalIdeal.extendedHom L (𝓞 L)).toMonoidHom

omit [FiniteDimensional K L] [IsGalois K L] in
/-- On a prime fractional ideal, extension is the fractional ideal
associated with the mapped integral ideal. -/
theorem extension_prime_val
    (w : HeightOneSpectrum (𝓞 K)) :
    ((extension K L (prime w) : FractionalIdealGroup L) :
      FractionalIdeal (nonZeroDivisors (𝓞 L)) L) =
      (w.asIdeal.map (algebraMap (𝓞 K) (𝓞 L)) :
        FractionalIdeal (nonZeroDivisors (𝓞 L)) L) := by
  change FractionalIdeal.extendedHom L (𝓞 L)
      (w.asIdeal :
        FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = _
  exact
    FractionalIdeal.extendedHom_coeIdeal_eq_map
      L (𝓞 L) w.asIdeal

end FractionalIdealGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.Cyclic_Herbrand_HerbrandLowDegree_BinaryProduct
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Low-degree Tate cohomology of binary products

This specializes the dependent-product calculation to two possibly
different coefficient groups.  It is used to join the unrestricted and
integral parts of a supported idele group.
-/

noncomputable section

namespace CyclicCohomology

open CyclicCohomology.ProfiniteCohomology.Herbrand

universe uG uA

variable {G : Type uG} [Group G] [Fintype G]
variable (A B : Type uA)
variable [CommGroup A] [CommGroup B]
variable [MulDistribMulAction G A] [MulDistribMulAction G B]

noncomputable def piHerbrandHMinusOneEquivProd
    (σ : G) :
    (∀ i, HerbrandHMinusOne G
      (BinaryCoefficientFamily A B i) σ) ≃*
        HerbrandHMinusOne G A σ ×
          HerbrandHMinusOne G B σ where
  toFun x := ⟨x false, x true⟩
  invFun x
    | false => x.1
    | true => x.2
  left_inv x := by
    funext i
    cases i <;> rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

end CyclicCohomology
end
end

section
-- module Solutions.OAIQ244_DUKE.Cyclic_Herbrand_HerbrandLowDegree_Index
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.CyclicCohomology.herbrandH0EquivariantMulEquiv_mk _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Cardinal consequences of a Herbrand quotient

This file isolates the elementary cardinal arithmetic at the end of the
low-degree Herbrand quotient calculation.  If a finite low-degree Tate quotient has Herbrand
quotient equal to a natural number `n`, then its degree-zero cardinality is
`n` times its negative-first cardinality.  In particular the degree-zero
cardinality is at least `n`.
-/

noncomputable section

namespace CyclicCohomology

open CyclicCohomology.ProfiniteCohomology.Herbrand

universe uG uA

variable {G : Type uG} {A : Type uA}
    [Group G] [Fintype G]
    [CommGroup A] [MulDistribMulAction G A]

/-- Clearing the nonzero denominator in a Herbrand quotient whose value is
a natural number. -/
theorem herbrandH0_card_eq_mul_herbrandHMinusOne_card
    (σ : G) (n : ℕ)
    [Finite (HerbrandH0 G A)]
    [Finite (HerbrandHMinusOne G A σ)]
    (hquotient :
      herbrandQuotient (G := G) (A := A) σ = n) :
    Nat.card (HerbrandH0 G A) =
      n * Nat.card
        (HerbrandHMinusOne G A σ) := by
  rw [herbrandQuotient_eq_card_ratio] at hquotient
  have hden :
      ((Nat.card
          (HerbrandHMinusOne G A σ) : ℚ) ≠ 0) :=
    Nat.cast_ne_zero.mpr
      (Finite.card_pos
        (α := HerbrandHMinusOne G A σ)).ne'
  have hrat :
      (Nat.card (HerbrandH0 G A) : ℚ) =
        (n : ℚ) *
          Nat.card
            (HerbrandHMinusOne G A σ) :=
    (div_eq_iff hden).mp hquotient
  exact_mod_cast hrat

/-- Cardinal-arithmetic step for low-degree Herbrand cohomology: a natural-valued Herbrand quotient
is a lower bound for the degree-zero Tate quotient. -/
theorem le_herbrandH0_card_of_herbrandQuotient_eq_nat
    (σ : G) (n : ℕ)
    [Finite (HerbrandH0 G A)]
    [Finite (HerbrandHMinusOne G A σ)]
    (hquotient :
      herbrandQuotient (G := G) (A := A) σ = n) :
    n ≤ Nat.card (HerbrandH0 G A) := by
  rw [herbrandH0_card_eq_mul_herbrandHMinusOne_card
    σ n hquotient]
  calc
    n = n * 1 := by simp
    _ ≤ n *
        Nat.card
          (HerbrandHMinusOne G A σ) :=
      Nat.mul_le_mul_left n
        (Finite.card_pos
          (α := HerbrandHMinusOne G A σ))

/-- If the degree-zero cardinality is also bounded above by the natural
value of the Herbrand quotient, both low-degree cardinalities are forced:
`#H⁰ = n` and `#H⁻¹ = 1`. -/
theorem lowDegree_card_eq_of_herbrandQuotient_eq_nat_of_le
    (σ : G) (n : ℕ) (hn : 0 < n)
    [Finite (HerbrandH0 G A)]
    [Finite (HerbrandHMinusOne G A σ)]
    (hquotient :
      herbrandQuotient (G := G) (A := A) σ = n)
    (hle : Nat.card (HerbrandH0 G A) ≤ n) :
    Nat.card (HerbrandH0 G A) = n ∧
      Nat.card (HerbrandHMinusOne G A σ) = 1 := by
  let a := Nat.card (HerbrandH0 G A)
  let b := Nat.card (HerbrandHMinusOne G A σ)
  have hmul : a = n * b :=
    herbrandH0_card_eq_mul_herbrandHMinusOne_card
      σ n hquotient
  have hb : 1 ≤ b :=
    Finite.card_pos
      (α := HerbrandHMinusOne G A σ)
  have hnle : n ≤ a := by
    rw [hmul]
    simpa using Nat.mul_le_mul_left n hb
  have ha : a = n :=
    Nat.le_antisymm hle hnle
  refine ⟨ha, ?_⟩
  have hcancel : n * b = n * 1 := by
    rw [← hmul, ha, mul_one]
  exact Nat.eq_of_mul_eq_mul_left hn hcancel

end CyclicCohomology
end
end


