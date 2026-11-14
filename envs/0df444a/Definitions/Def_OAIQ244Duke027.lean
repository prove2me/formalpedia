-- Prove2me | Definitions.Def_OAIQ244Duke027
-- name    : OAIQ244Duke027
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T06:31:41.28513+00:00
-- url     : https://prove2.me/theorems/5d5ee466-212e-4c4f-8d49-68d2745e65a7
-- title:
--   Definitions bundle OAIQ244Duke027 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 106 declarations of OpenAI's Lean: 25 definitions and 81 theorems. The definitions and types are `CyclicCohomology.galoisGroupIntegerUnitsModPrincipalUnitsMapEquivHomOfIsIntegralClosure`, `CyclicCohomology.galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure`, `CyclicCohomology.galoisGroupIntegerUnitsModPrincipalUnitsMulDistribMulActionOfIsIntegralClosure`, `CyclicCohomology.herbrandH0PiEquiv`, `CyclicCohomology.herbrandH0ProdEquiv`, `CyclicCohomology.herbrandHMinusOnePiEquiv`, `CyclicCohomology.inducedHerbrandH0Equiv`, `CyclicCohomology.inducedHerbrandH0EquivOfFiniteCyclic`, `CyclicCohomology.inducedHerbrandHMinusOneEquiv`, `CyclicCohomology.inducedHerbrandHMinusOneEquivOfFiniteCyclic`, `CyclicCohomology.inducedNormKernelProductHom`, `CyclicCohomology.inducedNormKernelSectionHom`, `CyclicCohomology.integerUnitsModPrincipalUnitsAtLevelLift`, `CyclicCohomology.integerUnitsModPrincipalUnitsMapEquivOfIntegerRingEquiv`, `CyclicCohomology.integerUnitsModPrincipalUnitsMapOfIntegerRingEquiv`, `CyclicCohomology.integerUnitsModPrincipalUnitsMapOfLe`, `CyclicCohomology.integerUnitsModPrincipalUnitsSuccMap`, `CyclicCohomology.normKernelPiEquiv`, `CyclicCohomology.permutationFunctionOrbitEquiv`, `CyclicCohomology.piHerbrandH0EquivProd`, `CyclicCohomology.principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc`, `CyclicCohomology.trivialIntFixedToZModHom`, `CyclicCohomology.trivialIntHerbrandH0EquivZMod`, `LocalFieldTheory.chosenResidueAddEquivMaximalIdealPowSuccQuot`, `LocalFieldTheory.chosenResidueLinearEquivMaximalIdealPowSuccQuot`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `Cyclic_Herbrand_HerbrandLowDegree_BinaryProduct`, `Cyclic_Herbrand_HerbrandLowDegree_EquivariantEquiv`, `Cyclic_Herbrand_HerbrandLowDegree_Product`, `Cyclic_Herbrand_Induced`, `Cyclic_Herbrand_NormalBasisLattice`, `Cyclic_Herbrand_Permutation_LatticeHerbrand`, `Cyclic_Herbrand_Permutation_Module`, `Cyclic_Herbrand_PrincipalUnits_QuotientReps`, `Cyclic_Herbrand_PrincipalUnits_QuotientTower`, `Cyclic_Herbrand_Product`, `GlobalClassFieldTheory_Reciprocity_FinitePlaceArtin_NormRestriction`, `LocalField_DiscreteValuationField_FieldNorm`, `LocalField_NonarchimedeanLocalField_IdealQuotients`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke015`, `OAIQ244Duke016`, `OAIQ244Duke017`, `OAIQ244Duke020` and `OAIQ244Duke021` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke038`, `OAIQ244Duke040`, `OAIQ244Duke042` and `OAIQ244Duke044`.
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
import Mathlib.FieldTheory.Galois.Notation
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
import Definitions.Def_OAIQ244Duke020
import Definitions.Def_OAIQ244Duke021

section
-- module Solutions.OAIQ244_DUKE.Cyclic_Herbrand_Induced
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instCommGroupSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.finite_nsmulAddKernel_padicInt_pi _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerKernel _root_.LocalFieldTheory.finite_nsmulAddKernel_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.CyclicCohomology.instMulDistribMulActionBinaryCoefficientFamily _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.CyclicCohomology.fixedPiEquiv_apply_coe _root_.CyclicCohomology.herbrandH0EquivariantMulEquiv_mk _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalClassFieldTheory.chosenNormalBasisPrincipalUnitSubgroup_sigmaMinusOne_coe _root_.LocalClassFieldTheory.inducedRightCosetCoordinates_apply _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Multiplicative induced modules

This file supplies the multiplicative induced-module model used in the
Herbrand quotient calculation.  If `H ≤ G` acts on a commutative group `B`, then
`Ind_H^G B` is represented by the equivariant functions

`f : G → B`,  `f (h * x) = h • f x`.

The ambient group acts by right translation.  This convention is the one
used for the products of the local multiplicative groups above a place.
The basic equivariant-function model is supplied by `ProCGroups.InducedFunctions`;
this module adds the cyclic-coordinate and Herbrand calculations.
-/

noncomputable section

namespace CyclicCohomology

open CyclicCohomology.ProfiniteCohomology.Herbrand

universe uG uB

variable {G : Type uG} {B : Type uB}

export ProCGroups.InducedFunctions
  (inducedSubgroup InducedModule inducedEvaluation inducedEvaluation_apply)

section InducedHerbrandH0

variable [CommGroup G] [Fintype G] [CommGroup B]
variable (H : Subgroup G) [MulDistribMulAction H B]

attribute [local instance] CyclicCohomology.instFintypeSubtypeMemSubgroup_solutions
/-- Under evaluation of fixed points, global and subgroup norm images
correspond. -/
theorem inducedFixedEquiv_mem_tateNormSubgroup_iff
    (σ : G)
    (hgen : ∀ x : G, x ∈ Subgroup.zpowers σ)
    (x : fixedSubgroup G
      (InducedModule (B := B) H)) :
    x.1 ∈ tateNormSubgroup G
        (InducedModule (B := B) H) ↔
      (inducedFixedEquiv H x).1 ∈
        tateNormSubgroup H B := by
  constructor
  · rintro ⟨f, hf⟩
    refine
      ⟨inducedCoordinateProduct H σ hgen f, ?_⟩
    calc
      tateNorm H B
            (inducedCoordinateProduct H σ hgen f) =
          inducedEvaluation H
            (tateNorm G
              (InducedModule (B := B) H) f) :=
        (inducedEvaluation_tateNorm
          H σ hgen f).symm
      _ = inducedEvaluation H x.1 :=
        congrArg (inducedEvaluation H) hf
      _ = (inducedFixedEquiv H x).1 := rfl
  · rintro ⟨b, hb⟩
    refine ⟨inducedSection H σ hgen b, ?_⟩
    let y : fixedSubgroup G
        (InducedModule (B := B) H) :=
      ⟨tateNorm G (InducedModule (B := B) H)
          (inducedSection H σ hgen b),
        fun g ↦ smul_tateNorm_eq
          (G := G)
          (A := InducedModule (B := B) H) g _⟩
    have hy :
        inducedFixedEquiv H y =
          inducedFixedEquiv H x := by
      apply Subtype.ext
      change
        inducedEvaluation H y.1 =
          (inducedFixedEquiv H x).1
      calc
        inducedEvaluation H y.1 =
            tateNorm H B
              (inducedCoordinateProduct H σ hgen
                (inducedSection H σ hgen b)) :=
          inducedEvaluation_tateNorm H σ hgen
            (inducedSection H σ hgen b)
        _ = tateNorm H B b := by
          rw [inducedCoordinateProduct_section
            H σ hgen b]
        _ = (inducedFixedEquiv H x).1 := hb
    exact congrArg Subtype.val
      ((inducedFixedEquiv H).injective hy)

/-- Multiplicative Shapiro lemma in Tate degree zero. -/
noncomputable def inducedHerbrandH0Equiv (σ : G)
    (hgen : ∀ x : G, x ∈ Subgroup.zpowers σ) :
    HerbrandH0 G (InducedModule (B := B) H) ≃*
      HerbrandH0 H B := by
  let e :
      fixedSubgroup G (InducedModule (B := B) H) ≃*
        fixedSubgroup H B :=
    inducedFixedEquiv H
  let NG :=
    (tateNormSubgroup G
      (InducedModule (B := B) H)).subgroupOf
      (fixedSubgroup G
        (InducedModule (B := B) H))
  let NH :=
    (tateNormSubgroup H B).subgroupOf
      (fixedSubgroup H B)
  exact quotientMulEquivOfSplit
    NG NH e.toMonoidHom e.symm.toMonoidHom
    (fun y ↦ e.apply_symm_apply y)
    (fun x hx ↦ by
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact
        (inducedFixedEquiv_mem_tateNormSubgroup_iff
          H σ hgen x).mp hx)
    (fun y hy ↦ by
      rw [Subgroup.mem_subgroupOf] at hy ⊢
      have h :=
        (inducedFixedEquiv_mem_tateNormSubgroup_iff
          H σ hgen (e.symm y)).mpr
          (by simpa [e] using hy)
      simpa [e] using h)
    (fun x hx ↦ by
      have hx1 : x = 1 := by
        apply e.injective
        simpa [e] using hx
      rw [hx1]
      exact NG.one_mem)

end InducedHerbrandH0

section InducedHerbrandHMinusOne

variable [CommGroup G] [Fintype G] [CommGroup B]
variable (H : Subgroup G) [MulDistribMulAction H B]

attribute [local instance] CyclicCohomology.instNeZeroNatIndex_solutions
/-- If the product of the canonical coordinates is one, successive partial
products construct a `σ`-primitive. -/
theorem inducedCoordinateProduct_eq_one_mem_augmentation
    (σ : G)
    (hgen : ∀ x : G, x ∈ Subgroup.zpowers σ)
    (f : InducedModule (B := B) H)
    (hf :
      inducedCoordinateProduct H σ hgen f = 1) :
    f ∈ augmentationSubgroup G
      (InducedModule (B := B) H) σ := by
  let e : InducedModule (B := B) H ≃*
      (Fin H.index → B) :=
    inducedCoordinates H σ hgen
  let v : Fin H.index → B := e f
  let p : Fin H.index → B :=
    fun i ↦ finPartialProduct v i.1
  let c : InducedModule (B := B) H :=
    e.symm p
  have hc : e c = p := e.apply_symm_apply p
  have hprod :
      (∏ i : Fin H.index, v i) = 1 := by
    change
      inducedCoordinateProduct H σ hgen f = 1 at hf
    exact hf
  have hfull :
      finPartialProduct v H.index = 1 := by
    rw [finPartialProduct_full]
    exact hprod
  refine ⟨c, ?_⟩
  apply e.injective
  funext i
  change
    c.1 (σ ^ i.1 * σ) *
        (c.1 (σ ^ i.1))⁻¹ = v i
  have hci :
      c.1 (σ ^ i.1) = p i :=
    congrFun hc i
  by_cases hi : i.1 + 1 < H.index
  · let j : Fin H.index := ⟨i.1 + 1, hi⟩
    have hcj :
        c.1 (σ ^ j.1) = p j :=
      congrFun hc j
    have hpow :
        σ ^ i.1 * σ = σ ^ j.1 :=
      (pow_succ σ i.1).symm
    rw [hpow, hcj, hci]
    change
      finPartialProduct v (i.1 + 1) *
          (finPartialProduct v i.1)⁻¹ = v i
    rw [finPartialProduct_succ v i]
    simp [mul_assoc]
  · have hle : i.1 + 1 ≤ H.index :=
      Nat.succ_le_iff.mpr i.2
    have heq : i.1 + 1 = H.index :=
      le_antisymm hle (Nat.le_of_not_gt hi)
    have hc0 : c.1 1 = 1 := by
      have h := congrFun hc (0 : Fin H.index)
      change
        c.1 (σ ^ (0 : Fin H.index).1) =
          p 0 at h
      simpa [p] using h
    have hcwrap :
        c.1 (σ ^ i.1 * σ) = 1 := by
      calc
        c.1 (σ ^ i.1 * σ) =
            c.1 (σ ^ (i.1 + 1)) := by
          rw [pow_succ]
        _ = c.1 (σ ^ H.index) := by
          rw [heq]
        _ = subgroupGenerator H σ • c.1 1 := by
          simpa only [subgroupGenerator_coe, mul_one] using
            c.2 (subgroupGenerator H σ) 1
        _ = 1 := by
          rw [hc0, MulDistribMulAction.smul_one]
    have hsucc :=
      finPartialProduct_succ v i
    rw [heq] at hsucc
    have hmul :
        finPartialProduct v i.1 * v i = 1 :=
      hsucc.symm.trans hfull
    rw [hcwrap, hci, one_mul]
    change
      (finPartialProduct v i.1)⁻¹ = v i
    exact (mul_eq_one_iff_inv_eq).mp hmul

attribute [local instance] CyclicCohomology.instFintypeSubtypeMemSubgroup_solutions_1
/-- The transversal product carries the ambient norm kernel into the
subgroup norm kernel. -/
theorem inducedCoordinateProduct_mem_normKernel
    (σ : G)
    (hgen : ∀ x : G, x ∈ Subgroup.zpowers σ)
    {f : InducedModule (B := B) H}
    (hf : f ∈ normKernelSubgroup G
      (InducedModule (B := B) H)) :
    inducedCoordinateProduct H σ hgen f ∈
      normKernelSubgroup H B := by
  change
    tateNorm G (InducedModule (B := B) H) f = 1 at hf
  change
    tateNorm H B
      (inducedCoordinateProduct H σ hgen f) = 1
  calc
    tateNorm H B
          (inducedCoordinateProduct H σ hgen f) =
        inducedEvaluation H
          (tateNorm G
            (InducedModule (B := B) H) f) :=
      (inducedEvaluation_tateNorm
        H σ hgen f).symm
    _ = inducedEvaluation H 1 :=
      congrArg (inducedEvaluation H) hf
    _ = 1 := rfl

/-- The canonical section carries the subgroup norm kernel into the ambient
norm kernel. -/
theorem inducedSection_mem_normKernel (σ : G)
    (hgen : ∀ x : G, x ∈ Subgroup.zpowers σ)
    {b : B} (hb : b ∈ normKernelSubgroup H B) :
    inducedSection H σ hgen b ∈
      normKernelSubgroup G
        (InducedModule (B := B) H) := by
  change tateNorm H B b = 1 at hb
  let y : fixedSubgroup G
      (InducedModule (B := B) H) :=
    ⟨tateNorm G (InducedModule (B := B) H)
        (inducedSection H σ hgen b),
      fun g ↦ smul_tateNorm_eq
        (G := G)
        (A := InducedModule (B := B) H) g _⟩
  have hey : inducedFixedEquiv H y = 1 := by
    apply Subtype.ext
    change inducedEvaluation H y.1 = 1
    calc
      inducedEvaluation H y.1 =
          tateNorm H B
            (inducedCoordinateProduct H σ hgen
              (inducedSection H σ hgen b)) :=
        inducedEvaluation_tateNorm H σ hgen
          (inducedSection H σ hgen b)
      _ = tateNorm H B b := by
        rw [inducedCoordinateProduct_section
          H σ hgen b]
      _ = 1 := hb
  have hy : y = 1 :=
    (inducedFixedEquiv H).injective hey
  exact congrArg Subtype.val hy

/-- The transversal product maps augmentation subgroups compatibly. -/
theorem inducedCoordinateProduct_mem_augmentation
    (σ : G)
    (hgen : ∀ x : G, x ∈ Subgroup.zpowers σ)
    {f : InducedModule (B := B) H}
    (hf : f ∈ augmentationSubgroup G
      (InducedModule (B := B) H) σ) :
    inducedCoordinateProduct H σ hgen f ∈
      augmentationSubgroup H B
        (subgroupGenerator H σ) := by
  obtain ⟨c, rfl⟩ := hf
  refine ⟨c.1 1, ?_⟩
  exact
    (inducedCoordinateProduct_sigmaMinusOne
      H σ hgen c).symm

/-- The canonical section maps subgroup coboundaries to ambient
coboundaries. -/
theorem inducedSection_mem_augmentation (σ : G)
    (hgen : ∀ x : G, x ∈ Subgroup.zpowers σ)
    {b : B}
    (hb : b ∈ augmentationSubgroup H B
      (subgroupGenerator H σ)) :
    inducedSection H σ hgen b ∈
      augmentationSubgroup G
        (InducedModule (B := B) H) σ := by
  obtain ⟨c, rfl⟩ := hb
  let a₁ : InducedModule (B := B) H :=
    inducedSection H σ hgen
      (sigmaMinusOne H B
        (subgroupGenerator H σ) c)
  let a₂ : InducedModule (B := B) H :=
    sigmaMinusOne G
      (InducedModule (B := B) H) σ
      (inducedSection H σ hgen c)
  have hnu₁ :
      inducedCoordinateProduct H σ hgen a₁ =
        sigmaMinusOne H B
          (subgroupGenerator H σ) c :=
    inducedCoordinateProduct_section H σ hgen _
  have hnu₂ :
      inducedCoordinateProduct H σ hgen a₂ =
        sigmaMinusOne H B
          (subgroupGenerator H σ) c := by
    calc
      inducedCoordinateProduct H σ hgen a₂ =
          sigmaMinusOne H B
            (subgroupGenerator H σ)
            ((inducedSection H σ hgen c).1 1) :=
        inducedCoordinateProduct_sigmaMinusOne
          H σ hgen
            (inducedSection H σ hgen c)
      _ = sigmaMinusOne H B
            (subgroupGenerator H σ) c := by
        rw [inducedSection_apply_one
          H σ hgen c]
  let d : InducedModule (B := B) H :=
    a₁ * a₂⁻¹
  have hnud :
      inducedCoordinateProduct H σ hgen d = 1 := by
    calc
      inducedCoordinateProduct H σ hgen d =
          inducedCoordinateProduct H σ hgen a₁ *
            (inducedCoordinateProduct
              H σ hgen a₂)⁻¹ := by
        simp only [d, map_mul, map_inv]
      _ = 1 := by
        rw [hnu₁, hnu₂, mul_inv_cancel]
  have hd :
      d ∈ augmentationSubgroup G
        (InducedModule (B := B) H) σ :=
    inducedCoordinateProduct_eq_one_mem_augmentation
      H σ hgen d hnud
  have ha₂ :
      a₂ ∈ augmentationSubgroup G
        (InducedModule (B := B) H) σ :=
    ⟨inducedSection H σ hgen c, rfl⟩
  have hmul :=
    (augmentationSubgroup G
      (InducedModule (B := B) H) σ).mul_mem
        hd ha₂
  have heq : d * a₂ = a₁ := by simp [d]
  rw [heq] at hmul
  exact hmul

/-- Restriction of the transversal product to norm kernels. -/
noncomputable def inducedNormKernelProductHom (σ : G)
    (hgen : ∀ x : G, x ∈ Subgroup.zpowers σ) :
    normKernelSubgroup G
        (InducedModule (B := B) H) →*
      normKernelSubgroup H B where
  toFun f :=
    ⟨inducedCoordinateProduct H σ hgen f.1,
      inducedCoordinateProduct_mem_normKernel
        H σ hgen f.2⟩
  map_one' := by
    apply Subtype.ext
    exact map_one
      (inducedCoordinateProduct H σ hgen)
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul
      (inducedCoordinateProduct H σ hgen)
        x.1 y.1

/-- Restriction of the canonical section to norm kernels. -/
noncomputable def inducedNormKernelSectionHom (σ : G)
    (hgen : ∀ x : G, x ∈ Subgroup.zpowers σ) :
    normKernelSubgroup H B →*
      normKernelSubgroup G
        (InducedModule (B := B) H) where
  toFun b :=
    ⟨inducedSection H σ hgen b.1,
      inducedSection_mem_normKernel
        H σ hgen b.2⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (inducedSection H σ hgen)
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul (inducedSection H σ hgen)
      x.1 y.1

/-- Multiplicative Shapiro lemma in Tate degree minus one. -/
noncomputable def inducedHerbrandHMinusOneEquiv
    (σ : G)
    (hgen : ∀ x : G, x ∈ Subgroup.zpowers σ) :
    HerbrandHMinusOne G
        (InducedModule (B := B) H) σ ≃*
      HerbrandHMinusOne H B
        (subgroupGenerator H σ) := by
  let f :
      normKernelSubgroup G
          (InducedModule (B := B) H) →*
        normKernelSubgroup H B :=
    inducedNormKernelProductHom H σ hgen
  let s :
      normKernelSubgroup H B →*
        normKernelSubgroup G
          (InducedModule (B := B) H) :=
    inducedNormKernelSectionHom H σ hgen
  let IG :=
    (augmentationSubgroup G
      (InducedModule (B := B) H) σ).subgroupOf
        (normKernelSubgroup G
          (InducedModule (B := B) H))
  let IH :=
    (augmentationSubgroup H B
      (subgroupGenerator H σ)).subgroupOf
        (normKernelSubgroup H B)
  exact quotientMulEquivOfSplit
    IG IH f s
    (fun y ↦ by
      apply Subtype.ext
      exact inducedCoordinateProduct_section
        H σ hgen y.1)
    (fun x hx ↦ by
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact inducedCoordinateProduct_mem_augmentation
        H σ hgen hx)
    (fun y hy ↦ by
      rw [Subgroup.mem_subgroupOf] at hy ⊢
      exact inducedSection_mem_augmentation
        H σ hgen hy)
    (fun x hx ↦ by
      rw [Subgroup.mem_subgroupOf]
      apply
        inducedCoordinateProduct_eq_one_mem_augmentation
          H σ hgen x.1
      exact congrArg Subtype.val hx)

end InducedHerbrandHMinusOne

section FiniteCyclicGroup

variable [Group G] [Fintype G] [CommGroup B]
variable (H : Subgroup G) [MulDistribMulAction H B]

/-- Tate-degree-zero Shapiro equivalence for an ordinary finite cyclic
group. -/
noncomputable def inducedHerbrandH0EquivOfFiniteCyclic
    (σ : G)
    (hgen : ∀ x : G, x ∈ Subgroup.zpowers σ) :
    letI : Fintype H := Fintype.ofFinite H
    HerbrandH0 G (InducedModule (B := B) H) ≃*
      HerbrandH0 H B := by
  letI : Fintype H := Fintype.ofFinite H
  letI : IsCyclic G := ⟨⟨σ, hgen⟩⟩
  letI : CommGroup G := IsCyclic.commGroup
  exact inducedHerbrandH0Equiv H σ hgen

/-- Tate-degree-minus-one Shapiro equivalence for an ordinary finite cyclic
group. -/
noncomputable def inducedHerbrandHMinusOneEquivOfFiniteCyclic
    (σ : G)
    (hgen : ∀ x : G, x ∈ Subgroup.zpowers σ) :
    letI : Fintype H := Fintype.ofFinite H
    HerbrandHMinusOne G
        (InducedModule (B := B) H) σ ≃*
      HerbrandHMinusOne H B
        (subgroupGeneratorOfGenerator H σ hgen) := by
  letI : Fintype H := Fintype.ofFinite H
  letI : IsCyclic G := ⟨⟨σ, hgen⟩⟩
  letI : CommGroup G := IsCyclic.commGroup
  have hτ :
      subgroupGeneratorOfGenerator H σ hgen =
        subgroupGenerator H σ :=
    Subtype.ext (by rfl)
  rw [hτ]
  exact inducedHerbrandHMinusOneEquiv H σ hgen

end FiniteCyclicGroup

end CyclicCohomology
end
end

section
-- module Solutions.OAIQ244_DUKE.Cyclic_Herbrand_HerbrandLowDegree_EquivariantEquiv
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Low-degree Tate cohomology under equivariant equivalences

An equivariant multiplicative equivalence identifies fixed elements, norm
kernels, norm images, and augmentation images.  Consequently it induces
equivalences on the concrete low-degree Tate cohomology groups and preserves
the Herbrand quotient.

These transport results let calculations made on field units or local
coordinates be applied to their actual images inside idele groups without
introducing comparison assumptions.
-/

noncomputable section

namespace CyclicCohomology

open CyclicCohomology.ProfiniteCohomology.Herbrand

universe uG uA uB

variable {G : Type uG} {A : Type uA} {B : Type uB}
    [Group G] [Fintype G]
    [CommGroup A] [CommGroup B]
    [MulDistribMulAction G A]
    [MulDistribMulAction G B]

/-- Herbrand quotients are invariant under equivariant multiplicative
equivalence. -/
theorem herbrandQuotient_eq_of_equivariantMulEquiv
    (e : A ≃* B)
    (he : ∀ (g : G) (a : A),
      e (g • a) = g • e a)
    (σ : G)
    [Finite (HerbrandH0 G A)]
    [Finite (HerbrandHMinusOne G A σ)] :
    letI _h0B : Finite (HerbrandH0 G B) :=
      herbrandH0Finite_of_equivariantMulEquiv e he
    letI _hMinusOneB :
        Finite (HerbrandHMinusOne G B σ) :=
      herbrandHMinusOneFinite_of_equivariantMulEquiv
        e he σ
    herbrandQuotient (G := G) (A := A) σ =
      herbrandQuotient (G := G) (A := B) σ := by
  let h0B : Finite (HerbrandH0 G B) :=
    herbrandH0Finite_of_equivariantMulEquiv e he
  let hMinusOneB :
      Finite (HerbrandHMinusOne G B σ) :=
    herbrandHMinusOneFinite_of_equivariantMulEquiv
      e he σ
  have h0Card :
      Nat.card (HerbrandH0 G A) =
        Nat.card (HerbrandH0 G B) := by
    exact Nat.card_congr
      (herbrandH0EquivariantMulEquiv e he).toEquiv
  have hMinusOneCard :
      Nat.card (HerbrandHMinusOne G A σ) =
        Nat.card
          (HerbrandHMinusOne G B σ) := by
    exact Nat.card_congr
      (herbrandHMinusOneEquivariantMulEquiv
        e he σ).toEquiv
  rw [herbrandQuotient_eq_card_ratio,
    herbrandQuotient_eq_card_ratio,
    h0Card, hMinusOneCard]

end CyclicCohomology
end
end

section
-- module Solutions.OAIQ244_DUKE.Cyclic_Herbrand_HerbrandLowDegree_Product
attribute [-instance] _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.HilbertRamification.Dedekind.inertiaSubgroupOfDecomposition_normal _root_.KummerTheory.DiscreteNthRootsSubgroup.instCommGroupSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.CyclicCohomology.instMulDistribMulActionBinaryCoefficientFamily _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.CyclicCohomology.herbrandH0EquivariantMulEquiv_mk _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalClassFieldTheory.chosenNormalBasisPrincipalUnitSubgroup_sigmaMinusOne_coe _root_.LocalClassFieldTheory.chosenNormalBasisPrincipalUnitSubgroup_tateNorm_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Low-degree Tate cohomology of products

This file proves that multiplicative Tate `H⁰` and `H⁻¹` commute with
dependent products, giving the product step for low-degree Herbrand quotients.
-/

noncomputable section

namespace CyclicCohomology

open CyclicCohomology.ProfiniteCohomology.Herbrand

universe uG uι uA

section TateProducts

variable {G : Type uG} [Group G] [Fintype G]
variable {ι : Type uι} (A : ι → Type uA)
variable [∀ i, CommGroup (A i)]
variable [∀ i, MulDistribMulAction G (A i)]

attribute [local instance] CyclicCohomology.instMulDistribMulActionForall_solutions
/-- Norm kernels of a product are products of norm kernels. -/
def normKernelPiEquiv :
    normKernelSubgroup G (∀ i, A i) ≃*
      ∀ i, normKernelSubgroup G (A i) where
  toFun x i := ⟨x.1 i, by
    change tateNorm G (A i) (x.1 i) = 1
    have hi := congrFun x.2 i
    simpa only [tateNormHom_apply, tateNorm, Finset.prod_apply,
      Pi.smul_apply, Pi.one_apply] using hi⟩
  invFun x := ⟨fun i ↦ (x i).1, by
    funext i
    change
      (tateNorm G (∀ i, A i)
        (fun i ↦ (x i).1)) i = 1
    have hi := (x i).2
    change tateNormHom (G := G) (A := A i) (x i).1 = 1 at hi
    rw [tateNormHom_apply] at hi
    simpa only [tateNorm, Finset.prod_apply,
      Pi.smul_apply] using hi⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[simp]
theorem normKernelPiEquiv_apply_coe
    (x : normKernelSubgroup G (∀ i, A i))
    (i : ι) :
    ((normKernelPiEquiv (G := G) A x i : A i)) =
      x.1 i :=
  rfl

/-- Tate `H⁰` commutes with dependent products. -/
noncomputable def herbrandH0PiEquiv :
    HerbrandH0 G (∀ i, A i) ≃*
      ∀ i, HerbrandH0 G (A i) := by
  let e :
      fixedSubgroup G (∀ i, A i) ≃*
        ∀ i, fixedSubgroup G (A i) :=
    fixedPiEquiv (G := G) A
  let N :=
    (tateNormSubgroup G (∀ i, A i)).subgroupOf
      (fixedSubgroup G (∀ i, A i))
  let M :=
    piSubgroup ι
      (fun i ↦ fixedSubgroup G (A i))
      (fun i ↦
        (tateNormSubgroup G (A i)).subgroupOf
          (fixedSubgroup G (A i)))
  let q :
      fixedSubgroup G (∀ i, A i) ⧸ N ≃*
        (∀ i, fixedSubgroup G (A i)) ⧸ M :=
    quotientMulEquivOfSplit
      N M e.toMonoidHom e.symm.toMonoidHom
      (fun y ↦ e.apply_symm_apply y)
      (fun x hx ↦ by
        rw [Subgroup.mem_subgroupOf] at hx
        change ∀ i, _ at ⊢
        rcases hx with ⟨a, ha⟩
        intro i
        rw [Subgroup.mem_subgroupOf]
        refine ⟨a i, ?_⟩
        have hi := congrFun ha i
        simpa [tateNormHom_apply, tateNorm, e, fixedPiEquiv] using hi)
      (fun y hy ↦ by
        change ∀ i, _ at hy
        have hy' :
            ∀ i, ∃ a : A i,
              tateNorm G (A i) a = (y i).1 := by
          intro i
          have hyi :
              (y i : A i) ∈ tateNormSubgroup G (A i) := by
            simpa only [Subgroup.mem_subgroupOf] using hy i
          rcases hyi with ⟨a, ha⟩
          exact ⟨a, by simpa only [tateNormHom_apply] using ha⟩
        choose a ha using hy'
        rw [Subgroup.mem_subgroupOf]
        refine ⟨fun i ↦ a i, ?_⟩
        funext i
        have hi := ha i
        simpa [tateNormHom_apply, e, fixedPiEquiv, tateNorm] using hi)
      (fun x hx ↦ by
        have hx1 : x = 1 := by
          apply e.injective
          simpa [e] using hx
        rw [hx1]
        exact N.one_mem)
  exact q.trans
    (piQuotientEquiv ι
      (fun i ↦ fixedSubgroup G (A i))
      (fun i ↦
        (tateNormSubgroup G (A i)).subgroupOf
          (fixedSubgroup G (A i))))

/-- Tate `H⁻¹` commutes with dependent products. -/
noncomputable def herbrandHMinusOnePiEquiv (σ : G) :
    HerbrandHMinusOne G (∀ i, A i) σ ≃*
      ∀ i, HerbrandHMinusOne G (A i) σ := by
  let e :
      normKernelSubgroup G (∀ i, A i) ≃*
        ∀ i, normKernelSubgroup G (A i) :=
    normKernelPiEquiv (G := G) A
  let N :=
    (augmentationSubgroup G (∀ i, A i) σ).subgroupOf
      (normKernelSubgroup G (∀ i, A i))
  let M :=
    piSubgroup ι
      (fun i ↦ normKernelSubgroup G (A i))
      (fun i ↦
        (augmentationSubgroup G (A i) σ).subgroupOf
          (normKernelSubgroup G (A i)))
  let q :
      normKernelSubgroup G (∀ i, A i) ⧸ N ≃*
        (∀ i, normKernelSubgroup G (A i)) ⧸ M :=
    quotientMulEquivOfSplit
      N M e.toMonoidHom e.symm.toMonoidHom
      (fun y ↦ e.apply_symm_apply y)
      (fun x hx ↦ by
        rw [Subgroup.mem_subgroupOf] at hx
        change ∀ i, _ at ⊢
        rcases hx with ⟨a, ha⟩
        intro i
        rw [Subgroup.mem_subgroupOf]
        refine ⟨a i, ?_⟩
        have hi := congrFun ha i
        simpa [sigmaMinusOneHom_apply, sigmaMinusOne, e,
          normKernelPiEquiv] using hi)
      (fun y hy ↦ by
        change ∀ i, _ at hy
        have hy' :
            ∀ i, ∃ a : A i,
              sigmaMinusOne G (A i) σ a =
                (y i).1 := by
          intro i
          have hyi :
              (y i : A i) ∈ augmentationSubgroup G (A i) σ := by
            simpa only [Subgroup.mem_subgroupOf] using hy i
          rcases hyi with ⟨a, ha⟩
          exact ⟨a, by simpa only [sigmaMinusOneHom_apply] using ha⟩
        choose a ha using hy'
        rw [Subgroup.mem_subgroupOf]
        refine ⟨fun i ↦ a i, ?_⟩
        funext i
        have hi := ha i
        simpa [sigmaMinusOneHom_apply, e, normKernelPiEquiv,
          sigmaMinusOne] using hi)
      (fun x hx ↦ by
        have hx1 : x = 1 := by
          apply e.injective
          simpa [e] using hx
        rw [hx1]
        exact N.one_mem)
  exact q.trans
    (piQuotientEquiv ι
      (fun i ↦ normKernelSubgroup G (A i))
      (fun i ↦
        (augmentationSubgroup G (A i) σ).subgroupOf
          (normKernelSubgroup G (A i))))

end TateProducts

end CyclicCohomology
end
end

section
-- module Solutions.OAIQ244_DUKE.Cyclic_Herbrand_HerbrandLowDegree_BinaryProduct
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
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

noncomputable def piHerbrandH0EquivProd :
    (∀ i, HerbrandH0 G
      (BinaryCoefficientFamily A B i)) ≃*
        HerbrandH0 G A × HerbrandH0 G B where
  toFun x := ⟨x false, x true⟩
  invFun x
    | false => x.1
    | true => x.2
  left_inv x := by
    funext i
    cases i <;> rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- Degree-zero Tate cohomology commutes with a binary product. -/
noncomputable def herbrandH0ProdEquiv :
    HerbrandH0 G (A × B) ≃*
      HerbrandH0 G A × HerbrandH0 G B := by
  letI familyAction : ∀ i, MulDistribMulAction G
      (BinaryCoefficientFamily A B i) :=
    binaryCoefficientFamilyAction A B
  letI piAction : MulDistribMulAction G
      (∀ i, BinaryCoefficientFamily A B i) :=
    piMulDistribMulAction G
      (BinaryCoefficientFamily A B)
  exact
    (herbrandH0EquivariantMulEquiv
      (prodEquivBinaryCoefficientFamily A B)
      (prodEquivBinaryCoefficientFamily_smul A B)).trans
      ((herbrandH0PiEquiv
        (G := G) (BinaryCoefficientFamily A B)).trans
        (piHerbrandH0EquivProd A B))

/-- Finiteness of degree zero is preserved by a binary product. -/
theorem herbrandH0ProdFinite
    [Finite (HerbrandH0 G A)]
    [Finite (HerbrandH0 G B)] :
    Finite (HerbrandH0 G (A × B)) :=
  Finite.of_equiv
    (HerbrandH0 G A × HerbrandH0 G B)
    (herbrandH0ProdEquiv A B).symm.toEquiv

/-- Cardinality of degree-zero Tate cohomology for a binary product. -/
theorem herbrandH0Prod_card
    [Finite (HerbrandH0 G A)]
    [Finite (HerbrandH0 G B)] :
    letI : Finite (HerbrandH0 G (A × B)) :=
      herbrandH0ProdFinite A B
    Nat.card (HerbrandH0 G (A × B)) =
      Nat.card (HerbrandH0 G A) *
        Nat.card (HerbrandH0 G B) := by
  rw [Nat.card_congr (herbrandH0ProdEquiv A B).toEquiv,
    Nat.card_prod]

end CyclicCohomology
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_IdealQuotients
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

/-! ### Residue and maximal-ideal successive quotients -/

/-- The version of `𝒪[K]/𝓂[K] ≃ 𝓂^n/𝓂^(n+1)` determined by the library's
chosen integer-ring uniformizer. -/
def chosenResidueLinearEquivMaximalIdealPowSuccQuot
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : Nat) :
    𝓀[K] ≃ₗ[𝒪[K]] MaximalIdealPowSuccQuot K n :=
  residueLinearEquivMaximalIdealPowSuccQuotOfIrreducible K
    (chosenIntegerRingUniformizer K) (chosenIntegerRingUniformizer_irreducible K) n

/-- Additive equivalence determined by the library's chosen integer-ring
uniformizer. -/
def chosenResidueAddEquivMaximalIdealPowSuccQuot
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : Nat) :
    𝓀[K] ≃+ MaximalIdealPowSuccQuot K n :=
  (chosenResidueLinearEquivMaximalIdealPowSuccQuot K n).toAddEquiv

end
end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.Cyclic_Herbrand_NormalBasisLattice
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.CyclicCohomology.integerUnitsModPrincipalUnitsAtLevelConcreteEquiv_mk _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalClassFieldTheory.chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction_smul _root_.LocalClassFieldTheory.chosenNormalBasisPrincipalUnitSubgroup_sigmaMinusOne_coe _root_.LocalClassFieldTheory.chosenNormalBasisPrincipalUnitSubgroup_tateNorm_coe _root_.LocalFieldTheory.maximalIdealPowMapOfUnramifiedValuation_apply _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.principalUnitsMapOfUnramifiedValuation_apply _root_.LocalFieldTheory.principalUnitsSuccQuotMapOfUnramifiedValuation_mk _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-! Provides the public normal-basis lattice declarations used in Herbrand computations. -/

namespace CyclicCohomology

open LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel
open Filter

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

variable [ValuativeRel K]

variable [TopologicalSpace K] [IsNonarchimedeanLocalField K]

omit [FiniteDimensional K L] [IsGalois K L] in
/-- If an `𝒪_K`-submodule spans `L` after extending scalars to `K`, then every
element of `L` enters that submodule after multiplying by a high enough power
of the base prime element.  The scalar-denominator step is exactly the local
DVR denominator clearing in `IdealQuotients`. -/
theorem exists_chosenBaseUniformizerPow_mul_mem_of_field_span_eq_top
    {M : Submodule 𝒪[K] L}
    (hMspan : Submodule.span K ((M : Set L)) = ⊤) (x : L) :
    ∃ n : Nat, algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * x ∈ M := by
  have hx : x ∈ Submodule.span K ((M : Set L)) := by
    rw [hMspan]
    exact Submodule.mem_top
  refine Submodule.span_induction
    (p := fun y _ =>
      ∃ n : Nat, algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * y ∈ M)
    ?hgen ?hzero ?hadd ?hsmul hx
  · intro y hyM
    refine ⟨0, ?_⟩
    simpa using hyM
  · refine ⟨0, ?_⟩
    simp
  · intro y z _ _ hy hz
    rcases hy with ⟨m, hm⟩
    rcases hz with ⟨n, hn⟩
    refine ⟨max m n, ?_⟩
    have hy' := chosenBaseUniformizerPow_mul_mem_mono
      (K := K) (L := L) (M := M) (Nat.le_max_left m n) hm
    have hz' := chosenBaseUniformizerPow_mul_mem_mono
      (K := K) (L := L) (M := M) (Nat.le_max_right m n) hn
    simpa [mul_add] using M.add_mem hy' hz'
  · intro c y _ hy
    rcases hy with ⟨m, hm⟩
    obtain ⟨d, hd⟩ := exists_chosenIntegerRingUniformizer_pow_mul_mem_integerRing K c
    let cInt : 𝒪[K] :=
      ⟨(((chosenIntegerRingUniformizer K : 𝒪[K]) : K) ^ d) * c, hd⟩
    refine ⟨d + m, ?_⟩
    have hscaled :
        algebraMap 𝒪[K] L cInt *
            (algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ m) * y) ∈ M := by
      simpa [Algebra.smul_def, mul_assoc] using M.smul_mem cInt hm
    have hcInt :
        algebraMap 𝒪[K] L cInt =
          algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ d) *
            algebraMap K L c := by
      change algebraMap K L
          ((((chosenIntegerRingUniformizer K : 𝒪[K]) : K) ^ d) * c) = _
      simp only [map_mul, map_pow]
      rfl
    rw [hcInt] at hscaled
    convert hscaled using 1
    all_goals try with_reducible_and_instances rfl
    rw [Algebra.smul_def, pow_add, map_mul]
    ring

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Finite-generation version of
`exists_chosenBaseUniformizerPow_mul_mem_of_field_span_eq_top`: one exponent works
for all elements of a finitely generated `𝒪_K`-submodule. -/
theorem exists_chosenBaseUniformizerPowSubmodule_le_of_fg_of_field_span_eq_top
    {M N : Submodule 𝒪[K] L} (hN : N.FG)
    (hMspan : Submodule.span K ((M : Set L)) = ⊤) :
    ∃ n : Nat, chosenBaseUniformizerPowSubmodule K L n N ≤ M := by
  rcases Submodule.fg_def.mp hN with ⟨S, hSfinite, hSspan⟩
  let t : Finset L := hSfinite.toFinset
  let nOf : L → Nat := fun y =>
    Classical.choose
      (exists_chosenBaseUniformizerPow_mul_mem_of_field_span_eq_top
        (K := K) (L := L) hMspan y)
  let n : Nat := t.sup nOf
  have hnOf_spec (y : L) :
      algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ nOf y) * y ∈ M :=
    Classical.choose_spec
      (exists_chosenBaseUniformizerPow_mul_mem_of_field_span_eq_top
        (K := K) (L := L) hMspan y)
  have hpow_mono {m : Nat} {y : L} (hmn : m ≤ n)
      (hy : algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ m) * y ∈ M) :
      algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * y ∈ M := by
    rcases Nat.exists_eq_add_of_le hmn with ⟨d, hd⟩
    rw [hd]
    have hscaled :
        algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ d) *
            (algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ m) * y) ∈ M := by
      simpa [Algebra.smul_def, mul_assoc] using
        M.smul_mem (chosenIntegerRingUniformizer K ^ d) hy
    simpa [pow_add, map_mul, mul_assoc, mul_comm, mul_left_comm] using hscaled
  have hN_mem (y : L) (hyN : y ∈ N) :
      algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * y ∈ M := by
    rw [← hSspan] at hyN
    refine Submodule.span_induction
      (p := fun y _ =>
        algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * y ∈ M)
      ?hgen ?hzero ?hadd ?hsmul hyN
    · intro y hyS
      have hyt : y ∈ t := by
        exact (Set.Finite.mem_toFinset hSfinite).2 hyS
      exact hpow_mono (Finset.le_sup hyt) (hnOf_spec y)
    · simp
    · intro y z _ _ hy hz
      simpa [mul_add] using M.add_mem hy hz
    · intro a y _ hy
      have hscaled :
          algebraMap 𝒪[K] L a *
              (algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * y) ∈ M := by
        simpa [Algebra.smul_def, mul_assoc] using M.smul_mem a hy
      simpa [Algebra.smul_def, mul_assoc, mul_comm, mul_left_comm] using hscaled
  refine ⟨n, ?_⟩
  intro z hz
  rcases (mem_chosenBaseUniformizerPowSubmodule_iff (K := K) (L := L) n N z).1 hz with
    ⟨y, hyN, rfl⟩
  exact hN_mem y hyN

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Product-denominator bound for multiplicative lattice control.  If `N` and `P` are finitely generated
`𝒪_K`-submodules and `M` spans `L` after inverting `𝒪_K`, then one power of the
base prime element sends every product `xy`, `x ∈ N`, `y ∈ P`, back into `M`.

This is the multiplicative source needed before proving that `1 + π_K^n M` is
closed under multiplication for large `n`. -/
theorem exists_chosenBaseUniformizerPow_mul_mul_mem_of_fg_of_field_span_eq_top
    {M N P : Submodule 𝒪[K] L} (hN : N.FG) (hP : P.FG)
    (hMspan : Submodule.span K ((M : Set L)) = ⊤) :
    ∃ n : Nat, ∀ x : L, x ∈ N → ∀ y : L, y ∈ P →
      algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * (x * y) ∈ M := by
  rcases Submodule.fg_def.mp hN with ⟨S, hSfinite, hSspan⟩
  rcases Submodule.fg_def.mp hP with ⟨T, hTfinite, hTspan⟩
  let s : Finset L := hSfinite.toFinset
  let t : Finset L := hTfinite.toFinset
  let pairExp : L × L → Nat := fun p =>
    Classical.choose
      (exists_chosenBaseUniformizerPow_mul_mem_of_field_span_eq_top
        (K := K) (L := L) hMspan (p.1 * p.2))
  let n : Nat := (s.product t).sup pairExp
  have hpair_spec (x y : L) :
      algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ (pairExp (x, y))) * (x * y) ∈ M :=
    Classical.choose_spec
      (exists_chosenBaseUniformizerPow_mul_mem_of_field_span_eq_top
        (K := K) (L := L) hMspan (x * y))
  have hpow_mono {m : Nat} {z : L} (hmn : m ≤ n)
      (hz : algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ m) * z ∈ M) :
      algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * z ∈ M := by
    rcases Nat.exists_eq_add_of_le hmn with ⟨d, hd⟩
    rw [hd]
    have hscaled :
        algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ d) *
            (algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ m) * z) ∈ M := by
      simpa [Algebra.smul_def, mul_assoc] using
        M.smul_mem (chosenIntegerRingUniformizer K ^ d) hz
    simpa [pow_add, map_mul, mul_assoc, mul_comm, mul_left_comm] using hscaled
  have hgen (x y : L) (hxS : x ∈ S) (hyT : y ∈ T) :
      algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * (x * y) ∈ M := by
    have hxs : x ∈ s := (Set.Finite.mem_toFinset hSfinite).2 hxS
    have hyt : y ∈ t := (Set.Finite.mem_toFinset hTfinite).2 hyT
    exact hpow_mono (Finset.le_sup (Finset.mem_product.2 ⟨hxs, hyt⟩))
      (hpair_spec x y)
  have hleft (x : L) (hxS : x ∈ S) :
      ∀ y : L, y ∈ P →
        algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * (x * y) ∈ M := by
    intro y hyP
    rw [← hTspan] at hyP
    refine Submodule.span_induction
      (p := fun y _ =>
        algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * (x * y) ∈ M)
      ?hgen ?hzero ?hadd ?hsmul hyP
    · intro y hyT
      exact hgen x y hxS hyT
    · simp
    · intro y z _ _ hy hz
      simpa [mul_add] using M.add_mem hy hz
    · intro a y _ hy
      have hscaled :
          algebraMap 𝒪[K] L a *
              (algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * (x * y)) ∈ M := by
        simpa [Algebra.smul_def, mul_assoc] using M.smul_mem a hy
      simpa [Algebra.smul_def, mul_assoc, mul_comm, mul_left_comm] using hscaled
  refine ⟨n, ?_⟩
  intro x hxN y hyP
  rw [← hSspan] at hxN
  refine Submodule.span_induction
    (p := fun x _ =>
      algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * (x * y) ∈ M)
    ?gen ?zero ?add ?smul hxN
  · intro x hxS
    exact hleft x hxS y hyP
  · simp
  · intro x z _ _ hx hz
    convert M.add_mem hx hz using 1 <;> first | rfl | ring
  · intro a x _ hx
    have hscaled :
        algebraMap 𝒪[K] L a *
            (algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * (x * y)) ∈ M := by
      simpa [Algebra.smul_def, mul_assoc] using M.smul_mem a hx
    simpa [Algebra.smul_def, mul_assoc, mul_comm, mul_left_comm] using hscaled

omit [FiniteDimensional K L] [IsGalois K L] in
/-- For sufficiently large `n`, the lattice `π_K^n M` is closed under
multiplication.  It supplies the multiplicative
closure of `1 + π_K^n M` in the principal-unit lattice. -/
theorem exists_chosenBaseUniformizerPowSubmodule_mul_mul_mem_self_of_fg_of_field_span_eq_top
    {M : Submodule 𝒪[K] L} (hMfg : M.FG)
    (hMspan : Submodule.span K ((M : Set L)) = ⊤) :
    ∃ c : Nat, ∀ n : Nat, c ≤ n → ∀ x : L,
      x ∈ chosenBaseUniformizerPowSubmodule K L n M →
      ∀ y : L, y ∈ chosenBaseUniformizerPowSubmodule K L n M →
        x * y ∈ chosenBaseUniformizerPowSubmodule K L n M := by
  rcases exists_chosenBaseUniformizerPow_mul_mul_mem_of_fg_of_field_span_eq_top
      (K := K) (L := L) (M := M) (N := M) (P := M) hMfg hMfg hMspan with
    ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro n hcn x hx y hy
  rcases (mem_chosenBaseUniformizerPowSubmodule_iff (K := K) (L := L) n M x).1 hx with
    ⟨x0, hx0M, rfl⟩
  rcases (mem_chosenBaseUniformizerPowSubmodule_iff (K := K) (L := L) n M y).1 hy with
    ⟨y0, hy0M, rfl⟩
  have hprod :
      algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * (x0 * y0) ∈ M :=
    chosenBaseUniformizerPow_mul_mem_mono (K := K) (L := L) hcn
      (hc x0 hx0M y0 hy0M)
  refine (mem_chosenBaseUniformizerPowSubmodule_iff (K := K) (L := L) n M _).2 ?_
  refine ⟨algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * (x0 * y0),
    hprod, ?_⟩
  simp [mul_assoc, mul_comm, mul_left_comm]

omit [FiniteDimensional K L] [IsGalois K L] in
/-- For sufficiently large `n`, products of two elements of `π_K^n M` land in
the next lattice step `π_K^(n+1) M`.

This is the product-depth estimate needed before the map
`V^n/V^(n+1) -> π_K^nM/π_K^(n+1)M` can be made well-defined. -/
theorem exists_chosenBaseUniformizerPowSubmodule_mul_mul_mem_succ_of_fg_of_field_span_eq_top
    {M : Submodule 𝒪[K] L} (hMfg : M.FG)
    (hMspan : Submodule.span K ((M : Set L)) = ⊤) :
    ∃ c : Nat, ∀ n : Nat, c ≤ n → ∀ x : L,
      x ∈ chosenBaseUniformizerPowSubmodule K L n M →
      ∀ y : L, y ∈ chosenBaseUniformizerPowSubmodule K L n M →
        x * y ∈ chosenBaseUniformizerPowSubmodule K L (n + 1) M := by
  rcases exists_chosenBaseUniformizerPow_mul_mul_mem_of_fg_of_field_span_eq_top
      (K := K) (L := L) (M := M) (N := M) (P := M) hMfg hMfg hMspan with
    ⟨c, hc⟩
  refine ⟨c + 1, ?_⟩
  intro n hcn x hx y hy
  rcases Nat.exists_eq_add_of_le hcn with ⟨d, hd⟩
  rcases (mem_chosenBaseUniformizerPowSubmodule_iff (K := K) (L := L) n M x).1 hx with
    ⟨x0, hx0M, rfl⟩
  rcases (mem_chosenBaseUniformizerPowSubmodule_iff (K := K) (L := L) n M y).1 hy with
    ⟨y0, hy0M, rfl⟩
  have hprod :
      algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ (c + d)) * (x0 * y0) ∈ M :=
    chosenBaseUniformizerPow_mul_mem_mono (K := K) (L := L)
      (Nat.le_add_right c d) (hc x0 hx0M y0 hy0M)
  refine (mem_chosenBaseUniformizerPowSubmodule_iff (K := K) (L := L) (n + 1) M _).2 ?_
  refine ⟨algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ (c + d)) * (x0 * y0),
    hprod, ?_⟩
  rw [hd]
  simp only [map_mul, pow_add, pow_one]
  ring

/-- A sufficiently deep uniformizer-power normal-basis lattice is closed under
the indicated self-products. -/
theorem exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_mul_mul_mem_self :
    ∃ c : Nat, ∀ n : Nat, c ≤ n → ∀ x : L,
      x ∈ chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) →
      ∀ y : L,
        y ∈ chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) →
          x * y ∈
            chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) :=
  exists_chosenBaseUniformizerPowSubmodule_mul_mul_mem_self_of_fg_of_field_span_eq_top
    (K := K) (L := L)
    (M := chosenNormalBasisIntegerLattice K L)
    (chosenNormalBasisIntegerLattice_fg (K := K) (L := L))
    (chosenNormalBasisIntegerLattice_field_span_eq_top (K := K) (L := L))

/-- A sufficiently deep lattice sends the indicated products into the next uniformizer level. -/
theorem exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_mul_mul_mem_succ :
    ∃ c : Nat, ∀ n : Nat, c ≤ n → ∀ x : L,
      x ∈ chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) →
      ∀ y : L,
        y ∈ chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) →
          x * y ∈
            chosenBaseUniformizerPowSubmodule K L (n + 1) (chosenNormalBasisIntegerLattice K L) :=
  exists_chosenBaseUniformizerPowSubmodule_mul_mul_mem_succ_of_fg_of_field_span_eq_top
    (K := K) (L := L)
    (M := chosenNormalBasisIntegerLattice K L)
    (chosenNormalBasisIntegerLattice_fg (K := K) (L := L))
    (chosenNormalBasisIntegerLattice_field_span_eq_top (K := K) (L := L))

variable [ValuativeRel L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Extension-field denominator clearing by powers of the base prime element.

For any `x : L`, a sufficiently high power of the chosen prime element of
`𝒪[K]`, mapped to `L`, sends `x` into `𝒪[L]`.  This is the denominator-clearing input used before comparing the normal-basis lattice with `𝒪_L`: it uses only the
DVR structure of `𝒪_L` and the fact that the image of the base prime lies in
`𝓂_L`. -/
theorem exists_chosenBaseUniformizerPow_mul_mem_integerRing_of_valuationExtension
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] (x : L) :
    ∃ n : Nat,
      algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * x ∈ 𝒪[L] := by
  obtain ⟨a, b, hb, hfrac⟩ := IsFractionRing.div_surjective (A := 𝒪[L]) x
  have hb_ne : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨m, ub, hb_factor⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb_ne
      (chosenIntegerRingUniformizer_irreducible L)
  refine ⟨m, ?_⟩
  let πK_L : 𝒪[L] :=
    integerRingMapOfValuationExtension K L (chosenIntegerRingUniformizer K)
  have hπK_L_mem : πK_L ∈ (𝓂[L] : Ideal 𝒪[L]) := by
    dsimp [πK_L]
    exact integerRingMap_uniformizer_mem_maximalIdeal_of_valuationExtension
      (K := K) (L := L)
  have hπK_L_pow_mem : πK_L ^ m ∈ (𝓂[L] ^ m : Ideal 𝒪[L]) :=
    Ideal.pow_mem_pow hπK_L_mem m
  have hπK_L_span :
      πK_L ^ m ∈
        Ideal.span ({chosenIntegerRingUniformizer L ^ m} : Set 𝒪[L]) := by
    simpa [maximalIdeal_pow_eq_span_uniformizer_pow L m] using hπK_L_pow_mem
  rcases Ideal.mem_span_singleton'.mp hπK_L_span with ⟨c, hc⟩
  rw [← hfrac, hb_factor]
  have hϖL_ne : (((chosenIntegerRingUniformizer L : 𝒪[L]) : L)) ≠ 0 := by
    intro h
    exact (chosenIntegerRingUniformizer_irreducible L).ne_zero
      ((IsFractionRing.injective 𝒪[L] L) h)
  have hϖL_pow_ne :
      (((chosenIntegerRingUniformizer L : 𝒪[L]) : L) ^ m) ≠ 0 :=
    pow_ne_zero m hϖL_ne
  have hub_ne : (((ub : 𝒪[L]) : L)) ≠ 0 := by
    intro h
    exact ub.ne_zero ((IsFractionRing.injective 𝒪[L] L) h)
  have hub_inv :
      (((↑ub⁻¹ : 𝒪[L]) : L)) = (((ub : 𝒪[L]) : L))⁻¹ := by
    exact map_units_inv (algebraMap 𝒪[L] L) ub
  have hbase :
      algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ m) =
        ((πK_L ^ m : 𝒪[L]) : L) := by
    dsimp [πK_L, integerRingMapOfValuationExtension]
    simp only [map_pow]
    change (algebraMap K L ((chosenIntegerRingUniformizer K : 𝒪[K]) : K)) ^ m =
      (algebraMap K L ((chosenIntegerRingUniformizer K : 𝒪[K]) : K)) ^ m
    rfl
  change algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ m) *
      ((a : L) /
        (((ub : 𝒪[L]) * chosenIntegerRingUniformizer L ^ m : 𝒪[L]) : L)) ∈ 𝒪[L]
  rw [hbase]
  have hclear :
      ((πK_L ^ m : 𝒪[L]) : L) *
          ((a : L) /
            (((ub : 𝒪[L]) * chosenIntegerRingUniformizer L ^ m : 𝒪[L]) : L)) =
        ((c * ↑ub⁻¹ * a : 𝒪[L]) : L) := by
    calc
      ((πK_L ^ m : 𝒪[L]) : L) *
          ((a : L) /
            (((ub : 𝒪[L]) * chosenIntegerRingUniformizer L ^ m : 𝒪[L]) : L))
          =
          ((c * chosenIntegerRingUniformizer L ^ m : 𝒪[L]) : L) *
            ((a : L) /
              (((ub : 𝒪[L]) * chosenIntegerRingUniformizer L ^ m : 𝒪[L]) : L)) := by
            rw [← hc]
      _ = ((c : L) * (((ub : 𝒪[L]) : L))⁻¹ * (a : L)) := by
            change
              ((c : L) * (((chosenIntegerRingUniformizer L : 𝒪[L]) : L) ^ m)) *
                  ((a : L) /
                    (((ub : 𝒪[L]) : L) *
                      (((chosenIntegerRingUniformizer L : 𝒪[L]) : L) ^ m))) =
                (c : L) * (((ub : 𝒪[L]) : L))⁻¹ * (a : L)
            field_simp [hub_ne, hϖL_pow_ne]
      _ = ((c * ↑ub⁻¹ * a : 𝒪[L]) : L) := by
            rw [← hub_inv]
            simp [mul_assoc]
  rw [hclear]
  exact (c * ↑ub⁻¹ * a : 𝒪[L]).2

omit [FiniteDimensional K L] [IsGalois K L] in
/-- A finitely generated `𝒪_K`-submodule of `L` is sent into `𝒪_L` after
multiplication by a single sufficiently high power of the base prime element.

This proves the `π_K^b N ≤ 𝒪_L` first direction of the lattice-bound statement for
any finitely generated `N`; applying it to the normal-basis lattice gives the
needed denominator bound for `M`. -/
theorem exists_chosenBaseUniformizerPowSubmodule_le_integerRingFieldSubmodule_of_fg
    [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    {N : Submodule 𝒪[K] L} (hN : N.FG) :
    ∃ n : Nat,
      chosenBaseUniformizerPowSubmodule K L n N ≤ integerRingFieldSubmodule K L := by
  rcases Submodule.fg_def.mp hN with ⟨S, hSfinite, hSspan⟩
  let t : Finset L := hSfinite.toFinset
  let nOf : L → Nat := fun y =>
    Classical.choose
      (exists_chosenBaseUniformizerPow_mul_mem_integerRing_of_valuationExtension
        (K := K) (L := L) y)
  let n : Nat := t.sup nOf
  have hnOf_spec (y : L) :
      algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ nOf y) * y ∈ 𝒪[L] :=
    Classical.choose_spec
      (exists_chosenBaseUniformizerPow_mul_mem_integerRing_of_valuationExtension
        (K := K) (L := L) y)
  have hpow_mono {m : Nat} {y : L} (hmn : m ≤ n)
      (hy : algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ m) * y ∈ 𝒪[L]) :
      algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * y ∈ 𝒪[L] := by
    rcases Nat.exists_eq_add_of_le hmn with ⟨d, hd⟩
    have hd_mem :
        algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ d) ∈ 𝒪[L] := by
      change algebraMap K L ((chosenIntegerRingUniformizer K ^ d : 𝒪[K]) : K) ∈ 𝒪[L]
      exact (integerRingMapOfValuationExtension K L
        (chosenIntegerRingUniformizer K ^ d)).2
    rw [hd]
    rw [pow_add, map_mul]
    simpa [mul_assoc, mul_comm, mul_left_comm] using mul_mem hd_mem hy
  have hN_mem (y : L) (hyN : y ∈ N) :
      algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * y ∈ 𝒪[L] := by
    rw [← hSspan] at hyN
    refine Submodule.span_induction
      (p := fun y _ =>
        algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * y ∈ 𝒪[L])
      ?hgen ?hzero ?hadd ?hsmul hyN
    · intro y hyS
      have hyt : y ∈ t := by
        exact (Set.Finite.mem_toFinset hSfinite).2 hyS
      exact hpow_mono (Finset.le_sup hyt) (hnOf_spec y)
    · simp
    · intro y z _ _ hy hz
      simpa [mul_add] using add_mem hy hz
    · intro a y _ hy
      have ha_mem : algebraMap 𝒪[K] L a ∈ 𝒪[L] := by
        change algebraMap K L (a : K) ∈ 𝒪[L]
        exact (integerRingMapOfValuationExtension K L a).2
      simpa [Algebra.smul_def, mul_assoc, mul_comm, mul_left_comm] using
        mul_mem ha_mem hy
  refine ⟨n, ?_⟩
  intro z hz
  rcases (mem_chosenBaseUniformizerPowSubmodule_iff (K := K) (L := L) n N z).1 hz with
    ⟨y, hyN, rfl⟩
  exact hN_mem y hyN

/-- Some uniformizer-power normal-basis lattice lies inside the integer-ring field submodule. -/
theorem exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_le_integerRingFieldSubmodule
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] :
    ∃ n : Nat,
      chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) ≤
        integerRingFieldSubmodule K L :=
  exists_chosenBaseUniformizerPowSubmodule_le_integerRingFieldSubmodule_of_fg
    (K := K) (L := L) (chosenNormalBasisIntegerLattice_fg (K := K) (L := L))

omit [FiniteDimensional K L] [IsGalois K L] in
/-- A finitely generated submodule has a sufficiently deep uniformizer multiple
inside the maximal ideal. -/
theorem exists_chosenBaseUniformizerPowSubmodule_le_maximalIdealFieldSubmodule_of_fg
    [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    {N : Submodule 𝒪[K] L} (hN : N.FG) :
    ∃ n : Nat,
      chosenBaseUniformizerPowSubmodule K L n N ≤ maximalIdealFieldSubmodule K L := by
  rcases exists_chosenBaseUniformizerPowSubmodule_le_integerRingFieldSubmodule_of_fg
      (K := K) (L := L) hN with
    ⟨b, hb⟩
  exact ⟨b + 1,
    chosenBaseUniformizerPowSubmodule_succ_le_maximalIdealFieldSubmodule_of_le_integerRingFieldSubmodule
      (K := K) (L := L) hb⟩

/-- Some uniformizer-power normal-basis lattice lies inside the maximal-ideal field submodule. -/
theorem exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_le_maximalIdealFieldSubmodule
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] :
    ∃ n : Nat,
      chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) ≤
        maximalIdealFieldSubmodule K L :=
  exists_chosenBaseUniformizerPowSubmodule_le_maximalIdealFieldSubmodule_of_fg
    (K := K) (L := L) (chosenNormalBasisIntegerLattice_fg (K := K) (L := L))

/-- A sufficiently deep normal-basis lattice lies in the maximal ideal and is
multiplicatively closed. -/
theorem exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_le_maximalIdeal_and_mul_closed
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] :
    ∃ c : Nat, ∀ n : Nat, c ≤ n →
      chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) ≤
        maximalIdealFieldSubmodule K L ∧
      ∀ x : L,
        x ∈ chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) →
        ∀ y : L,
          y ∈ chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) →
            x * y ∈
              chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) := by
  rcases exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_le_maximalIdealFieldSubmodule
      (K := K) (L := L) with
    ⟨d, hd⟩
  rcases exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_mul_mul_mem_self
      (K := K) (L := L) with
    ⟨c, hc⟩
  refine ⟨max c d, ?_⟩
  intro n hmaxn
  have hcn : c ≤ n := le_trans (le_max_left c d) hmaxn
  have hdn : d ≤ n := le_trans (le_max_right c d) hmaxn
  constructor
  · exact (chosenBaseUniformizerPowSubmodule_antitone
      (K := K) (L := L) (chosenNormalBasisIntegerLattice K L) hdn).trans hd
  · exact hc n hcn

/-- Every chosen normal-basis principal unit belongs to the first principal-unit group. -/
theorem chosenNormalBasisPrincipalUnitSet_mem_principalUnits_one {n : Nat}
    (hle : chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) ≤
      maximalIdealFieldSubmodule K L)
    {u : 𝒪[L]ˣ} (hu : u ∈ chosenNormalBasisPrincipalUnitSet K L n) :
    u ∈ principalUnits L 1 := by
  rw [mem_principalUnits_iff]
  have hmax :
      ((((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) ∈
        maximalIdealFieldSubmodule K L :=
    hle hu
  rcases (mem_maximalIdealFieldSubmodule_iff (K := K) (L := L)
      ((((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L)).1 hmax with
    ⟨a, ha, haeq⟩
  have ha_eq : a = ((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 :=
    Subtype.ext haeq
  simpa [ha_eq] using ha

/-- There is a multiplicatively closed normal-basis principal-unit set inside
the first principal-unit group. -/
theorem exists_chosenNormalBasisPrincipalUnitSet_mul_closed_le_principalUnits_one
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] :
    ∃ c : Nat, ∀ n : Nat, c ≤ n →
      (∀ u : 𝒪[L]ˣ, u ∈ chosenNormalBasisPrincipalUnitSet K L n →
        ∀ v : 𝒪[L]ˣ, v ∈ chosenNormalBasisPrincipalUnitSet K L n →
          u * v ∈ chosenNormalBasisPrincipalUnitSet K L n) ∧
      ∀ u : 𝒪[L]ˣ, u ∈ chosenNormalBasisPrincipalUnitSet K L n →
        u ∈ principalUnits L 1 := by
  rcases exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_le_maximalIdeal_and_mul_closed
      (K := K) (L := L) with
    ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro n hcn
  rcases hc n hcn with ⟨hle, hmul⟩
  constructor
  · intro u hu v hv
    exact chosenNormalBasisPrincipalUnitSet_mul_mem (K := K) (L := L) hmul hu hv
  · intro u hu
    exact chosenNormalBasisPrincipalUnitSet_mem_principalUnits_one
      (K := K) (L := L) hle hu

/-- Successive powers of the negative deviation from one converge to zero. -/
theorem chosenNormalBasisPrincipalUnitSet_neg_sub_one_pow_succ_tendsto_zero
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] {n : Nat}
    (hle : chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) ≤
      maximalIdealFieldSubmodule K L)
    {u : 𝒪[L]ˣ} (hu : u ∈ chosenNormalBasisPrincipalUnitSet K L n) :
    Tendsto
      (fun d : Nat => (-(((u : 𝒪[L]ˣ) : 𝒪[L]) - 1)) ^ (d + 1))
      atTop (nhds (0 : 𝒪[L])) := by
  have hu_one : u ∈ principalUnits L 1 :=
    chosenNormalBasisPrincipalUnitSet_mem_principalUnits_one
      (K := K) (L := L) hle hu
  have hpow :
      (((u : 𝒪[L]ˣ) : 𝒪[L]) - 1) ∈ (𝓂[L] ^ 1 : Ideal 𝒪[L]) :=
    (mem_principalUnits_iff L u 1).1 hu_one
  have hmax :
      (((u : 𝒪[L]ˣ) : 𝒪[L]) - 1) ∈ (𝓂[L] : Ideal 𝒪[L]) := by
    simpa [pow_one] using hpow
  exact tendsto_neg_pow_succ_of_mem_maximalIdeal L hmax

/-- The inverse-correction partial products converge to one. -/
theorem chosenNormalBasisPrincipalUnitSet_inverseCorrectionProduct_tendsto_one
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] {n : Nat}
    (hle : chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) ≤
      maximalIdealFieldSubmodule K L)
    {u : 𝒪[L]ˣ} (hu : u ∈ chosenNormalBasisPrincipalUnitSet K L n) :
    Tendsto
      (fun d : Nat =>
        (((u : 𝒪[L]ˣ) : 𝒪[L]) : L) *
          (1 + inverseCorrectionPartialSum (L := L)
            ((((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) d))
      atTop (nhds (1 : L)) := by
  let x𝒪 : 𝒪[L] := ((u : 𝒪[L]ˣ) : 𝒪[L]) - 1
  let x : L := (x𝒪 : L)
  have hres𝒪 :
      Tendsto (fun d : Nat => (-x𝒪) ^ (d + 1)) atTop (nhds (0 : 𝒪[L])) := by
    simpa [x𝒪] using
      chosenNormalBasisPrincipalUnitSet_neg_sub_one_pow_succ_tendsto_zero
        (K := K) (L := L) hle hu
  have hresL :
      Tendsto (fun d : Nat => ((((-x𝒪) ^ (d + 1) : 𝒪[L]) : L)))
        atTop (nhds (0 : L)) :=
    (continuous_subtype_val.tendsto (0 : 𝒪[L])).comp hres𝒪
  have htarget :
      Tendsto (fun d : Nat => (1 : L) - ((((-x𝒪) ^ (d + 1) : 𝒪[L]) : L)))
        atTop (nhds (1 : L)) := by
    simpa using (tendsto_const_nhds (x := (1 : L))).sub hresL
  refine htarget.congr' (Eventually.of_forall ?_)
  intro d
  have hgeom :
      (1 + x) * (1 + inverseCorrectionPartialSum (L := L) x d) =
        1 - (-x) ^ (d + 1) :=
    one_add_mul_one_add_inverseCorrectionPartialSum (L := L) x d
  have hu_eq : 1 + x = (((u : 𝒪[L]ˣ) : 𝒪[L]) : L) := by
    simp [x, x𝒪]
  simpa [x, x𝒪, hu_eq] using hgeom.symm

/-- One plus the inverse correction converges to the multiplicative inverse. -/
theorem chosenNormalBasisPrincipalUnitSet_one_add_inverseCorrection_tendsto_inv
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] {n : Nat}
    (hle : chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) ≤
      maximalIdealFieldSubmodule K L)
    {u : 𝒪[L]ˣ} (hu : u ∈ chosenNormalBasisPrincipalUnitSet K L n) :
    Tendsto
      (fun d : Nat =>
        1 + inverseCorrectionPartialSum (L := L)
          ((((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) d)
      atTop (nhds ((((u⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) : L))) := by
  have hprod :=
    chosenNormalBasisPrincipalUnitSet_inverseCorrectionProduct_tendsto_one
      (K := K) (L := L) hle hu
  have hmul :
      Tendsto
        (fun d : Nat =>
          (((u⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) : L) *
            ((((u : 𝒪[L]ˣ) : 𝒪[L]) : L) *
              (1 + inverseCorrectionPartialSum (L := L)
                ((((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) d)))
        atTop (nhds ((((u⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) : L))) := by
    simpa using
      (tendsto_const_nhds (x := (((u⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) : L))).mul hprod
  refine hmul.congr' (Eventually.of_forall ?_)
  intro d
  have huinv :
      ((((u⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) : L)) *
          ((((u : 𝒪[L]ˣ) : 𝒪[L]) : L)) = 1 := by
    have huinvₒ :
        (((u⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) * ((u : 𝒪[L]ˣ) : 𝒪[L])) = 1 :=
      Units.inv_mul u
    exact congrArg (algebraMap 𝒪[L] L) huinvₒ
  rw [← mul_assoc, huinv, one_mul]

/-- The inverse correction converges to the inverse minus one. -/
theorem chosenNormalBasisPrincipalUnitSet_inverseCorrection_tendsto_inv_sub_one
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] {n : Nat}
    (hle : chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) ≤
      maximalIdealFieldSubmodule K L)
    {u : 𝒪[L]ˣ} (hu : u ∈ chosenNormalBasisPrincipalUnitSet K L n) :
    Tendsto
      (fun d : Nat =>
        inverseCorrectionPartialSum (L := L)
          ((((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) d)
      atTop (nhds (((((u⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) : L) - 1))) := by
  have h :=
    chosenNormalBasisPrincipalUnitSet_one_add_inverseCorrection_tendsto_inv
      (K := K) (L := L) hle hu
  simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
    h.sub (tendsto_const_nhds (x := (1 : L)))

/-- Closedness of the lattice puts the inverse minus one back in the lattice. -/
theorem chosenNormalBasisPrincipalUnitSet_inverse_sub_one_mem_of_closed
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] {n : Nat}
    (hclosed : IsClosed
      ((chosenBaseUniformizerPowSubmodule K L n
        (chosenNormalBasisIntegerLattice K L) : Set L)))
    (hle : chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) ≤
      maximalIdealFieldSubmodule K L)
    (hmul : ∀ x : L,
      x ∈ chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) →
      ∀ y : L,
        y ∈ chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) →
          x * y ∈ chosenBaseUniformizerPowSubmodule K L n
            (chosenNormalBasisIntegerLattice K L))
    {u : 𝒪[L]ˣ} (hu : u ∈ chosenNormalBasisPrincipalUnitSet K L n) :
    ((((u⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) ∈
      chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) := by
  let E : Submodule 𝒪[K] L :=
    chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L)
  have hlim :
      (((((u⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) : L) - 1)) ∈ E := by
    exact submodule_mem_of_tendsto_of_forall_mem_of_closed
      (K := K) (L := L) (E := E) hclosed
      (chosenNormalBasisPrincipalUnitSet_inverseCorrection_tendsto_inv_sub_one
        (K := K) (L := L) hle hu)
      (fun d => chosenNormalBasisPrincipalUnitSet_inverseCorrectionPartialSum_mem
        (K := K) (L := L) hmul hu d)
  simpa [E] using hlim

/-- A closed normal-basis principal-unit set is closed under inversion. -/
theorem chosenNormalBasisPrincipalUnitSet_inv_mem_of_closed
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] {n : Nat}
    (hclosed : IsClosed
      ((chosenBaseUniformizerPowSubmodule K L n
        (chosenNormalBasisIntegerLattice K L) : Set L)))
    (hle : chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) ≤
      maximalIdealFieldSubmodule K L)
    (hmul : ∀ x : L,
      x ∈ chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) →
      ∀ y : L,
        y ∈ chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) →
          x * y ∈ chosenBaseUniformizerPowSubmodule K L n
            (chosenNormalBasisIntegerLattice K L))
    {u : 𝒪[L]ˣ} (hu : u ∈ chosenNormalBasisPrincipalUnitSet K L n) :
    u⁻¹ ∈ chosenNormalBasisPrincipalUnitSet K L n := by
  rw [mem_chosenNormalBasisPrincipalUnitSet_iff]
  exact chosenNormalBasisPrincipalUnitSet_inverse_sub_one_mem_of_closed
    (K := K) (L := L) hclosed hle hmul hu

/-- There is a closed normal-basis principal-unit set stable under inversion. -/
theorem exists_chosenNormalBasisPrincipalUnitSet_inv_mem_of_closed
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] :
    ∃ c : Nat, ∀ n : Nat, c ≤ n →
      IsClosed
        ((chosenBaseUniformizerPowSubmodule K L n
          (chosenNormalBasisIntegerLattice K L) : Set L)) →
      ∀ u : 𝒪[L]ˣ, u ∈ chosenNormalBasisPrincipalUnitSet K L n →
        u⁻¹ ∈ chosenNormalBasisPrincipalUnitSet K L n := by
  rcases exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_le_maximalIdeal_and_mul_closed
      (K := K) (L := L) with
    ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro n hcn hclosed u hu
  rcases hc n hcn with ⟨hle, hmul⟩
  exact chosenNormalBasisPrincipalUnitSet_inv_mem_of_closed
    (K := K) (L := L) hclosed hle hmul hu

omit [FiniteDimensional K L] [IsGalois K L] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] in
/-- The range of the integer-ring inclusion is the integer-ring field submodule. -/
theorem integerRingToFieldLinearMap_range_eq :
    LinearMap.range (integerRingToFieldLinearMap K L) =
      integerRingFieldSubmodule K L := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact y.2
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

omit [FiniteDimensional K L] [IsGalois K L] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] in
/-- If the extension valuation ring is finite over the base valuation ring, then
`𝒪_L`, viewed inside `L`, is a finitely generated `𝒪_K`-submodule. -/
theorem integerRingFieldSubmodule_fg_of_moduleFinite
    [Module.Finite 𝒪[K] 𝒪[L]] :
    (integerRingFieldSubmodule K L).FG := by
  have hfg :
      Submodule.FG
        ((⊤ : Submodule 𝒪[K] 𝒪[L]).map (integerRingToFieldLinearMap K L)) :=
    (Module.Finite.fg_top (R := 𝒪[K]) (M := 𝒪[L])).map
      (integerRingToFieldLinearMap K L)
  have hmap :
      (⊤ : Submodule 𝒪[K] 𝒪[L]).map (integerRingToFieldLinearMap K L) =
        integerRingFieldSubmodule K L := by
    rw [Submodule.map_top]
    exact integerRingToFieldLinearMap_range_eq (K := K) (L := L)
  simpa [hmap] using hfg

/-- The reverse lattice bound: if `𝒪_L` is finite over `𝒪_K`, then a
single high enough base-uniformizer power sends `𝒪_L` into the normal-basis
lattice `M`. -/
theorem exists_chosenBaseUniformizerPow_integerRingFieldSubmodule_le_chosenNormalBasisIntegerLattice
    [Module.Finite 𝒪[K] 𝒪[L]] :
    ∃ n : Nat,
      chosenBaseUniformizerPowSubmodule K L n (integerRingFieldSubmodule K L) ≤
        chosenNormalBasisIntegerLattice K L :=
  exists_chosenBaseUniformizerPowSubmodule_le_of_fg_of_field_span_eq_top
    (K := K) (L := L)
    (M := chosenNormalBasisIntegerLattice K L)
    (N := integerRingFieldSubmodule K L)
    (integerRingFieldSubmodule_fg_of_moduleFinite (K := K) (L := L))
    (chosenNormalBasisIntegerLattice_field_span_eq_top (K := K) (L := L))

/-- Some uniformizer-power normal-basis lattice is a neighborhood of zero. -/
theorem exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_mem_nhds_zero
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Module.Finite 𝒪[K] 𝒪[L]] :
    ∃ c : Nat, ∀ n : Nat, c ≤ n →
      ((chosenBaseUniformizerPowSubmodule K L n
        (chosenNormalBasisIntegerLattice K L) : Set L)) ∈ nhds (0 : L) := by
  rcases exists_chosenBaseUniformizerPow_integerRingFieldSubmodule_le_chosenNormalBasisIntegerLattice
      (K := K) (L := L) with
    ⟨a, ha⟩
  refine ⟨a, ?_⟩
  intro n han
  rcases Nat.exists_eq_add_of_le han with ⟨d, rfl⟩
  exact Filter.mem_of_superset
    (chosenBaseUniformizerPow_integerRingFieldSubmodule_mem_nhds_zero
      (K := K) (L := L) (a + (a + d)))
    (chosenBaseUniformizerPowSubmodule_add_le_chosenBaseUniformizerPowSubmodule_of_le
      (K := K) (L := L) (N := integerRingFieldSubmodule K L)
      (M := chosenNormalBasisIntegerLattice K L) (a := a) (n := a + d) ha)

/-- Some uniformizer-power normal-basis lattice is closed. -/
theorem exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_isClosed
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Module.Finite 𝒪[K] 𝒪[L]] :
    ∃ c : Nat, ∀ n : Nat, c ≤ n →
      IsClosed
        ((chosenBaseUniformizerPowSubmodule K L n
          (chosenNormalBasisIntegerLattice K L) : Set L)) := by
  rcases exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_mem_nhds_zero
      (K := K) (L := L) with
    ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro n hcn
  exact submodule_isClosed_of_mem_nhds_zero
    (K := K) (L := L) (E := chosenBaseUniformizerPowSubmodule K L n
      (chosenNormalBasisIntegerLattice K L)) (hc n hcn)

/-- There is a chosen normal-basis principal-unit set stable under inversion. -/
theorem exists_chosenNormalBasisPrincipalUnitSet_inv_mem
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Module.Finite 𝒪[K] 𝒪[L]] :
    ∃ c : Nat, ∀ n : Nat, c ≤ n →
      ∀ u : 𝒪[L]ˣ, u ∈ chosenNormalBasisPrincipalUnitSet K L n →
        u⁻¹ ∈ chosenNormalBasisPrincipalUnitSet K L n := by
  rcases exists_chosenNormalBasisPrincipalUnitSet_inv_mem_of_closed
      (K := K) (L := L) with
    ⟨c₁, hc₁⟩
  rcases exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_isClosed
      (K := K) (L := L) with
    ⟨c₂, hc₂⟩
  refine ⟨max c₁ c₂, ?_⟩
  intro n hmaxn u hu
  have hc₁n : c₁ ≤ n := le_trans (le_max_left c₁ c₂) hmaxn
  have hc₂n : c₂ ≤ n := le_trans (le_max_right c₁ c₂) hmaxn
  exact hc₁ n hc₁n (hc₂ n hc₂n) u hu

/-- There exists a principal-unit subgroup arising from a chosen normal-basis lattice. -/
theorem exists_chosenNormalBasisPrincipalUnitSubgroup
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Module.Finite 𝒪[K] 𝒪[L]] :
    ∃ c : Nat, ∀ n : Nat, c ≤ n →
      ∃ V : Subgroup 𝒪[L]ˣ,
        (V : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n ∧
        V ≤ principalUnits L 1 := by
  rcases exists_chosenNormalBasisPrincipalUnitSet_mul_closed_le_principalUnits_one
      (K := K) (L := L) with
    ⟨c₁, hc₁⟩
  rcases exists_chosenNormalBasisPrincipalUnitSet_inv_mem
      (K := K) (L := L) with
    ⟨c₂, hc₂⟩
  refine ⟨max c₁ c₂, ?_⟩
  intro n hmaxn
  have hc₁n : c₁ ≤ n := le_trans (le_max_left c₁ c₂) hmaxn
  have hc₂n : c₂ ≤ n := le_trans (le_max_right c₁ c₂) hmaxn
  rcases hc₁ n hc₁n with ⟨hmul, hle_one⟩
  let V : Subgroup 𝒪[L]ˣ := {
    carrier := chosenNormalBasisPrincipalUnitSet K L n
    one_mem' := chosenNormalBasisPrincipalUnitSet_one_mem (K := K) (L := L) n
    mul_mem' := by
      intro u v hu hv
      exact hmul u hu v hv
    inv_mem' := by
      intro u hu
      exact hc₂ n hc₂n u hu }
  refine ⟨V, rfl, ?_⟩
  intro u hu
  exact hle_one u hu

end
end CyclicCohomology

universe u

namespace CyclicCohomology

open LocalFieldTheory

noncomputable section

open scoped ValuativeRel
open Filter

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]

/-! ### Additive quotient boundary -/

omit [Valuation.HasExtension
  (ValuativeRel.valuation K) (ValuativeRel.valuation L)] in
/-- A suitable normal-basis principal-unit set has multiplication error in the
next lattice level. -/
theorem exists_chosenNormalBasisPrincipalUnitSet_mul_error_mem_succ :
    ∃ c : Nat, ∀ n : Nat, c ≤ n →
      ∀ u : 𝒪[L]ˣ, u ∈ chosenNormalBasisPrincipalUnitSet K L n →
        ∀ v : 𝒪[L]ˣ, v ∈ chosenNormalBasisPrincipalUnitSet K L n →
          (((((u * v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) -
              (((((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) +
                ((((v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L))) ∈
            chosenBaseUniformizerPowSubmodule K L (n + 1)
              (chosenNormalBasisIntegerLattice K L) := by
  rcases exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_mul_mul_mem_succ
      (K := K) (L := L) with
    ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro n hcn u hu v hv
  exact chosenNormalBasisPrincipalUnitSet_mul_error_mem_succ
    (K := K) (L := L) (hc n hcn) hu hv

/-- There exists a nested pair of normal-basis principal-unit subgroups at successive levels. -/
theorem exists_chosenNormalBasisPrincipalUnitSubgroupSuccPair
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Module.Finite 𝒪[K] 𝒪[L]] :
    ∃ c : Nat, ∀ n : Nat, c ≤ n →
      ∃ Vn Vsucc : Subgroup 𝒪[L]ˣ,
        (Vn : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n ∧
        (Vsucc : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L (n + 1) ∧
        Vsucc ≤ Vn ∧
        Vn ≤ principalUnits L 1 := by
  rcases exists_chosenNormalBasisPrincipalUnitSubgroup (K := K) (L := L) with
    ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro n hcn
  rcases hc n hcn with ⟨Vn, hVn, hVnle⟩
  have hcsucc : c ≤ n + 1 := le_trans hcn (Nat.le_succ n)
  rcases hc (n + 1) hcsucc with ⟨Vsucc, hVsucc, _hVsuccle⟩
  refine ⟨Vn, Vsucc, hVn, hVsucc, ?_, hVnle⟩
  intro u hu
  have hu_succ : u ∈ chosenNormalBasisPrincipalUnitSet K L (n + 1) := by
    exact hVsucc ▸ hu
  have hu_n : u ∈ chosenNormalBasisPrincipalUnitSet K L n :=
    chosenNormalBasisPrincipalUnitSet_succ_subset (K := K) (L := L) n hu_succ
  change u ∈ (Vn : Set 𝒪[L]ˣ)
  exact hVn.symm ▸ hu_n

end
end CyclicCohomology
end

section
-- module Solutions.OAIQ244_DUKE.Cyclic_Herbrand_Product
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.CyclicCohomology.instMulDistribMulActionBinaryCoefficientFamily _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Herbrand quotients of finite products

This file extracts the cardinality consequence of the product
decompositions of low-degree Tate cohomology, giving the corresponding
product formula for Herbrand quotients.
-/

open scoped BigOperators

noncomputable section

namespace CyclicCohomology

open CyclicCohomology.ProfiniteCohomology.Herbrand

universe uG uι uA

variable {G : Type uG} [Group G] [Fintype G]
variable {ι : Type uι} [Fintype ι]
variable (A : ι → Type uA)
variable [∀ i, CommGroup (A i)]
variable [∀ i, MulDistribMulAction G (A i)]

attribute [local instance] CyclicCohomology.instMulDistribMulActionForall_solutions_1
/-- The Herbrand quotient of a finite dependent product is the product of
the component Herbrand quotients. -/
theorem herbrandQuotient_pi
    (σ : G)
    [∀ i, Finite (HerbrandH0 G (A i))]
    [∀ i, Finite (HerbrandHMinusOne G (A i) σ)] :
    letI : Finite (HerbrandH0 G (∀ i, A i)) :=
      Finite.of_equiv
        (∀ i, HerbrandH0 G (A i))
        (herbrandH0PiEquiv (G := G) A).symm.toEquiv
    letI : Finite (HerbrandHMinusOne G (∀ i, A i) σ) :=
      Finite.of_equiv
        (∀ i, HerbrandHMinusOne G (A i) σ)
        (herbrandHMinusOnePiEquiv
          (G := G) A σ).symm.toEquiv
    herbrandQuotient (G := G) (A := ∀ i, A i) σ =
      ∏ i, herbrandQuotient (G := G) (A := A i) σ := by
  let : Finite (HerbrandH0 G (∀ i, A i)) :=
    Finite.of_equiv
      (∀ i, HerbrandH0 G (A i))
      (herbrandH0PiEquiv (G := G) A).symm.toEquiv
  let : Finite (HerbrandHMinusOne G (∀ i, A i) σ) :=
    Finite.of_equiv
      (∀ i, HerbrandHMinusOne G (A i) σ)
      (herbrandHMinusOnePiEquiv
        (G := G) A σ).symm.toEquiv
  unfold herbrandQuotient
  rw [Nat.card_congr
      (herbrandH0PiEquiv (G := G) A).toEquiv,
    Nat.card_congr
      (herbrandHMinusOnePiEquiv
        (G := G) A σ).toEquiv,
    Nat.card_pi, Nat.card_pi]
  simp only [Nat.cast_prod]
  simpa only [Finset.mem_univ, Finset.prod_const_one,
    Finset.prod_filter, true_and] using
    (Finset.prod_div_distrib
      (s := Finset.univ)
      (fun i : ι ↦
        (Nat.card (HerbrandH0 G (A i)) : ℚ))
      (fun i : ι ↦
        (Nat.card
          (HerbrandHMinusOne G (A i) σ) : ℚ))).symm

end CyclicCohomology
end
end

section
-- module Solutions.OAIQ244_DUKE.Cyclic_Herbrand_Permutation_Module
attribute [-instance] _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.HilbertRamification.Dedekind.inertiaSubgroupOfDecomposition_normal _root_.KummerTheory.DiscreteNthRootsSubgroup.instCommGroupSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.finite_nsmulAddKernel_padicInt_pi _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerKernel _root_.LocalFieldTheory.finite_nsmulAddKernel_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.CyclicCohomology.instMulDistribMulActionBinaryCoefficientFamily _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalClassFieldTheory.inducedRightCosetCoordinates_apply _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Herbrand quotients of permutation lattices

This file supplies the abstract cohomology calculation for permutation
lattices.  It proves the value of the Herbrand quotient on the trivial
integer lattice, transports that calculation through Shapiro's lemma to
transitive permutation lattices, and multiplies over a finite family of
orbits.  It also records invariance under passage to a finite-index stable
subgroup.
-/

open scoped BigOperators

noncomputable section

namespace CyclicCohomology

open CyclicCohomology.ProfiniteCohomology.Herbrand

universe uG uA uι

section TrivialInteger

variable {G : Type uG} [Group G] [Fintype G]

/-- Reduction modulo `|G|` on the fixed subgroup of the trivial integer
module. -/
def trivialIntFixedToZModHom :
    letI := trivialIntMulDistribMulAction G
    fixedSubgroup G (Multiplicative ℤ) →*
      Multiplicative (ZMod (Fintype.card G)) := by
  letI := trivialIntMulDistribMulAction G
  exact
    { toFun := fun x ↦ Multiplicative.ofAdd
        ((Multiplicative.toAdd
          (x : Multiplicative ℤ) : ℤ) :
            ZMod (Fintype.card G))
      map_one' := by simp
      map_mul' := by
        intro x y
        simp }

theorem trivialIntFixedToZModHom_surjective :
    letI := trivialIntMulDistribMulAction G
    Function.Surjective
      (trivialIntFixedToZModHom (G := G)) := by
  let := trivialIntMulDistribMulAction G
  intro y
  rcases ZMod.intCast_surjective
      (Multiplicative.toAdd y) with ⟨z, hz⟩
  let x : fixedSubgroup G (Multiplicative ℤ) :=
    ⟨Multiplicative.ofAdd z, by intro g; rfl⟩
  refine ⟨x, ?_⟩
  rw [show trivialIntFixedToZModHom
      (G := G) x =
        Multiplicative.ofAdd
          ((z : ℤ) : ZMod (Fintype.card G)) by rfl]
  exact congrArg Multiplicative.ofAdd hz

/-- The kernel of reduction modulo `|G|` is the norm subgroup. -/
theorem trivialIntFixedToZModHom_ker :
    letI := trivialIntMulDistribMulAction G
    MonoidHom.ker
        (trivialIntFixedToZModHom (G := G)) =
      (tateNormSubgroup G
        (Multiplicative ℤ)).subgroupOf
          (fixedSubgroup G (Multiplicative ℤ)) := by
  let := trivialIntMulDistribMulAction G
  ext x
  rw [MonoidHom.mem_ker]
  constructor
  · intro hx
    have hx0 :
        ((Multiplicative.toAdd
          (x : Multiplicative ℤ) : ℤ) :
            ZMod (Fintype.card G)) = 0 := by
      exact congrArg Multiplicative.toAdd hx
    rcases
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hx0
      with ⟨z, hz⟩
    change (x : Multiplicative ℤ) ∈
      tateNormSubgroup G (Multiplicative ℤ)
    refine ⟨Multiplicative.ofAdd z, ?_⟩
    have htoAdd :
        Multiplicative.toAdd
            (tateNorm G (Multiplicative ℤ)
              (Multiplicative.ofAdd z)) =
          Multiplicative.toAdd
            (x : Multiplicative ℤ) := by
      rw [trivialInt_tateNorm_toAdd]
      exact hz.symm
    exact congrArg Multiplicative.ofAdd htoAdd
  · intro hx
    change (x : Multiplicative ℤ) ∈
      tateNormSubgroup G (Multiplicative ℤ) at hx
    rcases hx with ⟨z, hz⟩
    exact congrArg Multiplicative.ofAdd (by
      change
        ((Multiplicative.toAdd
          (x : Multiplicative ℤ) : ℤ) :
            ZMod (Fintype.card G)) = 0
      rw [← hz, tateNormHom_apply, trivialInt_tateNorm_toAdd]
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2
      exact ⟨Multiplicative.toAdd z, rfl⟩)

/-- The degree-zero Herbrand group of the trivial integer module is
`ℤ / |G|ℤ`. -/
noncomputable def trivialIntHerbrandH0EquivZMod :
    letI := trivialIntMulDistribMulAction G
    HerbrandH0 G (Multiplicative ℤ) ≃*
      Multiplicative (ZMod (Fintype.card G)) := by
  letI := trivialIntMulDistribMulAction G
  exact
    (HerbrandH0.equiv
      (G := G) (A := Multiplicative ℤ)).trans
      ((QuotientGroup.quotientMulEquivOfEq
        (trivialIntFixedToZModHom_ker
          (G := G)).symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective
          (trivialIntFixedToZModHom (G := G))
          (trivialIntFixedToZModHom_surjective
            (G := G))))

theorem trivialIntHerbrandH0Finite :
    letI := trivialIntMulDistribMulAction G
    Finite (HerbrandH0 G (Multiplicative ℤ)) := by
  let := trivialIntMulDistribMulAction G
  exact Finite.of_equiv
    (Multiplicative (ZMod (Fintype.card G)))
    (trivialIntHerbrandH0EquivZMod
      (G := G)).symm.toEquiv

theorem trivialInt_herbrandH0_card :
    letI := trivialIntMulDistribMulAction G
    letI := trivialIntHerbrandH0Finite (G := G)
    Nat.card
        (HerbrandH0 G (Multiplicative ℤ)) =
      Fintype.card G := by
  let := trivialIntMulDistribMulAction G
  let := trivialIntHerbrandH0Finite (G := G)
  rw [Nat.card_congr
      (trivialIntHerbrandH0EquivZMod
        (G := G)).toEquiv]
  simp

/-- The norm kernel of the trivial torsion-free integer module is
trivial. -/
theorem trivialInt_normKernelSubgroup_eq_bot :
    letI := trivialIntMulDistribMulAction G
    normKernelSubgroup G (Multiplicative ℤ) = ⊥ := by
  let := trivialIntMulDistribMulAction G
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_bot]
    exact congrArg Multiplicative.ofAdd (by
      change
        Multiplicative.toAdd
          (x : Multiplicative ℤ) = 0
      have hnorm :
          (Fintype.card G : ℤ) *
              Multiplicative.toAdd
                (x : Multiplicative ℤ) = 0 := by
        rw [← trivialInt_tateNorm_toAdd]
        exact congrArg Multiplicative.toAdd hx
      exact (mul_eq_zero.mp hnorm).resolve_left (by
        exact_mod_cast Fintype.card_ne_zero))
  · exact bot_le

theorem trivialIntHerbrandHMinusOneFinite
    (σ : G) :
    letI := trivialIntMulDistribMulAction G
    Finite
      (HerbrandHMinusOne G
        (Multiplicative ℤ) σ) := by
  let := trivialIntMulDistribMulAction G
  have : Subsingleton
      (normKernelSubgroup G
        (Multiplicative ℤ)) := by
    rw [trivialInt_normKernelSubgroup_eq_bot
      (G := G)]
    infer_instance
  let : Subsingleton
      (HerbrandHMinusOne G
        (Multiplicative ℤ) σ) :=
    ⟨fun q ↦
      HerbrandHMinusOne.inductionOn σ
        (motive := fun q ↦ ∀ r, q = r) q fun x r ↦
          HerbrandHMinusOne.inductionOn σ
            (motive := fun r ↦
              HerbrandHMinusOne.mk σ x = r)
            r fun y ↦
              congrArg
                (fun z ↦ HerbrandHMinusOne.mk σ z)
                (Subsingleton.elim x y)⟩
  exact Finite.of_injective
    (fun _ : HerbrandHMinusOne G
      (Multiplicative ℤ) σ ↦ false)
    (fun x y _ ↦ Subsingleton.elim x y)

theorem trivialInt_herbrandHMinusOne_card_eq_one
    (σ : G) :
    letI := trivialIntMulDistribMulAction G
    letI :=
      trivialIntHerbrandHMinusOneFinite
        (G := G) σ
    Nat.card
      (HerbrandHMinusOne G
        (Multiplicative ℤ) σ) = 1 := by
  let := trivialIntMulDistribMulAction G
  let :=
    trivialIntHerbrandHMinusOneFinite
      (G := G) σ
  have : Subsingleton
      (normKernelSubgroup G
        (Multiplicative ℤ)) := by
    rw [trivialInt_normKernelSubgroup_eq_bot
      (G := G)]
    infer_instance
  let : Subsingleton
      (HerbrandHMinusOne G
        (Multiplicative ℤ) σ) :=
    ⟨fun q ↦
      HerbrandHMinusOne.inductionOn σ
        (motive := fun q ↦ ∀ r, q = r) q fun x r ↦
          HerbrandHMinusOne.inductionOn σ
            (motive := fun r ↦
              HerbrandHMinusOne.mk σ x = r)
            r fun y ↦
              congrArg
                (fun z ↦ HerbrandHMinusOne.mk σ z)
                (Subsingleton.elim x y)⟩
  rw [Nat.card_eq_one_iff_unique]
  exact ⟨inferInstance, inferInstance⟩

end TrivialInteger

section TransitivePermutationLattice

variable {G : Type uG} [Group G] [Fintype G]

theorem transitivePermutationLatticeHerbrandH0Finite
    (H : Subgroup G)
    (σ : G)
    (hgen : ∀ g : G,
      g ∈ Subgroup.zpowers σ) :
    letI _stabilizerAction :
        MulDistribMulAction H (Multiplicative ℤ) :=
      trivialIntMulDistribMulAction H
    letI _stabilizerFintype : Fintype H :=
      Fintype.ofFinite H
    Finite
      (HerbrandH0 G
        (TransitivePermutationLattice H)) := by
  let stabilizerAction :
      MulDistribMulAction H (Multiplicative ℤ) :=
    trivialIntMulDistribMulAction H
  let stabilizerFintype : Fintype H :=
    Fintype.ofFinite H
  let : Finite
      (HerbrandH0 H (Multiplicative ℤ)) :=
    trivialIntHerbrandH0Finite (G := H)
  exact Finite.of_equiv
    (HerbrandH0 H (Multiplicative ℤ))
    (inducedHerbrandH0EquivOfFiniteCyclic
      H σ hgen).symm.toEquiv

theorem transitivePermutationLatticeHerbrandHMinusOneFinite
    (H : Subgroup G)
    (σ : G)
    (hgen : ∀ g : G,
      g ∈ Subgroup.zpowers σ) :
    letI _stabilizerAction :
        MulDistribMulAction H (Multiplicative ℤ) :=
      trivialIntMulDistribMulAction H
    letI _stabilizerFintype : Fintype H :=
      Fintype.ofFinite H
    Finite
      (HerbrandHMinusOne G
        (TransitivePermutationLattice H) σ) := by
  let stabilizerAction :
      MulDistribMulAction H (Multiplicative ℤ) :=
    trivialIntMulDistribMulAction H
  let stabilizerFintype : Fintype H :=
    Fintype.ofFinite H
  let δ :=
    subgroupGeneratorOfGenerator H σ hgen
  let : Finite
      (HerbrandHMinusOne H
        (Multiplicative ℤ) δ) :=
    trivialIntHerbrandHMinusOneFinite
      (G := H) δ
  exact Finite.of_equiv
    (HerbrandHMinusOne H
      (Multiplicative ℤ) δ)
    (inducedHerbrandHMinusOneEquivOfFiniteCyclic
      H σ hgen).symm.toEquiv

/-- The Herbrand quotient of the permutation lattice on one orbit is the
order of the stabilizer. -/
theorem transitivePermutationLattice_herbrandQuotient_eq_stabilizerCard
    (H : Subgroup G)
    (σ : G)
    (hgen : ∀ g : G,
      g ∈ Subgroup.zpowers σ) :
    letI _stabilizerAction :
        MulDistribMulAction H (Multiplicative ℤ) :=
      trivialIntMulDistribMulAction H
    letI _stabilizerFintype : Fintype H :=
      Fintype.ofFinite H
    letI _h0Finite :
        Finite
          (HerbrandH0 G
            (TransitivePermutationLattice H)) :=
      transitivePermutationLatticeHerbrandH0Finite
        H σ hgen
    letI _hMinusOneFinite :
        Finite
          (HerbrandHMinusOne G
            (TransitivePermutationLattice H) σ) :=
      transitivePermutationLatticeHerbrandHMinusOneFinite
        H σ hgen
    herbrandQuotient
        (G := G)
        (A := TransitivePermutationLattice H) σ =
      (Fintype.card H : ℚ) := by
  let stabilizerAction :
      MulDistribMulAction H (Multiplicative ℤ) :=
    trivialIntMulDistribMulAction H
  let stabilizerFintype : Fintype H :=
    Fintype.ofFinite H
  let δ :=
    subgroupGeneratorOfGenerator H σ hgen
  let stabilizerH0Finite :
      Finite
        (HerbrandH0 H (Multiplicative ℤ)) :=
    trivialIntHerbrandH0Finite (G := H)
  let stabilizerHMinusOneFinite :
      Finite
        (HerbrandHMinusOne H
          (Multiplicative ℤ) δ) :=
    trivialIntHerbrandHMinusOneFinite
      (G := H) δ
  let h0Finite :
      Finite
        (HerbrandH0 G
          (TransitivePermutationLattice H)) :=
    transitivePermutationLatticeHerbrandH0Finite
      H σ hgen
  let hMinusOneFinite :
      Finite
        (HerbrandHMinusOne G
          (TransitivePermutationLattice H) σ) :=
    transitivePermutationLatticeHerbrandHMinusOneFinite
      H σ hgen
  have h0Card :
      Nat.card
          (HerbrandH0 G
            (TransitivePermutationLattice H)) =
        Fintype.card H := by
    calc
      Nat.card
          (HerbrandH0 G
            (TransitivePermutationLattice H)) =
        Nat.card
          (HerbrandH0 H
            (Multiplicative ℤ)) :=
        Nat.card_congr
          (inducedHerbrandH0EquivOfFiniteCyclic
            H σ hgen).toEquiv
      _ = Fintype.card H :=
        trivialInt_herbrandH0_card (G := H)
  have hMinusOneCard :
      Nat.card
          (HerbrandHMinusOne G
            (TransitivePermutationLattice H) σ) =
        1 := by
    calc
      Nat.card
          (HerbrandHMinusOne G
            (TransitivePermutationLattice H) σ) =
        Nat.card
          (HerbrandHMinusOne H
            (Multiplicative ℤ) δ) :=
        Nat.card_congr
          (inducedHerbrandHMinusOneEquivOfFiniteCyclic
            H σ hgen).toEquiv
      _ = 1 :=
        trivialInt_herbrandHMinusOne_card_eq_one
          (G := H) δ
  rw [herbrandQuotient_eq_card_ratio,
    h0Card, hMinusOneCard]
  simp

end TransitivePermutationLattice

section PermutationLatticeOrbits

variable {G : Type uG} [Group G] [Fintype G]
variable {ι : Type uι} [Fintype ι]

/-- The Herbrand quotient of a finite permutation lattice is
the product of the orders of the stabilizers of chosen orbit
representatives. -/
theorem permutationLattice_herbrandQuotient_eq_stabilizerProduct
    (H : ι → Subgroup G)
    (σ : G)
    (hgen : ∀ g : G,
      g ∈ Subgroup.zpowers σ) :
    letI _stabilizerAction : ∀ i,
        MulDistribMulAction (H i)
          (Multiplicative ℤ) :=
      fun i ↦ trivialIntMulDistribMulAction (H i)
    letI _stabilizerFintype : ∀ i,
        Fintype (H i) :=
      fun _ ↦ Fintype.ofFinite _
    letI _orbitAction : ∀ i,
        MulDistribMulAction G
          (TransitivePermutationLattice (H i)) :=
      fun i ↦ inducedMulDistribMulAction (H i)
    letI _familyAction :
        MulDistribMulAction G
          (PermutationLatticeOrbitFamily H) :=
      piMulDistribMulAction G
        (fun i ↦
          TransitivePermutationLattice (H i))
    letI _orbitH0Finite : ∀ i,
        Finite
          (HerbrandH0 G
            (TransitivePermutationLattice (H i))) :=
      fun i ↦
        transitivePermutationLatticeHerbrandH0Finite
          (H i) σ hgen
    letI _orbitHMinusOneFinite : ∀ i,
        Finite
          (HerbrandHMinusOne G
            (TransitivePermutationLattice (H i)) σ) :=
      fun i ↦
        transitivePermutationLatticeHerbrandHMinusOneFinite
          (H i) σ hgen
    letI _familyH0Finite :
        Finite
          (HerbrandH0 G
            (PermutationLatticeOrbitFamily H)) :=
      Finite.of_equiv
        (∀ i,
          HerbrandH0 G
            (TransitivePermutationLattice (H i)))
        (herbrandH0PiEquiv
          (G := G)
          (fun i ↦
            TransitivePermutationLattice
              (H i))).symm.toEquiv
    letI _familyHMinusOneFinite :
        Finite
          (HerbrandHMinusOne G
            (PermutationLatticeOrbitFamily H) σ) :=
      Finite.of_equiv
        (∀ i,
          HerbrandHMinusOne G
            (TransitivePermutationLattice (H i)) σ)
        (herbrandHMinusOnePiEquiv
          (G := G)
          (fun i ↦
            TransitivePermutationLattice
              (H i)) σ).symm.toEquiv
    herbrandQuotient
        (G := G)
        (A := PermutationLatticeOrbitFamily H) σ =
      ∏ i, (Fintype.card (H i) : ℚ) := by
  let stabilizerAction : ∀ i,
      MulDistribMulAction (H i)
        (Multiplicative ℤ) :=
    fun i ↦ trivialIntMulDistribMulAction (H i)
  let stabilizerFintype : ∀ i,
      Fintype (H i) :=
    fun _ ↦ Fintype.ofFinite _
  let orbitAction : ∀ i,
      MulDistribMulAction G
        (TransitivePermutationLattice (H i)) :=
    fun i ↦ inducedMulDistribMulAction (H i)
  let familyAction :
      MulDistribMulAction G
        (PermutationLatticeOrbitFamily H) :=
    piMulDistribMulAction G
      (fun i ↦
        TransitivePermutationLattice (H i))
  let orbitH0Finite : ∀ i,
      Finite
        (HerbrandH0 G
          (TransitivePermutationLattice (H i))) :=
    fun i ↦
      transitivePermutationLatticeHerbrandH0Finite
        (H i) σ hgen
  let orbitHMinusOneFinite : ∀ i,
      Finite
        (HerbrandHMinusOne G
          (TransitivePermutationLattice (H i)) σ) :=
    fun i ↦
      transitivePermutationLatticeHerbrandHMinusOneFinite
        (H i) σ hgen
  let familyH0Finite :
      Finite
        (HerbrandH0 G
          (PermutationLatticeOrbitFamily H)) :=
    Finite.of_equiv
      (∀ i,
        HerbrandH0 G
          (TransitivePermutationLattice (H i)))
      (herbrandH0PiEquiv
        (G := G)
        (fun i ↦
          TransitivePermutationLattice
            (H i))).symm.toEquiv
  let familyHMinusOneFinite :
      Finite
        (HerbrandHMinusOne G
          (PermutationLatticeOrbitFamily H) σ) :=
    Finite.of_equiv
      (∀ i,
        HerbrandHMinusOne G
          (TransitivePermutationLattice (H i)) σ)
      (herbrandHMinusOnePiEquiv
        (G := G)
        (fun i ↦
          TransitivePermutationLattice
            (H i)) σ).symm.toEquiv
  calc
    herbrandQuotient
        (G := G)
        (A := PermutationLatticeOrbitFamily H) σ =
        ∏ i, herbrandQuotient
          (G := G)
          (A := TransitivePermutationLattice
            (H i)) σ :=
      herbrandQuotient_pi
        (fun i ↦
          TransitivePermutationLattice
            (H i)) σ
    _ = ∏ i, (Fintype.card (H i) : ℚ) := by
      apply Finset.prod_congr rfl
      intro i _
      exact
        transitivePermutationLattice_herbrandQuotient_eq_stabilizerCard
          (H i) σ hgen

end PermutationLatticeOrbits

section CanonicalPermutationFunctions

variable {G : Type uG} [Group G] [Fintype G]
variable {ι : Type uι} [Fintype ι] [MulAction G ι]

/-- Integer-valued functions on a finite `G`-set, decomposed into the
induced modules belonging to its orbits. -/
noncomputable def permutationFunctionOrbitEquiv :
    letI _stabilizerAction :
        ∀ ω : MulAction.orbitRel.Quotient G ι,
          MulDistribMulAction
            (permutationOrbitStabilizer ω)
            (Multiplicative ℤ) :=
      fun ω =>
        trivialIntMulDistribMulAction
          (permutationOrbitStabilizer ω)
    (ι → Multiplicative ℤ) ≃*
      PermutationLatticeOrbitFamily
        (fun ω : MulAction.orbitRel.Quotient G ι =>
          permutationOrbitStabilizer ω) := by
  letI stabilizerAction :
      ∀ ω : MulAction.orbitRel.Quotient G ι,
        MulDistribMulAction
          (permutationOrbitStabilizer ω)
          (Multiplicative ℤ) :=
    fun ω =>
      trivialIntMulDistribMulAction
        (permutationOrbitStabilizer ω)
  refine
    { toFun := fun f ω =>
        ⟨fun x => f (x⁻¹ • ω.out), ?_⟩
      invFun := fun F i =>
        (F (Quotient.mk'' i)).1
          ((chosenPermutationOrbitTransport
            (G := G) i)⁻¹)
      left_inv := ?_
      right_inv := ?_
      map_mul' := ?_ }
  · intro h x
    change
      f ((h.1 * x)⁻¹ • ω.out) =
        f (x⁻¹ • ω.out)
    have hhInv :
        h.1⁻¹ • ω.out = ω.out := by
      calc
        h.1⁻¹ • ω.out =
            h.1⁻¹ • (h.1 • ω.out) :=
          congrArg (fun y => h.1⁻¹ • y) h.2.symm
        _ = ω.out := inv_smul_smul h.1 ω.out
    rw [mul_inv_rev, mul_smul, hhInv]
  · intro f
    funext i
    change
      f (((chosenPermutationOrbitTransport
          (G := G) i)⁻¹)⁻¹ •
          chosenPermutationOrbitRepresentative
            (G := G) i) = f i
    rw [inv_inv, chosenPermutationOrbitTransport_smul]
  · intro F
    funext ω
    apply Subtype.ext
    funext x
    have hω :
        (Quotient.mk'' (x⁻¹ • ω.out) :
            MulAction.orbitRel.Quotient G ι) = ω := by
      calc
        (Quotient.mk'' (x⁻¹ • ω.out) :
            MulAction.orbitRel.Quotient G ι) =
            Quotient.mk'' ω.out := by
              exact Quotient.sound
                (MulAction.orbitRel_apply.mpr
                  ⟨x⁻¹, rfl⟩)
        _ = ω := Quotient.out_eq' ω
    let t : G :=
      chosenPermutationOrbitTransport
        (G := G) (x⁻¹ • ω.out)
    have ht :
        t • ω.out = x⁻¹ • ω.out := by
      have ht' :=
        chosenPermutationOrbitTransport_smul
          (G := G) (x⁻¹ • ω.out)
      simpa only [t, chosenPermutationOrbitRepresentative,
        hω] using ht'
    let h : permutationOrbitStabilizer ω :=
      ⟨t⁻¹ * x⁻¹, by
        change (t⁻¹ * x⁻¹) • ω.out = ω.out
        rw [mul_smul, ← ht, inv_smul_smul]⟩
    change
      (F (Quotient.mk'' (x⁻¹ • ω.out))).1
          ((chosenPermutationOrbitTransport
            (G := G) (x⁻¹ • ω.out))⁻¹) =
        (F ω).1 x
    rw [hω]
    change (F ω).1 t⁻¹ = (F ω).1 x
    have hcov := (F ω).2 h x
    change (F ω).1 (h.1 * x) = (F ω).1 x at hcov
    simpa [h, mul_assoc] using hcov
  · intro f k
    funext ω
    apply Subtype.ext
    funext x
    rfl

omit [Fintype G] [Fintype ι] in
/-- The orbit decomposition of integer-valued functions is
`G`-equivariant. -/
theorem permutationFunctionOrbitEquiv_equivariant :
    letI _functionAction :
        MulDistribMulAction G (ι → Multiplicative ℤ) :=
      permutationFunctionMulDistribMulAction
    letI _stabilizerAction :
        ∀ ω : MulAction.orbitRel.Quotient G ι,
          MulDistribMulAction
            (permutationOrbitStabilizer ω)
            (Multiplicative ℤ) :=
      fun ω =>
        trivialIntMulDistribMulAction
          (permutationOrbitStabilizer ω)
    letI _orbitAction :
        ∀ ω : MulAction.orbitRel.Quotient G ι,
          MulDistribMulAction G
            (TransitivePermutationLattice
              (permutationOrbitStabilizer ω)) :=
      fun ω =>
        inducedMulDistribMulAction
          (permutationOrbitStabilizer ω)
    letI _familyAction :
        MulDistribMulAction G
          (PermutationLatticeOrbitFamily
            (fun ω : MulAction.orbitRel.Quotient G ι =>
              permutationOrbitStabilizer ω)) :=
      piMulDistribMulAction G
        (fun ω : MulAction.orbitRel.Quotient G ι =>
          TransitivePermutationLattice
            (permutationOrbitStabilizer ω))
    ∀ (g : G) (f : ι → Multiplicative ℤ),
      permutationFunctionOrbitEquiv (G := G) (ι := ι)
          (g • f) =
        g • permutationFunctionOrbitEquiv
          (G := G) (ι := ι) f := by
  let functionAction :
      MulDistribMulAction G (ι → Multiplicative ℤ) :=
    permutationFunctionMulDistribMulAction
  let stabilizerAction :
      ∀ ω : MulAction.orbitRel.Quotient G ι,
        MulDistribMulAction
          (permutationOrbitStabilizer ω)
          (Multiplicative ℤ) :=
    fun ω =>
      trivialIntMulDistribMulAction
        (permutationOrbitStabilizer ω)
  let orbitAction :
      ∀ ω : MulAction.orbitRel.Quotient G ι,
        MulDistribMulAction G
          (TransitivePermutationLattice
            (permutationOrbitStabilizer ω)) :=
    fun ω =>
      inducedMulDistribMulAction
        (permutationOrbitStabilizer ω)
  let familyAction :
      MulDistribMulAction G
        (PermutationLatticeOrbitFamily
          (fun ω : MulAction.orbitRel.Quotient G ι =>
            permutationOrbitStabilizer ω)) :=
    piMulDistribMulAction G
      (fun ω : MulAction.orbitRel.Quotient G ι =>
        TransitivePermutationLattice
          (permutationOrbitStabilizer ω))
  intro g f
  funext ω
  apply Subtype.ext
  funext x
  change
    f (g⁻¹ • (x⁻¹ • ω.out)) =
      f ((x * g)⁻¹ • ω.out)
  rw [mul_inv_rev, mul_smul]

/-- Degree-zero Tate cohomology of a finite integral permutation module
is finite for a cyclic generator. -/
theorem permutationFunctionHerbrandH0Finite
    (σ : G)
    (hgen : ∀ g : G,
      g ∈ Subgroup.zpowers σ) :
    letI _functionAction :
        MulDistribMulAction G (ι → Multiplicative ℤ) :=
      permutationFunctionMulDistribMulAction
    Finite
      (HerbrandH0 G (ι → Multiplicative ℤ)) := by
  let functionAction :
      MulDistribMulAction G (ι → Multiplicative ℤ) :=
    permutationFunctionMulDistribMulAction
  let stabilizerAction :
      ∀ ω : MulAction.orbitRel.Quotient G ι,
        MulDistribMulAction
          (permutationOrbitStabilizer ω)
          (Multiplicative ℤ) :=
    fun ω =>
      trivialIntMulDistribMulAction
        (permutationOrbitStabilizer ω)
  let stabilizerFintype :
      ∀ ω : MulAction.orbitRel.Quotient G ι,
        Fintype (permutationOrbitStabilizer ω) :=
    fun _ => Fintype.ofFinite _
  let orbitAction :
      ∀ ω : MulAction.orbitRel.Quotient G ι,
        MulDistribMulAction G
          (TransitivePermutationLattice
            (permutationOrbitStabilizer ω)) :=
    fun ω =>
      inducedMulDistribMulAction
        (permutationOrbitStabilizer ω)
  let familyAction :
      MulDistribMulAction G
        (PermutationLatticeOrbitFamily
          (fun ω : MulAction.orbitRel.Quotient G ι =>
            permutationOrbitStabilizer ω)) :=
    piMulDistribMulAction G
      (fun ω : MulAction.orbitRel.Quotient G ι =>
        TransitivePermutationLattice
          (permutationOrbitStabilizer ω))
  let orbitH0Finite :
      ∀ ω : MulAction.orbitRel.Quotient G ι,
        Finite
          (HerbrandH0 G
            (TransitivePermutationLattice
              (permutationOrbitStabilizer ω))) :=
    fun ω =>
      transitivePermutationLatticeHerbrandH0Finite
        (permutationOrbitStabilizer ω) σ hgen
  let familyH0Finite :
      Finite
        (HerbrandH0 G
          (PermutationLatticeOrbitFamily
            (fun ω : MulAction.orbitRel.Quotient G ι =>
              permutationOrbitStabilizer ω))) :=
    Finite.of_equiv
      (∀ ω : MulAction.orbitRel.Quotient G ι,
        HerbrandH0 G
          (TransitivePermutationLattice
            (permutationOrbitStabilizer ω)))
      (herbrandH0PiEquiv
        (G := G)
        (fun ω : MulAction.orbitRel.Quotient G ι =>
          TransitivePermutationLattice
            (permutationOrbitStabilizer ω))).symm.toEquiv
  let e :=
    permutationFunctionOrbitEquiv
      (G := G) (ι := ι)
  let he :=
    permutationFunctionOrbitEquiv_equivariant
      (G := G) (ι := ι)
  exact
    herbrandH0Finite_of_equivariantMulEquiv
      e.symm (mulEquiv_symm_commutes_smul e he)

/-- Degree-minus-one Tate cohomology of a finite integral permutation
module is finite for a cyclic generator. -/
theorem permutationFunctionHerbrandHMinusOneFinite
    (σ : G)
    (hgen : ∀ g : G,
      g ∈ Subgroup.zpowers σ) :
    letI _functionAction :
        MulDistribMulAction G (ι → Multiplicative ℤ) :=
      permutationFunctionMulDistribMulAction
    Finite
      (HerbrandHMinusOne G
        (ι → Multiplicative ℤ) σ) := by
  let functionAction :
      MulDistribMulAction G (ι → Multiplicative ℤ) :=
    permutationFunctionMulDistribMulAction
  let stabilizerAction :
      ∀ ω : MulAction.orbitRel.Quotient G ι,
        MulDistribMulAction
          (permutationOrbitStabilizer ω)
          (Multiplicative ℤ) :=
    fun ω =>
      trivialIntMulDistribMulAction
        (permutationOrbitStabilizer ω)
  let stabilizerFintype :
      ∀ ω : MulAction.orbitRel.Quotient G ι,
        Fintype (permutationOrbitStabilizer ω) :=
    fun _ => Fintype.ofFinite _
  let orbitAction :
      ∀ ω : MulAction.orbitRel.Quotient G ι,
        MulDistribMulAction G
          (TransitivePermutationLattice
            (permutationOrbitStabilizer ω)) :=
    fun ω =>
      inducedMulDistribMulAction
        (permutationOrbitStabilizer ω)
  let familyAction :
      MulDistribMulAction G
        (PermutationLatticeOrbitFamily
          (fun ω : MulAction.orbitRel.Quotient G ι =>
            permutationOrbitStabilizer ω)) :=
    piMulDistribMulAction G
      (fun ω : MulAction.orbitRel.Quotient G ι =>
        TransitivePermutationLattice
          (permutationOrbitStabilizer ω))
  let orbitHMinusOneFinite :
      ∀ ω : MulAction.orbitRel.Quotient G ι,
        Finite
          (HerbrandHMinusOne G
            (TransitivePermutationLattice
              (permutationOrbitStabilizer ω)) σ) :=
    fun ω =>
      transitivePermutationLatticeHerbrandHMinusOneFinite
        (permutationOrbitStabilizer ω) σ hgen
  let familyHMinusOneFinite :
      Finite
        (HerbrandHMinusOne G
          (PermutationLatticeOrbitFamily
            (fun ω : MulAction.orbitRel.Quotient G ι =>
              permutationOrbitStabilizer ω)) σ) :=
    Finite.of_equiv
      (∀ ω : MulAction.orbitRel.Quotient G ι,
        HerbrandHMinusOne G
          (TransitivePermutationLattice
            (permutationOrbitStabilizer ω)) σ)
      (herbrandHMinusOnePiEquiv
        (G := G)
        (fun ω : MulAction.orbitRel.Quotient G ι =>
          TransitivePermutationLattice
            (permutationOrbitStabilizer ω)) σ).symm.toEquiv
  let e :=
    permutationFunctionOrbitEquiv
      (G := G) (ι := ι)
  let he :=
    permutationFunctionOrbitEquiv_equivariant
      (G := G) (ι := ι)
  exact
    herbrandHMinusOneFinite_of_equivariantMulEquiv
      e.symm (mulEquiv_symm_commutes_smul e he) σ

/-- Canonical orbit form of the permutation-lattice Herbrand quotient formula: the Herbrand quotient of the
integer-valued functions on a finite `G`-set is the product of the
orders of the stabilizers of its orbits. -/
theorem permutationFunction_herbrandQuotient_eq_stabilizerProduct
    (σ : G)
    (hgen : ∀ g : G,
      g ∈ Subgroup.zpowers σ) :
    letI _functionAction :
        MulDistribMulAction G (ι → Multiplicative ℤ) :=
      permutationFunctionMulDistribMulAction
    letI _orbitFintype :
        Fintype (MulAction.orbitRel.Quotient G ι) :=
      Fintype.ofFinite _
    letI _stabilizerFintype :
        ∀ ω : MulAction.orbitRel.Quotient G ι,
          Fintype (permutationOrbitStabilizer ω) :=
      fun _ => Fintype.ofFinite _
    letI _functionH0Finite :
        Finite
          (HerbrandH0 G
            (ι → Multiplicative ℤ)) :=
      permutationFunctionHerbrandH0Finite σ hgen
    letI _functionHMinusOneFinite :
        Finite
          (HerbrandHMinusOne G
            (ι → Multiplicative ℤ) σ) :=
      permutationFunctionHerbrandHMinusOneFinite σ hgen
    herbrandQuotient
        (G := G) (A := ι → Multiplicative ℤ) σ =
      ∏ ω : MulAction.orbitRel.Quotient G ι,
        (Fintype.card
          (permutationOrbitStabilizer ω) : ℚ) := by
  let functionAction :
      MulDistribMulAction G (ι → Multiplicative ℤ) :=
    permutationFunctionMulDistribMulAction
  let orbitFintype :
      Fintype (MulAction.orbitRel.Quotient G ι) :=
    Fintype.ofFinite _
  let stabilizerAction :
      ∀ ω : MulAction.orbitRel.Quotient G ι,
        MulDistribMulAction
          (permutationOrbitStabilizer ω)
          (Multiplicative ℤ) :=
    fun ω =>
      trivialIntMulDistribMulAction
        (permutationOrbitStabilizer ω)
  let stabilizerFintype :
      ∀ ω : MulAction.orbitRel.Quotient G ι,
        Fintype (permutationOrbitStabilizer ω) :=
    fun _ => Fintype.ofFinite _
  let orbitAction :
      ∀ ω : MulAction.orbitRel.Quotient G ι,
        MulDistribMulAction G
          (TransitivePermutationLattice
            (permutationOrbitStabilizer ω)) :=
    fun ω =>
      inducedMulDistribMulAction
        (permutationOrbitStabilizer ω)
  let familyAction :
      MulDistribMulAction G
        (PermutationLatticeOrbitFamily
          (fun ω : MulAction.orbitRel.Quotient G ι =>
            permutationOrbitStabilizer ω)) :=
    piMulDistribMulAction G
      (fun ω : MulAction.orbitRel.Quotient G ι =>
        TransitivePermutationLattice
          (permutationOrbitStabilizer ω))
  let orbitH0Finite :
      ∀ ω : MulAction.orbitRel.Quotient G ι,
        Finite
          (HerbrandH0 G
            (TransitivePermutationLattice
              (permutationOrbitStabilizer ω))) :=
    fun ω =>
      transitivePermutationLatticeHerbrandH0Finite
        (permutationOrbitStabilizer ω) σ hgen
  let orbitHMinusOneFinite :
      ∀ ω : MulAction.orbitRel.Quotient G ι,
        Finite
          (HerbrandHMinusOne G
            (TransitivePermutationLattice
              (permutationOrbitStabilizer ω)) σ) :=
    fun ω =>
      transitivePermutationLatticeHerbrandHMinusOneFinite
        (permutationOrbitStabilizer ω) σ hgen
  let familyH0Finite :
      Finite
        (HerbrandH0 G
          (PermutationLatticeOrbitFamily
            (fun ω : MulAction.orbitRel.Quotient G ι =>
              permutationOrbitStabilizer ω))) :=
    Finite.of_equiv
      (∀ ω : MulAction.orbitRel.Quotient G ι,
        HerbrandH0 G
          (TransitivePermutationLattice
            (permutationOrbitStabilizer ω)))
      (herbrandH0PiEquiv
        (G := G)
        (fun ω : MulAction.orbitRel.Quotient G ι =>
          TransitivePermutationLattice
            (permutationOrbitStabilizer ω))).symm.toEquiv
  let familyHMinusOneFinite :
      Finite
        (HerbrandHMinusOne G
          (PermutationLatticeOrbitFamily
            (fun ω : MulAction.orbitRel.Quotient G ι =>
              permutationOrbitStabilizer ω)) σ) :=
    Finite.of_equiv
      (∀ ω : MulAction.orbitRel.Quotient G ι,
        HerbrandHMinusOne G
          (TransitivePermutationLattice
            (permutationOrbitStabilizer ω)) σ)
      (herbrandHMinusOnePiEquiv
        (G := G)
        (fun ω : MulAction.orbitRel.Quotient G ι =>
          TransitivePermutationLattice
            (permutationOrbitStabilizer ω)) σ).symm.toEquiv
  let functionH0Finite :
      Finite
        (HerbrandH0 G
          (ι → Multiplicative ℤ)) :=
    permutationFunctionHerbrandH0Finite σ hgen
  let functionHMinusOneFinite :
      Finite
        (HerbrandHMinusOne G
          (ι → Multiplicative ℤ) σ) :=
    permutationFunctionHerbrandHMinusOneFinite σ hgen
  let e :=
    permutationFunctionOrbitEquiv
      (G := G) (ι := ι)
  let he :=
    permutationFunctionOrbitEquiv_equivariant
      (G := G) (ι := ι)
  calc
    herbrandQuotient
        (G := G) (A := ι → Multiplicative ℤ) σ =
        herbrandQuotient
          (G := G)
          (A := PermutationLatticeOrbitFamily
            (fun ω : MulAction.orbitRel.Quotient G ι =>
              permutationOrbitStabilizer ω)) σ := by
      simpa only [e, he] using
        (herbrandQuotient_eq_of_equivariantMulEquiv
          e he σ)
    _ = ∏ ω : MulAction.orbitRel.Quotient G ι,
          (Fintype.card
            (permutationOrbitStabilizer ω) : ℚ) :=
      permutationLattice_herbrandQuotient_eq_stabilizerProduct
        (fun ω : MulAction.orbitRel.Quotient G ι =>
          permutationOrbitStabilizer ω) σ hgen

end CanonicalPermutationFunctions

section FiniteIndexStableSubgroupFiniteness

variable {G A : Type}
    [Group G] [CommGroup A]
    [MulDistribMulAction G A]

variable [Fintype G]

/-- Finite-index invariance for permutation lattices: passing from a cyclic
`G`-module to a stable subgroup with finite quotient does not change the
Herbrand quotient. -/
theorem herbrandQuotient_eq_of_finiteIndex_stableSubgroup
    (B : Subgroup A)
    (hstable : ∀ (g : G) (x : A),
      x ∈ B → g • x ∈ B)
    (σ : G)
    (hgen : ∀ g : G,
      g ∈ Subgroup.zpowers σ)
    (hB :
      letI :=
        stableSubgroupMulDistribMulAction
          B hstable
      HerbrandQuotientDefined G B σ)
    [Finite (A ⧸ B)] :
    letI _subgroupAction :=
      stableSubgroupMulDistribMulAction
        B hstable
    letI _quotientAction :=
      stableQuotientMulDistribMulAction
        B hstable
    let hA :=
      finiteIndexStableSubgroup_ambientHerbrandQuotientDefined
        B hstable σ hgen hB
    @herbrandQuotient G A _ _ _ _
        σ hA.1 hA.2 =
      @herbrandQuotient G B _ _ _ _
        σ hB.1 hB.2 := by
  let subgroupAction :=
    stableSubgroupMulDistribMulAction
      B hstable
  let quotientAction :=
    stableQuotientMulDistribMulAction
      B hstable
  let hQ :
      HerbrandQuotientDefined
        G (A ⧸ B) σ :=
    ⟨inferInstance, inferInstance⟩
  let hA :=
    finiteIndexStableSubgroup_ambientHerbrandQuotientDefined
      B hstable σ hgen hB
  let : Finite
      (HerbrandH0 G B) := hB.1
  let : Finite
      (HerbrandHMinusOne G B σ) := hB.2
  let : Finite
      (HerbrandH0 G A) := hA.1
  let : Finite
      (HerbrandHMinusOne G A σ) := hA.2
  let : Finite
      (HerbrandH0 G (A ⧸ B)) := hQ.1
  let : Finite
      (HerbrandHMinusOne G (A ⧸ B) σ) :=
    hQ.2
  have hmult :
      herbrandQuotient
          (G := G) (A := A) σ =
        herbrandQuotient
            (G := G) (A := B) σ *
          herbrandQuotient
            (G := G) (A := A ⧸ B) σ :=
    herbrandQuotient_multiplicative_of_shortExact
      B.subtype (QuotientGroup.mk' B)
      (stableSubgroup_subtype_equivariant
        B hstable)
      (stableSubgroup_quotientMap_equivariant
        B hstable)
      (stableSubgroup_quotientMap_exact B)
      B.subtype_injective
      (QuotientGroup.mk'_surjective B)
      σ hgen
  have hquotient :
      herbrandQuotient
          (G := G) (A := A ⧸ B) σ = 1 :=
    herbrandQuotient_eq_one_of_finite_module
      (G := G) (A := A ⧸ B) σ hgen
  change
    @herbrandQuotient G A _ _ _ _
        σ hA.1 hA.2 =
      @herbrandQuotient G B _ _ _ _
        σ hB.1 hB.2
  calc
    @herbrandQuotient G A _ _ _ _
          σ hA.1 hA.2 =
        @herbrandQuotient G B _ _ _ _
            σ hB.1 hB.2 *
          @herbrandQuotient G (A ⧸ B)
            _ _ _ _ σ hQ.1 hQ.2 :=
      hmult
    _ = @herbrandQuotient G B _ _ _ _
          σ hB.1 hB.2 := by
      rw [hquotient, mul_one]

end FiniteIndexStableSubgroupFiniteness

end CyclicCohomology
end
end

section
-- module Solutions.OAIQ244_DUKE.Cyclic_Herbrand_Permutation_LatticeHerbrand
attribute [-instance] _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instCommGroupSubtypeUnitsMemSubgroup _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.finite_nsmulAddKernel_padicInt_pi _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerKernel _root_.LocalFieldTheory.finite_nsmulAddKernel_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Herbrand quotients of complete permutation sublattices

This file connects the complete permutation sublattice with its
orbit-stabilizer Herbrand quotient calculation.
-/

open scoped BigOperators

noncomputable section

namespace CyclicCohomology

open Module Submodule
open CyclicCohomology.ProfiniteCohomology.Herbrand

universe uG uι

variable {G : Type uG} {ι : Type uι}

section StableSublattice

variable [Fintype G] [Group G] [Fintype ι] [DecidableEq ι]

/-- Degree-zero Tate cohomology of the canonical complete permutation
sublattice is finite. -/
theorem permutationSublatticeHerbrandH0Finite
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L)
    (σ : G)
    (hgen : ∀ g : G,
      g ∈ Subgroup.zpowers σ) :
    letI _indexAction : MulAction G ι :=
      permutationMulAction ρ
    letI _sublatticeAction :
        DistribMulAction G
          (permutationSublattice ρ L hL) :=
      permutationSublatticeDistribMulAction ρ L hL
    letI _multiplicativeAction :
        MulDistribMulAction G
          (Multiplicative
            (permutationSublattice ρ L hL)) :=
      multiplicativeDistribMulAction
    Finite
      (HerbrandH0 G
        (Multiplicative
          (permutationSublattice ρ L hL))) := by
  let indexAction : MulAction G ι :=
    permutationMulAction ρ
  let sublatticeAction :
      DistribMulAction G
        (permutationSublattice ρ L hL) :=
    permutationSublatticeDistribMulAction ρ L hL
  let multiplicativeAction :
      MulDistribMulAction G
        (Multiplicative
          (permutationSublattice ρ L hL)) :=
    multiplicativeDistribMulAction
  let functionAction :
      MulDistribMulAction G
        (ι → Multiplicative ℤ) :=
    permutationFunctionMulDistribMulAction
  let functionH0Finite :
      Finite
        (HerbrandH0 G
          (ι → Multiplicative ℤ)) :=
    permutationFunctionHerbrandH0Finite σ hgen
  let e :=
    permutationSublatticeBasisMulEquivFunctions
      ρ L hL
  let he :=
    permutationSublatticeBasisMulEquivFunctions_equivariant
      ρ L hL
  exact
    herbrandH0Finite_of_equivariantMulEquiv
      e.symm (mulEquiv_symm_commutes_smul e he)

/-- Degree-minus-one Tate cohomology of the canonical complete
permutation sublattice is finite. -/
theorem permutationSublatticeHerbrandHMinusOneFinite
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L)
    (σ : G)
    (hgen : ∀ g : G,
      g ∈ Subgroup.zpowers σ) :
    letI _indexAction : MulAction G ι :=
      permutationMulAction ρ
    letI _sublatticeAction :
        DistribMulAction G
          (permutationSublattice ρ L hL) :=
      permutationSublatticeDistribMulAction ρ L hL
    letI _multiplicativeAction :
        MulDistribMulAction G
          (Multiplicative
            (permutationSublattice ρ L hL)) :=
      multiplicativeDistribMulAction
    Finite
      (HerbrandHMinusOne G
        (Multiplicative
          (permutationSublattice ρ L hL)) σ) := by
  let indexAction : MulAction G ι :=
    permutationMulAction ρ
  let sublatticeAction :
      DistribMulAction G
        (permutationSublattice ρ L hL) :=
    permutationSublatticeDistribMulAction ρ L hL
  let multiplicativeAction :
      MulDistribMulAction G
        (Multiplicative
          (permutationSublattice ρ L hL)) :=
    multiplicativeDistribMulAction
  let functionAction :
      MulDistribMulAction G
        (ι → Multiplicative ℤ) :=
    permutationFunctionMulDistribMulAction
  let functionHMinusOneFinite :
      Finite
        (HerbrandHMinusOne G
          (ι → Multiplicative ℤ) σ) :=
    permutationFunctionHerbrandHMinusOneFinite σ hgen
  let e :=
    permutationSublatticeBasisMulEquivFunctions
      ρ L hL
  let he :=
    permutationSublatticeBasisMulEquivFunctions_equivariant
      ρ L hL
  exact
    herbrandHMinusOneFinite_of_equivariantMulEquiv
      e.symm (mulEquiv_symm_commutes_smul e he) σ

/-- For the canonical complete permutation sublattice, its Herbrand quotient
is the product of the orders of the
stabilizers of the index orbits. -/
theorem
    permutationSublattice_herbrandQuotient_eq_stabilizerProduct
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L)
    (σ : G)
    (hgen : ∀ g : G,
      g ∈ Subgroup.zpowers σ) :
    letI _indexAction : MulAction G ι :=
      permutationMulAction ρ
    letI _sublatticeAction :
        DistribMulAction G
          (permutationSublattice ρ L hL) :=
      permutationSublatticeDistribMulAction ρ L hL
    letI _multiplicativeAction :
        MulDistribMulAction G
          (Multiplicative
            (permutationSublattice ρ L hL)) :=
      multiplicativeDistribMulAction
    letI _orbitFintype :
        Fintype (MulAction.orbitRel.Quotient G ι) :=
      Fintype.ofFinite _
    letI _stabilizerFintype :
        ∀ ω : MulAction.orbitRel.Quotient G ι,
          Fintype (permutationOrbitStabilizer ω) :=
      fun _ => Fintype.ofFinite _
    letI _sublatticeH0Finite :
        Finite
          (HerbrandH0 G
            (Multiplicative
              (permutationSublattice ρ L hL))) :=
      permutationSublatticeHerbrandH0Finite
        ρ L hL σ hgen
    letI _sublatticeHMinusOneFinite :
        Finite
          (HerbrandHMinusOne G
            (Multiplicative
              (permutationSublattice ρ L hL)) σ) :=
      permutationSublatticeHerbrandHMinusOneFinite
        ρ L hL σ hgen
    herbrandQuotient
        (G := G)
        (A := Multiplicative
          (permutationSublattice ρ L hL)) σ =
      ∏ ω : MulAction.orbitRel.Quotient G ι,
        (Fintype.card
          (permutationOrbitStabilizer ω) : ℚ) := by
  let indexAction : MulAction G ι :=
    permutationMulAction ρ
  let sublatticeAction :
      DistribMulAction G
        (permutationSublattice ρ L hL) :=
    permutationSublatticeDistribMulAction ρ L hL
  let multiplicativeAction :
      MulDistribMulAction G
        (Multiplicative
          (permutationSublattice ρ L hL)) :=
    multiplicativeDistribMulAction
  let functionAction :
      MulDistribMulAction G
        (ι → Multiplicative ℤ) :=
    permutationFunctionMulDistribMulAction
  let orbitFintype :
      Fintype (MulAction.orbitRel.Quotient G ι) :=
    Fintype.ofFinite _
  let stabilizerFintype :
      ∀ ω : MulAction.orbitRel.Quotient G ι,
        Fintype (permutationOrbitStabilizer ω) :=
    fun _ => Fintype.ofFinite _
  let sublatticeH0Finite :
      Finite
        (HerbrandH0 G
          (Multiplicative
            (permutationSublattice ρ L hL))) :=
    permutationSublatticeHerbrandH0Finite
      ρ L hL σ hgen
  let sublatticeHMinusOneFinite :
      Finite
        (HerbrandHMinusOne G
          (Multiplicative
            (permutationSublattice ρ L hL)) σ) :=
    permutationSublatticeHerbrandHMinusOneFinite
      ρ L hL σ hgen
  let functionH0Finite :
      Finite
        (HerbrandH0 G
          (ι → Multiplicative ℤ)) :=
    permutationFunctionHerbrandH0Finite σ hgen
  let functionHMinusOneFinite :
      Finite
        (HerbrandHMinusOne G
          (ι → Multiplicative ℤ) σ) :=
    permutationFunctionHerbrandHMinusOneFinite σ hgen
  let e :=
    permutationSublatticeBasisMulEquivFunctions
      ρ L hL
  let he :=
    permutationSublatticeBasisMulEquivFunctions_equivariant
      ρ L hL
  calc
    herbrandQuotient
        (G := G)
        (A := Multiplicative
          (permutationSublattice ρ L hL)) σ =
        herbrandQuotient
          (G := G) (A := ι → Multiplicative ℤ) σ := by
      simpa only [e, he] using
        (herbrandQuotient_eq_of_equivariantMulEquiv
          e he σ)
    _ = ∏ ω : MulAction.orbitRel.Quotient G ι,
          (Fintype.card
            (permutationOrbitStabilizer ω) : ℚ) :=
      permutationFunction_herbrandQuotient_eq_stabilizerProduct
        σ hgen

/-- For an arbitrary complete stable lattice, passing to the canonical
finite-index permutation sublattice computes
the ambient Herbrand quotient as the product of orbit-stabilizer
orders. -/
theorem
    completePermutationLattice_herbrandQuotient_eq_stabilizerProduct
    {G ι : Type}
    [Fintype G] [Group G] [Fintype ι] [DecidableEq ι]
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L)
    (σ : G)
    (hgen : ∀ g : G,
      g ∈ Subgroup.zpowers σ) :
    letI _indexAction : MulAction G ι :=
      permutationMulAction ρ
    letI _ambientAction :
        DistribMulAction G L :=
      completePermutationLatticeDistribMulAction
        ρ L hL
    letI _ambientMultiplicativeAction :
        MulDistribMulAction G
          (Multiplicative L) :=
      multiplicativeDistribMulAction
    letI _orbitFintype :
        Fintype (MulAction.orbitRel.Quotient G ι) :=
      Fintype.ofFinite _
    letI _stabilizerFintype :
        ∀ ω : MulAction.orbitRel.Quotient G ι,
          Fintype (permutationOrbitStabilizer ω) :=
      fun _ => Fintype.ofFinite _
    ∃ h :
        HerbrandQuotientDefined
          G (Multiplicative L) σ,
      @herbrandQuotient
          G (Multiplicative L) _ _ _ _
          σ h.1 h.2 =
        ∏ ω : MulAction.orbitRel.Quotient G ι,
          (Fintype.card
            (permutationOrbitStabilizer ω) : ℚ) := by
  let indexAction : MulAction G ι :=
    permutationMulAction ρ
  let ambientAction :
      DistribMulAction G L :=
    completePermutationLatticeDistribMulAction
      ρ L hL
  let ambientMultiplicativeAction :
      MulDistribMulAction G
        (Multiplicative L) :=
    multiplicativeDistribMulAction
  let orbitFintype :
      Fintype (MulAction.orbitRel.Quotient G ι) :=
    Fintype.ofFinite _
  let stabilizerFintype :
      ∀ ω : MulAction.orbitRel.Quotient G ι,
        Fintype (permutationOrbitStabilizer ω) :=
    fun _ => Fintype.ofFinite _
  let B :=
    permutationSublatticeMultiplicativeSubgroup
      ρ L hL
  have hstable :
      ∀ (g : G) (x : Multiplicative L),
        x ∈ B → g • x ∈ B := by
    simpa only [B] using
      (permutationSublatticeMultiplicativeSubgroup_stable
        ρ L hL)
  let subgroupAction :
      MulDistribMulAction G B :=
    stableSubgroupMulDistribMulAction
      B hstable
  let quotientAction :
      MulDistribMulAction G
        (Multiplicative L ⧸ B) :=
    stableQuotientMulDistribMulAction
      B hstable
  let quotientFinite :
      Finite (Multiplicative L ⧸ B) := by
    simpa only [B] using
      (permutationSublatticeMultiplicativeSubgroup_finite_quotient
        ρ L hL)
  let sublatticeAction :
      DistribMulAction G
        (permutationSublattice ρ L hL) :=
    permutationSublatticeDistribMulAction ρ L hL
  let sublatticeMultiplicativeAction :
      MulDistribMulAction G
        (Multiplicative
          (permutationSublattice ρ L hL)) :=
    multiplicativeDistribMulAction
  let sublatticeH0Finite :
      Finite
        (HerbrandH0 G
          (Multiplicative
            (permutationSublattice ρ L hL))) :=
    permutationSublatticeHerbrandH0Finite
      ρ L hL σ hgen
  let sublatticeHMinusOneFinite :
      Finite
        (HerbrandHMinusOne G
          (Multiplicative
            (permutationSublattice ρ L hL)) σ) :=
    permutationSublatticeHerbrandHMinusOneFinite
      ρ L hL σ hgen
  let e :=
    permutationSublatticeSubgroupMulEquiv
      ρ L hL
  have he :
      ∀ (g : G) (x : B),
        e (g • x) = g • e x := by
    intro g x
    exact
      permutationSublatticeSubgroupMulEquiv_equivariant
        ρ L hL g x
  let subgroupH0Finite :
      Finite (HerbrandH0 G B) :=
    herbrandH0Finite_of_equivariantMulEquiv
      e.symm
      (mulEquiv_symm_commutes_smul e he)
  let subgroupHMinusOneFinite :
      Finite (HerbrandHMinusOne G B σ) :=
    herbrandHMinusOneFinite_of_equivariantMulEquiv
      e.symm
      (mulEquiv_symm_commutes_smul e he) σ
  let hB :
      HerbrandQuotientDefined G B σ :=
    ⟨subgroupH0Finite,
      subgroupHMinusOneFinite⟩
  let hA :
      HerbrandQuotientDefined
        G (Multiplicative L) σ :=
    finiteIndexStableSubgroup_ambientHerbrandQuotientDefined
      B hstable σ hgen hB
  refine ⟨hA, ?_⟩
  let ambientH0Finite :
      Finite
        (HerbrandH0 G
          (Multiplicative L)) :=
    hA.1
  let ambientHMinusOneFinite :
      Finite
        (HerbrandHMinusOne G
          (Multiplicative L) σ) :=
    hA.2
  calc
    @herbrandQuotient
          G (Multiplicative L) _ _ _ _
          σ hA.1 hA.2 =
        @herbrandQuotient
          G B _ _ _ _
          σ hB.1 hB.2 := by
      simpa only [hA] using
        (herbrandQuotient_eq_of_finiteIndex_stableSubgroup
          B hstable σ hgen hB)
    _ =
        herbrandQuotient
          (G := G)
          (A := Multiplicative
            (permutationSublattice ρ L hL)) σ := by
      simpa only [e, he] using
        (herbrandQuotient_eq_of_equivariantMulEquiv
          e he σ)
    _ = ∏ ω : MulAction.orbitRel.Quotient G ι,
          (Fintype.card
            (permutationOrbitStabilizer ω) : ℚ) :=
      permutationSublattice_herbrandQuotient_eq_stabilizerProduct
        ρ L hL σ hgen

end StableSublattice

end CyclicCohomology
end
end

section
-- module Solutions.OAIQ244_DUKE.Cyclic_Herbrand_PrincipalUnits_QuotientReps
attribute [-instance] _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.integerUnitsModPrincipalUnitsConcreteEquiv_mk _root_.LocalFieldTheory.integerUnitsModPrincipalUnitsLift_mk _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.principalUnitsMapOfUnramifiedValuation_apply _root_.LocalFieldTheory.principalUnitsSuccQuotAddEquivResidueOfIrreducible_symm_residue _root_.LocalFieldTheory.principalUnitsSuccQuotMapOfUnramifiedValuation_mk _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false
/-! Provides the public declarations in the `CyclicCohomology.Herbrand.PrincipalUnits.QuotientReps` Lean module. -/

namespace CyclicCohomology

open LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

/-- Every integer-unit quotient class has a representative. -/
theorem integerUnitsModPrincipalUnitsAtLevelMk_surjective
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    Function.Surjective (integerUnitsModPrincipalUnitsAtLevelMk K n) := by
  change Function.Surjective (QuotientGroup.mk' (principalUnits K n))
  exact QuotientGroup.mk'_surjective (principalUnits K n)

/-- Descend a homomorphism that kills `U_K^n`. -/
def integerUnitsModPrincipalUnitsAtLevelLift
    {K : Type u} {M : Type*} [Field K] [ValuativeRel K] [Group M]
    (n : Nat) (f : 𝒪[K]ˣ →* M) (h : principalUnits K n ≤ f.ker) :
    IntegerUnitsModPrincipalUnitsAtLevel K n →* M := by
  change (𝒪[K]ˣ ⧸ principalUnits K n) →* M
  exact QuotientGroup.lift (principalUnits K n) f h

/-- A map lifted from the integer-unit quotient agrees on representatives. -/
@[simp]
theorem integerUnitsModPrincipalUnitsAtLevelLift_mk
    {K : Type u} {M : Type*} [Field K] [ValuativeRel K] [Group M]
    (n : Nat) (f : 𝒪[K]ˣ →* M) (h : principalUnits K n ≤ f.ker)
    (x : 𝒪[K]ˣ) :
    integerUnitsModPrincipalUnitsAtLevelLift n f h
        (integerUnitsModPrincipalUnitsAtLevelMk K n x) = f x :=
  rfl

/-- A unit represents the identity exactly when it lies in the level principal-unit subgroup. -/
theorem integerUnitsModPrincipalUnitsAtLevelMk_eq_one_iff
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) (x : 𝒪[K]ˣ) :
    integerUnitsModPrincipalUnitsAtLevelMk K n x = 1 ↔
      x ∈ principalUnits K n := by
  change (QuotientGroup.mk x : 𝒪[K]ˣ ⧸ principalUnits K n) = 1 ↔ _
  exact QuotientGroup.eq_one_iff x

/-- Two units represent the same class exactly when their quotient is a level principal unit. -/
@[simp]
theorem integerUnitsModPrincipalUnitsAtLevelMk_eq_iff_div_mem
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) (x y : 𝒪[K]ˣ) :
    integerUnitsModPrincipalUnitsAtLevelMk K n x =
        integerUnitsModPrincipalUnitsAtLevelMk K n y ↔
      x / y ∈ principalUnits K n := by
  change
    (QuotientGroup.mk x : 𝒪[K]ˣ ⧸ principalUnits K n) =
      QuotientGroup.mk y ↔ _
  exact QuotientGroup.eq_iff_div_mem

end

end CyclicCohomology
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_FieldNorm
attribute [-instance] _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace LocalFieldTheory

/-!
# Field norm on unit groups

This file connects mathlib's `Algebra.norm` with the unit-group and valued-norm
APIs used by local CFT.
-/

noncomputable section

universe u v w

namespace DiscreteValuationField

variable (K : Type u) (L : Type v)
variable [Field K] [Field L] [Algebra K L]

/--
Establishes the identity `fieldNormUnitsQuotientKerEquivFieldNormSubgroup K L (QuotientGroup.mk'
(MonoidHom.ker (normUnits K L)) z) = (normUnits K L).rangeRestrict z`.
-/
@[simp] theorem fieldNormUnitsQuotientKerEquivFieldNormSubgroup_mk
    (z : Lˣ) :
    fieldNormUnitsQuotientKerEquivFieldNormSubgroup K L
        (QuotientGroup.mk'
          (MonoidHom.ker (normUnits K L)) z) =
      (normUnits K L).rangeRestrict z :=
  rfl

/--
Establishes the identity `((fieldNormUnitsQuotientKerEquivFieldNormSubgroup K L (QuotientGroup.mk'
(MonoidHom.ker (normUnits K L)) z) : fieldNormSubgroup K L) : Kˣ) = normUnits K L z`.
-/
@[simp] theorem coe_fieldNormUnitsQuotientKerEquivFieldNormSubgroup_mk
    (z : Lˣ) :
    ((fieldNormUnitsQuotientKerEquivFieldNormSubgroup K L
        (QuotientGroup.mk'
          (MonoidHom.ker (normUnits K L)) z) :
        fieldNormSubgroup K L) : Kˣ) =
      normUnits K L z :=
  rfl

end DiscreteValuationField

end

end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.Cyclic_Herbrand_PrincipalUnits_QuotientTower
attribute [-instance] _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.finite_nsmulAddKernel_padicInt_pi _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerKernel _root_.LocalFieldTheory.finite_nsmulAddKernel_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_finite_residue _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalClassFieldTheory.galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure_smul _root_.LocalFieldTheory.galoisGroupResidueFieldEquivOfIsIntegralClosure_residue _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.principalUnitsMapOfUnramifiedValuation_apply _root_.LocalFieldTheory.principalUnitsSuccQuotMapOfUnramifiedValuation_mk _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false
/-! Provides the public declarations in the `CyclicCohomology.Herbrand.PrincipalUnits.QuotientTower` Lean module. -/

namespace CyclicCohomology

open LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

/-- The natural projection `𝒪_Kˣ/U_K^m → 𝒪_Kˣ/U_K^n` for `n ≤ m`. -/
def integerUnitsModPrincipalUnitsMapOfLe
    (K : Type u) [Field K] [ValuativeRel K] {n m : Nat} (hnm : n ≤ m) :
    IntegerUnitsModPrincipalUnitsAtLevel K m →*
      IntegerUnitsModPrincipalUnitsAtLevel K n :=
  integerUnitsModPrincipalUnitsAtLevelLift m
    (integerUnitsModPrincipalUnitsAtLevelMk K n)
    (by
      intro x hx
      rw [MonoidHom.mem_ker,
        integerUnitsModPrincipalUnitsAtLevelMk_eq_one_iff]
      exact principalUnits_antitone K hnm hx)

/-- The level-change map sends a unit class to the class of the same unit. -/
@[simp]
theorem integerUnitsModPrincipalUnitsMapOfLe_mk
    (K : Type u) [Field K] [ValuativeRel K] {n m : Nat} (hnm : n ≤ m)
    (x : 𝒪[K]ˣ) :
    integerUnitsModPrincipalUnitsMapOfLe K hnm
        (integerUnitsModPrincipalUnitsAtLevelMk K m x) =
      integerUnitsModPrincipalUnitsAtLevelMk K n x :=
  integerUnitsModPrincipalUnitsAtLevelLift_mk m
    (integerUnitsModPrincipalUnitsAtLevelMk K n) _ x

/-- The successive projection `𝒪_Kˣ/U_K^(n+1) → 𝒪_Kˣ/U_K^n`. -/
def integerUnitsModPrincipalUnitsSuccMap
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    IntegerUnitsModPrincipalUnitsAtLevel K (n + 1) →*
      IntegerUnitsModPrincipalUnitsAtLevel K n :=
  integerUnitsModPrincipalUnitsMapOfLe K (Nat.le_succ n)

/-- The successor-level map sends a unit representative to its successor quotient class. -/
@[simp]
theorem integerUnitsModPrincipalUnitsSuccMap_mk
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat)
    (x : 𝒪[K]ˣ) :
    integerUnitsModPrincipalUnitsSuccMap K n
        (integerUnitsModPrincipalUnitsAtLevelMk K (n + 1) x) =
      integerUnitsModPrincipalUnitsAtLevelMk K n x :=
  integerUnitsModPrincipalUnitsMapOfLe_mk K (Nat.le_succ n) x

/-- The induced homomorphism on the finite quotient `𝒪_Kˣ/U_K^n`. -/
def integerUnitsModPrincipalUnitsMapOfIntegerRingEquiv
    (K : Type u) [Field K] [ValuativeRel K]
    (n : Nat) (e : 𝒪[K] ≃+* 𝒪[K]) :
    IntegerUnitsModPrincipalUnitsAtLevel K n →*
      IntegerUnitsModPrincipalUnitsAtLevel K n :=
  integerUnitsModPrincipalUnitsAtLevelLift n
    ((integerUnitsModPrincipalUnitsAtLevelMk K n).comp
      (Units.mapEquiv e.toMulEquiv).toMonoidHom)
    (by
      intro u hu
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply,
        integerUnitsModPrincipalUnitsAtLevelMk_eq_one_iff]
      exact principalUnits_integerRingEquiv_mem_self K n e u hu)

/-- An integer-ring equivalence maps a unit quotient class via its representative. -/
@[simp]
theorem integerUnitsModPrincipalUnitsMapOfIntegerRingEquiv_mk
    (K : Type u) [Field K] [ValuativeRel K]
    (n : Nat) (e : 𝒪[K] ≃+* 𝒪[K]) (u : 𝒪[K]ˣ) :
    integerUnitsModPrincipalUnitsMapOfIntegerRingEquiv K n e
        (integerUnitsModPrincipalUnitsAtLevelMk K n u) =
      integerUnitsModPrincipalUnitsAtLevelMk K n
        (Units.mapEquiv e.toMulEquiv u) :=
  integerUnitsModPrincipalUnitsAtLevelLift_mk n
    ((integerUnitsModPrincipalUnitsAtLevelMk K n).comp
      (Units.mapEquiv e.toMulEquiv).toMonoidHom) _ u

/-- A valuation-integer-ring equivalence descends to the finite quotient
`𝒪_Kˣ/U_K^n`. -/
def integerUnitsModPrincipalUnitsMapEquivOfIntegerRingEquiv
    (K : Type u) [Field K] [ValuativeRel K]
    (n : Nat) (e : 𝒪[K] ≃+* 𝒪[K]) :
    IntegerUnitsModPrincipalUnitsAtLevel K n ≃*
      IntegerUnitsModPrincipalUnitsAtLevel K n where
  toFun := integerUnitsModPrincipalUnitsMapOfIntegerRingEquiv K n e
  invFun := integerUnitsModPrincipalUnitsMapOfIntegerRingEquiv K n e.symm
  left_inv := by
    intro x
    refine IntegerUnitsModPrincipalUnitsAtLevel.inductionOn n
      (motive := fun x =>
        integerUnitsModPrincipalUnitsMapOfIntegerRingEquiv K n e.symm
            (integerUnitsModPrincipalUnitsMapOfIntegerRingEquiv K n e x) = x)
      x ?_
    intro u
    rw [integerUnitsModPrincipalUnitsMapOfIntegerRingEquiv_mk,
      integerUnitsModPrincipalUnitsMapOfIntegerRingEquiv_mk]
    have h :
        Units.mapEquiv e.symm.toMulEquiv (Units.mapEquiv e.toMulEquiv u) = u := by
      ext
      simp
    exact congrArg
      (integerUnitsModPrincipalUnitsAtLevelMk K n) h
  right_inv := by
    intro x
    refine IntegerUnitsModPrincipalUnitsAtLevel.inductionOn n
      (motive := fun x =>
        integerUnitsModPrincipalUnitsMapOfIntegerRingEquiv K n e
            (integerUnitsModPrincipalUnitsMapOfIntegerRingEquiv K n e.symm x) = x)
      x ?_
    intro u
    rw [integerUnitsModPrincipalUnitsMapOfIntegerRingEquiv_mk,
      integerUnitsModPrincipalUnitsMapOfIntegerRingEquiv_mk]
    have h :
        Units.mapEquiv e.toMulEquiv (Units.mapEquiv e.symm.toMulEquiv u) = u := by
      ext
      simp
    exact congrArg
      (integerUnitsModPrincipalUnitsAtLevelMk K n) h
  map_mul' := by
    intro x y
    exact map_mul (integerUnitsModPrincipalUnitsMapOfIntegerRingEquiv K n e) x y

/-- The induced quotient equivalence acts on a class through its unit representative. -/
@[simp]
theorem integerUnitsModPrincipalUnitsMapEquivOfIntegerRingEquiv_mk
    (K : Type u) [Field K] [ValuativeRel K]
    (n : Nat) (e : 𝒪[K] ≃+* 𝒪[K]) (u : 𝒪[K]ˣ) :
    integerUnitsModPrincipalUnitsMapEquivOfIntegerRingEquiv K n e
        (integerUnitsModPrincipalUnitsAtLevelMk K n u) =
      integerUnitsModPrincipalUnitsAtLevelMk K n
        (Units.mapEquiv e.toMulEquiv u) :=
  integerUnitsModPrincipalUnitsMapOfIntegerRingEquiv_mk K n e u

/-- The graded quotient `U_K^n/U_K^(n+1)` as the kernel source inside
`𝒪_Kˣ/U_K^(n+1)`. -/
def principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    PrincipalUnitsSuccQuot K n →*
      IntegerUnitsModPrincipalUnitsAtLevel K (n + 1) :=
  principalUnitsSuccQuotLift n
    ((integerUnitsModPrincipalUnitsAtLevelMk K (n + 1)).comp
      (principalUnits K n).subtype)
    (by
      intro u hu
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply,
        integerUnitsModPrincipalUnitsAtLevelMk_eq_one_iff]
      exact hu)

/-- The principal-unit quotient map sends a representative to its integer-unit class. -/
@[simp]
theorem principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc_mk
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat)
    (u : principalUnits K n) :
    principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc K n
        (principalUnitsSuccQuotMk K n u) =
      integerUnitsModPrincipalUnitsAtLevelMk K (n + 1) (u : 𝒪[K]ˣ) :=
  principalUnitsSuccQuotLift_mk n
    ((integerUnitsModPrincipalUnitsAtLevelMk K (n + 1)).comp
      (principalUnits K n).subtype) _ u

/-- The principal-unit inclusion followed by the successor map is the canonical quotient map. -/
theorem integerUnitsSuccMap_comp_principalUnitsSuccQuot
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    (integerUnitsModPrincipalUnitsSuccMap K n).comp
        (principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc K n) = 1 := by
  ext q
  refine PrincipalUnitsSuccQuot.inductionOn n
    (motive := fun q =>
      ((integerUnitsModPrincipalUnitsSuccMap K n).comp
        (principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc K n)) q =
          (1 : PrincipalUnitsSuccQuot K n →*
            IntegerUnitsModPrincipalUnitsAtLevel K n) q)
    q ?_
  intro u
  rw [MonoidHom.comp_apply,
    principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc_mk,
    integerUnitsModPrincipalUnitsSuccMap_mk]
  change integerUnitsModPrincipalUnitsAtLevelMk K n (u : 𝒪[K]ˣ) = 1
  rw [integerUnitsModPrincipalUnitsAtLevelMk_eq_one_iff]
  exact u.2

/-- Exactness of `U_K^n/U_K^(n+1) → 𝒪_Kˣ/U_K^(n+1) → 𝒪_Kˣ/U_K^n`
at the middle finite-filtration quotient. -/
theorem principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc_range_eq_ker
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    MonoidHom.range (principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc K n) =
      MonoidHom.ker (integerUnitsModPrincipalUnitsSuccMap K n) := by
  ext q
  constructor
  · rintro ⟨x, rfl⟩
    change (integerUnitsModPrincipalUnitsSuccMap K n).comp
        (principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc K n) x = 1
    rw [integerUnitsSuccMap_comp_principalUnitsSuccQuot]
    rfl
  · intro hq
    revert hq
    refine IntegerUnitsModPrincipalUnitsAtLevel.inductionOn (n + 1)
      (motive := fun q =>
        q ∈ MonoidHom.ker (integerUnitsModPrincipalUnitsSuccMap K n) →
          q ∈ MonoidHom.range
            (principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc K n))
      q ?_
    intro x hq
    have hx : x ∈ principalUnits K n := by
      exact (integerUnitsModPrincipalUnitsAtLevelMk_eq_one_iff K n x).1
        (by simpa using hq)
    let u : principalUnits K n := ⟨x, hx⟩
    exact ⟨principalUnitsSuccQuotMk K n u, by
      rw [principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc_mk]⟩

/-- Integral-closure Galois action on the finite quotient
`𝒪_Lˣ/U_L^n`. -/
def galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (n : Nat) (σ : Gal(L / K)) :
    IntegerUnitsModPrincipalUnitsAtLevel L n ≃*
      IntegerUnitsModPrincipalUnitsAtLevel L n :=
  integerUnitsModPrincipalUnitsMapEquivOfIntegerRingEquiv L n
    (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ)

/-- The Galois-induced quotient equivalence acts on a class through its representative. -/
@[simp]
theorem galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure_mk
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (n : Nat) (σ : Gal(L / K)) (u : 𝒪[L]ˣ) :
    galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure K L n σ
        (integerUnitsModPrincipalUnitsAtLevelMk L n u) =
      integerUnitsModPrincipalUnitsAtLevelMk L n
        (Units.mapEquiv
          (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ).toMulEquiv u) :=
  integerUnitsModPrincipalUnitsMapEquivOfIntegerRingEquiv_mk L n
    (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ) u

/-- Integral-closure Galois action on finite principal-unit
quotients as a group homomorphism. -/
def galoisGroupIntegerUnitsModPrincipalUnitsMapEquivHomOfIsIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (n : Nat) :
    Gal(L / K) →*
      (IntegerUnitsModPrincipalUnitsAtLevel L n ≃*
        IntegerUnitsModPrincipalUnitsAtLevel L n) where
  toFun := galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure K L n
  map_one' := by
    ext x
    refine IntegerUnitsModPrincipalUnitsAtLevel.inductionOn n
      (motive := fun x =>
        galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure
            K L n 1 x = x)
      x ?_
    intro u
    rw [galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure_mk]
    congr 1
  map_mul' := by
    intro σ τ
    ext x
    refine IntegerUnitsModPrincipalUnitsAtLevel.inductionOn n
      (motive := fun x =>
        galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure
            K L n (σ * τ) x =
          (galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure
              K L n σ *
            galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure
              K L n τ) x)
      x ?_
    intro u
    rw [galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure_mk]
    change
      integerUnitsModPrincipalUnitsAtLevelMk L n
          (Units.mapEquiv
            (galoisGroupIntegerRingEquivOfIsIntegralClosure K L (σ * τ)).toMulEquiv u) =
        galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure K L n σ
          (galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure K L n τ
            (integerUnitsModPrincipalUnitsAtLevelMk L n u))
    rw [
      galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure_mk,
      galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure_mk]
    congr 1

/-- Integral-closure Galois action on finite principal-unit
quotients, packaged for low-degree Herbrand quotients. -/
@[implicit_reducible]
def galoisGroupIntegerUnitsModPrincipalUnitsMulDistribMulActionOfIsIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (n : Nat) :
    MulDistribMulAction (Gal(L / K)) (IntegerUnitsModPrincipalUnitsAtLevel L n) where
  smul σ x := galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure K L n σ x
  one_smul := by
    intro x
    change galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure K L n 1 x = x
    have h := congrArg (fun e : IntegerUnitsModPrincipalUnitsAtLevel L n ≃*
        IntegerUnitsModPrincipalUnitsAtLevel L n => e x)
      (map_one (galoisGroupIntegerUnitsModPrincipalUnitsMapEquivHomOfIsIntegralClosure K L n))
    exact h
  mul_smul := by
    intro σ τ x
    change galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure K L n
        (σ * τ) x =
      galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure K L n σ
        (galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure K L n τ x)
    have h := congrArg (fun e : IntegerUnitsModPrincipalUnitsAtLevel L n ≃*
        IntegerUnitsModPrincipalUnitsAtLevel L n => e x)
      (map_mul (galoisGroupIntegerUnitsModPrincipalUnitsMapEquivHomOfIsIntegralClosure K L n)
        σ τ)
    exact h
  smul_mul := by
    intro σ x y
    exact map_mul (galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure
      K L n σ) x y
  smul_one := by
    intro σ
    exact map_one (galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure K L n σ)

/-- The Galois action on integer units modulo principal units is induced on representatives. -/
theorem galoisGroupIntegerUnitsModPrincipalUnitsMulDistribMulActionOfIsIntegralClosure_smul
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (n : Nat) (σ : Gal(L / K)) (x : IntegerUnitsModPrincipalUnitsAtLevel L n) :
    letI := galoisGroupIntegerUnitsModPrincipalUnitsMulDistribMulActionOfIsIntegralClosure
      K L n
    σ • x = galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure K L n σ x :=
  rfl

/-- The quotient `𝒪_Kˣ/U_K^0` is finite because `U_K^0 = 𝒪_Kˣ`. -/
theorem integerUnitsModPrincipalUnitsAtLevel_finite_zero
    (K : Type u) [Field K] [ValuativeRel K] :
    Finite (IntegerUnitsModPrincipalUnitsAtLevel K 0) := by
  let : Finite (𝒪[K]ˣ ⧸ principalUnits K 0) := by
    rw [principalUnits_zero]
    infer_instance
  exact Finite.of_equiv (𝒪[K]ˣ ⧸ principalUnits K 0)
    (integerUnitsModPrincipalUnitsAtLevelConcreteEquiv K 0).symm.toEquiv

/-- The initial nontrivial quotient `𝒪_Kˣ/U_K^1` is finite via
`𝒪_Kˣ/U_K^1 ≃ 𝓀_Kˣ`. -/
theorem integerUnitsModPrincipalUnitsAtLevel_finite_one_of_isNonarchimedeanLocalField
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    Finite (IntegerUnitsModPrincipalUnitsAtLevel K 1) := by
  let e : IntegerUnitsModPrincipalUnitsAtLevel K 1 ≃* ResidueUnits K :=
    (integerUnitsModPrincipalUnitsAtLevelConcreteEquiv K 1).trans
      ((integerUnitsModPrincipalUnitsConcreteEquiv K).symm.trans
        (integerUnitsModPrincipalUnitsEquivResidueUnits K))
  exact Finite.of_equiv (ResidueUnits K) e.symm.toEquiv

/-- If the previous finite quotient and the graded quotient are finite, then
the next finite quotient is finite. -/
theorem integerUnitsModPrincipalUnitsAtLevel_finite_succ_of_finite
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat)
    [Finite (PrincipalUnitsSuccQuot K n)]
    [Finite (IntegerUnitsModPrincipalUnitsAtLevel K n)] :
    Finite (IntegerUnitsModPrincipalUnitsAtLevel K (n + 1)) := by
  let i := principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc K n
  have : Finite i.range :=
    Finite.of_surjective
      (fun a : PrincipalUnitsSuccQuot K n => (⟨i a, ⟨a, rfl⟩⟩ : i.range))
      (by
        intro x
        rcases x with ⟨b, ⟨a, ha⟩⟩
        exact ⟨a, Subtype.ext ha⟩)
  let f := integerUnitsModPrincipalUnitsSuccMap K n
  exact (f.finite_iff_finite_ker_range).2 (by
    constructor
    · rw [← principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc_range_eq_ker K n]
      infer_instance
    · infer_instance)

end
end CyclicCohomology
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_FinitePlaceArtin_NormRestriction
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.gLocallyCompact _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.chosenFinitePlaceBaseIsUltrametricDist _root_.chosenFinitePlaceBaseLocallyCompactSpace _root_.chosenFinitePlaceBaseNontriviallyNormedField
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

local instance finitePlaceNormLowerExtensionAlgebra_r1c0c31_1 :
    Algebra K w.1.Completion :=
  AbsoluteValue.extensionCompletionAlgebra
    (K := K) w.1
local instance finitePlaceNormLowerCompletionAlgebra_r1c0c31_1 :
    Algebra Cₙ w.1.Completion :=
  AbsoluteValue.completionAlgebra vKₙ w.1 w.2
local instance finitePlaceNormUpperExtensionAlgebra_r1c0c31_1 :
    Algebra K' w'.1.Completion :=
  AbsoluteValue.extensionCompletionAlgebra
    (K := K') w'.1
local instance finitePlaceNormUpperCompletionAlgebra_r1c0c31_1 :
    Algebra Dₙ w'.1.Completion :=
  AbsoluteValue.completionAlgebra vKₙ' w'.1 w'.2
local instance finitePlaceNormLowerNontriviallyNormedField_r1c0c31_1 :
    NontriviallyNormedField Cₙ :=
  absoluteValueExtension_completionNontriviallyNormedField
    vKₙ (RayClass.adicAbv_isNontrivial v)
local instance finitePlaceNormLowerLocallyCompactSpace_r1c0c31_1 :
    LocallyCompactSpace Cₙ :=
  AbsoluteValue.Completion.locallyCompactSpace
    (finitePlaceCompletionBaseMap_isometry v)
attribute [local instance] GlobalClassFieldTheory.Reciprocity.finitePlaceNormUpperNontriviallyNormedField
attribute [local instance] GlobalClassFieldTheory.Reciprocity.finitePlaceNormUpperLocallyCompactSpace
local instance finitePlaceNormLowerUltrametric_r1c0c31_1 :
    IsUltrametricDist Cₙ :=
  finitePlaceArtinCompletionIsUltrametricDist vKₙ
    (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K v)
local instance finitePlaceNormLowerValued_r1c0c31_1 :
    Valued Cₙ ℝ≥0 :=
  finitePlaceArtinCompletionValued vKₙ
    (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K v)
local instance finitePlaceNormLowerValuationNontrivial_r1c0c31_1 :
    (Valued.v : Valuation Cₙ ℝ≥0).IsNontrivial :=
  (inferInstance :
    (NormedField.valuation (K := Cₙ)).IsNontrivial)
local instance finitePlaceNormLowerValuativeRel_r1c0c31_1 :
    ValuativeRel Cₙ :=
  finitePlaceArtinCompletionValuativeRel vKₙ
    (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K v)
local instance finitePlaceNormLowerValuationCompatible_r1c0c31_1 :
    (Valued.v : Valuation Cₙ ℝ≥0).Compatible :=
  Valuation.Compatible.ofValuation
    (Valued.v : Valuation Cₙ ℝ≥0)
local instance finitePlaceNormLowerValuativeRelNontrivial_r1c0c31_1 :
    ValuativeRel.IsNontrivial Cₙ :=
  (ValuativeRel.isNontrivial_iff_isNontrivial
    (Valued.v : Valuation Cₙ ℝ≥0)).2 inferInstance
local instance finitePlaceNormLowerLocalField_r1c0c31_1 :
    IsNonarchimedeanLocalField Cₙ :=
  finitePlaceArtinCompletionIsNonarchimedeanLocalField vKₙ
    (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K v)
attribute [local instance] GlobalClassFieldTheory.Reciprocity.finitePlaceNormUpperUltrametric
local instance finitePlaceNormUpperValued_r1c0c31_1 :
    Valued Dₙ ℝ≥0 :=
  finitePlaceArtinCompletionValued vKₙ'
    (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K' W)
local instance finitePlaceNormUpperValuationNontrivial_r1c0c31_1 :
    (Valued.v : Valuation Dₙ ℝ≥0).IsNontrivial :=
  (inferInstance :
    (NormedField.valuation (K := Dₙ)).IsNontrivial)
attribute [local instance] GlobalClassFieldTheory.Reciprocity.finitePlaceNormUpperValuativeRel
local instance finitePlaceNormUpperValuationCompatible_r1c0c31_1 :
    (Valued.v : Valuation Dₙ ℝ≥0).Compatible :=
  Valuation.Compatible.ofValuation
    (Valued.v : Valuation Dₙ ℝ≥0)
local instance finitePlaceNormUpperValuativeRelNontrivial_r1c0c31_1 :
    ValuativeRel.IsNontrivial Dₙ :=
  (ValuativeRel.isNontrivial_iff_isNontrivial
    (Valued.v : Valuation Dₙ ℝ≥0)).2 inferInstance
local instance finitePlaceNormUpperLocalField :
    IsNonarchimedeanLocalField Dₙ :=
  finitePlaceArtinCompletionIsNonarchimedeanLocalField vKₙ'
    (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K' W)

end FinitePlaceNormRestrictionInstances

end Reciprocity
end GlobalClassFieldTheory
end
end


