-- Prove2me | Definitions.Def_OAIQ244Duke025
-- name    : OAIQ244Duke025
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T06:28:32.285391+00:00
-- url     : https://prove2.me/theorems/d45a6bcc-27d5-491f-814c-f88b526b8b7e
-- title:
--   Definitions bundle OAIQ244Duke025 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 98 declarations of OpenAI's Lean: 39 definitions, 1 inductive type or structure, 1 instance and 57 theorems. The definitions and types are `AbsoluteValueSplitsCompletelyInExtension`, `AlgebraicNumberTheory.Valuations.henselFactorization_chosenNextPrefixState_of_mem_span`, `AlgebraicNumberTheory.Valuations.henselFactorization_infinitePCorr_of_mem_span`, `AlgebraicNumberTheory.Valuations.henselFactorization_infiniteQCorr_of_mem_span`, `AlgebraicNumberTheory.Valuations.henselFactorization_prefixStateSeq_of_mem_span`, `HilbertRamification.decompositionField_completionImageSubfield`, `HilbertRamification.decompositionField_decompositionFieldValuationSubring`, `HilbertRamification.decompositionField_decompositionField_integerMap`, `HilbertRamification.decompositionField_decompositionField_residueFieldEquiv`, `HilbertRamification.decompositionField_decompositionField_residueMap`, `HilbertRamification.decompositionField_toLocalizationAlgHom`, `HilbertRamification.localization`, `HilbertRamification.proposition98CompletionAlgebra`, `HilbertRamification.proposition98LocalizationBaseAlgebra`, `HilbertRamification.toLocalization`, `LocalClassFieldTheory.LocalBlockFamily`, `LocalClassFieldTheory.LocalPlaceBlock`, `LocalClassFieldTheory.LocalPlaceDatum`, `LocalClassFieldTheory.completionProductReindexRightCosets`, `LocalClassFieldTheory.completionProductUnitsEquivRightCosets`, `LocalClassFieldTheory.conjugateExtensionCompletionRingEquiv`, `LocalClassFieldTheory.decompositionGroupLocalUnitsAction`, `LocalClassFieldTheory.decompositionRightCosetsFinset`, `LocalClassFieldTheory.localBlockFamilyBlockAction`, `LocalClassFieldTheory.localBlockFamilyCohomologyAction`, `LocalClassFieldTheory.localBlockFamilyDecompositionFintype`, `LocalClassFieldTheory.localBlockFamilyLocalAction`, `LocalClassFieldTheory.localTensorEvaluation`, `LocalClassFieldTheory.localizedCompletionBaseAlgebra`, `LocalClassFieldTheory.localizedCompletionDecompositionGroupFintype`, `LocalClassFieldTheory.localizedCompletionGlobalAlgebra`, `LocalClassFieldTheory.rightCosetCompletionUnitsEquiv`, `LocalClassFieldTheory.rightCosetExtension`, `LocalClassFieldTheory.rightCosetExtensionEquiv`, `absoluteValueCompletionIntegers`, `chosenFinitePlaceExtension`, `doubleCosetExtension`, `extendAbsoluteValueExtensionFromIntermediate`, `finitePlaceDecompositionGroup`, `restrictAbsoluteValueExtensionToIntermediate`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `AlgebraicNumberTheory_Adele_IntegralTensorSupport_AbsoluteValue`, `AlgebraicNumberTheory_Galois_CyclicPrimeSubextension`, `AlgebraicNumberTheory_Idele_NormApproximation_FinitePlaces`, `AlgebraicNumberTheory_Ramification_Splitting_FinitePlace`, `AlgebraicNumberTheory_Ramification_Splitting_NormalClosure`, `LocalClassFieldTheory_ClassFormation_LocalBlocks_Family_Instances`, `LocalClassFieldTheory_ClassFormation_LocalBlocks_Induced`, `LocalClassFieldTheory_ClassFormation_LocalBlocks_Tensor`, `LocalClassFieldTheory_ClassFormation_LocalBlocks_TensorNorm`, `LocalClassFieldTheory_ClassFormation_LocalizedCompletionCohomology_Algebra`, `LocalClassFieldTheory_ClassFormation_LocalizedCompletionCohomology_Generator`, `Ramification_HilbertRamification_AbsoluteValueConjugacy`, `Ramification_HilbertRamification_AlgebraicLocalization`, `Ramification_HilbertRamification_DecompositionFieldLocalization`, `Valuation_Completion_DegreeNormTrace`, `Valuation_Henselian_Complete`, `Valuation_Henselian_Factorization_Assembly`, `Valuation_Henselian_Factorization_Complete`, `Valuation_Henselian_Factorization_FiniteApproximation`, `Valuation_Henselian_Factorization_InfiniteApproximation`, `Valuation_Henselian_Factorization_PrincipalLimits`, `Valuation_Henselian_Factorization_Step`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke014` and `OAIQ244Duke015` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke037`, `OAIQ244Duke038`, `OAIQ244Duke039`, `OAIQ244Duke040`, `OAIQ244Duke042` and `OAIQ244Duke043`.
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
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Module.LinearMap.Polynomial
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
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.LinearAlgebra.Quotient.Pi
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
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
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
import Definitions.Def_OAIQ244Duke014
import Definitions.Def_OAIQ244Duke015

section
-- module Solutions.OAIQ244_DUKE.Valuation_Henselian_Factorization_Step
attribute [-instance] _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# one Hensel iteration step

This file packages the algebraic correction, degree truncation, and `π`-power
update into the single step used recursively in the proof of Hensel's
lemma.
-/

noncomputable section

open scoped Polynomial

namespace AlgebraicNumberTheory
namespace Valuations

/-- displayed-factor one-step existence with the degree
invariants for the next approximants included. -/
theorem henselFactorization_exists_one_step_update_with_degree_bounds_of_mem_span
    {R : Type*} [CommRing R] [IsLocalRing R] [NoZeroDivisors R]
    {π : R} {n : ℕ} (hn : 1 ≤ n) (hπn : π ^ n ≠ 0)
    (hπmem : π ∈ IsLocalRing.maximalIdeal R)
    {f g0 h0 g h fn a b e : R[X]}
    {gbar : (IsLocalRing.ResidueField R)[X]} {m d : ℕ}
    (hf : f.natDegree ≤ d)
    (hg : ∀ i : ℕ, (g - g0).coeff i ∈ Ideal.span ({π} : Set R))
    (hh : ∀ i : ℕ, (h - h0).coeff i ∈ Ideal.span ({π} : Set R))
    (hgdeg : g.natDegree ≤ m)
    (hhdeg : h.natDegree ≤ d - m)
    (hg0map : g0.map (IsLocalRing.residue R) = gbar)
    (hg0nat : g0.natDegree = m)
    (hgbar_nat : gbar.natDegree = m)
    (hglead : gbar.leadingCoeff ≠ 0)
    (hh0 : h0.natDegree ≤ d - m)
    (hbezFactor : a * g0 + b * h0 - 1 = Polynomial.C π * e)
    (hfactor : f - g * h = Polynomial.C (π ^ n) * fn)
    (hmd : m ≤ d) :
    ∃ p q fnNext : R[X],
      p.natDegree ≤ m ∧ q.natDegree ≤ d - m ∧
        (g + Polynomial.C (π ^ n) * p).natDegree ≤ m ∧
          (h + Polynomial.C (π ^ n) * q).natDegree ≤ d - m ∧
            (∀ i : ℕ,
              (g + Polynomial.C (π ^ n) * p - g0).coeff i ∈
                Ideal.span ({π} : Set R)) ∧
              (∀ i : ℕ,
                (h + Polynomial.C (π ^ n) * q - h0).coeff i ∈
                  Ideal.span ({π} : Set R)) ∧
                (∀ i : ℕ,
                  (g + Polynomial.C (π ^ n) * p - g0).coeff i ∈
                    IsLocalRing.maximalIdeal R) ∧
                  (∀ i : ℕ,
                    (h + Polynomial.C (π ^ n) * q - h0).coeff i ∈
                      IsLocalRing.maximalIdeal R) ∧
                    f - (g + Polynomial.C (π ^ n) * p) *
                        (h + Polynomial.C (π ^ n) * q) =
                      Polynomial.C (π ^ (n + 1)) * fnNext := by
  rcases henselFactorization_exists_one_step_update_of_mem_span
      (π := π) hn hπn hπmem hf hg hh hgdeg hhdeg
      hg0map hg0nat hgbar_nat hglead hh0 hbezFactor hfactor hmd with
    ⟨p, q, fnNext, hpdeg, hqdeg, hgNext, hhNext,
      hgNextMax, hhNextMax, hfactorNext⟩
  have hgNextDeg :
      (g + Polynomial.C (π ^ n) * p).natDegree ≤ m := by
    have hterm : (Polynomial.C (π ^ n) * p).natDegree ≤ m :=
      (Polynomial.natDegree_C_mul_le (π ^ n) p).trans hpdeg
    exact Polynomial.natDegree_add_le_of_degree_le hgdeg hterm
  have hhNextDeg :
      (h + Polynomial.C (π ^ n) * q).natDegree ≤ d - m := by
    have hterm : (Polynomial.C (π ^ n) * q).natDegree ≤ d - m :=
      (Polynomial.natDegree_C_mul_le (π ^ n) q).trans hqdeg
    exact Polynomial.natDegree_add_le_of_degree_le hhdeg hterm
  exact ⟨p, q, fnNext, hpdeg, hqdeg, hgNextDeg, hhNextDeg,
    hgNext, hhNext, hgNextMax, hhNextMax, hfactorNext⟩


end Valuations
end AlgebraicNumberTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_Henselian_Factorization_FiniteApproximation
attribute [-instance] _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# finite Hensel prefixes

This file isolates the reusable one-step extension in the finite
Hensel construction.  Compatible prefixes themselves are assembled once, as
HenselFactorizationFinitePrefixState, in the next layer.
-/

noncomputable section

open scoped Polynomial

namespace AlgebraicNumberTheory
namespace Valuations

/-- extend a finite Hensel prefix by one step in the
displayed-factor principal-element form.  The current iterates are automatically
congruent to the initial lifts modulo `(π)`, so the extension uses only
`π ∈ m` and the displayed Bezout-error factor. -/
theorem henselFactorization_extend_finite_prefix_one_step_of_mem_span
    {R : Type*} [CommRing R] [IsLocalRing R] [NoZeroDivisors R]
    {π : R} (hπne : π ≠ 0)
    (hπmem : π ∈ IsLocalRing.maximalIdeal R)
    {f g0 h0 a b e : R[X]}
    {gbar : (IsLocalRing.ResidueField R)[X]} {m d n : ℕ}
    (hf : f.natDegree ≤ d)
    (hg0map : g0.map (IsLocalRing.residue R) = gbar)
    (hg0nat : g0.natDegree = m)
    (hgbar_nat : gbar.natDegree = m)
    (hglead : gbar.leadingCoeff ≠ 0)
    (hh0 : h0.natDegree ≤ d - m)
    (hbezFactor : a * g0 + b * h0 - 1 = Polynomial.C π * e)
    (hmd : m ≤ d)
    (pCorr qCorr : ℕ → R[X])
    (hprefix :
      ∀ r : ℕ, r ≤ n →
        ∃ fr : R[X],
          f - henselFactorization_henselIterate π g0 pCorr r *
              henselFactorization_henselIterate π h0 qCorr r =
            Polynomial.C (π ^ (r + 1)) * fr)
    {fn : R[X]}
    (hfactor :
      f - henselFactorization_henselIterate π g0 pCorr n *
          henselFactorization_henselIterate π h0 qCorr n =
        Polynomial.C (π ^ (n + 1)) * fn)
    (hgDeg : (henselFactorization_henselIterate π g0 pCorr n).natDegree ≤ m)
    (hhDeg : (henselFactorization_henselIterate π h0 qCorr n).natDegree ≤ d - m) :
    ∃ p q fnNext : R[X],
      p.natDegree ≤ m ∧ q.natDegree ≤ d - m ∧
        (∀ r : ℕ, r ≤ n →
          ∃ fr : R[X],
            f - henselFactorization_henselIterate π g0
                  (Function.update pCorr (n + 1) p) r *
                henselFactorization_henselIterate π h0
                  (Function.update qCorr (n + 1) q) r =
              Polynomial.C (π ^ (r + 1)) * fr) ∧
          f - henselFactorization_henselIterate π g0
                (Function.update pCorr (n + 1) p) (n + 1) *
              henselFactorization_henselIterate π h0
                (Function.update qCorr (n + 1) q) (n + 1) =
            Polynomial.C (π ^ (n + 2)) * fnNext ∧
            (henselFactorization_henselIterate π g0
                (Function.update pCorr (n + 1) p) (n + 1)).natDegree ≤ m ∧
              (henselFactorization_henselIterate π h0
                  (Function.update qCorr (n + 1) q) (n + 1)).natDegree ≤
                d - m ∧
                (∀ i : ℕ,
                  (henselFactorization_henselIterate π g0
                      (Function.update pCorr (n + 1) p) (n + 1) -
                    g0).coeff i ∈ IsLocalRing.maximalIdeal R) ∧
                  (∀ i : ℕ,
                    (henselFactorization_henselIterate π h0
                        (Function.update qCorr (n + 1) q) (n + 1) -
                      h0).coeff i ∈ IsLocalRing.maximalIdeal R) := by
  have hπpow : π ^ (n + 1) ≠ 0 := pow_ne_zero (n + 1) hπne
  have hgSpan :
      ∀ i : ℕ,
        (henselFactorization_henselIterate π g0 pCorr n - g0).coeff i ∈
          Ideal.span ({π} : Set R) :=
    henselFactorization_henselIterate_span_singleton (π := π) g0 pCorr n
  have hhSpan :
      ∀ i : ℕ,
        (henselFactorization_henselIterate π h0 qCorr n - h0).coeff i ∈
          Ideal.span ({π} : Set R) :=
    henselFactorization_henselIterate_span_singleton (π := π) h0 qCorr n
  rcases henselFactorization_exists_one_step_update_with_degree_bounds_of_mem_span
      (π := π) (n := n + 1) (Nat.succ_pos n) hπpow hπmem
      (f := f) (g0 := g0) (h0 := h0)
      (g := henselFactorization_henselIterate π g0 pCorr n)
      (h := henselFactorization_henselIterate π h0 qCorr n)
      (fn := fn) (a := a) (b := b) (e := e)
      (gbar := gbar) (m := m) (d := d)
      hf hgSpan hhSpan hgDeg hhDeg hg0map hg0nat hgbar_nat hglead
      hh0 hbezFactor hfactor hmd with
    ⟨p, q, fnNext, hpDeg, hqDeg, hgNextDeg, hhNextDeg,
      _hgNextSpan, _hhNextSpan, hgNextRed, hhNextRed, hfactorNextRaw⟩
  have hfactorNext :
      f - (henselFactorization_henselIterate π g0 pCorr n +
            Polynomial.C (π ^ (n + 1)) * p) *
          (henselFactorization_henselIterate π h0 qCorr n +
            Polynomial.C (π ^ (n + 1)) * q) =
        Polynomial.C (π ^ (n + 2)) * fnNext := by
    simpa [Nat.add_assoc] using hfactorNextRaw
  refine ⟨p, q, fnNext, hpDeg, hqDeg, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr
    rcases hprefix r hr with ⟨fr, hfr⟩
    exact ⟨fr,
      henselFactorization_henselIterate_update_preserves_factor_of_le
        (π := π) (pCorr := pCorr) (qCorr := qCorr)
        (n := n) (r := r) hr p q fr hfr⟩
  · exact henselFactorization_henselIterate_update_next_factor
      (π := π) (f := f) (g0 := g0) (h0 := h0)
      pCorr qCorr n p q fnNext hfactorNext
  · rw [henselFactorization_henselIterate_update_next
      (π := π) (F0 := g0) (corr := pCorr) (n := n) (c := p)]
    exact hgNextDeg
  · rw [henselFactorization_henselIterate_update_next
      (π := π) (F0 := h0) (corr := qCorr) (n := n) (c := q)]
    exact hhNextDeg
  · intro i
    rw [henselFactorization_henselIterate_update_next
      (π := π) (F0 := g0) (corr := pCorr) (n := n) (c := p)]
    exact hgNextRed i
  · intro i
    rw [henselFactorization_henselIterate_update_next
      (π := π) (F0 := h0) (corr := qCorr) (n := n) (c := q)]
    exact hhNextRed i

end Valuations
end AlgebraicNumberTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_Henselian_Factorization_InfiniteApproximation
attribute [-instance] _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# compatible Hensel prefixes

This file turns the finite Hensel-prefix construction into a recursive family
of compatible prefixes.  The completion/limit argument is kept for the next
layer.
-/

noncomputable section

open scoped Polynomial

namespace AlgebraicNumberTheory
namespace Valuations

/-- Choose an extension of a prefix state by one Hensel correction in the
displayed-factor form. -/
def henselFactorization_chosenNextPrefixState_of_mem_span
    {R : Type*} [CommRing R] [IsLocalRing R] [NoZeroDivisors R]
    {π : R} (hπne : π ≠ 0)
    (hπmem : π ∈ IsLocalRing.maximalIdeal R)
    {f g0 h0 a b e : R[X]}
    {gbar : (IsLocalRing.ResidueField R)[X]} {m d N : ℕ}
    (hf : f.natDegree ≤ d)
    (hg0map : g0.map (IsLocalRing.residue R) = gbar)
    (hg0nat : g0.natDegree = m)
    (hgbar_nat : gbar.natDegree = m)
    (hglead : gbar.leadingCoeff ≠ 0)
    (hh0deg : h0.natDegree ≤ d - m)
    (hbezFactor : a * g0 + b * h0 - 1 = Polynomial.C π * e)
    (hmd : m ≤ d)
    (s : HenselFactorizationFinitePrefixState π f g0 h0 m d N) :
    HenselFactorizationFinitePrefixState π f g0 h0 m d (N + 1) := by
  classical
  let hstep := henselFactorization_extend_finite_prefix_one_step_of_mem_span
      (π := π) hπne hπmem
      (f := f) (g0 := g0) (h0 := h0) (a := a) (b := b) (e := e)
      (gbar := gbar) (m := m) (d := d) (n := N)
      hf hg0map hg0nat hgbar_nat hglead hh0deg hbezFactor hmd
      s.pCorr s.qCorr s.prefixFactor s.factor s.gDeg s.hDeg
  let p := Classical.choose hstep
  have hpstep := Classical.choose_spec hstep
  let q := Classical.choose hpstep
  have hqstep := Classical.choose_spec hpstep
  let fnNext := Classical.choose hqstep
  have hspec := Classical.choose_spec hqstep
  have hpdeg : p.natDegree ≤ m := hspec.1
  have hqdeg : q.natDegree ≤ d - m := hspec.2.1
  have hprefixOld :
      ∀ r : ℕ, r ≤ N →
        ∃ fr : R[X],
          f - henselFactorization_henselIterate π g0
                (Function.update s.pCorr (N + 1) p) r *
              henselFactorization_henselIterate π h0
                (Function.update s.qCorr (N + 1) q) r =
            Polynomial.C (π ^ (r + 1)) * fr := hspec.2.2.1
  have hfactorNext :
      f - henselFactorization_henselIterate π g0
            (Function.update s.pCorr (N + 1) p) (N + 1) *
          henselFactorization_henselIterate π h0
            (Function.update s.qCorr (N + 1) q) (N + 1) =
        Polynomial.C (π ^ (N + 2)) * fnNext := hspec.2.2.2.1
  have hgNextDeg :
      (henselFactorization_henselIterate π g0
        (Function.update s.pCorr (N + 1) p) (N + 1)).natDegree ≤ m :=
    hspec.2.2.2.2.1
  have hhNextDeg :
      (henselFactorization_henselIterate π h0
        (Function.update s.qCorr (N + 1) q) (N + 1)).natDegree ≤ d - m :=
    hspec.2.2.2.2.2.1
  have hgNextRed :
      ∀ i : ℕ,
        (henselFactorization_henselIterate π g0
            (Function.update s.pCorr (N + 1) p) (N + 1) - g0).coeff i ∈
          IsLocalRing.maximalIdeal R :=
    hspec.2.2.2.2.2.2.1
  have hhNextRed :
      ∀ i : ℕ,
        (henselFactorization_henselIterate π h0
            (Function.update s.qCorr (N + 1) q) (N + 1) - h0).coeff i ∈
          IsLocalRing.maximalIdeal R :=
    hspec.2.2.2.2.2.2.2
  refine
    { pCorr := Function.update s.pCorr (N + 1) p
      qCorr := Function.update s.qCorr (N + 1) q
      fErr := fnNext
      prefixFactor := ?_
      pCorrDeg := ?_
      qCorrDeg := ?_
      factor := ?_
      gDeg := hgNextDeg
      hDeg := hhNextDeg
      gRed := hgNextRed
      hRed := hhNextRed }
  · intro r hr
    by_cases htop : r = N + 1
    · subst r
      exact ⟨fnNext, by simpa [Nat.add_assoc] using hfactorNext⟩
    · have hrn : r ≤ N := Nat.lt_succ_iff.mp (lt_of_le_of_ne hr htop)
      exact hprefixOld r hrn
  · exact henselFactorization_update_corr_natDegree_le s.pCorrDeg hpdeg
  · exact henselFactorization_update_corr_natDegree_le s.qCorrDeg hqdeg
  · simpa [Nat.add_assoc] using hfactorNext

/-- in the displayed-factor prefix extension the `p`
correction changes only at the newly constructed index. -/
theorem henselFactorization_chosenNextPrefixState_pCorr_of_ne_of_mem_span
    {R : Type*} [CommRing R] [IsLocalRing R] [NoZeroDivisors R]
    {π : R} (hπne : π ≠ 0)
    (hπmem : π ∈ IsLocalRing.maximalIdeal R)
    {f g0 h0 a b e : R[X]}
    {gbar : (IsLocalRing.ResidueField R)[X]} {m d N r : ℕ}
    (hf : f.natDegree ≤ d)
    (hg0map : g0.map (IsLocalRing.residue R) = gbar)
    (hg0nat : g0.natDegree = m)
    (hgbar_nat : gbar.natDegree = m)
    (hglead : gbar.leadingCoeff ≠ 0)
    (hh0deg : h0.natDegree ≤ d - m)
    (hbezFactor : a * g0 + b * h0 - 1 = Polynomial.C π * e)
    (hmd : m ≤ d)
    (s : HenselFactorizationFinitePrefixState π f g0 h0 m d N)
    (hr : r ≠ N + 1) :
    (henselFactorization_chosenNextPrefixState_of_mem_span
        (π := π) hπne hπmem
        (f := f) (g0 := g0) (h0 := h0) (a := a) (b := b) (e := e)
        (gbar := gbar) (m := m) (d := d) (N := N)
        hf hg0map hg0nat hgbar_nat hglead hh0deg hbezFactor hmd s).pCorr r =
      s.pCorr r := by
  unfold henselFactorization_chosenNextPrefixState_of_mem_span
  simp [Function.update_of_ne hr]

/-- in the displayed-factor prefix extension the `q`
correction changes only at the newly constructed index. -/
theorem henselFactorization_chosenNextPrefixState_qCorr_of_ne_of_mem_span
    {R : Type*} [CommRing R] [IsLocalRing R] [NoZeroDivisors R]
    {π : R} (hπne : π ≠ 0)
    (hπmem : π ∈ IsLocalRing.maximalIdeal R)
    {f g0 h0 a b e : R[X]}
    {gbar : (IsLocalRing.ResidueField R)[X]} {m d N r : ℕ}
    (hf : f.natDegree ≤ d)
    (hg0map : g0.map (IsLocalRing.residue R) = gbar)
    (hg0nat : g0.natDegree = m)
    (hgbar_nat : gbar.natDegree = m)
    (hglead : gbar.leadingCoeff ≠ 0)
    (hh0deg : h0.natDegree ≤ d - m)
    (hbezFactor : a * g0 + b * h0 - 1 = Polynomial.C π * e)
    (hmd : m ≤ d)
    (s : HenselFactorizationFinitePrefixState π f g0 h0 m d N)
    (hr : r ≠ N + 1) :
    (henselFactorization_chosenNextPrefixState_of_mem_span
        (π := π) hπne hπmem
        (f := f) (g0 := g0) (h0 := h0) (a := a) (b := b) (e := e)
        (gbar := gbar) (m := m) (d := d) (N := N)
        hf hg0map hg0nat hgbar_nat hglead hh0deg hbezFactor hmd s).qCorr r =
      s.qCorr r := by
  unfold henselFactorization_chosenNextPrefixState_of_mem_span
  simp [Function.update_of_ne hr]

/-- recursively chosen compatible finite Hensel prefixes in
the displayed-factor displayed-factor form. -/
def henselFactorization_prefixStateSeq_of_mem_span
    {R : Type*} [CommRing R] [IsLocalRing R] [NoZeroDivisors R]
    {π : R} (hπne : π ≠ 0)
    (hπmem : π ∈ IsLocalRing.maximalIdeal R)
    {f g0 h0 a b f1 e : R[X]}
    {gbar : (IsLocalRing.ResidueField R)[X]} {m d : ℕ}
    (hf : f.natDegree ≤ d)
    (hg0map : g0.map (IsLocalRing.residue R) = gbar)
    (hg0nat : g0.natDegree = m)
    (hgbar_nat : gbar.natDegree = m)
    (hglead : gbar.leadingCoeff ≠ 0)
    (hh0deg : h0.natDegree ≤ d - m)
    (hfactor0 : f - g0 * h0 = Polynomial.C π * f1)
    (hbezFactor : a * g0 + b * h0 - 1 = Polynomial.C π * e)
    (hmd : m ≤ d) :
    (N : ℕ) → HenselFactorizationFinitePrefixState π f g0 h0 m d N
  | 0 =>
      henselFactorization_initialPrefixState_of_factor
        (π := π) (f := f) (g0 := g0) (h0 := h0)
        (f1 := f1) (m := m) (d := d)
        hfactor0 hg0nat hh0deg
  | N + 1 =>
      henselFactorization_chosenNextPrefixState_of_mem_span
        (π := π) hπne hπmem
        (f := f) (g0 := g0) (h0 := h0) (a := a) (b := b) (e := e)
        (gbar := gbar) (m := m) (d := d) (N := N)
        hf hg0map hg0nat hgbar_nat hglead hh0deg hbezFactor hmd
        (henselFactorization_prefixStateSeq_of_mem_span
          (π := π) (f := f) (g0 := g0) (h0 := h0)
          (a := a) (b := b) (f1 := f1) (e := e)
          (gbar := gbar) (m := m) (d := d)
          hπne hπmem hf hg0map hg0nat hgbar_nat hglead hh0deg
          hfactor0 hbezFactor hmd N)

/-- coherence of the displayed-factor `p`-corrections:
later prefix states agree with earlier ones at every already constructed
index. -/
theorem henselFactorization_prefixStateSeq_pCorr_eq_of_le_of_mem_span
    {R : Type*} [CommRing R] [IsLocalRing R] [NoZeroDivisors R]
    {π : R} (hπne : π ≠ 0)
    (hπmem : π ∈ IsLocalRing.maximalIdeal R)
    {f g0 h0 a b f1 e : R[X]}
    {gbar : (IsLocalRing.ResidueField R)[X]} {m d : ℕ}
    (hf : f.natDegree ≤ d)
    (hg0map : g0.map (IsLocalRing.residue R) = gbar)
    (hg0nat : g0.natDegree = m)
    (hgbar_nat : gbar.natDegree = m)
    (hglead : gbar.leadingCoeff ≠ 0)
    (hh0deg : h0.natDegree ≤ d - m)
    (hfactor0 : f - g0 * h0 = Polynomial.C π * f1)
    (hbezFactor : a * g0 + b * h0 - 1 = Polynomial.C π * e)
    (hmd : m ≤ d) :
    ∀ {M N : ℕ}, M ≤ N →
      (henselFactorization_prefixStateSeq_of_mem_span
          (π := π) (f := f) (g0 := g0) (h0 := h0)
          (a := a) (b := b) (f1 := f1) (e := e)
          (gbar := gbar) (m := m) (d := d)
          hπne hπmem hf hg0map hg0nat hgbar_nat hglead hh0deg
          hfactor0 hbezFactor hmd N).pCorr M =
        (henselFactorization_prefixStateSeq_of_mem_span
          (π := π) (f := f) (g0 := g0) (h0 := h0)
          (a := a) (b := b) (f1 := f1) (e := e)
          (gbar := gbar) (m := m) (d := d)
          hπne hπmem hf hg0map hg0nat hgbar_nat hglead hh0deg
          hfactor0 hbezFactor hmd M).pCorr M := by
  intro M N hMN
  induction N generalizing M with
  | zero =>
      have hM0 : M = 0 := Nat.eq_zero_of_le_zero hMN
      subst M
      rfl
  | succ N ih =>
      by_cases htop : M = N + 1
      · subst M
        rfl
      · have hMN' : M ≤ N := Nat.lt_succ_iff.mp (lt_of_le_of_ne hMN htop)
        calc
          (henselFactorization_prefixStateSeq_of_mem_span
              (π := π) (f := f) (g0 := g0) (h0 := h0)
              (a := a) (b := b) (f1 := f1) (e := e)
              (gbar := gbar) (m := m) (d := d)
              hπne hπmem hf hg0map hg0nat hgbar_nat hglead hh0deg
              hfactor0 hbezFactor hmd (N + 1)).pCorr M =
            (henselFactorization_prefixStateSeq_of_mem_span
              (π := π) (f := f) (g0 := g0) (h0 := h0)
              (a := a) (b := b) (f1 := f1) (e := e)
              (gbar := gbar) (m := m) (d := d)
              hπne hπmem hf hg0map hg0nat hgbar_nat hglead hh0deg
              hfactor0 hbezFactor hmd N).pCorr M := by
              simpa [henselFactorization_prefixStateSeq_of_mem_span] using
                henselFactorization_chosenNextPrefixState_pCorr_of_ne_of_mem_span
                  (π := π) hπne hπmem
                  (f := f) (g0 := g0) (h0 := h0)
                  (a := a) (b := b) (e := e)
                  (gbar := gbar) (m := m) (d := d) (N := N) (r := M)
                  hf hg0map hg0nat hgbar_nat hglead hh0deg
                  hbezFactor hmd
                  (henselFactorization_prefixStateSeq_of_mem_span
                    (π := π) (f := f) (g0 := g0) (h0 := h0)
                    (a := a) (b := b) (f1 := f1) (e := e)
                    (gbar := gbar) (m := m) (d := d)
                    hπne hπmem hf hg0map hg0nat hgbar_nat hglead hh0deg
                    hfactor0 hbezFactor hmd N)
                  htop
          _ =
            (henselFactorization_prefixStateSeq_of_mem_span
              (π := π) (f := f) (g0 := g0) (h0 := h0)
              (a := a) (b := b) (f1 := f1) (e := e)
              (gbar := gbar) (m := m) (d := d)
              hπne hπmem hf hg0map hg0nat hgbar_nat hglead hh0deg
              hfactor0 hbezFactor hmd M).pCorr M := ih hMN'

/-- coherence of the displayed-factor `q`-corrections:
later prefix states agree with earlier ones at every already constructed
index. -/
theorem henselFactorization_prefixStateSeq_qCorr_eq_of_le_of_mem_span
    {R : Type*} [CommRing R] [IsLocalRing R] [NoZeroDivisors R]
    {π : R} (hπne : π ≠ 0)
    (hπmem : π ∈ IsLocalRing.maximalIdeal R)
    {f g0 h0 a b f1 e : R[X]}
    {gbar : (IsLocalRing.ResidueField R)[X]} {m d : ℕ}
    (hf : f.natDegree ≤ d)
    (hg0map : g0.map (IsLocalRing.residue R) = gbar)
    (hg0nat : g0.natDegree = m)
    (hgbar_nat : gbar.natDegree = m)
    (hglead : gbar.leadingCoeff ≠ 0)
    (hh0deg : h0.natDegree ≤ d - m)
    (hfactor0 : f - g0 * h0 = Polynomial.C π * f1)
    (hbezFactor : a * g0 + b * h0 - 1 = Polynomial.C π * e)
    (hmd : m ≤ d) :
    ∀ {M N : ℕ}, M ≤ N →
      (henselFactorization_prefixStateSeq_of_mem_span
          (π := π) (f := f) (g0 := g0) (h0 := h0)
          (a := a) (b := b) (f1 := f1) (e := e)
          (gbar := gbar) (m := m) (d := d)
          hπne hπmem hf hg0map hg0nat hgbar_nat hglead hh0deg
          hfactor0 hbezFactor hmd N).qCorr M =
        (henselFactorization_prefixStateSeq_of_mem_span
          (π := π) (f := f) (g0 := g0) (h0 := h0)
          (a := a) (b := b) (f1 := f1) (e := e)
          (gbar := gbar) (m := m) (d := d)
          hπne hπmem hf hg0map hg0nat hgbar_nat hglead hh0deg
          hfactor0 hbezFactor hmd M).qCorr M := by
  intro M N hMN
  induction N generalizing M with
  | zero =>
      have hM0 : M = 0 := Nat.eq_zero_of_le_zero hMN
      subst M
      rfl
  | succ N ih =>
      by_cases htop : M = N + 1
      · subst M
        rfl
      · have hMN' : M ≤ N := Nat.lt_succ_iff.mp (lt_of_le_of_ne hMN htop)
        calc
          (henselFactorization_prefixStateSeq_of_mem_span
              (π := π) (f := f) (g0 := g0) (h0 := h0)
              (a := a) (b := b) (f1 := f1) (e := e)
              (gbar := gbar) (m := m) (d := d)
              hπne hπmem hf hg0map hg0nat hgbar_nat hglead hh0deg
              hfactor0 hbezFactor hmd (N + 1)).qCorr M =
            (henselFactorization_prefixStateSeq_of_mem_span
              (π := π) (f := f) (g0 := g0) (h0 := h0)
              (a := a) (b := b) (f1 := f1) (e := e)
              (gbar := gbar) (m := m) (d := d)
              hπne hπmem hf hg0map hg0nat hgbar_nat hglead hh0deg
              hfactor0 hbezFactor hmd N).qCorr M := by
              simpa [henselFactorization_prefixStateSeq_of_mem_span] using
                henselFactorization_chosenNextPrefixState_qCorr_of_ne_of_mem_span
                  (π := π) hπne hπmem
                  (f := f) (g0 := g0) (h0 := h0)
                  (a := a) (b := b) (e := e)
                  (gbar := gbar) (m := m) (d := d) (N := N) (r := M)
                  hf hg0map hg0nat hgbar_nat hglead hh0deg
                  hbezFactor hmd
                  (henselFactorization_prefixStateSeq_of_mem_span
                    (π := π) (f := f) (g0 := g0) (h0 := h0)
                    (a := a) (b := b) (f1 := f1) (e := e)
                    (gbar := gbar) (m := m) (d := d)
                    hπne hπmem hf hg0map hg0nat hgbar_nat hglead hh0deg
                    hfactor0 hbezFactor hmd N)
                  htop
          _ =
            (henselFactorization_prefixStateSeq_of_mem_span
              (π := π) (f := f) (g0 := g0) (h0 := h0)
              (a := a) (b := b) (f1 := f1) (e := e)
              (gbar := gbar) (m := m) (d := d)
              hπne hπmem hf hg0map hg0nat hgbar_nat hglead hh0deg
              hfactor0 hbezFactor hmd M).qCorr M := ih hMN'

/-- the infinite `p`-correction sequence from the
displayed-factor displayed-factor prefix construction. -/
def henselFactorization_infinitePCorr_of_mem_span
    {R : Type*} [CommRing R] [IsLocalRing R] [NoZeroDivisors R]
    {π : R} (hπne : π ≠ 0)
    (hπmem : π ∈ IsLocalRing.maximalIdeal R)
    {f g0 h0 a b f1 e : R[X]}
    {gbar : (IsLocalRing.ResidueField R)[X]} {m d : ℕ}
    (hf : f.natDegree ≤ d)
    (hg0map : g0.map (IsLocalRing.residue R) = gbar)
    (hg0nat : g0.natDegree = m)
    (hgbar_nat : gbar.natDegree = m)
    (hglead : gbar.leadingCoeff ≠ 0)
    (hh0deg : h0.natDegree ≤ d - m)
    (hfactor0 : f - g0 * h0 = Polynomial.C π * f1)
    (hbezFactor : a * g0 + b * h0 - 1 = Polynomial.C π * e)
    (hmd : m ≤ d) (n : ℕ) : R[X] :=
  (henselFactorization_prefixStateSeq_of_mem_span
    (π := π) (f := f) (g0 := g0) (h0 := h0)
    (a := a) (b := b) (f1 := f1) (e := e)
    (gbar := gbar) (m := m) (d := d)
    hπne hπmem hf hg0map hg0nat hgbar_nat hglead hh0deg
    hfactor0 hbezFactor hmd n).pCorr n

/-- the infinite `q`-correction sequence from the
displayed-factor displayed-factor prefix construction. -/
def henselFactorization_infiniteQCorr_of_mem_span
    {R : Type*} [CommRing R] [IsLocalRing R] [NoZeroDivisors R]
    {π : R} (hπne : π ≠ 0)
    (hπmem : π ∈ IsLocalRing.maximalIdeal R)
    {f g0 h0 a b f1 e : R[X]}
    {gbar : (IsLocalRing.ResidueField R)[X]} {m d : ℕ}
    (hf : f.natDegree ≤ d)
    (hg0map : g0.map (IsLocalRing.residue R) = gbar)
    (hg0nat : g0.natDegree = m)
    (hgbar_nat : gbar.natDegree = m)
    (hglead : gbar.leadingCoeff ≠ 0)
    (hh0deg : h0.natDegree ≤ d - m)
    (hfactor0 : f - g0 * h0 = Polynomial.C π * f1)
    (hbezFactor : a * g0 + b * h0 - 1 = Polynomial.C π * e)
    (hmd : m ≤ d) (n : ℕ) : R[X] :=
  (henselFactorization_prefixStateSeq_of_mem_span
    (π := π) (f := f) (g0 := g0) (h0 := h0)
    (a := a) (b := b) (f1 := f1) (e := e)
    (gbar := gbar) (m := m) (d := d)
    hπne hπmem hf hg0map hg0nat hgbar_nat hglead hh0deg
    hfactor0 hbezFactor hmd n).qCorr n

/-- the displayed-factor infinite `p`-corrections retain the
stated degree bound. -/
theorem henselFactorization_infinitePCorr_natDegree_le_of_mem_span
    {R : Type*} [CommRing R] [IsLocalRing R] [NoZeroDivisors R]
    {π : R} (hπne : π ≠ 0)
    (hπmem : π ∈ IsLocalRing.maximalIdeal R)
    {f g0 h0 a b f1 e : R[X]}
    {gbar : (IsLocalRing.ResidueField R)[X]} {m d : ℕ}
    (hf : f.natDegree ≤ d)
    (hg0map : g0.map (IsLocalRing.residue R) = gbar)
    (hg0nat : g0.natDegree = m)
    (hgbar_nat : gbar.natDegree = m)
    (hglead : gbar.leadingCoeff ≠ 0)
    (hh0deg : h0.natDegree ≤ d - m)
    (hfactor0 : f - g0 * h0 = Polynomial.C π * f1)
    (hbezFactor : a * g0 + b * h0 - 1 = Polynomial.C π * e)
    (hmd : m ≤ d) :
    ∀ n : ℕ,
      (henselFactorization_infinitePCorr_of_mem_span
        (π := π) hπne hπmem
        (f := f) (g0 := g0) (h0 := h0)
        (a := a) (b := b) (f1 := f1) (e := e)
        (gbar := gbar) (m := m) (d := d)
        hf hg0map hg0nat hgbar_nat hglead hh0deg
        hfactor0 hbezFactor hmd n).natDegree ≤ m := by
  intro n
  unfold henselFactorization_infinitePCorr_of_mem_span
  exact
    (henselFactorization_prefixStateSeq_of_mem_span
      (π := π) (f := f) (g0 := g0) (h0 := h0)
      (a := a) (b := b) (f1 := f1) (e := e)
      (gbar := gbar) (m := m) (d := d)
      hπne hπmem hf hg0map hg0nat hgbar_nat hglead hh0deg
      hfactor0 hbezFactor hmd n).pCorrDeg n

/-- the displayed-factor infinite `q`-corrections retain the
stated degree bound. -/
theorem henselFactorization_infiniteQCorr_natDegree_le_of_mem_span
    {R : Type*} [CommRing R] [IsLocalRing R] [NoZeroDivisors R]
    {π : R} (hπne : π ≠ 0)
    (hπmem : π ∈ IsLocalRing.maximalIdeal R)
    {f g0 h0 a b f1 e : R[X]}
    {gbar : (IsLocalRing.ResidueField R)[X]} {m d : ℕ}
    (hf : f.natDegree ≤ d)
    (hg0map : g0.map (IsLocalRing.residue R) = gbar)
    (hg0nat : g0.natDegree = m)
    (hgbar_nat : gbar.natDegree = m)
    (hglead : gbar.leadingCoeff ≠ 0)
    (hh0deg : h0.natDegree ≤ d - m)
    (hfactor0 : f - g0 * h0 = Polynomial.C π * f1)
    (hbezFactor : a * g0 + b * h0 - 1 = Polynomial.C π * e)
    (hmd : m ≤ d) :
    ∀ n : ℕ,
      (henselFactorization_infiniteQCorr_of_mem_span
        (π := π) hπne hπmem
        (f := f) (g0 := g0) (h0 := h0)
        (a := a) (b := b) (f1 := f1) (e := e)
        (gbar := gbar) (m := m) (d := d)
        hf hg0map hg0nat hgbar_nat hglead hh0deg
        hfactor0 hbezFactor hmd n).natDegree ≤ d - m := by
  intro n
  unfold henselFactorization_infiniteQCorr_of_mem_span
  exact
    (henselFactorization_prefixStateSeq_of_mem_span
      (π := π) (f := f) (g0 := g0) (h0 := h0)
      (a := a) (b := b) (f1 := f1) (e := e)
      (gbar := gbar) (m := m) (d := d)
      hπne hπmem hf hg0map hg0nat hgbar_nat hglead hh0deg
      hfactor0 hbezFactor hmd n).qCorrDeg n

/-- a displayed-factor finite prefix state's
`p`-correction agrees with the extracted infinite `p`-correction at every
constructed index. -/
theorem henselFactorization_prefixStateSeq_pCorr_eq_infinite_of_le_of_mem_span
    {R : Type*} [CommRing R] [IsLocalRing R] [NoZeroDivisors R]
    {π : R} (hπne : π ≠ 0)
    (hπmem : π ∈ IsLocalRing.maximalIdeal R)
    {f g0 h0 a b f1 e : R[X]}
    {gbar : (IsLocalRing.ResidueField R)[X]} {m d : ℕ}
    (hf : f.natDegree ≤ d)
    (hg0map : g0.map (IsLocalRing.residue R) = gbar)
    (hg0nat : g0.natDegree = m)
    (hgbar_nat : gbar.natDegree = m)
    (hglead : gbar.leadingCoeff ≠ 0)
    (hh0deg : h0.natDegree ≤ d - m)
    (hfactor0 : f - g0 * h0 = Polynomial.C π * f1)
    (hbezFactor : a * g0 + b * h0 - 1 = Polynomial.C π * e)
    (hmd : m ≤ d) :
    ∀ {r N : ℕ}, r ≤ N →
      (henselFactorization_prefixStateSeq_of_mem_span
          (π := π) (f := f) (g0 := g0) (h0 := h0)
          (a := a) (b := b) (f1 := f1) (e := e)
          (gbar := gbar) (m := m) (d := d)
          hπne hπmem hf hg0map hg0nat hgbar_nat hglead hh0deg
          hfactor0 hbezFactor hmd N).pCorr r =
        henselFactorization_infinitePCorr_of_mem_span
          (π := π) hπne hπmem
          (f := f) (g0 := g0) (h0 := h0)
          (a := a) (b := b) (f1 := f1) (e := e)
          (gbar := gbar) (m := m) (d := d)
          hf hg0map hg0nat hgbar_nat hglead hh0deg
          hfactor0 hbezFactor hmd r := by
  intro r N hr
  unfold henselFactorization_infinitePCorr_of_mem_span
  exact henselFactorization_prefixStateSeq_pCorr_eq_of_le_of_mem_span
    (π := π) (f := f) (g0 := g0) (h0 := h0)
    (a := a) (b := b) (f1 := f1) (e := e)
    (gbar := gbar) (m := m) (d := d)
    hπne hπmem hf hg0map hg0nat hgbar_nat hglead hh0deg
    hfactor0 hbezFactor hmd hr

/-- a displayed-factor finite prefix state's
`q`-correction agrees with the extracted infinite `q`-correction at every
constructed index. -/
theorem henselFactorization_prefixStateSeq_qCorr_eq_infinite_of_le_of_mem_span
    {R : Type*} [CommRing R] [IsLocalRing R] [NoZeroDivisors R]
    {π : R} (hπne : π ≠ 0)
    (hπmem : π ∈ IsLocalRing.maximalIdeal R)
    {f g0 h0 a b f1 e : R[X]}
    {gbar : (IsLocalRing.ResidueField R)[X]} {m d : ℕ}
    (hf : f.natDegree ≤ d)
    (hg0map : g0.map (IsLocalRing.residue R) = gbar)
    (hg0nat : g0.natDegree = m)
    (hgbar_nat : gbar.natDegree = m)
    (hglead : gbar.leadingCoeff ≠ 0)
    (hh0deg : h0.natDegree ≤ d - m)
    (hfactor0 : f - g0 * h0 = Polynomial.C π * f1)
    (hbezFactor : a * g0 + b * h0 - 1 = Polynomial.C π * e)
    (hmd : m ≤ d) :
    ∀ {r N : ℕ}, r ≤ N →
      (henselFactorization_prefixStateSeq_of_mem_span
          (π := π) (f := f) (g0 := g0) (h0 := h0)
          (a := a) (b := b) (f1 := f1) (e := e)
          (gbar := gbar) (m := m) (d := d)
          hπne hπmem hf hg0map hg0nat hgbar_nat hglead hh0deg
          hfactor0 hbezFactor hmd N).qCorr r =
        henselFactorization_infiniteQCorr_of_mem_span
          (π := π) hπne hπmem
          (f := f) (g0 := g0) (h0 := h0)
          (a := a) (b := b) (f1 := f1) (e := e)
          (gbar := gbar) (m := m) (d := d)
          hf hg0map hg0nat hgbar_nat hglead hh0deg
          hfactor0 hbezFactor hmd r := by
  intro r N hr
  unfold henselFactorization_infiniteQCorr_of_mem_span
  exact henselFactorization_prefixStateSeq_qCorr_eq_of_le_of_mem_span
    (π := π) (f := f) (g0 := g0) (h0 := h0)
    (a := a) (b := b) (f1 := f1) (e := e)
    (gbar := gbar) (m := m) (d := d)
    hπne hπmem hf hg0map hg0nat hgbar_nat hglead hh0deg
    hfactor0 hbezFactor hmd hr

/-- every finite displayed-factor factorization invariant
transfers from the coherent prefix states to the extracted infinite correction
sequences. -/
theorem henselFactorization_infiniteCorr_factor_prefix_of_mem_span
    {R : Type*} [CommRing R] [IsLocalRing R] [NoZeroDivisors R]
    {π : R} (hπne : π ≠ 0)
    (hπmem : π ∈ IsLocalRing.maximalIdeal R)
    {f g0 h0 a b f1 e : R[X]}
    {gbar : (IsLocalRing.ResidueField R)[X]} {m d : ℕ}
    (hf : f.natDegree ≤ d)
    (hg0map : g0.map (IsLocalRing.residue R) = gbar)
    (hg0nat : g0.natDegree = m)
    (hgbar_nat : gbar.natDegree = m)
    (hglead : gbar.leadingCoeff ≠ 0)
    (hh0deg : h0.natDegree ≤ d - m)
    (hfactor0 : f - g0 * h0 = Polynomial.C π * f1)
    (hbezFactor : a * g0 + b * h0 - 1 = Polynomial.C π * e)
    (hmd : m ≤ d) :
    ∀ N : ℕ,
      ∃ fN : R[X],
        f - henselFactorization_henselIterate π g0
              (henselFactorization_infinitePCorr_of_mem_span
                (π := π) hπne hπmem
                (f := f) (g0 := g0) (h0 := h0)
                (a := a) (b := b) (f1 := f1) (e := e)
                (gbar := gbar) (m := m) (d := d)
                hf hg0map hg0nat hgbar_nat hglead hh0deg
                hfactor0 hbezFactor hmd) N *
            henselFactorization_henselIterate π h0
              (henselFactorization_infiniteQCorr_of_mem_span
                (π := π) hπne hπmem
                (f := f) (g0 := g0) (h0 := h0)
                (a := a) (b := b) (f1 := f1) (e := e)
                (gbar := gbar) (m := m) (d := d)
                hf hg0map hg0nat hgbar_nat hglead hh0deg
                hfactor0 hbezFactor hmd) N =
          Polynomial.C (π ^ (N + 1)) * fN := by
  intro N
  let S :=
    henselFactorization_prefixStateSeq_of_mem_span
      (π := π) (f := f) (g0 := g0) (h0 := h0)
      (a := a) (b := b) (f1 := f1) (e := e)
      (gbar := gbar) (m := m) (d := d)
      hπne hπmem hf hg0map hg0nat hgbar_nat hglead hh0deg
      hfactor0 hbezFactor hmd N
  have hp :
      henselFactorization_henselIterate π g0 S.pCorr N =
        henselFactorization_henselIterate π g0
          (henselFactorization_infinitePCorr_of_mem_span
            (π := π) hπne hπmem
            (f := f) (g0 := g0) (h0 := h0)
            (a := a) (b := b) (f1 := f1) (e := e)
            (gbar := gbar) (m := m) (d := d)
            hf hg0map hg0nat hgbar_nat hglead hh0deg
            hfactor0 hbezFactor hmd)
          N := by
    apply henselFactorization_henselIterate_eq_of_corr_eq_le
    intro k hk
    simpa [S] using
      henselFactorization_prefixStateSeq_pCorr_eq_infinite_of_le_of_mem_span
        (π := π) (f := f) (g0 := g0) (h0 := h0)
        (a := a) (b := b) (f1 := f1) (e := e)
        (gbar := gbar) (m := m) (d := d)
        hπne hπmem hf hg0map hg0nat hgbar_nat hglead hh0deg
        hfactor0 hbezFactor hmd (r := k) (N := N) hk
  have hq :
      henselFactorization_henselIterate π h0 S.qCorr N =
        henselFactorization_henselIterate π h0
          (henselFactorization_infiniteQCorr_of_mem_span
            (π := π) hπne hπmem
            (f := f) (g0 := g0) (h0 := h0)
            (a := a) (b := b) (f1 := f1) (e := e)
            (gbar := gbar) (m := m) (d := d)
            hf hg0map hg0nat hgbar_nat hglead hh0deg
            hfactor0 hbezFactor hmd)
          N := by
    apply henselFactorization_henselIterate_eq_of_corr_eq_le
    intro k hk
    simpa [S] using
      henselFactorization_prefixStateSeq_qCorr_eq_infinite_of_le_of_mem_span
        (π := π) (f := f) (g0 := g0) (h0 := h0)
        (a := a) (b := b) (f1 := f1) (e := e)
        (gbar := gbar) (m := m) (d := d)
        hπne hπmem hf hg0map hg0nat hgbar_nat hglead hh0deg
        hfactor0 hbezFactor hmd (r := k) (N := N) hk
  exact ⟨S.fErr, by simpa [S, hp, hq] using S.factor⟩

/-- the displayed-factor `g`-approximants keep the construction
degree bound. -/
theorem henselFactorization_infiniteGIter_natDegree_le_of_mem_span
    {R : Type*} [CommRing R] [IsLocalRing R] [NoZeroDivisors R]
    {π : R} (hπne : π ≠ 0)
    (hπmem : π ∈ IsLocalRing.maximalIdeal R)
    {f g0 h0 a b f1 e : R[X]}
    {gbar : (IsLocalRing.ResidueField R)[X]} {m d : ℕ}
    (hf : f.natDegree ≤ d)
    (hg0map : g0.map (IsLocalRing.residue R) = gbar)
    (hg0nat : g0.natDegree = m)
    (hgbar_nat : gbar.natDegree = m)
    (hglead : gbar.leadingCoeff ≠ 0)
    (hh0deg : h0.natDegree ≤ d - m)
    (hfactor0 : f - g0 * h0 = Polynomial.C π * f1)
    (hbezFactor : a * g0 + b * h0 - 1 = Polynomial.C π * e)
    (hmd : m ≤ d) :
    ∀ N : ℕ,
      (henselFactorization_henselIterate π g0
        (henselFactorization_infinitePCorr_of_mem_span
          (π := π) hπne hπmem
          (f := f) (g0 := g0) (h0 := h0)
          (a := a) (b := b) (f1 := f1) (e := e)
          (gbar := gbar) (m := m) (d := d)
          hf hg0map hg0nat hgbar_nat hglead hh0deg
          hfactor0 hbezFactor hmd)
        N).natDegree ≤ m := by
  exact henselFactorization_henselIterate_natDegree_le
    (π := π) (F0 := g0)
    (corr := henselFactorization_infinitePCorr_of_mem_span
      (π := π) hπne hπmem
      (f := f) (g0 := g0) (h0 := h0)
      (a := a) (b := b) (f1 := f1) (e := e)
      (gbar := gbar) (m := m) (d := d)
      hf hg0map hg0nat hgbar_nat hglead hh0deg
      hfactor0 hbezFactor hmd)
    (M := m)
    (by simp [hg0nat])
    (henselFactorization_infinitePCorr_natDegree_le_of_mem_span
      (π := π) hπne hπmem
      (f := f) (g0 := g0) (h0 := h0)
      (a := a) (b := b) (f1 := f1) (e := e)
      (gbar := gbar) (m := m) (d := d)
      hf hg0map hg0nat hgbar_nat hglead hh0deg
      hfactor0 hbezFactor hmd)

/-- the displayed-factor `h`-approximants keep the construction
degree bound. -/
theorem henselFactorization_infiniteHIter_natDegree_le_of_mem_span
    {R : Type*} [CommRing R] [IsLocalRing R] [NoZeroDivisors R]
    {π : R} (hπne : π ≠ 0)
    (hπmem : π ∈ IsLocalRing.maximalIdeal R)
    {f g0 h0 a b f1 e : R[X]}
    {gbar : (IsLocalRing.ResidueField R)[X]} {m d : ℕ}
    (hf : f.natDegree ≤ d)
    (hg0map : g0.map (IsLocalRing.residue R) = gbar)
    (hg0nat : g0.natDegree = m)
    (hgbar_nat : gbar.natDegree = m)
    (hglead : gbar.leadingCoeff ≠ 0)
    (hh0deg : h0.natDegree ≤ d - m)
    (hfactor0 : f - g0 * h0 = Polynomial.C π * f1)
    (hbezFactor : a * g0 + b * h0 - 1 = Polynomial.C π * e)
    (hmd : m ≤ d) :
    ∀ N : ℕ,
      (henselFactorization_henselIterate π h0
        (henselFactorization_infiniteQCorr_of_mem_span
          (π := π) hπne hπmem
          (f := f) (g0 := g0) (h0 := h0)
          (a := a) (b := b) (f1 := f1) (e := e)
          (gbar := gbar) (m := m) (d := d)
          hf hg0map hg0nat hgbar_nat hglead hh0deg
          hfactor0 hbezFactor hmd)
        N).natDegree ≤ d - m := by
  exact henselFactorization_henselIterate_natDegree_le
    (π := π) (F0 := h0)
    (corr := henselFactorization_infiniteQCorr_of_mem_span
      (π := π) hπne hπmem
      (f := f) (g0 := g0) (h0 := h0)
      (a := a) (b := b) (f1 := f1) (e := e)
      (gbar := gbar) (m := m) (d := d)
      hf hg0map hg0nat hgbar_nat hglead hh0deg
      hfactor0 hbezFactor hmd)
    (M := d - m)
    hh0deg
    (henselFactorization_infiniteQCorr_natDegree_le_of_mem_span
      (π := π) hπne hπmem
      (f := f) (g0 := g0) (h0 := h0)
      (a := a) (b := b) (f1 := f1) (e := e)
      (gbar := gbar) (m := m) (d := d)
      hf hg0map hg0nat hgbar_nat hglead hh0deg
      hfactor0 hbezFactor hmd)


end Valuations
end AlgebraicNumberTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_Henselian_Factorization_PrincipalLimits
attribute [-instance] _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# principal-ideal limit route

This file keeps the Hensel limit step in the filtration generated by the
chosen chosen element `π`.  This is the route needed for complete valued fields
whose maximal ideal is not assumed principal or adically separated.
-/

noncomputable section

open scoped Polynomial

namespace AlgebraicNumberTheory
namespace Valuations

/-- displayed-factor infinite `g`-approximants are Cauchy for
the principal-ideal filtration generated by the chosen `π`. -/
theorem henselFactorization_infiniteG_coeff_spanAdicCoeffCauchy_of_mem_span
    {R : Type*} [CommRing R] [IsLocalRing R] [NoZeroDivisors R]
    {π : R} (hπne : π ≠ 0)
    (hπmem : π ∈ IsLocalRing.maximalIdeal R)
    {f g0 h0 a b f1 e : R[X]}
    {gbar : (IsLocalRing.ResidueField R)[X]} {m d : ℕ}
    (hf : f.natDegree ≤ d)
    (hg0map : g0.map (IsLocalRing.residue R) = gbar)
    (hg0nat : g0.natDegree = m)
    (hgbar_nat : gbar.natDegree = m)
    (hglead : gbar.leadingCoeff ≠ 0)
    (hh0deg : h0.natDegree ≤ d - m)
    (hfactor0 : f - g0 * h0 = Polynomial.C π * f1)
    (hbezFactor : a * g0 + b * h0 - 1 = Polynomial.C π * e)
    (hmd : m ≤ d) (i : ℕ) :
    henselFactorization_adicCoeffCauchy (Ideal.span ({π} : Set R))
      (fun N : ℕ =>
        (henselFactorization_henselIterate π g0
          (henselFactorization_infinitePCorr_of_mem_span
            (π := π) hπne hπmem
            (f := f) (g0 := g0) (h0 := h0)
            (a := a) (b := b) (f1 := f1) (e := e)
            (gbar := gbar) (m := m) (d := d)
            hf hg0map hg0nat hgbar_nat hglead hh0deg
            hfactor0 hbezFactor hmd)
          N).coeff i) := by
  exact henselFactorization_coeff_adicCoeffCauchy_of_sub_coeff_mem
    (Ideal.span ({π} : Set R))
    (Pseq := fun N : ℕ =>
      henselFactorization_henselIterate π g0
        (henselFactorization_infinitePCorr_of_mem_span
          (π := π) hπne hπmem
          (f := f) (g0 := g0) (h0 := h0)
          (a := a) (b := b) (f1 := f1) (e := e)
          (gbar := gbar) (m := m) (d := d)
          hf hg0map hg0nat hgbar_nat hglead hh0deg
          hfactor0 hbezFactor hmd)
        N)
    (by
      intro M N hMN i
      exact henselFactorization_henselIterate_sub_coeff_mem_span_pow_of_le
        (π := π) g0
        (henselFactorization_infinitePCorr_of_mem_span
          (π := π) hπne hπmem
          (f := f) (g0 := g0) (h0 := h0)
          (a := a) (b := b) (f1 := f1) (e := e)
          (gbar := gbar) (m := m) (d := d)
          hf hg0map hg0nat hgbar_nat hglead hh0deg
          hfactor0 hbezFactor hmd)
        hMN i)
    i

/-- principal-filtration polynomial limit for the
displayed-factor infinite `g`-approximants. -/
theorem henselFactorization_exists_infiniteG_spanLimitPolynomial_of_mem_span
    {R : Type*} [CommRing R] [IsLocalRing R] [NoZeroDivisors R]
    {π : R} [IsPrecomplete (Ideal.span ({π} : Set R)) R]
    (hπne : π ≠ 0)
    (hπmem : π ∈ IsLocalRing.maximalIdeal R)
    {f g0 h0 a b f1 e : R[X]}
    {gbar : (IsLocalRing.ResidueField R)[X]} {m d : ℕ}
    (hf : f.natDegree ≤ d)
    (hg0map : g0.map (IsLocalRing.residue R) = gbar)
    (hg0nat : g0.natDegree = m)
    (hgbar_nat : gbar.natDegree = m)
    (hglead : gbar.leadingCoeff ≠ 0)
    (hh0deg : h0.natDegree ≤ d - m)
    (hfactor0 : f - g0 * h0 = Polynomial.C π * f1)
    (hbezFactor : a * g0 + b * h0 - 1 = Polynomial.C π * e)
    (hmd : m ≤ d) :
    ∃ G : R[X], G.natDegree ≤ m ∧
      ∀ n i : ℕ,
        (henselFactorization_henselIterate π g0
            (henselFactorization_infinitePCorr_of_mem_span
              (π := π) hπne hπmem
              (f := f) (g0 := g0) (h0 := h0)
              (a := a) (b := b) (f1 := f1) (e := e)
              (gbar := gbar) (m := m) (d := d)
              hf hg0map hg0nat hgbar_nat hglead hh0deg
              hfactor0 hbezFactor hmd) n - G).coeff i ∈
          Ideal.span ({π} : Set R) ^ n := by
  exact
    henselFactorization_exists_limitPolynomial_of_bounded_coeffLimits
      (Ideal.span ({π} : Set R))
      (N := m)
      (Pseq := fun n : ℕ =>
        henselFactorization_henselIterate π g0
          (henselFactorization_infinitePCorr_of_mem_span
            (π := π) hπne hπmem
            (f := f) (g0 := g0) (h0 := h0)
            (a := a) (b := b) (f1 := f1) (e := e)
            (gbar := gbar) (m := m) (d := d)
            hf hg0map hg0nat hgbar_nat hglead hh0deg
            hfactor0 hbezFactor hmd)
          n)
      (henselFactorization_infiniteGIter_natDegree_le_of_mem_span
        (π := π) hπne hπmem
        (f := f) (g0 := g0) (h0 := h0)
        (a := a) (b := b) (f1 := f1) (e := e)
        (gbar := gbar) (m := m) (d := d)
        hf hg0map hg0nat hgbar_nat hglead hh0deg
        hfactor0 hbezFactor hmd)
      (fun i =>
        henselFactorization_infiniteG_coeff_spanAdicCoeffCauchy_of_mem_span
          (π := π) hπne hπmem
          (f := f) (g0 := g0) (h0 := h0)
          (a := a) (b := b) (f1 := f1) (e := e)
          (gbar := gbar) (m := m) (d := d)
          hf hg0map hg0nat hgbar_nat hglead hh0deg
          hfactor0 hbezFactor hmd i)

/-- displayed-factor infinite `h`-approximants are Cauchy for
the principal-ideal filtration generated by the chosen `π`. -/
theorem henselFactorization_infiniteH_coeff_spanAdicCoeffCauchy_of_mem_span
    {R : Type*} [CommRing R] [IsLocalRing R] [NoZeroDivisors R]
    {π : R} (hπne : π ≠ 0)
    (hπmem : π ∈ IsLocalRing.maximalIdeal R)
    {f g0 h0 a b f1 e : R[X]}
    {gbar : (IsLocalRing.ResidueField R)[X]} {m d : ℕ}
    (hf : f.natDegree ≤ d)
    (hg0map : g0.map (IsLocalRing.residue R) = gbar)
    (hg0nat : g0.natDegree = m)
    (hgbar_nat : gbar.natDegree = m)
    (hglead : gbar.leadingCoeff ≠ 0)
    (hh0deg : h0.natDegree ≤ d - m)
    (hfactor0 : f - g0 * h0 = Polynomial.C π * f1)
    (hbezFactor : a * g0 + b * h0 - 1 = Polynomial.C π * e)
    (hmd : m ≤ d) (i : ℕ) :
    henselFactorization_adicCoeffCauchy (Ideal.span ({π} : Set R))
      (fun N : ℕ =>
        (henselFactorization_henselIterate π h0
          (henselFactorization_infiniteQCorr_of_mem_span
            (π := π) hπne hπmem
            (f := f) (g0 := g0) (h0 := h0)
            (a := a) (b := b) (f1 := f1) (e := e)
            (gbar := gbar) (m := m) (d := d)
            hf hg0map hg0nat hgbar_nat hglead hh0deg
            hfactor0 hbezFactor hmd)
          N).coeff i) := by
  exact henselFactorization_coeff_adicCoeffCauchy_of_sub_coeff_mem
    (Ideal.span ({π} : Set R))
    (Pseq := fun N : ℕ =>
      henselFactorization_henselIterate π h0
        (henselFactorization_infiniteQCorr_of_mem_span
          (π := π) hπne hπmem
          (f := f) (g0 := g0) (h0 := h0)
          (a := a) (b := b) (f1 := f1) (e := e)
          (gbar := gbar) (m := m) (d := d)
          hf hg0map hg0nat hgbar_nat hglead hh0deg
          hfactor0 hbezFactor hmd)
        N)
    (by
      intro M N hMN i
      exact henselFactorization_henselIterate_sub_coeff_mem_span_pow_of_le
        (π := π) h0
        (henselFactorization_infiniteQCorr_of_mem_span
          (π := π) hπne hπmem
          (f := f) (g0 := g0) (h0 := h0)
          (a := a) (b := b) (f1 := f1) (e := e)
          (gbar := gbar) (m := m) (d := d)
          hf hg0map hg0nat hgbar_nat hglead hh0deg
          hfactor0 hbezFactor hmd)
        hMN i)
    i

/-- principal-filtration polynomial limit for the
displayed-factor infinite `h`-approximants. -/
theorem henselFactorization_exists_infiniteH_spanLimitPolynomial_of_mem_span
    {R : Type*} [CommRing R] [IsLocalRing R] [NoZeroDivisors R]
    {π : R} [IsPrecomplete (Ideal.span ({π} : Set R)) R]
    (hπne : π ≠ 0)
    (hπmem : π ∈ IsLocalRing.maximalIdeal R)
    {f g0 h0 a b f1 e : R[X]}
    {gbar : (IsLocalRing.ResidueField R)[X]} {m d : ℕ}
    (hf : f.natDegree ≤ d)
    (hg0map : g0.map (IsLocalRing.residue R) = gbar)
    (hg0nat : g0.natDegree = m)
    (hgbar_nat : gbar.natDegree = m)
    (hglead : gbar.leadingCoeff ≠ 0)
    (hh0deg : h0.natDegree ≤ d - m)
    (hfactor0 : f - g0 * h0 = Polynomial.C π * f1)
    (hbezFactor : a * g0 + b * h0 - 1 = Polynomial.C π * e)
    (hmd : m ≤ d) :
    ∃ H : R[X], H.natDegree ≤ d - m ∧
      ∀ n i : ℕ,
        (henselFactorization_henselIterate π h0
            (henselFactorization_infiniteQCorr_of_mem_span
              (π := π) hπne hπmem
              (f := f) (g0 := g0) (h0 := h0)
              (a := a) (b := b) (f1 := f1) (e := e)
              (gbar := gbar) (m := m) (d := d)
              hf hg0map hg0nat hgbar_nat hglead hh0deg
              hfactor0 hbezFactor hmd) n - H).coeff i ∈
          Ideal.span ({π} : Set R) ^ n := by
  exact
    henselFactorization_exists_limitPolynomial_of_bounded_coeffLimits
      (Ideal.span ({π} : Set R))
      (N := d - m)
      (Pseq := fun n : ℕ =>
        henselFactorization_henselIterate π h0
          (henselFactorization_infiniteQCorr_of_mem_span
            (π := π) hπne hπmem
            (f := f) (g0 := g0) (h0 := h0)
            (a := a) (b := b) (f1 := f1) (e := e)
            (gbar := gbar) (m := m) (d := d)
            hf hg0map hg0nat hgbar_nat hglead hh0deg
            hfactor0 hbezFactor hmd)
          n)
      (henselFactorization_infiniteHIter_natDegree_le_of_mem_span
        (π := π) hπne hπmem
        (f := f) (g0 := g0) (h0 := h0)
        (a := a) (b := b) (f1 := f1) (e := e)
        (gbar := gbar) (m := m) (d := d)
        hf hg0map hg0nat hgbar_nat hglead hh0deg
        hfactor0 hbezFactor hmd)
      (fun i =>
        henselFactorization_infiniteH_coeff_spanAdicCoeffCauchy_of_mem_span
          (π := π) hπne hπmem
          (f := f) (g0 := g0) (h0 := h0)
          (a := a) (b := b) (f1 := f1) (e := e)
          (gbar := gbar) (m := m) (d := d)
          hf hg0map hg0nat hgbar_nat hglead hh0deg
          hfactor0 hbezFactor hmd i)

/-- displayed-factor error estimate in the principal
filtration generated by `π`. -/
theorem henselFactorization_infiniteCorr_error_coeff_mem_span_pow_of_mem_span
    {R : Type*} [CommRing R] [IsLocalRing R] [NoZeroDivisors R]
    {π : R} (hπne : π ≠ 0)
    (hπmem : π ∈ IsLocalRing.maximalIdeal R)
    {f g0 h0 a b f1 e : R[X]}
    {gbar : (IsLocalRing.ResidueField R)[X]} {m d : ℕ}
    (hf : f.natDegree ≤ d)
    (hg0map : g0.map (IsLocalRing.residue R) = gbar)
    (hg0nat : g0.natDegree = m)
    (hgbar_nat : gbar.natDegree = m)
    (hglead : gbar.leadingCoeff ≠ 0)
    (hh0deg : h0.natDegree ≤ d - m)
    (hfactor0 : f - g0 * h0 = Polynomial.C π * f1)
    (hbezFactor : a * g0 + b * h0 - 1 = Polynomial.C π * e)
    (hmd : m ≤ d) :
    ∀ N i : ℕ,
      (f - henselFactorization_henselIterate π g0
            (henselFactorization_infinitePCorr_of_mem_span
              (π := π) hπne hπmem
              (f := f) (g0 := g0) (h0 := h0)
              (a := a) (b := b) (f1 := f1) (e := e)
              (gbar := gbar) (m := m) (d := d)
              hf hg0map hg0nat hgbar_nat hglead hh0deg
              hfactor0 hbezFactor hmd) N *
          henselFactorization_henselIterate π h0
            (henselFactorization_infiniteQCorr_of_mem_span
              (π := π) hπne hπmem
              (f := f) (g0 := g0) (h0 := h0)
              (a := a) (b := b) (f1 := f1) (e := e)
              (gbar := gbar) (m := m) (d := d)
              hf hg0map hg0nat hgbar_nat hglead hh0deg
              hfactor0 hbezFactor hmd) N).coeff i ∈
        Ideal.span ({π} : Set R) ^ (N + 1) := by
  intro N i
  rcases henselFactorization_infiniteCorr_factor_prefix_of_mem_span
      (π := π) hπne hπmem
      (f := f) (g0 := g0) (h0 := h0)
      (a := a) (b := b) (f1 := f1) (e := e)
      (gbar := gbar) (m := m) (d := d)
      hf hg0map hg0nat hgbar_nat hglead hh0deg
      hfactor0 hbezFactor hmd N with
    ⟨fN, hfactor⟩
  exact henselFactorization_coeff_mem_span_pow_of_factor
    (π := π) (n := N + 1) hfactor i

/-- complete-limit factorization from displayed initial
principal-element errors, using the `π`-adic principal filtration. -/
theorem henselFactorization_exists_limit_factorization_of_mem_span_principal
    {R : Type*} [CommRing R] [IsLocalRing R] [NoZeroDivisors R]
    {π : R} [IsPrecomplete (Ideal.span ({π} : Set R)) R]
    [IsHausdorff (Ideal.span ({π} : Set R)) R]
    (hπne : π ≠ 0)
    (hπmem : π ∈ IsLocalRing.maximalIdeal R)
    {f g0 h0 a b f1 e : R[X]}
    {gbar hbar : (IsLocalRing.ResidueField R)[X]} {m d : ℕ}
    (hf : f.natDegree ≤ d)
    (hg0map : g0.map (IsLocalRing.residue R) = gbar)
    (hh0map : h0.map (IsLocalRing.residue R) = hbar)
    (hg0nat : g0.natDegree = m)
    (hgbar_nat : gbar.natDegree = m)
    (hglead : gbar.leadingCoeff ≠ 0)
    (hh0deg : h0.natDegree ≤ d - m)
    (hfactor0 : f - g0 * h0 = Polynomial.C π * f1)
    (hbezFactor : a * g0 + b * h0 - 1 = Polynomial.C π * e)
    (hmd : m ≤ d) :
    ∃ G H : R[X],
      G.natDegree ≤ m ∧ H.natDegree ≤ d - m ∧ f = G * H ∧
        G.map (IsLocalRing.residue R) = gbar ∧
        H.map (IsLocalRing.residue R) = hbar := by
  rcases henselFactorization_exists_infiniteG_spanLimitPolynomial_of_mem_span
      (π := π) hπne hπmem
      (f := f) (g0 := g0) (h0 := h0)
      (a := a) (b := b) (f1 := f1) (e := e)
      (gbar := gbar) (m := m) (d := d)
      hf hg0map hg0nat hgbar_nat hglead hh0deg
      hfactor0 hbezFactor hmd with
    ⟨G, hGdeg, hGlim⟩
  rcases henselFactorization_exists_infiniteH_spanLimitPolynomial_of_mem_span
      (π := π) hπne hπmem
      (f := f) (g0 := g0) (h0 := h0)
      (a := a) (b := b) (f1 := f1) (e := e)
      (gbar := gbar) (m := m) (d := d)
      hf hg0map hg0nat hgbar_nat hglead hh0deg
      hfactor0 hbezFactor hmd with
    ⟨H, hHdeg, hHlim⟩
  let I : Ideal R := Ideal.span ({π} : Set R)
  have hfactor : f = G * H := by
    apply henselFactorization_limit_factor_eq_of_approximants
      (I := I)
      (Gseq := fun n : ℕ =>
        henselFactorization_henselIterate π g0
          (henselFactorization_infinitePCorr_of_mem_span
            (π := π) hπne hπmem
            (f := f) (g0 := g0) (h0 := h0)
            (a := a) (b := b) (f1 := f1) (e := e)
            (gbar := gbar) (m := m) (d := d)
            hf hg0map hg0nat hgbar_nat hglead hh0deg
            hfactor0 hbezFactor hmd)
          n)
      (Hseq := fun n : ℕ =>
        henselFactorization_henselIterate π h0
          (henselFactorization_infiniteQCorr_of_mem_span
            (π := π) hπne hπmem
            (f := f) (g0 := g0) (h0 := h0)
            (a := a) (b := b) (f1 := f1) (e := e)
            (gbar := gbar) (m := m) (d := d)
            hf hg0map hg0nat hgbar_nat hglead hh0deg
            hfactor0 hbezFactor hmd)
          n)
    · intro n i
      exact (Ideal.pow_le_pow_right (Nat.le_succ n))
        (by
          simpa [I] using
            henselFactorization_infiniteCorr_error_coeff_mem_span_pow_of_mem_span
              (π := π) hπne hπmem
              (f := f) (g0 := g0) (h0 := h0)
              (a := a) (b := b) (f1 := f1) (e := e)
              (gbar := gbar) (m := m) (d := d)
              hf hg0map hg0nat hgbar_nat hglead hh0deg
              hfactor0 hbezFactor hmd n i)
    · simpa [I] using hGlim
    · simpa [I] using hHlim
  have hGredSpan : ∀ i : ℕ, (G - g0).coeff i ∈ Ideal.span ({π} : Set R) :=
    henselFactorization_limit_reduction_of_approx_reduction
      (I := Ideal.span ({π} : Set R))
      (Pseq := fun n : ℕ =>
        henselFactorization_henselIterate π g0
          (henselFactorization_infinitePCorr_of_mem_span
            (π := π) hπne hπmem
            (f := f) (g0 := g0) (h0 := h0)
            (a := a) (b := b) (f1 := f1) (e := e)
            (gbar := gbar) (m := m) (d := d)
            hf hg0map hg0nat hgbar_nat hglead hh0deg
            hfactor0 hbezFactor hmd)
          n)
      (P := G) (P0 := g0) hGlim
      (henselFactorization_henselIterate_span_singleton g0
        (henselFactorization_infinitePCorr_of_mem_span
          (π := π) hπne hπmem
          (f := f) (g0 := g0) (h0 := h0)
          (a := a) (b := b) (f1 := f1) (e := e)
          (gbar := gbar) (m := m) (d := d)
          hf hg0map hg0nat hgbar_nat hglead hh0deg
          hfactor0 hbezFactor hmd))
  have hHredSpan : ∀ i : ℕ, (H - h0).coeff i ∈ Ideal.span ({π} : Set R) :=
    henselFactorization_limit_reduction_of_approx_reduction
      (I := Ideal.span ({π} : Set R))
      (Pseq := fun n : ℕ =>
        henselFactorization_henselIterate π h0
          (henselFactorization_infiniteQCorr_of_mem_span
            (π := π) hπne hπmem
            (f := f) (g0 := g0) (h0 := h0)
            (a := a) (b := b) (f1 := f1) (e := e)
            (gbar := gbar) (m := m) (d := d)
            hf hg0map hg0nat hgbar_nat hglead hh0deg
            hfactor0 hbezFactor hmd)
          n)
      (P := H) (P0 := h0) hHlim
      (henselFactorization_henselIterate_span_singleton h0
        (henselFactorization_infiniteQCorr_of_mem_span
          (π := π) hπne hπmem
          (f := f) (g0 := g0) (h0 := h0)
          (a := a) (b := b) (f1 := f1) (e := e)
          (gbar := gbar) (m := m) (d := d)
          hf hg0map hg0nat hgbar_nat hglead hh0deg
          hfactor0 hbezFactor hmd))
  have hspan_le :
      Ideal.span ({π} : Set R) ≤ IsLocalRing.maximalIdeal R :=
    henselFactorization_span_singleton_le_ideal_of_mem
      (IsLocalRing.maximalIdeal R) hπmem
  have hGred : ∀ i : ℕ, (G - g0).coeff i ∈ IsLocalRing.maximalIdeal R :=
    fun i => hspan_le (hGredSpan i)
  have hHred : ∀ i : ℕ, (H - h0).coeff i ∈ IsLocalRing.maximalIdeal R :=
    fun i => hspan_le (hHredSpan i)
  have hGmap0 :
      G.map (IsLocalRing.residue R) =
        g0.map (IsLocalRing.residue R) :=
    henselFactorization_residue_map_eq_of_sub_coeff_mem_maximalIdeal hGred
  have hHmap0 :
      H.map (IsLocalRing.residue R) =
        h0.map (IsLocalRing.residue R) :=
    henselFactorization_residue_map_eq_of_sub_coeff_mem_maximalIdeal hHred
  refine ⟨G, H, hGdeg, hHdeg, hfactor, ?_, ?_⟩
  · rw [hGmap0, hg0map]
  · rw [hHmap0, hh0map]

end Valuations
end AlgebraicNumberTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_Henselian_Factorization_Assembly
attribute [-instance] _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# explicit valuation-ring Hensel statement

This file connects the chosen finite-minimum coefficient to
the displayed-factor complete-limit theorem.
-/

noncomputable section

open scoped Polynomial

namespace AlgebraicNumberTheory
namespace Valuations

/-- complete-limit factorization from coprime residual factors
and chosen lifts over a valuation ring, using the principal filtration
generated by the finite-minimum element `π`. -/
theorem henselFactorization_exists_limit_factorization_of_coprime_lifts_valuationRing_principal
    {R : Type*} [CommRing R] [Nontrivial R] [PreValuationRing R]
    [NoZeroDivisors R]
    (hpre : ∀ π : R, π ≠ 0 → π ∈ IsLocalRing.maximalIdeal R →
      IsPrecomplete (Ideal.span ({π} : Set R)) R)
    (hhaus : ∀ π : R, π ≠ 0 → π ∈ IsLocalRing.maximalIdeal R →
      IsHausdorff (Ideal.span ({π} : Set R)) R)
    {f g0 h0 : R[X]}
    {gbar hbar : (IsLocalRing.ResidueField R)[X]} {m d : ℕ}
    (hfbar : f.map (IsLocalRing.residue R) = gbar * hbar)
    (hg0map : g0.map (IsLocalRing.residue R) = gbar)
    (hh0map : h0.map (IsLocalRing.residue R) = hbar)
    (hcop : IsCoprime gbar hbar)
    (hf : f.natDegree ≤ d)
    (hg0nat : g0.natDegree = m)
    (hgbar_nat : gbar.natDegree = m)
    (hglead : gbar.leadingCoeff ≠ 0)
    (hh0deg : h0.natDegree ≤ d - m)
    (hmd : m ≤ d) :
    ∃ G H : R[X],
      G.natDegree ≤ m ∧ H.natDegree ≤ d - m ∧ f = G * H ∧
        G.map (IsLocalRing.residue R) = gbar ∧
        H.map (IsLocalRing.residue R) = hbar := by
  classical
  rcases henselFactorization_exists_bezout_lifts
      (IsLocalRing.residue R) IsLocalRing.residue_surjective
      hcop hg0map hh0map with
    ⟨a, b, hbez⟩
  let S := henselFactorization_twoPolynomialCoeffFinset
    (f - g0 * h0) (a * g0 + b * h0 - 1)
  by_cases hs : S.Nonempty
  · rcases henselFactorization_exists_pi_factor_initial_errors_of_residue_lifts_of_nonempty
      (R := R) (f := f) (g0 := g0) (h0 := h0) (a := a) (b := b)
      (gbar := gbar) (hbar := hbar)
      hfbar hg0map hh0map hbez (by simpa [S] using hs) with
      ⟨π, hπmem, hπcoeff, ⟨f1, hfactor0⟩, ⟨e, hbezFactor⟩⟩
    have hπne : π ≠ 0 :=
      henselFactorization_ne_zero_of_mem_twoPolynomialCoeffFinset hπcoeff
    let : IsPrecomplete (Ideal.span ({π} : Set R)) R :=
      hpre π hπne hπmem
    let : IsHausdorff (Ideal.span ({π} : Set R)) R :=
      hhaus π hπne hπmem
    exact henselFactorization_exists_limit_factorization_of_mem_span_principal
      (π := π) hπne hπmem
      (f := f) (g0 := g0) (h0 := h0)
      (a := a) (b := b) (f1 := f1) (e := e)
      (gbar := gbar) (hbar := hbar) (m := m) (d := d)
      hf hg0map hh0map hg0nat hgbar_nat hglead hh0deg
      hfactor0 hbezFactor hmd
  · have hSempty :
        henselFactorization_twoPolynomialCoeffFinset
          (f - g0 * h0) (a * g0 + b * h0 - 1) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hs ⟨x, by simpa [S] using hx⟩
    have hzeros :=
      henselFactorization_twoPolynomialCoeffFinset_empty_iff.mp hSempty
    rcases hzeros with ⟨hfactor0, _hbez0⟩
    refine ⟨g0, h0, ?_, hh0deg, ?_, hg0map, hh0map⟩
    · simp [hg0nat]
    · exact sub_eq_zero.mp hfactor0

/-- explicit residual-factor form using the principal
filtration generated by the finite-minimum element chosen in the proof. -/
theorem henselFactorization_exists_limit_factorization_of_residual_factors_valuationRing_principal
    {R : Type*} [CommRing R] [Nontrivial R] [PreValuationRing R]
    [NoZeroDivisors R]
    (hpre : ∀ π : R, π ≠ 0 → π ∈ IsLocalRing.maximalIdeal R →
      IsPrecomplete (Ideal.span ({π} : Set R)) R)
    (hhaus : ∀ π : R, π ≠ 0 → π ∈ IsLocalRing.maximalIdeal R →
      IsHausdorff (Ideal.span ({π} : Set R)) R)
    {f : R[X]}
    {gbar hbar : (IsLocalRing.ResidueField R)[X]}
    (hprim : f.map (IsLocalRing.residue R) ≠ 0)
    (hfbar : f.map (IsLocalRing.residue R) = gbar * hbar)
    (hcop : IsCoprime gbar hbar) :
    ∃ G H : R[X],
      G.natDegree = gbar.natDegree ∧
        H.natDegree ≤ f.natDegree - gbar.natDegree ∧
          f = G * H ∧
            G.map (IsLocalRing.residue R) = gbar ∧
              H.map (IsLocalRing.residue R) = hbar := by
  rcases henselFactorization_exists_degreeControlledLifts_of_residual_factorization
      hprim hfbar with
    ⟨g0, h0, hg0map, hh0map, hg0nat, hh0deg, hmd, hglead⟩
  rcases
      henselFactorization_exists_limit_factorization_of_coprime_lifts_valuationRing_principal
        (R := R) hpre hhaus
        (f := f) (g0 := g0) (h0 := h0)
        (gbar := gbar) (hbar := hbar)
        (m := gbar.natDegree) (d := f.natDegree)
        hfbar hg0map hh0map hcop le_rfl hg0nat rfl hglead hh0deg hmd with
    ⟨G, H, hGle, hHle, hfactor, hGmap, hHmap⟩
  have hGdegree : G.natDegree = gbar.natDegree :=
    henselFactorization_natDegree_eq_of_residue_eq_of_le
      (R := R) (P := G) (gbar := gbar) (m := gbar.natDegree)
      hGle hGmap rfl hglead
  exact ⟨G, H, hGdegree, hHle, hfactor, hGmap, hHmap⟩

end Valuations
end AlgebraicNumberTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_Henselian_Factorization_Complete
attribute [-instance] _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Hensel's lemma over a complete valued field

This file supplies the explicit endpoint from completeness and
nonarchimedeanness, using the principal element selected from the finitely many
initial error coefficients in the proof core.
-/

noncomputable section

open scoped Polynomial

namespace AlgebraicNumberTheory
namespace Valuations

/-- Hensel's lemma in the complete
nonarchimedean-valued-field setting.  A primitive polynomial over the
valuation ring whose reduction is a product of coprime factors lifts to a
factorization with the prescribed reductions and with the degree of the left
factor unchanged. -/
theorem henselFactorization_complete_exists_factorization
    {K : Type*} [Field K]
    (v : AbsoluteValue K ℝ)
    (hcomplete : IsCompleteForAbsoluteValue v)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    {f : (absoluteValueValuationSubring v hnonarch)[X]}
    {gbar hbar : (IsLocalRing.ResidueField
      (absoluteValueValuationSubring v hnonarch))[X]}
    (hprim : f.map (IsLocalRing.residue
      (absoluteValueValuationSubring v hnonarch)) ≠ 0)
    (hfbar : f.map (IsLocalRing.residue
      (absoluteValueValuationSubring v hnonarch)) =
        gbar * hbar)
    (hcop : IsCoprime gbar hbar) :
    ∃ G H :
        (absoluteValueValuationSubring v hnonarch)[X],
      f = G * H ∧
        G.natDegree = gbar.natDegree ∧
          G.map (IsLocalRing.residue
            (absoluteValueValuationSubring v hnonarch)) =
              gbar ∧
            H.map (IsLocalRing.residue
              (absoluteValueValuationSubring v hnonarch)) =
                hbar := by
  let V := absoluteValueValuationSubring v hnonarch
  let hpre :
      ∀ π : V, π ≠ 0 → π ∈ IsLocalRing.maximalIdeal V →
        IsPrecomplete (Ideal.span ({π} : Set V)) V := by
    intro π hπne hπmem
    exact principalPrecomplete_of_complete
      v hcomplete hnonarch hπne hπmem
  let hhaus :
      ∀ π : V, π ≠ 0 → π ∈ IsLocalRing.maximalIdeal V →
        IsHausdorff (Ideal.span ({π} : Set V)) V := by
    intro π hπne hπmem
    exact principalHausdorff_of_nonzero_mem_maximalIdeal
      v hnonarch hπne hπmem
  rcases
      henselFactorization_exists_limit_factorization_of_residual_factors_valuationRing_principal
        (R := V) hpre hhaus
        (f := f) (gbar := gbar) (hbar := hbar)
        hprim hfbar hcop with
    ⟨G, H, hGdegree, _hHle, hfactor, hGmap, hHmap⟩
  exact ⟨G, H, hfactor, hGdegree, hGmap, hHmap⟩

end Valuations
end AlgebraicNumberTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.Ramification_HilbertRamification_AbsoluteValueConjugacy
attribute [-instance] _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.adicCompletionProperSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Valuation conjugacy

For a possibly infinite Galois extension `L/K`, the Galois group acts
transitively on the extensions to `L` of a nontrivial absolute value of `K`.
-/

noncomputable section

universe u v

namespace AlgebraicNumberTheory
namespace Valuations

/-- The valuation-conjugacy theorem: the Galois group acts transitively
on the exact extensions of a nontrivial valuation.  This statement covers
finite and infinite Galois extensions and both archimedean and
nonarchimedean absolute values. -/
theorem absoluteValueConjugacy
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [IsGalois K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w w' : AbsoluteValueExtension vK L) :
    ∃ σ : L ≃ₐ[K] L,
      w' = absoluteValueExtensionConjugate vK w σ := by
  rcases absoluteValueConjugacy_exists_conjugatingAlgEquiv vK hvK w w' with
    ⟨σ, hσ⟩
  exact ⟨σ, Subtype.ext hσ⟩

end Valuations
end AlgebraicNumberTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.Ramification_HilbertRamification_AlgebraicLocalization
attribute [-instance] _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.AlgebraicNumberTheory.Valuations.completionExtensionFactor_adjoinRootEquivCompletion_root _root_.AlgebraicNumberTheory.Valuations.completionTensorDecomposition_factorEquiv_one_tmul_gen _root_.AlgebraicNumberTheory.Valuations.completionTensorDecomposition_left_tmul_apply _root_.AlgebraicNumberTheory.Valuations.completionTensorMap_leftCanonicalHom_tmul_apply _root_.AlgebraicNumberTheory.Valuations.localTensorUnitsEquivCompletionProduct_apply_coe _root_.HilbertRamification.mem_absoluteValueDecompositionField_iff _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Localization and decomposition comparison for decomposition groups

For a possibly infinite Galois extension, this file constructs the canonical
isomorphism between the decomposition group of an exact absolute value and
the Galois group of the localization over the completed base field.  The
localization is algebraic, not the
whole metric completion in infinite degree.
-/

noncomputable section

universe u v

namespace HilbertRamification

open AlgebraicNumberTheory.Valuations

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

section DecompositionEquiv

variable (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
  (w : AbsoluteValueExtension vK L)

include hvK

omit hvK

variable [IsGalois K L]

include hvK

omit hvK

include hvK

omit hvK

include hvK

omit hvK

include hvK

omit hvK

include hvK

@[simp] theorem localizationRamificationGroups_decompositionGroupEquiv_symm_apply
    (τ :
      letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
      letI : SMul K w.1.Completion := hK.toSMul
      letI := AbsoluteValue.completionAlgebra vK w.1 w.2
      AbsoluteValue.algebraicLocalization vK w.1 w.2 ≃ₐ[vK.Completion]
        AbsoluteValue.algebraicLocalization vK w.1 w.2) :
    (decompositionGroupEquivAlgebraicLocalizationAut vK hvK w).symm τ =
      localizationToDecompositionGroup vK hvK w τ :=
  rfl

@[simp] theorem localizationRamificationGroups_decompositionGroupEquiv_toLocalization
    (σ : absoluteValueDecompositionGroup K w.1) (x : L) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    decompositionGroupEquivAlgebraicLocalizationAut vK hvK w σ
        (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 x) =
      AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 ((σ : L ≃ₐ[K] L) x) :=
  decompositionGroupToLocalization_toLocalization vK hvK w σ x

end DecompositionEquiv

end HilbertRamification
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_LocalBlocks_Induced
attribute [-instance] _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.AlgebraicNumberTheory.Valuations.completionExtensionFactor_adjoinRootEquivCompletion_root _root_.AlgebraicNumberTheory.Valuations.completionTensorDecomposition_factorEquiv_one_tmul_gen _root_.AlgebraicNumberTheory.Valuations.completionTensorDecomposition_left_tmul_apply _root_.AlgebraicNumberTheory.Valuations.completionTensorMap_leftCanonicalHom_tmul_apply _root_.AlgebraicNumberTheory.Valuations.localTensorUnitsEquivCompletionProduct_apply_coe _root_.HilbertRamification.mem_absoluteValueDecompositionField_iff _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Local blocks of the idele group

For a place `w` of a Galois extension above a base absolute value `v`, its
decomposition group acts on the local multiplicative group.  The product of
all conjugate local factors is therefore the induced module from that
decomposition group. This is the algebraic content of the induced local block.

The local field is expressed as the canonical algebraic localization.
For finite extensions this is the entire metric completion by
`absoluteValueExtension_finiteLocalization_eq_top`.
-/

open scoped TensorProduct

noncomputable section

namespace LocalClassFieldTheory

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open CyclicCohomology.ProfiniteCohomology.Herbrand
open CyclicCohomology

universe u v

variable {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    [IsGalois K L]

/-- The decomposition group acts on the units of the chosen local field,
through the canonical global-to-local Galois equivalence. -/
@[reducible]
noncomputable def decompositionGroupLocalUnitsAction
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L) :
    MulDistribMulAction
      (absoluteValueDecompositionGroup K w.1)
      (LocalizedCompletion vK w)ˣ :=
  MulDistribMulAction.compHom
    (LocalizedCompletion vK w)ˣ
    (decompositionGroupEquivAlgebraicLocalizationAut
      vK hvK w).toMonoidHom

omit [FiniteDimensional K L] in
@[simp]
theorem decompositionGroup_smul_localUnit_coe
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)
    (σ : absoluteValueDecompositionGroup K w.1)
    (x : (LocalizedCompletion vK w)ˣ) :
    letI :=
      decompositionGroupLocalUnitsAction vK hvK w
    ((σ • x : (LocalizedCompletion vK w)ˣ) :
        LocalizedCompletion vK w) =
      decompositionGroupEquivAlgebraicLocalizationAut
        vK hvK w σ (x : LocalizedCompletion vK w) :=
  rfl

/-- The block of local multiplicative groups above `v`, after choosing
one extension `w`.  It is the induced module from the decomposition group
at `w`. -/
abbrev LocalPlaceBlock
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L) :=
  @InducedModule
    (G := L ≃ₐ[K] L)
    (B := (LocalizedCompletion vK w)ˣ)
    inferInstance
    (absoluteValueDecompositionGroup K w.1)
    inferInstance
    (decompositionGroupLocalUnitsAction vK hvK w)

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_Completion_DegreeNormTrace
attribute [-instance] _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Compatibility of local degree, norm, and trace

The canonical decomposition of the completion tensor-product decomposition gives the sum of the local
degrees and the product/sum formulas for norm and trace.  Since the global
norm and trace lie in `K`, their Lean statements are mapped into `K_v`.
-/

noncomputable section

open scoped BigOperators TensorProduct
open ValuationTheory.Completion

namespace AlgebraicNumberTheory
namespace Valuations

universe u v

/-- Every local completion is finite-dimensional over `K_v`.  This is
derived from the completion tensor-product decomposition by projecting from its finite product. -/
theorem completionModuleFinite
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L) :
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    Module.Finite vK.Completion w.1.Completion := by
  let : ∀ w : AbsoluteValueExtension vK L,
      Algebra vK.Completion w.1.Completion :=
    fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
  let : Module.Finite vK.Completion (vK.Completion ⊗[K] L) :=
    inferInstance
  let : Module.Finite vK.Completion
      (∀ w : AbsoluteValueExtension vK L, w.1.Completion) :=
    Module.Finite.equiv (completionTensorDecomposition_left vK hvK).toLinearEquiv
  exact moduleFiniteOfPi
    (fun w : AbsoluteValueExtension vK L ↦ w.1.Completion) w

end Valuations
end AlgebraicNumberTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_Henselian_Complete
attribute [-instance] _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.AlgebraicNumberTheory.Valuations.absoluteValueExponentialValuation_apply_ne_zero _root_.AlgebraicNumberTheory.Valuations.completionExponentialSubringMap_apply _root_.AlgebraicNumberTheory.Valuations.completionResidueEquiv_residue _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Complete nonarchimedean absolute values are Henselian

The localization reduction in the ramification-localization argument passes to the completion
of a rank-one nonarchimedean absolute value.  the factorization form of Hensel's lemma already supplies the
degree-controlled factorization statement for every complete
nonarchimedean absolute value.  This file records the direct the primitive factorization definition
consequence used in the henselianity criterion.
-/

noncomputable section

namespace AlgebraicNumberTheory
namespace Valuations

/-- A complete nonarchimedean absolute value satisfies the factorization
form of Hensel's lemma from the primitive factorization definition. -/
theorem henselFactorization_of_complete
    {K : Type*} [Field K]
    (v : AbsoluteValue K ℝ)
    (hcomplete : IsCompleteForAbsoluteValue v)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v) :
    ValuationTheory.DiscreteValuationField.HenselFactorizationProperty
      (absoluteValueValuationSubring v hnonarch) := by
  intro f gbar hbar hprimitive hfactor hcoprime
  obtain ⟨G, H, hGH, hGdegree, hGresidue, hHresidue⟩ :=
    henselFactorization_complete_exists_factorization
      v hcomplete hnonarch hprimitive hfactor hcoprime
  have hproduct : gbar * hbar ≠ 0 := by
    rw [← hfactor]
    exact hprimitive
  have hgbar : gbar ≠ 0 := left_ne_zero_of_mul hproduct
  have hhbar : hbar ≠ 0 := right_ne_zero_of_mul hproduct
  have hG : G ≠ 0 := by
    intro hzero
    subst G
    simp at hGresidue
    exact hgbar hGresidue.symm
  have hH : H ≠ 0 := by
    intro hzero
    subst H
    simp at hHresidue
    exact hhbar hHresidue.symm
  have hdegree :
      H.natDegree = f.natDegree - gbar.natDegree := by
    rw [hGH, Polynomial.natDegree_mul hG hH, hGdegree,
      Nat.add_sub_cancel_left]
  exact ⟨G, H, hGdegree, hdegree.le, hGH, hGresidue, hHresidue⟩

/-- A complete nonarchimedean absolute value is Henselian in the exact sense
of the primitive factorization definition. -/
theorem henselianValuation_of_complete
    {K : Type*} [Field K]
    (v : AbsoluteValue K ℝ)
    (hcomplete : IsCompleteForAbsoluteValue v)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v) :
    ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (absoluteValueValuationSubring
        v hnonarch).valuation := by
  rw [henselianValuation_iff_henselFactorization v hnonarch]
  exact henselFactorization_of_complete v hcomplete hnonarch

end Valuations
end AlgebraicNumberTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.Ramification_HilbertRamification_DecompositionFieldLocalization
attribute [-instance] _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.LocalClassFieldTheory.decompositionGroup_smul_localUnit_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Decomposition-field value and residue comparison

This file identifies the decomposition field with the literal intersection
`L ∩ K_v` inside the algebraic localization `L_w`.  It then records the
canonical residue-field isomorphism and equality of absolute-value ranges in
the nonarchimedean case.
-/

noncomputable section

universe u v

namespace HilbertRamification

open AlgebraicNumberTheory.Valuations

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

section LocalizationGalois

variable [IsGalois K L]
variable (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
  (w : AbsoluteValueExtension vK L)

local instance proposition98CompletionBaseAlgebra_rb6e731_1 : Algebra K w.1.Completion :=
  AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
local instance proposition98CompletionBaseSMul_rb6e731_1 : SMul K w.1.Completion :=
  (AbsoluteValue.extensionCompletionAlgebra (K := K) w.1).toSMul
local instance proposition98CompletionAlgebra : Algebra vK.Completion w.1.Completion :=
  AbsoluteValue.completionAlgebra vK w.1 w.2

abbrev localization_p0 : IntermediateField vK.Completion w.1.Completion :=
  AbsoluteValue.algebraicLocalization vK w.1 w.2

abbrev toLocalization_p0 : L →+* localization_p0 vK w :=
  AbsoluteValue.toAlgebraicLocalization vK w.1 w.2

local instance proposition98LocalizationBaseAlgebra : Algebra K (localization_p0 vK w) :=
  ((algebraMap vK.Completion (localization_p0 vK w)).comp
    (algebraMap K vK.Completion)).toAlgebra

local instance proposition98LocalizationScalarTower :
    IsScalarTower K vK.Completion (localization_p0 vK w) :=
  IsScalarTower.of_algebraMap_eq' (by
    ext x
    rfl)

/-- The dense copy of `L` in the localization, as a `K`-algebra embedding
for the scalar tower `K → K_v → L_w`. -/
def decompositionField_toLocalizationAlgHom :
    L →ₐ[K] localization_p0 vK w where
  __ := toLocalization_p0 vK w
  commutes' x := AbsoluteValue.toAlgebraicLocalization_algebraMap vK w.1 w.2 x

omit [IsGalois K L] in
/-- The localization is generated over `K_v` by the subtype-valued copy of
`L`, not only by its ambient-completion representatives. -/
theorem decompositionField_localization_adjoin_range_eq_top :
    IntermediateField.adjoin vK.Completion
      (Set.range (toLocalization_p0 vK w)) = ⊤ := by
  let E := localization_p0 vK w
  apply IntermediateField.lift_injective E
  rw [IntermediateField.lift_adjoin, IntermediateField.lift_top]
  change IntermediateField.adjoin vK.Completion
      (Subtype.val '' Set.range (toLocalization_p0 vK w)) =
    AbsoluteValue.algebraicLocalization vK w.1 w.2
  congr 1
  ext z
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨toLocalization_p0 vK w x, ⟨x, rfl⟩, rfl⟩

omit hvK in
/-- Every generator coming from `L` is separable over `K_v`. -/
theorem decompositionField_toLocalization_isSeparable (x : L) :
    IsSeparable vK.Completion (toLocalization_p0 vK w x) := by
  have hx : IsSeparable K
      (decompositionField_toLocalizationAlgHom vK w x) :=
    (Algebra.IsSeparable.isSeparable K x).map
      (decompositionField_toLocalizationAlgHom vK w)
      (decompositionField_toLocalizationAlgHom vK w).injective
  exact IsSeparable.tower_top vK.Completion hx

omit hvK in
/-- Every generator coming from `L` has its `K_v`-minimal polynomial split
inside the localization. -/
theorem decompositionField_toLocalization_minpoly_splits (x : L) :
    ((minpoly vK.Completion (toLocalization_p0 vK w x)).map
      (algebraMap vK.Completion (localization_p0 vK w))).Splits := by
  let i := decompositionField_toLocalizationAlgHom vK w
  have hxint : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  have hsK : ((minpoly K x).map
      (algebraMap K (localization_p0 vK w))).Splits := by
    have hi : i.toRingHom.comp (algebraMap K L) =
        algebraMap K (localization_p0 vK w) := i.comp_algebraMap
    have hs := (Normal.splits (F := K) (K := L) inferInstance x).map
      i.toRingHom
    simpa only [Polynomial.map_map, hi] using hs
  have hsTower : (((minpoly K x).map (algebraMap K vK.Completion)).map
      (algebraMap vK.Completion (localization_p0 vK w))).Splits := by
    simpa only [Polynomial.map_map,
      IsScalarTower.algebraMap_eq K vK.Completion (localization_p0 vK w)] using hsK
  have hdvd : minpoly vK.Completion (toLocalization_p0 vK w x) ∣
      (minpoly K x).map (algebraMap K vK.Completion) := by
    have h := minpoly.dvd_map_of_isScalarTower K vK.Completion
      (toLocalization_p0 vK w x)
    have hmin : minpoly K (toLocalization_p0 vK w x) = minpoly K x :=
      minpoly.algHom_eq i i.injective x
    rwa [hmin] at h
  exact hsTower.of_dvd
    (Polynomial.map_ne_zero
      (Polynomial.map_ne_zero (minpoly.ne_zero hxint)))
    ((Polynomial.map_dvd_map' _).mpr hdvd)

omit hvK in
/-- The algebraic localization of a Galois extension is normal over the
completed base field, with no finite-degree hypothesis. -/
theorem decompositionField_localization_normal :
    Normal vK.Completion (localization_p0 vK w) := by
  let : Algebra.IsAlgebraic vK.Completion (localization_p0 vK w) :=
    AbsoluteValue.algebraicLocalization_isAlgebraic vK w.1 w.2
  rw [normal_iff]
  intro z
  refine ⟨Algebra.IsIntegral.isIntegral z, ?_⟩
  apply IntermediateField.splits_of_mem_adjoin
      (F := vK.Completion) (K := localization_p0 vK w)
      (L := localization_p0 vK w)
      (S := Set.range (toLocalization_p0 vK w))
  · intro y hy
    rcases hy with ⟨x, rfl⟩
    exact ⟨(decompositionField_toLocalization_isSeparable vK w x).isIntegral,
      decompositionField_toLocalization_minpoly_splits vK w x⟩
  · rw [decompositionField_localization_adjoin_range_eq_top vK w]
    trivial

omit hvK in
/-- The algebraic localization of a Galois extension is separable over the
completed base field, with no finite-degree hypothesis. -/
theorem decompositionField_localization_separable :
    Algebra.IsSeparable vK.Completion (localization_p0 vK w) := by
  let S := Set.range (toLocalization_p0 vK w)
  have hS : Algebra.IsSeparable vK.Completion
      (IntermediateField.adjoin vK.Completion S) :=
    (IntermediateField.isSeparable_adjoin_iff_isSeparable
      (F := vK.Completion) (E := localization_p0 vK w)).mpr fun y hy => by
      rcases hy with ⟨x, rfl⟩
      exact decompositionField_toLocalization_isSeparable vK w x
  let : Algebra.IsSeparable vK.Completion
      (IntermediateField.adjoin vK.Completion S) := hS
  refine ⟨fun z => ?_⟩
  have hz : z ∈ IntermediateField.adjoin vK.Completion S := by
    rw [decompositionField_localization_adjoin_range_eq_top vK w]
    trivial
  exact IntermediateField.isSeparable_of_mem_isSeparable vK.Completion
    (localization_p0 vK w) hz

omit hvK in
/-- The algebraic localization of a Galois extension is Galois over `K_v`.
This permits the fixed-field argument in infinite degree. -/
theorem algebraicLocalization_isGalois :
    IsGalois vK.Completion (localization_p0 vK w) :=
  isGalois_iff.mpr
    ⟨decompositionField_localization_separable vK w,
      decompositionField_localization_normal vK w⟩

/-- The copy of `K_v` as an actual subfield of the algebraic localization. -/
abbrev decompositionField_completionImageSubfield :
    Subfield (localization_p0 vK w) :=
  (algebraMap vK.Completion (localization_p0 vK w)).fieldRange

include hvK

/-- The decomposition-field extension comparison, comap form: an element of `L` lies in the
decomposition field exactly when its image in `L_w` belongs to the embedded
copy of `K_v`. -/
theorem decompositionField_decompositionField_eq_completionImage_comap :
    (decompositionField_completionImageSubfield vK w).comap
        (toLocalization_p0 vK w) =
      (absoluteValueDecompositionField K w.1).toSubfield := by
  let : IsGalois vK.Completion (localization_p0 vK w) :=
    algebraicLocalization_isGalois vK w
  ext x
  change toLocalization_p0 vK w x ∈
      Set.range (algebraMap vK.Completion (localization_p0 vK w)) ↔
    x ∈ absoluteValueDecompositionField K w.1
  rw [InfiniteGalois.mem_range_algebraMap_iff_fixed,
    mem_absoluteValueDecompositionField_iff]
  constructor
  · intro hfixed σ hσ
    let δ : absoluteValueDecompositionGroup K w.1 := ⟨σ, hσ⟩
    apply (toLocalization_p0 vK w).injective
    calc
      toLocalization_p0 vK w (σ x) =
          decompositionGroupEquivAlgebraicLocalizationAut vK hvK w δ
            (toLocalization_p0 vK w x) :=
        (localizationRamificationGroups_decompositionGroupEquiv_toLocalization
          vK hvK w δ x).symm
      _ = toLocalization_p0 vK w x := hfixed _
  · intro hZ τ
    let δ : absoluteValueDecompositionGroup K w.1 :=
      (decompositionGroupEquivAlgebraicLocalizationAut vK hvK w).symm τ
    have hδ : ((δ : L ≃ₐ[K] L) x) = x := hZ δ δ.property
    calc
      τ (toLocalization_p0 vK w x) =
          decompositionGroupEquivAlgebraicLocalizationAut vK hvK w δ
            (toLocalization_p0 vK w x) := by
        rw [MulEquiv.apply_symm_apply]
      _ = toLocalization_p0 vK w ((δ : L ≃ₐ[K] L) x) :=
        localizationRamificationGroups_decompositionGroupEquiv_toLocalization
          vK hvK w δ x
      _ = toLocalization_p0 vK w x := congrArg (toLocalization_p0 vK w) hδ

omit hvK

omit [IsGalois K L] in
/-- Nonarchimedeanness passes from the exact base valuation to its extension
`w`; this uses only the bounded-natural-number definition. -/
theorem absoluteValueExtension_nonarchimedean_of_base
    (hv : LubinTate.Valuations.NonarchimedeanAbsoluteValue vK) :
    LubinTate.Valuations.NonarchimedeanAbsoluteValue w.1 := by
  rcases hv with ⟨C, hC⟩
  refine ⟨C, fun n => ?_⟩
  have hext := w.2 (n : K)
  simpa using hext.trans_le (hC n)

omit [IsGalois K L] in
/-- Nonarchimedeanness also passes to the restriction of `w` to `Z_w`. -/
theorem decompositionField_decompositionField_nonarchimedean
    (hv : LubinTate.Valuations.NonarchimedeanAbsoluteValue vK) :
    LubinTate.Valuations.NonarchimedeanAbsoluteValue
      (AlgebraicNumberTheory.Valuations.absoluteValueRestrictIntermediateField w.1
        (absoluteValueDecompositionField K w.1)) := by
  rcases absoluteValueExtension_nonarchimedean_of_base vK w hv with ⟨C, hC⟩
  exact ⟨C, fun n => by simpa using hC n⟩

/-- The norm absolute value on `K_v` is nonarchimedean whenever `v` is. -/
theorem decompositionField_completion_nonarchimedean
    (hv : LubinTate.Valuations.NonarchimedeanAbsoluteValue vK) :
    LubinTate.Valuations.NonarchimedeanAbsoluteValue
      (AbsoluteValue.completionAbsoluteValue vK) :=
  (AbsoluteValue.isNonarchimedean_iff_bounded_nat
    (AbsoluteValue.completionAbsoluteValue vK)).1
    (AbsoluteValue.completionAbsoluteValue_isNonarchimedean vK
      ((AbsoluteValue.isNonarchimedean_iff_bounded_nat vK).2 hv))

include hvK

omit hvK

/-- The valuation subring of `w|Z_w`. -/
abbrev decompositionField_decompositionFieldValuationSubring
    (hv : LubinTate.Valuations.NonarchimedeanAbsoluteValue vK) :
    _root_.ValuationSubring (absoluteValueDecompositionField K w.1) :=
  absoluteValueValuationSubring
    (AlgebraicNumberTheory.Valuations.absoluteValueRestrictIntermediateField w.1
      (absoluteValueDecompositionField K w.1))
    (decompositionField_decompositionField_nonarchimedean vK w hv)

/-- The canonical local homomorphism between the two valuation subrings in
the decomposition-field extension comparison. -/
def decompositionField_decompositionField_integerMap
    (hv : LubinTate.Valuations.NonarchimedeanAbsoluteValue vK) :
    decompositionField_baseValuationSubring vK hv →+*
      decompositionField_decompositionFieldValuationSubring vK w hv := by
  let Z := absoluteValueDecompositionField K w.1
  let AK := decompositionField_baseValuationSubring vK hv
  let AZ := decompositionField_decompositionFieldValuationSubring vK w hv
  apply RingHom.codRestrict ((algebraMap K Z).comp AK.subtype) AZ
  intro x
  rw [mem_absoluteValueValuationSubring_iff]
  change w.1 (algebraMap Z L (algebraMap K Z x)) ≤ 1
  rw [← IsScalarTower.algebraMap_apply K Z L, w.2]
  exact (mem_absoluteValueValuationSubring_iff
    vK hv x).mp x.property

omit [IsGalois K L] in
@[simp] theorem decompositionField_decompositionField_integerMap_apply
    (hv : LubinTate.Valuations.NonarchimedeanAbsoluteValue vK)
    (x : decompositionField_baseValuationSubring vK hv) :
    ((decompositionField_decompositionField_integerMap vK w hv x :
        decompositionField_decompositionFieldValuationSubring vK w hv) :
      absoluteValueDecompositionField K w.1) =
      algebraMap K (absoluteValueDecompositionField K w.1) (x : K) :=
  rfl

/-- The valuation-ring map in the decomposition-field extension comparison is local. -/
instance decompositionField_decompositionField_integerMap_isLocalHom
    (hv : LubinTate.Valuations.NonarchimedeanAbsoluteValue vK) :
    IsLocalHom (decompositionField_decompositionField_integerMap vK w hv) where
  map_nonunit x hx := by
    rw [← IsLocalRing.notMem_maximalIdeal] at hx ⊢
    intro hxmax
    apply hx
    have hxabs : vK (x : K) < 1 :=
      (absoluteValueValuationSubring_mem_maximalIdeal_iff_abs_lt_one
        vK hv x).mp hxmax
    rw [absoluteValueValuationSubring_mem_maximalIdeal_iff_abs_lt_one]
    rw [decompositionField_decompositionField_integerMap_apply]
    change w.1 (algebraMap
      (absoluteValueDecompositionField K w.1) L
      (algebraMap K (absoluteValueDecompositionField K w.1) (x : K))) < 1
    rw [← IsScalarTower.algebraMap_apply K
      (absoluteValueDecompositionField K w.1) L, w.2]
    exact hxabs

/-- The induced canonical map of actual residue fields. -/
def decompositionField_decompositionField_residueMap
    (hv : LubinTate.Valuations.NonarchimedeanAbsoluteValue vK) :
    IsLocalRing.ResidueField (decompositionField_baseValuationSubring vK hv) →+*
      IsLocalRing.ResidueField
        (decompositionField_decompositionFieldValuationSubring vK w hv) :=
  IsLocalRing.ResidueField.map
    (decompositionField_decompositionField_integerMap vK w hv)

include hvK

/-- The canonical residue-field map in the decomposition-field extension comparison is surjective.
The proof chooses a representative in `K_v`, then approximates
it modulo the maximal ideal by an element of `K`. -/
theorem decompositionField_decompositionField_residueMap_surjective
    (hv : LubinTate.Valuations.NonarchimedeanAbsoluteValue vK) :
    Function.Surjective
      (decompositionField_decompositionField_residueMap vK w hv) := by
  let Z := absoluteValueDecompositionField K w.1
  let AK := decompositionField_baseValuationSubring vK hv
  let AZ := decompositionField_decompositionFieldValuationSubring vK w hv
  let f := decompositionField_decompositionField_integerMap vK w hv
  let aK := AbsoluteValue.completionAbsoluteValue vK
  let aE := AbsoluteValue.algebraicLocalizationAbsoluteValue vK w.1 w.2
  let vId : AbsoluteValueExtension vK K := ⟨vK, fun _ => rfl⟩
  intro q
  obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective q
  have hzmem : ((z : Z) : L) ∈ Z.toSubfield := (z : Z).property
  rw [← decompositionField_decompositionField_eq_completionImage_comap
    vK hvK w] at hzmem
  rcases hzmem with ⟨y, hy⟩
  have hzle :
      (AlgebraicNumberTheory.Valuations.absoluteValueRestrictIntermediateField w.1 Z)
        (z : Z) ≤ 1 :=
    (mem_absoluteValueValuationSubring_iff
      _ (decompositionField_decompositionField_nonarchimedean vK w hv) _).mp
        z.property
  have hyle : aK y ≤ 1 := by
    calc
      aK y = aE (algebraMap vK.Completion (localization_p0 vK w) y) :=
        (AbsoluteValue.algebraicLocalizationAbsoluteValue_extends vK w.1 w.2 y).symm
      _ = aE (toLocalization_p0 vK w ((z : Z) : L)) := by rw [hy]
      _ = w.1 ((z : Z) : L) :=
        AbsoluteValue.algebraicLocalizationAbsoluteValue_toAlgebraicLocalization vK w.1 w.2 _
      _ ≤ 1 := hzle
  obtain ⟨x, hx⟩ :=
    (AbsoluteValue.denseRange_toCompletion vId.1).exists_dist_lt
      y (show (0 : ℝ) < 1 by norm_num)
  have hclose : aK (y - algebraMap K vK.Completion x) < 1 := by
    change ‖y - AbsoluteValue.toCompletion vId.1 x‖ < 1
    simpa only [dist_eq_norm] using hx
  have hstrong : LubinTate.Valuations.StrongTriangle aK :=
    LubinTate.Valuations.strong_triangle_of_nonarchimedean aK
      (decompositionField_completion_nonarchimedean vK hv)
  have hxle : aK (algebraMap K vK.Completion x) ≤ 1 := by
    calc
      aK (algebraMap K vK.Completion x) =
          aK (y + -(y - algebraMap K vK.Completion x)) := by
        congr 1
        ring
      _ ≤ max (aK y) (aK (-(y - algebraMap K vK.Completion x))) :=
        hstrong _ _
      _ = max (aK y) (aK (y - algebraMap K vK.Completion x)) := by
        rw [AbsoluteValue.map_neg]
      _ ≤ 1 := max_le hyle hclose.le
  have hxbase : vK x ≤ 1 := by
    rw [← AbsoluteValue.completionAbsoluteValue_coe vK x]
    exact hxle
  let xA : AK :=
    ⟨x, (mem_absoluteValueValuationSubring_iff
      vK hv x).mpr hxbase⟩
  refine ⟨IsLocalRing.residue AK xA, ?_⟩
  change IsLocalRing.ResidueField.map f (IsLocalRing.residue AK xA) =
    IsLocalRing.residue AZ z
  rw [IsLocalRing.ResidueField.map_residue]
  rw [ValuationTheory.DiscreteValuationField.ResidueField.residue_eq_residue_iff_sub_mem_maximalIdeal]
  rw [absoluteValueValuationSubring_mem_maximalIdeal_iff_abs_lt_one]
  calc
    (AlgebraicNumberTheory.Valuations.absoluteValueRestrictIntermediateField w.1 Z)
        (((f xA : AZ) : Z) - (z : Z)) =
      aE (toLocalization_p0 vK w
        ((((f xA : AZ) : Z) - (z : Z) : Z) : L)) :=
        (AbsoluteValue.algebraicLocalizationAbsoluteValue_toAlgebraicLocalization vK w.1 w.2 _).symm
    _ = aE (algebraMap vK.Completion (localization_p0 vK w)
        (algebraMap K vK.Completion x - y)) := by
      congr 1
      rw [map_sub (algebraMap vK.Completion (localization_p0 vK w))]
      dsimp [f]
      dsimp [xA]
      rw [map_sub, AbsoluteValue.toAlgebraicLocalization_algebraMap, ← hy]
    _ = aK (algebraMap K vK.Completion x - y) :=
      AbsoluteValue.algebraicLocalizationAbsoluteValue_extends vK w.1 w.2 _
    _ = aK (y - algebraMap K vK.Completion x) := by
      rw [← AbsoluteValue.map_neg]
      congr 1
      ring
    _ < 1 := hclose

/-- The decomposition-field extension comparison, residue-field form: the canonical residue map is an
isomorphism of the actual residue fields. -/
def decompositionField_decompositionField_residueFieldEquiv
    (hv : LubinTate.Valuations.NonarchimedeanAbsoluteValue vK) :
    IsLocalRing.ResidueField (decompositionField_baseValuationSubring vK hv) ≃+*
      IsLocalRing.ResidueField
        (decompositionField_decompositionFieldValuationSubring vK w hv) :=
  ValuationTheory.DiscreteValuationField.ResidueField.ringEquivOfSurjective
    (decompositionField_decompositionField_integerMap vK w hv)
    (decompositionField_decompositionField_residueMap_surjective vK hvK w hv)

@[simp] theorem decompositionField_decompositionField_residueFieldEquiv_apply
    (hv : LubinTate.Valuations.NonarchimedeanAbsoluteValue vK)
    (x : IsLocalRing.ResidueField
      (decompositionField_baseValuationSubring vK hv)) :
    decompositionField_decompositionField_residueFieldEquiv vK hvK w hv x =
      decompositionField_decompositionField_residueMap vK w hv x :=
  rfl

end LocalizationGalois

end HilbertRamification
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_LocalizedCompletionCohomology_Algebra
attribute [-instance] _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Algebra for localized completion cohomology

This file provides named algebra, finite-dimensional, Galois, scalar-tower, and
global-to-local embedding providers for localized completions.
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

universe u v

variable {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L]

/-- The canonical algebra structure on an algebraic localization over the
completed base.  Naming this instance keeps clients from rebuilding the
completion tower at every declaration boundary. -/
@[reducible]
noncomputable def localizedCompletionBaseAlgebra
    (vK : AbsoluteValue K ℝ)
    (w : AbsoluteValueExtension vK L) :
    Algebra vK.Completion (LocalizedCompletion vK w) := by
  letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  letI : SMul K w.1.Completion := hK.toSMul
  letI : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  exact inferInstance

/-- The algebra structure on the algebraic localization induced by the tower
`K → K_v → L_w`. -/
@[reducible]
noncomputable def localizedCompletionGlobalAlgebra
    (vK : AbsoluteValue K ℝ)
    (w : AbsoluteValueExtension vK L) :
    letI : Algebra vK.Completion (LocalizedCompletion vK w) :=
      localizedCompletionBaseAlgebra vK w
    Algebra K (LocalizedCompletion vK w) := by
  letI : Algebra vK.Completion (LocalizedCompletion vK w) :=
    localizedCompletionBaseAlgebra vK w
  exact
    ((algebraMap vK.Completion
        (LocalizedCompletion vK w)).comp
      (algebraMap K vK.Completion)).toAlgebra


end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_LocalizedCompletionCohomology_Generator
attribute [-instance] _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.adicCompletionProperSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# A generator of a localized finite Galois group
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

universe u v

variable {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L]
    [IsGalois K L] [FiniteDimensional K L]

/-- The canonical finite structure on the decomposition group used by the
localized low-degree cohomology calculations. -/
@[reducible]
noncomputable def localizedCompletionDecompositionGroupFintype
    (vK : AbsoluteValue K ℝ)
    (w : AbsoluteValueExtension vK L) :
    Fintype (absoluteValueDecompositionGroup K w.1) :=
  Fintype.ofFinite _

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_NormApproximation_FinitePlaces
attribute [-instance] _root_.OAI.PrimeDegreePackets.matrixSecondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Weak approximation for actual local norm quotients

For a finite Galois extension `L / K` and a finite set `S` of finite
places of `K`, this file chooses an actual extension of every `v ∈ S`,
forms the corresponding algebraic localization `L_w / K_v`, and
transports its local norm subgroup to mathlib's concrete adic
completion.  These transported norm subgroups are open.  Multiplicative
weak approximation therefore gives a surjection

`Kˣ → ∏ v ∈ S, K_vˣ / N(L_wˣ)`.

All choices are made from the extension theorem for absolute values;
none of the local conclusions is included as input data.
-/

open scoped NumberField Classical NNReal
open NumberField IsDedekindDomain

noncomputable section

open LocalClassFieldTheory


open AlgebraicNumberTheory.Valuations
open LocalClassFieldTheory
open LocalFieldTheory

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- The chosen extension of the `v`-adic absolute value to `L`.
The embedding is supplied by algebraic closedness of the completion's
algebraic closure. -/
noncomputable def chosenFinitePlaceExtension
    (v : HeightOneSpectrum (𝓞 K)) :
    AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L :=
  pullbackAbsoluteValueExtension
    (NumberField.HeightOneSpectrum.adicAbv K v)
    (RayClass.adicAbv_isNontrivial v)
    IsAlgClosed.lift
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_LocalBlocks_Tensor
attribute [-instance] _root_.HilbertRamification.decompositionField_decompositionField_integerMap_isLocalHom _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.HilbertRamification.decompositionField_decompositionField_integerMap_apply _root_.HilbertRamification.decompositionField_decompositionField_residueFieldEquiv_apply _root_.HilbertRamification.mem_absoluteValueDecompositionField_iff _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The tensor-product realization of a local induced block

This file connects the induced module in `LocalBlock` with the actual local
factor of the scalar-extended adele algebra.  The natural Galois action on
`K_v ⊗[K] L` is conjugation on the second tensor factor. The completion tensor-product theorem
identifies this algebra with the product of the completions above `v`.

The first part records the natural tensor action and the canonical
identifications between completions at conjugate absolute values.  These
identifications are the concrete source of the induced-module covariance in
the induced local-block calculation.
-/

open scoped TensorProduct

noncomputable section

namespace LocalClassFieldTheory

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open CyclicCohomology

universe u v

variable {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    [IsGalois K L]

omit [FiniteDimensional K L] [IsGalois K L] in
@[simp]
theorem conjugateCompletionRingEquiv_toCompletion
    (w : AbsoluteValue L ℝ) (σ : L ≃ₐ[K] L) (x : L) :
    conjugateCompletionRingEquiv w σ
        (AbsoluteValue.toCompletion
          (absoluteValueConjugate w σ) x) =
      AbsoluteValue.toCompletion w (σ x) := by
  change
    UniformSpace.Completion.mapRingEquiv
        (conjugateWithAbsRingEquiv w σ)
        (conjugateWithAbsRingEquiv_isometry w σ).continuous
        (conjugateWithAbsRingEquiv_symm_isometry w σ).continuous
      (((WithAbs.equiv
        (absoluteValueConjugate w σ)).symm x :
          WithAbs (absoluteValueConjugate w σ)) :
        (absoluteValueConjugate w σ).Completion) = _
  rw [UniformSpace.Completion.mapRingEquiv_apply,
    UniformSpace.Completion.map_coe
      (conjugateWithAbsRingEquiv_isometry w σ).uniformContinuous]
  rfl

/-- The conjugate-completion equivalence with its source indexed by the
corresponding element of `AbsoluteValueExtension`.  This wrapper keeps
dependent product components definitionally aligned. -/
noncomputable def conjugateExtensionCompletionRingEquiv
    (vK : AbsoluteValue K ℝ)
    (w : AbsoluteValueExtension vK L)
    (σ : L ≃ₐ[K] L) :
    (absoluteValueExtensionConjugate vK w σ).1.Completion ≃+*
      w.1.Completion := by
  change
    (absoluteValueConjugate w.1 σ).Completion ≃+*
      w.1.Completion
  exact conjugateCompletionRingEquiv w.1 σ

omit [FiniteDimensional K L] [IsGalois K L] in
@[simp]
theorem conjugateExtensionCompletionRingEquiv_toCompletion
    (vK : AbsoluteValue K ℝ)
    (w : AbsoluteValueExtension vK L)
    (σ : L ≃ₐ[K] L) (x : L) :
    conjugateExtensionCompletionRingEquiv vK w σ
        (AbsoluteValue.toCompletion
          (absoluteValueExtensionConjugate vK w σ).1 x) =
      AbsoluteValue.toCompletion w.1 (σ x) := by
  change
    conjugateCompletionRingEquiv w.1 σ
        (AbsoluteValue.toCompletion
          (absoluteValueConjugate w.1 σ) x) =
      AbsoluteValue.toCompletion w.1 (σ x)
  exact conjugateCompletionRingEquiv_toCompletion w.1 σ x

/-- Evaluation of the local tensor algebra in the chosen completion,
with codomain written in the algebraic-localization model used by
`LocalPlaceBlock`. -/
noncomputable def localTensorEvaluation
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    LocalTensorAlgebra (L := L) vK →ₐ[vK.Completion]
      LocalizedCompletion vK w := by
  letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  letI : SMul K w.1.Completion := hK.toSMul
  letI := AbsoluteValue.completionAlgebra vK w.1 w.2
  exact
    (localizedCompletionEquivCompletion vK hvK w).symm.toAlgHom.comp
      (absoluteValueExtension_localizationTensorHom vK w)

omit [IsGalois K L] in
@[simp]
theorem localTensorEvaluation_tmul
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)
    (b : vK.Completion) (x : L) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    localTensorEvaluation vK hvK w (b ⊗ₜ[K] x) =
      algebraMap vK.Completion (LocalizedCompletion vK w) b *
        AbsoluteValue.toAlgebraicLocalization
          vK w.1 w.2 x := by
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let _ : SMul K w.1.Completion := hK.toSMul
  let _ := AbsoluteValue.completionAlgebra vK w.1 w.2
  apply (localizedCompletionEquivCompletion vK hvK w).injective
  rw [map_mul]
  simp only [localTensorEvaluation, AlgHom.coe_comp, Function.comp_apply,
    absoluteValueExtension_localizationTensorHom_tmul]
  rfl

section ExtensionOrbit

variable (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)

local notation "G" => L ≃ₐ[K] L

/-- The chosen representative of a right coset sends `w` to a well-defined
extension above `v`. -/
noncomputable def rightCosetExtension
    (q : InducedRightCosets
      (absoluteValueDecompositionGroup K w.1)) :
    AbsoluteValueExtension vK L :=
  absoluteValueExtensionConjugate vK w (Quotient.out q)

omit [FiniteDimensional K L] [IsGalois K L] in
include hvK in
theorem rightCosetExtension_eq_of_mk
    (g : G) :
    rightCosetExtension vK w
        (Quotient.mk'' g : InducedRightCosets
          (absoluteValueDecompositionGroup K w.1)) =
      absoluteValueExtensionConjugate vK w g := by
  let q : InducedRightCosets
      (absoluteValueDecompositionGroup K w.1) := Quotient.mk'' g
  let h : absoluteValueDecompositionGroup K w.1 :=
    rightCosetCoefficient (absoluteValueDecompositionGroup K w.1) g
  have hfix :
      absoluteValueExtensionConjugate vK w h.1 = w :=
    (mem_absoluteValueDecompositionGroup_iff_extensionConjugate_eq
      vK hvK w h.1).mp h.2
  have hg :
      h.1 * Quotient.out q = g :=
    rightCosetCoefficient_mul_out
      (absoluteValueDecompositionGroup K w.1) g
  apply Subtype.ext
  ext x
  change w.1 (Quotient.out q x) = w.1 (g x)
  rw [← hg]
  change w.1 (Quotient.out q x) =
    w.1 (h.1 (Quotient.out q x))
  have hp :
      w.1 (h.1 (Quotient.out q x)) =
        w.1 (Quotient.out q x) := by
    have hp' := congrArg
      (fun z : AbsoluteValueExtension vK L =>
        z.1 (Quotient.out q x)) hfix
    change
      w.1 (h.1 (Quotient.out q x)) =
        w.1 (Quotient.out q x) at hp'
    exact hp'
  exact hp.symm

/-- Transitivity of extensions, sharpened to the orbit equivalence
`H \ G ≃ {w' | w' ∣ v}`. -/
noncomputable def rightCosetExtensionEquiv :
    InducedRightCosets (absoluteValueDecompositionGroup K w.1) ≃
      AbsoluteValueExtension vK L := by
  apply Equiv.ofBijective (rightCosetExtension vK w)
  constructor
  · intro q r hqr
    have hmem :
        Quotient.out r * (Quotient.out q)⁻¹ ∈
          absoluteValueDecompositionGroup K w.1 := by
      rw [mem_absoluteValueDecompositionGroup_iff_extensionConjugate_eq
        vK hvK w]
      apply Subtype.ext
      ext x
      change
        w.1 (Quotient.out r ((Quotient.out q)⁻¹ x)) =
          w.1 x
      have hp :
          w.1 (Quotient.out q ((Quotient.out q)⁻¹ x)) =
            w.1 (Quotient.out r ((Quotient.out q)⁻¹ x)) := by
        have hp' := congrArg
          (fun z : AbsoluteValueExtension vK L =>
            z.1 ((Quotient.out q)⁻¹ x)) hqr
        change
          w.1 (Quotient.out q ((Quotient.out q)⁻¹ x)) =
            w.1 (Quotient.out r ((Quotient.out q)⁻¹ x))
          at hp'
        exact hp'
      simpa using hp.symm
    have hout :
        (Quotient.mk'' (Quotient.out q) :
          InducedRightCosets
            (absoluteValueDecompositionGroup K w.1)) =
          Quotient.mk'' (Quotient.out r) := by
      apply Quotient.sound'
      exact QuotientGroup.rightRel_apply.mpr hmem
    calc
      q = Quotient.mk'' (Quotient.out q) :=
        (Quotient.out_eq' q).symm
      _ = Quotient.mk'' (Quotient.out r) := hout
      _ = r := Quotient.out_eq' r
  · intro w'
    obtain ⟨g, hg⟩ := absoluteValueConjugacy vK hvK w w'
    refine ⟨Quotient.mk'' g, ?_⟩
    exact (rightCosetExtension_eq_of_mk vK hvK w g).trans hg.symm

omit [FiniteDimensional K L] in
@[simp]
theorem rightCosetExtensionEquiv_apply
    (q : InducedRightCosets
      (absoluteValueDecompositionGroup K w.1)) :
    rightCosetExtensionEquiv vK hvK w q =
      absoluteValueExtensionConjugate
        vK w (Quotient.out q) :=
  rfl

end ExtensionOrbit

section ProductEquivalences

variable (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)

/-- Reindex the product of all completion unit groups by the right cosets
of the decomposition group. -/
noncomputable def completionProductReindexRightCosets :
    (∀ w' : AbsoluteValueExtension vK L, w'.1.Completionˣ) ≃*
      (∀ q : InducedRightCosets
          (absoluteValueDecompositionGroup K w.1),
        ((rightCosetExtensionEquiv vK hvK w q).1.Completion)ˣ) := by
  let e :=
    Equiv.piCongrLeft'
      (fun w' : AbsoluteValueExtension vK L =>
        w'.1.Completionˣ)
      (rightCosetExtensionEquiv vK hvK w).symm
  exact
    { e with
      map_mul' := by
        intro x y
        funext q
        rfl }

/-- For a right coset, conjugation by its chosen representative identifies
the corresponding completion with the fixed completion at `w`. -/
noncomputable def rightCosetCompletionUnitsEquiv
    (q : InducedRightCosets
      (absoluteValueDecompositionGroup K w.1)) :
    ((rightCosetExtensionEquiv vK hvK w q).1.Completion)ˣ ≃*
      w.1.Completionˣ := by
  exact Units.mapEquiv
    (conjugateExtensionCompletionRingEquiv
      vK w (Quotient.out q)).toMulEquiv

omit [FiniteDimensional K L] in
@[simp]
theorem rightCosetCompletionUnitsEquiv_apply_coe
    (q : InducedRightCosets
      (absoluteValueDecompositionGroup K w.1))
    (z :
      ((rightCosetExtensionEquiv vK hvK w q).1.Completion)ˣ) :
    ((rightCosetCompletionUnitsEquiv vK hvK w q z :
        w.1.Completionˣ) : w.1.Completion) =
      conjugateExtensionCompletionRingEquiv
        vK w (Quotient.out q)
        (z :
          (rightCosetExtensionEquiv vK hvK w q).1.Completion) :=
  rfl

/-- The product supplied by the completion tensor-product decomposition, rewritten as one copy of the
chosen local multiplicative group for every right coset. -/
noncomputable def completionProductUnitsEquivRightCosets :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    (∀ w' : AbsoluteValueExtension vK L, w'.1.Completionˣ) ≃*
      (InducedRightCosets
          (absoluteValueDecompositionGroup K w.1) →
        (LocalizedCompletion vK w)ˣ) := by
  letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  letI : SMul K w.1.Completion := hK.toSMul
  letI := AbsoluteValue.completionAlgebra vK w.1 w.2
  exact
    (completionProductReindexRightCosets vK hvK w).trans
      ((MulEquiv.piCongrRight fun q : InducedRightCosets
          (absoluteValueDecompositionGroup K w.1) =>
        rightCosetCompletionUnitsEquiv vK hvK w q).trans
        (MulEquiv.piCongrRight fun _ : InducedRightCosets
            (absoluteValueDecompositionGroup K w.1) =>
          (Units.mapEquiv
            (localizedCompletionEquivCompletion
              vK hvK w).toMulEquiv).symm))

@[simp]
theorem completionProductUnitsEquivRightCosets_apply_coe
    (p : ∀ w' : AbsoluteValueExtension vK L,
      w'.1.Completionˣ)
    (q : InducedRightCosets
      (absoluteValueDecompositionGroup K w.1)) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    ((completionProductUnitsEquivRightCosets vK hvK w p q :
        (LocalizedCompletion vK w)ˣ) :
      LocalizedCompletion vK w) =
      (localizedCompletionEquivCompletion vK hvK w).symm
        (conjugateExtensionCompletionRingEquiv
          vK w (Quotient.out q)
          ((p (rightCosetExtensionEquiv vK hvK w q) :
              (rightCosetExtensionEquiv vK hvK w q).1.Completionˣ) :
            (rightCosetExtensionEquiv vK hvK w q).1.Completion)) := by
  rfl

end ProductEquivalences

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_LocalBlocks_TensorNorm
attribute [-instance] _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.adicCompletionProperSpace
attribute [-simp] _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The norm image of a local tensor factor

For a finite Galois extension `L / K`, the completion tensor-product theorem decomposes

`K_v ⊗[K] L`

as the product of the completions above `v`.  After choosing one extension
`w`, Galois conjugation identifies every factor with `L_w`.  Consequently
the image of the determinant norm on the tensor algebra is exactly the field
norm subgroup of `L_w / K_v`.

This is the concrete norm-subgroup form of the local calculation used in
the local-block norm calculation, and it is also the bridge between the local cohomology
calculation and multiplicative weak approximation.
-/

open scoped BigOperators TensorProduct

noncomputable section

namespace LocalClassFieldTheory

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalFieldTheory
open ValuationTheory.Completion

universe u

variable {K L : Type u}
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

section ChosenCompletion

variable (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)

/-- The finite set of right cosets of the decomposition group.  It is
packaged explicitly so statements about products do not depend on a chosen
`Fintype` structure for the quotient. -/
noncomputable def decompositionRightCosetsFinset :
    Finset
      (InducedRightCosets
        (absoluteValueDecompositionGroup K w.1)) :=
  @Finset.univ _ (Fintype.ofFinite _)

omit [IsGalois K L] in
@[simp]
theorem mem_decompositionRightCosetsFinset
    (q : InducedRightCosets
      (absoluteValueDecompositionGroup K w.1)) :
    q ∈ decompositionRightCosetsFinset
      (K := K) (vK := vK) (w := w) := by
  simp [decompositionRightCosetsFinset]

end ChosenCompletion

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Adele_IntegralTensorSupport_AbsoluteValue
attribute [-instance] _root_.OAI.PrimeDegreePackets.matrixSecondCountable
attribute [-simp] _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Integral lattices for the relative tensor basis

This file continues the finite-support construction for relative tensor
decompositions.  A single nonzero integer is chosen which carries every
vector of the fixed `K`-basis of `L` into `𝓞 L`.  Their
`𝓞 K`-span is a full lattice in `𝓞 L`.

The quotient of `𝓞 L` by this lattice is then proved directly to be a
finite torsion `𝓞 K`-module.  A nonzero element of its annihilator
therefore gives an actual finite set of bad height-one primes.  Outside
that set the scaled lattice generates the localization of `𝓞 L` over
the local ring of `K`.

Finally, a universe-polymorphic comparison between the absolute-value
and adic models of `K_v` carries this result through the canonical local tensor decomposition.
Away from the same bad set, the chosen basis-integral lattice maps into
the product of the completion valuation rings; applying the statement
to a unit and its inverse gives the actual product of local integer
unit groups needed in the finite-support decomposition.
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

/-- Every extension of a nonarchimedean absolute value is again
nonarchimedean.  For algebraic extensions this follows already from
the bounded-natural-number criterion and the extension identity. -/
theorem absoluteValueExtension_isNonarchimedean
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (vF : AbsoluteValue F ℝ)
    (hvF : IsNonarchimedean (vF : F → ℝ))
    (w : AbsoluteValueExtension vF E) :
    IsNonarchimedean (w.1 : E → ℝ) := by
  rw [AbsoluteValue.isNonarchimedean_iff_bounded_nat]
  refine ⟨1, ?_⟩
  intro n
  calc
    w.1 (n : E) =
        w.1 (algebraMap F E (n : F)) := by simp
    _ = vF (n : F) := w.2 (n : F)
    _ ≤ 1 :=
      hvF.apply_natCast_le_one

/-- The valuation ring in the completion of a nonarchimedean
real-absolute-valued field. -/
noncomputable def absoluteValueCompletionIntegers
    {F : Type*} [Field F]
    (vF : AbsoluteValue F ℝ)
    (hvF : IsNonarchimedean (vF : F → ℝ)) :
    ValuationSubring vF.Completion :=
  (realAbsoluteValueValuation
    (AbsoluteValue.completionAbsoluteValue vF)
    (AbsoluteValue.completionAbsoluteValue_isNonarchimedean
      vF hvF)).valuationSubring

/-- Membership in the absolute-value completion integers is the valuation bound. -/
@[simp]
theorem mem_absoluteValueCompletionIntegers_iff
    {F : Type*} [Field F]
    (vF : AbsoluteValue F ℝ)
    (hvF : IsNonarchimedean (vF : F → ℝ))
    (x : vF.Completion) :
    x ∈ absoluteValueCompletionIntegers vF hvF ↔
      ‖x‖ ≤ 1 :=
  Iff.rfl
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Ramification_Splitting_FinitePlace
attribute [-instance] _root_.OAI.PrimeDegreePackets.matrixSecondCountable
attribute [-simp] _root_.LocalClassFieldTheory.completionProductUnitsEquivRightCosets_apply_coe _root_.LocalClassFieldTheory.conjugateExtensionCompletionRingEquiv_toCompletion _root_.LocalClassFieldTheory.localTensorEvaluation_tmul _root_.LocalClassFieldTheory.mem_decompositionRightCosetsFinset _root_.LocalClassFieldTheory.rightCosetCompletionUnitsEquiv_apply_coe _root_.LocalClassFieldTheory.rightCosetExtensionEquiv_apply _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Decomposition groups and complete splitting at finite places

For a finite Galois extension of number fields `L / K`, this file
attaches an actual decomposition subgroup to every finite place of
`K`.  The extension of the adic absolute value is the one constructed
in `LocalNormApproximation`; no place above `v` is supplied as an
additional hypothesis.

The stabilizer is identified with the automorphism group of the algebraic
localization. The finite-localization theorem supplies finite dimensionality,
so the order of
the decomposition group is exactly the local degree.  Consequently
complete splitting is equivalent both to cardinality one and to local
degree one.
-/

open scoped NumberField Classical
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- The actual decomposition subgroup at the chosen extension of the
finite place `v`. -/
noncomputable def finitePlaceDecompositionGroup
    (v : HeightOneSpectrum (𝓞 K)) :
    Subgroup (L ≃ₐ[K] L) :=
  absoluteValueDecompositionGroup K
    (chosenFinitePlaceExtension (L := L) v).1

omit [FiniteDimensional K L] in
/-- Membership in the finite-place decomposition group is exactly
stabilization of the chosen extension of the absolute value. -/
@[simp]
theorem mem_finitePlaceDecompositionGroup_iff
    (v : HeightOneSpectrum (𝓞 K))
    (σ : L ≃ₐ[K] L) :
    σ ∈ finitePlaceDecompositionGroup
        (K := K) (L := L) v ↔
      absoluteValueExtensionConjugate
          (NumberField.HeightOneSpectrum.adicAbv K v)
          (chosenFinitePlaceExtension (L := L) v) σ =
        chosenFinitePlaceExtension (L := L) v := by
  exact
    mem_absoluteValueDecompositionGroup_iff_extensionConjugate_eq
      (NumberField.HeightOneSpectrum.adicAbv K v)
      (RayClass.adicAbv_isNontrivial v)
      (chosenFinitePlaceExtension (L := L) v) σ
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Galois_CyclicPrimeSubextension
attribute [-instance] _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.matrixSecondCountable
attribute [-simp] _root_.LocalClassFieldTheory.completionProductUnitsEquivRightCosets_apply_coe _root_.LocalClassFieldTheory.conjugateExtensionCompletionRingEquiv_toCompletion _root_.LocalClassFieldTheory.localTensorEvaluation_tmul _root_.LocalClassFieldTheory.mem_decompositionRightCosetsFinset _root_.LocalClassFieldTheory.rightCosetCompletionUnitsEquiv_apply_coe _root_.LocalClassFieldTheory.rightCosetExtensionEquiv_apply _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The prime-degree subextension of a cyclic prime-power extension

This file constructs a prime-degree intermediate field.
For a nontrivial cyclic Galois extension whose group has order
`p ^ exponent`, the index-`p` subgroup constructed in
`SplittingGroupTheory` is sent through the finite Galois
correspondence.  Its fixed field is an actual cyclic Galois extension
of the base of degree `p`.

The finite-place decomposition group in that subextension is obtained
by restricting the decomposition group of `L / K`.  Thus complete
splitting descends to the prime-degree subextension, and nonsplitting
there ascends to `L`.
-/

open scoped NumberField Classical IsMulCommutative
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations
open HilbertRamification

section ValuationRestriction

variable {F E : Type}
    [Field F] [Field E] [Algebra F E]

/-- Restrict an actual extension of an absolute value to an
intermediate field. -/
def restrictAbsoluteValueExtensionToIntermediate
    (vF : AbsoluteValue F ℝ)
    (w : AbsoluteValueExtension vF E)
    (M : IntermediateField F E) :
    AbsoluteValueExtension vF M where
  val :=
    w.1.comp (f := M.val.toRingHom)
      M.val.injective
  property x := by
    change w.1 (algebraMap F E x) = vF x
    exact w.2 x

@[simp]
theorem restrictAbsoluteValueExtensionToIntermediate_apply
    (vF : AbsoluteValue F ℝ)
    (w : AbsoluteValueExtension vF E)
    (M : IntermediateField F E)
    (x : M) :
    (restrictAbsoluteValueExtensionToIntermediate
      vF w M).1 x = w.1 x :=
  rfl

end ValuationRestriction
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Ramification_Splitting_NormalClosure
attribute [-instance] _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.matrixSecondCountable
attribute [-simp] _root_.LocalClassFieldTheory.completionProductUnitsEquivRightCosets_apply_coe _root_.LocalClassFieldTheory.conjugateExtensionCompletionRingEquiv_toCompletion _root_.LocalClassFieldTheory.localTensorEvaluation_tmul _root_.LocalClassFieldTheory.mem_decompositionRightCosetsFinset _root_.LocalClassFieldTheory.rightCosetCompletionUnitsEquiv_apply_coe _root_.LocalClassFieldTheory.rightCosetExtensionEquiv_apply _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Complete splitting and normal closures

This file formalizes the normal-closure reduction for complete splitting.
For a finite Galois extension `M / K`, an intermediate field `L`, a
nontrivial absolute value `v` of `K`, and an extension `w` to `M`, put

* `G = Gal(M / K)`,
* `H = Gal(M / L)`, and
* `D = D(w / v)`.

Restriction of the conjugates of `w` gives an equivalence

`H \ G / D ≃ { extensions of v to L }`.

Thus the intrinsic complete-splitting condition for the possibly
non-Galois extension `L / K` is exactly the equality between the number
of double cosets and the number of left cosets.  If `M` is generated by
the `K`-conjugates of `L`, then `H` has trivial normal core.
`SplittingGroupTheory` consequently forces `D = 1`, so the place splits
completely already in `M`.
-/

open scoped NumberField Classical
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations
open HilbertRamification

section AbsoluteValueExtensions

variable {K M : Type}
    [Field K] [Field M] [Algebra K M]

/-- Extend an actual extension of `v` from an intermediate field to the
ambient finite Galois extension.  The source is the absolute-value
extension theorem, applied to the algebraic extension `M / L`. -/
noncomputable def extendAbsoluteValueExtensionFromIntermediate
    [FiniteDimensional K M]
    (vK : AbsoluteValue K ℝ)
    (hvK : vK.IsNontrivial)
    (L : IntermediateField K M)
    (u : AbsoluteValueExtension vK L) :
    AbsoluteValueExtension vK M := by
  let : Module.IsTorsionFree L
      (absoluteValueExtension_algebraicCompletionClosure u.1) :=
    DivisionSemiring.to_moduleIsTorsionFree
  let hu : u.1.IsNontrivial :=
    u.isNontrivial hvK
  let wL : AbsoluteValueExtension u.1 M :=
    pullbackAbsoluteValueExtension
      u.1 hu IsAlgClosed.lift
  exact
    { val := wL.1
      property := by
        intro x
        rw [IsScalarTower.algebraMap_apply K L M,
          wL.2, u.2] }

@[simp]
theorem extendAbsoluteValueExtensionFromIntermediate_apply
    [FiniteDimensional K M]
    (vK : AbsoluteValue K ℝ)
    (hvK : vK.IsNontrivial)
    (L : IntermediateField K M)
    (u : AbsoluteValueExtension vK L)
    (x : L) :
    (extendAbsoluteValueExtensionFromIntermediate
      vK hvK L u).1 x = u.1 x := by
  let : Module.IsTorsionFree L
      (absoluteValueExtension_algebraicCompletionClosure u.1) :=
    DivisionSemiring.to_moduleIsTorsionFree
  change
    (pullbackAbsoluteValueExtension
      u.1 (u.isNontrivial hvK)
        IsAlgClosed.lift).1
      (algebraMap L M x) = u.1 x
  exact
    (pullbackAbsoluteValueExtension
      u.1 (u.isNontrivial hvK)
        IsAlgClosed.lift).2 x

variable (vK : AbsoluteValue K ℝ)
    (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK M)
    (L : IntermediateField K M)

local notation "G" => M ≃ₐ[K] M
local notation "H" => L.fixingSubgroup
local notation "D" => absoluteValueDecompositionGroup K w.val

/-- The extension of `v` to `L` attached to a representative of
`H \ G / D`.  Inversion changes the natural `D \ G / H` convention for
the right action `w ↦ w ∘ σ` into the convention used for the normal-closure reduction. -/
noncomputable def doubleCosetExtension :
    DoubleCoset.Quotient (H : Set G) D →
      AbsoluteValueExtension vK L :=
  Quotient.lift
    (fun g : G ↦
      restrictAbsoluteValueExtensionToIntermediate
        vK
        (absoluteValueExtensionConjugate
          vK w g⁻¹)
        L)
    (by
      intro g r hgr
      change
        DoubleCoset.setoid (H : Set G) (D : Set G) g r
        at hgr
      rw [DoubleCoset.rel_iff] at hgr
      obtain ⟨h, hh, d, hd, rfl⟩ := hgr
      apply Subtype.ext
      ext x
      change
        w.1 (g⁻¹ (x : M)) =
          w.1 (d⁻¹ (g⁻¹ (h⁻¹ (x : M))))
      have hhInv : h⁻¹ ∈ H :=
        L.fixingSubgroup.inv_mem hh
      have hfix : h⁻¹ (x : M) = (x : M) :=
        hhInv x
      rw [hfix]
      have hdInv : d⁻¹ ∈ D :=
        (absoluteValueDecompositionGroup K w.val).inv_mem hd
      have hdEq :=
        (mem_absoluteValueDecompositionGroup_iff_extensionConjugate_eq
          vK hvK w d⁻¹).mp hdInv
      have hvalue :=
        congrArg
          (fun z : AbsoluteValueExtension vK M ↦
            z.1 (g⁻¹ (x : M)))
          hdEq
      exact hvalue.symm)

@[simp]
theorem doubleCosetExtension_mk
    (g : G) :
    doubleCosetExtension vK hvK w L
        (DoubleCoset.mk H D g) =
      restrictAbsoluteValueExtensionToIntermediate
        vK
        (absoluteValueExtensionConjugate
          vK w g⁻¹)
        L :=
  rfl

end AbsoluteValueExtensions

section CompleteSplitting

variable {K E : Type}
    [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E]

/-- Intrinsic complete splitting for an arbitrary finite extension:
the number of actual extensions of the absolute value is the full
degree.  Unlike a decomposition-group definition, this remains correct
when `E / K` is not Galois. -/
def AbsoluteValueSplitsCompletelyInExtension
    (vK : AbsoluteValue K ℝ) : Prop :=
  Nat.card (AbsoluteValueExtension vK E) =
    Module.finrank K E

end CompleteSplitting
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_LocalBlocks_Family_Instances
attribute [-instance] _root_.HilbertRamification.decompositionField_decompositionField_integerMap_isLocalHom _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.adicCompletionProperSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Finite families of local idele blocks

This file combines the local induced-module calculation over a finite
family of places. It is the finite-support part of the localized class formation.
-/

noncomputable section

namespace LocalClassFieldTheory

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open CyclicCohomology.ProfiniteCohomology.Herbrand
open CyclicCohomology

universe u v w

variable (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- A chosen extension `w` of a nontrivial base absolute value.  These are
exactly the concrete inputs needed to form one local block. -/
structure LocalPlaceDatum where
  /-- The base absolute value. -/
  base : AbsoluteValue K ℝ
  /-- Nontriviality of the base absolute value. -/
  base_isNontrivial : base.IsNontrivial
  /-- A chosen extension of the base absolute value to `L`. -/
  extension : AbsoluteValueExtension base L

variable {K L}

/-- Product of the local blocks attached to a family of chosen places. -/
abbrev LocalBlockFamily {ι : Type w}
    (d : ι → LocalPlaceDatum K L) :=
  ∀ i, LocalPlaceBlock
    (d i).base (d i).base_isNontrivial
    (d i).extension


/-- Canonical componentwise decomposition-group action for a local-block
family. -/
@[reducible]
noncomputable def localBlockFamilyLocalAction
    {ι : Type w} (d : ι → LocalPlaceDatum K L) :
    ∀ i, MulDistribMulAction
      (absoluteValueDecompositionGroup K (d i).extension.1)
      (LocalizedCompletion
        (d i).base (d i).extension)ˣ :=
  fun i =>
    decompositionGroupLocalUnitsAction
      (d i).base (d i).base_isNontrivial
      (d i).extension

/-- Canonical induced action on every local block in a family. -/
@[reducible]
noncomputable def localBlockFamilyBlockAction
    {ι : Type w} (d : ι → LocalPlaceDatum K L) :
    ∀ i, MulDistribMulAction (L ≃ₐ[K] L)
      (LocalPlaceBlock
        (d i).base (d i).base_isNontrivial
        (d i).extension) := by
  letI := localBlockFamilyLocalAction d
  exact fun i =>
    inducedMulDistribMulAction
      (absoluteValueDecompositionGroup K
        (d i).extension.1)

/-- Canonical componentwise action on the product of a local-block family. -/
@[reducible]
noncomputable def localBlockFamilyCohomologyAction
    {ι : Type w} (d : ι → LocalPlaceDatum K L) :
    MulDistribMulAction (L ≃ₐ[K] L)
      (LocalBlockFamily d) := by
  letI := localBlockFamilyLocalAction d
  letI := localBlockFamilyBlockAction d
  exact
    piMulDistribMulAction (L ≃ₐ[K] L)
      (fun i ↦ LocalPlaceBlock
        (d i).base (d i).base_isNontrivial
        (d i).extension)

/-- Canonical finite structures on the decomposition groups in a local-block
family. -/
@[reducible]
noncomputable def localBlockFamilyDecompositionFintype
    {ι : Type w} (d : ι → LocalPlaceDatum K L) :
    ∀ i, Fintype
      (absoluteValueDecompositionGroup K
        (d i).extension.1) :=
  fun _ => Fintype.ofFinite _

end LocalClassFieldTheory
end
end


