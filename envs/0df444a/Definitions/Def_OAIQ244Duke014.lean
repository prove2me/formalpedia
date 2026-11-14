-- Prove2me | Definitions.Def_OAIQ244Duke014
-- name    : OAIQ244Duke014
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T06:15:15.842872+00:00
-- url     : https://prove2.me/theorems/5c6d4263-be4f-49f7-8220-c206c5a165f4
-- title:
--   Definitions bundle OAIQ244Duke014 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 70 declarations of OpenAI's Lean: 24 definitions and 46 theorems. The definitions and types are `AlgebraicNumberTheory.Valuations.absoluteValueExtensionConjugate`, `AlgebraicNumberTheory.Valuations.absoluteValueExtension_localizationEmbeddingOfPullback`, `AlgebraicNumberTheory.Valuations.completionExponentialSubringMap`, `AlgebraicNumberTheory.Valuations.completionExtensionFactor_extensionEquivFactors`, `AlgebraicNumberTheory.Valuations.completionExtensionFactor_extensionsEquivCompletionFactorsAux`, `AlgebraicNumberTheory.Valuations.completionExtensionFactor_extensionsEquivEmbeddingClasses`, `AlgebraicNumberTheory.Valuations.completionExtensionFactor_extensionsEquivMinpolyFactors`, `AlgebraicNumberTheory.Valuations.completionExtensionFactor_minpolyFactorsEquivCompletionFactors`, `AlgebraicNumberTheory.Valuations.completionResidueEquiv`, `AlgebraicNumberTheory.Valuations.completionTensorDecomposition_extensionFintype`, `AlgebraicNumberTheory.Valuations.completionTensorDecomposition_factorEquiv`, `AlgebraicNumberTheory.Valuations.completionTensorDecomposition_left`, `AlgebraicNumberTheory.Valuations.completionTensorMap_leftCanonicalHom`, `AlgebraicNumberTheory.Valuations.localTensorUnitsEquivCompletionProduct`, `AlgebraicNumberTheory.Valuations.pullbackAbsoluteValueExtension`, `HilbertRamification.decompositionField_baseValuationSubring`, `HilbertRamification.decompositionGroupEquivAlgebraicLocalizationAut`, `HilbertRamification.decompositionGroupToLocalization`, `HilbertRamification.localizationAlgEquivRestrict`, `HilbertRamification.localizationToDecompositionGroup`, `HilbertRamification.valuationPreservingCompletionRingEquiv`, `HilbertRamification.valuationPreservingLocalizationAlgEquiv`, `HilbertRamification.valuationPreservingWithAbsRingEquiv`, `OAI.PrimeDegreePackets.packetSupport`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `PrimePackets_PacketMoments`, `Ramification_HilbertRamification_AbsoluteValueConjugacy`, `Ramification_HilbertRamification_AlgebraicLocalization`, `Ramification_HilbertRamification_DecompositionFieldLocalization`, `Ramification_HilbertRamification_DecompositionGroup`, `Valuation_Completion_AbsoluteValueExtensions`, `Valuation_Completion_CanonicalTensorMap`, `Valuation_Completion_ExtensionFactorClassification`, `Valuation_Completion_ExtensionInvariants`, `Valuation_Completion_PolynomialFactors`, `Valuation_Completion_SeparablePolynomialFactors`, `Valuation_Completion_TensorProductDecomposition`, `Valuation_Henselian_Factorization_Step`.
--
--   **Imports.** It imports the published bundle `Def_DukePrimeDegree`; the bundles `OAIQ244Duke000`, `OAIQ244Duke001`, `OAIQ244Duke002` and `OAIQ244Duke011` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ244Duke025`; the proof of `OAI.PrimeDegreePackets.packet_tight_of_zeta_scale`.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.CharP.Subring
import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Algebra.Module.Shrink
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.Algebra.Order.WithTop.Untop0
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.Analysis.Normed.Algebra.GelfandMazur
import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.Analysis.Normed.Field.WithAbs
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.Trace
import Mathlib.NumberTheory.Ostrowski
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Adjoin.PowerBasis
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.IsPrincipalPowQuotient
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Polynomial.ContentIdeal
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.TensorProduct.Maps
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
import Mathlib.Topology.UniformSpace.AbsoluteValue
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke000
import Definitions.Def_OAIQ244Duke001
import Definitions.Def_OAIQ244Duke002
import Definitions.Def_OAIQ244Duke011

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_PacketMoments
attribute [-instance] _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
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
namespace PrimeDegreePackets
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

open scoped Matrix
open Matrix

open TopologicalSpace
open scoped Topology

def packetSupport {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K) : Set (X (d+1)) :=
  ⋃ O : packetOrbits M σ, O.1

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_Henselian_Factorization_Step
attribute [-instance] _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
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

/-- existence of one recursive Hensel step from the current
error factor in the displayed-factor principal-element form.  The chosen `π`
only has to lie in the maximal ideal; the needed congruence modulo `(π)` is
carried as an invariant and is produced from the displayed finite-minimum
Bezout-error factor. -/
theorem henselFactorization_exists_one_step_update_of_mem_span
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
  have hdegree : g0.natDegree = gbar.natDegree := by
    rw [hg0nat, hgbar_nat]
  rcases henselFactorization_division_by_lifted_factor_degree_lt
      (g0 := g0) (gbar := gbar) hg0map hdegree hglead (b * fn) with
    ⟨qdiv, p, hdiv, hpdeg⟩
  have hpNat : p.natDegree ≤ m :=
    henselFactorization_remainder_natDegree_le_of_degree_lt
      (R := R) (g0 := g0) (p := p) hg0nat hpdeg
  have hgunit : IsUnit g0.leadingCoeff :=
    henselFactorization_lift_leadingCoeff_isUnit_of_natDegree_eq
      hg0map hdegree hglead
  have hfn : fn.natDegree ≤ d :=
    henselFactorization_error_factor_natDegree_le
      (π := π) hπn hf hgdeg hhdeg hmd hfactor
  rcases henselFactorization_one_step_update_from_division_data_of_mem_span
      (π := π) hn hπmem hfactor hg hh hgunit hg0nat
      hbezFactor hdiv hfn hh0 hpNat hmd with
    ⟨hqdeg, hgNext, hhNext, hgNextMax, hhNextMax, hnext⟩
  rcases hnext with ⟨fnNext, hfactorNext⟩
  exact ⟨p, henselFactorization_lowPart (d - m) (a * fn + h0 * qdiv), fnNext,
    hpNat, hqdeg, hgNext, hhNext, hgNextMax, hhNextMax, hfactorNext⟩


end Valuations
end AlgebraicNumberTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_Completion_AbsoluteValueExtensions
attribute [-instance] _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Extension of valuations to finite field extensions

The setup uses nontrivial real-valued absolute values throughout.  For an
absolute value `v` on `K`, we use mathlib's completion `v.Completion` and its
concrete algebraic closure.  The absolute value `bar v` on that algebraic
closure is produced by the unique-extension unique extension theorem, not supplied as an
extra hypothesis.
-/

noncomputable section

open scoped Topology

namespace AlgebraicNumberTheory
namespace Valuations

universe u v

/-- The image of the localization under the completed embedding lies in the
dense algebraic closure inside its completion. -/
theorem absoluteValueExtension_embeddingCompletionAlgHom_mem_range
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)
    (tau : L →ₐ[K] absoluteValueExtension_algebraicCompletionClosure vK)
    (htau : w.1 = absoluteValueExtension_pullback vK hvK tau)
    (z : AbsoluteValue.algebraicLocalization vK w.1 w.2) :
    letI := absoluteValueExtension_algebraicClosureCompletionAlgebra vK hvK
    absoluteValueExtension_embeddingCompletionAlgHom vK hvK w tau htau (z : w.1.Completion)
      ∈ (absoluteValueExtension_algebraicClosureToCompletionAlgHom vK hvK).range := by
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let := AbsoluteValue.completionAlgebra vK w.1 w.2
  let := absoluteValueExtension_algebraicClosureCompletionAlgebra vK hvK
  let E := AbsoluteValue.algebraicLocalization vK w.1 w.2
  let F := absoluteValueExtension_embeddingCompletionAlgHom vK hvK w tau htau
  let j := absoluteValueExtension_algebraicClosureToCompletionAlgHom vK hvK
  change F (z : w.1.Completion) ∈ j.range
  apply IntermediateField.adjoin_induction
      (F := vK.Completion)
      (s := Set.range (AbsoluteValue.toCompletion w.1))
      (p := fun x _ => F x ∈ j.range)
      (x := (z : w.1.Completion))
  · intro x hx
    rcases hx with ⟨y, rfl⟩
    refine ⟨tau y, ?_⟩
    symm
    change absoluteValueExtension_embeddingCompletionMap vK hvK w tau htau
      (AbsoluteValue.toCompletion w.1 y) =
        absoluteValueExtension_algebraicClosureToCompletionRingHom vK hvK (tau y)
    change absoluteValueExtension_embeddingCompletionMap vK hvK w tau htau
      (((WithAbs.equiv w.1).symm y : WithAbs w.1) : w.1.Completion) = _
    rw [absoluteValueExtension_embeddingCompletionMap_coe]
    rfl
  · intro x
    refine ⟨algebraMap vK.Completion
      (absoluteValueExtension_algebraicCompletionClosure vK) x, ?_⟩
    exact (absoluteValueExtension_embeddingCompletionMap_completionMap
      vK hvK w tau htau x).symm
  · intro x y _ _ hx hy
    simpa only [map_add] using j.range.add_mem hx hy
  · intro x _ hx
    rcases hx with ⟨a, ha⟩
    refine ⟨a⁻¹, ?_⟩
    simpa only [map_inv₀] using congrArg Inv.inv ha
  · intro x y _ _ hx hy
    simpa only [map_mul] using j.range.mul_mem hx hy
  · exact z.property

/-- A valuation-preserving embedding `tau : L → \bar K_v` extends to a
`K_v`-embedding of the common localization.  The construction first extends
to metric completions and then factors through the actual dense copy of
`\bar K_v`; no completeness of the algebraic closure is assumed. -/
noncomputable def absoluteValueExtension_localizationEmbeddingOfPullback
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)
    (tau : L →ₐ[K] absoluteValueExtension_algebraicCompletionClosure vK)
    (htau : w.1 = absoluteValueExtension_pullback vK hvK tau) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    AbsoluteValue.algebraicLocalization vK w.1 w.2 →ₐ[vK.Completion]
      absoluteValueExtension_algebraicCompletionClosure vK := by
  letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  letI : SMul K w.1.Completion := hK.toSMul
  letI := AbsoluteValue.completionAlgebra vK w.1 w.2
  letI := absoluteValueExtension_algebraicClosureCompletionAlgebra vK hvK
  let E := AbsoluteValue.algebraicLocalization vK w.1 w.2
  let F := absoluteValueExtension_embeddingCompletionAlgHom vK hvK w tau htau
  let j := absoluteValueExtension_algebraicClosureToCompletionAlgHom vK hvK
  let f : E →ₐ[vK.Completion] j.range :=
    (F.comp E.val).codRestrict j.range
      (absoluteValueExtension_embeddingCompletionAlgHom_mem_range
        vK hvK w tau htau)
  exact (AlgEquiv.ofInjectiveField j).symm.toAlgHom.comp f

/-- The extended localization embedding restricts to the original `tau` on
the dense copy of `L`. -/
theorem absoluteValueExtension_localizationEmbeddingOfPullback_toLocalization
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)
    (tau : L →ₐ[K] absoluteValueExtension_algebraicCompletionClosure vK)
    (htau : w.1 = absoluteValueExtension_pullback vK hvK tau)
    (x : L) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    absoluteValueExtension_localizationEmbeddingOfPullback vK hvK w tau htau
        (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 x) = tau x := by
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let := AbsoluteValue.completionAlgebra vK w.1 w.2
  let := absoluteValueExtension_algebraicClosureCompletionAlgebra vK hvK
  let E := AbsoluteValue.algebraicLocalization vK w.1 w.2
  let F := absoluteValueExtension_embeddingCompletionAlgHom vK hvK w tau htau
  let j := absoluteValueExtension_algebraicClosureToCompletionAlgHom vK hvK
  apply j.injective
  change j ((AlgEquiv.ofInjectiveField j).symm
      ⟨F (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 x),
        absoluteValueExtension_embeddingCompletionAlgHom_mem_range
          vK hvK w tau htau _⟩) = j (tau x)
  rw [show j ((AlgEquiv.ofInjectiveField j).symm
      ⟨F (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 x),
        absoluteValueExtension_embeddingCompletionAlgHom_mem_range
          vK hvK w tau htau _⟩) =
      F (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 x) by
        exact congrArg Subtype.val
          ((AlgEquiv.ofInjectiveField j).apply_symm_apply _)]
  change absoluteValueExtension_embeddingCompletionMap vK hvK w tau htau
      (AbsoluteValue.toCompletion w.1 x) =
    absoluteValueExtension_algebraicClosureToCompletionRingHom vK hvK (tau x)
  change absoluteValueExtension_embeddingCompletionMap vK hvK w tau htau
      (((WithAbs.equiv w.1).symm x : WithAbs w.1) : w.1.Completion) = _
  rw [absoluteValueExtension_embeddingCompletionMap_coe]
  rfl

/-- The difficult direction of clause (ii) of the valuation-extension theorem: equality of pullback absolute
values forces conjugacy over `K_v`. -/
theorem absoluteValueExtension_conjugate_of_pullback_eq
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    {tau tau' : L →ₐ[K] absoluteValueExtension_algebraicCompletionClosure vK}
    (h : absoluteValueExtension_pullback vK hvK tau =
      absoluteValueExtension_pullback vK hvK tau') :
    AbsoluteValueExtensionConjugateOverCompletion vK tau tau' := by
  let w : AbsoluteValueExtension vK L :=
    ⟨absoluteValueExtension_pullback vK hvK tau,
      absoluteValueExtension_pullback_extends vK hvK tau⟩
  have htau : w.1 = absoluteValueExtension_pullback vK hvK tau := rfl
  have htau' : w.1 = absoluteValueExtension_pullback vK hvK tau' := h
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let := AbsoluteValue.completionAlgebra vK w.1 w.2
  let phi := absoluteValueExtension_localizationEmbeddingOfPullback
    vK hvK w tau htau
  let phi' := absoluteValueExtension_localizationEmbeddingOfPullback
    vK hvK w tau' htau'
  let : Algebra.IsAlgebraic vK.Completion
      (AbsoluteValue.algebraicLocalization vK w.1 w.2) :=
    AbsoluteValue.algebraicLocalization_isAlgebraic vK w.1 w.2
  obtain ⟨sigma, hsigma⟩ :=
    absoluteValueExtension_algHom_conjugate_in_algClosure phi phi'
  refine ⟨sigma, fun x => ?_⟩
  rw [← absoluteValueExtension_localizationEmbeddingOfPullback_toLocalization
      vK hvK w tau htau x,
    ← absoluteValueExtension_localizationEmbeddingOfPullback_toLocalization
      vK hvK w tau' htau' x]
  exact (hsigma (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 x)).symm

/-- Clause (ii) of the valuation-extension theorem: two embeddings induce the same extension exactly when
they are conjugate by an automorphism over the completion `K_v`. -/
theorem absoluteValueExtension_pullback_eq_iff_conjugate
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (tau tau' : L →ₐ[K] absoluteValueExtension_algebraicCompletionClosure vK) :
    absoluteValueExtension_pullback vK hvK tau =
        absoluteValueExtension_pullback vK hvK tau' ↔
      AbsoluteValueExtensionConjugateOverCompletion vK tau tau' := by
  constructor
  · exact absoluteValueExtension_conjugate_of_pullback_eq vK hvK
  · exact absoluteValueExtension_pullback_eq_of_conjugate vK hvK

end Valuations
end AlgebraicNumberTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.Ramification_HilbertRamification_AbsoluteValueConjugacy
attribute [-instance] _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial
attribute [-simp] _root_.AlgebraicNumberTheory.Valuations.absoluteValueExtension_localizationTensorHom_tmul _root_.AlgebraicNumberTheory.Valuations.completionExtensionFactor_adjoinRootEquivCompletion_root _root_.AlgebraicNumberTheory.Valuations.localizedCompletionEquivCompletion_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
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

/-- Conjugating an extension by a ground-field automorphism gives another
exact extension of the same base absolute value. -/
theorem absoluteValueConjugate_extends
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (w : AbsoluteValueExtension vK L)
    (σ : L ≃ₐ[K] L) :
    AbsoluteValue.Extends vK (absoluteValueConjugate w.1 σ) := by
  intro x
  rw [absoluteValueConjugate_apply, σ.commutes, w.2 x]

/-- The conjugated extension as an element of the exact-extension type. -/
def absoluteValueExtensionConjugate
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (w : AbsoluteValueExtension vK L)
    (σ : L ≃ₐ[K] L) : AbsoluteValueExtension vK L :=
  ⟨absoluteValueConjugate w.1 σ,
    absoluteValueConjugate_extends vK w σ⟩

/-- Equivalent exact extensions of a nontrivial base absolute value are equal.
Thus `AbsoluteValueExtension vK L` is a faithful normalized model for the
absolute-value classes lying over the class of `vK`. -/
theorem equivalent_exactExtensions_eq
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w w' : AbsoluteValueExtension vK L)
    (h : LubinTate.Valuations.EquivalentAbsoluteValues w.1 w'.1) :
    w = w' := by
  rcases (LubinTate.Valuations.equivalentAbsoluteValues_iff_exists_rpow_eq w.1 w'.1).mp h with
    ⟨s, hs, hpow⟩
  rcases hvK with ⟨a, ha, hva⟩
  have hbase : vK a ^ s = vK a := by
    have hpoint := congrFun hpow (algebraMap K L a)
    simpa [w.2 a, w'.2 a] using hpoint
  have hs_one : s = 1 :=
    (Real.rpow_right_inj (vK.pos ha) hva).mp (by simpa using hbase)
  apply Subtype.ext
  ext x
  have hpoint := congrFun hpow x
  simpa [hs_one] using hpoint

end Valuations
end AlgebraicNumberTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.Ramification_HilbertRamification_DecompositionGroup
attribute [-instance] _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Decomposition-group restriction law

This file gives the three tower-intersection formulas in their common ambient
Galois group.  The decomposition-group statement is formulated for arbitrary
absolute values, including the archimedean case.  The inertia and ramification
statements use valuation subrings and therefore cover the nonarchimedean case
in which those groups are defined.
-/

noncomputable section

universe u v w

namespace HilbertRamification

open AlgebraicNumberTheory.Valuations

variable (K : Type u) {L : Type w} [Field K] [Field L] [Algebra K L]

/-- The decomposition and inertia definition: on the normalized extension type,
the decomposition group is exactly the stabilizer of the chosen extension
under `w ↦ w ∘ σ`. -/
theorem mem_absoluteValueDecompositionGroup_iff_extensionConjugate_eq
    {K₀ : Type u} {L₀ : Type w} [Field K₀] [Field L₀] [Algebra K₀ L₀]
    (vK : AbsoluteValue K₀ ℝ) (hvK : vK.IsNontrivial)
    (vL : AbsoluteValueExtension vK L₀) (σ : L₀ ≃ₐ[K₀] L₀) :
    σ ∈ absoluteValueDecompositionGroup K₀ vL.1 ↔
      absoluteValueExtensionConjugate vK vL σ = vL := by
  rw [mem_absoluteValueDecompositionGroup_iff_equivalent]
  change
    LubinTate.Valuations.EquivalentAbsoluteValues
        (absoluteValueExtensionConjugate vK vL σ).1 vL.1 ↔ _
  constructor
  · exact equivalent_exactExtensions_eq vK hvK
      (absoluteValueExtensionConjugate vK vL σ) vL
  · intro h
    rw [h]
    exact LubinTate.Valuations.equivalentAbsoluteValues_refl vL.1

end HilbertRamification
end
end

section
-- module Solutions.OAIQ244_DUKE.Ramification_HilbertRamification_AlgebraicLocalization
attribute [-instance] _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.AlgebraicNumberTheory.Valuations.completionExtensionFactor_adjoinRootEquivCompletion_root _root_.HilbertRamification.mem_absoluteValueDecompositionField_iff _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
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

section LocalizationLift

variable (vK : AbsoluteValue K ℝ) (w : AbsoluteValueExtension vK L)

/-- The ring equivalence of the normed copy of `L` attached to an automorphism
which preserves `w`. -/
def valuationPreservingWithAbsRingEquiv
    (σ : L ≃ₐ[K] L) : WithAbs w.1 ≃+* WithAbs w.1 :=
  (WithAbs.equiv w.1).trans
    (σ.toRingEquiv.trans (WithAbs.equiv w.1).symm)

@[simp] theorem valuationPreservingWithAbsRingEquiv_apply
    (σ : L ≃ₐ[K] L) (x : L) :
    WithAbs.equiv w.1
        (valuationPreservingWithAbsRingEquiv vK w σ
          ((WithAbs.equiv w.1).symm x)) = σ x :=
  rfl

theorem valuationPreservingWithAbsRingEquiv_isometry
    (σ : L ≃ₐ[K] L) (hσ : ∀ x : L, w.1 (σ x) = w.1 x) :
    Isometry (valuationPreservingWithAbsRingEquiv vK w σ) := by
  apply AddMonoidHomClass.isometry_of_norm
  intro x
  rw [WithAbs.norm_eq_apply_ofAbs, WithAbs.norm_eq_apply_ofAbs]
  exact hσ (WithAbs.equiv w.1 x)

theorem valuationPreservingWithAbsRingEquiv_symm_isometry
    (σ : L ≃ₐ[K] L) (hσ : ∀ x : L, w.1 (σ x) = w.1 x) :
    Isometry (valuationPreservingWithAbsRingEquiv vK w σ).symm := by
  apply AddMonoidHomClass.isometry_of_norm
  intro x
  rw [WithAbs.norm_eq_apply_ofAbs, WithAbs.norm_eq_apply_ofAbs]
  have h := hσ (σ⁻¹ (WithAbs.equiv w.1 x))
  simpa [valuationPreservingWithAbsRingEquiv] using h.symm

/-- A valuation-preserving automorphism of `L` extends functorially to a ring
automorphism of the metric completion of `(L,w)`. -/
def valuationPreservingCompletionRingEquiv
    (σ : L ≃ₐ[K] L) (hσ : ∀ x : L, w.1 (σ x) = w.1 x) :
    w.1.Completion ≃+* w.1.Completion :=
  UniformSpace.Completion.mapRingEquiv
    (valuationPreservingWithAbsRingEquiv vK w σ)
    (valuationPreservingWithAbsRingEquiv_isometry vK w σ hσ).continuous
    (valuationPreservingWithAbsRingEquiv_symm_isometry vK w σ hσ).continuous

@[simp] theorem valuationPreservingCompletionRingEquiv_toCompletion
    (σ : L ≃ₐ[K] L) (hσ : ∀ x : L, w.1 (σ x) = w.1 x) (x : L) :
    valuationPreservingCompletionRingEquiv vK w σ hσ
        (AbsoluteValue.toCompletion w.1 x) =
      AbsoluteValue.toCompletion w.1 (σ x) := by
  change
    UniformSpace.Completion.mapRingEquiv
          (valuationPreservingWithAbsRingEquiv vK w σ)
          (valuationPreservingWithAbsRingEquiv_isometry vK w σ hσ).continuous
          (valuationPreservingWithAbsRingEquiv_symm_isometry vK w σ hσ).continuous
        (((WithAbs.equiv w.1).symm x : WithAbs w.1) : w.1.Completion) = _
  rw [UniformSpace.Completion.mapRingEquiv_apply,
    UniformSpace.Completion.map_coe
      (valuationPreservingWithAbsRingEquiv_isometry
        vK w σ hσ).uniformContinuous]
  rfl

/-- The extended automorphism fixes the embedded completed base field. -/
theorem valuationPreservingCompletionRingEquiv_completionMap
    (σ : L ≃ₐ[K] L) (hσ : ∀ x : L, w.1 (σ x) = w.1 x)
    (x : vK.Completion) :
    valuationPreservingCompletionRingEquiv vK w σ hσ
        (AbsoluteValue.completionMap vK w.1 w.2 x) =
      AbsoluteValue.completionMap vK w.1 w.2 x := by
  have hfun :
      (fun y : vK.Completion =>
        valuationPreservingCompletionRingEquiv vK w σ hσ
          (AbsoluteValue.completionMap vK w.1 w.2 y)) =
        AbsoluteValue.completionMap vK w.1 w.2 := by
    apply UniformSpace.Completion.ext
    · exact UniformSpace.Completion.continuous_map.comp
        (AbsoluteValue.completionMap_isometry vK w.1 w.2).continuous
    · exact (AbsoluteValue.completionMap_isometry vK w.1 w.2).continuous
    · intro y
      have hy : (y : vK.Completion) =
          algebraMap K vK.Completion (WithAbs.equiv vK y) := by
        rw [← AbsoluteValue.toCompletion_eq_algebraMap]
        simp
      rw [hy, AbsoluteValue.completionMap_coe]
      change
        valuationPreservingCompletionRingEquiv vK w σ hσ
            (AbsoluteValue.toCompletion w.1
              (algebraMap K L (WithAbs.equiv vK y))) =
          AbsoluteValue.toCompletion w.1
            (algebraMap K L (WithAbs.equiv vK y))
      rw [valuationPreservingCompletionRingEquiv_toCompletion, σ.commutes]
  exact congrFun hfun x

/-- The completion lift preserves the algebraic localization `L K_v`. -/
theorem valuationPreservingCompletionRingEquiv_mem_localization
    (σ : L ≃ₐ[K] L) (hσ : ∀ x : L, w.1 (σ x) = w.1 x)
    {z : w.1.Completion} (hz : z ∈ AbsoluteValue.algebraicLocalization vK w.1 w.2) :
    valuationPreservingCompletionRingEquiv vK w σ hσ z ∈
      AbsoluteValue.algebraicLocalization vK w.1 w.2 := by
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let := AbsoluteValue.completionAlgebra vK w.1 w.2
  let E := AbsoluteValue.algebraicLocalization vK w.1 w.2
  apply IntermediateField.adjoin_induction
      (p := fun x (_ : x ∈ E) =>
        valuationPreservingCompletionRingEquiv vK w σ hσ x ∈ E)
      (s := Set.range (AbsoluteValue.toCompletion w.1))
  · intro x hx
    rcases hx with ⟨a, rfl⟩
    rw [valuationPreservingCompletionRingEquiv_toCompletion]
    exact IntermediateField.subset_adjoin vK.Completion _ ⟨σ a, rfl⟩
  · intro x
    change
      valuationPreservingCompletionRingEquiv vK w σ hσ
          (AbsoluteValue.completionMap vK w.1 w.2 x) ∈ E
    rw [valuationPreservingCompletionRingEquiv_completionMap]
    exact E.algebraMap_mem x
  · intro x y hx hy hx' hy'
    simpa only [map_add] using E.add_mem hx' hy'
  · intro x hx hx'
    simpa only [map_inv₀] using E.inv_mem hx'
  · intro x y hx hy hx' hy'
    simpa only [map_mul] using E.mul_mem hx' hy'
  · exact hz

/-- The inverse completion lift also preserves `L K_v`. -/
theorem valuationPreservingCompletionRingEquiv_symm_mem_localization
    (σ : L ≃ₐ[K] L) (hσ : ∀ x : L, w.1 (σ x) = w.1 x)
    {z : w.1.Completion} (hz : z ∈ AbsoluteValue.algebraicLocalization vK w.1 w.2) :
    (valuationPreservingCompletionRingEquiv vK w σ hσ).symm z ∈
      AbsoluteValue.algebraicLocalization vK w.1 w.2 := by
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let := AbsoluteValue.completionAlgebra vK w.1 w.2
  let E := AbsoluteValue.algebraicLocalization vK w.1 w.2
  apply IntermediateField.adjoin_induction
      (p := fun x (_ : x ∈ E) =>
        (valuationPreservingCompletionRingEquiv vK w σ hσ).symm x ∈ E)
      (s := Set.range (AbsoluteValue.toCompletion w.1))
  · intro x hx
    rcases hx with ⟨a, rfl⟩
    have hgen := valuationPreservingCompletionRingEquiv_toCompletion
      vK w σ hσ (σ⁻¹ a)
    have hsymm :
        (valuationPreservingCompletionRingEquiv vK w σ hσ).symm
            (AbsoluteValue.toCompletion w.1 a) =
          AbsoluteValue.toCompletion w.1 (σ⁻¹ a) := by
      rw [← (valuationPreservingCompletionRingEquiv vK w σ hσ).injective.eq_iff,
        (valuationPreservingCompletionRingEquiv vK w σ hσ).apply_symm_apply]
      simpa using hgen.symm
    rw [hsymm]
    exact IntermediateField.subset_adjoin vK.Completion _ ⟨σ⁻¹ a, rfl⟩
  · intro x
    have hbase := valuationPreservingCompletionRingEquiv_completionMap
      vK w σ hσ x
    have hsymm :
        (valuationPreservingCompletionRingEquiv vK w σ hσ).symm
            (AbsoluteValue.completionMap vK w.1 w.2 x) =
          AbsoluteValue.completionMap vK w.1 w.2 x := by
      rw [← (valuationPreservingCompletionRingEquiv vK w σ hσ).injective.eq_iff,
        (valuationPreservingCompletionRingEquiv vK w σ hσ).apply_symm_apply]
      exact hbase.symm
    change
      (valuationPreservingCompletionRingEquiv vK w σ hσ).symm
          (AbsoluteValue.completionMap vK w.1 w.2 x) ∈ E
    rw [hsymm]
    exact E.algebraMap_mem x
  · intro x y hx hy hx' hy'
    simpa only [map_add] using E.add_mem hx' hy'
  · intro x hx hx'
    simpa only [map_inv₀] using E.inv_mem hx'
  · intro x y hx hy hx' hy'
    simpa only [map_mul] using E.mul_mem hx' hy'
  · exact hz

/-- A valuation-preserving automorphism of `L` extends to a
`K_v`-automorphism of the algebraic localization. -/
def valuationPreservingLocalizationAlgEquiv
    (σ : L ≃ₐ[K] L) (hσ : ∀ x : L, w.1 (σ x) = w.1 x) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    AbsoluteValue.algebraicLocalization vK w.1 w.2 ≃ₐ[vK.Completion]
      AbsoluteValue.algebraicLocalization vK w.1 w.2 := by
  letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  letI : SMul K w.1.Completion := hK.toSMul
  letI := AbsoluteValue.completionAlgebra vK w.1 w.2
  let E := AbsoluteValue.algebraicLocalization vK w.1 w.2
  let e := valuationPreservingCompletionRingEquiv vK w σ hσ
  exact
    { toFun := fun z =>
        ⟨e z, valuationPreservingCompletionRingEquiv_mem_localization
          vK w σ hσ z.property⟩
      invFun := fun z =>
        ⟨e.symm z,
          valuationPreservingCompletionRingEquiv_symm_mem_localization
            vK w σ hσ z.property⟩
      left_inv := fun z => by
        apply Subtype.ext
        exact e.symm_apply_apply z
      right_inv := fun z => by
        apply Subtype.ext
        exact e.apply_symm_apply z
      map_mul' := fun x y => by
        apply Subtype.ext
        exact e.map_mul x y
      map_add' := fun x y => by
        apply Subtype.ext
        exact e.map_add x y
      commutes' := fun x => by
        apply Subtype.ext
        exact valuationPreservingCompletionRingEquiv_completionMap
          vK w σ hσ x }

@[simp] theorem valuationPreservingLocalizationAlgEquiv_toLocalization
    (σ : L ≃ₐ[K] L) (hσ : ∀ x : L, w.1 (σ x) = w.1 x) (x : L) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    valuationPreservingLocalizationAlgEquiv vK w σ hσ
        (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 x) =
      AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 (σ x) := by
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let := AbsoluteValue.completionAlgebra vK w.1 w.2
  apply Subtype.ext
  exact valuationPreservingCompletionRingEquiv_toCompletion vK w σ hσ x

end LocalizationLift

section DecompositionEquiv

variable (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
  (w : AbsoluteValueExtension vK L)

include hvK

/-- Membership in the decomposition group supplies equality, not merely
equivalence, of the normalized absolute-value representatives. -/
theorem absoluteValueDecompositionGroup_preserves_absoluteValue
    (σ : absoluteValueDecompositionGroup K w.1) (x : L) :
    w.1 ((σ : L ≃ₐ[K] L) x) = w.1 x := by
  have hσ :=
    (mem_absoluteValueDecompositionGroup_iff_extensionConjugate_eq
      vK hvK w (σ : L ≃ₐ[K] L)).mp σ.property
  have hx := congrArg (fun q : AbsoluteValueExtension vK L => q.1 x) hσ
  simpa [absoluteValueExtensionConjugate,
    absoluteValueConjugate, AbsoluteValue.comp] using hx

omit hvK

variable [IsGalois K L]

include hvK

/-- Every automorphism of the algebraic localization over `K_v` preserves its
unique extended absolute value. -/
theorem localizationAbsoluteValue_algEquiv
    (τ :
      letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
      letI : SMul K w.1.Completion := hK.toSMul
      letI := AbsoluteValue.completionAlgebra vK w.1 w.2
      AbsoluteValue.algebraicLocalization vK w.1 w.2 ≃ₐ[vK.Completion]
        AbsoluteValue.algebraicLocalization vK w.1 w.2)
    (x :
      letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
      letI : SMul K w.1.Completion := hK.toSMul
      letI := AbsoluteValue.completionAlgebra vK w.1 w.2
      AbsoluteValue.algebraicLocalization vK w.1 w.2) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    AbsoluteValue.algebraicLocalizationAbsoluteValue vK w.1 w.2 (τ x) =
      AbsoluteValue.algebraicLocalizationAbsoluteValue vK w.1 w.2 x := by
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let := AbsoluteValue.completionAlgebra vK w.1 w.2
  let E := AbsoluteValue.algebraicLocalization vK w.1 w.2
  let vhat := AbsoluteValue.completionAbsoluteValue vK
  let wloc := AbsoluteValue.algebraicLocalizationAbsoluteValue vK w.1 w.2
  let : Algebra.IsAlgebraic vK.Completion E :=
    AbsoluteValue.algebraicLocalization_isAlgebraic vK w.1 w.2
  let R := AbsoluteValue.uniqueAlgebraicExtension
    (K := vK.Completion) (L := E) vhat
    (AbsoluteValue.completionAbsoluteValue_complete vK)
    (AbsoluteValue.completionAbsoluteValue_isNontrivial vK hvK)
  have hwloc : wloc = R.extension := by
    apply R.unique
    intro y
    exact AbsoluteValue.algebraicLocalizationAbsoluteValue_extends vK w.1 w.2 y
  let wconj : AbsoluteValue E ℝ :=
    wloc.comp (f := τ.toRingEquiv.toRingHom) τ.injective
  have hwconj : wconj = R.extension := by
    apply R.unique
    intro y
    change wloc (τ (algebraMap vK.Completion E y)) = vhat y
    rw [τ.commutes]
    exact AbsoluteValue.algebraicLocalizationAbsoluteValue_extends vK w.1 w.2 y
  have h := congrArg (fun q : AbsoluteValue E ℝ => q x)
    (hwconj.trans hwloc.symm)
  exact h

omit hvK

/-- Restrict a local automorphism to `L`.  Normality of `L/K` ensures that
the image of the dense algebraic copy of `L` is again that copy. -/
def localizationAlgEquivRestrict
    (τ :
      letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
      letI : SMul K w.1.Completion := hK.toSMul
      letI := AbsoluteValue.completionAlgebra vK w.1 w.2
      AbsoluteValue.algebraicLocalization vK w.1 w.2 ≃ₐ[vK.Completion]
        AbsoluteValue.algebraicLocalization vK w.1 w.2) : L ≃ₐ[K] L := by
  letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  letI : SMul K w.1.Completion := hK.toSMul
  letI := AbsoluteValue.completionAlgebra vK w.1 w.2
  let E := AbsoluteValue.algebraicLocalization vK w.1 w.2
  let i : L →+* E := AbsoluteValue.toAlgebraicLocalization vK w.1 w.2
  letI : Algebra K E := (i.comp (algebraMap K L)).toAlgebra
  let iAlg : L →ₐ[K] E :=
    { __ := i
      commutes' := fun x => by
        change i (algebraMap K L x) = (i.comp (algebraMap K L)) x
        rfl }
  letI : Algebra L E := i.toAlgebra
  letI : IsScalarTower K L E :=
    IsScalarTower.of_algebraMap_eq' rfl
  let τK : E ≃ₐ[K] E :=
    { __ := τ.toRingEquiv
      commutes' := fun x => by
        change τ (i (algebraMap K L x)) = i (algebraMap K L x)
        rw [AbsoluteValue.toAlgebraicLocalization_algebraMap, τ.commutes] }
  exact Normal.algHomEquivAut K E L (τK.toAlgHom.comp iAlg)

/-- The normality restriction is characterized by its action on the embedded
copy of `L`. -/
theorem localizationAlgEquivRestrict_toLocalization
    (τ :
      letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
      letI : SMul K w.1.Completion := hK.toSMul
      letI := AbsoluteValue.completionAlgebra vK w.1 w.2
      AbsoluteValue.algebraicLocalization vK w.1 w.2 ≃ₐ[vK.Completion]
        AbsoluteValue.algebraicLocalization vK w.1 w.2)
    (x : L) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    AbsoluteValue.toAlgebraicLocalization vK w.1 w.2
        (localizationAlgEquivRestrict vK w τ x) =
      τ (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 x) := by
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let := AbsoluteValue.completionAlgebra vK w.1 w.2
  let E := AbsoluteValue.algebraicLocalization vK w.1 w.2
  let i : L →+* E := AbsoluteValue.toAlgebraicLocalization vK w.1 w.2
  let : Algebra K E := (i.comp (algebraMap K L)).toAlgebra
  let iAlg : L →ₐ[K] E :=
    { __ := i
      commutes' := fun x => by
        change i (algebraMap K L x) = (i.comp (algebraMap K L)) x
        rfl }
  let : Algebra L E := i.toAlgebra
  let : IsScalarTower K L E :=
    IsScalarTower.of_algebraMap_eq' rfl
  let τK : E ≃ₐ[K] E :=
    { __ := τ.toRingEquiv
      commutes' := fun y => by
        change τ (i (algebraMap K L y)) = i (algebraMap K L y)
        rw [AbsoluteValue.toAlgebraicLocalization_algebraMap, τ.commutes] }
  change i (Normal.algHomEquivAut K E L (τK.toAlgHom.comp iAlg) x) =
    τ (i x)
  simpa [iAlg, τK, AlgHom.restrictNormal', RingHom.algebraMap_toAlgebra] using
    ((τK.toAlgHom.comp iAlg).restrictNormal_commutes L x)

/-- Restriction of a local automorphism belongs to the decomposition group. -/
def localizationToDecompositionGroup
    (τ :
      letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
      letI : SMul K w.1.Completion := hK.toSMul
      letI := AbsoluteValue.completionAlgebra vK w.1 w.2
      AbsoluteValue.algebraicLocalization vK w.1 w.2 ≃ₐ[vK.Completion]
        AbsoluteValue.algebraicLocalization vK w.1 w.2) :
    absoluteValueDecompositionGroup K w.1 := by
  letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  letI : SMul K w.1.Completion := hK.toSMul
  letI := AbsoluteValue.completionAlgebra vK w.1 w.2
  let σ := localizationAlgEquivRestrict vK w τ
  refine ⟨σ, ?_⟩
  intro x
  have habs : w.1 (σ x) = w.1 x := by
    calc
      w.1 (σ x) = AbsoluteValue.algebraicLocalizationAbsoluteValue vK w.1 w.2
          (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 (σ x)) :=
        (AbsoluteValue.algebraicLocalizationAbsoluteValue_toAlgebraicLocalization vK w.1 w.2 (σ x)).symm
      _ = AbsoluteValue.algebraicLocalizationAbsoluteValue vK w.1 w.2
          (τ (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 x)) := by
        rw [localizationAlgEquivRestrict_toLocalization]
      _ = AbsoluteValue.algebraicLocalizationAbsoluteValue vK w.1 w.2
          (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 x) :=
        localizationAbsoluteValue_algEquiv vK hvK w τ _
      _ = w.1 x :=
        AbsoluteValue.algebraicLocalizationAbsoluteValue_toAlgebraicLocalization vK w.1 w.2 x
  rw [habs]

include hvK

/-- Extend an element of the decomposition group from `L` to the algebraic
localization `L_w`. -/
def decompositionGroupToLocalization
    (σ : absoluteValueDecompositionGroup K w.1) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    AbsoluteValue.algebraicLocalization vK w.1 w.2 ≃ₐ[vK.Completion]
      AbsoluteValue.algebraicLocalization vK w.1 w.2 :=
  valuationPreservingLocalizationAlgEquiv vK w (σ : L ≃ₐ[K] L)
    (absoluteValueDecompositionGroup_preserves_absoluteValue vK hvK w σ)

omit [IsGalois K L] in
@[simp] theorem decompositionGroupToLocalization_toLocalization
    (σ : absoluteValueDecompositionGroup K w.1) (x : L) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    decompositionGroupToLocalization vK hvK w σ
        (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 x) =
      AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 ((σ : L ≃ₐ[K] L) x) :=
  valuationPreservingLocalizationAlgEquiv_toLocalization vK w
    (σ : L ≃ₐ[K] L)
    (absoluteValueDecompositionGroup_preserves_absoluteValue vK hvK w σ) x

omit hvK

include hvK

/-- Restriction after extension is the original element of the decomposition
group. -/
theorem localizationToDecompositionGroup_decompositionGroupToLocalization
    (σ : absoluteValueDecompositionGroup K w.1) :
    localizationToDecompositionGroup vK hvK w
        (decompositionGroupToLocalization vK hvK w σ) = σ := by
  apply Subtype.ext
  apply AlgEquiv.ext
  intro x
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let := AbsoluteValue.completionAlgebra vK w.1 w.2
  let i := AbsoluteValue.toAlgebraicLocalization vK w.1 w.2
  apply i.injective
  calc
    i ((localizationToDecompositionGroup vK hvK w
          (decompositionGroupToLocalization vK hvK w σ) :
        L ≃ₐ[K] L) x) =
        decompositionGroupToLocalization vK hvK w σ (i x) :=
      localizationAlgEquivRestrict_toLocalization vK w
        (decompositionGroupToLocalization vK hvK w σ) x
    _ = i ((σ : L ≃ₐ[K] L) x) :=
      decompositionGroupToLocalization_toLocalization vK hvK w σ x

/-- Extension after restriction is the original local automorphism. -/
theorem decompositionGroupToLocalization_localizationToDecompositionGroup
    (τ :
      letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
      letI : SMul K w.1.Completion := hK.toSMul
      letI := AbsoluteValue.completionAlgebra vK w.1 w.2
      AbsoluteValue.algebraicLocalization vK w.1 w.2 ≃ₐ[vK.Completion]
        AbsoluteValue.algebraicLocalization vK w.1 w.2) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    decompositionGroupToLocalization vK hvK w
        (localizationToDecompositionGroup vK hvK w τ) = τ := by
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let := AbsoluteValue.completionAlgebra vK w.1 w.2
  let i := AbsoluteValue.toAlgebraicLocalization vK w.1 w.2
  let ρ := decompositionGroupToLocalization vK hvK w
    (localizationToDecompositionGroup vK hvK w τ)
  have hρ : ρ.toAlgHom = τ.toAlgHom := by
    apply IntermediateField.adjoin_algHom_ext
    intro z hz
    rcases hz with ⟨x, rfl⟩
    change ρ (i x) = τ (i x)
    rw [decompositionGroupToLocalization_toLocalization]
    change i (localizationAlgEquivRestrict vK w τ x) = τ (i x)
    exact localizationAlgEquivRestrict_toLocalization vK w τ x
  exact AlgEquiv.ext fun x => DFunLike.congr_fun hρ x

omit hvK

include hvK

omit [IsGalois K L] in
/-- Extension from the decomposition group respects composition. -/
theorem decompositionGroupToLocalization_mul
    (σ τ : absoluteValueDecompositionGroup K w.1) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    decompositionGroupToLocalization vK hvK w (σ * τ) =
      decompositionGroupToLocalization vK hvK w σ *
        decompositionGroupToLocalization vK hvK w τ := by
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let := AbsoluteValue.completionAlgebra vK w.1 w.2
  let i := AbsoluteValue.toAlgebraicLocalization vK w.1 w.2
  let ρL := decompositionGroupToLocalization vK hvK w (σ * τ)
  let ρR := decompositionGroupToLocalization vK hvK w σ *
    decompositionGroupToLocalization vK hvK w τ
  have hρ : ρL.toAlgHom = ρR.toAlgHom := by
    apply IntermediateField.adjoin_algHom_ext
    intro z hz
    rcases hz with ⟨x, rfl⟩
    change ρL (i x) = ρR (i x)
    calc
      ρL (i x) = i (((σ * τ : absoluteValueDecompositionGroup K w.1) :
          L ≃ₐ[K] L) x) :=
        decompositionGroupToLocalization_toLocalization vK hvK w (σ * τ) x
      _ = i ((σ : L ≃ₐ[K] L) ((τ : L ≃ₐ[K] L) x)) := rfl
      _ = decompositionGroupToLocalization vK hvK w σ
          (i ((τ : L ≃ₐ[K] L) x)) :=
        (decompositionGroupToLocalization_toLocalization
          vK hvK w σ ((τ : L ≃ₐ[K] L) x)).symm
      _ = decompositionGroupToLocalization vK hvK w σ
          (decompositionGroupToLocalization vK hvK w τ (i x)) := by
        exact congrArg (decompositionGroupToLocalization vK hvK w σ)
          (decompositionGroupToLocalization_toLocalization
            vK hvK w τ x).symm
      _ = ρR (i x) := rfl
  exact AlgEquiv.ext fun x => DFunLike.congr_fun hρ x

omit hvK

include hvK

/-- The localization and decomposition comparison (decomposition groups): for a possibly infinite Galois
extension, the decomposition group at `w` is canonically isomorphic to the
Galois group of the algebraic localization over `K_v`. -/
def decompositionGroupEquivAlgebraicLocalizationAut :
    absoluteValueDecompositionGroup K w.1 ≃*
      (letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
       letI : SMul K w.1.Completion := hK.toSMul
       letI := AbsoluteValue.completionAlgebra vK w.1 w.2
       AbsoluteValue.algebraicLocalization vK w.1 w.2 ≃ₐ[vK.Completion]
         AbsoluteValue.algebraicLocalization vK w.1 w.2) where
  toFun := decompositionGroupToLocalization vK hvK w
  invFun := localizationToDecompositionGroup vK hvK w
  left_inv := localizationToDecompositionGroup_decompositionGroupToLocalization
    vK hvK w
  right_inv :=
    decompositionGroupToLocalization_localizationToDecompositionGroup vK hvK w
  map_mul' := decompositionGroupToLocalization_mul vK hvK w

@[simp] theorem localizationRamificationGroups_decompositionGroupEquiv_apply
    (σ : absoluteValueDecompositionGroup K w.1) :
    decompositionGroupEquivAlgebraicLocalizationAut vK hvK w σ =
      decompositionGroupToLocalization vK hvK w σ :=
  rfl

end DecompositionEquiv

end HilbertRamification
end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_Completion_CanonicalTensorMap
attribute [-instance] _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.AlgebraicNumberTheory.Valuations.completionExtensionFactor_adjoinRootEquivCompletion_root _root_.HilbertRamification.decompositionGroupToLocalization_toLocalization _root_.HilbertRamification.localizationRamificationGroups_decompositionGroupEquiv_apply _root_.HilbertRamification.valuationPreservingCompletionRingEquiv_toCompletion _root_.HilbertRamification.valuationPreservingLocalizationAlgEquiv_toLocalization _root_.HilbertRamification.valuationPreservingWithAbsRingEquiv_apply _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The canonical tensor map to all completions

For every exact extension `w | v`, multiplication in `L_w` gives the map
`K_v ⊗_K L → L_w`.  Taking all components produces the canonical map
which occurs in the tensor-product decomposition over a completion.  This construction is
independent of the factorisation argument later used to prove bijectivity.
-/

noncomputable section

namespace AlgebraicNumberTheory
namespace Valuations

universe u v

open scoped TensorProduct

/-- The product of the component maps `K_v ⊗_K L → L_w`. -/
noncomputable def completionTensorMap_leftCanonicalHom
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) :
    letI : ∀ w : AbsoluteValueExtension vK L,
        Algebra vK.Completion w.1.Completion :=
      fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
    vK.Completion ⊗[K] L →ₐ[vK.Completion]
      ∀ w : AbsoluteValueExtension vK L, w.1.Completion := by
  letI : ∀ w : AbsoluteValueExtension vK L,
      Algebra vK.Completion w.1.Completion :=
    fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
  exact AlgHom.pi fun w ↦
    absoluteValueExtension_localizationTensorHom vK w

@[simp]
theorem completionTensorMap_leftCanonicalHom_tmul_apply
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (b : vK.Completion) (a : L)
    (w : AbsoluteValueExtension vK L) :
    letI : ∀ w : AbsoluteValueExtension vK L,
        Algebra vK.Completion w.1.Completion :=
      fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
    completionTensorMap_leftCanonicalHom vK (b ⊗ₜ[K] a) w =
      algebraMap vK.Completion w.1.Completion b *
        AbsoluteValue.toCompletionAlgHom (K := K) w.1 a := by
  let : ∀ w : AbsoluteValueExtension vK L,
      Algebra vK.Completion w.1.Completion :=
    fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
  exact absoluteValueExtension_localizationTensorHom_tmul vK w b a

end Valuations
end AlgebraicNumberTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_Completion_PolynomialFactors
attribute [-instance] _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
attribute [-simp] _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Irreducible factors as conjugacy classes of roots

This file records the algebraic source lemma underlying
the extension-factor correspondence.  Multiplicities are deliberately discarded: extensions of a
valuation correspond to the *distinct* irreducible factors over the
completion.
-/

noncomputable section

open Polynomial
open UniqueFactorizationMonoid

namespace ValuationTheory
namespace Completion

universe u v

/-- Associated polynomials have the same multiset of normalized irreducible factors. -/
theorem polynomialNormalizedFactors_eq_of_associated
    {F : Type u} [Field F] {p q : F[X]} (h : Associated p q) :
    polynomialNormalizedFactors p = polynomialNormalizedFactors q := by
  classical
  dsimp [polynomialNormalizedFactors]
  exact h.normalizedFactors_eq

/-- Associated polynomials have the same set of distinct normalized factors. -/
theorem polynomialDistinctNormalizedFactors_eq_of_associated
    {F : Type u} [Field F] {p q : F[X]} (h : Associated p q) :
    polynomialDistinctNormalizedFactors p =
      polynomialDistinctNormalizedFactors q := by
  classical
  dsimp [polynomialDistinctNormalizedFactors]
  rw [polynomialNormalizedFactors_eq_of_associated h]

end Completion
end ValuationTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_Completion_ExtensionFactorClassification
attribute [-instance] _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Classification of extensions of a completed absolute value

For a simple finite extension `L = K(α)`, the extensions of a nontrivial
absolute value of `K` correspond to the distinct irreducible factors, over
the completion, of an irreducible polynomial having `α` as a root.  The final
theorem below also records the explicit pullback valuation and the extension
of the chosen embedding to the completed field.
-/

noncomputable section

open Polynomial
open scoped Topology
open ValuationTheory.Completion

namespace AlgebraicNumberTheory
namespace Valuations

universe u v

/-- After base change to the completion, the chosen irreducible polynomial and the minimal
polynomial still have exactly the same normalized irreducible factors. -/
theorem completionExtensionFactor_completionFactors_eq_minpolyFactors
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) {α : L} {f : K[X]}
    (hf : Irreducible f) (hroot : Polynomial.aeval α f = 0) :
    polynomialDistinctNormalizedFactors
        (completionExtensionFactor_completionPolynomial vK f) =
      polynomialDistinctNormalizedFactors
        ((minpoly K α).map (algebraMap K vK.Completion)) := by
  exact polynomialDistinctNormalizedFactors_eq_of_associated
    (Polynomial.associated_map_map (algebraMap K vK.Completion)
      (completionExtensionFactor_definingPolynomial_associated_minpoly hf hroot))

/-- Transport the factor set of the mapped minimal polynomial to the factor
set of the particular chosen irreducible polynomial. -/
noncomputable def completionExtensionFactor_minpolyFactorsEquivCompletionFactors
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) {α : L} {f : K[X]}
    (hf : Irreducible f) (hroot : Polynomial.aeval α f = 0) :
    DistinctNormalizedFactors
        ((minpoly K α).map (algebraMap K vK.Completion)) ≃
      CompletionExtensionFactorCompletionFactors vK f :=
  Equiv.setCongr (by
    ext g
    exact Finset.ext_iff.mp
      (completionExtensionFactor_completionFactors_eq_minpolyFactors
        vK hf hroot).symm g)

/-- For a simple extension, the relation used in the preceding quotient is
exactly conjugacy of embeddings over `K_v` from the valuation-extension theorem. -/
theorem completionExtensionFactor_embeddingSetoid_rel_iff_conjugate
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (α : L) (hα : IsIntegral K α)
    (hgen : Algebra.adjoin K ({α} : Set L) = ⊤)
    (τ τ' : L →ₐ[K] absoluteValueExtension_algebraicCompletionClosure vK) :
    (CompletionExtensionFactorEmbeddingSetoid vK α hα hgen).r τ τ' ↔
      AbsoluteValueExtensionConjugateOverCompletion vK τ τ' := by
  let pb : PowerBasis K L := PowerBasis.ofAdjoinEqTop hα hgen
  have hpbgen : pb.gen = α := by simp [pb]
  change IsConjRoot vK.Completion (τ α) (τ' α) ↔ _
  constructor
  · intro hconj
    obtain ⟨σ, hσ⟩ := IsConjRoot.exists_algEquiv hconj.symm
    refine ⟨σ, ?_⟩
    let στ : L →ₐ[K] absoluteValueExtension_algebraicCompletionClosure vK :=
      (σ.toAlgHom.restrictScalars K).comp τ
    have heq : τ' = στ := by
      apply pb.algHom_ext
      rw [hpbgen]
      exact hσ.symm
    intro x
    exact DFunLike.congr_fun heq x
  · rintro ⟨σ, hσ⟩
    change minpoly vK.Completion (τ α) = minpoly vK.Completion (τ' α)
    rw [hσ α]
    exact (minpoly.algEquiv_eq σ (τ α)).symm

/-- Regard the pullback attached to an embedding as an exact extension.
The extension property is the one proved in the valuation-extension theorem, rather than an
extra field in the data of the extension-factor correspondence. -/
noncomputable def pullbackAbsoluteValueExtension
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (τ : L →ₐ[K] absoluteValueExtension_algebraicCompletionClosure vK) :
    AbsoluteValueExtension vK L :=
  ⟨absoluteValueExtension_pullback vK hvK τ,
    absoluteValueExtension_pullback_extends vK hvK τ⟩

/-- In the simple-extension situation, equality of the two pullback
valuations is exactly the factor relation used on embeddings.  The forward
direction is proved by extending both embeddings to the same completion and
comparing minimal polynomials there. -/
theorem completionExtensionFactor_pullback_eq_iff_embeddingSetoid_rel
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (α : L) (hα : IsIntegral K α)
    (hgen : Algebra.adjoin K ({α} : Set L) = ⊤)
    (τ τ' : L →ₐ[K] absoluteValueExtension_algebraicCompletionClosure vK) :
    absoluteValueExtension_pullback vK hvK τ =
        absoluteValueExtension_pullback vK hvK τ' ↔
      (CompletionExtensionFactorEmbeddingSetoid vK α hα hgen).r τ τ' := by
  let pb : PowerBasis K L := PowerBasis.ofAdjoinEqTop hα hgen
  let : FiniteDimensional K L := pb.finite
  let : Algebra.IsAlgebraic K L := inferInstance
  rw [completionExtensionFactor_embeddingSetoid_rel_iff_conjugate
    vK α hα hgen τ τ']
  exact absoluteValueExtension_pullback_eq_iff_conjugate vK hvK τ τ'

/-- Exact extensions are the same as the conjugacy classes of embeddings
used in the factor calculation. -/
noncomputable def completionExtensionFactor_extensionsEquivEmbeddingClasses
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (α : L) (hα : IsIntegral K α)
    (hgen : Algebra.adjoin K ({α} : Set L) = ⊤) :
    AbsoluteValueExtension vK L ≃
      Quotient (CompletionExtensionFactorEmbeddingSetoid vK α hα hgen) := by
  let pb : PowerBasis K L := PowerBasis.ofAdjoinEqTop hα hgen
  letI : FiniteDimensional K L := pb.finite
  letI : Algebra.IsAlgebraic K L := inferInstance
  let fromClass :
      Quotient (CompletionExtensionFactorEmbeddingSetoid vK α hα hgen) →
        AbsoluteValueExtension vK L :=
    Quotient.lift
      (pullbackAbsoluteValueExtension vK hvK)
      (by
        intro τ τ' hrel
        apply Subtype.ext
        exact (completionExtensionFactor_pullback_eq_iff_embeddingSetoid_rel
          vK hvK α hα hgen τ τ').2 hrel)
  refine
    { toFun := fun w => Quotient.mk
        (CompletionExtensionFactorEmbeddingSetoid vK α hα hgen)
        (absoluteValueExtension_embeddingOfExtension vK w)
      invFun := fromClass
      left_inv := ?_
      right_inv := ?_ }
  · intro w
    apply Subtype.ext
    exact (completionExtensionFactor_extension_eq_pullback_embeddingOfExtension
      vK hvK w).symm
  · intro q
    induction q using Quotient.inductionOn with
    | _ τ =>
      apply Quotient.sound
      let wτ : AbsoluteValueExtension vK L :=
        pullbackAbsoluteValueExtension vK hvK τ
      apply (completionExtensionFactor_pullback_eq_iff_embeddingSetoid_rel
        vK hvK α hα hgen
        (absoluteValueExtension_embeddingOfExtension vK wτ) τ).1
      exact (completionExtensionFactor_extension_eq_pullback_embeddingOfExtension
        vK hvK wτ).symm

/-- Auxiliary form of the correspondence, first stated for the mapped
minimal polynomial. -/
noncomputable def completionExtensionFactor_extensionsEquivMinpolyFactors
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (α : L) (hα : IsIntegral K α)
    (hgen : Algebra.adjoin K ({α} : Set L) = ⊤) :
    AbsoluteValueExtension vK L ≃
      DistinctNormalizedFactors
        ((minpoly K α).map (algebraMap K vK.Completion)) :=
  (completionExtensionFactor_extensionsEquivEmbeddingClasses
      vK hvK α hα hgen).trans
    (completionExtensionFactor_embeddingClassesEquivMinpolyFactors
      vK α hα hgen)

/-- Auxiliary form with the particular chosen irreducible polynomial `f` as
target. -/
noncomputable def completionExtensionFactor_extensionsEquivCompletionFactorsAux
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    {α : L} {f : K[X]} (hf : Irreducible f)
    (hroot : Polynomial.aeval α f = 0)
    (hgen : Algebra.adjoin K ({α} : Set L) = ⊤) :
    AbsoluteValueExtension vK L ≃
      CompletionExtensionFactorCompletionFactors vK f :=
  let hα := completionExtensionFactor_root_isIntegral hf hroot
  (completionExtensionFactor_extensionsEquivMinpolyFactors
      vK hvK α hα hgen).trans
    (completionExtensionFactor_minpolyFactorsEquivCompletionFactors
      vK hf hroot)

/-- The factor read from the canonical embedding supplied by the valuation-extension theorem is
the same polynomial as the factor read directly in the metric completion
`L_w`. -/
theorem completionExtensionFactor_embeddingOfExtension_minpoly
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (vK : AbsoluteValue K ℝ) (α : L)
    (w : AbsoluteValueExtension vK L) :
    minpoly vK.Completion
        (absoluteValueExtension_embeddingOfExtension vK w α) =
      completionExtensionFactor_extensionFactor vK α w := by
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let := AbsoluteValue.completionAlgebra vK w.1 w.2
  let a := AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 α
  calc
    minpoly vK.Completion
        (absoluteValueExtension_embeddingOfExtension vK w α) =
        minpoly vK.Completion a :=
      minpoly.algHom_eq
        (absoluteValueExtension_localizationEmbedding vK w)
        (absoluteValueExtension_localizationEmbedding vK w).injective a
    _ = minpoly vK.Completion
        (AbsoluteValue.toCompletionAlgHom (K := K) w.1 α) := by
      rw [← minpoly.algHom_eq
        (AbsoluteValue.algebraicLocalization vK w.1 w.2).val
        (AbsoluteValue.algebraicLocalization vK w.1 w.2).val.injective a]
      rfl
    _ = completionExtensionFactor_extensionFactor vK α w := rfl

/-- On an extension `w`, the auxiliary correspondence is the directly
defined polynomial `minpoly_{K_v}(α in L_w)`. -/
theorem completionExtensionFactor_extensionsEquivCompletionFactorsAux_apply
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    {α : L} {f : K[X]} (hf : Irreducible f)
    (hroot : Polynomial.aeval α f = 0)
    (hgen : Algebra.adjoin K ({α} : Set L) = ⊤)
    (w : AbsoluteValueExtension vK L) :
    (completionExtensionFactor_extensionsEquivCompletionFactorsAux
        vK hvK hf hroot hgen w).1 =
      completionExtensionFactor_extensionFactor vK α w := by
  let hα := completionExtensionFactor_root_isIntegral hf hroot
  let pb : PowerBasis K L := PowerBasis.ofAdjoinEqTop hα hgen
  let : FiniteDimensional K L := pb.finite
  let : Algebra.IsAlgebraic K L := inferInstance
  change minpoly vK.Completion
      (absoluteValueExtension_embeddingOfExtension vK w α) =
    completionExtensionFactor_extensionFactor vK α w
  exact completionExtensionFactor_embeddingOfExtension_minpoly vK α w

/-- the extension-factor correspondence, correspondence part: exact extensions of `v` to the
simple extension are in canonical bijection with the distinct normalized
irreducible factors of `f` over `K_v`.  Its forward map is definitionally the
factor obtained from `α` in `L_w`. -/
noncomputable def completionExtensionFactor_extensionEquivFactors
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    {α : L} {f : K[X]} (hf : Irreducible f)
    (hroot : Polynomial.aeval α f = 0)
    (hgen : Algebra.adjoin K ({α} : Set L) = ⊤) :
    AbsoluteValueExtension vK L ≃
      CompletionExtensionFactorCompletionFactors vK f := by
  let e := completionExtensionFactor_extensionsEquivCompletionFactorsAux
    vK hvK hf hroot hgen
  apply Equiv.ofBijective
    (completionExtensionFactor_extensionToFactor vK hf hroot)
  have heq : completionExtensionFactor_extensionToFactor vK hf hroot = e := by
    funext w
    apply Subtype.ext
    exact (completionExtensionFactor_extensionsEquivCompletionFactorsAux_apply
      vK hvK hf hroot hgen w).symm
  rw [heq]
  exact e.bijective

end Valuations
end AlgebraicNumberTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_Completion_SeparablePolynomialFactors
attribute [-instance] _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
attribute [-simp] _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Distinct factors of a separable polynomial

A separable monic polynomial is the product of its distinct normalized
irreducible factors, and those factors are pairwise coprime.  These are the
factorization facts used in the Chinese-remainder proof of tensor-product decomposition.
-/

noncomputable section

open Polynomial UniqueFactorizationMonoid
open scoped BigOperators

namespace ValuationTheory
namespace Completion

universe u

/-- A monic separable polynomial is the product of its distinct normalized
irreducible factors. -/
theorem separable_monic_eq_prod_distinctNormalizedFactors
    {F : Type u} [Field F] (p : F[X])
    (hpmonic : p.Monic) (hpsep : p.Separable) :
    p = ∏ g : DistinctNormalizedFactors p, (g.1 : F[X]) := by
  classical
  let : NormalizationMonoid F := inferInstance
  let : NormalizationMonoid F[X] := Polynomial.instNormalizationMonoid
  have hp0 : p ≠ 0 := hpmonic.ne_zero
  have hnodup : (normalizedFactors p).Nodup :=
    (squarefree_iff_nodup_normalizedFactors hp0).1 hpsep.squarefree
  have hprod : (normalizedFactors p).prod = p := by
    simpa [hpmonic.leadingCoeff] using
      (Polynomial.leadingCoeff_mul_prod_normalizedFactors p)
  calc
    p = (normalizedFactors p).prod := hprod.symm
    _ = ∏ g : DistinctNormalizedFactors p, (g.1 : F[X]) := by
      change (normalizedFactors p).prod =
        ∏ g : {g : F[X] // g ∈ (normalizedFactors p).toFinset}, g.1
      rw [Finset.univ_eq_attach,
        Finset.prod_attach (f := fun x : F[X] ↦ x)]
      change (normalizedFactors p).prod =
        ((normalizedFactors p).toFinset.1.map id).prod
      rw [Multiset.toFinset_val, hnodup.dedup, Multiset.map_id]

/-- Distinct normalized irreducible factors are pairwise coprime. -/
theorem distinctNormalizedFactors_pairwise_coprime
    {F : Type u} [Field F] (p : F[X]) :
    ∀ i j : DistinctNormalizedFactors p, i ≠ j →
      IsCoprime (i.1 : F[X]) j.1 := by
  classical
  let : NormalizationMonoid F := inferInstance
  let : NormalizationMonoid F[X] := Polynomial.instNormalizationMonoid
  intro i j hij
  have hnorm : polynomialNormalizedFactors p = normalizedFactors p := by
    rfl
  have hi : i.1 ∈ normalizedFactors p := by
    rw [← hnorm]
    exact Multiset.mem_toFinset.mp i.2
  have hj : j.1 ∈ normalizedFactors p := by
    rw [← hnorm]
    exact Multiset.mem_toFinset.mp j.2
  rcases (prime_of_normalized_factor i.1 hi).irreducible.isCoprime_or_dvd j.1 with h | h
  · exact h
  · exfalso
    apply hij
    apply Subtype.ext
    exact normalizedFactors_eq_of_dvd p i.1 hi j.1 hj h

end Completion
end ValuationTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_Completion_TensorProductDecomposition
attribute [-instance] _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.HilbertRamification.decompositionGroupToLocalization_toLocalization _root_.HilbertRamification.localizationRamificationGroups_decompositionGroupEquiv_apply _root_.HilbertRamification.valuationPreservingCompletionRingEquiv_toCompletion _root_.HilbertRamification.valuationPreservingLocalizationAlgEquiv_toLocalization _root_.HilbertRamification.valuationPreservingWithAbsRingEquiv_apply _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Tensor-product decomposition over a completion

For a finite separable extension `L / K`, the canonical map
`L ⊗_K K_v → ∏_{w|v} L_w` is an isomorphism.  The proof follows the
construction: choose a primitive element, factor its mapped minimal polynomial,
apply the Chinese remainder theorem, and identify every simple factor with
the corresponding completion using the extension-factor correspondence.
-/

noncomputable section

open Polynomial
open scoped BigOperators TensorProduct
open ValuationTheory.Completion

namespace AlgebraicNumberTheory
namespace Valuations

universe u v

/-- the extension-factor correspondence makes the extensions `w | v` into a finite type. -/
@[reducible]
noncomputable def completionTensorDecomposition_extensionFintype
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial) :
    Fintype (AbsoluteValueExtension vK L) := by
  let pb := completionTensorDecomposition_powerBasis K L
  let hf : Irreducible (minpoly K pb.gen) :=
    minpoly.irreducible pb.isIntegral_gen
  let e := completionExtensionFactor_extensionEquivFactors vK hvK hf
    (minpoly.aeval K pb.gen) pb.adjoin_gen_eq_top
  exact Fintype.ofEquiv _ e.symm

/-- In the separable case the mapped minimal polynomial is the product of
the factors indexed by all extensions `w | v`. -/
theorem completionTensorDecomposition_mapped_minpoly_eq_prod_extensionFactors
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial) :
    letI := completionTensorDecomposition_extensionFintype (K := K) (L := L) vK hvK
    (minpoly K (completionTensorDecomposition_powerBasis K L).gen).map
        (algebraMap K vK.Completion) =
      ∏ w : AbsoluteValueExtension vK L,
        completionExtensionFactor_extensionFactor vK
          (completionTensorDecomposition_powerBasis K L).gen w := by
  classical
  let := completionTensorDecomposition_extensionFintype (K := K) (L := L) vK hvK
  let pb := completionTensorDecomposition_powerBasis K L
  let p := (minpoly K pb.gen).map (algebraMap K vK.Completion)
  let hf : Irreducible (minpoly K pb.gen) :=
    minpoly.irreducible pb.isIntegral_gen
  let e := completionExtensionFactor_extensionEquivFactors vK hvK hf
    (minpoly.aeval K pb.gen) pb.adjoin_gen_eq_top
  have hpmonic : p.Monic :=
    (minpoly.monic pb.isIntegral_gen).map (algebraMap K vK.Completion)
  have hpsep : p.Separable :=
    Polynomial.Separable.map
      (Algebra.IsSeparable.isSeparable K (pb.gen : L))
  calc
    p = ∏ g : CompletionExtensionFactorCompletionFactors vK (minpoly K pb.gen),
        (g.1 : vK.Completion[X]) :=
      separable_monic_eq_prod_distinctNormalizedFactors p hpmonic hpsep
    _ = ∏ w : AbsoluteValueExtension vK L,
        completionExtensionFactor_extensionFactor vK pb.gen w := by
      symm
      exact Fintype.prod_equiv e _ _ (fun _ ↦ rfl)

/-- The factors indexed by distinct extensions are pairwise coprime. -/
theorem completionTensorDecomposition_extensionFactors_pairwise_coprime
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial) :
    letI := completionTensorDecomposition_extensionFintype (K := K) (L := L) vK hvK
    ∀ w w' : AbsoluteValueExtension vK L, w ≠ w' →
      IsCoprime
        (completionExtensionFactor_extensionFactor vK
          (completionTensorDecomposition_powerBasis K L).gen w)
        (completionExtensionFactor_extensionFactor vK
          (completionTensorDecomposition_powerBasis K L).gen w') := by
  classical
  let := completionTensorDecomposition_extensionFintype (K := K) (L := L) vK hvK
  let pb := completionTensorDecomposition_powerBasis K L
  let hf : Irreducible (minpoly K pb.gen) :=
    minpoly.irreducible pb.isIntegral_gen
  let e := completionExtensionFactor_extensionEquivFactors vK hvK hf
    (minpoly.aeval K pb.gen) pb.adjoin_gen_eq_top
  intro w w' hww'
  have he : e w ≠ e w' := fun h ↦ hww' (e.injective h)
  exact distinctNormalizedFactors_pairwise_coprime
    ((minpoly K pb.gen).map (algebraMap K vK.Completion))
    (e w) (e w') he

/-- The factorization/CRT equivalence in the left tensor order
`K_v ⊗_K L`. -/
noncomputable def completionTensorDecomposition_factorEquiv
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial) :
    letI : ∀ w : AbsoluteValueExtension vK L,
        Algebra vK.Completion w.1.Completion :=
      fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
    vK.Completion ⊗[K] L ≃ₐ[vK.Completion]
      ∀ w : AbsoluteValueExtension vK L, w.1.Completion := by
  classical
  letI := completionTensorDecomposition_extensionFintype (K := K) (L := L) vK hvK
  let pb := completionTensorDecomposition_powerBasis K L
  let hα := pb.isIntegral_gen
  let hgen := pb.adjoin_gen_eq_top
  letI hK : ∀ w : AbsoluteValueExtension vK L,
      Algebra K w.1.Completion :=
    fun w ↦ AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  letI : ∀ w : AbsoluteValueExtension vK L, SMul K w.1.Completion :=
    fun w ↦ (hK w).toSMul
  letI : ∀ w : AbsoluteValueExtension vK L,
      Algebra vK.Completion w.1.Completion :=
    fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
  let ebase := baseChangeEquivAdjoinRoot (A := vK.Completion) pb
  let hprod := completionTensorDecomposition_mapped_minpoly_eq_prod_extensionFactors
    (K := K) (L := L) vK hvK
  let econgr := AdjoinRoot.algEquivOfEq vK.Completion _ _ hprod
  let ecrt := adjoinRootProdEquivPi
    (fun w : AbsoluteValueExtension vK L ↦
      completionExtensionFactor_extensionFactor vK pb.gen w)
    (completionTensorDecomposition_extensionFactors_pairwise_coprime
      (K := K) (L := L) vK hvK)
  let elocal := AlgEquiv.piCongrRight fun w ↦
    completionExtensionFactor_adjoinRootEquivCompletion
      vK hvK pb.gen hα hgen w
  exact ebase.trans (econgr.trans (ecrt.trans elocal))

/-- The CRT equivalence sends the primitive generator to its canonical
image in every completion. -/
@[simp]
theorem completionTensorDecomposition_factorEquiv_one_tmul_gen
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L) :
    letI : ∀ w : AbsoluteValueExtension vK L,
        Algebra vK.Completion w.1.Completion :=
      fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
    completionTensorDecomposition_factorEquiv (K := K) (L := L) vK hvK
        (1 ⊗ₜ[K] (completionTensorDecomposition_powerBasis K L).gen) w =
      AbsoluteValue.toCompletionAlgHom (K := K) w.1
        (completionTensorDecomposition_powerBasis K L).gen := by
  classical
  let := completionTensorDecomposition_extensionFintype (K := K) (L := L) vK hvK
  let pb := completionTensorDecomposition_powerBasis K L
  let hK : ∀ w : AbsoluteValueExtension vK L,
      Algebra K w.1.Completion :=
    fun w ↦ AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : ∀ w : AbsoluteValueExtension vK L, SMul K w.1.Completion :=
    fun w ↦ (hK w).toSMul
  let : ∀ w : AbsoluteValueExtension vK L,
      Algebra vK.Completion w.1.Completion :=
    fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
  let factors := fun w : AbsoluteValueExtension vK L ↦
    completionExtensionFactor_extensionFactor vK pb.gen w
  let hcop := completionTensorDecomposition_extensionFactors_pairwise_coprime
    (K := K) (L := L) vK hvK
  let ebase := baseChangeEquivAdjoinRoot (A := vK.Completion) pb
  let hprod := completionTensorDecomposition_mapped_minpoly_eq_prod_extensionFactors
    (K := K) (L := L) vK hvK
  let econgr := AdjoinRoot.algEquivOfEq vK.Completion _ _ hprod
  let ecrt := adjoinRootProdEquivPi factors hcop
  let elocal := AlgEquiv.piCongrRight fun w ↦
    completionExtensionFactor_adjoinRootEquivCompletion
      vK hvK pb.gen pb.isIntegral_gen pb.adjoin_gen_eq_top w
  change elocal (ecrt (econgr (ebase (1 ⊗ₜ[K] pb.gen)))) w = _
  rw [baseChangeEquivAdjoinRoot_one_tmul_gen,
    AdjoinRoot.algEquivOfEq_root]
  change
    (completionExtensionFactor_adjoinRootEquivCompletion
      vK hvK pb.gen pb.isIntegral_gen pb.adjoin_gen_eq_top w)
        (adjoinRootProdEquivPi factors hcop
          (AdjoinRoot.mk (∏ w, factors w) X) w) = _
  rw [adjoinRootProdEquivPi_mk]
  exact completionExtensionFactor_adjoinRootEquivCompletion_root
    vK hvK pb.gen pb.isIntegral_gen pb.adjoin_gen_eq_top w

/-- The factorization equivalence is not merely an abstract isomorphism:
its algebra homomorphism is the canonical product map. -/
theorem completionTensorDecomposition_factorEquiv_toAlgHom
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial) :
    letI : ∀ w : AbsoluteValueExtension vK L,
        Algebra vK.Completion w.1.Completion :=
      fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
    (completionTensorDecomposition_factorEquiv (K := K) (L := L) vK hvK).toAlgHom =
      completionTensorMap_leftCanonicalHom vK := by
  classical
  let := completionTensorDecomposition_extensionFintype (K := K) (L := L) vK hvK
  let pb := completionTensorDecomposition_powerBasis K L
  let hK : ∀ w : AbsoluteValueExtension vK L,
      Algebra K w.1.Completion :=
    fun w ↦ AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : ∀ w : AbsoluteValueExtension vK L, SMul K w.1.Completion :=
    fun w ↦ (hK w).toSMul
  let : ∀ w : AbsoluteValueExtension vK L,
      Algebra vK.Completion w.1.Completion :=
    fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
  apply (powerBasisBaseChange (A := vK.Completion) pb).algHom_ext
  funext w
  change
    completionTensorDecomposition_factorEquiv (K := K) (L := L) vK hvK
        (1 ⊗ₜ[K] (completionTensorDecomposition_powerBasis K L).gen) w =
      completionTensorMap_leftCanonicalHom (K := K) (L := L) vK
        (1 ⊗ₜ[K] (completionTensorDecomposition_powerBasis K L).gen) w
  rw [completionTensorDecomposition_factorEquiv_one_tmul_gen
      (K := K) (L := L) vK hvK w,
    completionTensorMap_leftCanonicalHom_tmul_apply]
  simp

/-- The canonical product map in the left tensor order is bijective. -/
theorem completionTensorDecomposition_leftCanonicalHom_bijective
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial) :
    letI : ∀ w : AbsoluteValueExtension vK L,
        Algebra vK.Completion w.1.Completion :=
      fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
    Function.Bijective
      (completionTensorMap_leftCanonicalHom (K := K) (L := L) vK) := by
  classical
  let : ∀ w : AbsoluteValueExtension vK L,
      Algebra vK.Completion w.1.Completion :=
    fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
  rw [← completionTensorDecomposition_factorEquiv_toAlgHom
    (K := K) (L := L) vK hvK]
  exact (completionTensorDecomposition_factorEquiv
    (K := K) (L := L) vK hvK).bijective

/-- the completion tensor-product decomposition in the left tensor order, retained for the scalar
extension calculations in the local degree, norm, and trace formulas.  Its underlying map is canonical. -/
noncomputable def completionTensorDecomposition_left
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial) :
    letI : ∀ w : AbsoluteValueExtension vK L,
        Algebra vK.Completion w.1.Completion :=
      fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
    vK.Completion ⊗[K] L ≃ₐ[vK.Completion]
      ∀ w : AbsoluteValueExtension vK L, w.1.Completion := by
  letI : ∀ w : AbsoluteValueExtension vK L,
      Algebra vK.Completion w.1.Completion :=
    fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
  exact AlgEquiv.ofBijective
    (completionTensorMap_leftCanonicalHom (K := K) (L := L) vK)
    (completionTensorDecomposition_leftCanonicalHom_bijective
      (K := K) (L := L) vK hvK)

@[simp]
theorem completionTensorDecomposition_left_tmul_apply
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (b : vK.Completion) (a : L)
    (w : AbsoluteValueExtension vK L) :
    letI : ∀ w : AbsoluteValueExtension vK L,
        Algebra vK.Completion w.1.Completion :=
      fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
    completionTensorDecomposition_left (K := K) (L := L) vK hvK (b ⊗ₜ[K] a) w =
      algebraMap vK.Completion w.1.Completion b *
        AbsoluteValue.toCompletionAlgHom (K := K) w.1 a := by
  let : ∀ w : AbsoluteValueExtension vK L,
      Algebra vK.Completion w.1.Completion :=
    fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
  change completionTensorMap_leftCanonicalHom (K := K) (L := L) vK
    (b ⊗ₜ[K] a) w = _
  exact completionTensorMap_leftCanonicalHom_tmul_apply vK b a w

/-- the completion tensor-product decomposition on unit groups, in the tensor-factor order used by
local scalar extension. -/
noncomputable def localTensorUnitsEquivCompletionProduct
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial) :
    letI : ∀ w' : AbsoluteValueExtension vK L,
        Algebra vK.Completion w'.1.Completion :=
      fun w' ↦ AbsoluteValue.completionAlgebra vK w'.1 w'.2
    (vK.Completion ⊗[K] L)ˣ ≃*
      (∀ w' : AbsoluteValueExtension vK L,
        w'.1.Completionˣ) := by
  letI : ∀ w' : AbsoluteValueExtension vK L,
      Algebra vK.Completion w'.1.Completion :=
    fun w' ↦ AbsoluteValue.completionAlgebra vK w'.1 w'.2
  exact
    (Units.mapEquiv
      (completionTensorDecomposition_left
        (K := K) (L := L) vK hvK).toMulEquiv).trans
      MulEquiv.piUnits

/-- Evaluation of the unit-group form of the completion tensor-product decomposition agrees with the
underlying tensor-product decomposition. -/
@[simp]
theorem localTensorUnitsEquivCompletionProduct_apply_coe
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (z : (vK.Completion ⊗[K] L)ˣ)
    (w' : AbsoluteValueExtension vK L) :
    letI : ∀ u : AbsoluteValueExtension vK L,
        Algebra vK.Completion u.1.Completion :=
      fun u ↦ AbsoluteValue.completionAlgebra vK u.1 u.2
    (((localTensorUnitsEquivCompletionProduct vK hvK z) w' :
        w'.1.Completionˣ) : w'.1.Completion) =
      completionTensorDecomposition_left (K := K) (L := L) vK hvK
        (z : vK.Completion ⊗[K] L) w' :=
  rfl

end Valuations
end AlgebraicNumberTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_Completion_ExtensionInvariants
attribute [-instance] _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Local degree, ramification, and residue invariants

For a finite separable extension `L / K` and a discrete nonarchimedean
absolute value `v` on `K`, this file proves the exact degree formula
`∑_{w ∣ v} e_w f_w = [L : K]`.

The proof makes explicit the two facts used implicitly in the construction: metric
completion preserves the value group and residue field, and every completed
local extension `L_w / K_v` is finite separable.  The fundamental inequality then gives
`[L_w : K_v] = e_w f_w`; summing and applying the local degree, norm, and trace formulas gives the result.
-/

noncomputable section

open scoped BigOperators

namespace AlgebraicNumberTheory.Valuations

universe u v

theorem completionNonarchimedean
    {K : Type u} [Field K] (vK : AbsoluteValue K ℝ)
    (hv : LubinTate.Valuations.NonarchimedeanAbsoluteValue vK) :
    LubinTate.Valuations.NonarchimedeanAbsoluteValue
      (AbsoluteValue.completionAbsoluteValue vK) :=
  (AbsoluteValue.isNonarchimedean_iff_bounded_nat
    (AbsoluteValue.completionAbsoluteValue vK)).1
    (AbsoluteValue.completionAbsoluteValue_isNonarchimedean vK
      ((AbsoluteValue.isNonarchimedean_iff_bounded_nat vK).2 hv))

/-- The homomorphism from the exponential valuation subring of a field to that
of its completion, induced by the canonical map into the completion. -/
def completionExponentialSubringMap
    {K : Type u} [Field K] (a : AbsoluteValue K ℝ)
    (ha : LubinTate.Valuations.NonarchimedeanAbsoluteValue a) :
    LubinTate.Valuations.exponentialValuationSubring
        (absoluteValueExponentialValuation a ha) →+*
      LubinTate.Valuations.exponentialValuationSubring
        (absoluteValueExponentialValuation
          (AbsoluteValue.completionAbsoluteValue a)
          (completionNonarchimedean a ha)) :=
  (algebraMap K a.Completion).restrict _ _ fun x hx => by
    rw [mem_absoluteValueExponentialSubring_iff] at hx ⊢
    change AbsoluteValue.completionAbsoluteValue a (x : a.Completion) ≤ 1
    rw [AbsoluteValue.completionAbsoluteValue_coe]
    exact hx

@[simp] theorem completionExponentialSubringMap_apply
    {K : Type u} [Field K] (a : AbsoluteValue K ℝ)
    (ha : LubinTate.Valuations.NonarchimedeanAbsoluteValue a)
    (x : LubinTate.Valuations.exponentialValuationSubring
      (absoluteValueExponentialValuation a ha)) :
    ((completionExponentialSubringMap a ha x :
      LubinTate.Valuations.exponentialValuationSubring
        (absoluteValueExponentialValuation
          (AbsoluteValue.completionAbsoluteValue a)
          (completionNonarchimedean a ha))) : a.Completion) =
      algebraMap K a.Completion (x : K) := rfl

theorem completionExponentialSubringMap_isLocalHom
    {K : Type u} [Field K] (a : AbsoluteValue K ℝ)
    (ha : LubinTate.Valuations.NonarchimedeanAbsoluteValue a) :
    IsLocalHom (completionExponentialSubringMap a ha) := by
  constructor
  intro x hx
  rw [LubinTate.Valuations.associatedAbsoluteValue_isUnit_iff_eq_one
    (absoluteValueExponentialValuation_associated a ha)]
  rw [LubinTate.Valuations.associatedAbsoluteValue_isUnit_iff_eq_one
    (absoluteValueExponentialValuation_associated
      (AbsoluteValue.completionAbsoluteValue a)
      (completionNonarchimedean a ha))] at hx
  change AbsoluteValue.completionAbsoluteValue a
      ((x : K) : a.Completion) = 1 at hx
  rw [AbsoluteValue.completionAbsoluteValue_coe] at hx
  exact hx

theorem completionResidueMap_surjective
    {K : Type u} [Field K] (a : AbsoluteValue K ℝ)
    (ha : LubinTate.Valuations.NonarchimedeanAbsoluteValue a) :
    letI : IsLocalHom (completionExponentialSubringMap a ha) :=
      completionExponentialSubringMap_isLocalHom a ha
    Function.Surjective
      (IsLocalRing.ResidueField.map (completionExponentialSubringMap a ha)) := by
  let v := absoluteValueExponentialValuation a ha
  let aC := AbsoluteValue.completionAbsoluteValue a
  let haC := completionNonarchimedean a ha
  let vC := absoluteValueExponentialValuation aC haC
  let V := LubinTate.Valuations.exponentialValuationSubring v
  let VC := LubinTate.Valuations.exponentialValuationSubring vC
  let f : V →+* VC := completionExponentialSubringMap a ha
  let : IsLocalHom f := completionExponentialSubringMap_isLocalHom a ha
  intro z
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective z
  let vId : AbsoluteValueExtension a K := ⟨a, fun _ => rfl⟩
  obtain ⟨x, hx⟩ :=
    (AbsoluteValue.denseRange_toCompletion vId.1).exists_dist_lt
      (y : a.Completion) zero_lt_one
  have hclose : aC (algebraMap K a.Completion x - (y : a.Completion)) < 1 := by
    change ‖algebraMap K a.Completion x - (y : a.Completion)‖ < 1
    rw [dist_eq_norm] at hx
    change ‖(y : a.Completion) - algebraMap K a.Completion x‖ < 1 at hx
    simpa only [norm_sub_rev] using hx
  have hy_le : aC (y : a.Completion) ≤ 1 := by
    exact (mem_absoluteValueExponentialSubring_iff aC haC (y : a.Completion)).1 y.property
  have hx_leC : aC (algebraMap K a.Completion x) ≤ 1 := by
    calc
      aC (algebraMap K a.Completion x) =
          aC ((algebraMap K a.Completion x - (y : a.Completion)) + y) := by
            congr 1
            ring
      _ ≤ max (aC (algebraMap K a.Completion x - (y : a.Completion)))
          (aC (y : a.Completion)) :=
        LubinTate.Valuations.strong_triangle_of_nonarchimedean aC haC _ _
      _ ≤ 1 := max_le hclose.le hy_le
  have hx_le : a x ≤ 1 := by
    change aC (x : a.Completion) ≤ 1 at hx_leC
    rwa [AbsoluteValue.completionAbsoluteValue_coe] at hx_leC
  let xV : V := ⟨x, (mem_absoluteValueExponentialSubring_iff a ha x).2 hx_le⟩
  refine ⟨IsLocalRing.residue V xV, ?_⟩
  rw [IsLocalRing.ResidueField.map_residue]
  rw [ValuationTheory.DiscreteValuationField.ResidueField.residue_eq_residue_iff_sub_mem_maximalIdeal]
  rw [mem_absoluteValueExponentialSubring_maximalIdeal_iff aC haC]
  exact hclose

/-- The residue-field equivalence induced by the canonical map from a
nonarchimedean valued field to its completion. -/
noncomputable def completionResidueEquiv
    {K : Type u} [Field K] (a : AbsoluteValue K ℝ)
    (ha : LubinTate.Valuations.NonarchimedeanAbsoluteValue a) :
    IsLocalRing.ResidueField
        (LubinTate.Valuations.exponentialValuationSubring
          (absoluteValueExponentialValuation a ha)) ≃+*
      IsLocalRing.ResidueField
        (LubinTate.Valuations.exponentialValuationSubring
          (absoluteValueExponentialValuation
            (AbsoluteValue.completionAbsoluteValue a)
            (completionNonarchimedean a ha))) := by
  letI : IsLocalHom (completionExponentialSubringMap a ha) :=
    completionExponentialSubringMap_isLocalHom a ha
  exact ValuationTheory.DiscreteValuationField.ResidueField.ringEquivOfSurjective
    (completionExponentialSubringMap a ha)
    (completionResidueMap_surjective a ha)

@[simp] theorem completionResidueEquiv_residue
    {K : Type u} [Field K] (a : AbsoluteValue K ℝ)
    (ha : LubinTate.Valuations.NonarchimedeanAbsoluteValue a)
    (x : LubinTate.Valuations.exponentialValuationSubring
      (absoluteValueExponentialValuation a ha)) :
    completionResidueEquiv a ha
        (IsLocalRing.residue _ x) =
      IsLocalRing.residue _ (completionExponentialSubringMap a ha x) := by
  let : IsLocalHom (completionExponentialSubringMap a ha) :=
    completionExponentialSubringMap_isLocalHom a ha
  exact IsLocalRing.ResidueField.map_residue _ _


end AlgebraicNumberTheory.Valuations
end
end

section
-- module Solutions.OAIQ244_DUKE.Ramification_HilbertRamification_DecompositionFieldLocalization
attribute [-instance] _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial
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

include hvK

omit hvK

include hvK

omit hvK

/-- The valuation subring of the nonarchimedean base absolute value. -/
abbrev decompositionField_baseValuationSubring
    (hv : LubinTate.Valuations.NonarchimedeanAbsoluteValue vK) :
    _root_.ValuationSubring K :=
  absoluteValueValuationSubring vK hv

end LocalizationGalois

end HilbertRamification
end
end


