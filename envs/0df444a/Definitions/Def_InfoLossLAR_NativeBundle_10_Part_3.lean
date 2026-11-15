-- Prove2me | Definitions.Def_InfoLossLAR_NativeBundle_10_Part_3
-- name    : InfoLossLAR_NativeBundle_10_Part_3
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T19:10:39.616208+00:00
-- url     : https://prove2.me/theorems/134dbe7b-654f-4414-9065-edaa46b8da7f
-- title:
--   Coefficient extraction and selected root profile data
-- statement:
--   This package defines control-choice averages, rational and binary coefficient extraction, selected root and primary columns, weighted point kernels, finite family products and density tensors, symmetrization, leg coefficients, positive profiles, touched-cycle lookup data, and flag iteration arrays.
--
--   These are stored finite data and their constructor and interpretation APIs. They keep the actual binary or rational computation distinct from its ideal real semantics; later theorems establish approximation and platform running-time guarantees. The smaller compilation unit preserves entire original source modules and introduces no assumed transport or lattice-reduction result.
-- source:
--   Local manuscript proof repository commit 5c3becb254daaa8738368b474349766c1769c2a0. Original source units Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryControlChoiceAverage, Definitions.Def_InfoLossLAR_Native_CurrentAFT_RationalCoefficientExtraction, Definitions.Def_InfoLossLAR_Native_CurrentAFT_RationalSelectedRootProgram, Definitions.Def_InfoLossLAR_Native_CurrentAFT_RationalPrimaryColumnProgram, Definitions.Def_InfoLossLAR_Native_CurrentAFT_WeightedPointKernelProgram, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryWeightedPointKernel, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryFixedPointPrograms, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryFamilyProductClosure, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryCoefficientAtomFormula, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryCoefficientAtom, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryDensityInverseColumn, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryDensityInverseTensor, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryCoefficientDensity, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryStoredSymmetrization, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryCoefficientExtraction, Definitions.Def_InfoLossLAR_Native_CurrentAFT_RationalLegCoefficientExtraction, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryLegCoefficientExtraction, Definitions.Def_InfoLossLAR_Native_CurrentAFT_RationalLegFamilyTable, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryLegSelectedCoefficient, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinarySubsetCoefficientSum, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryLegFamily, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryLegFamilyResources, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryFourPointPair, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryRootMeanResources, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryRootControlRest, Definitions.Def_InfoLossLAR_Native_CurrentAFT_RationalPositiveReferenceProgram, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryPositiveReference, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryProfileLookup, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryTouchedCycle, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryTouchedCycleBuffer, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryTouchedCycleRanks, Definitions.Def_InfoLossLAR_Native_CurrentAFT_CurrentFlagIteration, Definitions.Def_InfoLossLAR_Native_CurrentAFT_CurrentFlagArray. Exact syntax-oracle source spans, body hashes and closed scope wrappers recorded in compact_heavy_split/manifest.json. Source SHA256 581fbbd732f5704667954592efe228aca0fbec460acf182bcb9f808779de49ac. Compiler-only optimization: one local scope marks Polynomial addition and multiplication instances irreducible while generating native equation lemmas. Every original definition and proof source body is unchanged; all11528 public types and recursive standard-axiom audits pass. New sourceSHA256 69dd1ad0a4329d7718af11205781138d97902a496f888285ee54848b3e14db54.

import Definitions.Def_InfoLossLAR_NativeBundle_10_Part_2

section
attribute [local irreducible] Polynomial.instAdd Polynomial.instMul

section





























/-! # Actual counter-generated independent without-replacement control choices -/
namespace CurrentAFT.BinaryControlChoiceAverage
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open GradedControlAlgebra
open scoped BigOperators
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryFullResponseCounts.current BinaryTwoPoolAverage.current
  PublicParameterProgram.modulus BinaryProposalMetadata.counts Parameters.legCount BackgroundRates.ordinaryPool

abbrev PrimaryPool (security : ℕ) := Fin (BinaryFullResponseCounts.current security).leg
abbrev BodyPool (security : ℕ) := Fin (BinaryFullResponseCounts.current security).ordinary
abbrev Choice (security r s : ℕ) := (Fin r ↪ PrimaryPool security) × (Fin s ↪ BodyPool security)

def current (security order : ℕ) (source : TruncatedArity order)
    (kernel : Vector (PrimaryPool security) source.val.1.val → Vector (BodyPool security) source.val.2.val → RationalResult) : RationalResult :=
  let counts := BinaryFullResponseCounts.current security
  let result := BinaryTwoPoolAverage.current counts.leg counts.ordinary source.val.1.val source.val.2.val
    (BinaryFullResponseCounts.positive security).1 (BinaryFullResponseCounts.positive security).2.1 kernel
  ⟨result.data,counts.work+result.work+2⟩

def choiceEquiv (security r s : ℕ) : Choice security r s ≃ UniformTaggedOutput.Choice security r s :=
  Equiv.prodCongr
    (Equiv.embeddingCongr (Equiv.refl (Fin r)) (finCongr (BinaryFullResponseCounts.current_value security).1))
    (Equiv.embeddingCongr (Equiv.refl (Fin s)) (finCongr (BinaryFullResponseCounts.current_value security).2.1))

noncomputable section
open scoped Classical






noncomputable def heightPolynomial (order : ℕ) (leafHeight : Polynomial ℕ) : Polynomial ℕ :=
  ∑ source : TruncatedArity order, BinaryWeightResources.averageHeightPolynomial BinaryProposalMetadata.sizePolynomial
    BinaryProposalMetadata.sizePolynomial source.val.1.val source.val.2.val leafHeight
noncomputable def workPolynomial (order : ℕ) (leafHeight leafWork : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFullResponseCounts.workPolynomial+
    (∑ source : TruncatedArity order, BinaryWeightResources.averageWorkPolynomial BinaryProposalMetadata.sizePolynomial
      BinaryProposalMetadata.sizePolynomial source.val.1.val source.val.2.val leafHeight leafWork)+2



end
end CurrentAFT.BinaryControlChoiceAverage

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryControlChoiceAverage.heightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryControlChoiceAverage.workPolynomial
  pure ()

end

section
























/-! # Computed ordering and rational local coefficient extraction

Selected output slots are sorted in their actual `Fin 4` order. The
canonical coefficient is independent of the arbitrary finite equivalence
used by the abstract construction, after its genuine symmetrization.
-/
namespace CurrentAFT.RationalCoefficientExtraction
open AFT DiffuseProfiles ProposalPrimary ActualControls
  ControlCoordinates ControlProduct
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def slotNumber (selected : Finset (Fin 4)) : selected → Fin selected.card :=
  (Finset.orderIsoOfFin selected rfl).symm

def atom (security bits source output : ℕ) : ℚ :=
  ((if source = output then 1 else 0) - 1 / (PublicParameterProgram.modulus security).count) /
    RationalProposalProgram.primary security bits output

def density (security bits : ℕ) (mass : (Fin 4 → ℕ) → ℚ) (selected : Finset (Fin 4))
    (output : Fin selected.card → ℕ) : ℚ :=
  ∑ source : Fin 4 → Fin (PublicParameterProgram.modulus security).count,
    mass (fun index => (source index).val) *
      ∏ slot : selected, atom security bits (source slot.val).val (output (slotNumber selected slot))

def normalized (security bits : ℕ) (mass : (Fin 4 → ℕ) → ℚ) (selected : Finset (Fin 4))
    (output : Fin selected.card → ℕ) : ℚ :=
  RationalTensorInverseProgram.current security bits selected.card (density security bits mass selected) output

def selectedKernel (security bits : ℕ) (mass : (Fin 4 → ℕ) → ℚ) (selected : Finset (Fin 4))
    (output : Fin selected.card → ℕ) : ℚ :=
  (1 / selected.card.factorial : ℚ) *
    ∑ permutation : Equiv.Perm (Fin selected.card), normalized security bits mass selected (output ∘ permutation)

noncomputable section
open scoped Classical
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSubtypeDecidableEq {Index : Type*} (selected : Finset Index) : DecidableEq selected := Classical.decEq _
attribute [local irreducible] Parameters.base primaryLaw

def orderedDensity (security : ℕ) (mass : (Fin 4 → Palette security) → ℝ) (selected : Finset (Fin 4))
    (output : Fin selected.card → Palette security) : ℝ :=
  LocalTensors.referenceRestrictedComponent (fun _ : Fin 4 => primaryLaw security)
    (fun _ : Fin 4 => LocalReferenceEnergy.uniformReference security) mass selected
      (fun slot => output (slotNumber selected slot))



def orderPermutation (selected : Finset (Fin 4)) : Equiv.Perm (Fin selected.card) :=
  (Fintype.equivFinOfCardEq (by simp : Fintype.card selected = selected.card)).symm.trans
    (Finset.orderIsoOfFin selected rfl).symm.toEquiv











def atomErrorConstant (security : ℕ) : ℝ :=
  16 * (Parameters.modulus security : ℝ)^2 * RationalRootMassProgram.primaryErrorConstant security









def extractionError (security degree : ℕ) (massBound massError : ℝ) : ℝ :=
  (Parameters.modulus security : ℝ)^4 *
    (massError + massBound * degree * atomErrorConstant security) *
      (4 * (Parameters.modulus security : ℝ))^degree

def extractionBound (security degree : ℕ) (massBound massError : ℝ) : ℝ :=
  (Parameters.modulus security : ℝ)^4 * (massBound + massError) *
    (4 * (Parameters.modulus security : ℝ))^degree





def normalizedError (security degree : ℕ) (massBound massError : ℝ) : ℝ :=
  RationalTensorInverseProgram.tensorErrorConstant security degree * extractionBound security degree massBound massError +
    (Parameters.modulus security : ℝ)^degree * (RationalTensorInverseProgram.actualBound security)^degree *
      extractionError security degree massBound massError









end
end CurrentAFT.RationalCoefficientExtraction

end

section




















/-! # Actual root-retained selected coefficient entries

The mass input is now the computed complete four-endpoint experiment,
including its common scalar. The entry error has no supplied physical
mass or operator estimate: it follows from the current proposal tables.
-/
namespace CurrentAFT.RationalSelectedRootProgram
open AFT DiffuseProfiles ProposalPrimary ActualControls
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def current (security bits : ℕ) (compensatorRoot attachmentRoot : ℤ)
    (score : ℕ → ℚ) (selected : Finset (Fin 4)) (output : Fin selected.card → ℕ) : ℚ :=
  RationalCoefficientExtraction.selectedKernel security bits
    (RationalRootMassProgram.primaryMass security bits compensatorRoot attachmentRoot score) selected output

noncomputable section
open scoped Classical
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSubtypeDecidableEq {Index : Type*} (selected : Finset Index) : DecidableEq selected := Classical.decEq _
attribute [local irreducible] Parameters.base primaryLaw









end
end CurrentAFT.RationalSelectedRootProgram

end

section






















/-! # The actual centered primary point column

The program centers a point score using its computed primary table.
The proof compares with the original exact `C_p delta` column, including
the error of that centering. Root masses have already been factored out.
-/
namespace CurrentAFT.RationalPrimaryColumnProgram
open AFT DiffuseProfiles ProposalPrimary ActualControls CoefficientHilbert
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def centerDelta (security bits source color : ℕ) : ℚ :=
  (if color = source then 1 else 0) - RationalProposalProgram.primary security bits source

def current (security bits : ℕ) (compensatorRoot attachmentRoot : ℤ) (primaryColor : ℕ)
    (selected : Finset (Fin 4)) (output : Fin selected.card → ℕ) : ℚ :=
  RationalSelectedRootProgram.current security bits compensatorRoot attachmentRoot
    (centerDelta security bits primaryColor) selected output

noncomputable section
open scoped Classical
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSubtypeDecidableEq {Index : Type*} (selected : Finset Index) : DecidableEq selected := Classical.decEq _
attribute [local irreducible] Parameters.base primaryLaw













def massErrorConstant (security : ℕ) : ℝ :=
  RationalRootMassProgram.primaryMassErrorConstant security +
    (2 * (Parameters.modulus security : ℝ)^2) * RationalRootMassProgram.primaryErrorConstant security



def errorConstant (security degree : ℕ) : ℝ :=
  RationalCoefficientExtraction.normalizedError security degree (2 * (Parameters.modulus security : ℝ)^2)
    (massErrorConstant security)



end
end CurrentAFT.RationalPrimaryColumnProgram

end

section
























/-! # Weighted point-source columns without source-reference reciprocals

The reference mass in exact point reconstruction cancels each centered
Dirac denominator before the joint point tensor is symmetrized.
-/
namespace CurrentAFT.WeightedPointKernelProgram
open AFT DiffuseProfiles ProposalPrimary ActualControls CanonicalReconstruction
  ControlCoordinates ControlProduct GradedControlAlgebra
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def bodyDelta (security bits source color : ℕ) : ℚ :=
  (if color = source then 1 else 0) - RationalProposalProgram.center security bits source

def current (security bits r s : ℕ) (sourcePrimary : Fin r → ℕ) (sourceBody : Fin s → ℕ)
    (colors : Fin r → ℕ) (centers : Fin s → ℕ) : ℚ :=
  RationalFamilyProductProgram.average r s (fun primaryOrder bodyOrder =>
    (∏ index, RationalPrimaryColumnProgram.centerDelta security bits (sourcePrimary index) (colors (primaryOrder index))) *
    ∏ index, bodyDelta security bits (sourceBody index) (centers (bodyOrder index)))

noncomputable section
open scoped Classical
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance safeDecidableEq (security : ℕ) : DecidableEq (SafePalette security) := Classical.decEq _
attribute [local irreducible] Parameters.base primaryLaw bodyReference

section Generic
variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]

def weightedTensor {r s : ℕ} (primary : FiniteDist Primary) (body : FiniteDist Body)
    (sourcePrimary : Fin r → Primary) (sourceBody : Fin s → Body) :
    DensityKernel (Primary := Primary) (Body := Body) r s :=
  fun colors centers => MixedKernel.canonicalPointBasis (fun _ : Fin r => primary) sourcePrimary colors *
    MixedKernel.canonicalPointBasis (fun _ : Fin s => body) sourceBody centers



end Generic

def actualKernel (security : ℕ) {r s : ℕ} (sourcePrimary : Fin r → Palette security)
    (sourceBody : Fin s → SafePalette security) :
    canonicalKernels (primaryLaw security) (bodyReference security) r s :=
  ((∏ index, (primaryLaw security).weight (sourcePrimary index)) *
    (∏ index, (bodyReference security).weight (sourceBody index))) •
      pointKernel (primaryLaw security) (bodyReference security) (primaryReference_positive security)
        (bodyReference_positive security) sourcePrimary sourceBody













def errorConstant (security r s : ℕ) : ℝ :=
  r * RationalRootMassProgram.primaryErrorConstant security +
    s * (RationalRootMassProgram.primaryErrorConstant security * Parameters.modulus security + 2)





end
end CurrentAFT.WeightedPointKernelProgram

end

section




























/-! Executed reference-weighted canonical point columns. Slot permutations are
finite stored arithmetic syntax fixed before security; each dynamic atom reads
its two palette positions and the generated proposal table. -/
namespace CurrentAFT.BinaryWeightedPointKernel
open AFT RationalNumerics BinaryArithmetic RationalRejectionProgram
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryReferenceTables.current

abbrev Color (security : ℕ) := Fin (PublicParameterProgram.modulus security).count
abbrev Atom (r s : ℕ) := (Fin r × Fin r) ⊕ (Fin s × Fin s)
abbrev Program (r s : ℕ) := StoredScalarProgram (Atom r s) RationalBits

def firstColor (security : ℕ) : Color security :=
  ⟨0, by rw [PublicParameterProgram.modulus_value]; exact (Parameters.modulus_spec security).2.pos⟩

def factor {degree : ℕ} (security : ℕ) (table : Vector RationalBits (PublicParameterProgram.modulus security).count)
    (source output : Vector (Color security) degree) (indices : Fin degree × Fin degree) : CountedValue RationalBits :=
  let input := readVector (firstColor security) source indices.1
  let color := readVector (firstColor security) output indices.2
  let matched := equalCounter color.value.val input.value.val
  let reference := readVector RationalBits.zero table input.value
  let negative := RationalBits.negate reference.value
  let difference := RationalBits.add (if matched.value then RationalBits.one else RationalBits.zero) negative.data
  ⟨difference.data,input.work+color.work+matched.work+reference.work+negative.work+difference.work+6⟩

 


def atom {r s : ℕ} (security : ℕ) (tables : BinaryReferenceTables.Result security)
    (sourcePrimary colors : Vector (Color security) r) (sourceBody centers : Vector (Color security) s) :
    Atom r s → CountedValue RationalBits
  | .inl indices => factor security tables.primary sourcePrimary colors indices
  | .inr indices => factor security tables.center sourceBody centers indices


def withTables {r s : ℕ} (security : ℕ) (program : Program r s) (tables : BinaryReferenceTables.Result security)
    (sourcePrimary colors : Vector (Color security) r) (sourceBody centers : Vector (Color security) s) : RationalResult :=
  let result := program.binaryRun (atom security tables sourcePrimary colors sourceBody centers)
  ⟨result.value,result.work+1⟩


def current {r s : ℕ} (security bits : ℕ) (program : Program r s)
    (sourcePrimary colors : Vector (Color security) r) (sourceBody centers : Vector (Color security) s) : RationalResult :=
  let tables := BinaryReferenceTables.current security bits
  let result := withTables security program tables sourcePrimary colors sourceBody centers
  ⟨result.data,tables.work+result.work+1⟩


def productList {Index : Type*} : List (ScalarProgram Index) → ScalarProgram Index
  | [] => .rational 1
  | head::tail => .multiply head (productList tail)

 

noncomputable section
open scoped Classical


def product {Index Leaf : Type*} [Fintype Index] (term : Index → ScalarProgram Leaf) : ScalarProgram Leaf :=
  productList (List.ofFn (fun index : Fin (Fintype.card Index) => term ((Fintype.equivFin Index).symm index)))

 


def pointSyntax (r s : ℕ) : ScalarProgram (Atom r s) :=
  .multiply (.rational ((r.factorial:ℚ)⁻¹*(s.factorial:ℚ)⁻¹))
    (FamilyProductSyntax.sum (fun primaryOrder : Equiv.Perm (Fin r) =>
      FamilyProductSyntax.sum (fun bodyOrder : Equiv.Perm (Fin s) =>
        .multiply (product (fun index : Fin r => .atom (.inl (index,primaryOrder index))))
          (product (fun index : Fin s => .atom (.inr (index,bodyOrder index)))))))

 

 


def atomWorkPolynomial (limit : ℕ) (height : Polynomial ℕ) : Polynomial ℕ :=
  let Q := BinaryProposalMetadata.sizePolynomial
  Polynomial.C (6*limit)+9*Q+2*RationalBits.primitiveWorkPolynomial (height+1)+30

 


def heightPolynomial {r s : ℕ} (program : Program r s) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFixedScalarProgram.heightPolynomial program (BinaryReferenceTables.heightPolynomial precision+1)

def workPolynomial {r s : ℕ} (program : Program r s) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryReferenceTables.currentWorkPolynomial precision+
    BinaryFixedScalarProgram.workPolynomial program (BinaryReferenceTables.heightPolynomial precision+1)
      (atomWorkPolynomial (r+s) (BinaryReferenceTables.heightPolynomial precision))+2

 

end
end CurrentAFT.BinaryWeightedPointKernel

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryWeightedPointKernel.atomWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryWeightedPointKernel.heightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryWeightedPointKernel.workPolynomial
  pure ()

end

section




























/-! # One finite program list for each fixed calibration order

The list is fixed before the security parameter. Runtime dispatch scans its
stored arity tags using executed counters. Choice occurs only in the proof
that this finite collection of static encoded programs exists.
-/
namespace CurrentAFT.BinaryFixedPointPrograms
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open GradedControlAlgebra
set_option maxHeartbeats 700000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

abbrev Program (order : ℕ) (arity : TruncatedArity order) :=
  BinaryWeightedPointKernel.Program arity.val.1.val arity.val.2.val
abbrev Entry (order : ℕ) := (arity : TruncatedArity order) × Program order arity

open FixedFamilyPrograms (matchArity matchArity_value matchArity_work)

def lookup (order : ℕ) (target : TruncatedArity order) : List (Entry order) → CountedValue (Program order target)
  | [] => ⟨.literal zero, 1⟩
  | entry::tail =>
      let equal := matchArity order entry.1 target
      if h : equal.value = true then
        let same := (matchArity_value order entry.1 target).mp h
        ⟨same ▸ entry.2, equal.work+2⟩
      else
        let result := lookup order target tail
        ⟨result.value, equal.work+result.work+2⟩




def current (security bits order : ℕ) (programs : List (Entry order)) (arity : TruncatedArity order)
    (sourcePrimary colors : Vector (BinaryWeightedPointKernel.Color security) arity.val.1.val)
    (sourceBody centers : Vector (BinaryWeightedPointKernel.Color security) arity.val.2.val) : RationalResult :=
  let selected := lookup order arity programs
  let value := BinaryWeightedPointKernel.current security bits selected.value sourcePrimary colors sourceBody centers
  ⟨value.data,selected.work+value.work+1⟩

noncomputable section
open scoped Classical BigOperators

def Correct (order : ℕ) (list : List (Entry order)) : Prop :=
  ∀ entry ∈ list, entry.2.meaning RationalBits.decode = BinaryWeightedPointKernel.pointSyntax entry.1.val.1.val entry.1.val.2.val

def Complete (order : ℕ) (list : List (Entry order)) : Prop :=
  ∀ arity, ∃ program : Program order arity, (⟨arity, program⟩ : Entry order) ∈ list








noncomputable def heightPolynomial (order : ℕ) (programs : List (Entry order)) (precision : Polynomial ℕ) : Polynomial ℕ :=
  ∑ arity : TruncatedArity order, BinaryWeightedPointKernel.heightPolynomial (lookup order arity programs).value precision
noncomputable def workPolynomial (order : ℕ) (programs : List (Entry order)) (precision : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (programs.length*(12*order+7)+2)+∑ arity : TruncatedArity order,
    BinaryWeightedPointKernel.workPolynomial (lookup order arity programs).value precision



end
end CurrentAFT.BinaryFixedPointPrograms

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryFixedPointPrograms.heightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryFixedPointPrograms.workPolynomial
  pure ()

end

section



















/-! # Composing two verified binary coefficient programs -/
namespace CurrentAFT.BinaryFamilyProductClosure
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
  RationalRejectionProgram BinaryFamilyProduct FixedFamilyPrograms
set_option maxHeartbeats 1200000
noncomputable section

def heightPolynomial (order : ℕ) (programs : List (Entry order)) (firstBits secondBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFamilyArithmetic.heightPolynomial order programs (firstBits+secondBits)
def workPolynomial (order : ℕ) (programs : List (Entry order))
    (firstBits secondBits firstWork secondWork : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFamilyArithmetic.workPolynomial order programs (firstBits+secondBits) (firstWork+secondWork)



end
end CurrentAFT.BinaryFamilyProductClosure

end

section





















/-! # Literal arithmetic for a centered uniform atom divided by its primary mass -/
namespace CurrentAFT.BinaryCoefficientAtomFormula
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

inductive Leaf where
  | point | population | primary
  deriving DecidableEq

def expression : ScalarProgram Leaf :=
  .multiply (.add (.atom .point) (.negate (.inverse (.atom .population)))) (.inverse (.atom .primary))



def leaf (point population primary : RationalBits) : Leaf→RationalBits
  | .point => point
  | .population => population
  | .primary => primary

def read (values : Leaf→RationalBits) (code : Leaf) : CountedValue RationalBits :=
  let result := RationalBits.copy (values code)
  ⟨result.data,result.work+1⟩

def current (point population primary : RationalBits) : RationalResult :=
  let result := expression.compileBinaryRun (read (leaf point population primary))
  ⟨result.value,result.work+1⟩



def height (bound : ℕ) := expression.nodes*(bound+3)
def work (bound : ℕ) := expression.nodes*(smallRationalEncodingWork 1+(4*bound+9)+primitiveWorkBound (height bound)+2)+2



noncomputable def heightPolynomial (bound : Polynomial ℕ) : Polynomial ℕ := Polynomial.C expression.nodes*(bound+3)
noncomputable def workPolynomial (bound : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C expression.nodes*(smallRationalEncodingPolynomial 1+(4*bound+9)+primitiveWorkPolynomial (heightPolynomial bound)+2)+2





end CurrentAFT.BinaryCoefficientAtomFormula

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryCoefficientAtomFormula.heightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryCoefficientAtomFormula.workPolynomial
  pure ()

end

section






























/-! Actual uniform-centering atoms, with computed prime and reference cache. -/
namespace CurrentAFT.BinaryCoefficientAtom
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryReferenceTables.current
abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

def current (security bits : ℕ) (source output : Fin (colors security)) : RationalResult :=
  let metadata := BinaryProposalMetadata.current security
  let reference := BinaryReferenceTables.current security bits
  let primary := readVector zero reference.primary output
  let point := BinaryMassLiftColumn.point source output
  let result := BinaryCoefficientAtomFormula.current point.data metadata.colors primary.value
  ⟨result.data,metadata.work+reference.work+primary.work+point.work+result.work+5⟩



noncomputable section
noncomputable def operandPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryProposalMetadata.sizePolynomial+BinaryReferenceTables.heightPolynomial precision+1
noncomputable def heightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryCoefficientAtomFormula.heightPolynomial (operandPolynomial precision)
noncomputable def workPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryProposalMetadata.currentWorkPolynomial+BinaryReferenceTables.currentWorkPolynomial precision+
    15*BinaryFirstInverseProgram.colorsPolynomial+15+BinaryCoefficientAtomFormula.workPolynomial (operandPolynomial precision)



end
end CurrentAFT.BinaryCoefficientAtom

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryCoefficientAtom.heightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryCoefficientAtom.operandPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryCoefficientAtom.workPolynomial
  pure ()

end

section


























/-! Actual binary columns of the density inverse, including the complete
stored delta input and its primary-reference conjugation. -/
namespace CurrentAFT.BinaryDensityInverseColumn
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits BinaryMassLiftColumn
open scoped BigOperators
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryDensityInverseProgram.current PublicParameterProgram.modulus

def current (security bits : ℕ) (source output : Fin (BinaryFirstInverseProgram.colors security)) : RationalResult :=
  let input := delta source
  let result := BinaryDensityInverseProgram.current security bits input.data output
  ⟨result.data, input.work+result.work+3⟩



noncomputable section
noncomputable def heightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryDensityInverseProgram.currentHeightPolynomial precision 1
noncomputable def workPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  let Q := BinaryFirstInverseProgram.colorsPolynomial
  Q*(12*Q+9)+2+BinaryDensityInverseProgram.currentWorkPolynomial precision 1+3



end
end CurrentAFT.BinaryDensityInverseColumn

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryDensityInverseColumn.workPolynomial
  pure ()

end

section































/-! # The full joint density-inverse tensor on explicitly enumerated binary tuples -/
namespace CurrentAFT.BinaryDensityInverseTensor
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryDensityInverseColumn.current BinaryFiniteProduct.current
  BinaryTupleSum.current

abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

def first (security : ℕ) : Fin (colors security) :=
  ⟨0, by rw [colors, BinaryFirstInverseProgram.colors, PublicParameterProgram.modulus_value]
         exact (Parameters.modulus_spec security).2.pos⟩

def column {degree : ℕ} (security bits : ℕ) (source output : Vector (Fin (colors security)) degree)
    (slot : Fin degree) : RationalResult :=
  let input := readVector (first security) source slot
  let result := readVector (first security) output slot
  let entry := BinaryDensityInverseColumn.current security bits input.value result.value
  ⟨entry.data, input.work+result.work+entry.work+3⟩



def term {degree : ℕ} (security bits : ℕ) (output : Vector (Fin (colors security)) degree)
    (profile : Vector (Fin (colors security)) degree → RationalResult)
    (source : Vector (Fin (colors security)) degree) : RationalResult :=
  let input := profile source
  let kernel := BinaryFiniteProduct.current degree (column security bits source output)
  let result := RationalBits.multiply input.data kernel.data
  ⟨result.data, input.work+kernel.work+result.work+3⟩



def current (security bits degree : ℕ) (output : Vector (Fin (colors security)) degree)
    (profile : Vector (Fin (colors security)) degree → RationalResult) : RationalResult :=
  let modulus := PublicParameterProgram.modulus security
  let result := BinaryTupleSum.current modulus.count degree (term security bits output profile)
  ⟨result.data, modulus.work+result.work+2⟩



noncomputable section





noncomputable def columnWorkPolynomial (degree : ℕ) (precision : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (6*degree+9)+BinaryDensityInverseColumn.workPolynomial precision
noncomputable def termHeightPolynomial (degree : ℕ) (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  inputBits+Polynomial.C degree*BinaryDensityInverseColumn.heightPolynomial precision
noncomputable def termWorkPolynomial (degree : ℕ) (precision inputBits inputWork : Polynomial ℕ) : Polynomial ℕ :=
  inputWork+BinaryFiniteProduct.workPolynomial degree (BinaryDensityInverseColumn.heightPolynomial precision)
    (columnWorkPolynomial degree precision)+primitiveWorkPolynomial (termHeightPolynomial degree precision inputBits)+3
noncomputable def heightPolynomial (degree : ℕ) (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryTupleSum.heightPolynomial BinaryFirstInverseProgram.colorsPolynomial degree (termHeightPolynomial degree precision inputBits)
noncomputable def workPolynomial (degree : ℕ) (precision inputBits inputWork : Polynomial ℕ) : Polynomial ℕ :=
  PublicParameterProgram.workPolynomial+
    BinaryTupleSum.workPolynomial BinaryFirstInverseProgram.colorsPolynomial degree
      (termHeightPolynomial degree precision inputBits) (termWorkPolynomial degree precision inputBits inputWork)+2







end
end CurrentAFT.BinaryDensityInverseTensor

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryDensityInverseTensor.columnWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryDensityInverseTensor.heightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryDensityInverseTensor.termHeightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryDensityInverseTensor.termWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryDensityInverseTensor.workPolynomial
  pure ()

end

section



























/-! Complete four-endpoint coefficient extraction. The selected slots are
stored fixed metadata; all four source colors are summed jointly. -/
namespace CurrentAFT.BinaryCoefficientDensity
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryCoefficientAtom.current BinaryFiniteProduct.current BinaryTupleSum.current
variable {totalSlots : ℕ}

abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

def column {degree : ℕ} (security bits : ℕ) (slots : Vector (Fin totalSlots) degree)
    (source : Vector (Fin (colors security)) totalSlots) (output : Vector (Fin (colors security)) degree) (index : Fin degree) : RationalResult :=
  let position := readVector ⟨0, by have h := (slots.get index).isLt; omega⟩ slots index
  let input := readVector (BinaryDensityInverseTensor.first security) source position.value
  let value := readVector (BinaryDensityInverseTensor.first security) output index
  let result := BinaryCoefficientAtom.current security bits input.value value.value
  ⟨result.data,position.work+input.work+value.work+result.work+4⟩



def term {degree : ℕ} (security bits : ℕ) (slots : Vector (Fin totalSlots) degree)
    (output : Vector (Fin (colors security)) degree)
    (mass : Vector (Fin (colors security)) totalSlots → RationalResult) (source : Vector (Fin (colors security)) totalSlots) : RationalResult :=
  let value := mass source
  let product := BinaryFiniteProduct.current degree (column security bits slots source output)
  let result := RationalBits.multiply value.data product.data
  ⟨result.data,value.work+product.work+result.work+3⟩



def current {degree : ℕ} (security bits : ℕ) (slots : Vector (Fin totalSlots) degree)
    (output : Vector (Fin (colors security)) degree) (mass : Vector (Fin (colors security)) totalSlots → RationalResult) : RationalResult :=
  let modulus := PublicParameterProgram.modulus security
  let result := BinaryTupleSum.current modulus.count totalSlots (term security bits slots output mass)
  ⟨result.data,modulus.work+result.work+2⟩





noncomputable section





noncomputable def columnWorkPolynomial (totalSlots degree : ℕ) (precision : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (6*degree+3*totalSlots+13)+BinaryCoefficientAtom.workPolynomial precision
noncomputable def termHeightPolynomial (degree : ℕ) (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  inputBits+Polynomial.C degree*BinaryCoefficientAtom.heightPolynomial precision
noncomputable def termWorkPolynomial (totalSlots degree : ℕ) (precision inputBits inputWork : Polynomial ℕ) : Polynomial ℕ :=
  inputWork+BinaryFiniteProduct.workPolynomial degree (BinaryCoefficientAtom.heightPolynomial precision)
    (columnWorkPolynomial totalSlots degree precision)+primitiveWorkPolynomial (termHeightPolynomial degree precision inputBits)+3
noncomputable def heightPolynomial (totalSlots degree : ℕ) (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryTupleSum.heightPolynomial BinaryFirstInverseProgram.colorsPolynomial totalSlots (termHeightPolynomial degree precision inputBits)
noncomputable def workPolynomial (totalSlots degree : ℕ) (precision inputBits inputWork : Polynomial ℕ) : Polynomial ℕ :=
  PublicParameterProgram.workPolynomial+BinaryTupleSum.workPolynomial BinaryFirstInverseProgram.colorsPolynomial totalSlots
    (termHeightPolynomial degree precision inputBits) (termWorkPolynomial totalSlots degree precision inputBits inputWork)+2







end
end CurrentAFT.BinaryCoefficientDensity

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryCoefficientDensity.columnWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryCoefficientDensity.heightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryCoefficientDensity.termHeightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryCoefficientDensity.termWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryCoefficientDensity.workPolynomial
  pure ()

end

section



























/-! Symmetrization by a finite stored arithmetic program. This program is
fixed before security; all runtime tuple reads and arithmetic are charged. -/
namespace CurrentAFT.BinaryStoredSymmetrization
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

abbrev Slots (degree : ℕ) := Vector (Fin degree) degree
abbrev Program (degree : ℕ) := StoredScalarProgram (Slots degree) RationalBits

def gatherEntry {degree : ℕ} (security : ℕ)
    (input : Vector (Fin (BinaryFirstInverseProgram.colors security)) degree) (slots : Slots degree)
    (index : Fin degree) : CountedValue (Fin (BinaryFirstInverseProgram.colors security)) :=
  let position := readVector ⟨0, by have h := index.isLt; omega⟩ slots index
  let result := readVector (BinaryDensityInverseTensor.first security) input position.value
  ⟨result.value,position.work+result.work+1⟩

def gather {degree : ℕ} (security : ℕ)
    (input : Vector (Fin (BinaryFirstInverseProgram.colors security)) degree) (slots : Slots degree) :
    CountedValue (Vector (Fin (BinaryFirstInverseProgram.colors security)) degree) :=
  storeData degree (gatherEntry security input slots)





def leaf {degree : ℕ} (security : ℕ)
    (input : Vector (Fin (BinaryFirstInverseProgram.colors security)) degree)
    (kernel : Vector (Fin (BinaryFirstInverseProgram.colors security)) degree → RationalResult)
    (slots : Slots degree) : CountedValue RationalBits :=
  let word := gather security input slots
  let value := kernel word.value
  ⟨value.data,word.work+value.work+2⟩

def current {degree : ℕ} (security : ℕ) (program : Program degree)
    (input : Vector (Fin (BinaryFirstInverseProgram.colors security)) degree)
    (kernel : Vector (Fin (BinaryFirstInverseProgram.colors security)) degree → RationalResult) : RationalResult :=
  let value := program.binaryRun (leaf security input kernel)
  ⟨value.value,value.work+1⟩

noncomputable section
open scoped Classical

def meanSyntax (degree : ℕ) : ScalarProgram (Slots degree) :=
  .multiply (.rational (1/(degree.factorial:ℚ)))
    (FamilyProductSyntax.sum (fun permutation : Equiv.Perm (Fin degree) => .atom (Vector.ofFn permutation)))





noncomputable def heightPolynomial {degree : ℕ} (program : Program degree) (inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFixedScalarProgram.heightPolynomial program inputBits
noncomputable def workPolynomial {degree : ℕ} (program : Program degree) (inputBits inputWork : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFixedScalarProgram.workPolynomial program inputBits (Polynomial.C (degree*(6*degree+9)+4)+inputWork)+1



end
end CurrentAFT.BinaryStoredSymmetrization

end

section



























/-! Stored-slot joint density extraction, tensor inversion, and exact
symmetrization, implemented by binary arithmetic and full finite sums. -/
namespace CurrentAFT.BinaryCoefficientExtraction
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
variable {totalSlots degree : ℕ}
abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

def normalized (security bits : ℕ) (slots : Vector (Fin totalSlots) degree)
    (output : Vector (Fin (colors security)) degree) (mass : Vector (Fin (colors security)) totalSlots → RationalResult) : RationalResult :=
  BinaryDensityInverseTensor.current security bits degree output (fun source => BinaryCoefficientDensity.current security bits slots source mass)

def current (security bits : ℕ) (slots : Vector (Fin totalSlots) degree)
    (program : BinaryStoredSymmetrization.Program degree)
    (output : Vector (Fin (colors security)) degree) (mass : Vector (Fin (colors security)) totalSlots → RationalResult) : RationalResult :=
  BinaryStoredSymmetrization.current security program output (fun source => normalized security bits slots source mass)



noncomputable section
open scoped Classical



noncomputable def normalizedHeightPolynomial (totalSlots degree : ℕ) (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryDensityInverseTensor.heightPolynomial degree precision (BinaryCoefficientDensity.heightPolynomial totalSlots degree precision inputBits)
noncomputable def normalizedWorkPolynomial (totalSlots degree : ℕ) (precision inputBits inputWork : Polynomial ℕ) : Polynomial ℕ :=
  BinaryDensityInverseTensor.workPolynomial degree precision (BinaryCoefficientDensity.heightPolynomial totalSlots degree precision inputBits)
    (BinaryCoefficientDensity.workPolynomial totalSlots degree precision inputBits inputWork)
noncomputable def heightPolynomial (totalSlots : ℕ) (program : BinaryStoredSymmetrization.Program degree)
    (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryStoredSymmetrization.heightPolynomial program (normalizedHeightPolynomial totalSlots degree precision inputBits)
noncomputable def workPolynomial (totalSlots : ℕ) (program : BinaryStoredSymmetrization.Program degree)
    (precision inputBits inputWork : Polynomial ℕ) : Polynomial ℕ :=
  BinaryStoredSymmetrization.workPolynomial program (normalizedHeightPolynomial totalSlots degree precision inputBits)
    (normalizedWorkPolynomial totalSlots degree precision inputBits inputWork)





end
end CurrentAFT.BinaryCoefficientExtraction

end

section
























/-! # Computed ordering and rational local coefficient extraction

Selected output slots are sorted in their actual `Fin 3` order. The
canonical coefficient is independent of the arbitrary finite equivalence
used by the abstract construction, after its genuine symmetrization.
-/
namespace CurrentAFT.RationalLegCoefficientExtraction
open AFT DiffuseProfiles ProposalPrimary ActualControls
  ControlCoordinates ControlProduct
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def slotNumber (selected : Finset (Fin 3)) : selected → Fin selected.card :=
  (Finset.orderIsoOfFin selected rfl).symm

def atom (security bits source output : ℕ) : ℚ :=
  ((if source = output then 1 else 0) - 1 / (PublicParameterProgram.modulus security).count) /
    RationalProposalProgram.primary security bits output

def density (security bits : ℕ) (mass : (Fin 3 → ℕ) → ℚ) (selected : Finset (Fin 3))
    (output : Fin selected.card → ℕ) : ℚ :=
  ∑ source : Fin 3 → Fin (PublicParameterProgram.modulus security).count,
    mass (fun index => (source index).val) *
      ∏ slot : selected, atom security bits (source slot.val).val (output (slotNumber selected slot))

def normalized (security bits : ℕ) (mass : (Fin 3 → ℕ) → ℚ) (selected : Finset (Fin 3))
    (output : Fin selected.card → ℕ) : ℚ :=
  RationalTensorInverseProgram.current security bits selected.card (density security bits mass selected) output

def selectedKernel (security bits : ℕ) (mass : (Fin 3 → ℕ) → ℚ) (selected : Finset (Fin 3))
    (output : Fin selected.card → ℕ) : ℚ :=
  (1 / selected.card.factorial : ℚ) *
    ∑ permutation : Equiv.Perm (Fin selected.card), normalized security bits mass selected (output ∘ permutation)

noncomputable section
open scoped Classical
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSubtypeDecidableEq {Index : Type*} (selected : Finset Index) : DecidableEq selected := Classical.decEq _
attribute [local irreducible] Parameters.base primaryLaw

def orderedDensity (security : ℕ) (mass : (Fin 3 → Palette security) → ℝ) (selected : Finset (Fin 3))
    (output : Fin selected.card → Palette security) : ℝ :=
  LocalTensors.referenceRestrictedComponent (fun _ : Fin 3 => primaryLaw security)
    (fun _ : Fin 3 => LocalReferenceEnergy.uniformReference security) mass selected
      (fun slot => output (slotNumber selected slot))



def orderPermutation (selected : Finset (Fin 3)) : Equiv.Perm (Fin selected.card) :=
  (Fintype.equivFinOfCardEq (by simp : Fintype.card selected = selected.card)).symm.trans
    (Finset.orderIsoOfFin selected rfl).symm.toEquiv











def atomErrorConstant (security : ℕ) : ℝ :=
  16 * (Parameters.modulus security : ℝ)^2 * RationalRootMassProgram.primaryErrorConstant security









def extractionError (security degree : ℕ) (massBound massError : ℝ) : ℝ :=
  (Parameters.modulus security : ℝ)^3 *
    (massError + massBound * degree * atomErrorConstant security) *
      (4 * (Parameters.modulus security : ℝ))^degree

def extractionBound (security degree : ℕ) (massBound massError : ℝ) : ℝ :=
  (Parameters.modulus security : ℝ)^3 * (massBound + massError) *
    (4 * (Parameters.modulus security : ℝ))^degree





def normalizedError (security degree : ℕ) (massBound massError : ℝ) : ℝ :=
  RationalTensorInverseProgram.tensorErrorConstant security degree * extractionBound security degree massBound massError +
    (Parameters.modulus security : ℝ)^degree * (RationalTensorInverseProgram.actualBound security)^degree *
      extractionError security degree massBound massError









end
end CurrentAFT.RationalLegCoefficientExtraction

end

section



























/-! # The executed joint extractor for the three actual leg endpoints -/
namespace CurrentAFT.BinaryLegCoefficientExtraction
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security





noncomputable section
open scoped Classical



end
end CurrentAFT.BinaryLegCoefficientExtraction

end

section


























/-! Literal selected-slot tables for the complete actual three-output leg. -/
namespace CurrentAFT.RationalLegFamilyTable
open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates GradedControlAlgebra
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def insertSelected {Scalar Primary Body : Type*} [Zero Scalar] (order : ℕ)
    (selected : Finset (Fin 3)) (value : (Fin selected.card → Primary) → Scalar) :
    RationalFamilyProductProgram.Table Scalar Primary Body order :=
  fun arity colors _ => if hmatch : selected.card = arity.val.1.val ∧ 0 = arity.val.2.val then
    value (colors ∘ finCongr hmatch.1) else 0

def higher (security bits order : ℕ) (mass : (Fin 3 → ℕ) → ℚ) :
    RationalFamilyProductProgram.Table ℚ ℕ ℕ order := fun arity colors centers =>
  ∑ selected ∈ (Finset.univ : Finset (Finset (Fin 3))).filter (fun selected => 2 ≤ selected.card),
    insertSelected order selected (RationalLegCoefficientExtraction.selectedKernel security bits mass selected) arity colors centers

def positive (security bits order : ℕ) (mass : (Fin 3 → ℕ) → ℚ) :
    RationalFamilyProductProgram.Table ℚ ℕ ℕ order := fun arity colors centers =>
  RationalFamilyProductProgram.unit order arity colors centers +
    ∑ selected ∈ (Finset.univ : Finset (Finset (Fin 3))).erase ∅,
      insertSelected order selected (RationalLegCoefficientExtraction.selectedKernel security bits mass selected) arity colors centers

noncomputable section
open scoped Classical
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSubtypeDecidableEq {Index : Type*} (selected : Finset Index) : DecidableEq selected := Classical.decEq _
attribute [local irreducible] Parameters.base primaryLaw





def higherError (security : ℕ) (massBound massError : ℝ) : ℝ :=
  ∑ selected ∈ (Finset.univ : Finset (Finset (Fin 3))).filter (fun selected => 2 ≤ selected.card),
    RationalLegCoefficientExtraction.normalizedError security selected.card massBound massError







def positiveError (security : ℕ) (massError : ℝ) : ℝ :=
  ∑ selected ∈ (Finset.univ : Finset (Finset (Fin 3))).erase ∅,
    RationalLegCoefficientExtraction.normalizedError security selected.card 1 massError




end
end CurrentAFT.RationalLegFamilyTable

end

section





























/-! # A stored three-endpoint subset inserted in its actual coefficient fiber -/
namespace CurrentAFT.BinaryLegSelectedCoefficient
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
  GradedControlAlgebra RationalRejectionProgram BinaryFamilyProduct
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

structure Entry where
  selected : Finset (Fin 3)
  slots : Vector (Fin 3) selected.card
  program : BinaryStoredSymmetrization.Program selected.card

def finite (security bits order : ℕ) (entry : Entry)
    (mass : Vector (Fin (BinaryFirstInverseProgram.colors security)) 3 → RationalResult) :
    BinaryFiniteCoefficient.FiniteProgram security order := fun arity colors centers =>
  let result := BinaryCoefficientFiber.current security arity.val.1.val arity.val.2.val entry.selected.card 0 colors centers
    (fun inputs _ => BinaryCoefficientExtraction.current security bits entry.slots entry.program inputs mass)
  ⟨result.data,result.work+4⟩

def current (security bits order : ℕ) (entry : Entry)
    (mass : Vector (Fin (BinaryFirstInverseProgram.colors security)) 3 → RationalResult) : CoefficientProgram order :=
  BinaryFiniteCoefficient.lift security order (finite security bits order entry mass)

noncomputable section
open scoped Classical





def heightPolynomial (entry : Entry) (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryCoefficientExtraction.heightPolynomial 3 entry.program precision inputBits
def finiteWorkPolynomial (order : ℕ) (entry : Entry) (precision inputBits inputWork : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (6*order+8*entry.selected.card+34)+BinaryCoefficientExtraction.workPolynomial 3 entry.program precision inputBits inputWork
def workPolynomial (order : ℕ) (entry : Entry) (precision inputBits inputWork : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFiniteCoefficient.workPolynomial order (finiteWorkPolynomial order entry precision inputBits inputWork)





def Valid (entry : Entry) : Prop :=
  (∀ index, entry.slots.get index=((Finset.orderIsoOfFin entry.selected rfl) index).val) ∧
    entry.program.meaning RationalBits.decode=BinaryStoredSymmetrization.meanSyntax entry.selected.card





end
end CurrentAFT.BinaryLegSelectedCoefficient

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryLegSelectedCoefficient.finiteWorkPolynomial
  pure ()

end

section


























/-! Summation over a finite stored list of local subset descriptors. Each
runtime descriptor read and each rational addition is actually executed. -/
namespace CurrentAFT.BinarySubsetCoefficientSum
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
  GradedControlAlgebra BinaryFamilyProduct
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
variable {Descriptor : Type*} {count : ℕ}

def term (order : ℕ) (fallback : Descriptor) (entries : Vector Descriptor count)
    (evaluate : Descriptor → CoefficientProgram order) (arity : TruncatedArity order)
    (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val) (index : Fin count) : RationalResult :=
  let entry := readVector fallback entries index
  let value := evaluate entry.value arity colors centers
  ⟨value.value,entry.work+value.work+2⟩

def current (order : ℕ) (fallback : Descriptor) (entries : Vector Descriptor count)
    (evaluate : Descriptor → CoefficientProgram order) : CoefficientProgram order :=
  fun arity colors centers =>
    let result := sumFin count (term order fallback entries evaluate arity colors centers)
    ⟨result.data,result.work+1⟩



noncomputable section
open scoped Classical





noncomputable def heightPolynomial (count : ℕ) (leafBits : Polynomial ℕ) : Polynomial ℕ := Polynomial.C count*(leafBits+1)
noncomputable def workPolynomial (count : ℕ) (leafBits leafWork : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C count*(Polynomial.C (3*count+5)+leafWork+primitiveWorkPolynomial (Polynomial.C (count+1)*(leafBits+1))+2)+3



end
end CurrentAFT.BinarySubsetCoefficientSum

end

section





























/-! # All eight stored subsets of the actual three-endpoint joint mass -/
namespace CurrentAFT.BinaryLegFamily
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
  GradedControlAlgebra RationalRejectionProgram BinaryFamilyProduct
open BinaryLegSelectedCoefficient
open scoped BigOperators
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def guarded (security bits order lower : ℕ) (entry : Entry)
    (mass : Vector (Fin (BinaryFirstInverseProgram.colors security)) 3 → RationalResult) : CoefficientProgram order :=
  fun arity colors centers =>
    let shape := lessCounter (lower-1) entry.selected.card
    if shape.value then
      let result := BinaryLegSelectedCoefficient.current security bits order entry mass arity colors centers
      ⟨result.value,shape.work+result.work+2⟩
    else ⟨zero,shape.work+2⟩

def sum (security bits order lower : ℕ) (fallback : Entry) (entries : Vector Entry 8)
    (mass : Vector (Fin (BinaryFirstInverseProgram.colors security)) 3 → RationalResult) : CoefficientProgram order :=
  BinarySubsetCoefficientSum.current order fallback entries (fun entry => guarded security bits order lower entry mass)

def higher (security bits order : ℕ) (fallback : Entry) (entries : Vector Entry 8)
    (mass : Vector (Fin (BinaryFirstInverseProgram.colors security)) 3 → RationalResult) : CoefficientProgram order :=
  sum security bits order 2 fallback entries mass

def positive (security bits order : ℕ) (fallback : Entry) (entries : Vector Entry 8)
    (mass : Vector (Fin (BinaryFirstInverseProgram.colors security)) 3 → RationalResult) : CoefficientProgram order :=
  fun arity colors centers =>
    let unit := BinaryFamilyPower.unit order arity colors centers
    let terms := sum security bits order 1 fallback entries mass arity colors centers
    let result := RationalBits.add unit.value terms.value
    ⟨result.data,unit.work+terms.work+result.work+2⟩

noncomputable section
open scoped Classical









end
end CurrentAFT.BinaryLegFamily

end

section

























/-! # Full joint subset-table production with every stored read charged -/
namespace CurrentAFT.BinaryLegFamily
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
  GradedControlAlgebra RationalRejectionProgram BinaryFamilyProduct
open BinaryLegSelectedCoefficient
open scoped BigOperators
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
noncomputable section

def leafHeightPolynomial (entries : Vector Entry 8) (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  ∑ index : Fin 8, BinaryLegSelectedCoefficient.heightPolynomial (entries.get index) precision inputBits
def leafWorkPolynomial (order lower : ℕ) (entries : Vector Entry 8) (precision inputBits inputWork : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (3*lower+13)+∑ index : Fin 8,
    BinaryLegSelectedCoefficient.workPolynomial order (entries.get index) precision inputBits inputWork



def sumHeightPolynomial (entries : Vector Entry 8) (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinarySubsetCoefficientSum.heightPolynomial 8 (leafHeightPolynomial entries precision inputBits)
def sumWorkPolynomial (order lower : ℕ) (entries : Vector Entry 8) (precision inputBits inputWork : Polynomial ℕ) : Polynomial ℕ :=
  BinarySubsetCoefficientSum.workPolynomial 8 (leafHeightPolynomial entries precision inputBits)
    (leafWorkPolynomial order lower entries precision inputBits inputWork)



def positiveHeightPolynomial (entries : Vector Entry 8) (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  sumHeightPolynomial entries precision inputBits+1
def positiveWorkPolynomial (order : ℕ) (entries : Vector Entry 8) (precision inputBits inputWork : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (12*order+8)+sumWorkPolynomial order 1 entries precision inputBits inputWork+
    primitiveWorkPolynomial (sumHeightPolynomial entries precision inputBits)



end
end CurrentAFT.BinaryLegFamily

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryLegFamily.leafHeightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryLegFamily.leafWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryLegFamily.positiveHeightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryLegFamily.positiveWorkPolynomial
  pure ()

end

section



























/-! The local pair reads its two endpoints from the stored joint four-word. -/
namespace CurrentAFT.BinaryFourPointPair
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus
abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

def current (security bits : ℕ) (primary : Fin (colors security)) (scalar : IntegerBits)
    (word : Vector (Fin (colors security)) 4) : RationalResult :=
  let first := readVector (BinaryDensityInverseTensor.first security) word 1
  let second := readVector (BinaryDensityInverseTensor.first security) word 2
  let firstCode := canonicalCounter first.value.val
  let secondCode := canonicalCounter second.value.val
  let pair := BinaryPairProgram.current security bits primary.val scalar.negative scalar.digits firstCode.digits secondCode.digits
  ⟨pair.data,first.work+second.work+firstCode.work+secondCode.work+pair.work+5⟩



noncomputable section
noncomputable def inputPolynomial (inputBits : Polynomial ℕ) : Polynomial ℕ := inputBits+BinaryFirstInverseProgram.colorsPolynomial
noncomputable def heightPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryPairProgram.currentHeightPolynomial precision (inputPolynomial inputBits)
noncomputable def workPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  100*(BinaryFirstInverseProgram.colorsPolynomial+1)^2+35+
    BinaryPairProgram.currentWorkPolynomial precision (inputPolynomial inputBits)



end
end CurrentAFT.BinaryFourPointPair

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryFourPointPair.workPolynomial
  pure ()

end

section
























/-! # Materialized root profiles and exact binary convolution resources -/
namespace CurrentAFT.BinaryRootProfile
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open UniformBodyProfiles (BodyRole)
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryReferenceTables.current BinaryPaletteLookup.current
  BinaryShiftedSafeProfile.current PublicParameterProgram.modulus BinaryActivationProgram.cutoff
  BinaryRootConvolution.current IntegerBits.residue signedAdd
noncomputable section

def keyBitsPolynomial (rootBits inputBits : Polynomial ℕ) : Polynomial ℕ :=
  rootBits+inputBits+BinaryFirstInverseProgram.colorsPolynomial+1
def keyWorkPolynomial (rootBits inputBits : Polynomial ℕ) : Polynomial ℕ :=
  PublicParameterProgram.workPolynomial+50*(BinaryFirstInverseProgram.colorsPolynomial+1)^2+
    20*(rootBits+inputBits)+8+60*(rootBits+inputBits+BinaryFirstInverseProgram.colorsPolynomial+2)^2+14



def shiftedHeightPolynomial (precision queueBits rootBits inputBits : Polynomial ℕ) : Polynomial ℕ :=
  preRootHeightPolynomial precision queueBits (keyBitsPolynomial rootBits inputBits)
def shiftedWorkPolynomial (precision queueBits rootBits inputBits : Polynomial ℕ) : Polynomial ℕ :=
  keyWorkPolynomial rootBits inputBits+preRootWorkPolynomial precision queueBits (keyBitsPolynomial rootBits inputBits)+2



def profileHeightPolynomial (precision queueBits : Polynomial ℕ) : Polynomial ℕ :=
  preRootHeightPolynomial precision queueBits BinaryFirstInverseProgram.colorsPolynomial
def profileWorkPolynomial (precision queueBits : Polynomial ℕ) : Polynomial ℕ :=
  50*(BinaryFirstInverseProgram.colorsPolynomial+1)^2+
    preRootWorkPolynomial precision queueBits BinaryFirstInverseProgram.colorsPolynomial+2



def meanHeightPolynomial (precision queueBits inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryRootConvolution.heightPolynomial precision inputBits (profileHeightPolynomial precision queueBits)
def meanWorkPolynomial (precision queueBits inputBits : Polynomial ℕ) : Polynomial ℕ :=
  PublicParameterProgram.workPolynomial+
    BinaryFirstInverseProgram.colorsPolynomial*(profileWorkPolynomial precision queueBits+2)+2+
    BinaryRootConvolution.workPolynomial precision inputBits (profileHeightPolynomial precision queueBits)+3



end
end CurrentAFT.BinaryRootProfile

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryRootProfile.keyBitsPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryRootProfile.meanWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryRootProfile.profileWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryRootProfile.shiftedWorkPolynomial
  pure ()

end

section

































/-! The compensator equality and attachment use their actual retained roots
and the same scalar as the pair. No hidden root is replaced by a marginal. -/
namespace CurrentAFT.BinaryRootControlRest
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryRootProfile.key BinaryShiftedSafeProfile.current
abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

def current (security : ℕ) (compensator attachment scalar : IntegerBits)
    (center : Fin (colors security)) (word : Vector (Fin (colors security)) 4) : RationalResult :=
  let first := readVector (BinaryDensityInverseTensor.first security) word 0
  let last := readVector (BinaryDensityInverseTensor.first security) word 3
  let firstCode := canonicalCounter first.value.val
  let lastCode := canonicalCounter last.value.val
  let centerCode := canonicalCounter center.val
  let negative := IntegerBits.negate compensator
  let key := BinaryRootProfile.key security negative.value centerCode.digits
  let matched := signedEqual false false key.digits firstCode.digits
  let shift := IntegerBits.add attachment scalar
  let body := BinaryShiftedSafeProfile.current security shift.value lastCode.digits
  ⟨if matched.value then body.data else zero,
    first.work+last.work+firstCode.work+lastCode.work+centerCode.work+negative.work+key.work+matched.work+shift.work+body.work+10⟩



noncomputable section
noncomputable def heightPolynomial (inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryShiftedSafeProfile.heightPolynomial (inputBits+1) BinaryFirstInverseProgram.colorsPolynomial
noncomputable def workPolynomial (inputBits : Polynomial ℕ) : Polynomial ℕ :=
  let Q := BinaryFirstInverseProgram.colorsPolynomial
  let K := BinaryRootProfile.keyBitsPolynomial inputBits Q
  150*(Q+1)^2+20*inputBits+100+BinaryRootProfile.keyWorkPolynomial inputBits Q+
    48*(K+Q)+BinaryShiftedSafeProfile.workPolynomial (inputBits+1) Q



end
end CurrentAFT.BinaryRootControlRest

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryRootControlRest.workPolynomial
  pure ()

end

section






















/-! # Computed independent positive four-endpoint mass

Both compensator and attachment roots are independently averaged, while
one and the same scalar is retained in the pair and attachment. Every
leaf is an actual rational proposal, local pair, or Gaussian table entry.
-/
namespace CurrentAFT.RationalPositiveReferenceProgram
open AFT GaussianSource RationalNumerics DiffuseProfiles ProposalPrimary
  RationalProposalProgram LocalReferenceEnergy RationalRootMassProgram
open scoped BigOperators
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def fixedMass (security bits : ℕ) (compensatorRoot attachmentRoot scalar : ℤ)
    (word : Fin 4 → ℕ) : ℚ :=
  ∑ primaryColor : Fin (PublicParameterProgram.modulus security).count,
    ∑ centerColor : Fin (PublicParameterProgram.modulus security).count,
      primary security bits primaryColor.val * center security bits centerColor.val *
        LocalPairProgram.current security bits primaryColor.val scalar (word 1) (word 2) *
          controlRest security compensatorRoot attachmentRoot scalar centerColor.val word

def current (security bits : ℕ) (word : Fin 4 → ℕ) : ℚ :=
  ∑ index : Fin (2*(Parameters.sourceCutoff security-1)+1),
    let scalar := AFT.FiniteConvolutionProgram.windowIndexEquiv (Parameters.sourceCutoff security-1) index
    gaussianWeight security (Parameters.sourceCutoff security - 1) bits scalar *
      seedEvaluate security bits (fun compensator => seedEvaluate security bits (fun attachment =>
        fixedMass security bits (actualBlur security compensator) (actualBlur security attachment) scalar.val word))

noncomputable section
open scoped Classical
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base primaryLaw centerLaw









def fixedErrorConstant (security : ℕ) : ℝ :=
  (Parameters.modulus security : ℝ)^2 * (4 * primaryErrorConstant security +
    4 * (primaryErrorConstant security * Parameters.modulus security + 2) + 3)



def approximateRootLaw (security bits : ℕ) : FiniteDist (IndependentReferenceEnergy.Roots security) :=
  (windowApproxLaw (WindowGaussianSampler.squaredWidth security) (Parameters.sourceCutoff security - 1) bits).prod
    ((approximateSeedLaw security bits).prod (approximateSeedLaw security bits))





def errorConstant (security : ℕ) : ℝ := fixedErrorConstant security + 7



end
end CurrentAFT.RationalPositiveReferenceProgram

end

section





























/-! Actual four-endpoint positive reference mass before scalar/root averaging. -/
namespace CurrentAFT.BinaryPositiveReference
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryReferenceTables.current
  BinaryFourPointPair.current BinaryRootControlRest.current
abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

def term (security bits : ℕ) (compensator attachment scalar : IntegerBits)
    (word : Vector (Fin (colors security)) 4) (primary center : Fin (colors security)) : RationalResult :=
  let references := BinaryReferenceTables.current security bits
  let p := readVector zero references.primary primary
  let b := readVector zero references.center center
  let pair := BinaryFourPointPair.current security bits primary scalar word
  let rest := BinaryRootControlRest.current security compensator attachment scalar center word
  let first := RationalBits.multiply p.value b.value
  let second := RationalBits.multiply first.data pair.data
  let final := RationalBits.multiply second.data rest.data
  ⟨final.data,references.work+p.work+b.work+pair.work+rest.work+first.work+second.work+final.work+8⟩



def fixedMass (security bits : ℕ) (compensator attachment scalar : IntegerBits)
    (word : Vector (Fin (colors security)) 4) : RationalResult :=
  let modulus := PublicParameterProgram.modulus security
  let result := sumFin modulus.count (fun primary => sumFin modulus.count (term security bits compensator attachment scalar word primary))
  ⟨result.data,modulus.work+result.work+2⟩



noncomputable section
noncomputable def termHeightPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  2*BinaryReferenceTables.heightPolynomial precision+BinaryFourPointPair.heightPolynomial precision inputBits+
    BinaryRootControlRest.heightPolynomial inputBits
noncomputable def termWorkPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryReferenceTables.currentWorkPolynomial precision+6*BinaryFirstInverseProgram.colorsPolynomial+14+
    BinaryFourPointPair.workPolynomial precision inputBits+BinaryRootControlRest.workPolynomial inputBits+
    3*primitiveWorkPolynomial (termHeightPolynomial precision inputBits)



noncomputable def innerHeightPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFirstInverseProgram.colorsPolynomial*(termHeightPolynomial precision inputBits+1)
noncomputable def innerWorkPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  let Q := BinaryFirstInverseProgram.colorsPolynomial
  Q*(termWorkPolynomial precision inputBits+primitiveWorkPolynomial ((Q+1)*(termHeightPolynomial precision inputBits+1))+2)+2
noncomputable def heightPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFirstInverseProgram.colorsPolynomial*(innerHeightPolynomial precision inputBits+1)
noncomputable def workPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  let Q := BinaryFirstInverseProgram.colorsPolynomial
  PublicParameterProgram.workPolynomial+Q*(innerWorkPolynomial precision inputBits+
    primitiveWorkPolynomial ((Q+1)*(innerHeightPolynomial precision inputBits+1))+2)+4



end
end CurrentAFT.BinaryPositiveReference

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryPositiveReference.heightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryPositiveReference.innerHeightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryPositiveReference.innerWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryPositiveReference.termHeightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryPositiveReference.termWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryPositiveReference.workPolynomial
  pure ()

end

section
























/-! # Charged palette normalization and lookup of a generated profile -/
namespace CurrentAFT.BinaryProfileLookup
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryRootProfile.key BinaryPaletteLookup.current

abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

def zeroRoot : IntegerBits := ⟨false,[]⟩

def current (security : ℕ) (profile : Fin (colors security) → RationalResult) (output : ℕ) : RationalResult :=
  let code := canonicalCounter output
  let modulus := PublicParameterProgram.modulus security
  let table := buildArray modulus.count profile
  let key := BinaryRootProfile.key security zeroRoot code.digits
  let result := BinaryPaletteLookup.current table.data key.digits
  ⟨result.data,code.work+modulus.work+table.work+key.work+result.work+5⟩





noncomputable section
def heightPolynomial (profileBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFirstInverseProgram.colorsPolynomial*(profileBits+1)
def lookupWorkPolynomial (profileBits : Polynomial ℕ) : Polynomial ℕ :=
  let Q := BinaryFirstInverseProgram.colorsPolynomial
  let K := BinaryRootProfile.keyBitsPolynomial 0 Q
  Q*(50*(Q+1)^2+48*(Q+K)+42+3*Q+3+primitiveWorkPolynomial ((Q+1)*(profileBits+1))+2)+2
def workPolynomial (profileBits profileWork : Polynomial ℕ) : Polynomial ℕ :=
  50*(BinaryFirstInverseProgram.colorsPolynomial+1)^2+PublicParameterProgram.workPolynomial+
    BinaryFirstInverseProgram.colorsPolynomial*(profileWork+2)+2+
    BinaryRootProfile.keyWorkPolynomial 0 BinaryFirstInverseProgram.colorsPolynomial+
    lookupWorkPolynomial profileBits+5



end
end CurrentAFT.BinaryProfileLookup

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryProfileLookup.workPolynomial
  pure ()

end

section
























/-! Explicit touched-edge buffers for selected cycle roots. The candidates
are the selected edge and its cyclic predecessor. Duplicate removal compares
native stored vertex counters; no finite-choice enumeration is executed. -/
namespace CurrentAFT.BinaryTouchedCycle
open AFT BinaryArithmetic RationalRejectionProgram
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false


def previous (body : ℕ) (hb : 0 < body) (point : Fin body) : CountedValue (Fin body) :=
  let last := subtractCounter body 1
  let before := subtractCounter point.val 1
  let first := equalCounter point.val 0
  if h : first.value = true then
    ⟨⟨last.count,by rw [subtractCounter_value]; omega⟩,last.work+before.work+first.work+3⟩
  else
    ⟨⟨before.count,by rw [subtractCounter_value]; exact (Nat.sub_le _ _).trans_lt point.isLt⟩,
      last.work+before.work+first.work+3⟩

 theorem previous_value (body : ℕ) (hb : 0 < body) (point : Fin body) :
    (previous body hb point).value = (finRotate body).symm point := by
  letI : NeZero body := ⟨hb.ne'⟩
  by_cases hp : point.val = 0
  · have he := (equalCounter_value point.val 0).mpr hp
    obtain ⟨count,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb.ne'
    have hz : point = (0 : Fin (count+1)) := Fin.ext hp
    subst point
    rw [show (finRotate (count+1)).symm 0 = Fin.last count from
      (finRotate (count+1)).symm_apply_eq.mpr (finRotate_last).symm]
    apply Fin.ext
    simp only [previous,dif_pos he,Fin.val_mk,subtractCounter_value,Fin.val_last]
    omega
  · have he : ¬(equalCounter point.val 0).value = true := fun h => hp ((equalCounter_value _ _).mp h)
    apply Fin.ext
    rw [coe_finRotate_symm_of_ne_zero (fun h => hp (congrArg Fin.val h))]
    simp only [previous,dif_neg he,Fin.val_mk,subtractCounter_value]

 


def contains {body : ℕ} (point : Fin body) : List (Fin body) → CountedValue Bool
  | [] => ⟨false,1⟩
  | head::tail =>
    let hit := equalCounter head.val point.val
    let rest := contains point tail
    ⟨hit.value || rest.value,hit.work+rest.work+2⟩

 theorem contains_value {body : ℕ} (point : Fin body) (items : List (Fin body)) :
    (contains point items).value = true ↔ point ∈ items := by
  induction items with
  | nil => simp only [contains,List.not_mem_nil,Bool.false_eq_true]
  | cons head tail ih =>
    simp only [contains,Bool.or_eq_true,equalCounter_value,ih,List.mem_cons,Fin.ext_iff]
    exact or_congr eq_comm Iff.rfl

 


def unique {body : ℕ} : List (Fin body) → CountedValue (List (Fin body))
  | [] => ⟨[],1⟩
  | head::tail =>
    let rest := unique tail
    let hit := contains head rest.value
    ⟨if hit.value then rest.value else head::rest.value,rest.work+hit.work+2⟩

 theorem unique_mem {body : ℕ} (items : List (Fin body)) (point : Fin body) :
    point ∈ (unique items).value ↔ point ∈ items := by
  induction items generalizing point with
  | nil => rfl
  | cons head tail ih =>
    change point ∈ (if (contains head (unique tail).value).value then (unique tail).value else head::(unique tail).value) ↔ _
    by_cases h : (contains head (unique tail).value).value = true
    · rw [if_pos h]
      have hh : head ∈ tail := (ih head).mp ((contains_value head _).mp h)
      rw [ih, List.mem_cons]
      constructor
      · exact Or.inr
      · rintro (rfl | hp); exact hh; exact hp
    · rw [if_neg h,List.mem_cons,List.mem_cons,ih]

 theorem unique_nodup {body : ℕ} (items : List (Fin body)) : (unique items).value.Nodup := by
  induction items with
  | nil => exact List.nodup_nil
  | cons head tail ih =>
    change (if (contains head (unique tail).value).value then (unique tail).value else head::(unique tail).value).Nodup
    by_cases h : (contains head (unique tail).value).value = true
    · rw [if_pos h]; exact ih
    · rw [if_neg h,List.nodup_cons]
      exact ⟨fun hh => h ((contains_value head _).mpr hh),ih⟩

 

 


def candidates {body count : ℕ} (hb : 0 < body) (sites : Vector (Fin body) count) : CountedValue (List (Fin body)) :=
  let pairs := storeData count (fun slot =>
    let selected := readVector ⟨0,hb⟩ sites slot
    let predecessor := previous body hb selected.value
    ⟨(selected.value,predecessor.value),selected.work+predecessor.work+2⟩)
  ⟨pairs.value.toList.flatMap (fun pair => [pair.1,pair.2]),pairs.work+3*count+1⟩

 theorem candidates_value {body count : ℕ} (hb : 0 < body) (sites : Vector (Fin body) count) :
    (candidates hb sites).value = (List.finRange count).flatMap (fun slot => [sites.get slot,(finRotate body).symm (sites.get slot)]) := by
  simp only [candidates]
  rw [show (storeData count (fun slot =>
    let selected := readVector (⟨0,hb⟩ : Fin body) sites slot
    let predecessor := previous body hb selected.value
    (⟨(selected.value,predecessor.value),selected.work+predecessor.work+2⟩ : CountedValue (Fin body × Fin body)))).value =
      Vector.ofFn (fun slot => (sites.get slot,(finRotate body).symm (sites.get slot))) by
        apply Vector.ext
        intro index hi
        change (storeData _ _).value.get ⟨index,hi⟩ = _
        simp only [storeData_get,readVector_value,previous_value,Vector.getElem_ofFn]]
  rw [Vector.toList_ofFn,List.ofFn_eq_map,List.flatMap_map]

 

 theorem candidates_mem {body count : ℕ} (hb : 0 < body) (sites : Vector (Fin body) count) (point : Fin body) :
    point ∈ (candidates hb sites).value ↔ point ∈ CyclePatternProgram.touched sites.get := by
  rw [candidates_value]
  simp only [List.mem_flatMap,List.mem_finRange,true_and,List.mem_cons,List.not_mem_nil,or_false,
    CyclePatternProgram.touched,Finset.mem_union,Finset.mem_image,Finset.mem_univ]
  aesop


def prepare {body count : ℕ} (hb : 0 < body) (sites : Vector (Fin body) count) : CountedValue (List (Fin body)) :=
  let raw := candidates hb sites
  let result := unique raw.value
  ⟨result.value,raw.work+result.work+2⟩

 theorem prepare_nodup {body count : ℕ} (hb : 0 < body) (sites : Vector (Fin body) count) : (prepare hb sites).value.Nodup := unique_nodup _

 theorem prepare_mem {body count : ℕ} (hb : 0 < body) (sites : Vector (Fin body) count) (point : Fin body) :
    point ∈ (prepare hb sites).value ↔ point ∈ CyclePatternProgram.touched sites.get :=
  (unique_mem _ _).trans (candidates_mem hb sites point)

 

end CurrentAFT.BinaryTouchedCycle

end

section


















/-! Materialized touched-edge vectors and executed rank queries. The finite
bijection is used only to verify the Gaussian sum, never as a runtime lookup. -/
namespace CurrentAFT.BinaryTouchedCycleBuffer
open AFT BinaryArithmetic RationalRejectionProgram BinaryTouchedCycle
set_option maxHeartbeats 1400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

 

 


def buffer {body count : ℕ} (hb : 0 < body) (sites : Vector (Fin body) count) :
    CountedValue (Vector (Fin body) (prepare hb sites).value.length) :=
  let prepared := prepare hb sites
  let array := storeData prepared.value.length (fun index =>
    let selected := readList prepared.value index.val
    ⟨selected.data.getD ⟨0,hb⟩,selected.work+2⟩)
  ⟨array.value,prepared.work+array.work+2⟩

 theorem buffer_get {body count : ℕ} (hb : 0 < body) (sites : Vector (Fin body) count)
    (index : Fin (prepare hb sites).value.length) :
    (buffer hb sites).value.get index = (prepare hb sites).value.get index := by
  simp only [buffer,storeData_get,readList_value]
  rw [List.getElem?_eq_getElem index.isLt]
  rfl

 theorem buffer_injective {body count : ℕ} (hb : 0 < body) (sites : Vector (Fin body) count) :
    Function.Injective (buffer hb sites).value.get := by
  intro first second he
  rw [buffer_get,buffer_get] at he
  exact (prepare_nodup hb sites).get_inj_iff.mp he

 theorem vector_mem_get {Value : Type*} {size : ℕ} (values : Vector Value size) (point : Value) :
    point ∈ values.toList ↔ ∃ index : Fin size, values.get index = point := by
  rw [Vector.mem_toList_iff,Vector.mem_iff_getElem]
  exact ⟨fun ⟨index,hi,he⟩ => ⟨⟨index,hi⟩,he⟩, fun ⟨index,he⟩ => ⟨index.val,index.isLt,he⟩⟩

 theorem buffer_mem {body count : ℕ} (hb : 0 < body) (sites : Vector (Fin body) count) (point : Fin body) :
    point ∈ (buffer hb sites).value.toList ↔ point ∈ CyclePatternProgram.touched sites.get := by
  rw [vector_mem_get]
  constructor
  · rintro ⟨index,he⟩
    apply (prepare_mem hb sites point).mp
    rw [← he,buffer_get]
    exact List.get_mem (prepare hb sites).value index
  · intro hp
    obtain ⟨index,he⟩ := List.mem_iff_get.mp ((prepare_mem hb sites point).mpr hp)
    exact ⟨index,by rw [buffer_get]; exact he⟩


def rank {body size : ℕ} (values : Vector (Fin body) size) (target : Fin body) :
    (length : ℕ) → length ≤ size → CountedValue (Option (Fin size))
  | 0, _ => ⟨none,1⟩
  | length+1, h =>
    let old := rank values target length (by omega)
    let index : Fin size := ⟨length,by omega⟩
    let vertex := readVector target values index
    let hit := equalCounter vertex.value.val target.val
    ⟨if hit.value then some index else old.value,old.work+vertex.work+hit.work+3⟩

 theorem rank_value {body size : ℕ} (values : Vector (Fin body) size) (hinj : Function.Injective values.get)
    (target : Fin body) (index : Fin size) (hindex : values.get index = target)
    (length : ℕ) (hlength : length ≤ size) (hvisited : index.val < length) :
    (rank values target length hlength).value = some index := by
  induction length with
  | zero => omega
  | succ length ih =>
    let last : Fin size := ⟨length,by omega⟩
    have hh : (equalCounter (readVector target values last).value.val target.val).value = true ↔ values.get last = target := by
      rw [equalCounter_value,readVector_value,Fin.ext_iff]
    change (if (equalCounter (readVector target values last).value.val target.val).value then some last else
      (rank values target length _).value) = _
    by_cases he : values.get last = target
    · rw [if_pos (hh.mpr he)]
      exact congrArg some (hinj (he.trans hindex.symm))
    · rw [if_neg (fun h => he (hh.mp h))]
      apply ih (by omega)
      have hn : index.val ≠ length := by
        intro h
        have hi : index = last := Fin.ext h
        exact he (hi ▸ hindex)
      omega

 


def lookup {body size : ℕ} (values : Vector (Fin body) size) (hinj : Function.Injective values.get)
    (target : Fin body) (hmem : target ∈ values.toList) : CountedValue (Fin size) :=
  let found := rank values target size le_rfl
  have hs : found.value.isSome := by
    obtain ⟨index,he⟩ := (vector_mem_get values target).mp hmem
    have hg : values.get index = target := he
    have hr := rank_value values hinj target index hg size le_rfl index.isLt
    rw [show found.value = some index from hr]
    trivial
  ⟨found.value.get hs,found.work+2⟩

 

 

noncomputable section

def edgeEquiv {body count : ℕ} (hb : 0 < body) (sites : Vector (Fin body) count) :
    Fin (prepare hb sites).value.length ≃ CyclePatternProgram.touched sites.get :=
  Equiv.ofBijective (fun index => ⟨(buffer hb sites).value.get index,
    (buffer_mem hb sites _).mp ((vector_mem_get (buffer hb sites).value _).mpr ⟨index,rfl⟩)⟩) (by
      constructor
      · intro first second he
        exact buffer_injective hb sites (congrArg Subtype.val he)
      · intro vertex
        obtain ⟨index,he⟩ := (vector_mem_get (buffer hb sites).value vertex.val).mp ((buffer_mem hb sites vertex.val).mpr vertex.property)
        exact ⟨index,Subtype.ext he⟩)

end
end CurrentAFT.BinaryTouchedCycleBuffer

end

section


















/-! The current/predecessor rank pair is materialized for every selected root
using the executed touched-edge lookup, before any Gaussian word is visited. -/
namespace CurrentAFT.BinaryTouchedCycleRanks
open AFT BinaryArithmetic RationalRejectionProgram BinaryTouchedCycle BinaryTouchedCycleBuffer
set_option maxHeartbeats 1400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false


def prepareWork (body count : ℕ) : ℕ :=
  count*(3*count+7*body+19)+3 + (2*count)*(2*count*(6*body+4)+3)+3

def bufferWork (body count : ℕ) : ℕ := prepareWork body count + (2*count)*(4*count+5)+4

 


def positions {body count : ℕ} (hb : 0 < body) (sites : Vector (Fin body) count) :
    CountedValue (Vector (Fin (prepare hb sites).value.length × Fin (prepare hb sites).value.length) count) :=
  let vertices := buffer hb sites
  let result := storeData count (fun slot =>
    let point := readVector ⟨0,hb⟩ sites slot
    let before := previous body hb point.value
    have hp : point.value ∈ vertices.value.toList := by
      rw [buffer_mem,readVector_value]
      exact (CyclePatternProgram.currentEdge sites.get slot).property
    have hb' : before.value ∈ vertices.value.toList := by
      rw [buffer_mem,previous_value,readVector_value]
      exact (CyclePatternProgram.previousEdge sites.get slot).property
    let first := lookup vertices.value (buffer_injective hb sites) point.value hp
    let second := lookup vertices.value (buffer_injective hb sites) before.value hb'
    ⟨(first.value,second.value),point.work+before.work+first.work+second.work+5⟩)
  ⟨result.value,vertices.work+result.work+2⟩

 


def positionsWork (body count : ℕ) : ℕ :=
  bufferWork body count + count*(3*count+7*body+2*((2*count)*(6*count+6*body+8)+3)+20)+4

 

end CurrentAFT.BinaryTouchedCycleRanks

end

section




















/-!
# Finite rational iteration for the actual chart response

The matrix is minus the literal deletion operator, so the stored iteration
`rhs - matrix * previous` is the Neumann recurrence.  Its limit is the
canonical rational ideal used by `currentLaw`, rather than a separately
chosen positive table.  Matrix-entry construction and bit costs are kept
separate from the convergence proof.
-/

namespace CurrentAFT.CurrentFlagIteration

open AFT AFT.BoundaryCalibration AFT.RationalNumerics
open AffineFlagCalibration CurrentRationalFlagLaw
open scoped BigOperators Classical

noncomputable section
set_option maxHeartbeats 1200000

variable {Ω C I : Type*} [Fintype Ω] [Fintype C] [Fintype I] [DecidableEq Ω]

def iterationMatrix (features : I → Ω → C) (allowed : I → Finset C) (safe : Ω → Prop) :
    Matrix Ω Ω ℚ :=
  LinearMap.toMatrix' (responseQ features allowed safe - LinearMap.id)

def iterate (features : I → Ω → C) (allowed : I → Finset C) (safe : Ω → Prop)
    (target : Ω → ℚ) (steps : ℕ) : Ω → ℚ :=
  linearIteration (iterationMatrix features allowed safe) target steps









def regularIterate (features : I → Ω → C) (allowed : I → Finset C)
    (line : I → Prop) (safe : Ω → Prop) (atom : ℚ) (spike : Ω → ℚ) (steps : ℕ) : Ω → ℚ :=
  fun x => if safe x then iterate features allowed safe
    (1 - (atom / (1 - atom)) • offLineDefectQ features allowed line spike) steps x else 0



section ActualParameters

variable {F J : Type*} [Field F] [Fintype F] [Fintype J]



local instance iterationPrime (security : ℕ) : Fact (Parameters.modulus security).Prime :=
  ⟨(Parameters.modulus_spec security).2⟩



end ActualParameters

end
end CurrentAFT.CurrentFlagIteration

end

section


















/-!
# Executable finite arrays for the simultaneous flag repair

Every protected input on the zero-first-coordinate line is excluded from
the defect.  This differs from a repair with a single distinguished input.
The definitions use finite sums, rational arithmetic, and explicit Boolean
masks.  Their semantics are the canonical rational response of this branch.
-/

namespace CurrentAFT.CurrentFlagArray

open AFT AFT.BoundaryCalibration CurrentRationalFlagLaw CurrentFlagIteration
open scoped BigOperators

variable {C I : Type*} [Fintype C] [Fintype I] [DecidableEq C]

def mean (charts : ℕ) (profile : Fin charts → ℚ) : ℚ := (∑ point, profile point) / charts

def conditional (charts : ℕ) (feature : Fin charts → C) (profile : Fin charts → ℚ) (color : C) : ℚ :=
  (Fintype.card C : ℚ) * mean charts (fun point => if feature point = color then profile point else 0)

def component (charts : ℕ) (feature : Fin charts → C) (allowed : Finset C)
    (profile : Fin charts → ℚ) (point : Fin charts) : ℚ :=
  if feature point ∈ allowed then conditional charts feature profile (feature point) -
    (∑ color ∈ allowed, conditional charts feature profile color) / allowed.card else 0

def projection (charts : ℕ) (features : I → Fin charts → C) (allowed : I → Finset C)
    (profile : Fin charts → ℚ) (point : Fin charts) : ℚ :=
  mean charts profile + ∑ index, component charts (features index) (allowed index) profile point

def deletion (charts : ℕ) (features : I → Fin charts → C) (allowed : I → Finset C)
    (safe : Fin charts → Bool) (profile : Fin charts → ℚ) (point : Fin charts) : ℚ :=
  projection charts features allowed (fun input => if safe input then 0 else profile input) point

def defect (charts : ℕ) (features : I → Fin charts → C) (allowed : I → Finset C)
    (line : I → Bool) (spike : Fin charts → ℚ) (point : Fin charts) : ℚ :=
  ∑ index, if line index then 0 else component charts (features index) (allowed index) spike point

def target (charts : ℕ) (features : I → Fin charts → C) (allowed : I → Finset C)
    (line : I → Bool) (atom : ℚ) (spike : Fin charts → ℚ) (point : Fin charts) : ℚ :=
  1 - atom / (1 - atom) * defect charts features allowed line spike point

def iterate (charts : ℕ) (features : I → Fin charts → C) (allowed : I → Finset C)
    (safe : Fin charts → Bool) (rhs : Fin charts → ℚ) : ℕ → Vector ℚ charts
  | 0 => Vector.replicate charts 0
  | steps + 1 =>
    let previous := iterate charts features allowed safe rhs steps
    Vector.ofFn (fun point => rhs point + deletion charts features allowed safe previous.get point)

def regular (charts : ℕ) (features : I → Fin charts → C) (allowed : I → Finset C)
    (line : I → Bool) (safe : Fin charts → Bool) (atom : ℚ) (spike : Fin charts → ℚ)
    (steps : ℕ) : Vector ℚ charts :=
  let raw := iterate charts features allowed safe (target charts features allowed line atom spike) steps
  Vector.ofFn (fun point => if safe point then raw.get point else 0)

noncomputable section
open scoped Classical
set_option maxHeartbeats 1200000



















end
end CurrentAFT.CurrentFlagArray

end

end


