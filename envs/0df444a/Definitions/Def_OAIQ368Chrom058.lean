-- Prove2me | Definitions.Def_OAIQ368Chrom058
-- name    : OAIQ368Chrom058
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T18:34:10.811332+00:00
-- url     : https://prove2.me/theorems/518572d8-7822-40d8-9206-6b321a0bd910
-- title:
--   Definitions bundle OAIQ368Chrom058 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 193 declarations of OpenAI's Lean: 120 definitions, 4 inductive types or structures, 1 instance and 68 theorems. The definitions and types are `OAI.ElementaryPositivity.ElementaryMatrix.colCount`, `OAI.ElementaryPositivity.ElementaryMatrix.rowCount`, `OAI.ElementaryPositivity.ElementaryMatrix.transpose`, `OAI.ElementaryPositivity.ElementaryMatrix.transposeEquiv`, `OAI.ElementaryPositivity.LatticeExtension.Extended`, `OAI.ElementaryPositivity.LatticeExtension.dot`, `OAI.ElementaryPositivity.LatticeExtension.form`, `OAI.ElementaryPositivity.LatticeExtension.includeVertices`, `OAI.ElementaryPositivity.LatticeRealization.extendedCast`, `OAI.ElementaryPositivity.LatticeRealization.extendedRealForm`, `OAI.ElementaryPositivity.LatticeRealization.realDot`, `OAI.ElementaryPositivity.LatticeRealization.realPairing`, `OAI.ElementaryPositivity.NaturalUnitIntervalGraph.coloringInversions`, `OAI.ElementaryPositivity.NaturalUnitIntervalGraph.edgeCount`, `OAI.ElementaryPositivity.NaturalUnitIntervalGraph.edges`, `OAI.ElementaryPositivity.NaturalUnitIntervalGraph.extendedH`, `OAI.ElementaryPositivity.NaturalUnitIntervalGraph.invertedEdges`, `OAI.ElementaryPositivity.NaturalUnitIntervalGraph.reversePerm`, `OAI.ElementaryPositivity.OrbitMonomial.exponentOrbit`, `OAI.ElementaryPositivity.OrbitMonomial.polynomial`, `OAI.ElementaryPositivity.PhaseLabel`, `OAI.ElementaryPositivity.QuantumTorus.BlockValid`, `OAI.ElementaryPositivity.QuantumTorus.ElementaryExpr.integer`, `OAI.ElementaryPositivity.QuantumTorus.ElementaryExpr.natural`, `OAI.ElementaryPositivity.QuantumTorus.ElementaryExpr.nscale`, `OAI.ElementaryPositivity.QuantumTorus.ElementaryExpr.ordinary`, `OAI.ElementaryPositivity.QuantumTorus.ElementaryExpr.sequence`, `OAI.ElementaryPositivity.QuantumTorus.ElementaryExpr.zscale`, `OAI.ElementaryPositivity.QuantumTorus.LocalHistoryFormula`, `OAI.ElementaryPositivity.QuantumTorus.LocalHistoryFormula.Bounded`, `OAI.ElementaryPositivity.QuantumTorus.LocalHistoryFormula.Leaf`, `OAI.ElementaryPositivity.QuantumTorus.LocalHistoryFormula.Positive`, `OAI.ElementaryPositivity.QuantumTorus.LocalHistoryFormula.eval`, `OAI.ElementaryPositivity.QuantumTorus.LocalHistoryFormula.finSum`, `OAI.ElementaryPositivity.QuantumTorus.LocalHistoryFormula.leafDegree`, `OAI.ElementaryPositivity.QuantumTorus.LocalHistoryFormula.leafExponent`, `OAI.ElementaryPositivity.QuantumTorus.LocalHistoryFormula.leafWeight`, `OAI.ElementaryPositivity.QuantumTorus.LocalHistoryFormula.sumList`, `OAI.ElementaryPositivity.QuantumTorus.blockLabels`, `OAI.ElementaryPositivity.QuantumTorus.commonHistoryLeavesRing` and 84 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `Chromatic_GradedAlgebra_HomogenizedPolynomialSection`, `Chromatic_GradedAlgebra_RootCoefficientLocality`, `Chromatic_GradedAlgebra_RootSectionHalfspace`, `Chromatic_GradedAlgebra_SquarefreeCoefficient`, `Chromatic_Histories_CommonHistoryLeaves`, `Chromatic_Histories_GraphCommonHistory`, `Chromatic_Histories_LocalHistoryFormula`, `Chromatic_Histories_TriangularCommonHistory`, `Chromatic_QuantumTorus_Admissible`, `Chromatic_QuantumTorus_ConeSectionDomination`, `Chromatic_QuantumTorus_ExpressionAdditiveOperations`, `Chromatic_QuantumTorus_GraphRationalModel`, `Chromatic_QuantumTorus_GraphSquarefreeKernel`, `Chromatic_QuantumTorus_OrbitMonomialSymmetric`, `Chromatic_QuantumTorus_OrderedIndependentProduct`, `Chromatic_QuantumTorus_OrdinaryElementaryExpressions`, `Chromatic_QuantumTorus_PolynomialThetaIdentification`, `Chromatic_Walls_ElementaryMatrixDuality`, `Chromatic_Walls_ForwardChartMutation`, `Chromatic_Walls_GraphTriangularEmbedding`, `Chromatic_Walls_IncomingExtremalLocality`, `Chromatic_Walls_LaurentPositiveDomination`, `Chromatic_Walls_PathRoot`, `Chromatic_Walls_RealLatticeRealization`, `Chromatic_Walls_SquarefreeBlocks`, `Chromatic_Walls_TriangularAnchorProjection`, `Chromatic_Walls_TriangularAnchored`, `Chromatic_Walls_TriangularCommutativity`, `Chromatic_Walls_TriangularGapPairing`, `Chromatic_Walls_TriangularGapTotals`, `Chromatic_Walls_TriangularGaps`, `Chromatic_Walls_TriangularLevelQueues`, `Chromatic_Walls_TriangularLinearSection`, `Chromatic_Walls_TriangularMonomialCriterion`, `Chromatic_Walls_TriangularPolynomialStationarity`, `Chromatic_Walls_TriangularPositivePowers`.
--
--   **Imports.** It imports the published bundle `Def_ElementaryPositivity`; the bundles `OAIQ368Chrom015`, `OAIQ368Chrom016`, `OAIQ368Chrom026` and `OAIQ368Chrom057` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ368Chrom059`, `OAIQ368Chrom061`, `OAIQ368Chrom063`, `OAIQ368Chrom064` and `OAIQ368Chrom066`; the statements `OAI.ElementaryPositivity.QuantumTorus.polynomial_common_history`, `OAI.ElementaryPositivity.TriangularDynamics.graph_common_history`, `OAI.ElementaryPositivity.TriangularDynamics.monomial_producer_supported`, `OAI.ElementaryPositivity.TriangularDynamics.triangularIncoming_anchorCoeff`, `OAI.ElementaryPositivity.TriangularDynamics.triangularLinear_anchorIncoming`, `OAI.ElementaryPositivity.TriangularDynamics.triangularLinear_locality`, `OAI.ElementaryPositivity.TriangularDynamics.triangularMonomial_initial`, `OAI.ElementaryPositivity.TriangularDynamics.triangularPower_incoming_retain`, `OAI.ElementaryPositivity.TriangularDynamics.triangularPower_positive`, `OAI.ElementaryPositivity.TriangularDynamics.triangularPureIncoming_delta` and `OAI.ElementaryPositivity.TriangularDynamics.triangularPure_equal`; the proofs of `OAI.ElementaryPositivity.QuantumTorus.polynomial_common_history`, `OAI.ElementaryPositivity.TriangularDynamics.graph_common_history`, `OAI.ElementaryPositivity.TriangularDynamics.monomial_producer_supported`, `OAI.ElementaryPositivity.TriangularDynamics.triangularIncoming_anchorCoeff`, `OAI.ElementaryPositivity.TriangularDynamics.triangularLinear_anchorIncoming`, `OAI.ElementaryPositivity.TriangularDynamics.triangularLinear_locality`, `OAI.ElementaryPositivity.TriangularDynamics.triangularMonomial_initial`, `OAI.ElementaryPositivity.TriangularDynamics.triangularPower_incoming_retain`, `OAI.ElementaryPositivity.TriangularDynamics.triangularPower_positive` and `OAI.ElementaryPositivity.TriangularDynamics.triangularPureIncoming_delta`.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_ElementaryPositivity
import Definitions.Def_OAIQ368Chrom015
import Definitions.Def_OAIQ368Chrom016
import Definitions.Def_OAIQ368Chrom026
import Definitions.Def_OAIQ368Chrom057

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_HomogenizedPolynomialSection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries HahnSeries PowerSeriesAdjoint WallUnits
open Classical
noncomputable section
variable {M I:Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (C:(I → ℤ) →+ M) (coord:M →+ (I → ℤ)) (hcoord:∀d,coord (C d)=d)
local instance homogenizedPolynomialSectionRing : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
local instance homogenizedPolynomialSectionAddCommMonoid_r5b98ce_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance homogenizedPolynomialSectionAddGroup_r5b98ce_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
local instance homogenizedPolynomialSectionNonUnitalSemiring_r5b98ce_1 : NonUnitalSemiring (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalSemiring
local instance homogenizedPolynomialSectionNonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalNonAssocSemiring

def polynomialInitial (F:Torus LaurentRay.vUnit Ω) : PowerSeries (Torus LaurentRay.vUnit Ω) :=
  adjoint (invOfUnit (simpleTotalTransport Ω C).val 1) (homogenize LaurentRay.vUnit Ω (rootOrder coord) F)

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_RootSectionHalfspace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint WallUnits
open Classical
noncomputable section
variable {M I:Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (C:(I → ℤ) →+ M)
local instance rootSectionHalfspaceRing : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint
open scoped BigOperators
open Classical
noncomputable section
variable {K M:Type*} [Field K] [AddCommGroup M]
variable (v:Kˣ) (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
local instance targetCyclicRing : Ring (Torus v Ω) := Torus.instRing v Ω
local instance targetCyclicAddCommMonoid : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_RootCoefficientLocality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint WallUnits
open scoped BigOperators
open Classical
noncomputable section
variable {M I:Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (C:(I → ℤ) →+ M) (coord:M →+ (I → ℤ)) (hcoord:∀d,coord (C d)=d)
local instance rootCoefficientLocalityRing : Ring (Torus LaurentRay.vUnit Ω) :=
  Torus.instRing LaurentRay.vUnit Ω
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_OrderedIndependentProduct
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instAddCommGroup _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.RawShuffle.quotientCommRing _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open scoped BigOperators
open Classical
noncomputable section
variable {K M V:Type*} [Field K] [AddCommGroup M] [Fintype V] [DecidableEq V]
variable (v:Kˣ) (Ω:M →+ M →+ ℤ)
local instance orderedIndependentProductRing_r5b98ce_1 : Ring (Torus v Ω) := Torus.instRing v Ω
local instance orderedIndependentProductAddCommMonoid : AddCommMonoid (Torus v Ω) :=
  (Torus.instRing v Ω).toAddCommMonoid
local instance orderedIndependentProductAddGroup_r5b98ce_1 : AddGroup (Torus v Ω) :=
  (Torus.instRing v Ω).toAddGroup
local instance orderedIndependentProductNonUnitalSemiring_r5b98ce_1 : NonUnitalSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalSemiring
local instance orderedIndependentProductNonUnitalNonAssocSemiring :
    NonUnitalNonAssocSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalNonAssocSemiring
local instance orderedIndependentProductAddCommGroup_r5b98ce_1 : AddCommGroup (Torus v Ω) :=
  (Torus.instRing v Ω).toAddCommGroup
local instance orderedIndependentProductAddMonoid : AddMonoid (Torus v Ω) :=
  (Torus.instRing v Ω).toAddMonoid
local instance orderedIndependentProductSemiring : Semiring (Torus v Ω) :=
  (Torus.instRing v Ω).toSemiring
variable (u:V → M)

def wordExponent {r:ℕ} (a:Fin r → M) : M:=∑i,a i

def wordEnergy : {r:ℕ} → (Fin r → M) → ℤ
  | 0,_=>0
  | _+1,a=>Ω (a 0) (wordExponent (fun i=>a i.succ))+wordEnergy (fun i=>a i.succ)

def BlockValid {r:ℕ} (a:Fin r → ℕ) (s:Fin r → Finset V) : Prop :=
  ∀i,IsIndependent Ω u (s i) ∧ (s i).card=a i

def blockLabels {r:ℕ} (s:Fin r → Finset V) : Fin r → M:=fun i=>∑x∈s i,u x

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_SquarefreeBlocks
attribute [-instance] _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.degreesDecidableEq _root_.OAI.ElementaryPositivity.TriangularDynamics.cutContains_decidable _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
attribute [-simp] _root_.OAI.ElementaryPositivity.WallUnits.rescale_C
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.SquarefreeBlocks
open scoped BigOperators
open Classical
noncomputable section
variable {V:Type*} [DecidableEq V]
variable {n r:ℕ} (b:Fin n ↪ V)

def target : V → ℤ:=∑j:Fin n,Pi.single (b j) 1

def vector (s:Fin r → Finset V) : V → ℤ:=∑i:Fin r,∑x∈s i,Pi.single x 1

lemma target_apply (x:V) : target b x=if x∈Set.range b then 1 else 0 := by
  unfold target
  simp only [Finset.sum_apply,Pi.single_apply]
  by_cases h:x∈Set.range b
  · obtain ⟨j,rfl⟩:=h
    rw [ite_eq_left (Set.mem_range_self j)]
    rw [Finset.sum_eq_single j]
    · simp
    · intro k hk hkj
      rw [ite_eq_right (fun h=>hkj (b.injective h.symm))]
    · simp
  · rw [ite_eq_right h]
    apply Finset.sum_eq_zero
    intro j hj
    exact ite_eq_right (fun hj=>h ⟨j,hj.symm⟩)

lemma vector_apply (s:Fin r → Finset V) (x:V) :
    vector s x=((Finset.univ.filter (fun i=>x∈s i)).card:ℤ) := by
  unfold vector
  simp only [Finset.sum_apply,Pi.single_apply]
  simp only [Finset.sum_ite_eq,Finset.sum_boole]

lemma membership_unique (s:Fin r → Finset V) (hs:vector s=target b) (j:Fin n) :
    ∃!i:Fin r,b j∈s i := by
  have H:=congrFun hs (b j)
  rw [vector_apply,target_apply,ite_eq_left (Set.mem_range_self j)] at H
  have hc:(Finset.univ.filter (fun i=>b j∈s i)).card=1:=by exact_mod_cast H
  obtain ⟨i,hi⟩:=Finset.card_eq_one.mp hc
  refine ⟨i,?_,?_⟩
  · have h:i∈Finset.univ.filter (fun i=>b j∈s i):=by rw [hi]; simp
    exact (Finset.mem_filter.mp h).2
  · intro k hk
    have h:k∈Finset.univ.filter (fun i=>b j∈s i):=Finset.mem_filter.mpr ⟨Finset.mem_univ _,hk⟩
    rw [hi,Finset.mem_singleton] at h
    exact h

lemma membership_range (s:Fin r → Finset V) (hs:vector s=target b) (i:Fin r) (x:V) (hx:x∈s i) :
    x∈Set.range b := by
  by_contra hn
  have H:=congrFun hs x
  rw [vector_apply,target_apply,ite_eq_right hn] at H
  have hc:(Finset.univ.filter (fun i=>x∈s i)).card=0:=by exact_mod_cast H
  have hh:=Finset.card_eq_zero.mp hc
  have hm:i∈Finset.univ.filter (fun i=>x∈s i):=Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩
  rw [hh] at hm
  exact Finset.notMem_empty _ hm

def coloring (s:{s:Fin r → Finset V // vector s=target b}) : Fin n → Fin r:=
  fun j=>(membership_unique b s.val s.property j).choose
lemma coloring_mem (s:{s:Fin r → Finset V // vector s=target b}) (j:Fin n) :
    b j∈s.val (coloring b s j):=(membership_unique b s.val s.property j).choose_spec.1
lemma coloring_eq (s:{s:Fin r → Finset V // vector s=target b}) (j:Fin n) (i:Fin r) (h:b j∈s.val i) :
    coloring b s j=i:=((membership_unique b s.val s.property j).choose_spec.2 i h).symm

def blocks (κ:Fin n → Fin r) (i:Fin r) : Finset V:=
  (Finset.univ.filter (fun j=>κ j=i)).map b
omit [DecidableEq V] in
lemma mem_blocks (κ:Fin n → Fin r) (i:Fin r) (x:V) :
    x∈blocks b κ i ↔ ∃j,κ j=i ∧ b j=x := by simp [blocks]
lemma blocks_vector (κ:Fin n → Fin r) : vector (blocks b κ)=target b := by
  ext x
  simp only [vector,blocks,Finset.sum_apply,Finset.sum_map,Finset.sum_filter]
  rw [Finset.sum_comm]
  simp only [ite_apply,Pi.zero_apply]
  change (∑j:Fin n,∑i:Fin r,if κ j=i then (Pi.single (b j) (1:ℤ) : V → ℤ) x else 0)=_
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true, if_true]
  simp only [target,Finset.sum_apply]

def equiv : {s:Fin r → Finset V // vector s=target b} ≃ (Fin n → Fin r) where
  toFun:=coloring b
  invFun κ:=⟨blocks b κ,blocks_vector b κ⟩
  left_inv s:=by
    apply Subtype.ext
    funext i
    apply Finset.ext
    intro x
    rw [mem_blocks]
    constructor
    · rintro ⟨j,hj,rfl⟩
      rw [←hj]
      exact coloring_mem b s j
    · intro hx
      obtain ⟨j,rfl⟩:=membership_range b s.val s.property i x hx
      exact ⟨j,coloring_eq b s j i hx,rfl⟩
  right_inv κ:=by
    funext j
    apply coloring_eq
    exact (mem_blocks b κ (κ j) (b j)).mpr ⟨j,rfl,rfl⟩
end
end ElementaryPositivity.SquarefreeBlocks

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_SquarefreeCoefficient
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.quotientCommRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity
open scoped BigOperators
open Classical
noncomputable section

namespace QuantumTorus
variable {K M V:Type*} [Field K] [AddCommGroup M] [Fintype V] [DecidableEq V]
variable (v:Kˣ) (Ω:M →+ M →+ ℤ)
local instance squarefreeCoefficientRing_r5b98ce_1 : Ring (Torus v Ω) := Torus.instRing v Ω
local instance squarefreeCoefficientAddCommMonoid : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
end QuantumTorus
end
end ElementaryPositivity

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Histories_LocalHistoryFormula
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint PowerSeriesSplit LaurentPositive WallUnits
open scoped BigOperators
open Classical
noncomputable section
variable {M E I:Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]

inductive LocalHistoryFormula (M E:Type*) [AddCommGroup E] [Module ℝ E] where
  | zero
  | stop (degree:ℕ) (exponent:M)
  | add (left right:LocalHistoryFormula M E)
  | jump (degree:ℕ) (source target:M) (transfer:LineTransfer E) (tail:LocalHistoryFormula M E)

namespace LocalHistoryFormula
variable (Ω:M →+ M →+ ℤ) (C:(I → ℤ) →+ M) (e:M →+ E)
variable (F:CompletedPositive LaurentRay.vUnit Ω C)
def eval (A:ℕ → M → LaurentSeries ℚ) : LocalHistoryFormula M E → LaurentSeries ℚ
  | .zero=>0
  | .stop j m=>A j m
  | .add p q=>eval A p+eval A q
  | .jump d m r t p=>monomialJump Ω (t.operator Ω C e F) d m r*eval A p

def Positive : LocalHistoryFormula M E → Prop
  | .zero=>True
  | .stop _ _=>True
  | .add p q=>Positive p ∧ Positive q
  | .jump d m r t p=>LaurentPositive.Positive (monomialJump Ω (t.operator Ω C e F) d m r) ∧ Positive p

def Bounded (b:M) (N:ℕ) : LocalHistoryFormula M E → Prop
  | .zero=>True
  | .stop j m=>j≤N ∧ HasRootDegree C j (m-b)
  | .add p q=>Bounded b N p ∧ Bounded b N q
  | .jump d _ _ _ p=>0<d ∧ ∃j,j+d≤N ∧ Bounded b j p

def sumList : List (LocalHistoryFormula M E) → LocalHistoryFormula M E
  | []=>.zero
  | p::ps=>.add p (sumList ps)

end LocalHistoryFormula
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint PowerSeriesSplit LaurentPositive WallUnits
open scoped BigOperators
open Classical
noncomputable section
variable {M E I:Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]
namespace LocalHistoryFormula
variable (Ω:M →+ M →+ ℤ) (C:(I → ℤ) →+ M) (e:M →+ E)
variable (F:CompletedPositive LaurentRay.vUnit Ω C)
def finSum {J:Type*} (s:Finset J) (f:J → LocalHistoryFormula M E) : LocalHistoryFormula M E :=
  sumList (s.toList.map f)
end LocalHistoryFormula

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Histories_CommonHistoryLeaves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus.LocalHistoryFormula
open PowerSeries PowerSeriesAdjoint PowerSeriesSplit LaurentPositive WallUnits
open scoped BigOperators
open Classical
noncomputable section
variable {M E I:Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]

def Leaf : LocalHistoryFormula M E → Type
  | .zero=>Empty
  | .stop _ _=>Unit
  | .add p q=>Sum (Leaf p) (Leaf q)
  | .jump _ _ _ _ p=>Leaf p

instance leafFintype (p:LocalHistoryFormula M E) : Fintype p.Leaf := by
  induction p with
  | zero=>exact inferInstanceAs (Fintype Empty)
  | stop _ _=>exact inferInstanceAs (Fintype Unit)
  | add p q ihp ihq=>letI:=ihp; letI:=ihq; exact inferInstanceAs (Fintype (Sum p.Leaf q.Leaf))
  | jump _ _ _ _ p ih=>exact ih

def leafDegree : (p:LocalHistoryFormula M E) → p.Leaf → ℕ
  | .zero,l=>nomatch l
  | .stop j _,_=>j
  | .add p _,.inl l=>leafDegree p l
  | .add _ q,.inr l=>leafDegree q l
  | .jump _ _ _ _ p,l=>leafDegree p l

def leafExponent : (p:LocalHistoryFormula M E) → p.Leaf → M
  | .zero,l=>nomatch l
  | .stop _ m,_=>m
  | .add p _,.inl l=>leafExponent p l
  | .add _ q,.inr l=>leafExponent q l
  | .jump _ _ _ _ p,l=>leafExponent p l

variable (Ω:M →+ M →+ ℤ) (C:(I → ℤ) →+ M) (e:M →+ E)
variable (F:CompletedPositive LaurentRay.vUnit Ω C)
def leafWeight : (p:LocalHistoryFormula M E) → p.Leaf → LaurentSeries ℚ
  | .zero,l=>nomatch l
  | .stop _ _,_=>1
  | .add p _,.inl l=>leafWeight p l
  | .add _ q,.inr l=>leafWeight q l
  | .jump d m r t p,l=>monomialJump Ω (t.operator Ω C e F) d m r*leafWeight p l

end
end ElementaryPositivity.QuantumTorus.LocalHistoryFormula

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint WallUnits HahnSeries
open Classical
noncomputable section
variable {M E I:Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (C:(I → ℤ) →+ M) (coord:M →+ (I → ℤ)) (hcoord:∀d,coord (C d)=d)
local instance commonHistoryLeavesRing : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_OrbitMonomialSymmetric
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.degreesDecidableEq _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.OrbitMonomial
open scoped BigOperators
open Classical
noncomputable section
variable {σ:Type*} [Fintype σ] [DecidableEq σ] {R:Type*} [CommRing R]

def exponentOrbit (μ:σ →₀ ℕ) : Finset (σ →₀ ℕ) :=
  Finset.univ.image (fun e:Equiv.Perm σ=>μ.mapDomain e)

def polynomial (μ:σ →₀ ℕ) : MvPolynomial σ R :=
  ∑d∈exponentOrbit μ,MvPolynomial.monomial d 1

end
end ElementaryPositivity.OrbitMonomial

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_OrdinaryElementaryExpressions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open scoped BigOperators
open Classical
noncomputable section

variable {σ : Type*} [Fintype σ] {R : Type*} [CommRing R]

def ElementaryExpr.ordinary : {N:ℕ} → ElementaryExpr N → MvPolynomial σ R
  | _,.zero _ => 0
  | _,.one => 1
  | _,.atom k => MvPolynomial.esymm σ R k
  | _,.add f g => ordinary f+ordinary g
  | _,.neg f => -ordinary f
  | _,.mul f g => ordinary f*ordinary g

def ElementaryExpr.natural : ℕ → ElementaryExpr 0
  | 0=>.zero 0
  | k+1=>.add (natural k) .one

def ElementaryExpr.integer : ℤ → ElementaryExpr 0
  | .ofNat k => natural k
  | .negSucc k => .neg (natural (k+1))

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_PolynomialThetaIdentification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint WallUnits
open Classical
noncomputable section
variable {M I:Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (C:(I → ℤ) →+ M) (coord:M →+ (I → ℤ)) (hcoord:∀d,coord (C d)=d)
local instance instRingTorusLaurentSeriesRatVUnit_16 : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_IncomingExtremalLocality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint WallUnits
open Classical
noncomputable section
variable {M I:Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (C:(I → ℤ) →+ M) (coord:M →+ (I → ℤ))
local instance incomingExtremalLocalityTorusRing : Ring (Torus LaurentRay.vUnit Ω) :=
  Torus.instRing LaurentRay.vUnit Ω
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_PathRoot
attribute [-instance] _root_.OAI.ElementaryPositivity.TriangularDynamics.instAntisymmCellPhaseLE _root_.OAI.ElementaryPositivity.TriangularDynamics.instDecidableRelCellPhaseLE _root_.OAI.ElementaryPositivity.TriangularDynamics.instIsTransCellPhaseLE _root_.OAI.ElementaryPositivity.TriangularDynamics.instTotalCellPhaseLE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open scoped BigOperators
open Classical
noncomputable section
variable {n : ℕ}

variable {R : Type*} [CommRing R]

lemma forwardGap_independent : LinearIndependent R (forwardGap (R:=R) (n:=n)) := by
  have H:=Pi.linearIndependent_single_one (GapIndex n) R
  have HH:LinearIndependent R (fun g : GapIndex n=>forwardCoord (forwardGap (R:=R) g)) := by
    simpa only [forwardCoord_gap] using H
  exact HH.of_comp forwardCoord

end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TriangularGapPairing
attribute [-instance] _root_.OAI.ElementaryPositivity.TriangularDynamics.instAntisymmCellPhaseLE _root_.OAI.ElementaryPositivity.TriangularDynamics.instDecidableRelCellPhaseLE _root_.OAI.ElementaryPositivity.TriangularDynamics.instIsTransCellPhaseLE _root_.OAI.ElementaryPositivity.TriangularDynamics.instTotalCellPhaseLE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ}

def ownNodeWeight (a r j:ℕ) : ℤ :=
  if j=0 then 1 else if j=a+2 then -1 else
    if j+r < a+1 then 2 else if j+r=a+1 then 1 else 0
def lowerNodeWeight (a r j:ℕ) : ℤ :=
  if j=0 then 0 else if j=a+2 then 1 else if j+r ≤ a+1 then -1 else 0
def upperNodeWeight (a r j:ℕ) : ℤ :=
  if j=0 then -1 else if j=a+2 then 0 else if j+r < a+1 then -1 else 0

def eventNodeWeight (b:Cell n) (i:Fin n) (j:ℕ) : ℤ :=
  if i=b.1 then ownNodeWeight i.val b.2.val j
  else if i.val+1=b.1.val then lowerNodeWeight i.val b.2.val j
  else if b.1.val+1=i.val then upperNodeWeight i.val b.2.val j
  else 0

lemma eventRoot_levelNode (b:Cell n) (i:Fin n) (j:Fin (i.val+3)) :
    triangularOmega n (eventRoot cellLevel 0 b) (Pi.single (levelNode i j) 1)=eventNodeWeight b i j.val := by
  have hb := b.2.isLt
  have hj := j.isLt
  unfold levelNode
  split_ifs with h0 he
  · change triangularOmega n (eventRoot cellLevel 0 b) (anchor i.castSucc)=_
    rw [eventRoot_anchor]
    simp only [eventNodeWeight,ownNodeWeight,lowerNodeWeight,upperNodeWeight,h0,Fin.ext_iff,Fin.val_castSucc,Fin.val_succ]
    split_ifs <;> first | contradiction | omega
  · change triangularOmega n (eventRoot cellLevel 0 b) (anchor i.succ)=_
    rw [eventRoot_anchor]
    simp only [eventNodeWeight,ownNodeWeight,lowerNodeWeight,upperNodeWeight,he,Fin.ext_iff,Fin.val_castSucc,Fin.val_succ]
    split_ifs <;> first | contradiction | omega
  · change triangularOmega n (eventRoot cellLevel 0 b) (bridge ⟨i,⟨i.val+1-j.val,_⟩⟩)=_
    rw [eventRoot_bridge_value]
    have hcell : (⟨i,⟨i.val+1-j.val,by omega⟩⟩ : Cell n)=b ↔
        i.val=b.1.val ∧ i.val+1-j.val=b.2.val := by
      constructor
      · intro h; exact ⟨congrArg (fun x:Cell n=>x.1.val) h,congrArg (fun x:Cell n=>x.2.val) h⟩
      · intro h; exact cell_ext (Fin.ext h.1) h.2
    simp only [hcell,eventNodeWeight,ownNodeWeight,lowerNodeWeight,upperNodeWeight,phaseEarlier,cellRow,Fin.ext_iff,Fin.lt_def]
    by_cases hlev:i.val=b.1.val
    · simp only [hlev,ite_true, if_true,true_and,lt_self_iff_false,and_false,or_false]
      split_ifs <;> first | contradiction | omega
    · simp only [hlev,ite_false, if_false]
      by_cases hlo:i.val+1=b.1.val
      · simp only [hlo,true_or,ite_true, if_true]
        split_ifs <;> first | contradiction | omega
      · simp only [hlo,false_or,ite_false, if_false]
        by_cases hup:b.1.val+1=i.val
        · simp only [hup,ite_true, if_true]
          split_ifs <;> first | contradiction | omega
        · simp only [hup,ite_false, if_false]

lemma ownNodeWeight_step (a r j:ℕ) (hr:r ≤ a) (hj:j ≤ a+1) :
    ownNodeWeight a r (j+1)-ownNodeWeight a r j=
      (if j=0 then 1 else 0)-(if j=a-r then 1 else 0)-
      (if j=a+1-r then 1 else 0)-(if j=a+1 then 1 else 0) := by
  have h1 : j=a-r ↔ j+r=a := by omega
  have h2 : j=a+1-r ↔ j+r=a+1 := by omega
  simp only [ownNodeWeight,h1,h2]
  by_cases hz:j=0
  · simp only [hz,zero_add]
    split_ifs <;> first | contradiction | omega
  · simp only [hz,ite_false, if_false]
    by_cases he:j=a+1
    · simp only [he]
      split_ifs <;> first | contradiction | omega
    · split_ifs <;> first | contradiction | omega

lemma lowerNodeWeight_step (a r j:ℕ) (hr:r ≤ a+1) (hj:j ≤ a+1) :
    lowerNodeWeight a r (j+1)-lowerNodeWeight a r j=
      -(if j=0 then 1 else 0)+(if j=a+1-r then 1 else 0)+
      (if j=a+1 then 1 else 0) := by
  have h1:j=a+1-r ↔ j+r=a+1 := by omega
  simp only [lowerNodeWeight,h1]
  by_cases hz:j=0
  · simp only [hz,zero_add]
    split_ifs <;> first | contradiction | omega
  · simp only [hz,ite_false, if_false]
    by_cases he:j=a+1
    · simp only [he]
      split_ifs <;> first | contradiction | omega
    · split_ifs <;> first | contradiction | omega

lemma upperNodeWeight_step (a r j:ℕ) (hr:r < a) (hj:j ≤ a+1) :
    upperNodeWeight a r (j+1)-upperNodeWeight a r j=
      (if j=a-r then 1 else 0) := by
  have h1:j=a-r ↔ j+r=a := by omega
  simp only [upperNodeWeight,h1]
  split_ifs <;> first | contradiction | omega

def eventGapWeight (b:Cell n) (g:GapIndex n) : ℤ :=
  if g.1=b.1 then
    (if g.2.val=0 then 1 else 0) -
    (if g.2.val=b.1.val-b.2.val then 1 else 0) -
    (if g.2.val=b.1.val+1-b.2.val then 1 else 0) -
    (if g.2.val=b.1.val+1 then 1 else 0)
  else if g.1.val+1=b.1.val then
    -(if g.2.val=0 then 1 else 0) +
    (if g.2.val=b.1.val-b.2.val then 1 else 0) +
    (if g.2.val=b.1.val then 1 else 0)
  else if b.1.val+1=g.1.val then
    (if g.2.val=b.1.val+1-b.2.val then 1 else 0)
  else 0

lemma eventRoot_forwardGap (b:Cell n) (g:GapIndex n) :
    triangularOmega n (eventRoot cellLevel 0 b) (forwardGap g)=eventGapWeight b g := by
  rw [forwardGap,map_sub,eventRoot_levelNode,eventRoot_levelNode]
  simp only [Fin.val_succ,Fin.val_castSucc,eventNodeWeight,eventGapWeight,Fin.ext_iff]
  have hb:=b.2.isLt
  have hg:=g.2.isLt
  by_cases hlev:g.1.val=b.1.val
  · simp only [hlev,ite_true, if_true]
    exact ownNodeWeight_step _ _ _ (by omega) (by omega)
  · simp only [hlev,ite_false, if_false]
    by_cases hlo:g.1.val+1=b.1.val
    · simp only [hlo,ite_true, if_true]
      convert lowerNodeWeight_step g.1.val b.2.val g.2.val (by omega) (by omega) using 1
      all_goals try with_reducible_and_instances rfl
      rw [hlo]
    · simp only [hlo,ite_false, if_false]
      by_cases hup:b.1.val+1=g.1.val
      · simp only [hup,ite_true, if_true]
        convert upperNodeWeight_step g.1.val b.2.val g.2.val (by omega) (by omega) using 1
      · simp only [hup,ite_false, if_false,sub_self]
end
end ElementaryPositivity.TriangularDynamics

end
section
namespace ElementaryPositivity.TriangularDynamics
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ}

def gapValue (c:GapIndex n → ℤ) (i t:ℕ) : ℤ :=
  ∑g,if g.1.val+1=i ∧ g.2.val=t then c g else 0

lemma gapValue_nonneg (c:GapIndex n → ℤ) (hc:∀g,0 ≤ c g) (i t:ℕ) : 0 ≤ gapValue c i t := by
  apply Finset.sum_nonneg
  intro g _
  split_ifs <;> first | exact hc g | omega

lemma gapValue_out (c:GapIndex n → ℤ) (i t:ℕ)
    (h:¬(1 ≤ i ∧ i ≤ n ∧ t ≤ i)) : gapValue c i t=0 := by
  apply Finset.sum_eq_zero
  intro g _
  split_ifs with hg
  · have h1:=g.1.isLt
    have h2:=g.2.isLt
    exact (h (by omega)).elim
  · rfl

lemma sum_eventGapWeight (c:GapIndex n → ℤ) (b:Cell n) :
    (∑g,c g*eventGapWeight b g)=
      gapValue c (b.1.val+1) 0-gapValue c (b.1.val+1) (b.1.val-b.2.val)-
      gapValue c (b.1.val+1) (b.1.val+1-b.2.val)-gapValue c (b.1.val+1) (b.1.val+1)-
      gapValue c b.1.val 0+gapValue c b.1.val (b.1.val-b.2.val)+gapValue c b.1.val b.1.val+
      gapValue c (b.1.val+2) (b.1.val+1-b.2.val) := by
  simp only [gapValue,←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro g _
  have h1:g.1.val+1=b.1.val+1 ↔ g.1.val=b.1.val := by omega
  have h2:g.1.val+1=b.1.val+2 ↔ b.1.val+1=g.1.val := by omega
  simp only [eventGapWeight,Fin.ext_iff,h1,h2]
  by_cases he:g.1.val=b.1.val
  · have hlo:g.1.val+1≠b.1.val:=by omega
    have hup:b.1.val+1≠g.1.val:=by omega
    have hself:b.1.val+1≠b.1.val:=by omega
    simp only [he,hself,true_and,false_and,ite_true, if_true,ite_false, if_false,mul_sub,mul_ite,mul_one,mul_zero]
    ring
  · by_cases hlo:g.1.val+1=b.1.val
    · have hup:b.1.val+1≠g.1.val:=by omega
      simp only [he,hlo,hup,true_and,false_and,ite_true, if_true,ite_false, if_false,mul_add,mul_neg,mul_ite,mul_one,mul_zero]
      ring
    · by_cases hup:b.1.val+1=g.1.val
      · simp only [he,hlo,hup,true_and,false_and,ite_true, if_true,ite_false, if_false,mul_ite,mul_one,mul_zero]
        ring
      · simp only [he,hlo,hup,false_and,ite_false, if_false,mul_zero,sub_zero,add_zero]

lemma eventRoot_roots (b:Cell n) (c:GapIndex n → ℤ) :
    triangularOmega n (eventRoot cellLevel 0 b) (forwardRoots c)=∑g,c g*eventGapWeight b g := by
  rw [forwardRoots_apply,map_sum]
  simp only [map_zsmul,smul_eq_mul,eventRoot_forwardGap]
end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TriangularGaps
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instAddCommGroup _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.degreesDecidableEq _root_.OAI.ElementaryPositivity.RawShuffle.quotientCommRing
attribute [-simp] _root_.OAI.ElementaryPositivity.WallUnits.rescale_C
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TriangularGaps

structure Recurrence (n : ℕ) where
  u : ℕ → ℕ → ℕ
  T : ℕ → ℕ → ℕ
  xi : ℕ → ℕ → ℕ
  u_out : ∀ j i, ¬(1 ≤ j ∧ j ≤ i ∧ i ≤ n) → u j i = 0
  T_out : ∀ j i, ¬(1 ≤ j ∧ j ≤ i ∧ i ≤ n) → T j i = 0
  diagonal : ∀ j i, 1 ≤ j → j ≤ i → i ≤ n →
    u j i = T j i + u (j + 1) (i + 1)
  row : ∀ j i, 1 ≤ j → j ≤ i → i < n →
    T j (i + 1) + xi j (i + 1) = T j i
  start : ∀ j, 1 ≤ j → j ≤ n →
    T j j + xi j j + u 1 j = (if j = 1 then 1 else 0) + u 1 (j - 1)

structure IntegerGaps (n : ℕ) where
  u : ℕ → ℕ → ℤ
  xi : ℕ → ℕ → ℤ
  u_out : ∀ j i, ¬(1 ≤ j ∧ j ≤ i ∧ i ≤ n) → u j i = 0
  u_nonneg : ∀ j i, 0 ≤ u j i
  xi_nonneg : ∀ j i, 1 ≤ j → j ≤ i → i ≤ n → 0 ≤ xi j i
  pairing : ∀ j i, 1 ≤ j → j ≤ i → i ≤ n →
    xi j i = (if i = 1 then 1 else 0) - u j i -
      (if j < i then u (j+1) i else u 1 i) +
      (if j < i then u j (i-1) else u 1 (j-1)) + u (j+1) (i+1)

namespace IntegerGaps
variable {n : ℕ} (A : IntegerGaps n)

def t (j i : ℕ) : ℤ := A.u j i - A.u (j+1) (i+1)

lemma t_row (j i : ℕ) (hj : 1 ≤ j) (hji : j ≤ i) (hi : i < n) :
    A.t j (i+1) + A.xi j (i+1) = A.t j i := by
  have h := A.pairing j (i+1) hj (by omega) (by omega)
  rw [ite_eq_right (show i+1 ≠ 1 by omega), ite_eq_left (by omega), ite_eq_left (by omega)] at h
  simp only [Nat.add_sub_cancel] at h
  dsimp [t]
  linarith

lemma t_start (j : ℕ) (hj : 1 ≤ j) (hjn : j ≤ n) :
    A.t j j + A.xi j j + A.u 1 j = (if j = 1 then 1 else 0) + A.u 1 (j-1) := by
  have h := A.pairing j j hj le_rfl hjn
  simp only [lt_self_iff_false, ite_false, if_false] at h
  dsimp [t]
  linarith

lemma t_nonneg (j i : ℕ) (hj : 1 ≤ j) (hji : j ≤ i) (hi : i ≤ n) :
    0 ≤ A.t j i := by
  apply Nat.decreasingInduction' (m := i) (n := n) (P := fun k => 0 ≤ A.t j k) _ hi
  · dsimp [t]
    rw [A.u_out (j+1) (n+1) (by omega), sub_zero]
    exact A.u_nonneg j n
  · intro k hk hik hnext
    have hr := A.t_row j k hj (by omega) hk
    have hx := A.xi_nonneg j (k+1) hj (by omega) (by omega)
    linarith

def recurrence : Recurrence n where
  u j i := (A.u j i).toNat
  T j i := if 1 ≤ j ∧ j ≤ i ∧ i ≤ n then (A.t j i).toNat else 0
  xi j i := (A.xi j i).toNat
  u_out j i h := by simp only [A.u_out j i h, Int.toNat_zero]
  T_out j i h := by simp only [ite_eq_right h]
  diagonal j i hj hji hi := by
    rw [ite_eq_left ⟨hj, hji, hi⟩, ← Int.toNat_add (A.t_nonneg j i hj hji hi) (A.u_nonneg _ _)]
    congr 1
    dsimp [t]
    ring
  row j i hj hji hi := by
    rw [ite_eq_left ⟨hj, by omega, by omega⟩, ite_eq_left ⟨hj, hji, by omega⟩,
      ← Int.toNat_add (A.t_nonneg j (i+1) hj (by omega) (by omega))
        (A.xi_nonneg j (i+1) hj (by omega) (by omega)), A.t_row j i hj hji hi]
  start j hj hjn := by
    rw [ite_eq_left ⟨hj, le_rfl, hjn⟩,
      ← Int.toNat_add (A.t_nonneg j j hj le_rfl hjn) (A.xi_nonneg j j hj le_rfl hjn),
      ← Int.toNat_add (add_nonneg (A.t_nonneg j j hj le_rfl hjn)
        (A.xi_nonneg j j hj le_rfl hjn)) (A.u_nonneg 1 j), A.t_start j hj hjn]
    split_ifs <;> simp [Int.toNat_add, A.u_nonneg]

end IntegerGaps
end ElementaryPositivity.TriangularGaps

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TriangularGapTotals
attribute [-instance] _root_.OAI.ElementaryPositivity.TriangularDynamics.instAntisymmCellPhaseLE _root_.OAI.ElementaryPositivity.TriangularDynamics.instDecidableRelCellPhaseLE _root_.OAI.ElementaryPositivity.TriangularDynamics.instIsTransCellPhaseLE _root_.OAI.ElementaryPositivity.TriangularDynamics.instTotalCellPhaseLE
attribute [-simp] _root_.OAI.ElementaryPositivity.TriangularDynamics.levelNode_last _root_.OAI.ElementaryPositivity.TriangularDynamics.levelNode_zero _root_.OAI.ElementaryPositivity.TriangularDynamics.mem_phaseCycle _root_.OAI.ElementaryPositivity.TriangularDynamics.partialBridge_cycle _root_.OAI.ElementaryPositivity.TriangularDynamics.partialBridge_nil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ}

lemma levelTotal_node (i j:Fin n) (t:Fin (j.val+3)) :
    levelTotal cellLevel i (Pi.single (levelNode j t) (1:ℤ))=
      if j=i ∧ 0<t.val ∧ t.val<j.val+2 then 1 else 0 := by
  unfold levelNode
  by_cases h0:t.val=0
  · rw [dite_eq_left h0]
    change levelTotal cellLevel i (anchor j.castSucc)=_
    rw [levelTotal_anchor]
    simp only [h0,lt_self_iff_false,false_and,and_false,ite_false, if_false]
  · rw [dite_eq_right h0]
    by_cases he:t.val=j.val+2
    · rw [dite_eq_left he]
      change levelTotal cellLevel i (anchor j.succ)=_
      rw [levelTotal_anchor]
      simp only [he,lt_self_iff_false,and_false,ite_false, if_false]
    · rw [dite_eq_right he]
      change levelTotal cellLevel i (bridge ⟨j,⟨j.val+1-t.val,_⟩⟩)=_
      rw [levelTotal_bridge]
      have h1:0<t.val:=by omega
      have h2:t.val<j.val+2:=by have := t.isLt; omega
      simp only [cellLevel,h1,h2,and_true]
      rfl

lemma levelTotal_gap (i:Fin n) (g:GapIndex n) :
    levelTotal cellLevel i (forwardGap g)=
      (if g.1=i ∧ g.2.val=0 then 1 else 0)-
      (if g.1=i ∧ g.2.val=g.1.val+1 then 1 else 0) := by
  rw [forwardGap,map_sub,levelTotal_node,levelTotal_node]
  simp only [Fin.val_succ,Fin.val_castSucc]
  have hg:=g.2.isLt
  by_cases hi:g.1=i
  · simp only [hi,true_and]
    split_ifs <;> omega
  · simp only [hi,false_and,ite_false, if_false,sub_self]

lemma levelTotal_roots (i:Fin n) (c:GapIndex n → ℤ) :
    levelTotal cellLevel i (forwardRoots c)=gapValue c (i.val+1) 0-gapValue c (i.val+1) (i.val+1) := by
  rw [forwardRoots_apply,map_sum]
  simp only [map_zsmul,smul_eq_mul,levelTotal_gap,gapValue,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro g _
  have h1:g.1.val+1=i.val+1 ↔ g.1=i := by simp [Fin.ext_iff]
  by_cases he:g.1=i
  · simp only [he,true_and,mul_sub,mul_ite,mul_one,mul_zero]
  · simp only [h1,he,false_and,ite_false, if_false,sub_self,mul_zero]

lemma gapValue_end_eq (c:GapIndex n → ℤ) (m:Lattice n (Cell n))
    (hm:m=anchor 0+forwardRoots c) (hK:∀i,levelTotal cellLevel i m=0) (i:ℕ) :
    gapValue c i 0=gapValue c i i := by
  by_cases hi:1 ≤ i ∧ i ≤ n
  · let a:Fin n:=⟨i-1,by omega⟩
    have H:=hK a
    rw [hm,map_add,levelTotal_anchor,zero_add,levelTotal_roots] at H
    have ha:a.val+1=i:=by dsimp [a]; omega
    rw [ha] at H
    omega
  · rw [gapValue_out c i 0 (by omega),gapValue_out c i i (by omega)]
end
end ElementaryPositivity.TriangularDynamics

end
section
namespace ElementaryPositivity.TriangularDynamics
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ}

def gapU (c:GapIndex n → ℤ) (j i:ℕ) : ℤ :=
  if 1 ≤ j ∧ j ≤ i ∧ i ≤ n then gapValue c i (i+1-j) else 0

def indexedCell (j i:ℕ) (h:1 ≤ j ∧ j ≤ i ∧ i ≤ n) : Cell n :=
  ⟨⟨i-1,by omega⟩,⟨j-1,by change j-1 < i-1+1; omega⟩⟩

def gapXi (m:Lattice n (Cell n)) (j i:ℕ) : ℤ :=
  if h:1 ≤ j ∧ j ≤ i ∧ i ≤ n then triangularOmega n (eventRoot cellLevel 0 (indexedCell j i h)) m else 0

lemma gapU_first (c:GapIndex n → ℤ) (i:ℕ) : gapU c 1 i=gapValue c i i := by
  unfold gapU
  by_cases h:1 ≤ 1 ∧ 1 ≤ i ∧ i ≤ n
  · rw [ite_eq_left h,Nat.add_sub_cancel]
  · rw [ite_eq_right h,gapValue_out c i i (by omega)]

lemma gapU_upper (c:GapIndex n → ℤ) (j i:ℕ) (hj:1 ≤ j) (hji:j ≤ i) :
    gapU c (j+1) (i+1)=gapValue c (i+1) (i+1-j) := by
  unfold gapU
  by_cases h:1 ≤ j+1 ∧ j+1 ≤ i+1 ∧ i+1 ≤ n
  · rw [ite_eq_left h]
    congr 1
    omega
  · rw [ite_eq_right h,gapValue_out c (i+1) (i+1-j) (by omega)]

lemma gapXi_formula (c:GapIndex n → ℤ) (m:Lattice n (Cell n))
    (hm:m=anchor 0+forwardRoots c) (hK:∀i,levelTotal cellLevel i m=0)
    (j i:ℕ) (hj:1 ≤ j) (hji:j ≤ i) (hi:i ≤ n) :
    gapXi m j i=(if i=1 then 1 else 0)-gapValue c i (i+1-j)-gapValue c i (i-j)+
      gapValue c (i-1) (i-j)+gapValue c (i+1) (i+1-j) := by
  have hh:1 ≤ j ∧ j ≤ i ∧ i ≤ n:=⟨hj,hji,hi⟩
  rw [gapXi,dite_eq_left hh,hm,map_add,eventRoot_anchor,eventRoot_roots,sum_eventGapWeight]
  simp only [indexedCell,Fin.ext_iff,Fin.val_zero,Fin.val_castSucc,Fin.val_succ]
  have h1:i-1+1=i:=by omega
  have h2:i-1-(j-1)=i-j:=by omega
  have h3:i-1+1-(j-1)=i+1-j:=by omega
  have h4:i-1+2=i+1:=by omega
  have hz:¬0=i-1+1:=by omega
  have hzi:0=i-1 ↔ i=1:=by omega
  rw [h2,h3,h4]
  have hze:¬0=i:=by omega
  simp only [hzi,h1,hze,ite_false, if_false,sub_zero]
  rw [gapValue_end_eq c m hm hK i,gapValue_end_eq c m hm hK (i-1)]
  ring

lemma gapXi_pairing (c:GapIndex n → ℤ) (m:Lattice n (Cell n))
    (hm:m=anchor 0+forwardRoots c) (hK:∀i,levelTotal cellLevel i m=0)
    (j i:ℕ) (hj:1 ≤ j) (hji:j ≤ i) (hi:i ≤ n) :
    gapXi m j i=(if i=1 then 1 else 0)-gapU c j i-
      (if j < i then gapU c (j+1) i else gapU c 1 i)+
      (if j < i then gapU c j (i-1) else gapU c 1 (j-1))+gapU c (j+1) (i+1) := by
  rw [gapXi_formula c m hm hK j i hj hji hi,gapU_upper c j i hj hji]
  have hu:gapU c j i=gapValue c i (i+1-j):=by rw [gapU,ite_eq_left ⟨hj,hji,hi⟩]
  rw [hu]
  by_cases hji':j < i
  · have hU1:gapU c (j+1) i=gapValue c i (i-j):=by
      rw [gapU,ite_eq_left (show 1 ≤ j+1 ∧ j+1 ≤ i ∧ i ≤ n by omega)]
      congr 1
      omega
    have hU2:gapU c j (i-1)=gapValue c (i-1) (i-j):=by
      rw [gapU,ite_eq_left (show 1 ≤ j ∧ j ≤ i-1 ∧ i-1 ≤ n by omega)]
      congr 1
      omega
    rw [ite_eq_left hji',ite_eq_left hji',hU1,hU2]
  · have hjj:j=i:=by omega
    subst j
    rw [ite_eq_right (lt_irrefl i),ite_eq_right (lt_irrefl i),gapU_first,gapU_first,Nat.sub_self,
      gapValue_end_eq c m hm hK i,gapValue_end_eq c m hm hK (i-1)]

def actualIntegerGaps (c:GapIndex n → ℤ) (m:Lattice n (Cell n))
    (hc:∀g,0 ≤ c g) (hm:m=anchor 0+forwardRoots c) (hK:∀i,levelTotal cellLevel i m=0)
    (hxi:∀b,0 ≤ triangularOmega n (eventRoot cellLevel 0 b) m) : TriangularGaps.IntegerGaps n where
  u:=gapU c
  xi:=gapXi m
  u_out j i h:=by rw [gapU,ite_eq_right h]
  u_nonneg j i:=by unfold gapU; split_ifs; exact gapValue_nonneg c hc _ _; omega
  xi_nonneg j i hj hji hi:=by rw [gapXi,dite_eq_left ⟨hj,hji,hi⟩]; exact hxi _
  pairing:=gapXi_pairing c m hm hK
end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TriangularLevelQueues
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open Classical
noncomputable section
variable {n : ℕ}

def initialLevelQueue (i : Fin n) : List (Cell n) := List.ofFn (fun j:Fin (i.val+1)=>⟨i,j.rev⟩)

end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_ForwardChartMutation
attribute [-simp] _root_.OAI.ElementaryPositivity.TriangularDynamics.partialBridge_cycle _root_.OAI.ElementaryPositivity.TriangularDynamics.partialBridge_nil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open Classical
noncomputable section
variable {n : ℕ} {R : Type*} [CommRing R]

def gapIndices (n:ℕ) : List (GapIndex n) :=
  (List.finRange n).flatMap (fun i=>(List.finRange (i.val+2)).map (Sigma.mk i))

lemma simpleRoot_forwardRoots (i:GapIndex n) :
    QuantumTorus.simpleRoot (forwardRoots (R:=ℤ)).toAddMonoidHom i=forwardGap i := by
  rw [QuantumTorus.simpleRoot,LinearMap.toAddMonoidHom_coe,forwardRoots_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · simp
end
end ElementaryPositivity.TriangularDynamics

end
section
namespace ElementaryPositivity.LatticeExtension
open scoped BigOperators
variable {V : Type*} [Fintype V]
abbrev Extended (V : Type*) := (V → ℤ) × (V → ℤ)

def dot (x : V → ℤ) : (V → ℤ) →+ ℤ where
  toFun y := ∑ i,x i*y i
  map_zero' := by simp
  map_add' y z := by simp [mul_add,Finset.sum_add_distrib]

lemma dot_apply (x y : V → ℤ) : dot x y=∑i,x i*y i := by simp [dot]
lemma dot_add (x y z : V → ℤ) : dot (x+y) z=dot x z+dot y z := by
  simp only [dot_apply,Pi.add_apply,add_mul,Finset.sum_add_distrib]
lemma dot_zero (y : V → ℤ) : dot 0 y=0 := by simp [dot_apply]
@[simp] lemma dot_single [DecidableEq V] (x : V → ℤ) (i : V) : dot x (Pi.single i 1)=x i := by
  simp [dot_apply,Pi.single_apply]

variable (Ω : (V → ℤ) →+ (V → ℤ) →+ ℤ)
def form : Extended V →+ Extended V →+ ℤ where
  toFun x := ((Ω x.1).comp (AddMonoidHom.fst _ _)) +
    ((dot x.2).comp (AddMonoidHom.fst _ _)) -
    ((dot x.1).comp (AddMonoidHom.snd _ _))
  map_zero' := by ext y; simp [dot_zero]
  map_add' x x' := by ext y; simp [dot_add]; abel

lemma form_apply (x y : Extended V) :
    form Ω x y=Ω x.1 y.1+dot x.2 y.1-dot x.1 y.2 := rfl

def includeVertices : (V → ℤ) →+ Extended V := (AddMonoidHom.id _).prod 0
omit [Fintype V] in
@[simp] lemma includeVertices_apply (m : V → ℤ) : includeVertices m=(m,0) := rfl
@[simp] lemma form_original (m m' : V → ℤ) :
    form Ω (includeVertices m) (includeVertices m')=Ω m m' := by
  simp [form_apply,dot_zero]

end ElementaryPositivity.LatticeExtension

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_RealLatticeRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.LatticeRealization
open scoped BigOperators
open TriangularDynamics
variable {V : Type*} [Fintype V] [DecidableEq V]

variable (A : Matrix V V ℤ)
noncomputable def realPairing : (V → ℝ) →ₗ[ℝ] (V → ℝ) →ₗ[ℝ] ℝ :=
  Matrix.toBilin' (fun i j => (A i j:ℝ))

noncomputable def realDot : (V → ℝ) →ₗ[ℝ] (V → ℝ) →ₗ[ℝ] ℝ := Matrix.toBilin' (1 : Matrix V V ℝ)

noncomputable def extendedCast : LatticeExtension.Extended V →+ ((V → ℝ) × (V → ℝ)) :=
  (cast.comp (AddMonoidHom.fst _ _)).prod (cast.comp (AddMonoidHom.snd _ _))

noncomputable def extendedRealForm : ((V → ℝ) × (V → ℝ)) →ₗ[ℝ]
    ((V → ℝ) × (V → ℝ)) →ₗ[ℝ] ℝ :=
  ((realPairing A).compl₁₂ (LinearMap.fst ℝ _ _) (LinearMap.fst ℝ _ _)) +
    (realDot.compl₁₂ (LinearMap.snd ℝ _ _) (LinearMap.fst ℝ _ _)) -
    (realDot.compl₁₂ (LinearMap.fst ℝ _ _) (LinearMap.snd ℝ _ _))

end ElementaryPositivity.LatticeRealization

end
section
namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus LatticeExtension LatticeRealization
open Classical
noncomputable section
variable {n:ℕ}

lemma cast_single {V:Type*} [Fintype V] [DecidableEq V] (i:V) (z:ℤ) :
    LatticeRealization.cast (Pi.single i z)=Pi.single i (z:ℝ) := by
  ext j
  simp only [LatticeRealization.cast_apply,Pi.single_apply]
  split_ifs <;> simp
lemma cast_forwardGap (g:GapIndex n) :
    LatticeRealization.cast (forwardGap (R:=ℤ) g)=forwardGap (R:=ℝ) g := by
  simp only [forwardGap,map_sub,cast_single,Int.cast_one]

def extendedRoots (n:ℕ) : (GapIndex n → ℤ) →+ Extended (Vertex n (Cell n)) :=
  includeVertices.comp (forwardRoots (R:=ℤ)).toAddMonoidHom

def extendedCoord (n:ℕ) : Extended (Vertex n (Cell n)) →+ (GapIndex n → ℤ) :=
  (forwardCoord (R:=ℤ)).toAddMonoidHom.comp (AddMonoidHom.fst _ _)

lemma extendedCoord_roots (c:GapIndex n → ℤ) : extendedCoord n (extendedRoots n c)=c := by
  exact forwardCoord_roots c
lemma extendedRoot_eq (g:GapIndex n) : simpleRoot (extendedRoots n) g=includeVertices (forwardGap g) := by
  change includeVertices (simpleRoot (forwardRoots (R:=ℤ)).toAddMonoidHom g)=_
  rw [simpleRoot_forwardRoots]
lemma extendedRoots_realIndependent :
    LinearIndependent ℝ (fun i:GapIndex n=>extendedCast (simpleRoot (extendedRoots n) i)) := by
  let incl : (Vertex n (Cell n) → ℝ) →ₗ[ℝ]
      ((Vertex n (Cell n) → ℝ) × (Vertex n (Cell n) → ℝ)) := LinearMap.inl ℝ _ _
  have hincl : Function.Injective incl := by
    intro x y h
    exact congrArg Prod.fst h
  have hk : LinearMap.ker incl = ⊥ := LinearMap.ker_eq_bot.mpr hincl
  have Hi : LinearIndependent ℝ (incl ∘ (forwardGap (R:=ℝ) (n:=n))) :=
    (forwardGap_independent (R:=ℝ) (n:=n)).map' incl hk
  convert Hi using 1
  all_goals try with_reducible_and_instances rfl
  funext i
  rw [extendedRoot_eq]
  change (LatticeRealization.cast (forwardGap (R:=ℤ) i),LatticeRealization.cast 0)=(forwardGap i,0)
  rw [cast_forwardGap,map_zero]

def initialFreeChart (n:ℕ) : FreeChart (I:=GapIndex n) (extendedCast (V:=Vertex n (Cell n))) where
  roots := extendedRoots n
  coord := extendedCoord n
  retract := extendedCoord_roots
  independent := extendedRoots_realIndependent

def extendedOmega (n:ℕ) := LatticeExtension.form (triangularOmega n)
lemma extendedOmega_original (m m':Lattice n (Cell n)) :
    extendedOmega n (includeVertices m) (includeVertices m')=triangularOmega n m m' := form_original _ _ _
def triangularRealForm (n:ℕ) := extendedRealForm (chartMatrix (@cellLevel n) (@triangularBB n))
end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TriangularPolynomialStationarity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus WallUnits LatticeExtension LatticeRealization
open Classical
noncomputable section
variable {n:ℕ}

def triangularExpression {N:ℕ} (f:ElementaryExpr N) : Torus LaurentRay.vUnit (extendedOmega n) :=
  f.eval LaurentRay.vUnit (extendedOmega n) (vertexDisplay (includeVertices ∘ anchor) (includeVertices ∘ bridge))

def triangularIncoming {N:ℕ} (f:ElementaryExpr N) (m:Lattice n (Cell n)) : LaurentSeries ℚ :=
  polynomialSectionIncoming (extendedOmega n) (extendedRoots n) (extendedCoord n)
    (triangularExpression f) (includeVertices m)

end
end ElementaryPositivity.TriangularDynamics

end
section
namespace ElementaryPositivity.TriangularDynamics
open scoped BigOperators
open QuantumTorus
open Classical
noncomputable section
variable {n:ℕ} {R:Type*} [CommRing R]

def vertexWeight : (Vertex n (Cell n) → R) →ₗ[R] R := ∑a,LinearMap.proj a
end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TriangularLinearSection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus WallUnits LatticeExtension
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ}

def pureAnchor (μ:Fin (n+1) → ℤ) : Lattice n (Cell n) :=
  ∑a,μ a • anchor a

lemma pureAnchor_apply_anchor (μ:Fin (n+1) → ℤ) (a:Fin (n+1)) : pureAnchor μ (.inl a)=μ a := by
  simp [pureAnchor,anchor,Finset.sum_apply,Pi.single_apply]
lemma pureAnchor_apply_bridge (μ:Fin (n+1) → ℤ) (b:Cell n) : pureAnchor μ (.inr b)=0 := by
  simp [pureAnchor,anchor,Finset.sum_apply]

lemma anchor_pair_pure (a:Fin (n+1)) (μ:Fin (n+1) → ℤ) :
    triangularOmega n (anchor a) (pureAnchor μ)=0 := by
  rw [pureAnchor,map_sum]
  simp only [map_zsmul,smul_eq_mul]
  apply Finset.sum_eq_zero
  intro b _
  have hh:triangularOmega n (anchor a) (anchor b)=0:=by
    change matrixPairing (chartMatrix cellLevel triangularBB) (Pi.single (.inl a) 1) (Pi.single (.inl b) 1)=0
    rw [matrixPairing_single]
    rfl
  rw [hh,mul_zero]

end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TriangularCommutativity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus WallUnits LatticeExtension
open Classical
noncomputable section
variable {n:ℕ}

local instance triangularCommutativityRing_r5b98ce_1 : Ring (Torus LaurentRay.vUnit (extendedOmega n)) := Torus.instRing LaurentRay.vUnit (extendedOmega n)
local instance triangularCommutativityAddCommGroup_r5b98ce_1 : AddCommGroup (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toAddCommGroup
local instance triangularCommutativityAddGroup_r5b98ce_1 : AddGroup (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toAddGroup
local instance triangularCommutativitySub_r5b98ce_1 : Sub (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toSub
lemma pureAnchor_pair (μ ν:Fin (n+1) → ℤ) : triangularOmega n (pureAnchor μ) (pureAnchor ν)=0 := by
  rw [pureAnchor,map_sum,AddMonoidHom.finsetSum_apply]
  simp only [map_zsmul,AddMonoidHom.zsmul_apply,anchor_pair_pure,zsmul_zero,Finset.sum_const_zero]

end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_ConeSectionDomination
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint WallUnits LaurentPositive
open Classical
noncomputable section
variable {M E I:Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]
variable (Ω:M →+ M →+ ℤ) (C:(I → ℤ) →+ M)
local instance coneSectionDominationTorusRing_r5b98ce_1 : Ring (Torus LaurentRay.vUnit Ω) :=
  Torus.instRing LaurentRay.vUnit Ω
local instance coneSectionDominationTorusAddCommMonoid : AddCommMonoid (Torus LaurentRay.vUnit Ω) :=
  (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance coneSectionDominationTorusAddCommGroup : AddCommGroup (Torus LaurentRay.vUnit Ω) :=
  (Torus.instRing LaurentRay.vUnit Ω).toAddCommGroup
local instance coneSectionDominationTorusAddGroup : AddGroup (Torus LaurentRay.vUnit Ω) :=
  (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
local instance coneSectionDominationTorusSub : Sub (Torus LaurentRay.vUnit Ω) :=
  (Torus.instRing LaurentRay.vUnit Ω).toSub
variable (F:CompletedPositive LaurentRay.vUnit Ω C) (base:M)

local instance coneSectionDominationTorusNonUnitalSemiring_r5b98ce_1 : NonUnitalSemiring (Torus LaurentRay.vUnit Ω) :=
  (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalSemiring
local instance coneSectionDominationTorusNonUnitalNonAssocSemiring_r5b98ce_1 :
    NonUnitalNonAssocSemiring (Torus LaurentRay.vUnit Ω) :=
  (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalNonAssocSemiring
def coneDelta (d:ℕ) (m:M) (k:ℕ) : Torus LaurentRay.vUnit Ω :=
  if k=d then Torus.X LaurentRay.vUnit Ω m else 0

def coneThetaInitial (d:ℕ) (m:M) : PowerSeries (Torus LaurentRay.vUnit Ω) :=
  sectionSolution LaurentRay.vUnit Ω C F base (coneDelta Ω d m)
def coneThetaValue (d:ℕ) (m:M) (h:M →+ ℝ) : PowerSeries (Torus LaurentRay.vUnit Ω) :=
  sectionValue LaurentRay.vUnit Ω C F h (coneThetaInitial Ω C F base d m)
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TriangularPositivePowers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus WallUnits LatticeExtension LatticeRealization PowerSeries PowerSeriesAdjoint LaurentPositive
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ}
local instance triangularPositivePowersRing : Ring (Torus LaurentRay.vUnit (extendedOmega n)) := Torus.instRing LaurentRay.vUnit (extendedOmega n)

def linearPower : (N:ℕ) → ElementaryExpr N
  | 0 => .one
  | N+1 => .mul (linearPower N) (.atom 1)

end
end ElementaryPositivity.TriangularDynamics

end
section
namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus WallUnits LatticeExtension PowerSeries PowerSeriesAdjoint LaurentPositive
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ}
local instance triangularOrdinaryPowersRing : Ring (Torus LaurentRay.vUnit (extendedOmega n)) := Torus.instRing LaurentRay.vUnit (extendedOmega n)
local instance triangularOrdinaryPowersAddCommMonoid : AddCommMonoid (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toAddCommMonoid
local instance triangularOrdinaryPowersAddCommGroup : AddCommGroup (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toAddCommGroup
local instance triangularOrdinaryPowersAddGroup : AddGroup (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toAddGroup
local instance triangularOrdinaryPowersSub : Sub (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toSub

def natAnchor (μ:Fin (n+1) → ℕ) : Lattice n (Cell n) := pureAnchor (fun a=>(μ a:ℤ))
end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_LaurentPositiveDomination
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus WallUnits LatticeExtension LatticeRealization PowerSeries PowerSeriesAdjoint LaurentPositive
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ}
local instance instRingTorusLaurentSeriesRatExtendedVertexCellVUnitExtendedOmega : Ring (Torus LaurentRay.vUnit (extendedOmega n)) := Torus.instRing LaurentRay.vUnit (extendedOmega n)
local instance instAddCommMonoidTorusLaurentSeriesRatExtendedVertexCellVUnitExtendedOmega : AddCommMonoid (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toAddCommMonoid
local instance instAddCommGroupTorusLaurentSeriesRatExtendedVertexCellVUnitExtendedOmega : AddCommGroup (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toAddCommGroup
local instance instAddGroupTorusLaurentSeriesRatExtendedVertexCellVUnitExtendedOmega : AddGroup (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toAddGroup
local instance instSubTorusLaurentSeriesRatExtendedVertexCellVUnitExtendedOmega : Sub (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toSub

def triangularBase (N:ℕ) : Extended (Vertex n (Cell n)) := includeVertices ((N:ℤ) • anchor 0)

def triangularConeTheta (N d:ℕ) (μ:Fin (n+1) → ℕ) (h:Extended (Vertex n (Cell n)) →+ ℝ) :=
  coneThetaValue (extendedOmega n) (extendedRoots n) (simpleTotalTransport (extendedOmega n) (extendedRoots n))
    (triangularBase N) d (includeVertices (natAnchor μ)) h

end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TriangularMonomialCriterion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus WallUnits LatticeExtension LatticeRealization PowerSeries PowerSeriesAdjoint LaurentPositive
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ}
local instance instRingTorusLaurentSeriesRatExtendedVertexCellVUnitExtendedOmega_1 : Ring (Torus LaurentRay.vUnit (extendedOmega n)) := Torus.instRing LaurentRay.vUnit (extendedOmega n)
local instance instAddCommMonoidTorusLaurentSeriesRatExtendedVertexCellVUnitExtendedOmega_1_r5b98ce_1 : AddCommMonoid (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toAddCommMonoid
local instance instAddCommGroupTorusLaurentSeriesRatExtendedVertexCellVUnitExtendedOmega_1_r5b98ce_1 : AddCommGroup (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toAddCommGroup
local instance instAddGroupTorusLaurentSeriesRatExtendedVertexCellVUnitExtendedOmega_1_r5b98ce_1 : AddGroup (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toAddGroup
local instance instSubTorusLaurentSeriesRatExtendedVertexCellVUnitExtendedOmega_1 : Sub (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toSub

end
end ElementaryPositivity.TriangularDynamics

end
section
namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus WallUnits LatticeExtension
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ}
local instance instRingTorusLaurentSeriesRatExtendedVertexCellVUnitExtendedOmega_2 : Ring (Torus LaurentRay.vUnit (extendedOmega n)) := Torus.instRing LaurentRay.vUnit (extendedOmega n)

local instance instAddCommMonoidTorusLaurentSeriesRatExtendedVertexCellVUnitExtendedOmega_2_r5b98ce_1 : AddCommMonoid (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toAddCommMonoid
local instance instAddCommGroupTorusLaurentSeriesRatExtendedVertexCellVUnitExtendedOmega_2_r5b98ce_1 : AddCommGroup (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toAddCommGroup
local instance instAddGroupTorusLaurentSeriesRatExtendedVertexCellVUnitExtendedOmega_2_r5b98ce_1 : AddGroup (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toAddGroup
local instance instSubTorusLaurentSeriesRatExtendedVertexCellVUnitExtendedOmega_2_r5b98ce_1 : Sub (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toSub
def anchorExponent : (Fin (n+1) →₀ ℕ) →+ Extended (Vertex n (Cell n)) where
  toFun d:=includeVertices (pureAnchor (fun a=>(d a:ℤ)))
  map_zero':=by apply Prod.ext; ext a; cases a <;> simp [pureAnchor_apply_anchor,pureAnchor_apply_bridge]; rfl
  map_add' d e:=by
    apply Prod.ext
    · ext a
      cases a <;> simp [pureAnchor_apply_anchor,pureAnchor_apply_bridge]
    · rfl
lemma anchorExponent_pair (d e:Fin (n+1) →₀ ℕ) :
    extendedOmega n (anchorExponent d) (anchorExponent e)=0 := by
  change extendedOmega n (includeVertices _) (includeVertices _)=0
  rw [extendedOmega_original,pureAnchor_pair]

def anchorPolynomialAdd : MvPolynomial (Fin (n+1)) (LaurentSeries ℚ) →+
    Torus LaurentRay.vUnit (extendedOmega n) where
  toFun p:=Finsupp.mapDomain (anchorExponent (n:=n)) (AddMonoidAlgebra.coeff p)
  map_zero':=Finsupp.mapDomain_zero
  map_add' _ _:=Finsupp.mapDomain_add
lemma anchorPolynomial_monomial (d:Fin (n+1) →₀ ℕ) (r:LaurentSeries ℚ) :
    anchorPolynomialAdd (MvPolynomial.monomial d r)=Torus.monomial LaurentRay.vUnit (extendedOmega n) (anchorExponent d) r :=
  Finsupp.mapDomain_single
lemma anchorPolynomial_mul (p q:MvPolynomial (Fin (n+1)) (LaurentSeries ℚ)) :
    anchorPolynomialAdd (p*q)=anchorPolynomialAdd p*anchorPolynomialAdd q := by
  induction p using MvPolynomial.induction_on' with
  | add p p' hp hp'=>simp only [add_mul,map_add,hp,hp']
  | monomial d r=>
    induction q using MvPolynomial.induction_on' with
    | add q q' hq hq'=>simp only [mul_add,map_add,hq,hq']
    | monomial e s=>
      rw [MvPolynomial.monomial_mul_monomial,anchorPolynomial_monomial,anchorPolynomial_monomial,anchorPolynomial_monomial,
        Torus.monomial_mul_monomial,anchorExponent_pair,zpow_zero,Units.val_one,mul_one,map_add]

def anchorPolynomial : MvPolynomial (Fin (n+1)) (LaurentSeries ℚ) →+*
    Torus LaurentRay.vUnit (extendedOmega n) where
  __:=anchorPolynomialAdd
  map_one':=by
    change anchorPolynomialAdd (MvPolynomial.monomial 0 1)=_
    rw [anchorPolynomial_monomial,map_zero]
    rfl
  map_mul':=anchorPolynomial_mul
end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TriangularAnchorProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus WallUnits LatticeExtension
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ}
local instance triangularAnchorProjectionRing : Ring (Torus LaurentRay.vUnit (extendedOmega n)) :=
  Torus.instRing LaurentRay.vUnit (extendedOmega n)
local instance triangularAnchorProjectionAddCommMonoid : AddCommMonoid (Torus LaurentRay.vUnit (extendedOmega n)) :=
  (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toAddCommMonoid
local instance triangularAnchorProjectionAddCommGroup : AddCommGroup (Torus LaurentRay.vUnit (extendedOmega n)) :=
  (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toAddCommGroup
local instance triangularAnchorProjectionAddGroup : AddGroup (Torus LaurentRay.vUnit (extendedOmega n)) :=
  (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toAddGroup

local instance triangularAnchorProjectionSub_r5b98ce_1 : Sub (Torus LaurentRay.vUnit (extendedOmega n)) :=
  (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toSub
def bridgeCut : Extended (Vertex n (Cell n)) →+ ℝ where
  toFun m:= -∑b:Cell n,(m.1 (.inr b):ℝ)
  map_zero':=by simp
  map_add' m r:=by simp [Finset.sum_add_distrib,add_comm]

end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_ExpressionAdditiveOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open scoped BigOperators
noncomputable section

def ElementaryExpr.nscale {N:ℕ} (k:ℕ) (f:ElementaryExpr N) : ElementaryExpr N :=
  match k with
  | 0=>.zero N
  | k+1=>.add (nscale k f) f

def ElementaryExpr.zscale {N:ℕ} (z:ℤ) (f:ElementaryExpr N) : ElementaryExpr N :=
  match z with
  | .ofNat k=>nscale k f
  | .negSucc k=>.neg (nscale (k+1) f)

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TriangularAnchored
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus WallUnits LatticeExtension LatticeRealization PowerSeries PowerSeriesAdjoint
open scoped BigOperators
open Classical
noncomputable section
variable {n : ℕ}

def AnchorSupported {N:ℕ} (f : ElementaryExpr N) : Prop :=
  ∀ m : Lattice n (Cell n), triangularIncoming f m ≠ 0 →
    ∃ μ : Fin (n+1) →₀ ℕ, μ.degree = N ∧
      (∀ i : Fin n, μ i.succ ≤ μ i.castSucc) ∧ m = natAnchor (fun a => μ a)

end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Histories_TriangularCommonHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus WallUnits LatticeExtension LatticeRealization PowerSeries PowerSeriesAdjoint
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ}

def AnchoredLeaf {E:Type*} [AddCommGroup E] [Module ℝ E]
    (N:ℕ) (p:LocalHistoryFormula (Extended (Vertex n (Cell n))) E) (l:p.Leaf) : Prop :=
  ∃μ:Fin (n+1) →₀ ℕ,μ.degree=N ∧ (∀i:Fin n,μ i.succ≤μ i.castSucc) ∧
    p.leafExponent l=anchorExponent μ

def leafProfile {E:Type*} [AddCommGroup E] [Module ℝ E] (N:ℕ)
    (p:LocalHistoryFormula (Extended (Vertex n (Cell n))) E)
    (l:{l:p.Leaf // AnchoredLeaf N p l}) : Fin (n+1) →₀ ℕ := l.property.choose
end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_Admissible
attribute [-instance] _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
attribute [-simp] _root_.OAI.ElementaryPositivity.WallUnits.rescale_C
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.NaturalUnitIntervalGraph
variable {n : ℕ} (G : ElementaryPositivity.NaturalUnitIntervalGraph n)

@[simp] theorem edge_comm (a b : Fin n) : G.Edge a b ↔ G.Edge b a := by
  simp only [Edge, or_comm]

@[simp] theorem edge_irrefl (a : Fin n) : ¬ G.Edge a a := by
  simp [Edge]

def reversePerm (σ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n) :=
  Fin.revPerm.trans σ

@[simp] theorem reversePerm_apply (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    reversePerm σ i = σ i.rev := rfl

@[simp] theorem reversePerm_reverse (σ : Equiv.Perm (Fin n)) :
    reversePerm (reversePerm σ) = σ := by
  ext i
  simp

def edges : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun ab => ab.1 < ab.2 ∧ G.Edge ab.1 ab.2)

def edgeCount : ℕ := G.edges.card

def invertedEdges (σ : Equiv.Perm (Fin n)) : Finset (Fin n × Fin n) :=
  G.edges.filter (fun ab => σ.symm ab.2 < σ.symm ab.1)

@[simp] lemma mem_edges (ab : Fin n × Fin n) :
    ab ∈ G.edges ↔ ab.1 < ab.2 ∧ G.Edge ab.1 ab.2 := by simp [edges]

@[simp] lemma mem_invertedEdges (σ : Equiv.Perm (Fin n)) (ab : Fin n × Fin n) :
    ab ∈ G.invertedEdges σ ↔
      ab.1 < ab.2 ∧ G.Edge ab.1 ab.2 ∧ σ.symm ab.2 < σ.symm ab.1 := by
  simp [invertedEdges, and_assoc]

@[simp] theorem inverse_reverse_apply (σ : Equiv.Perm (Fin n)) (a : Fin n) :
    (reversePerm σ).symm a = (σ.symm a).rev := rfl

def coloringInversions {r : ℕ} (f : Fin n → Fin r) : ℕ :=
  (G.edges.filter (fun ab => f ab.2 < f ab.1)).card

lemma coloringAscents_eq_card {r : ℕ} (f : Fin n → Fin r) :
    G.coloringAscents f = (G.edges.filter (fun ab => f ab.1 < f ab.2)).card := by
  unfold coloringAscents
  congr 1
  ext ab
  simp [edges, and_assoc]

theorem coloringInversions_add_ascents {r : ℕ} (f : Fin n → Fin r)
    (hf : G.Proper f) :
    G.coloringInversions f + G.coloringAscents f = G.edgeCount := by
  rw [coloringInversions, coloringAscents_eq_card]
  have hfilter : G.edges.filter (fun ab => f ab.1 < f ab.2) =
      G.edges.filter (fun ab => ¬ f ab.2 < f ab.1) := by
    apply Finset.filter_congr
    intro ab hab
    have hne := hf ab.1 ab.2 ((G.mem_edges ab).mp hab).2
    exact ⟨fun h => not_lt.mpr h.le, fun h => lt_of_le_of_ne (not_lt.mp h) hne⟩
  rw [hfilter]
  exact Finset.card_filter_add_card_filter_not (s := G.edges) _

end ElementaryPositivity.NaturalUnitIntervalGraph

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_GraphSquarefreeKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open scoped BigOperators
open Classical
noncomputable section

def ElementaryExpr.sequence : (a:List ℕ) → ElementaryExpr a.sum
  | []=>.one
  | k::a=>.mul (.atom k) (sequence a)

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_ElementaryMatrixDuality
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.degreesDecidableEq _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFinite _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
attribute [-simp] _root_.OAI.ElementaryPositivity.WallUnits.rescale_C
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.ElementaryMatrix
open scoped BigOperators
open Classical
noncomputable section
variable {A B:Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

def transpose (s:B → Finset A) : A → Finset B:=fun a=>Finset.univ.filter (fun b=>a∈s b)
lemma transpose_transpose (s:B → Finset A) : transpose (transpose s)=s := by
  funext b
  ext a
  simp [transpose]
def transposeEquiv : (B → Finset A) ≃ (A → Finset B) where
  toFun:=transpose
  invFun:=transpose
  left_inv:=transpose_transpose
  right_inv:=transpose_transpose

def rowCount (s:B → Finset A) : B →₀ ℕ:=Finsupp.equivFunOnFinite.symm (fun b=>(s b).card)
def colCount (s:B → Finset A) : A →₀ ℕ:=∑b,∑a∈s b,Finsupp.single a 1
omit [Fintype A] [DecidableEq B] in
lemma colCount_apply (s:B → Finset A) (a:A) : colCount s a=(transpose s a).card := by
  simp only [colCount,Finsupp.finsetSum_apply,Finsupp.single_apply]
  simp only [Finset.sum_ite_eq',Finset.sum_boole]
  rfl
omit [DecidableEq B] in
lemma rowCount_transpose (s:B → Finset A) : rowCount (transpose s)=colCount s := by
  ext a
  exact (colCount_apply s a).symm
lemma colCount_transpose (s:B → Finset A) : colCount (transpose s)=rowCount s := by
  rw [←rowCount_transpose,transpose_transpose]
omit [Fintype A] [DecidableEq A] [DecidableEq B] in
lemma rowCount_eq (s:B → Finset A) (a:B →₀ ℕ) : rowCount s=a ↔ ∀b,(s b).card=a b := by
  exact Finsupp.ext_iff

variable {R:Type*} [CommSemiring R]
omit [DecidableEq A] in
lemma esymm_all (k:ℕ) : MvPolynomial.esymm A R k=
    ∑s:Finset A,if s.card=k then MvPolynomial.monomial (∑a∈s,Finsupp.single a 1) (1:R) else 0 := by
  rw [MvPolynomial.esymm_eq_sum_monomial]
  have H:Finset.powersetCard k (Finset.univ:Finset A)=Finset.univ.filter (fun s:Finset A=>s.card=k):=by
    ext s
    simp
  rw [H,Finset.sum_filter]

omit [DecidableEq A] in
lemma elementary_product (a:B →₀ ℕ) :
    (∏b: B,MvPolynomial.esymm A R (a b))=
      ∑s:B → Finset A,if rowCount s=a then MvPolynomial.monomial (colCount s) (1:R) else 0 := by
  simp only [esymm_all]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro s hs
  by_cases h:rowCount s=a
  · rw [ite_eq_left h]
    have h':∀b,(s b).card=a b:=(rowCount_eq s a).mp h
    simp only [h',ite_true, if_true]
    exact (MvPolynomial.monomial_sum_one Finset.univ (fun b=>∑a∈s b,Finsupp.single a 1)).symm
  · rw [ite_eq_right h]
    obtain ⟨b,hb⟩:=not_forall.mp (mt (rowCount_eq s a).mpr h)
    exact Finset.prod_eq_zero (Finset.mem_univ b) (ite_eq_right hb)

lemma elementary_product_coeff (a:B →₀ ℕ) (μ:A →₀ ℕ) :
    (∏b:B,MvPolynomial.esymm A R (a b)).coeff μ=
      ∑s:B → Finset A,if rowCount s=a ∧ colCount s=μ then (1:R) else 0 := by
  rw [elementary_product,MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro s hs
  by_cases h:rowCount s=a
  · simp only [h,ite_true, if_true,true_and,MvPolynomial.coeff_monomial]
  · simp only [h,ite_false, if_false,false_and,MvPolynomial.coeff_zero,Finsupp.zero_apply]

theorem duality (a:B →₀ ℕ) (μ:A →₀ ℕ) :
    (∏b:B,MvPolynomial.esymm A R (a b)).coeff μ=
      (∏i:A,MvPolynomial.esymm B R (μ i)).coeff a := by
  rw [elementary_product_coeff,elementary_product_coeff,
    ←Equiv.sum_comp (transposeEquiv (A:=A) (B:=B))]
  apply Finset.sum_congr rfl
  intro s hs
  change (if rowCount s=a ∧ colCount s=μ then (1:R) else 0)=
    if rowCount (transpose s)=μ ∧ colCount (transpose s)=a then 1 else 0
  simp only [rowCount_transpose,colCount_transpose,and_comm]
end
end ElementaryPositivity.ElementaryMatrix

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_GraphRationalModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.NaturalUnitIntervalGraph
variable {n:ℕ} (G:ElementaryPositivity.NaturalUnitIntervalGraph n)

def extendedH (i:ℕ) : ℕ := if hi:i < n then (G.h ⟨i,hi⟩).val else i
end ElementaryPositivity.NaturalUnitIntervalGraph

namespace ElementaryPositivity
structure PhaseLabel (n:ℕ) where
  val:Fin n
  deriving DecidableEq, Fintype

end ElementaryPositivity

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_GraphTriangularEmbedding
attribute [-instance] _root_.OAI.ElementaryPositivity.TriangularDynamics.instAntisymmCellPhaseLE _root_.OAI.ElementaryPositivity.TriangularDynamics.instDecidableRelCellPhaseLE _root_.OAI.ElementaryPositivity.TriangularDynamics.instIsTransCellPhaseLE _root_.OAI.ElementaryPositivity.TriangularDynamics.instTotalCellPhaseLE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open scoped BigOperators
open Classical
noncomputable section

def rankedCell {n:ℕ} (l:Fin n → ℕ) (r:Equiv.Perm (Fin n)) (i:Fin n) :
    Cell (n+1+∑j,l j) :=
  ⟨⟨n+l i,by have H:=Finset.single_le_sum (f:=l) (fun _ _=>Nat.zero_le _) (Finset.mem_univ i); omega⟩,
    ⟨(r i).rev.val,by change (r i).rev.val < n+l i+1; have H: (r i).rev.val < n:=(r i).rev.isLt; omega⟩⟩

end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Histories_GraphCommonHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus WallUnits LatticeExtension LatticeRealization PowerSeries PowerSeriesAdjoint
open scoped BigOperators
open Classical
noncomputable section
variable {n D:ℕ}

def graphVertex (b:Fin n ↪ Cell D) : Fin n ↪ Vertex D (Cell D):=
  ⟨fun i=>Sum.inr (b i),fun _ _ h=>b.injective (Sum.inr.inj h)⟩

end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end


