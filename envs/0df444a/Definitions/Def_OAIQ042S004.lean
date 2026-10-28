-- Prove2me | Definitions.Def_OAIQ042S004
-- name    : OAIQ042S004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T01:35:43.374991+00:00
-- url     : https://prove2.me/theorems/ffaa230a-ea3f-4160-a53d-a67dd69b6479
-- title:
--   Definitions bundle OAIQ042S004 of the split of OpenAI, Critical strip-crossing mass on the honeycomb lattice (result family 237)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CriticalStrip.critical_strip_mass`, carved from OpenAI's openai/math development (OpenAI, *Critical strip-crossing mass on the honeycomb lattice (result family 237)*, OpenAI Math Release, September 26, 2026, result family 237, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 367 declarations of OpenAI's Lean: 111 definitions, 1 instance and 255 theorems. The definitions and types are `OAI.CriticalStrip.Diagram.PartialColumn.twoRows`, `OAI.CriticalStrip.Diagram.ThreeBox.mergeNumerator`, `OAI.CriticalStrip.Diagram.Tile.transposeEquiv`, `OAI.CriticalStrip.Diagram.TriplePosition.MirrorOutside`, `OAI.CriticalStrip.Diagram.TriplePosition.mirrorActive`, `OAI.CriticalStrip.Diagram.TriplePosition.mirrorExterior`, `OAI.CriticalStrip.Diagram.Weights.IsFlat`, `OAI.CriticalStrip.Diagram.archRootExponent`, `OAI.CriticalStrip.Diagram.collisionSubstitution`, `OAI.CriticalStrip.Diagram.copiedNodeWeights`, `OAI.CriticalStrip.Diagram.copyEvaluation`, `OAI.CriticalStrip.Diagram.deformationAngles`, `OAI.CriticalStrip.Diagram.deletionDataFactor`, `OAI.CriticalStrip.Diagram.deletionPerm`, `OAI.CriticalStrip.Diagram.deletionScalarTuple`, `OAI.CriticalStrip.Diagram.doubleSignTwist`, `OAI.CriticalStrip.Diagram.edgeSubstitution`, `OAI.CriticalStrip.Diagram.evalMonomialCharacter`, `OAI.CriticalStrip.Diagram.firstPair`, `OAI.CriticalStrip.Diagram.firstPairDecompose`, `OAI.CriticalStrip.Diagram.firstScalarHom`, `OAI.CriticalStrip.Diagram.horizontalWeights`, `OAI.CriticalStrip.Diagram.identityWeights`, `OAI.CriticalStrip.Diagram.incidentPair`, `OAI.CriticalStrip.Diagram.infinityDenominator`, `OAI.CriticalStrip.Diagram.infinityKernel`, `OAI.CriticalStrip.Diagram.infinityNumerator`, `OAI.CriticalStrip.Diagram.infinityPairEmbed`, `OAI.CriticalStrip.Diagram.inlinePrivate156_tileEast`, `OAI.CriticalStrip.Diagram.inlinePrivate156_tileWest`, `OAI.CriticalStrip.Diagram.insertedNodeWeights`, `OAI.CriticalStrip.Diagram.inverseRowDenominator`, `OAI.CriticalStrip.Diagram.inverseRowNumerator`, `OAI.CriticalStrip.Diagram.lastCosine`, `OAI.CriticalStrip.Diagram.lastFactor`, `OAI.CriticalStrip.Diagram.lastLaurent`, `OAI.CriticalStrip.Diagram.mergeWeights`, `OAI.CriticalStrip.Diagram.nodalHeadL`, `OAI.CriticalStrip.Diagram.nodeSign`, `OAI.CriticalStrip.Diagram.plainKernel` and 71 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/StripMass, in whole or in part: `StripMass_ArchRoots`, `StripMass_AugmentedTail`, `StripMass_Basic`, `StripMass_BlockPfaffian`, `StripMass_BottomPadding`, `StripMass_BoundaryTree`, `StripMass_CauchyMatrices`, `StripMass_CollisionSubstitutions`, `StripMass_CoordinateBoxes`, `StripMass_CramerBounds`, `StripMass_DeficitBounds`, `StripMass_DeformationWeights`, `StripMass_DiagonalFactors`, `StripMass_FirstFlatSpecialization`, `StripMass_FluxWindow`, `StripMass_GraphPath`, `StripMass_HoneycombClip`, `StripMass_InterpolantCovariance`, `StripMass_LastRow`, `StripMass_LaurentBox`, `StripMass_LaurentNumerator`, `StripMass_MirrorExterior`, `StripMass_MonicPositive`, `StripMass_NodalExchange`, `StripMass_NodalNodes`, `StripMass_NodalRegularity`, `StripMass_NodalScalarDeletion`, `StripMass_NodalTorusValue`, `StripMass_PairSelfNode`, `StripMass_PairingDiagrams`, `StripMass_PfaffianConfluentLimit`, `StripMass_PfaffianSupport`, `StripMass_PhaseAlgebra`, `StripMass_PhysicalPorts`, `StripMass_ReflectionFractions`, `StripMass_ResidualParityCoefficients`, `StripMass_RestrictedDiagrams`, `StripMass_ReversedConvergence`, `StripMass_RibbonGlobal`, `StripMass_RibbonLocal`, `StripMass_RightStieltjes`, `StripMass_ScalarBridge`, `StripMass_ScalarDegree`, `StripMass_ScalarDeleteContinuation`, `StripMass_ScalarFlat`, `StripMass_ScalarMergeTrig`, `StripMass_SidePaths`, `StripMass_Specialization`, `StripMass_SpecializationPolynomial`, `StripMass_SwapVacancy`, `StripMass_ThreeBoxSplitPolynomial`, `StripMass_TopPadding`, `StripMass_VacuumClosure`, `StripMass_VacuumDegree`, `StripMass_WeightComparison`.
--
--   **Imports.** It imports the published bundle `Def_CriticalStripMass`; the bundles `OAIQ042S000` and `OAIQ042S001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ042S006`, `OAIQ042S007`, `OAIQ042S008` and `OAIQ042S009`; the statements `OAI.CriticalStrip.HoneycombBranch.physical_stepped_flux`, `OAI.CriticalStrip.criticalStripMass_of_physical_identities`, `OAI.CriticalStrip.homogeneous_arch_coefficient_integral` and `OAI.CriticalStrip.positiveLaw_inverseQuarterSum_growth_upper`; the proofs of `OAI.CriticalStrip.criticalStripMass_of_physical_identities`, `OAI.CriticalStrip.homogeneous_arch_coefficient_integral` and `OAI.CriticalStrip.positiveLaw_inverseQuarterSum_growth_upper`.
-- source:
--   OpenAI, Critical strip-crossing mass on the honeycomb lattice (result family 237), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 237; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Critical-strip-crossing-mass-on-the-honeycomb-lattice-September-26-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/StripMass at commit adc7f12

import Mathlib
import Definitions.Def_CriticalStripMass
import Definitions.Def_OAIQ042S000
import Definitions.Def_OAIQ042S001

section
-- module Solutions.OAIQ042_SS.StripMass_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip

noncomputable section
open scoped BigOperators
open Set MeasureTheory

def density (N : ℕ) (y : Fin N → ℝ) : ℝ :=
  (∏ i, omega (y i)) * ∏ i, ∏ j ∈ Finset.Ioi i, pairKernel (y i) (y j)

def normalizer (N : ℕ) : ℝ := ∫ y in orderedDomain N, density N y

def expectation (N : ℕ) (f : (Fin N → ℝ) → ℝ) : ℝ :=
  (∫ y in orderedDomain N, f y * density N y) / normalizer N

def momentIntegrand (N : ℕ) (x : ℝ) : ℝ :=
  (1 - expectation N (reflectionProduct N x)) * omega x / x



end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_PairingDiagrams
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



 

namespace CriticalStrip.Diagram
noncomputable section
open Finset


def identityWeights {𝕜 : Type*} [Zero 𝕜] [One 𝕜] : Weights 𝕜 := ⟨1,0,0,1,0⟩



end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_BottomPadding
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.tileAdjDecidable _root_.OAI.CriticalStrip.Diagram.tileOccupiedDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open Finset

theorem Tile.vacant_of_three (t : Tile) (h₀ : ¬ t.Occupied 0)
    (h₁ : ¬ t.Occupied 1) (h₂ : ¬ t.Occupied 2) : t = .vacant := by
  cases t <;> simp_all [Tile.Occupied, Tile.Adj, Tile.edges]

theorem Tile.identity_zero_of_south_vacant_east_occupied
    {𝕜 : Type*} [Zero 𝕜] [One 𝕜] (a : Tile) (hs : ¬a.Occupied 0)
    (he : a.Occupied 2) : (identityWeights : Weights 𝕜).tile a = 0 := by
  cases a <;> simp_all [Tile.Occupied, Tile.Adj, Tile.edges,
    identityWeights, Weights.tile]

theorem Tile.deletion_zero_of_south_vacant_west_occupied
    {𝕜 : Type*} [Zero 𝕜] [One 𝕜] (a : Tile) (hs : ¬a.Occupied 0)
    (hw : a.Occupied 1) : (deletionWeights : Weights 𝕜).tile a = 0 := by
  cases a <;> simp_all [Tile.Occupied, Tile.Adj, Tile.edges,
    deletionWeights, Weights.tile]


theorem vertexCastSucc_injective {n : ℕ} : Function.Injective (@vertexCastSucc n) := by
  intro v w h
  apply Prod.ext
  · exact Fin.castSucc_injective n (congrArg (fun v : Vertex (n+1) => v.1) h)
  · exact congrArg (fun v : Vertex (n+1) => v.2) h

 
theorem wiring_padTop_last {n : ℕ} (p : Pairing n) (t : Configuration n)
    (ht : ∀ i, i.val+1=n → ¬(t i).Occupied 3)
    (a : Fin 4) (w : Vertex (n+1)) :
    ¬Wiring p.padTop t.padTop (Fin.last n,a) w := by
  intro h
  rcases h with ⟨hw,hh⟩ | hh | ⟨_,_,hv,_⟩ | ⟨_,_,hv,ho⟩
  · simp at hh
  · exact p.padTop_not_adj_last w.1 hh.2.2
  · have hw := w.1.isLt
    change n+1 = w.1.val at hv
    omega
  · rcases w with ⟨j,b⟩
    induction j using Fin.lastCases with
    | last => simp at ho
    | cast j => exact ht j hv (by simpa using ho)

theorem wiring_padTop_last_right {n : ℕ} (p : Pairing n) (t : Configuration n)
    (ht : ∀ i, i.val+1=n → ¬(t i).Occupied 3)
    (v : Vertex (n+1)) (b : Fin 4) :
    ¬Wiring p.padTop t.padTop v (Fin.last n,b) :=
  fun h => wiring_padTop_last p t ht b v (wiring_symm h)

theorem reach_padTop_image {n : ℕ} (p : Pairing n) (t : Configuration n)
    (ht : ∀ i, i.val+1=n → ¬(t i).Occupied 3)
    {v : Vertex n} {w : Vertex (n+1)} (h : Reach p.padTop t.padTop (vertexCastSucc v) w) :
    ∃ z, w = vertexCastSucc z ∧ Reach p t v z := by
  induction h with
  | refl => exact ⟨v,rfl,Relation.ReflTransGen.refl⟩
  | @tail w z _ hwz ih =>
    obtain ⟨w',rfl,hw'⟩ := ih
    rcases z with ⟨j,b⟩
    induction j using Fin.lastCases with
    | last => exact (wiring_padTop_last_right p t ht _ b hwz).elim
    | cast j =>
      exact ⟨(j,b),rfl,hw'.tail ((wiring_padTop_iff p t _ _).1 hwz)⟩

theorem reach_padTop_iff {n : ℕ} (p : Pairing n) (t : Configuration n)
    (ht : ∀ i, i.val+1=n → ¬(t i).Occupied 3) (v w : Vertex n) :
    Reach p.padTop t.padTop (vertexCastSucc v) (vertexCastSucc w) ↔ Reach p t v w := by
  constructor
  · intro h
    obtain ⟨z,hz,hz'⟩ := reach_padTop_image p t ht h
    have := vertexCastSucc_injective hz
    simpa only [this] using hz'
  · exact Relation.ReflTransGen.lift vertexCastSucc
      (fun a b h => (wiring_padTop_iff p t a b).2 h) _ _

theorem reach_padTop_last_iff {n : ℕ} (p : Pairing n) (t : Configuration n)
    (ht : ∀ i, i.val+1=n → ¬(t i).Occupied 3) (a : Fin 4) (w : Vertex (n+1)) :
    Reach p.padTop t.padTop (Fin.last n,a) w ↔ w = (Fin.last n,a) :=
  Relation.reflTransGen_iff_eq (wiring_padTop_last p t ht a)

theorem reach_padTop_last_right_iff {n : ℕ} (p : Pairing n) (t : Configuration n)
    (ht : ∀ i, i.val+1=n → ¬(t i).Occupied 3) (v : Vertex (n+1)) (b : Fin 4) :
    Reach p.padTop t.padTop v (Fin.last n,b) ↔ v = (Fin.last n,b) := by
  constructor
  · intro h
    exact (reach_padTop_last_iff p t ht b v).1 (reach_symm h)
  · rintro rfl; exact Relation.ReflTransGen.refl

 
end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_TopPadding
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.tileAdjDecidable _root_.OAI.CriticalStrip.Diagram.tileOccupiedDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open Finset

theorem Tile.vacant_of_three_top (t : Tile) (h₃ : ¬ t.Occupied 3)
    (h₁ : ¬ t.Occupied 1) (h₂ : ¬ t.Occupied 2) : t = .vacant := by
  cases t <;> simp_all [Tile.Occupied, Tile.Adj, Tile.edges]


theorem Tile.deletion_zero_of_north_vacant_east_occupied
    {𝕜 : Type*} [Zero 𝕜] [One 𝕜] (a : Tile) (hn : ¬a.Occupied 3)
    (he : a.Occupied 2) : (deletionWeights : Weights 𝕜).tile a = 0 := by
  cases a <;> simp_all [Tile.Occupied, Tile.Adj, Tile.edges,
    deletionWeights, Weights.tile]

theorem Tile.identity_zero_of_north_vacant_west_occupied
    {𝕜 : Type*} [Zero 𝕜] [One 𝕜] (a : Tile) (hn : ¬a.Occupied 3)
    (hw : a.Occupied 1) : (identityWeights : Weights 𝕜).tile a = 0 := by
  cases a <;> simp_all [Tile.Occupied, Tile.Adj, Tile.edges,
    identityWeights, Weights.tile]

def Weights.IsFlat {𝕜 : Type*} [Zero 𝕜] [One 𝕜] (w : Weights 𝕜) : Prop :=
  w = identityWeights ∨ w = deletionWeights



theorem inlinePrivate0_sin_two_lambda : Real.sin (2*lambda) = Real.cos (2*lambda) := by
  rw [← Real.sin_pi_div_two_sub]
  congr 1
  unfold lambda
  ring

end

end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_RestrictedDiagrams
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.tileAdjDecidable _root_.OAI.CriticalStrip.Diagram.tileOccupiedDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section

def lastCosine (n : ℕ) : Laurent (n+1) :=
  AddMonoidAlgebra.single (lastExponent n 2) (phase^(-3 : ℤ)/2) +
    AddMonoidAlgebra.single (lastExponent n (-2)) (phase^3/2)

theorem rowNumerator_flatEval {n : ℕ} (i : Fin n) (t : Tile) :
    flatEval n (rowNumerator i t) =
      flatEval n (rowDenominator i) * (deletionWeights : Weights ℂ).tile t := by
  cases t <;> simp only [rowNumerator, map_mul, flatEval_constant,
    flatEval_sine_phase, flatEval_rowDenominator, deletionWeights, Weights.tile,
    Int.cast_ofNat, Int.cast_zero, zero_mul, Real.sin_zero, Complex.ofReal_zero,
    mul_zero, mul_one]
  all_goals try rw [d, ← inlinePrivate0_sin_two_lambda]
  all_goals ring

end

end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_LastRow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



 

namespace CriticalStrip.Diagram
noncomputable section
open Finset



def lastFactor {K : Type*} [CommRing K] {n : ℕ}
    (d c C : K) (p q : Pairing (n+1)) : Polynomial K := by
  classical
  exact if q.Occupied (Fin.last n) then
    if p.Occupied (Fin.last n) then Polynomial.X - Polynomial.C c
    else Polynomial.C (2*d)
  else if p.Occupied (Fin.last n) then Polynomial.C d * (Polynomial.X - Polynomial.C c)
    else Polynomial.X + Polynomial.C C



end





end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_PfaffianSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open Finset



theorem prod_upperPair {R : Type*} [CommMonoid R] {n : ℕ}
    (D : Fin n → Fin n → R) :
    (∏ e : UpperPair n, D e.val.1 e.val.2) =
      ∏ i, ∏ j ∈ Finset.Ioi i, D i j := by
  rw [← Finset.prod_subtype (Finset.univ.filter (fun ij : Fin n × Fin n => ij.1 < ij.2))
    (by simp) (fun ij : Fin n × Fin n => D ij.1 ij.2), Finset.prod_filter]
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro i _
  have h : Finset.Ioi i = Finset.univ.filter (fun j => i < j) := by ext j; simp
  rw [h, Finset.prod_filter]

 
def upperPairEmbed {n m : ℕ} (h : n ≤ m) (e : UpperPair n) : UpperPair m :=
  ⟨(e.val.1.castLE h,e.val.2.castLE h),e.property⟩

theorem upperPairEmbed_injective {n m : ℕ} (h : n ≤ m) :
    Function.Injective (upperPairEmbed h) := by
  intro e f hef
  apply Subtype.ext
  have hv := congrArg Subtype.val hef
  apply Prod.ext
  · apply Fin.ext
    exact congrArg (fun e : Fin m × Fin m => e.1.val) hv
  · apply Fin.ext
    exact congrArg (fun e : Fin m × Fin m => e.2.val) hv







theorem product_augmentedDenominator {R : Type*} [CommRing R] {n : ℕ}
    (dd : R) (a : Fin n → R) :
    (∏ e : UpperPair (n+n%2), augmentedDenominator dd a e.val.1 e.val.2) =
      ∏ i, ∏ j ∈ Finset.Ioi i, discriminant dd (a i) (a j) := by
  let hn : n ≤ n+n%2 := Nat.le_add_right _ _
  rw [← prod_upperPair]
  symm
  apply Fintype.prod_of_injective (upperPairEmbed hn) (upperPairEmbed_injective hn)
  · intro e he
    unfold augmentedDenominator
    split_ifs with hi hj
    · exfalso
      apply he
      refine ⟨⟨(⟨e.val.1.val,hi⟩,⟨e.val.2.val,hj⟩),e.property⟩,?_⟩
      apply Subtype.ext
      exact Prod.ext (Fin.ext rfl) (Fin.ext rfl)
    · rfl
    · rfl
  · intro e
    simp [upperPairEmbed, augmentedDenominator, e.val.1.isLt, e.val.2.isLt]



end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_DiagonalFactors
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.spectralFieldCharZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open Finset








def sourceVandermonde {R : Type*} [CommRing R] {n : ℕ} (a : Fin n → R) : R :=
  ∏ e : UpperPair n, (a e.val.1 - a e.val.2)

theorem sourceVandermonde_ne_zero {R : Type*} [CommRing R] [IsDomain R] {n : ℕ}
    (a : Fin n → R) (ha : Function.Injective a) : sourceVandermonde a ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro e _
  exact sub_ne_zero.mpr (ha.ne (ne_of_lt e.property))

theorem sourceVandermonde_eq_det {R : Type*} [CommRing R] {n : ℕ} (a : Fin n → R) :
    sourceVandermonde a = Matrix.det (Matrix.vandermonde (fun i => -a i)) := by
  rw [Matrix.det_vandermonde, sourceVandermonde, prod_upperPair (fun i j => a i - a j)]
  simp only [neg_sub_neg]

theorem sourceVandermonde_reindex {R : Type*} [CommRing R] {n : ℕ}
    (a : Fin n → R) (σ : Equiv.Perm (Fin n)) :
    sourceVandermonde (a ∘ σ) = (Equiv.Perm.sign σ : ℤ) * sourceVandermonde a := by
  rw [sourceVandermonde_eq_det, sourceVandermonde_eq_det]
  have hm : Matrix.vandermonde (fun i => -(a ∘ σ) i) =
      (Matrix.vandermonde (fun i => -a i)).submatrix σ id := by
    rfl
  rw [hm, Matrix.det_permute]

theorem map_sourceVandermonde {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (f : R →+* S) (a : Fin n → R) :
    f (sourceVandermonde a) = sourceVandermonde (fun i => f (a i)) := by
  simp [sourceVandermonde, map_prod]



end





noncomputable section
open scoped LaurentPolynomial


lemma peelLaurent_injective {n : ℕ} (i : Fin (n+1)) : Function.Injective (peelLaurent i) :=
  (AddMonoidAlgebra.map_injective _ (IsFractionRing.injective (SpectralRing n) (SpectralField n))).comp
    (peelLaurentEquiv i).injective

instance peeledRingIsDomain (n : ℕ) : IsDomain (LaurentPolynomial (SpectralField n)) :=
  AddMonoidAlgebra.instIsDomainOfIsCancelAddOfUniqueSums

end







end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_LaurentBox
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram





noncomputable section
open Finset

theorem pairFirst_injective (n : ℕ) : Function.Injective (pairFirst n) := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  dsimp [pairFirst] at this
  omega

theorem pairSecond_injective (n : ℕ) : Function.Injective (pairSecond n) := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  dsimp [pairSecond] at this
  omega

theorem upperPair_incident_iff {n : ℕ} (i j v : Fin n) (h : i ≠ j) :
    ((upperPair i j h).val.1 = v ∨ (upperPair i j h).val.2 = v) ↔ i = v ∨ j = v := by
  unfold upperPair
  split_ifs <;> simp [or_comm]

theorem pairIndex_unique {n : ℕ} (σ : Equiv.Perm (Fin n))
    (i j : Fin (n/2)) (v : Fin n)
    (hi : σ (pairFirst n i) = v ∨ σ (pairSecond n i) = v)
    (hj : σ (pairFirst n j) = v ∨ σ (pairSecond n j) = v) : i = j := by
  rcases hi with hi | hi <;> rcases hj with hj | hj
  · exact pairFirst_injective n (σ.injective (hi.trans hj.symm))
  · exact False.elim (pairFirst_ne_pairSecond i j (σ.injective (hi.trans hj.symm)))
  · exact False.elim (pairFirst_ne_pairSecond j i (σ.injective (hj.trans hi.symm)))
  · exact pairSecond_injective n (σ.injective (hi.trans hj.symm))

 
theorem selectedPairs_incident_unique {n : ℕ} (σ : Equiv.Perm (Fin n))
    (e f : UpperPair n) (he : e ∈ selectedPairs σ) (hf : f ∈ selectedPairs σ)
    (v : Fin n) (hev : e.val.1 = v ∨ e.val.2 = v) (hfv : f.val.1 = v ∨ f.val.2 = v) :
    e = f := by
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hf
  apply congrArg (permutationPair σ)
  apply pairIndex_unique σ i j v
  · exact (upperPair_incident_iff _ _ _ _).mp hev
  · exact (upperPair_incident_iff _ _ _ _).mp hfv

 
theorem pairIndex_cover {n : ℕ} (hn : n % 2 = 0) (σ : Equiv.Perm (Fin n)) (v : Fin n) :
    ∃ i : Fin (n/2), σ (pairFirst n i) = v ∨ σ (pairSecond n i) = v := by
  let p := σ.symm v
  let i : Fin (n/2) := ⟨p.val/2, by have := p.isLt; omega⟩
  refine ⟨i,?_⟩
  by_cases hp : p.val%2 = 0
  · left
    have h : pairFirst n i = p := by apply Fin.ext; dsimp [pairFirst,i]; omega
    rw [h]
    exact σ.apply_symm_apply v
  · right
    have h : pairSecond n i = p := by apply Fin.ext; dsimp [pairSecond,i]; omega
    rw [h]
    exact σ.apply_symm_apply v

def firstPair (m : ℕ) : UpperPair (2*(m+1)) := ⟨(0,1), by
  change (0 : Fin (2*m+2)) < 1
  exact Fin.zero_lt_one⟩

theorem firstPair_eq_upperPair (m : ℕ) :
    firstPair m = upperPair 0 1 (by exact ne_of_lt (firstPair m).property) := by
  have h : (0 : Fin (2*(m+1))) < 1 := (firstPair m).property
  simp only [upperPair, h, dite_true, firstPair]



theorem repairFirstDenominator_compl {R : Type*} [One R] {m : ℕ}
    (D : Matrix (Fin (2*(m+1))) (Fin (2*(m+1))) R)
    (σ : Equiv.Perm (Fin (2*(m+1)))) (hσ : firstPair m ∈ selectedPairs σ)
    (e : UpperPair (2*(m+1))) (he : e ∈ (selectedPairs σ)ᶜ) :
    repairFirstDenominator D e.val.1 e.val.2 = D e.val.1 e.val.2 := by
  unfold repairFirstDenominator
  rw [ite_eq_right]
  rintro (h | h)
  · have heq : e = firstPair m := Subtype.ext (Prod.ext h.1 h.2)
    exact (Finset.mem_compl.mp he) (heq.symm ▸ hσ)
  · have := e.property
    rw [h.1,h.2] at this
    exact (not_lt_of_ge (firstPair m).property.le) this

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_BlockPfaffian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open Finset








theorem pfaffian_eq_block {K : Type*} [Field K] {m : ℕ}
    (M : Matrix (Fin (2*m)) (Fin (2*m)) K) :
    pfaffian M = (2^m * (Nat.factorial m : K))⁻¹ * ∑ σ, blockSummand M σ := by
  have hm : 2*m/2 = m := by omega
  unfold pfaffian blockSummand
  congr 1
  · rw [hm]
  · apply Finset.sum_congr rfl
    intro σ _
    congr 1
    let e : Fin (2*m/2) ≃ Fin m := finCongr hm
    apply Fintype.prod_equiv e
    intro i
    congr 2

 

theorem pfaffian_isolated {K : Type*} [Field K] [CharZero K] {m : ℕ}
    (M : Matrix (Fin (2*(m+1))) (Fin (2*(m+1))) K)
    (hM : ∀ i j, M j i = -M i j) (hzero : ∀ j, j ≠ 1 → M 0 j = 0) :
    pfaffian M = M 0 1 * pfaffian (fun i j : Fin (2*m) => M i.succ.succ j.succ.succ) := by
  rw [pfaffian_eq_block M, blockSummand_sum_isolated M hM hzero,
    pfaffian_eq_block (m := m) (fun i j : Fin (2*m) => M i.succ.succ j.succ.succ)]
  rw [pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have htwo : (2 : K) ≠ 0 := by norm_num
  have hm : (m+1 : K) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  have hf : (Nat.factorial m : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  field_simp



theorem pfaffian_firstRow_add {K : Type*} [Field K] {m : ℕ}
    (M A B : Matrix (Fin (2*(m+1))) (Fin (2*(m+1))) K)
    (hM : ∀ i j, M j i = -M i j)
    (hA : ∀ i j, A j i = -A i j)
    (hB : ∀ i j, B j i = -B i j)
    (hrow : ∀ j, M 0 j = A 0 j + B 0 j)
    (hrestA : ∀ i j : Fin (2*m+1), M i.succ j.succ = A i.succ j.succ)
    (hrestB : ∀ i j : Fin (2*m+1), M i.succ j.succ = B i.succ j.succ) :
    pfaffian M = pfaffian A + pfaffian B := by
  rw [pfaffian_eq_block, pfaffian_eq_block, pfaffian_eq_block,
    blockSummand_sum_fixedZero M hM, blockSummand_sum_fixedZero A hA,
    blockSummand_sum_fixedZero B hB]
  rw [← mul_add, ← mul_add, ← Finset.sum_add_distrib]
  congr 2
  apply Finset.sum_congr rfl
  intro τ _
  simp only [blockSummand_fixZero, hrow]
  have hprodA : (∏ i : Fin m, M (τ (blockFirst i).succ).succ (τ (blockSecond i).succ).succ) =
      ∏ i : Fin m, A (τ (blockFirst i).succ).succ (τ (blockSecond i).succ).succ :=
    Finset.prod_congr rfl (fun _ _ => hrestA _ _)
  have hprodB : (∏ i : Fin m, M (τ (blockFirst i).succ).succ (τ (blockSecond i).succ).succ) =
      ∏ i : Fin m, B (τ (blockFirst i).succ).succ (τ (blockSecond i).succ).succ :=
    Finset.prod_congr rfl (fun _ _ => hrestB _ _)
  rw [← hprodA, ← hprodB]
  ring


 

 


 

theorem clearedPfaffianTerm_of_missing_pair {R : Type*} [CommRing R] {m : ℕ}
    (N D : Matrix (Fin (2*(m+1))) (Fin (2*(m+1))) R)
    (hD : D 0 1 = 0) (σ : Equiv.Perm (Fin (2*(m+1))))
    (hσ : firstPair m ∉ selectedPairs σ) : clearedPfaffianTerm N D σ = 0 := by
  unfold clearedPfaffianTerm
  have hz : (∏ e ∈ (selectedPairs σ)ᶜ, D e.val.1 e.val.2) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_compl.mpr hσ)
    exact hD
  rw [hz, mul_zero]

 
theorem isolateFirstNumerator_prod_of_missing_pair {R : Type*} [CommRing R] {m : ℕ}
    (N : Matrix (Fin (2*(m+1))) (Fin (2*(m+1))) R)
    (σ : Equiv.Perm (Fin (2*(m+1)))) (hσ : firstPair m ∉ selectedPairs σ) :
    (∏ i : Fin (2*(m+1)/2),
      isolateFirstNumerator N (σ (pairFirst _ i)) (σ (pairSecond _ i))) = 0 := by
  obtain ⟨i,hi⟩ := pairIndex_cover (n := 2*(m+1)) (by omega) σ 0
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  have hpair : permutationPair σ i ≠ firstPair m := by
    intro he
    apply hσ
    exact he ▸ Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  unfold isolateFirstNumerator
  rw [ite_eq_left]
  rcases hi with hi | hi
  · left
    refine ⟨hi,?_⟩
    intro hj
    apply hpair
    unfold permutationPair
    simp only [hi,hj]
    exact (firstPair_eq_upperPair m).symm
  · right
    refine ⟨hi,?_⟩
    intro hj
    apply hpair
    unfold permutationPair upperPair
    have h : ¬ (1 : Fin (2*(m+1))) < 0 := by exact not_lt_of_ge (firstPair m).property.le
    simp only [hi,hj,h,dite_false,firstPair]








def firstPairDecompose (n : ℕ) : UpperPair (n+1) ≃ Fin n ⊕ UpperPair n where
  toFun e := if hi : e.val.1 = 0 then
      Sum.inl (e.val.2.pred (ne_of_gt (hi ▸ e.property)))
    else
      let hj : e.val.2 ≠ 0 := by
        intro hj; have := e.property; simp [hj] at this
      Sum.inr ⟨(e.val.1.pred hi,e.val.2.pred hj),
        (Fin.pred_lt_pred_iff (ha := hi) (hb := hj)).mpr e.property⟩
  invFun e := match e with
    | Sum.inl j => ⟨(0,j.succ),Fin.succ_pos _⟩
    | Sum.inr e => ⟨(e.val.1.succ,e.val.2.succ), Fin.succ_lt_succ_iff.mpr e.property⟩
  left_inv e := by
    dsimp
    split_ifs with hi
    · apply Subtype.ext
      apply Prod.ext hi.symm
      simp only [Fin.succ_pred]
    · apply Subtype.ext
      apply Prod.ext <;> simp only [Fin.succ_pred]
  right_inv e := by
    cases e with
    | inl j => simp
    | inr e => simp

 
theorem prod_upperPair_succ {R : Type*} [CommMonoid R] {n : ℕ}
    (D : Fin (n+1) → Fin (n+1) → R) :
    (∏ e : UpperPair (n+1), D e.val.1 e.val.2) =
      (∏ j : Fin n, D 0 j.succ) *
        ∏ e : UpperPair n, D e.val.1.succ e.val.2.succ := by
  calc
    _ = ∏ e : Fin n ⊕ UpperPair n,
        D ((firstPairDecompose n).symm e).val.1 ((firstPairDecompose n).symm e).val.2 :=
      (Fintype.prod_equiv (firstPairDecompose n).symm _ _ (fun _ => rfl)).symm
    _ = _ := by rw [Fintype.prod_sum_type]; rfl

theorem prod_upperPair_two {R : Type*} [CommMonoid R] {n : ℕ}
    (D : Fin (n+2) → Fin (n+2) → R) :
    (∏ e : UpperPair (n+2), D e.val.1 e.val.2) =
      D 0 1 * (∏ j : Fin n, D 0 j.succ.succ * D 1 j.succ.succ) *
        ∏ e : UpperPair n, D e.val.1.succ.succ e.val.2.succ.succ := by
  rw [prod_upperPair_succ D, Fin.prod_univ_succ,
    prod_upperPair_succ (fun i j : Fin (n+1) => D i.succ j.succ),
    Finset.prod_mul_distrib]
  simp only [Fin.succ_zero_eq_one]
  ac_rfl


 

 


theorem pfaffian_cast {K : Type*} [Field K] {n m : ℕ} (h : n = m)
    (M : Matrix (Fin n) (Fin n) K) :
    pfaffian (fun i j : Fin m => M (i.cast h.symm) (j.cast h.symm)) = pfaffian M := by
  subst m
  rfl

theorem clearedPfaffian_cast {R : Type*} [CommRing R] {n m : ℕ} (h : n = m)
    (t : R) (N D : Matrix (Fin n) (Fin n) R) :
    clearedPfaffian t (fun i j : Fin m => N (i.cast h.symm) (j.cast h.symm))
      (fun i j : Fin m => D (i.cast h.symm) (j.cast h.symm)) = clearedPfaffian t N D := by
  subst m
  rfl



end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_AugmentedTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open Finset

theorem augmentedNumerator_skew {R : Type*} [CommRing R] {n : ℕ}
    (rr : R) (a : Fin n → R) :
    ∀ i j, augmentedNumerator rr a j i = -augmentedNumerator rr a i j := by
  intro i j
  unfold augmentedNumerator
  split_ifs <;> ring

@[simp] theorem augmentedNumerator_two_zero_one {R : Type*} [CommRing R] {n : ℕ}
    (rr x y : R) (a : Fin n → R) :
    augmentedNumerator rr (twoCons x y a) 0 1 = (x-y)*(x+y+rr) := by
  simp [augmentedNumerator, Nat.mod_eq_of_lt (by omega : 1 < n+2+n%2)]

@[simp] theorem augmentedDenominator_two_zero_one {R : Type*} [CommRing R] {n : ℕ}
    (dd x y : R) (a : Fin n → R) :
    augmentedDenominator dd (twoCons x y a) 0 1 = discriminant dd x y := by
  simp [augmentedDenominator, Nat.mod_eq_of_lt (by omega : 1 < n+2+n%2)]

theorem augmentedNumerator_two_tail {R : Type*} [CommRing R] {n : ℕ}
    (rr x y : R) (a : Fin n → R) (i j : Fin (n+n%2)) :
    augmentedNumerator rr (twoCons x y a)
        (augmentTwoIndex n i.succ.succ) (augmentTwoIndex n j.succ.succ) =
      augmentedNumerator rr a i j := by
  simp only [augmentedNumerator, augmentTwoIndex_val, Fin.val_succ, Nat.add_assoc,
    Nat.reduceAdd, Nat.add_lt_add_iff_right]
  split_ifs <;> rfl

theorem augmentedDenominator_two_tail {R : Type*} [CommRing R] {n : ℕ}
    (dd x y : R) (a : Fin n → R) (i j : Fin (n+n%2)) :
    augmentedDenominator dd (twoCons x y a)
        (augmentTwoIndex n i.succ.succ) (augmentTwoIndex n j.succ.succ) =
      augmentedDenominator dd a i j := by
  simp only [augmentedDenominator, augmentTwoIndex_val, Fin.val_succ, Nat.add_assoc,
    Nat.reduceAdd, Nat.add_lt_add_iff_right]
  split_ifs <;> rfl


theorem augmentedDenominator_two_zero_tail {R : Type*} [CommRing R] {n : ℕ}
    (dd x y : R) (a : Fin n → R) (i : Fin (n+n%2)) :
    augmentedDenominator dd (twoCons x y a) 0 (augmentTwoIndex n i.succ.succ) =
      if hi : i.val < n then discriminant dd x (a ⟨i.val,hi⟩) else 1 := by
  simp only [augmentedDenominator, Fin.val_zero, augmentTwoIndex_val, Fin.val_succ,
    Nat.add_assoc, Nat.reduceAdd, Nat.add_lt_add_iff_right]
  rw [dite_eq_left (by omega : 0 < n+2)]
  split_ifs <;> rfl

theorem augmentedDenominator_two_one_tail {R : Type*} [CommRing R] {n : ℕ}
    (dd x y : R) (a : Fin n → R) (i : Fin (n+n%2)) :
    augmentedDenominator dd (twoCons x y a) 1 (augmentTwoIndex n i.succ.succ) =
      if hi : i.val < n then discriminant dd y (a ⟨i.val,hi⟩) else 1 := by
  have hv : (1 : Fin ((n+2)+(n+2)%2)).val = 1 := by
    change 1 % ((n+2)+(n+2)%2) = 1
    exact Nat.mod_eq_of_lt (by omega)
  simp only [augmentedDenominator, hv, augmentTwoIndex_val, Fin.val_succ,
    Nat.add_assoc, Nat.reduceAdd, Nat.add_lt_add_iff_right]
  rw [dite_eq_left (by omega : 1 < n+2)]
  split_ifs <;> rfl

theorem augmentedDenominator_two_cross {R : Type*} [CommRing R] {n : ℕ}
    (dd x y : R) (a : Fin n → R) :
    (∏ i : Fin (n+n%2),
      augmentedDenominator dd (twoCons x y a) 0 (augmentTwoIndex n i.succ.succ) *
      augmentedDenominator dd (twoCons x y a) 1 (augmentTwoIndex n i.succ.succ)) =
      ∏ i : Fin n, discriminant dd x (a i) * discriminant dd y (a i) := by
  simp only [augmentedDenominator_two_zero_tail, augmentedDenominator_two_one_tail]
  have he : (fun i : Fin (n+n%2) =>
      (if hi : i.val < n then discriminant dd x (a ⟨i.val,hi⟩) else 1) *
      (if hi : i.val < n then discriminant dd y (a ⟨i.val,hi⟩) else 1)) =
      (fun i : Fin (n+n%2) => if hi : i.val < n then
        discriminant dd x (a ⟨i.val,hi⟩) * discriminant dd y (a ⟨i.val,hi⟩) else 1) := by
    funext i
    split_ifs <;> simp
  rw [he]
  exact prod_pad_one (n := n) (m := n+n%2) (Nat.le_add_right _ _)
    (fun i => discriminant dd x (a i) * discriminant dd y (a i))


 

 


 

theorem scalarNumerator_eval_cleared {K : Type*} [Field K] (f : ℂ →+* K)
    (n : ℕ) (dd rr : ℂ) (a : Fin n → K) :
    MvPolynomial.eval₂Hom f a (scalarNumerator n dd rr) =
      clearedPfaffian (2^((n+n%2)/2) * (Nat.factorial ((n+n%2)/2) : K))⁻¹
        (augmentedNumerator (f rr) a) (augmentedDenominator (f dd) a) := by
  rw [scalarNumerator, map_clearedPfaffian, map_augmentedNumerator, map_augmentedDenominator]
  simp only [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X',
    map_inv₀, map_mul, map_pow, map_ofNat, map_natCast]







theorem sourceVandermonde_twoCons {R : Type*} [CommRing R] {n : ℕ}
    (x y : R) (a : Fin n → R) :
    sourceVandermonde (twoCons x y a) =
      (x-y) * (∏ i : Fin n, (x-a i)*(y-a i)) * sourceVandermonde a := by
  unfold sourceVandermonde
  apply Eq.trans (prod_upperPair_two (fun i j => twoCons x y a i - twoCons x y a j))
  simp only [twoCons_zero,twoCons_one,twoCons_succ_succ]



end

 

 

noncomputable section


theorem discriminant_cosine_roots (w z : ℝ) :
    discriminant d (Real.cos w) z =
      (z-Real.cos (w-6*lambda))*(z-Real.cos (w+6*lambda)) := by
  rw [Real.cos_sub,Real.cos_add,cos_six_lambda,sin_six_lambda]
  unfold discriminant
  have hw := Real.sin_sq_add_cos_sq w
  nlinarith [sq_nonneg (Real.cos w),d_sq]

 
theorem discriminant_cosine_roots_complex (w : ℝ) (z : ℂ) :
    discriminant (d:ℂ) (Real.cos w) z =
      (z-(Real.cos (w-6*lambda):ℂ))*(z-(Real.cos (w+6*lambda):ℂ)) := by
  have hs : (Real.cos (w-6*lambda):ℂ) + (Real.cos (w+6*lambda):ℂ) =
      -2*(d:ℂ)*(Real.cos w:ℂ) := by
    rw [Real.cos_sub,Real.cos_add,cos_six_lambda,sin_six_lambda]
    push_cast
    ring
  have hp : (Real.cos (w-6*lambda):ℂ)*(Real.cos (w+6*lambda):ℂ) =
      (Real.cos w:ℂ)^2-(d:ℂ)^2 := by
    have h := discriminant_cosine_roots w 0
    have hr : Real.cos (w-6*lambda)*Real.cos (w+6*lambda) = Real.cos w^2-d^2 := by
      simpa [discriminant] using h.symm
    exact_mod_cast hr
  unfold discriminant
  linear_combination z*hs-hp






open Finset
open scoped Classical



end





end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_NodalNodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section


theorem twice_variableExponent_ne_neg {n : ℕ} (i j : Fin n) :
    (2 : ℤ) • variableExponent i ≠ -((2 : ℤ) • variableExponent j) := by
  intro h
  have hi := congrFun h i
  by_cases hij : i = j
  · subst j
    simp [variableExponent] at hi
  · simp [variableExponent, eq_comm, hij] at hi

theorem twice_variableExponent_injective {n : ℕ} :
    Function.Injective (fun i : Fin n => (2 : ℤ) • variableExponent i) := by
  intro i j h
  by_contra hij
  have hi := congrFun h i
  simp [variableExponent, eq_comm, hij] at hi

theorem cosineL_two_injective {n : ℕ} (z : ℂ) (hz : z ≠ 0) :
    Function.Injective (fun i : Fin n => cosineL ((2 : ℤ) • variableExponent i) z) := by
  intro i j h
  by_contra hij
  have he : (2 : ℤ) • variableExponent i ≠ (2 : ℤ) • variableExponent j :=
    fun h => hij (twice_variableExponent_injective h)
  have hh := congrArg (fun f : Laurent n => f.coeff ((2 : ℤ) • variableExponent i)) h
  simp only [cosineL, monomialL, AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_single,
    Finsupp.add_apply, Finsupp.single_apply] at hh
  simp only [ite_eq_right (twice_variableExponent_ne_neg i i).symm,
    ite_eq_right he.symm, ite_eq_right (twice_variableExponent_ne_neg i j).symm,
    add_zero] at hh
  exact hz ((div_eq_zero_iff).mp hh |>.resolve_right (by norm_num))

theorem deletionBeta_injective (n : ℕ) : Function.Injective (@deletionBeta n) := by
  intro i j h
  rw [deletionBeta_laurent, deletionBeta_laurent] at h
  exact cosineL_two_injective _ (pow_ne_zero _ phase_ne_zero)
    (IsFractionRing.injective (SpectralRing n) (SpectralField n) h)

theorem deletionNode_sine_ne_zero {n : ℕ} (i : Fin n) : torusSin (deletionNode i) ≠ 0 := by
  have hs : evalLaurent (sineL (variableExponent i) (phase^3)) = torusSin (deletionNode i) := by
    rw [evalLaurent, map_sine_variable_nat]
    congr 1
    exact mul_comm ..
  rw [← hs]
  apply (IsFractionRing.to_map_eq_zero_iff.not).2
  intro he
  have hz := congrArg (flatEval n) he
  have hflat : flatEval n (sineL (variableExponent i) (phase^3)) =
      (Real.sin (3*lambda) : ℂ) := by
    simpa only [zpow_ofNat, Int.cast_ofNat] using flatEval_sine_phase (variableExponent i) 3
  rw [hflat, map_zero] at hz
  have hd := flatEval_rowDenominator_ne_zero i
  rw [flatEval_rowDenominator, hz, zero_mul] at hd
  exact hd rfl


 

 

open scoped LaurentPolynomial Classical

lemma variableExponent_ne_neg {n : ℕ} (i : Fin n) : variableExponent i≠-variableExponent i := by
  intro h
  have hh:=congrFun h i
  simp [variableExponent] at hh

lemma collisionRoots_injective {n : ℕ} (j : Fin n) :
    Function.Injective (cosineCollisionRoots (constantUnit n (phase^3) (pow_ne_zero _ phase_ne_zero)) (variableUnit j)) := by
  intro k l h
  have hp:=congrArg (fun v : (Laurent n)ˣ => (v:Laurent n).coeff (variableExponent j)) h
  have hn:=congrArg (fun v : (Laurent n)ˣ => (v:Laurent n).coeff (-variableExponent j)) h
  fin_cases k <;> fin_cases l <;> try rfl
  all_goals dsimp [cosineCollisionRoots,constantUnit,variableUnit,monomialUnit] at hp hn
  all_goals try simp only [monomialL_mul,zero_add,mul_one,neg_zero,inv_one] at hp hn
  all_goals simp [monomialL,variableExponent_ne_neg j,(variableExponent_ne_neg j).symm] at hp hn
  all_goals try norm_num at hp
  all_goals exfalso; apply inv_ne_zero (pow_ne_zero 3 phase_ne_zero)
  all_goals first | linear_combination hn / 2 | linear_combination -hn / 2

lemma peel_betaL_self {n : ℕ} (i : Fin (n+1)) :
    peelLaurentEquiv i (betaL i)=
      LaurentPolynomial.C (constantL n (phase^3/2))*LaurentPolynomial.T 2+
      LaurentPolynomial.C (constantL n ((phase^3)⁻¹/2))*LaurentPolynomial.T (-2) := by
  have hrem:Fin.removeNth i ((2:ℤ) • variableExponent i)=0 := by
    funext j
    simp [Fin.removeNth,variableExponent,Fin.succAbove_ne]
  have hval:((2:ℤ) • variableExponent i) i=2 := by simp [variableExponent]
  simp only [betaL,cosineL,map_add,peelLaurentEquiv_monomial,hval,hrem,Pi.neg_apply]
  have hn:Fin.removeNth i (-((2:ℤ) • variableExponent i))=0 := by
    funext j
    change -(Fin.removeNth i ((2:ℤ) • variableExponent i) j)=0
    rw [hrem]; rfl
  rw [hn]
  simp only [LaurentPolynomial.single_eq_C_mul_T]
  rfl

lemma insert_betaL {n : ℕ} (i : Fin (n+1)) (j : Fin n) :
    insertLaurent i (betaL j)=betaL (i.succAbove j) := by
  simp only [betaL,cosineL,map_add,insertLaurent_monomial]
  congr 2
  all_goals funext k; refine Fin.succAboveCases i ?_ (fun l => ?_) k
  all_goals simp [variableExponent,Pi.single_apply,eq_comm]

lemma peel_betaL_other {n : ℕ} (i : Fin (n+1)) (j : Fin n) :
    peelLaurentEquiv i (betaL (i.succAbove j))=LaurentPolynomial.C (betaL j) := by
  rw [←insert_betaL i j,peelLaurentEquiv_insert]

lemma betaL_monomial_expression {n : ℕ} (j : Fin n) :
    monomialL 0 2*(cosineL ((2:ℤ) • variableExponent j) (phase^3))=
    monomialL 0 (phase^3)*(monomialL (variableExponent j) 1)^2+
    monomialL 0 ((phase^3)⁻¹)*(monomialL (-variableExponent j) 1)^2 := by
  simp only [cosineL,pow_two,mul_add,monomialL_mul,zero_add,mul_one,two_smul,neg_add]
  congr 2 <;> ring

lemma betaL_unit_expression {n : ℕ} (j : Fin n) :
    (constantL n 2)*betaL j=
      (constantUnit n (phase^3) (pow_ne_zero _ phase_ne_zero) : Laurent n)*(variableUnit j : Laurent n)^2+
      (((constantUnit n (phase^3) (pow_ne_zero _ phase_ne_zero))⁻¹ : (Laurent n)ˣ) : Laurent n)*
        (((variableUnit j)⁻¹ : (Laurent n)ˣ) : Laurent n)^2 := by
  simp only [variableUnit_coe,variableUnit_inv_coe,constantUnit_coe,constantUnit_inv_coe]
  exact betaL_monomial_expression j

lemma cosineCollisionPacket_betaL {n : ℕ} (i : Fin (n+1)) (j : Fin n) :
    cosineCollisionPacket (constantUnit n (phase^3) (pow_ne_zero _ phase_ne_zero)) (variableUnit j)=
      2*(peelLaurentEquiv i (betaL i-betaL (i.succAbove j))) := by
  rw [map_sub,peel_betaL_self,peel_betaL_other,cosineCollisionPacket,←betaL_unit_expression]
  simp only [map_mul,constantUnit,monomialUnit]
  have h1 : (2:LaurentPolynomial (Laurent n))*LaurentPolynomial.C (constantL n (phase^3/2))=
      LaurentPolynomial.C (constantL n (phase^3)) := by
    rw [←map_ofNat LaurentPolynomial.C 2,←map_mul,←map_ofNat (constantL n) 2,←map_mul]
    congr 2
    ring
  have h2 : (2:LaurentPolynomial (Laurent n))*LaurentPolynomial.C (constantL n ((phase^3)⁻¹/2))=
      LaurentPolynomial.C (constantL n ((phase^3)⁻¹)) := by
    rw [←map_ofNat LaurentPolynomial.C 2,←map_mul,←map_ofNat (constantL n) 2,←map_mul]
    congr 2
    ring
  change LaurentPolynomial.C (constantL n (phase^3))*LaurentPolynomial.T 2+
    LaurentPolynomial.C (constantL n ((phase^3)⁻¹))*LaurentPolynomial.T (-2)-
    LaurentPolynomial.C (constantL n 2)*LaurentPolynomial.C (betaL j)=_
  simp only [map_ofNat]
  linear_combination -(LaurentPolynomial.T 2)*h1-(LaurentPolynomial.T (-2))*h2

 
lemma betaL_difference_dvd {n : ℕ} (i : Fin (n+1)) (j : Fin n) (f : Laurent (n+1))
    (h:∀ k, substituteLaurent i
      (cosineCollisionRoots (constantUnit n (phase^3) (pow_ne_zero _ phase_ne_zero)) (variableUnit j) k) f=0) :
    betaL i-betaL (i.succAbove j) ∣ f := by
  have hh:=cosineCollisionPacket_dvd (constantUnit n (phase^3) (pow_ne_zero _ phase_ne_zero))
    (variableUnit j) (collisionRoots_injective j) (peelLaurentEquiv i f) h
  rw [cosineCollisionPacket_betaL i j] at hh
  have hdiv : peelLaurentEquiv i (betaL i-betaL (i.succAbove j)) ∣ peelLaurentEquiv i f :=
    dvd_trans (dvd_mul_left _ _) hh
  exact (map_dvd_iff (peelLaurentEquiv i)).mp hdiv

end

 

 

noncomputable section
open scoped Classical LaurentPolynomial

lemma sum_upperPair {R:Type*} [AddCommMonoid R] {n:ℕ} (D:Fin n → Fin n → R) :
    (∑ e:UpperPair n,D e.val.1 e.val.2)=∑ i,∑ j∈Finset.Ioi i,D i j := by
  rw [←Finset.sum_subtype (Finset.univ.filter (fun ij:Fin n × Fin n => ij.1 < ij.2))
    (by simp) (fun ij:Fin n × Fin n => D ij.1 ij.2),Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  have h:Finset.Ioi i=Finset.univ.filter (fun j => i<j) := by ext j; simp
  rw [h,Finset.sum_filter]

lemma upperPair_incidence_sum {n:ℕ} (k:Fin (n+1)) :
    (∑ e:UpperPair (n+1), ((if e.val.1=k then 1 else 0)+(if e.val.2=k then 1 else 0):ℕ))=n := by
  rw [sum_upperPair (fun i j => ((if i=k then 1 else 0)+(if j=k then 1 else 0):ℕ))]
  simp_rw [Finset.sum_add_distrib]
  have h1:(∑ i:Fin (n+1),∑ _j∈Finset.Ioi i,(if i=k then 1 else 0:ℕ))=n-k.val := by
    simp only [Finset.sum_const,smul_eq_mul]
    simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true,Fin.card_Ioi]
    omega
  have h2:(∑ i:Fin (n+1),∑ j∈Finset.Ioi i,(if j=k then 1 else 0:ℕ))=k.val := by
    simp only [Finset.sum_ite_eq',Finset.mem_Ioi]
    rw [←Finset.sum_filter]
    have h:Finset.univ.filter (fun i:Fin (n+1) => i<k)=Finset.Iio k := by ext i; simp
    rw [h]
    simp only [Finset.sum_const,smul_eq_mul,mul_one,Fin.card_Iio]
  rw [h1,h2]
  have :=k.isLt
  omega

end

 

 

noncomputable section







lemma torusCos_sum {n : ℕ} (z w : SpectralField n) (hz : z≠0) (hw : w≠0) :
    torusCos (z/w)+torusCos (z*w)=2*torusCos z*torusCos w := by
  unfold torusCos
  field_simp [hz,hw]
  ring

lemma torusCos_product {n : ℕ} (z w : SpectralField n) (hz : z≠0) (hw : w≠0) :
    torusCos (z/w)*torusCos (z*w)=(torusCos z)^2+(torusCos w)^2-1 := by
  unfold torusCos
  field_simp [hz,hw]
  norm_num
  ring

lemma discriminant_torus_roots {n : ℕ} (z t : SpectralField n) (hz : z≠0) :
    discriminant (constF n d) (torusCos z) t=
      (t-torusCos (z/constF n phase^6))*(t-torusCos (z*constF n phase^6)) := by
  have hq := pow_ne_zero 6 (constF_phase_ne_zero n)
  have h6 : torusCos (constF n phase^6) = -constF n d := by
    rw [torusCos_phase_pow]
    simp only [Nat.cast_ofNat,cos_six_lambda,Complex.ofReal_neg,constF,map_neg]
  have hd : (constF n d)^2=1/2 := by
    have h:=congrArg (fun a : ℝ => constF n (a:ℂ)) d_sq
    simpa only [Complex.ofReal_pow,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat,
      constF,map_pow,map_div₀,map_one,map_ofNat] using h
  have hs:=torusCos_sum z (constF n phase^6) hz hq
  have hp:=torusCos_product z (constF n phase^6) hz hq
  rw [h6] at hs hp
  unfold discriminant
  linear_combination t*hs-hp-2*hd

lemma cosineL_two_ne {n : ℕ} (i j : Fin n) (hij : i≠j) (z w : ℂ) (hz : z≠0) :
    cosineL ((2:ℤ) • variableExponent i) z≠cosineL ((2:ℤ) • variableExponent j) w := by
  intro h
  have he : (2 : ℤ) • variableExponent i ≠ (2 : ℤ) • variableExponent j :=
    fun h => hij (twice_variableExponent_injective h)
  have hh:=congrArg (fun f : Laurent n => f.coeff ((2:ℤ) • variableExponent i)) h
  simp only [cosineL,monomialL,AddMonoidAlgebra.coeff_add,AddMonoidAlgebra.coeff_single,
    Finsupp.add_apply,Finsupp.single_apply] at hh
  simp only [ite_eq_right (twice_variableExponent_ne_neg i i).symm,
    ite_eq_right he.symm,ite_eq_right (twice_variableExponent_ne_neg i j).symm,add_zero] at hh
  exact hz ((div_eq_zero_iff).mp hh |>.resolve_right (by norm_num))

lemma cosineL_two_parameter {n : ℕ} (i : Fin n) (z w : ℂ) :
    cosineL ((2:ℤ) • variableExponent i) z=cosineL ((2:ℤ) • variableExponent i) w → z=w := by
  intro h
  have hh:=congrArg (fun f : Laurent n => f.coeff ((2:ℤ) • variableExponent i)) h
  simp only [cosineL,monomialL,AddMonoidAlgebra.coeff_add,AddMonoidAlgebra.coeff_single,
    Finsupp.add_apply,Finsupp.single_apply] at hh
  simp only [ite_eq_right (twice_variableExponent_ne_neg i i).symm,add_zero] at hh
  exact (div_left_inj' (by norm_num : (2:ℂ)≠0)).mp hh

 
def shiftedCosine {n : ℕ} (i : Fin n) (z : ℂ) : SpectralField n :=
  evalLaurent (cosineL ((2:ℤ) • variableExponent i) z)

lemma shiftedCosine_eq {n : ℕ} (i : Fin n) (z : ℂ) (hz : z≠0) :
    shiftedCosine i z=torusCos (constF n z*variableF i^2) := by
  rw [shiftedCosine,cosineL_map _ _ hz,map_monomialL_two_variable]

lemma shiftedCosine_ne {n : ℕ} (i j : Fin n) (hij : i≠j) (z w : ℂ) (hz : z≠0) :
    shiftedCosine i z≠shiftedCosine j w := by
  intro h
  exact cosineL_two_ne i j hij z w hz ((IsFractionRing.injective (SpectralRing n) (SpectralField n)) h)

lemma shiftedCosine_parameter {n : ℕ} (i : Fin n) (z w : ℂ) :
    shiftedCosine i z=shiftedCosine i w → z=w := by
  intro h
  exact cosineL_two_parameter i z w ((IsFractionRing.injective (SpectralRing n) (SpectralField n)) h)

lemma spectralA_shiftedCosine {n : ℕ} (i : Fin n) : spectralA i=shiftedCosine i (phase^(-3:ℤ)) := by
  rw [shiftedCosine_eq _ _ (zpow_ne_zero _ phase_ne_zero)]
  simp only [spectralA,constF,zpow_neg,zpow_ofNat,map_inv₀,map_pow,div_eq_mul_inv,mul_comm]

lemma deletionBeta_shiftedCosine {n : ℕ} (i : Fin n) :
    deletionBeta i=shiftedCosine i (phase^(3:ℤ)) := deletionBeta_laurent i


 

 


lemma shiftedCosine_roots {n : ℕ} (i : Fin n) (k : ℤ) (t : SpectralField n) :
    discriminant (constF n d) (shiftedCosine i (phase^k)) t=
      (t-shiftedCosine i (phase^(k-6)))*(t-shiftedCosine i (phase^(k+6))) := by
  rw [shiftedCosine_eq _ _ (zpow_ne_zero _ phase_ne_zero),
    shiftedCosine_eq _ _ (zpow_ne_zero _ phase_ne_zero),
    shiftedCosine_eq _ _ (zpow_ne_zero _ phase_ne_zero),
    discriminant_torus_roots _ _ (mul_ne_zero (by
      simpa only [constF,map_zero] using (algebraMap ℂ (SpectralField n)).injective.ne (zpow_ne_zero k phase_ne_zero)) (pow_ne_zero _ (variableF_ne_zero i)))]
  have hq := constF_phase_ne_zero n
  simp only [constF,map_zpow₀,zpow_sub₀ phase_ne_zero,zpow_add₀ phase_ne_zero,
    map_div₀,map_mul,map_pow,zpow_ofNat]
  congr 2 <;> congr 1 <;> ring

lemma shiftedCosine_discriminant_ne {n : ℕ} (i j : Fin n) (hij : i≠j) (k l : ℤ) :
    discriminant (constF n d) (shiftedCosine i (phase^k)) (shiftedCosine j (phase^l))≠0 := by
  rw [shiftedCosine_roots]
  exact mul_ne_zero (sub_ne_zero.mpr (shiftedCosine_ne j i hij.symm _ _ (zpow_ne_zero _ phase_ne_zero)))
    (sub_ne_zero.mpr (shiftedCosine_ne j i hij.symm _ _ (zpow_ne_zero _ phase_ne_zero)))

lemma phase_six_ne_one : phase^(6:ℕ)≠1 := by
  intro h
  have h₃ : phase^(24:ℕ)=1 := by simpa only [←pow_mul,one_pow] using congrArg (fun z : ℂ => z^(4:ℕ)) h
  have h₂ : phase^24=-1 := by
    calc
      _ = (phase^8)^3 := by rw [←pow_mul]
      _ = -1 := by rw [phase_eight]; norm_num
  rw [h₃] at h₂
  norm_num at h₂

lemma spectralA_ne_deletionBeta {n : ℕ} (i : Fin n) : spectralA i≠deletionBeta i := by
  rw [spectralA_shiftedCosine,deletionBeta_shiftedCosine]
  intro hh
  have h:=shiftedCosine_parameter i _ _ hh
  simp only [zpow_neg,zpow_ofNat] at h
  have hp : phase^6=1 := by
    calc
      _ = phase^3*phase^3 := by ring
      _ = (phase^3)⁻¹*phase^3 := by rw [h]
      _ = 1 := inv_mul_cancel₀ (pow_ne_zero _ phase_ne_zero)
  exact phase_six_ne_one hp

lemma spectralA_roots {n : ℕ} (i : Fin n) (t : SpectralField n) :
    discriminant (constF n d) (spectralA i) t=
      (t-deletionBeta i)*(t-shiftedCosine i (phase^(-9:ℤ))) := by
  rw [spectralA_shiftedCosine,deletionBeta_shiftedCosine,shiftedCosine_roots]
  norm_num
  ring

lemma deletionBeta_roots {n : ℕ} (i : Fin n) (t : SpectralField n) :
    discriminant (constF n d) (deletionBeta i) t=
      (t-spectralA i)*(t-shiftedCosine i (phase^(9:ℤ))) := by
  rw [spectralA_shiftedCosine,deletionBeta_shiftedCosine,shiftedCosine_roots]
  norm_num

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ThreeBoxSplitPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram.ThreeBox
noncomputable section

def mergeNumerator {K : Type*} [CommRing K] (q : K) : Tile → K
  | .vacant => q^2+1
  | .vertical₀ | .vertical₁ | .diagonal₀ | .diagonal₁ | .cap | .cup => q
  | _ => 0






open Finset



end
end CriticalStrip.Diagram.ThreeBox

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_PhaseAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/





namespace CriticalStrip.Diagram
noncomputable section


def mergeWeights {K : Type*} [Field K] (q : K) : Weights K :=
  ⟨q/(q^2+1),q/(q^2+1),q/(q^2+1),0,0⟩

lemma mergeWeights_cleared {K : Type*} [Field K] (q : K) (hq : q^2+1≠0) :
    (fun t => (q^2+1)*(mergeWeights q).tile t) = ThreeBox.mergeNumerator q := by
  funext t
  cases t <;> simp [mergeWeights,Weights.tile,ThreeBox.mergeNumerator, mul_div_cancel₀, hq]

lemma shifted_gamma_difference {n : ℕ} (i j : Fin n) :
    spectralA j-shiftedCosine i (phase^(-9:ℤ))=
      -2*torusSin (variableF i*variableF j/constF n phase^6)*
        torusSin (constF n phase^5*(variableF i/variableF j)) := by
  have hq := constF_phase_ne_zero n
  have hi := variableF_ne_zero i
  have hj := variableF_ne_zero j
  have hp:=torusSin_product (variableF i*variableF j/constF n phase^6)
    (constF n phase^3*variableF j/variableF i)
    (div_ne_zero (mul_ne_zero hi hj) (pow_ne_zero _ hq))
    (div_ne_zero (mul_ne_zero (pow_ne_zero _ hq) hj) hi)
  have he₁ : (variableF i*variableF j/constF n phase^6)/
      (constF n phase^3*variableF j/variableF i)=constF n (phase^(-9:ℤ))*variableF i^2 := by
    simp only [constF,zpow_neg,zpow_ofNat,map_inv₀,map_pow]
    field_simp
  have he₂ : (variableF i*variableF j/constF n phase^6)*
      (constF n phase^3*variableF j/variableF i)=variableF j^2/constF n phase^3 := by
    field_simp
  have he₃ : constF n phase^3*variableF j/variableF i=
      -(constF n phase^5*(variableF i/variableF j))⁻¹ := by
    have h:=constF_phase_eight n
    field_simp
    linear_combination h
  rw [he₁,he₂,he₃,torusSin_neg,torusSin_inv] at hp
  rw [shiftedCosine_eq _ _ (zpow_ne_zero _ phase_ne_zero)]
  change torusCos (variableF j^2/constF n phase^3)-_= _
  rw [neg_neg] at hp
  linear_combination hp

lemma shifted_sigma_difference {n : ℕ} (i j : Fin n) :
    spectralA j-shiftedCosine i (phase^(9:ℤ))=
      2*torusSin (constF n phase^3*(variableF i*variableF j))*
        torusSin (constF n phase^6*(variableF i/variableF j)) := by
  have hq := constF_phase_ne_zero n
  have hi := variableF_ne_zero i
  have hj := variableF_ne_zero j
  have hp:=torusSin_product (constF n phase^3*(variableF i*variableF j))
    (variableF j/(constF n phase^6*variableF i))
    (mul_ne_zero (pow_ne_zero _ hq) (mul_ne_zero hi hj))
    (div_ne_zero hj (mul_ne_zero (pow_ne_zero _ hq) hi))
  have he₁ : (constF n phase^3*(variableF i*variableF j))/
      (variableF j/(constF n phase^6*variableF i))=constF n (phase^(9:ℤ))*variableF i^2 := by
    simp only [constF,zpow_ofNat,map_pow]
    field_simp
  have he₂ : (constF n phase^3*(variableF i*variableF j))*
      (variableF j/(constF n phase^6*variableF i))=variableF j^2/constF n phase^3 := by
    field_simp
  have he₃ : variableF j/(constF n phase^6*variableF i)=
      (constF n phase^6*(variableF i/variableF j))⁻¹ := by
    field_simp
  rw [he₁,he₂,he₃,torusSin_inv] at hp
  rw [shiftedCosine_eq _ _ (zpow_ne_zero _ phase_ne_zero)]
  change torusCos (variableF j^2/constF n phase^3)-_= _
  linear_combination hp

 

theorem movingBox_scalar_cancellation {n : ℕ} (i j : Fin n) :
    (spectralA j-shiftedCosine i (phase^(-9:ℤ)))*
      (spectralA j-shiftedCosine i (phase^(9:ℤ)))=
      (-4*torusSin (variableF i*variableF j/constF n phase^6)*
        torusSin (constF n phase^3*(variableF i*variableF j)))*
          torusL (constF n phase^3*(variableF i/variableF j)) := by
  rw [shifted_gamma_difference,shifted_sigma_difference]
  unfold torusL
  have h₁ : constF n phase^2*(constF n phase^3*(variableF i/variableF j))=
      constF n phase^5*(variableF i/variableF j) := by ring
  have h₂ : constF n phase^3*(constF n phase^3*(variableF i/variableF j))=
      constF n phase^6*(variableF i/variableF j) := by ring
  rw [h₁,h₂]
  ring

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_MirrorExterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical
namespace TriplePosition
variable {n : ℕ} (s : TriplePosition n)

def mirrorActive (p q : Pairing n) : Fin 6 → Prop :=
  ![p.Occupied s.c,p.Occupied s.b,p.Occupied s.a,
    q.Occupied s.c,q.Occupied s.b,q.Occupied s.a]

def mirrorExterior (p q : Pairing n) : (Fin n ⊕ Fin n) → (Fin n ⊕ Fin n) → Prop
  | .inl i,.inl j => p.Adj i j
  | .inl i,.inr j | .inr j,.inl i => i=j ∧ i≠s.c ∧ i≠s.b ∧ i≠s.a ∧ q.Occupied i
  | .inr _,.inr _ => False

def MirrorOutside (p q : Pairing n) : Prop :=
  ∀ i, i≠s.c → i≠s.b → i≠s.a → (p.Occupied i ↔ q.Occupied i)

lemma mirror_interface_old (p q : Pairing n) (v : Fin 12) (i : Fin n) :
    (∃ k, s.mirrorActive p q k ∧ v=ThreeBox.boundary k ∧ (.inl i : Fin n ⊕ Fin n)=s.mirrorInterface k) ↔
      (i=s.c ∧ v=4 ∧ p.Occupied s.c) ∨
      (i=s.b ∧ v=0 ∧ p.Occupied s.b) ∨ (i=s.a ∧ v=1 ∧ p.Occupied s.a) := by
  simp only [Fin.exists_fin_succ,mirrorInterface,mirrorActive,ThreeBox.boundary]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_fin_one,
    Sum.inl.injEq,Sum.inl_ne_inr,and_false,or_false,Fin.exists_fin_zero]
  itauto

lemma mirror_interface_new (p q : Pairing n) (v : Fin 12) (i : Fin n) :
    (∃ k, s.mirrorActive p q k ∧ v=ThreeBox.boundary k ∧ (.inr i : Fin n ⊕ Fin n)=s.mirrorInterface k) ↔
      ((i=s.c ∧ v=6) ∨ (i=s.b ∧ v=10) ∨ (i=s.a ∧ v=11)) ∧ q.Occupied i := by
  simp only [Fin.exists_fin_succ,mirrorInterface,mirrorActive,ThreeBox.boundary]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_fin_one,
    Sum.inr.injEq,Sum.inr_ne_inl,and_false,false_or,or_false,Fin.exists_fin_zero]
  constructor
  · rintro (⟨h,hv,hi⟩ | ⟨h,hv,hi⟩ | ⟨h,hv,hi⟩) <;> subst i
    · exact ⟨Or.inl ⟨rfl,hv⟩,h⟩
    · exact ⟨Or.inr (Or.inl ⟨rfl,hv⟩),h⟩
    · exact ⟨Or.inr (Or.inr ⟨rfl,hv⟩),h⟩
  · rintro ⟨(⟨rfl,hv⟩|⟨rfl,hv⟩|⟨rfl,hv⟩),h⟩
    · exact Or.inl ⟨h,hv,rfl⟩
    · exact Or.inr (Or.inl ⟨h,hv,rfl⟩)
    · exact Or.inr (Or.inr ⟨h,hv,rfl⟩)

end TriplePosition
end
end CriticalStrip.Diagram





end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_SwapVacancy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram





noncomputable section
open scoped Classical
namespace PartialColumn
variable {n m : ℕ}

 
def twoRows {K : Type*} (w : Fin n → Weights K) (r : ℕ) (a b : Weights K) : Fin n → Weights K :=
  fun i => if i.val=r then a else if i.val=r+1 then b else w i

lemma twoRows₀ {K : Type*} (w : Fin n → Weights K) (r : ℕ) (hr : r+2≤n) (a b : Weights K) :
    twoRows w r a b ⟨r,by omega⟩=a := by simp [twoRows]
lemma twoRows₁ {K : Type*} (w : Fin n → Weights K) (r : ℕ) (hr : r+2≤n) (a b : Weights K) :
    twoRows w r a b ⟨r+1,by omega⟩=b := by simp [twoRows]
lemma twoRows_other {K : Type*} (w : Fin n → Weights K) (r : ℕ) (a b : Weights K)
    (i : Fin n) (hi : i.val≠r) (hj : i.val≠r+1) : w i=twoRows w r a b i := by simp [twoRows,hi,hj]



end PartialColumn
end





end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_NodalRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section

 
def inverseRowDenominator {n : ℕ} (i : Fin n) : Laurent n :=
  sineL (-variableExponent i) (phase^(2:ℤ)) *
    sineL (-variableExponent i) (phase^(3:ℤ))

def inverseRowNumerator {n : ℕ} (i : Fin n) : Tile → Laurent n
  | .vacant => inverseRowDenominator i
  | .vertical₀ | .vertical₁ =>
      constantL n d * sineL (variableExponent i) (phase^(3:ℤ))
  | .diagonal₀ | .diagonal₁ =>
      sineL (-variableExponent i) (phase^(0:ℤ)) *
        sineL (variableExponent i) (phase^(3:ℤ))
  | .cap | .cup => constantL n d * sineL (-variableExponent i) (phase^(0:ℤ))
  | .verticalPair =>
      sineL (variableExponent i) (phase^(3:ℤ)) *
        sineL (variableExponent i) (phase^(2:ℤ))
  | .capCup =>
      sineL (-variableExponent i) (phase^(-1:ℤ)) *
        sineL (-variableExponent i) (phase^(0:ℤ))

theorem inverseRowDenominator_flat {n : ℕ} (i : Fin n) :
    flatEval n (inverseRowDenominator i) =
      (Real.sin (2*lambda) : ℂ) * (Real.sin (3*lambda) : ℂ) := by
  simp only [inverseRowDenominator, map_mul, flatEval_sine_phase, Int.cast_ofNat]

theorem inverseRowDenominator_flat_ne_zero {n : ℕ} (i : Fin n) :
    flatEval n (inverseRowDenominator i) ≠ 0 := by
  simpa only [inverseRowDenominator_flat, flatEval_rowDenominator, mul_comm] using
    flatEval_rowDenominator_ne_zero i

theorem inverseRowDenominator_map {n : ℕ} (i : Fin n) :
    evalLaurent (inverseRowDenominator i) = torusL (variableF i)⁻¹ := by
  simp only [evalLaurent, inverseRowDenominator, map_mul, zpow_ofNat,
    map_sine_neg_variable_nat, torusL, div_eq_mul_inv]

theorem inverseRowDenominator_map_ne_zero {n : ℕ} (i : Fin n) :
    evalLaurent (inverseRowDenominator i) ≠ 0 := by
  apply (IsFractionRing.to_map_eq_zero_iff.not).2
  intro h
  exact inverseRowDenominator_flat_ne_zero i (by rw [h, map_zero])

theorem inverseRowNumerator_flat {n : ℕ} (i : Fin n) (t : Tile) :
    flatEval n (inverseRowNumerator i t) =
      flatEval n (inverseRowDenominator i) * (identityWeights : Weights ℂ).tile t := by
  have hd : (d : ℂ) = (Real.sin (2*lambda) : ℂ) := by
    congr 1
    rw [d, ← Real.sin_pi_div_two_sub]
    congr 1
    unfold lambda
    ring
  cases t <;> simp only [inverseRowNumerator, map_mul, flatEval_constant,
    flatEval_sine_phase, inverseRowDenominator_flat, identityWeights, Weights.tile,
    Int.cast_ofNat, Int.cast_zero, zero_mul, Real.sin_zero, Complex.ofReal_zero,
    mul_zero, mul_one]
  all_goals try rw [hd]
  all_goals ring

theorem inverseRowNumerator_map {n : ℕ} (i : Fin n) (t : Tile) :
    evalLaurent (inverseRowNumerator i t) =
      evalLaurent (inverseRowDenominator i) * (torusWeights (variableF i)⁻¹).tile t := by
  have hx := variableF_ne_zero i
  have hq := constF_phase_ne_zero n
  have hL : torusL (variableF i)⁻¹ ≠ 0 := by
    rw [← inverseRowDenominator_map]
    exact inverseRowDenominator_map_ne_zero i
  have h₃ : constF n phase ^ 3 / (variableF i)⁻¹ = constF n phase ^ 3 * variableF i := by simp
  have h₂ : constF n phase ^ 2 / (variableF i)⁻¹ = constF n phase ^ 2 * variableF i := by simp
  have hd : algebraMap (SpectralRing n) (SpectralField n) (inverseRowDenominator i) =
      torusL (variableF i)⁻¹ := inverseRowDenominator_map i
  cases t <;> simp only [evalLaurent, inverseRowNumerator, map_mul, map_constantL,
    zpow_ofNat, map_sine_variable_nat, map_sine_neg_variable_nat,
    zpow_neg_one, hd, torusWeights, Weights.tile,
    h₃, h₂, mul_one]
  all_goals try simp only [← one_div (variableF i)] at hL
  all_goals try field_simp [hL]
  rw [sineL_map _ _ (one_div_ne_zero phase_ne_zero), map_monomialL_neg_variable]
  simp only [constF, div_eq_mul_inv, mul_inv_rev]
  simp only [mul_one, one_mul, map_inv₀, mul_comm]

theorem nodalWeights_last {n : ℕ} (i : Fin n) :
    nodalWeights i (Fin.last n) = torusWeights (variableF i)⁻¹ := by
  simp only [nodalWeights, Fin.snoc_last, deletionNode]
  congr 1
  field_simp [constF_phase_ne_zero]






open scoped Classical



lemma map_monomialL_sub_variable {n : ℕ} (i j : Fin n) (z : ℂ) :
    evalLaurent (monomialL (variableExponent j-variableExponent i) z)=
      constF n z*(variableF j/variableF i) := by
  have hm : monomialL (variableExponent j-variableExponent i) z =
      monomialL (variableExponent j) z * monomialL (-variableExponent i) 1 := by
    simp only [monomialL_mul,mul_one,sub_eq_add_neg]
  rw [hm,evalLaurent,map_mul,map_monomialL_variable,map_monomialL_neg_variable]
  simp only [constF,map_one,div_eq_mul_inv,mul_assoc,one_mul]

lemma torusL_ratio_ne_zero {n : ℕ} (i j : Fin n) : torusL (variableF j/variableF i)≠0 := by
  let e := variableExponent j-variableExponent i
  let D : Laurent n := sineL e (phase^2)*sineL e (phase^3)
  have hev : evalLaurent D=torusL (variableF j/variableF i) := by
    simp only [D,evalLaurent,map_mul,torusL]
    rw [sineL_map _ _ (pow_ne_zero _ phase_ne_zero),
      sineL_map _ _ (pow_ne_zero _ phase_ne_zero),
      show (algebraMap (SpectralRing n) (SpectralField n)) (monomialL e (phase^2))=
        constF n (phase^2)*(variableF j/variableF i) from map_monomialL_sub_variable i j _,
      show (algebraMap (SpectralRing n) (SpectralField n)) (monomialL e (phase^3))=
        constF n (phase^3)*(variableF j/variableF i) from map_monomialL_sub_variable i j _]
    simp only [constF,map_pow]
  have hf : flatEval n D=(Real.sin (2*lambda):ℂ)*(Real.sin (3*lambda):ℂ) := by
    change (flatEval n (sineL e (phase^(2:ℤ))*sineL e (phase^(3:ℤ))))=_
    simp only [map_mul,flatEval_sine_phase,Int.cast_ofNat]
  rw [←hev]
  apply (IsFractionRing.to_map_eq_zero_iff.not).2
  intro h
  have hne:=flatEval_rowDenominator_ne_zero i
  apply hne
  rw [flatEval_rowDenominator]
  have hh : flatEval n D=0 := by rw [h,map_zero]
  rw [hf] at hh
  simpa only [mul_comm] using hh



end

 

 

noncomputable section
open scoped Classical

 
def insertedNodeWeights {n : ℕ} (i : Fin n) (j : Fin (n+1)) :
    Fin (n+1) → Weights (SpectralField n) :=
  Fin.insertNth j (torusWeights (variableF i)⁻¹) (spectralWeights n)

lemma insertedNodeWeights_last {n : ℕ} (i : Fin n) :
    insertedNodeWeights i (Fin.last n)=nodalWeights i := by
  rw [insertedNodeWeights,Fin.insertNth_last']
  funext j
  induction j using Fin.lastCases with
  | last => rw [Fin.snoc_last,nodalWeights_last]
  | cast j => simp [nodalWeights]



lemma torusL_deletion_ratio_ne_zero {n : ℕ} (i j : Fin n) :
    torusL (constF n phase^3*(variableF i/variableF j))≠0 := by
  let e:=variableExponent i-variableExponent j
  let D : Laurent n:=sineL e (phase^5)*sineL e (phase^6)
  have hev : evalLaurent D=torusL (constF n phase^3*(variableF i/variableF j)) := by
    simp only [D,evalLaurent,map_mul,torusL]
    rw [sineL_map _ _ (pow_ne_zero _ phase_ne_zero),sineL_map _ _ (pow_ne_zero _ phase_ne_zero),
      show (algebraMap (SpectralRing n) (SpectralField n)) (monomialL e (phase^5))=
        constF n (phase^5)*(variableF i/variableF j) from map_monomialL_sub_variable j i _,
      show (algebraMap (SpectralRing n) (SpectralField n)) (monomialL e (phase^6))=
        constF n (phase^6)*(variableF i/variableF j) from map_monomialL_sub_variable j i _]
    simp only [constF,map_pow]
    congr 1 <;> congr 1 <;> ring
  have hf : flatEval n D=flatEval n (rowDenominator i) := by
    change (flatEval n (sineL e (phase^(5:ℤ))*sineL e (phase^(6:ℤ))))=_
    simp only [rowDenominator,map_mul,flatEval_sine_phase]
  rw [←hev]
  apply (IsFractionRing.to_map_eq_zero_iff.not).2
  intro h
  exact flatEval_rowDenominator_ne_zero i (by rw [←hf,h,map_zero])



lemma permSpectral_nodalWeights {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    (fun j => (nodalWeights i j).map (permSpectral σ))=
      (fun j => nodalWeights (σ i) (topPerm σ j)) := by
  funext j
  induction j using Fin.lastCases with
  | last => simp [nodalWeights,map_div₀]
  | cast j => simp [nodalWeights]

end

 

 

noncomputable section

 

def deletionPerm {n : ℕ} (i : Fin (n+1)) : Equiv.Perm (Fin (n+2)) :=
  Equiv.ofBijective (twoCons i.castSucc (Fin.last (n+1)) (fun j => (i.succAbove j).castSucc))
    (Finite.injective_iff_bijective.mp (by
      intro a b h
      induction a using Fin.cases with
      | zero =>
          induction b using Fin.cases with
          | zero => rfl
          | succ b =>
              induction b using Fin.cases with
              | zero => exact (Fin.castSucc_ne_last i (by simp at h)).elim
              | succ b =>
                  have hh : i=i.succAbove b := (by simp at h)
                  exact (Fin.succAbove_ne i b hh.symm).elim
      | succ a =>
          induction a using Fin.cases with
          | zero =>
              induction b using Fin.cases with
              | zero => exact (Fin.castSucc_ne_last i (by simpa using h.symm)).elim
              | succ b =>
                  induction b using Fin.cases with
                  | zero => rfl
                  | succ b => exact (Fin.castSucc_ne_last (i.succAbove b) (by simpa using h.symm)).elim
          | succ a =>
              induction b using Fin.cases with
              | zero =>
                  have hh : i.succAbove a=i := (by simp at h)
                  exact (Fin.succAbove_ne i a hh).elim
              | succ b =>
                  induction b using Fin.cases with
                  | zero => exact (Fin.castSucc_ne_last (i.succAbove a) (by simp at h)).elim
                  | succ b =>
                      have hh : i.succAbove a=i.succAbove b := (by simpa using h)
                      exact congrArg (fun j : Fin n => j.succ.succ) (Fin.succAbove_right_injective hh)))

lemma deletionPerm_tuple {K : Type*} {n : ℕ} (i : Fin (n+1)) (a : Fin (n+1) → K) (b : K) :
    (Fin.snoc a b) ∘ deletionPerm i=twoCons (a i) b (fun k => a (i.succAbove k)) := by
  funext j
  induction j using Fin.cases with
  | zero => simp [deletionPerm]
  | succ j =>
      induction j using Fin.cases with
      | zero => simp [deletionPerm]
      | succ j => simp [deletionPerm]

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_NodalScalarDeletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open Finset
open scoped Classical

lemma spectralA_injective (n : ℕ) : Function.Injective (@spectralA n) := by
  intro i j h
  by_contra hij
  rw [spectralA_shiftedCosine,spectralA_shiftedCosine] at h
  exact shiftedCosine_ne i j hij _ _ (zpow_ne_zero _ phase_ne_zero) h

lemma spectralA_ne_beta {n : ℕ} (i j : Fin n) : spectralA j≠deletionBeta i := by
  by_cases hij : j=i
  · subst j; exact spectralA_ne_deletionBeta i
  · rw [spectralA_shiftedCosine,deletionBeta_shiftedCosine]
    exact shiftedCosine_ne j i hij _ _ (zpow_ne_zero _ phase_ne_zero)

def deletionScalarTuple {n : ℕ} (i : Fin (n+1)) : Fin (n+2) → SpectralField (n+1) :=
  twoCons (spectralA i) (deletionBeta i) (fun k => spectralA (i.succAbove k))

lemma deletionScalarTuple_injective {n : ℕ} (i : Fin (n+1)) :
    Function.Injective (deletionScalarTuple i) := by
  rw [deletionScalarTuple,←deletionPerm_tuple]
  apply Function.Injective.comp _ (deletionPerm i).injective
  intro j k h
  induction j using Fin.lastCases with
  | last =>
      induction k using Fin.lastCases with
      | last => rfl
      | cast k => exact (spectralA_ne_beta i k (by simpa using h.symm)).elim
  | cast j =>
      induction k using Fin.lastCases with
      | last => exact (spectralA_ne_beta i j (by simpa using h)).elim
      | cast k => exact congrArg Fin.castSucc (spectralA_injective _ (by simpa using h))

lemma spectralA_discriminant_ne {n : ℕ} (i j : Fin n) (hij : i≠j) :
    discriminant (constF n d) (spectralA i) (spectralA j)≠0 := by
  rw [spectralA_shiftedCosine,spectralA_shiftedCosine]
  exact shiftedCosine_discriminant_ne i j hij _ _

lemma beta_spectralA_discriminant_ne {n : ℕ} (i j : Fin n) (hij : i≠j) :
    discriminant (constF n d) (deletionBeta i) (spectralA j)≠0 := by
  rw [deletionBeta_shiftedCosine,spectralA_shiftedCosine]
  exact shiftedCosine_discriminant_ne i j hij _ _

lemma deletionScalarTuple_discriminant {n : ℕ} (i : Fin (n+1))
    (j k : Fin (n+2)) (hjk : j≠k)
    (hp : ¬((j=0 ∧ k=1) ∨ (j=1 ∧ k=0))) :
    discriminant (constF (n+1) d) (deletionScalarTuple i j) (deletionScalarTuple i k)≠0 := by
  induction j using Fin.cases with
  | zero =>
      induction k using Fin.cases with
      | zero => exact (hjk rfl).elim
      | succ k =>
          induction k using Fin.cases with
          | zero => exact (hp (Or.inl ⟨rfl,by simp⟩)).elim
          | succ k =>
              exact spectralA_discriminant_ne i (i.succAbove k) (Fin.succAbove_ne i k).symm
  | succ j =>
      induction j using Fin.cases with
      | zero =>
          induction k using Fin.cases with
          | zero => exact (hp (Or.inr ⟨by simp,rfl⟩)).elim
          | succ k =>
              induction k using Fin.cases with
              | zero => exact (hjk rfl).elim
              | succ k =>
                  exact beta_spectralA_discriminant_ne i (i.succAbove k) (Fin.succAbove_ne i k).symm
      | succ j =>
          induction k using Fin.cases with
          | zero =>
              exact spectralA_discriminant_ne (i.succAbove j) i (Fin.succAbove_ne i j)
          | succ k =>
              induction k using Fin.cases with
              | zero =>
                  rw [discriminant_symm]
                  exact beta_spectralA_discriminant_ne i (i.succAbove j) (Fin.succAbove_ne i j).symm
              | succ k =>
                  exact spectralA_discriminant_ne _ _ (fun he => hjk
                    (congrArg (fun x : Fin n => x.succ.succ) (Fin.succAbove_right_injective he)))








def deletionDataFactor {n : ℕ} (i : Fin (n+1)) : SpectralField (n+1) :=
  (spectralA i+deletionBeta i+constF (n+1) rho)*
    ∏ j : Fin n, (spectralA (i.succAbove j)-shiftedCosine i (phase^(-9:ℤ)))*
      (spectralA (i.succAbove j)-shiftedCosine i (phase^(9:ℤ)))

end

 

 

noncomputable section
open scoped Classical


def torusNumerator {n : ℕ} (z : SpectralField n) : Tile → SpectralField n
  | .vacant => torusL z
  | .cap | .cup => constF n d*torusSin z
  | .vertical₀ | .vertical₁ => constF n d*torusSin (constF n phase^3/z)
  | .diagonal₀ | .diagonal₁ => torusSin z*torusSin (constF n phase^3/z)
  | .verticalPair => torusSin (constF n phase^3/z)*torusSin (constF n phase^2/z)
  | .capCup => torusSin (z/constF n phase)*torusSin z

lemma torusNumerator_eq {n : ℕ} (z : SpectralField n) (hL : torusL z≠0) (t : Tile) :
    torusNumerator z t=torusL z*(torusWeights z).tile t := by
  cases t <;> simp only [torusNumerator,torusWeights,Weights.tile]
  all_goals field_simp



end

 

 

noncomputable section
open scoped Classical

variable {K L ι : Type*} [CommRing K] [CommRing L] [Fintype ι] [DecidableEq ι]

lemma matrixPrefix_smul_partial {n : ℕ} (a : Fin n → K) (A : Fin n → Matrix ι ι K)
    (k : ℕ) :
    matrixPrefix (fun i => a i • A i) k=
      (∏ j∈Finset.range k,if h:j<n then a ⟨j,h⟩ else 1) • matrixPrefix A k := by
  induction k with
  | zero => simp [matrixPrefix]
  | succ k ih =>
    rw [matrixPrefix,Finset.prod_range_succ,matrixPrefix]
    by_cases hk:k<n
    · rw [dite_eq_left hk,dite_eq_left hk,dite_eq_left hk,ih,Matrix.smul_mul,Matrix.mul_smul,smul_smul]
      congr 1
      exact mul_comm _ _
    · rw [dite_eq_right hk,dite_eq_right hk,dite_eq_right hk,mul_one,ih]

lemma matrixPrefix_smul {n : ℕ} (a : Fin n → K) (A : Fin n → Matrix ι ι K) :
    matrixPrefix (fun i => a i • A i) n=(∏ i,a i) • matrixPrefix A n := by
  rw [matrixPrefix_smul_partial,←Finset.prod_fin_eq_prod_range]

end

 

 

noncomputable section






open scoped Classical


def reflectionFactor {n : ℕ} (i j : Fin n) : SpectralField n :=
  if j=i then 1 else torusSin (constF n phase^3*(variableF i*variableF j))

def scalarPairFactor {n : ℕ} (i j : Fin n) : SpectralField n :=
  if j=i then 1 else (spectralA j-shiftedCosine i (phase^(-9:ℤ)))*
    (spectralA j-shiftedCosine i (phase^(9:ℤ)))



lemma scalarPairFactor_product {n : ℕ} (i : Fin (n+1)) :
    (∏ j,scalarPairFactor i j)=
      ∏ j : Fin n,(spectralA (i.succAbove j)-shiftedCosine i (phase^(-9:ℤ)))*
        (spectralA (i.succAbove j)-shiftedCosine i (phase^(9:ℤ))) := by
  rw [Fin.prod_univ_succAbove _ i]
  simp [scalarPairFactor,Fin.succAbove_ne]



end





noncomputable section
open scoped Classical

def reducedNodalHead {n : ℕ} (i : Fin n) (occupied : Prop) [Decidable occupied] : SpectralField n :=
  if occupied then 4*constF n c*torusSin (constF n phase^3/variableF i)
  else spectralA i+deletionBeta i+constF n rho


end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_LaurentNumerator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

lemma evalLaurent_monomial_scale {n : ℕ} (e : Fin n → ℤ) (c z : ℂ) :
    (algebraMap (SpectralRing n) (SpectralField n)) (monomialL e (c*z))=constF n c*(algebraMap (SpectralRing n) (SpectralField n)) (monomialL e z) := by
  rw [←map_constantL]
  change (algebraMap (SpectralRing n) (SpectralField n)) (monomialL e (c*z))=(algebraMap (SpectralRing n) (SpectralField n)) (monomialL 0 c)*(algebraMap (SpectralRing n) (SpectralField n)) (monomialL e z)
  rw [←map_mul,monomialL_mul,zero_add]

lemma evalLaurent_monomial_quot {n : ℕ} (e : Fin n → ℤ) (z : ℂ) (hz:z≠0) (c : ℂ) :
    (algebraMap (SpectralRing n) (SpectralField n)) (monomialL (-e) (c/z))=constF n c/(algebraMap (SpectralRing n) (SpectralField n)) (monomialL e z) := by
  rw [div_eq_mul_inv,div_eq_mul_inv,evalLaurent_monomial_scale]
  congr 1
  exact (map_monomialL_inv e z hz).symm

 
def torusNumeratorL {n : ℕ} (e : Fin n → ℤ) (z : ℂ) : Tile → Laurent n
  | .vacant => sineL e (phase^2*z)*sineL e (phase^3*z)
  | .vertical₀ | .vertical₁ => constantL n d*sineL (-e) (phase^3/z)
  | .cap | .cup => constantL n d*sineL e z
  | .diagonal₀ | .diagonal₁ => sineL e z*sineL (-e) (phase^3/z)
  | .verticalPair => sineL (-e) (phase^3/z)*sineL (-e) (phase^2/z)
  | .capCup => sineL e (z/phase)*sineL e z

lemma sineL_map_scale {n : ℕ} (e : Fin n → ℤ) (c z : ℂ) (hc:c≠0) (hz:z≠0) :
    (algebraMap (SpectralRing n) (SpectralField n)) (sineL e (c*z))=torusSin (constF n c*(algebraMap (SpectralRing n) (SpectralField n)) (monomialL e z)) := by
  rw [sineL_map e (c*z) (mul_ne_zero hc hz),evalLaurent_monomial_scale]

lemma sineL_map_quot {n : ℕ} (e : Fin n → ℤ) (z c : ℂ) (hc:c≠0) (hz:z≠0) :
    (algebraMap (SpectralRing n) (SpectralField n)) (sineL (-e) (c/z))=torusSin (constF n c/(algebraMap (SpectralRing n) (SpectralField n)) (monomialL e z)) := by
  rw [sineL_map _ _ (div_ne_zero hc hz),evalLaurent_monomial_quot e z hz]

lemma torusNumeratorL_map {n : ℕ} (e : Fin n → ℤ) (z : ℂ) (hz:z≠0) (t : Tile) :
    (algebraMap (SpectralRing n) (SpectralField n)) (torusNumeratorL e z t)=torusNumerator ((algebraMap (SpectralRing n) (SpectralField n)) (monomialL e z)) t := by
  cases t
  all_goals simp only [torusNumeratorL,torusNumerator,torusL,map_mul,map_constantL]
  all_goals try rw [sineL_map e z hz]
  all_goals try rw [sineL_map_scale e (phase^2) z (pow_ne_zero _ phase_ne_zero) hz]
  all_goals try rw [sineL_map_scale e (phase^3) z (pow_ne_zero _ phase_ne_zero) hz]
  all_goals try rw [sineL_map_quot e z (phase^3) (pow_ne_zero _ phase_ne_zero) hz]
  all_goals try rw [sineL_map_quot e z (phase^2) (pow_ne_zero _ phase_ne_zero) hz]
  all_goals try simp only [constF,map_pow]
  have he:z/phase=phase⁻¹*z := by ring
  rw [he,sineL_map_scale e phase⁻¹ z (inv_ne_zero phase_ne_zero) hz]
  simp only [constF,map_inv₀]
  congr 2
  exact inv_mul_eq_div _ _







lemma map_monomialL_add_variable {n : ℕ} (i j : Fin n) (z : ℂ) :
    evalLaurent (monomialL (variableExponent i+variableExponent j) z)=
      constF n z*(variableF i*variableF j) := by
  have hm : monomialL (variableExponent i+variableExponent j) z =
      monomialL (variableExponent i) z*monomialL (variableExponent j) 1 := by simp
  rw [hm,evalLaurent,map_mul,map_monomialL_variable,map_monomialL_variable]
  simp only [constF,map_one,one_mul,mul_assoc]



lemma reducedMovingStepL_scalar {n : ℕ} (i j : Fin n) :
    evalLaurent (constantL n (-4)*sineL (variableExponent i+variableExponent j) (phase^(-6:ℤ)))=
      -4*torusSin (variableF i*variableF j/constF n phase^6) := by
  rw [evalLaurent,map_mul,map_constantL,sineL_map _ _ (zpow_ne_zero _ phase_ne_zero)]
  change constF n (-4)*torusSin (evalLaurent (monomialL _ _))=_
  rw [map_monomialL_add_variable]
  simp only [constF,map_neg,map_ofNat,map_zpow₀,zpow_neg,map_inv₀]
  congr 2
  field_simp

lemma torusNumeratorL_pair_map {n : ℕ} (i j : Fin n) (t : Tile) :
    evalLaurent (torusNumeratorL (variableExponent i-variableExponent j) (phase^3) t)=
      torusNumerator (constF n phase^3*(variableF i/variableF j)) t := by
  change (algebraMap (SpectralRing n) (SpectralField n)) (_)=_
  rw [torusNumeratorL_map _ _ (pow_ne_zero _ phase_ne_zero)]
  change torusNumerator (evalLaurent (monomialL _ _)) t=_
  rw [map_monomialL_sub_variable]
  simp only [constF,map_pow]

def nodalHeadL {n : ℕ} (i : Fin n) (occupied : Prop) [Decidable occupied] : Laurent n :=
  if occupied then constantL n (4*c)*sineL (-variableExponent i) (phase^3)
  else cosineL ((2:ℤ) • variableExponent i) (phase^(-3:ℤ))+
    cosineL ((2:ℤ) • variableExponent i) (phase^3)+constantL n rho

lemma nodalHeadL_map {n : ℕ} (i : Fin n) (occupied : Prop) [Decidable occupied] :
    evalLaurent (nodalHeadL i occupied)=reducedNodalHead i occupied := by
  by_cases h:occupied
  · simp only [nodalHeadL,reducedNodalHead,ite_eq_left h,evalLaurent,map_mul,map_constantL]
    rw [sineL_map _ _ (pow_ne_zero _ phase_ne_zero),map_monomialL_neg_variable]
    change constF n 4*constF n c*torusSin (constF n (phase^3)*(variableF i)⁻¹)=_
    simp only [constF,map_ofNat,map_pow,div_eq_mul_inv]
  · simp only [nodalHeadL,reducedNodalHead,ite_eq_right h,evalLaurent,map_add,map_constantL]
    change evalLaurent (cosineL _ _)+evalLaurent (cosineL _ _)+constF n rho=_
    rw [←deletionBeta_laurent]
    congr 2
    rw [cosineL_map _ _ (zpow_ne_zero _ phase_ne_zero),map_monomialL_two_variable]
    change torusCos (constF n (phase^(-3:ℤ))*variableF i^2)=torusCos (variableF i^2/constF n phase^3)
    congr 1
    simp only [constF,zpow_neg,zpow_ofNat,map_inv₀,map_pow]
    ring

def reflectionFactorL {n : ℕ} (i j : Fin n) : Laurent n :=
  if j=i then 1 else sineL (variableExponent i+variableExponent j) (phase^3)

lemma reflectionFactorL_map {n : ℕ} (i j : Fin n) :
    evalLaurent (reflectionFactorL i j)=reflectionFactor i j := by
  by_cases h:j=i
  · simp [reflectionFactorL,reflectionFactor,h,evalLaurent]
  · simp only [reflectionFactorL,reflectionFactor,ite_eq_right h]
    change (algebraMap (SpectralRing n) (SpectralField n)) (sineL _ _)=_
    rw [sineL_map _ _ (pow_ne_zero _ phase_ne_zero)]
    change torusSin (evalLaurent (monomialL _ _))=_
    rw [map_monomialL_add_variable]
    simp only [constF,map_pow]



lemma pairBound_add {n:ℕ} (i j:Fin n) (h:j≠i) (k:Fin n) :
    -(pairBound i j k:ℤ)≤(variableExponent i+variableExponent j) k ∧
      (variableExponent i+variableExponent j) k ≤ pairBound i j k := by
  by_cases hki:k=i <;> by_cases hkj:k=j
  all_goals simp_all [pairBound,variableExponent]

lemma pairBound_sub {n:ℕ} (i j k:Fin n) :
    -(pairBound i j k:ℤ)≤(variableExponent i-variableExponent j) k ∧
      (variableExponent i-variableExponent j) k ≤ pairBound i j k := by
  by_cases hij:j=i <;> by_cases hki:k=i <;> by_cases hkj:k=j
  all_goals simp_all [pairBound,variableExponent]

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_CramerBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram





noncomputable section
open scoped Classical LaurentPolynomial

lemma constants_extreme_nonzero (n:ℕ) :
    constF n (phase^3/2)≠0 ∧ constF n ((phase^3)⁻¹/2)≠0 := by
  constructor
  · exact (map_ne_zero (algebraMap ℂ (SpectralField n))).mpr (div_ne_zero (pow_ne_zero _ phase_ne_zero) (by norm_num))
  · exact (map_ne_zero (algebraMap ℂ (SpectralField n))).mpr (div_ne_zero (inv_ne_zero (pow_ne_zero _ phase_ne_zero)) (by norm_num))

end





noncomputable section
open scoped Classical
open Finset


def inlinePrivate156_tileWest : Tile → Bool
  | .vertical₁ | .diagonal₁ | .cap | .verticalPair | .capCup => true
  | _ => false
def inlinePrivate156_tileEast : Tile → Bool
  | .vertical₀ | .diagonal₁ | .cup | .verticalPair | .capCup => true
  | _ => false
lemma inlinePrivate156_tileWest_iff (t : Tile) : t.Occupied 1 ↔ inlinePrivate156_tileWest t=true := by
  cases t <;> unfold Tile.Occupied Tile.Adj Tile.edges inlinePrivate156_tileWest <;> decide
lemma inlinePrivate156_tileEast_iff (t : Tile) : t.Occupied 2 ↔ inlinePrivate156_tileEast t=true := by
  cases t <;> unfold Tile.Occupied Tile.Adj Tile.edges inlinePrivate156_tileEast <;> decide

lemma Weights.signTwist_tile {K : Type*} [CommRing K] (w : Weights K) (t : Tile) :
    w.signTwist.tile t=(if t.Occupied 1 then -1 else 1)*
      (if t.Occupied 2 then -1 else 1)*w.tile t := by
  simp only [inlinePrivate156_tileWest_iff,inlinePrivate156_tileEast_iff]
  cases t <;> simp [signTwist,tile,inlinePrivate156_tileWest,inlinePrivate156_tileEast]

end

 

 

noncomputable section
open scoped Classical

lemma signSpectral_spectralWeights {n : ℕ} (i : Fin n) :
    (fun j => (spectralWeights n j).map (signSpectral i))=
      Function.update (spectralWeights n) i (spectralWeights n i).signTwist := by
  funext j
  simp only [spectralWeights,signSpectral_torusWeights,map_div₀,map_pow,signSpectral_const,
    signSpectral_variable]
  by_cases h:j=i
  · subst j
    simp only [ite_true,Function.update_self]
    have hh : constF n phase ^ 3 / -variableF i = -(constF n phase ^ 3 / variableF i) := div_neg_eq_neg_div _ _
    rw [hh,torusWeights_neg]
  · simp only [ite_eq_right h,Function.update_of_ne h]
    rfl

def doubleSignTwist {K : Type*} [Ring K] {n : ℕ} (w : Fin n → Weights K) (i j : Fin n) :=
  Function.update (Function.update w i (w i).signTwist) j (w j).signTwist

lemma signSpectral_nodalWeights {n : ℕ} (k i : Fin n) :
    (fun j => (nodalWeights i j).map (signSpectral k))=
      if i=k then doubleSignTwist (nodalWeights i) k.castSucc (Fin.last n)
      else Function.update (nodalWeights i) k.castSucc (nodalWeights i k.castSucc).signTwist := by
  funext j
  by_cases hi:i=k
  · simp only [ite_eq_left hi,doubleSignTwist]
    induction j using Fin.lastCases with
    | last =>
      simp only [nodalWeights,Fin.snoc_last,signSpectral_torusWeights,map_div₀,
        map_pow,signSpectral_const,signSpectral_deletionNode,ite_eq_left hi,Function.update_self]
      rw [spectral_div_neg,torusWeights_neg]
    | cast j =>
      rw [Function.update_of_ne (Fin.castSucc_ne_last j)]
      by_cases hj:j=k
      · subst j
        simp [nodalWeights,spectralWeights,map_div₀,spectral_div_neg]
      · have hj' : j.castSucc≠k.castSucc := fun h => hj (Fin.castSucc_injective n h)
        simp [nodalWeights,spectralWeights,map_div₀,hj,hj']
  · simp only [ite_eq_right hi]
    induction j using Fin.lastCases with
    | last =>
      simp only [nodalWeights,Fin.snoc_last,signSpectral_torusWeights,map_div₀,
        map_pow,signSpectral_const,signSpectral_deletionNode,ite_eq_right hi,
        Function.update_of_ne (Fin.castSucc_ne_last k).symm]
    | cast j =>
      by_cases hj:j=k
      · subst j
        simp [nodalWeights,spectralWeights,map_div₀,spectral_div_neg]
      · have hj' : j.castSucc≠k.castSucc := fun h => hj (Fin.castSucc_injective n h)
        simp [nodalWeights,spectralWeights,map_div₀,hj,hj']

def nodeSign {n : ℕ} (k i : Fin n) (p : Pairing (n+1)) : SpectralField n :=
  occupancySign p k.castSucc * (if i=k then occupancySign p (Fin.last n) else 1)

lemma nodeSign_square {n : ℕ} (k i : Fin n) (p : Pairing (n+1)) :
    nodeSign k i p*nodeSign k i p=1 := by
  unfold nodeSign
  split_ifs
  · rw [mul_mul_mul_comm,occupancySign_mul_self,occupancySign_mul_self,one_mul]
  · simp

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_NodalExchange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram





noncomputable section

theorem torus_sine_pair {n : ℕ} (z : SpectralField n) (hz : z ≠ 0) :
    2 * torusSin z * torusSin (constF n phase ^ 3 / z) =
      torusCos (z^2 / constF n phase ^ 3) - constF n c := by
  have hq := constF_phase_ne_zero n
  rw [torusSin_product _ _ hz (div_ne_zero (pow_ne_zero _ hq) hz)]
  have h₁ : z / (constF n phase ^ 3 / z) = z^2 / constF n phase ^ 3 := by field_simp
  have h₂ : z * (constF n phase ^ 3 / z) = constF n phase ^ 3 := by field_simp
  rw [h₁, h₂, torusCos_phase_pow]
  rfl

theorem torus_twice_denominator {n : ℕ} (z : SpectralField n) (hz : z ≠ 0) :
    2 * torusL (constF n phase ^ 3 / z) =
      torusCos (z^2 / constF n phase ^ 3) + constF n C := by
  have hq := constF_phase_ne_zero n
  have h₅ : constF n phase ^ 2 * (constF n phase ^ 3 / z) = constF n phase ^ 5 / z := by ring
  have h₆ : constF n phase ^ 3 * (constF n phase ^ 3 / z) = constF n phase ^ 6 / z := by ring
  rw [torusL, h₅, h₆, ← mul_assoc, torusSin_product _ _
    (div_ne_zero (pow_ne_zero _ hq) hz) (div_ne_zero (pow_ne_zero _ hq) hz)]
  have hdiv : (constF n phase ^ 5 / z) / (constF n phase ^ 6 / z) =
      (constF n phase)⁻¹ := by field_simp
  have hmul : (constF n phase ^ 5 / z) * (constF n phase ^ 6 / z) =
      -(z^2 / constF n phase ^ 3)⁻¹ := by
    have h := constF_phase_eight n
    field_simp
    exact h
  rw [hdiv, hmul, torusCos_inv, torusCos_neg, torusCos_inv,
    ← pow_one (constF n phase), torusCos_phase_pow]
  simp only [Nat.cast_one, one_mul, sub_neg_eq_add]
  rw [add_comm]
  rfl

theorem torus_last_cleared {n : ℕ} (z : SpectralField n) (hz : z ≠ 0)
    (hL : torusL (constF n phase ^ 3 / z) ≠ 0) :
    let b := torusCos (z^2 / constF n phase ^ 3)
    let r := fun t => (b + constF n C) * (torusWeights (constF n phase^3/z)).tile t
    r .vacant = b + constF n C ∧
    r .cap = 2 * constF n d * torusSin (constF n phase^3/z) ∧
    r .vertical₀ = 2 * constF n d * torusSin z ∧
    r .diagonal₁ = b - constF n c := by
  dsimp only
  rw [← torus_twice_denominator z hz]
  have hq := constF_phase_ne_zero n
  have h₃ : constF n phase^3 / (constF n phase^3/z) = z := by field_simp
  simp only [torusWeights, Weights.tile, mul_one, h₃]
  constructor
  · trivial
  constructor
  · field_simp
  constructor
  · field_simp
  · rw [← torus_sine_pair z hz]
    field_simp






open Finset
open scoped Classical



end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_Specialization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



 

namespace CriticalStrip.Diagram





noncomputable section
open Finset



theorem rationalAt_const {n k : ℕ} (φ : Laurent n →ₐ[ℂ] SpectralField k) (c : ℂ) :
    RationalAt φ.toRingHom (constF n c) (constF k c) := by
  have h := RationalAt.algebraMap (φ := φ.toRingHom) (F := SpectralField n) (constantL n c)
  rw [map_constantL] at h
  have he : φ (constantL n c) = constF k c := φ.commutes c
  simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, he] using h

theorem rationalAt_variable {n k : ℕ} (z : Fin n → SpectralField k)
    (hz : ∀ i, z i ≠ 0) (i : Fin n) :
    RationalAt (torusEvaluation z hz).toRingHom (variableF i) (z i) := by
  have h := RationalAt.algebraMap (φ := (torusEvaluation z hz).toRingHom)
    (F := SpectralField n) (monomialL (variableExponent i) 1)
  change RationalAt (torusEvaluation z hz).toRingHom (variableF i)
    (torusEvaluation z hz (monomialL (variableExponent i) 1)) at h
  simpa only [torusEvaluation_variable] using h

theorem rationalAt_torusSin {n k : ℕ} (φ : Laurent n →ₐ[ℂ] SpectralField k)
    {x : SpectralField n} {z : SpectralField k}
    (h : RationalAt φ.toRingHom x z) (hz : z ≠ 0) :
    RationalAt φ.toRingHom (torusSin x) (torusSin z) := by
  have hc : constF k (2*Complex.I) ≠ 0 := by
    apply (map_ne_zero (algebraMap ℂ (SpectralField k))).mpr
    exact mul_ne_zero (by norm_num) Complex.I_ne_zero
  have hd : RationalAt φ.toRingHom (2 * constF n Complex.I) (2 * constF k Complex.I) :=
    (RationalAt.natCast 2).mul (rationalAt_const φ Complex.I)
  apply (h.sub (h.inv hz)).div hd
  simpa only [constF, map_mul, map_ofNat] using hc

theorem rationalAt_torusCos {n k : ℕ} (φ : Laurent n →ₐ[ℂ] SpectralField k)
    {x : SpectralField n} {z : SpectralField k}
    (h : RationalAt φ.toRingHom x z) (hz : z ≠ 0) :
    RationalAt φ.toRingHom (torusCos x) (torusCos z) := by
  exact (h.add (h.inv hz)).div (RationalAt.natCast 2) (by exact two_ne_zero)

theorem rationalAt_torusL {n k : ℕ} (φ : Laurent n →ₐ[ℂ] SpectralField k)
    {x : SpectralField n} {z : SpectralField k}
    (h : RationalAt φ.toRingHom x z) (hz : z ≠ 0) :
    RationalAt φ.toRingHom (torusL x) (torusL z) := by
  exact (rationalAt_torusSin φ (((rationalAt_const φ phase).pow 2).mul h)
    (mul_ne_zero (pow_ne_zero _ (constF_phase_ne_zero k)) hz)).mul
    (rationalAt_torusSin φ (((rationalAt_const φ phase).pow 3).mul h)
      (mul_ne_zero (pow_ne_zero _ (constF_phase_ne_zero k)) hz))

theorem rationalAt_torusWeights {n k : ℕ} (φ : Laurent n →ₐ[ℂ] SpectralField k)
    {x : SpectralField n} {z : SpectralField k}
    (h : RationalAt φ.toRingHom x z) (hz : z ≠ 0) (hL : torusL z ≠ 0) (t : Tile) :
    RationalAt φ.toRingHom ((torusWeights x).tile t) ((torusWeights z).tile t) := by
  have hq := rationalAt_const φ phase
  have hd := rationalAt_const φ d
  have hs := rationalAt_torusSin φ h hz
  have ht := rationalAt_torusSin φ ((hq.pow 3).div h hz)
    (div_ne_zero (pow_ne_zero _ (constF_phase_ne_zero k)) hz)
  have hv := rationalAt_torusSin φ ((hq.pow 2).div h hz)
    (div_ne_zero (pow_ne_zero _ (constF_phase_ne_zero k)) hz)
  have hu := rationalAt_torusSin φ (h.div hq (constF_phase_ne_zero k))
    (div_ne_zero hz (constF_phase_ne_zero k))
  have hden := rationalAt_torusL φ h hz
  cases t
  · exact RationalAt.one
  · exact (hd.mul ht).div hden hL
  · exact (hd.mul ht).div hden hL
  · exact (hs.mul ht).div hden hL
  · exact (hs.mul ht).div hden hL
  · exact (hd.mul hs).div hden hL
  · exact (hd.mul hs).div hden hL
  · exact (ht.mul hv).div hden hL
  · exact (hu.mul hs).div hden hL

end

 

 

noncomputable section
open scoped Classical

def copiedNodeWeights {m n : ℕ} (v : Fin m → Fin n) (i : Fin n) :
    Fin (m+1) → Weights (SpectralField n) :=
  Fin.snoc (fun j => spectralWeights n (v j)) (torusWeights (variableF i)⁻¹)



def copyEvaluation {m n : ℕ} (v : Fin m → Fin n) : Laurent m →ₐ[ℂ] SpectralField n :=
  torusEvaluation (fun j => variableF (v j)) (fun j => variableF_ne_zero (v j))

lemma rationalAt_copy_variable {m n : ℕ} (v : Fin m → Fin n) (i : Fin m) :
    RationalAt (copyEvaluation v).toRingHom (variableF i) (variableF (v i)) :=
  rationalAt_variable _ _ i

lemma rationalAt_copy_deletionNode {m n : ℕ} (v : Fin m → Fin n) (i : Fin m) :
    RationalAt (copyEvaluation v).toRingHom (deletionNode i) (deletionNode (v i)) :=
  (rationalAt_copy_variable v i).mul ((rationalAt_const (copyEvaluation v) phase).pow 3)

lemma rationalAt_copy_spectralA {m n : ℕ} (v : Fin m → Fin n) (i : Fin m) :
    RationalAt (copyEvaluation v).toRingHom (spectralA i) (spectralA (v i)) := by
  apply rationalAt_torusCos
  · exact ((rationalAt_copy_variable v i).pow 2).div
      ((rationalAt_const (copyEvaluation v) phase).pow 3) (pow_ne_zero _ (constF_phase_ne_zero n))
  · exact div_ne_zero (pow_ne_zero _ (variableF_ne_zero (v i))) (pow_ne_zero _ (constF_phase_ne_zero n))

lemma rationalAt_copy_deletionBeta {m n : ℕ} (v : Fin m → Fin n) (i : Fin m) :
    RationalAt (copyEvaluation v).toRingHom (deletionBeta i) (deletionBeta (v i)) := by
  apply rationalAt_torusCos
  · exact ((rationalAt_copy_deletionNode v i).pow 2).div
      ((rationalAt_const (copyEvaluation v) phase).pow 3) (pow_ne_zero _ (constF_phase_ne_zero n))
  · exact div_ne_zero (pow_ne_zero _ (mul_ne_zero (variableF_ne_zero (v i))
      (pow_ne_zero _ (constF_phase_ne_zero n)))) (pow_ne_zero _ (constF_phase_ne_zero n))

lemma rationalAt_copy_weights {m n : ℕ} (v : Fin m → Fin n) (i : Fin m)
    (j : Fin (m+1)) (t : Tile) :
    RationalAt (copyEvaluation v).toRingHom ((nodalWeights i j).tile t)
      ((copiedNodeWeights v (v i) j).tile t) := by
  induction j using Fin.lastCases with
  | cast j =>
    simp only [nodalWeights,copiedNodeWeights,Fin.snoc_castSucc,spectralWeights]
    apply rationalAt_torusWeights
    · exact ((rationalAt_const (copyEvaluation v) phase).pow 3).div
        (rationalAt_copy_variable v j) (variableF_ne_zero _)
    · exact div_ne_zero (pow_ne_zero _ (constF_phase_ne_zero n)) (variableF_ne_zero _)
    · rw [←rowDenominator_map]
      exact rowDenominator_map_ne_zero _
  | last =>
    simp only [nodalWeights_last,copiedNodeWeights,Fin.snoc_last]
    apply rationalAt_torusWeights
    · exact (rationalAt_copy_variable v i).inv (variableF_ne_zero _)
    · exact inv_ne_zero (variableF_ne_zero _)
    · rw [←inverseRowDenominator_map]
      exact inverseRowDenominator_map_ne_zero _







lemma RationalAt.mv_eval {R F K C σ : Type*} [CommRing R] [IsDomain R]
    [Field F] [Field K] [Algebra R F] [IsFractionRing R F] [CommRing C]
    {φ : R →+* K} (c : C →+* F) (d : C →+* K) (v : σ → F) (w : σ → K)
    (hc : ∀ z,RationalAt φ (c z) (d z)) (hv : ∀ i,RationalAt φ (v i) (w i))
    (p : MvPolynomial σ C) :
    RationalAt φ (MvPolynomial.eval₂Hom c v p) (MvPolynomial.eval₂Hom d w p) := by
  induction p using MvPolynomial.induction_on with
  | C z => simpa using hc z
  | add p q hp hq => simpa only [map_add] using hp.add hq
  | mul_X p i hp => simpa only [map_mul,MvPolynomial.eval₂Hom_X'] using hp.mul (hv i)

end

 

 

noncomputable section
open scoped Classical LaurentPolynomial

def evalMonomialCharacter (n : ℕ) : Multiplicative (Fin n → ℤ) →* SpectralField n where
  toFun e:=evalLaurent (monomialL e.toAdd 1)
  map_one' := by simp [evalLaurent]
  map_mul' e f:=by
    change evalLaurent (monomialL (e.toAdd+f.toAdd) 1)=_
    simp only [evalLaurent]
    rw [←map_mul]
    simp only [monomialL_mul,mul_one]

lemma evalLaurent_monomial_product {n : ℕ} (e : Fin n → ℤ) (z : ℂ) :
    evalLaurent (monomialL e z)=constF n z*∏ i,variableF i ^ e i := by
  rw [evalLaurent,map_monomialL_factor]
  congr 1
  have he : e=∑ i:Fin n,(e i) • variableExponent i := by
    funext j
    simp [variableExponent,Pi.single_apply]
  change evalMonomialCharacter n (Multiplicative.ofAdd e)=_
  rw [he]
  simp only [ofAdd_sum,map_prod,ofAdd_zsmul,map_zpow]
  rw [←he]
  rfl

lemma evalLaurent_unit_zpow {n : ℕ} (u : (Laurent n)ˣ) (k : ℤ) :
    evalLaurent ((u^k : (Laurent n)ˣ):Laurent n)=(evalLaurent (u:Laurent n))^k :=
  ((algebraMap (SpectralRing n) (SpectralField n)).toMonoidHom.comp (Units.coeHom _)).map_zpow u k

lemma substituteLaurent_monomial {n : ℕ} (i : Fin (n+1)) (u : (Laurent n)ˣ)
    (e : Fin (n+1) → ℤ) (z : ℂ) :
    substituteLaurent i u (monomialL e z)=monomialL (Fin.removeNth i e) z * (u^(e i):(Laurent n)ˣ) := by
  change LaurentPolynomial.eval₂ (RingHom.id _) u (peelLaurentEquiv i _)=_
  rw [peelLaurentEquiv_monomial,LaurentPolynomial.single_eq_C_mul_T,LaurentPolynomial.eval₂_C_mul_T]
  rfl

lemma substitution_torusEvaluation {n : ℕ} (i : Fin (n+1)) (u : (Laurent n)ˣ)
    (v : Fin (n+1) → SpectralField n) (hv:∀ j,v j≠0)
    (hi:v i=evalLaurent (u:Laurent n)) (hj:∀ j,v (i.succAbove j)=variableF j) (f : Laurent (n+1)) :
    torusEvaluation v hv f=evalLaurent (substituteLaurent i u f) := by
  have h:(torusEvaluation v hv).toRingHom=
      (algebraMap (SpectralRing n) (SpectralField n)).comp (substituteLaurent i u) := by
    apply AddMonoidAlgebra.ringHom_ext <;> intro e
    all_goals change torusEvaluation v hv (monomialL _ _)=evalLaurent (substituteLaurent i u (monomialL _ _))
    all_goals rw [torusEvaluation_monomial,substituteLaurent_monomial]
    all_goals simp only [evalLaurent,map_mul]
    all_goals rw [←evalLaurent,evalLaurent_monomial_product,←evalLaurent,evalLaurent_unit_zpow]
    all_goals rw [Fin.prod_univ_succAbove _ i]
    all_goals simp only [hi,hj,Fin.removeNth]
    all_goals ring
  exact DFunLike.congr_fun h f

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_CollisionSubstitutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped LaurentPolynomial Classical

def collisionSubstitution {n : ℕ} (i : Fin (n+1)) (j : Fin n) (k : Fin 4) :
    Laurent (n+1) →+* Laurent n :=
  substituteLaurent i (cosineCollisionRoots
    (constantUnit n (phase^3) (pow_ne_zero _ phase_ne_zero)) (variableUnit j) k)

lemma collisionSubstitution_beta_self {n : ℕ} (i : Fin (n+1)) (j : Fin n) (k : Fin 4) :
    collisionSubstitution i j k (betaL i)=betaL j := by
  have h:=cosineCollisionPacket_eval_root
    (constantUnit n (phase^3) (pow_ne_zero _ phase_ne_zero)) (variableUnit j) k
  rw [cosineCollisionPacket_betaL i j,map_mul,map_ofNat] at h
  have hzero : collisionSubstitution i j k (betaL i-betaL (i.succAbove j))=0 := by
    exact (mul_eq_zero.mp h).resolve_left (by
      intro hz
      have h:=congrArg (algebraMap (SpectralRing n) (SpectralField n)) hz
      simp only [map_ofNat,map_zero] at h
      exact (two_ne_zero : (2 : SpectralField n)≠0) h)
  rw [map_sub] at hzero
  have ho : collisionSubstitution i j k (betaL (i.succAbove j))=betaL j := by
    rw [←insert_betaL i j]
    exact substituteLaurent_insert _ _ _
  rw [ho] at hzero
  exact sub_eq_zero.mp hzero

lemma collisionSubstitution_beta {n : ℕ} (i : Fin (n+1)) (j : Fin n) (k : Fin 4) (l : Fin (n+1)) :
    collisionSubstitution i j k (betaL l)=betaL (collisionCopy i j l) := by
  refine Fin.succAboveCases i ?_ (fun l => ?_) l
  · simpa only [collisionCopy,Fin.insertNth_apply_same] using collisionSubstitution_beta_self i j k
  · simp only [collisionCopy,Fin.insertNth_apply_succAbove,id_eq]
    rw [←insert_betaL i l]
    exact substituteLaurent_insert _ _ _

lemma collisionSubstitution_cross {n : ℕ} (i : Fin (n+1)) (j : Fin n)
    (hij : i < i.succAbove j) (e:UpperPair (n+1)) (hne:e≠⟨(i,i.succAbove j),hij⟩) (k : Fin 4) :
    collisionSubstitution i j k (betaL e.val.1-betaL e.val.2)≠0 := by
  rw [map_sub,collisionSubstitution_beta,collisionSubstitution_beta]
  apply sub_ne_zero.mpr
  intro h
  have hcopy:=cosineL_two_injective _ (pow_ne_zero 3 phase_ne_zero) h
  rcases collisionCopy_eq i j e.val.1 e.val.2 (ne_of_lt e.property) hcopy with h | h
  · apply hne
    exact Subtype.ext (Prod.ext h.1 h.2)
  · have he:=e.property
    rw [h.1,h.2] at he
    exact lt_asymm hij he

end

 

 

noncomputable section
open scoped Classical

lemma copyEvaluation_collision {n : ℕ} (i : Fin (n+1)) (j : Fin n) (f : Laurent (n+1)) :
    copyEvaluation (collisionCopy i j) f=evalLaurent (substituteLaurent i (variableUnit j) f) := by
  apply substitution_torusEvaluation
  · simp only [collisionCopy,Fin.insertNth_apply_same]
    rfl
  · intro k
    simp only [collisionCopy,Fin.insertNth_apply_succAbove,id_eq]

lemma substitute_reflection_sine {n : ℕ} (i : Fin (n+1)) (j : Fin n) :
    substituteLaurent i (reflectionUnit j)
      (sineL (variableExponent i+variableExponent (i.succAbove j)) (phase^3))=0 := by
  have hrem : Fin.removeNth i (variableExponent i+variableExponent (i.succAbove j))=variableExponent j := by
    funext k
    simp [Fin.removeNth,variableExponent,Pi.single_apply,Fin.succAbove_ne]
  have he : (variableExponent i+variableExponent (i.succAbove j)) i=1 := by
    simp [variableExponent,(Fin.succAbove_ne i j).symm]
  have hremn : Fin.removeNth i (-(variableExponent i+variableExponent (i.succAbove j)))= -variableExponent j := by
    funext k
    change -(Fin.removeNth i (variableExponent i+variableExponent (i.succAbove j)) k)=_
    rw [hrem]; rfl
  rw [sineL,map_mul]
  suffices h : substituteLaurent i (reflectionUnit j)
      (monomialL (variableExponent i+variableExponent (i.succAbove j)) (phase^3) -
       monomialL (-(variableExponent i+variableExponent (i.succAbove j))) ((phase^3)⁻¹))=0 by
    rw [h,zero_mul]
  rw [map_sub,substituteLaurent_monomial,substituteLaurent_monomial]
  simp only [hrem,hremn,he,Pi.neg_apply,zpow_one,zpow_neg_one,reflectionUnit_coe,
    reflectionUnit_inv_coe,monomialL_mul,add_neg_cancel,neg_add_cancel]
  apply sub_eq_zero.mpr
  congr 1
  field_simp [phase_ne_zero]

lemma reflectionFactorL_collision_left {n : ℕ} (i : Fin (n+1)) (j : Fin n) :
    substituteLaurent i (reflectionUnit j) (reflectionFactorL i (i.succAbove j))=0 := by
  rw [reflectionFactorL,ite_eq_right (Fin.succAbove_ne i j)]
  exact substitute_reflection_sine i j

lemma reflectionFactorL_collision_right {n : ℕ} (i : Fin (n+1)) (j : Fin n) :
    substituteLaurent i (reflectionUnit j) (reflectionFactorL (i.succAbove j) i)=0 := by
  rw [reflectionFactorL,ite_eq_right (Fin.succAbove_ne i j).symm,
    add_comm (variableExponent (i.succAbove j)) (variableExponent i)]
  exact substitute_reflection_sine i j







lemma substituteLaurent_neg_sign_monomial {n : ℕ} (i : Fin (n+1)) (u : (Laurent n)ˣ)
    (e : Fin (n+1) → ℤ) (z : ℂ) :
    substituteLaurent i (-u) (monomialL e z)=substituteLaurent i u (signLaurent i (monomialL e z)) := by
  rw [signLaurent_monomial,substituteLaurent_monomial,substituteLaurent_monomial]
  apply IsFractionRing.injective (SpectralRing n) (SpectralField n)
  change evalLaurent (_ * _)=evalLaurent (_ * _)
  simp only [evalLaurent,map_mul]
  rw [←evalLaurent,evalLaurent_monomial_product,←evalLaurent,evalLaurent_unit_zpow,
    ←evalLaurent,evalLaurent_monomial_product,←evalLaurent,evalLaurent_unit_zpow]
  simp only [Units.val_neg,evalLaurent,map_neg,constF,map_mul,map_zpow₀,map_neg,map_one]
  rw [neg_eq_neg_one_mul,mul_zpow]
  ring

lemma substituteLaurent_neg_sign {n : ℕ} (i : Fin (n+1)) (u : (Laurent n)ˣ) (f:Laurent (n+1)) :
    substituteLaurent i (-u) f=substituteLaurent i u (signLaurent i f) := by
  have h:(substituteLaurent i (-u))=(substituteLaurent i u).comp (signLaurent i) := by
    apply AddMonoidAlgebra.ringHom_ext
    · intro z
      exact substituteLaurent_neg_sign_monomial i u 0 z
    · intro e
      exact substituteLaurent_neg_sign_monomial i u e 1
  exact DFunLike.congr_fun h f







def upperPairOther {n : ℕ} (e : UpperPair (n+1)) : Fin n :=
  (Fin.exists_succAbove_eq (ne_of_gt e.property)).choose

lemma upperPairOther_spec {n : ℕ} (e : UpperPair (n+1)) :
    e.val.1.succAbove (upperPairOther e)=e.val.2 :=
  (Fin.exists_succAbove_eq (ne_of_gt e.property)).choose_spec

def edgeSubstitution {n : ℕ} (e : UpperPair (n+1)) (k : Fin 4) :
    Laurent (n+1) →+* Laurent n := collisionSubstitution e.val.1 (upperPairOther e) k

lemma edgeSubstitution_kernel {n : ℕ} (e : UpperPair (n+1)) (f : Laurent (n+1))
    (hf:∀ k,edgeSubstitution e k f=0) : (betaL e.val.2-betaL e.val.1) ∣ f := by
  obtain ⟨g,hg⟩:=betaL_difference_dvd e.val.1 (upperPairOther e) f hf
  rw [upperPairOther_spec] at hg
  refine ⟨-g,?_⟩
  rw [hg]
  ring

lemma edgeSubstitution_cross {n : ℕ} (e f : UpperPair (n+1)) (hef:e≠f) (k : Fin 4) :
    edgeSubstitution e k (betaL f.val.2-betaL f.val.1)≠0 := by
  have he:e.val.1<e.val.1.succAbove (upperPairOther e) := by rw [upperPairOther_spec]; exact e.property
  have hne:f≠⟨(e.val.1,e.val.1.succAbove (upperPairOther e)),he⟩ := by
    intro hh
    apply hef
    apply Subtype.ext
    have hv:=congrArg Subtype.val hh
    simpa only [upperPairOther_spec] using hv.symm
  have hh:=collisionSubstitution_cross e.val.1 (upperPairOther e) he f hne k
  intro hz
  rw [map_sub] at hh hz
  exact hh (sub_eq_zero.mpr (sub_eq_zero.mp hz).symm)



end





end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_SpecializationPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical







lemma liftLaurent_eq_insert {n:ℕ} (P:Laurent n) : liftLaurent P=insertLaurent (Fin.last n) P := by
  have he:liftLaurentHom n=insertLaurent (Fin.last n) := by
    apply AddMonoidAlgebra.ringHom_ext <;> intro e
    all_goals change liftLaurent (monomialL _ _)=insertLaurent (Fin.last n) (monomialL _ _)
    all_goals rw [liftLaurent_monomial,insertLaurent_monomial]
    all_goals congr 1
    all_goals ext i; induction i using Fin.lastCases <;> simp
  exact DFunLike.congr_fun he P

lemma lastExponent_eq_smul (n:ℕ) (a:ℤ) : lastExponent n a=a • variableExponent (Fin.last n) := by
  ext i
  induction i using Fin.lastCases <;> simp [lastExponent,variableExponent]

lemma lastCosine_eq (n:ℕ) : lastCosine n=cosineL ((2:ℤ) • variableExponent (Fin.last n)) (phase^3)⁻¹ := by
  unfold lastCosine cosineL
  rw [lastExponent_eq_smul,lastExponent_eq_smul]
  simp only [zpow_neg,zpow_ofNat,inv_inv,neg_smul]
  rfl

lemma lastCosine_map (n:ℕ) : evalLaurent (lastCosine n)=spectralA (Fin.last n) := by
  rw [lastCosine_eq,cosineL_map _ _ (inv_ne_zero (pow_ne_zero _ phase_ne_zero)),map_monomialL_two_variable]
  simp only [constF,map_inv₀,map_pow]
  congr 1
  simp [constF,div_eq_mul_inv,mul_comm]


def lastLaurent {n:ℕ} (p:Pairing (n+1)) (P:Polynomial (Laurent n)) : Laurent (n+1) :=
  (if p.Occupied (Fin.last n) then lastSine n else 1)*P.eval₂ (liftLaurentHom n) (lastCosine n)

end





noncomputable section
open scoped Classical

lemma variableExponent_selfBound {n:ℕ} (i:Fin n) :
    ∀j,-(selfBound i 1 j:ℤ)≤variableExponent i j ∧ variableExponent i j≤ selfBound i 1 j := by
  intro j
  by_cases h:j=i <;> simp [selfBound,variableExponent,h]
lemma negVariableExponent_selfBound {n:ℕ} (i:Fin n) :
    ∀j,-(selfBound i 1 j:ℤ)≤(-variableExponent i) j ∧ (-variableExponent i) j≤ selfBound i 1 j := by
  intro j; have :=variableExponent_selfBound i j; simp only [Pi.neg_apply]; omega







lemma signLaurent_lift {n:ℕ} (i:Fin n) (f:Laurent n) :
    signLaurent i.castSucc (liftLaurent f)=liftLaurent (signLaurent i f) := by
  have he:(signLaurent i.castSucc).comp (liftLaurentHom n)=
      (liftLaurentHom n).comp (signLaurent i) := by
    apply AddMonoidAlgebra.ringHom_ext <;> intro e
    all_goals change signLaurent i.castSucc (liftLaurent (monomialL _ _))=liftLaurent (signLaurent i (monomialL _ _))
    all_goals rw [liftLaurent_monomial,signLaurent_monomial,signLaurent_monomial,liftLaurent_monomial]
    all_goals simp only [Fin.snoc_castSucc]
  exact DFunLike.congr_fun he f

end





end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_InterpolantCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

lemma permLaurent_lift {n:ℕ} (σ:Equiv.Perm (Fin n)) (f:Laurent n) :
    permLaurent (topPerm σ) (liftLaurent f)=liftLaurent (permLaurent σ f) := by
  have he:(permLaurent (topPerm σ)).comp (liftLaurentHom n)=
      (liftLaurentHom n).comp (permLaurent σ) := by
    apply AddMonoidAlgebra.ringHom_ext <;> intro e
    all_goals change permLaurent (topPerm σ) (liftLaurent (monomialL _ _))=liftLaurent (permLaurent σ (monomialL _ _))
    all_goals rw [liftLaurent_monomial,permLaurent_monomial,permLaurent_monomial,liftLaurent_monomial]
    all_goals congr 1; funext i; induction i using Fin.lastCases <;> simp [topPerm_symm]
  exact DFunLike.congr_fun he f

end

 

 

noncomputable section
open Finset


 
theorem pfaffian_eq_zero_of_equal_rows {K : Type*} [Field K] [CharZero K] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (hM : ∀ i j, M j i = -M i j)
    (a b : Fin n) (hab : a ≠ b) (hrows : ∀ j, M a j = M b j) : pfaffian M = 0 := by
  have hr (i j : Fin n) : M (Equiv.swap a b i) j = M i j := by
    by_cases hi : i = a
    · subst i; simpa using (hrows j).symm
    by_cases hi' : i = b
    · subst i; simpa using hrows j
    rw [Equiv.swap_apply_of_ne_of_ne hi hi']
  have hc (i j : Fin n) : M i (Equiv.swap a b j) = M i j := by
    rw [hM, hr, hM, neg_neg]
  have hm : (fun i j => M (Equiv.swap a b i) (Equiv.swap a b j)) = M := by
    funext i j
    rw [hr, hc]
  have h := pfaffian_reindex M (Equiv.swap a b)
  rw [hm, Equiv.Perm.sign_swap hab] at h
  simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_one_mul] at h
  have hz : (2:K)*pfaffian M = 0 := by linear_combination h
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)



theorem pfaffian_replaceFirst_add {K : Type*} [Field K] {m : ℕ}
    (M : Matrix (Fin (2*(m+1))) (Fin (2*(m+1))) K) (hM : ∀ i j, M j i = -M i j)
    (v w : Fin (2*(m+1)) → K) (hv : v 0 = 0) (hw : w 0 = 0) :
    pfaffian (replaceFirst M (v+w)) = pfaffian (replaceFirst M v) +
      pfaffian (replaceFirst M w) := by
  apply pfaffian_firstRow_add
  · exact replaceFirst_skew M hM _ (by simp [hv,hw])
  · exact replaceFirst_skew M hM v hv
  · exact replaceFirst_skew M hM w hw
  · intro j; simp
  · intro i j; simp only [replaceFirst_rest]
  · intro i j; simp only [replaceFirst_rest]

theorem pfaffian_replaceFirst_smul {K : Type*} [Field K] {m : ℕ}
    (M : Matrix (Fin (2*(m+1))) (Fin (2*(m+1))) K) (hM : ∀ i j, M j i = -M i j)
    (v : Fin (2*(m+1)) → K) (hv : v 0 = 0) (t : K) :
    pfaffian (replaceFirst M (t • v)) = t * pfaffian (replaceFirst M v) := by
  rw [pfaffian_eq_block (m := m+1) (replaceFirst M (t • v)),
    pfaffian_eq_block (m := m+1) (replaceFirst M v),
    blockSummand_sum_fixedZero _ (replaceFirst_skew M hM _ (by simp [hv])),
    blockSummand_sum_fixedZero _ (replaceFirst_skew M hM v hv)]
  simp only [blockSummand_fixZero, replaceFirst_row, replaceFirst_rest, Pi.smul_apply,
    smul_eq_mul]
  simp only [mul_left_comm _ t, mul_assoc, ← Finset.mul_sum]



theorem pfaffian_replaceFirst_otherRow {K : Type*} [Field K] [CharZero K] {m : ℕ}
    (M : Matrix (Fin (2*(m+1))) (Fin (2*(m+1))) K) (hM : ∀ i j, M j i = -M i j)
    (r : Fin (2*(m+1))) (hr : r ≠ 0) :
    pfaffian (replaceFirst M (fun j => if j = 0 then 0 else M r j)) = 0 := by
  apply pfaffian_eq_zero_of_equal_rows _ (replaceFirst_skew M hM _ (by simp)) 0 r hr.symm
  intro j
  by_cases hj : j = 0
  · subst j
    simp [replaceFirst, hr, skew_diagonal_zero M hM r]
  · simp [replaceFirst, hr, hj]

 

theorem pfaffian_firstRow_add_other {K : Type*} [Field K] [CharZero K] {m : ℕ}
    (M : Matrix (Fin (2*(m+1))) (Fin (2*(m+1))) K) (hM : ∀ i j, M j i = -M i j)
    (r : Fin (2*(m+1))) (hr : r ≠ 0) (t : K) :
    pfaffian (replaceFirst M (fun j => if j = 0 then 0 else M 0 j + t * M r j)) =
      pfaffian M := by
  let v : Fin (2*(m+1)) → K := fun j => M 0 j
  let w : Fin (2*(m+1)) → K := fun j => if j = 0 then 0 else M r j
  have hv : v 0 = 0 := skew_diagonal_zero M hM 0
  have hw : w 0 = 0 := by simp [w]
  have he : (fun j => if j = 0 then 0 else M 0 j + t * M r j) = v + t • w := by
    funext j
    by_cases hj : j = 0
    · subst j; simp [v,w,skew_diagonal_zero M hM 0]
    · simp [v,w,hj]
  apply Eq.trans (congrArg (fun x => pfaffian (replaceFirst M x)) he)
  have hw0 : pfaffian (replaceFirst M w) = 0 :=
    pfaffian_replaceFirst_otherRow M hM r hr
  rw [pfaffian_replaceFirst_add M hM v _ hv (by simp [hw]),
    pfaffian_replaceFirst_smul M hM w hw t, hw0,
    mul_zero, add_zero]
  congr 1
  funext i j
  by_cases hi : i = 0
  · subst i; simp [v]
  by_cases hj : j = 0
  · subst j; simp only [replaceFirst,hi,ite_false,ite_true,v]
    exact (hM 0 i).symm
  · simp [replaceFirst,hi,hj]








theorem pfaffian_frontBorder_scale {K : Type*} [Field K] {m : ℕ}
    (M : Matrix (Fin (2*m+1)) (Fin (2*m+1)) K) (hM : ∀ i j, M j i = -M i j) (v t : K) :
    pfaffian (frontBorder M (t*v)) = t * pfaffian (frontBorder M v) := by
  let A := frontBorder M v
  have hA := frontBorder_skew M v hM
  have he : replaceFirst A (t • (fun j => A 0 j)) = frontBorder M (t*v) := by
    funext i j
    induction i using Fin.cases <;> induction j using Fin.cases <;>
      simp [replaceFirst,A]
  have he' : replaceFirst A (fun j => A 0 j) = A := by
    funext i j
    induction i using Fin.cases <;> induction j using Fin.cases <;> simp [replaceFirst,A]
  have h := pfaffian_replaceFirst_smul A hA (fun j => A 0 j) (by simp [A]) t
  calc
    _ = pfaffian (replaceFirst A (t • (fun j => A 0 j))) := congrArg pfaffian he.symm
    _ = _ := h
    _ = _ := congrArg (fun X => t * pfaffian X) he'

 

theorem pfaffian_front_back {K : Type*} [Field K] {m : ℕ}
    (M : Matrix (Fin (2*m+1)) (Fin (2*m+1)) K) (hM : ∀ i j, M j i = -M i j) :
    pfaffian (frontBorder M 1) = pfaffian (backBorder M) := by
  have h := pfaffian_reindex (backBorder M) (finRotate (2*m+1+1)).symm
  rw [backBorder_rotate] at h
  have hs : Equiv.Perm.sign (finRotate (2*m+1+1)).symm = -1 := by
    change Equiv.Perm.sign ((finRotate (2*m+1+1))⁻¹) = -1
    rw [Equiv.Perm.sign_inv,sign_finRotate]
    simp [pow_add,pow_mul]
  rw [hs] at h
  simp only [Units.val_neg,Units.val_one,Int.cast_neg,Int.cast_one,neg_one_mul] at h
  have hv := pfaffian_frontBorder_scale M hM (1:K) (-1)
  simp only [neg_one_mul] at hv
  rw [hv] at h
  exact neg_injective h



theorem sign_tailRotateInv (n : ℕ) : Equiv.Perm.sign (tailRotateInv n) = (-1)^n := by
  rw [tailRotateInv,Equiv.Perm.decomposeFin.symm_sign,ite_eq_left rfl,one_mul]
  change Equiv.Perm.sign ((finRotate (n+1))⁻¹) = _
  rw [Equiv.Perm.sign_inv,sign_finRotate,Nat.add_sub_cancel]

 

theorem pfaffian_doubleBorder {K : Type*} [Field K] [CharZero K] {m : ℕ}
    (M : Matrix (Fin (2*m)) (Fin (2*m)) K) (hM : ∀ i j, M j i = -M i j) :
    pfaffian (frontBorder (backBorder M) 1) = pfaffian M := by
  let A := frontBorder (backBorder M) 1
  let r : Fin (2*m+2) := (Fin.last (2*m)).succ
  let v := fun j => if j = 0 then 0 else A 0 j + A r j
  let B := replaceFirst A v
  let σ := tailRotateInv (2*m)
  let T := fun i j => B (σ i) (σ j)
  have hA : ∀ i j, A j i = -A i j := frontBorder_skew _ _ (backBorder_skew M hM)
  have hv : v 0 = 0 := by simp [v]
  have hB : ∀ i j, B j i = -B i j := replaceFirst_skew A hA v hv
  have hT : ∀ i j, T j i = -T i j := fun i j => hB (σ i) (σ j)
  have hzero : ∀ j, j ≠ 1 → T 0 j = 0 := by
    intro j hj
    induction j using Fin.cases with
    | zero => simp only [T,σ,tailRotateInv_zero,B,replaceFirst_row,hv]
    | succ j =>
      induction j using Fin.cases with
      | zero => exact (hj rfl).elim
      | succ j =>
        simp only [T,σ,tailRotateInv_zero,tailRotateInv_succ_succ,B,replaceFirst_row,v,
          Fin.succ_ne_zero,ite_false,A,frontBorder_zero_succ,r,frontBorder_succ_succ,
          backBorder_last_cast,add_neg_cancel]
  have h01 : T 0 1 = 1 := by
    simp only [T,σ,tailRotateInv_zero,tailRotateInv_one,B,replaceFirst_row,v,
      Fin.succ_ne_zero,ite_false,A,frontBorder_zero_succ,r,frontBorder_succ_succ,
      backBorder_last_last,add_zero]
  have htail : (fun i j : Fin (2*m) => T i.succ.succ j.succ.succ) = M := by
    funext i j
    simp only [T,σ,tailRotateInv_succ_succ,B,replaceFirst_rest,A,
      frontBorder_succ_succ,backBorder_cast_cast]
  have hep : pfaffian T = pfaffian M := by
    have h := pfaffian_isolated T hT hzero
    apply Eq.trans h
    apply Eq.trans (congrArg (fun z => z * pfaffian (fun i j : Fin (2*m) =>
      T i.succ.succ j.succ.succ)) h01)
    rw [one_mul]
    exact congrArg pfaffian htail
  have hσ : Equiv.Perm.sign σ = 1 := by simp [σ,sign_tailRotateInv,pow_mul]
  have htp : pfaffian T = pfaffian B := by
    have h := pfaffian_reindex B σ
    change pfaffian T = _ at h
    simpa only [hσ,Units.val_one,Int.cast_one,one_mul] using h
  have hbp : pfaffian B = pfaffian A := by
    apply Eq.trans ?_ (pfaffian_firstRow_add_other A hA r (Fin.succ_ne_zero _) 1)
    congr 1
    funext i j
    simp only [B,v,one_mul,replaceFirst]
  exact hbp.symm.trans (htp.symm.trans hep)







theorem pfaffian_back_front {K : Type*} [Field K] [CharZero K] {m : ℕ}
    (M : Matrix (Fin (2*m)) (Fin (2*m)) K) (hM : ∀ i j, M j i = -M i j) (t : K) :
    pfaffian (backBorder (frontBorder M t)) = pfaffian M := by
  apply Eq.trans (congrArg pfaffian (back_front_eq_rowAdd M hM t))
  apply Eq.trans (pfaffian_firstRow_add_other _
    (frontBorder_skew _ _ (backBorder_skew M hM)) (Fin.last (2*m)).succ (Fin.succ_ne_zero _) (1-t))
  exact pfaffian_doubleBorder M hM

def plainKernel {K : Type*} [Field K] {n : ℕ} (dd rr : K) (a : Fin n → K) :
    Matrix (Fin n) (Fin n) K :=
  fun i j => (a i-a j)*(a i+a j+rr)/discriminant dd (a i) (a j)

theorem plainKernel_skew {K : Type*} [Field K] {n : ℕ} (dd rr : K) (a : Fin n → K) :
    ∀ i j, plainKernel dd rr a j i = -plainKernel dd rr a i j := by
  intro i j
  unfold plainKernel discriminant
  have hD : a j^2+a i^2+2*dd*a j*a i-dd^2 = a i^2+a j^2+2*dd*a i*a j-dd^2 := by ring
  rw [hD,← neg_div]
  congr 1
  ring

theorem pfaffian_augmented_even {K : Type*} [Field K] (m : ℕ) (dd rr : K) (a : Fin (2*m) → K) :
    pfaffian (augmentedKernel dd rr a) = pfaffian (plainKernel dd rr a) := by
  have hs : 2*m+(2*m)%2 = 2*m := by omega
  apply Eq.trans (pfaffian_cast hs (augmentedKernel dd rr a)).symm
  congr 1
  funext i j
  simp only [augmentedKernel,Fin.val_cast,i.isLt,j.isLt,dite_eq_left]
  rfl

theorem pfaffian_augmented_odd {K : Type*} [Field K] (m : ℕ) (dd rr : K) (a : Fin (2*m+1) → K) :
    pfaffian (augmentedKernel dd rr a) = pfaffian (backBorder (plainKernel dd rr a)) := by
  have hs : (2*m+1)+(2*m+1)%2 = (2*m+1)+1 := by omega
  apply Eq.trans (pfaffian_cast hs (augmentedKernel dd rr a)).symm
  congr 1
  funext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp only [augmentedKernel,Fin.val_cast,Fin.val_last,Fin.val_castSucc,
      lt_self_iff_false,dite_false,ite_true,ite_false,Fin.isLt,dite_eq_left,backBorder_last_last,
      backBorder_last_cast,backBorder_cast_last,backBorder_cast_cast,plainKernel]

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ScalarFlat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open Finset

 

theorem plainKernel_cons_flat {K : Type*} [Field K] {n : ℕ} (dd rr cc CC : K)
    (a : Fin n → K) (hshift : cc+rr = CC)
    (hroot : ∀ z, discriminant dd cc z = (z-cc)*(z+CC))
    (hfirst : ∀ i, a i ≠ cc) (hsecond : ∀ i, a i+CC ≠ 0) :
    plainKernel dd rr (Fin.cons cc a) = frontBorder (plainKernel dd rr a) (-1) := by
  have hrow : ∀ i : Fin n, plainKernel dd rr (Fin.cons cc a) 0 i.succ = -1 := by
    intro i
    simp only [plainKernel,Fin.cons_zero,Fin.cons_succ,hroot]
    have hc : cc+a i+rr = a i+CC := by rw [← hshift]; ring
    rw [hc]
    field_simp [sub_ne_zero.mpr (hfirst i),hsecond i]
    ring
  funext i j
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => simp [plainKernel]
    | succ j => exact hrow j
  | succ i =>
    induction j using Fin.cases with
    | zero =>
      rw [plainKernel_skew _ _ _ 0 i.succ,hrow]
      simp
    | succ j => rfl

 

theorem pfaffian_augmented_cons_flat {K : Type*} [Field K] [CharZero K] {n : ℕ}
    (dd rr cc CC : K) (a : Fin n → K) (hshift : cc+rr = CC)
    (hroot : ∀ z, discriminant dd cc z = (z-cc)*(z+CC))
    (hfirst : ∀ i, a i ≠ cc) (hsecond : ∀ i, a i+CC ≠ 0) :
    pfaffian (augmentedKernel dd rr (Fin.cons cc a)) =
      (-1)^n * pfaffian (augmentedKernel dd rr a) := by
  obtain ⟨m,hm|hm⟩ : ∃ m, n = 2*m ∨ n = 2*m+1 := ⟨n/2,by omega⟩
  · subst n
    rw [pfaffian_augmented_odd, pfaffian_augmented_even]
    apply Eq.trans (congrArg (fun M => pfaffian (backBorder M))
      (plainKernel_cons_flat dd rr cc CC a hshift hroot hfirst hsecond))
    rw [pfaffian_back_front _ (plainKernel_skew _ _ _)]
    simp [pow_mul]
  · subst n
    have hcast : 2*m+1+1 = 2*(m+1) := by omega
    have he := pfaffian_augmented_even (m+1) dd rr (Fin.cons cc a)
    apply Eq.trans he
    apply Eq.trans (congrArg pfaffian (plainKernel_cons_flat dd rr cc CC a hshift hroot hfirst hsecond))
    have h := pfaffian_frontBorder_scale (plainKernel dd rr a) (plainKernel_skew _ _ _) (1:K) (-1)
    simp only [neg_one_mul] at h
    apply Eq.trans h
    rw [pfaffian_front_back _ (plainKernel_skew _ _ _),pfaffian_augmented_odd]
    simp [pow_add,pow_mul]

end

 

 

noncomputable section
open scoped Classical

lemma cosineVar_ne_const {n : ℕ} (i : Fin n) (z : ℂ) :
    cosineVar i ≠ cosineConst n z := by
  intro h
  have he := (IsFractionRing.injective (CosineRing n) (CosineField n)) h
  have := congrArg (MvPolynomial.eval (fun _ : Fin n => z+1)) he
  simp at this

lemma cosineVar_injective (n : ℕ) : Function.Injective (@cosineVar n) :=
  (IsFractionRing.injective (CosineRing n) (CosineField n)).comp MvPolynomial.X_injective

lemma flat_discriminant_map {K : Type*} [CommRing K] (f : ℂ →+* K)
    (dd cc CC : ℂ) (hlin : 2*dd*cc=CC-cc) (hconst : cc^2-dd^2= -cc*CC) (z : K) :
    discriminant (f dd) (f cc) z=(z-f cc)*(z+f CC) := by
  have hl := congrArg f hlin
  have hc := congrArg f hconst
  simp only [map_mul,map_ofNat,map_sub,map_pow,map_neg] at hl hc
  unfold discriminant
  linear_combination z*hl+hc



end

 

 

noncomputable section

lemma cos_five_lambda_eq : Real.cos (5*lambda)= -c := by
  rw [show 5*lambda=Real.pi-3*lambda by simp [lambda]; ring,Real.cos_pi_sub]
  rfl

lemma discriminant_flat_complex (z : ℂ) :
    discriminant (d:ℂ) (c:ℂ) z=(z-(c:ℂ))*(z+(C:ℂ)) := by
  have h:=discriminant_cosine_roots_complex (3*lambda) z
  rw [show 3*lambda-6*lambda= -(3*lambda) by ring,Real.cos_neg,
    show 3*lambda+6*lambda=lambda+Real.pi by simp [lambda]; ring,Real.cos_add_pi] at h
  simpa only [c,C,Complex.ofReal_neg,sub_neg_eq_add] using h

lemma flat_scalar_constant : (c:ℂ)^2-(d:ℂ)^2= -(c:ℂ)*(C:ℂ) := by
  simpa [discriminant] using discriminant_flat_complex 0

lemma sin_three_lambda_pos : 0 < Real.sin (3*lambda) := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · unfold lambda
    positivity
  · unfold lambda
    linarith [Real.pi_pos]








open Finset
open scoped Classical


end





end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_FirstFlatSpecialization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram





noncomputable section
open Finset

theorem numerator_degree_bound {n : ℕ} (k : Fin n) (rr : ℂ)
    (a b : CosineRing n) (r : ℕ)
    (ha : MvPolynomial.degreeOf k a ≤ r) (hb : MvPolynomial.degreeOf k b ≤ r) :
    MvPolynomial.degreeOf k ((a-b)*(a+b+MvPolynomial.C rr)) ≤ 2*r := by
  have h₁ : MvPolynomial.degreeOf k (a-b) ≤ r :=
    (MvPolynomial.degreeOf_sub_le _ _ _).trans (max_le ha hb)
  have h₂ : MvPolynomial.degreeOf k (a+b+MvPolynomial.C rr) ≤ r := by
    refine (MvPolynomial.degreeOf_add_le _ _ _).trans (max_le ?_ ?_)
    · exact (MvPolynomial.degreeOf_add_le _ _ _).trans (max_le ha hb)
    · simp
  exact (MvPolynomial.degreeOf_mul_le _ _ _).trans (by omega)

theorem discriminant_degree_bound {n : ℕ} (k : Fin n) (dd : ℂ)
    (a b : CosineRing n) (r : ℕ)
    (ha : MvPolynomial.degreeOf k a ≤ r) (hb : MvPolynomial.degreeOf k b ≤ r) :
    MvPolynomial.degreeOf k (discriminant (MvPolynomial.C dd) a b) ≤ 2*r := by
  have he : discriminant (MvPolynomial.C dd) a b =
      a^2+b^2+MvPolynomial.C (2*dd)*(a*b)-MvPolynomial.C (dd^2) := by
    simp only [discriminant, map_mul, map_ofNat, map_pow]
    ring
  rw [he]
  refine (MvPolynomial.degreeOf_sub_le _ _ _).trans (max_le ?_ ?_)
  swap
  · simpa only [MvPolynomial.degreeOf_C] using
      (Nat.zero_le (2*r))
  refine (MvPolynomial.degreeOf_add_le _ _ _).trans (max_le ?_ ?_)
  · refine (MvPolynomial.degreeOf_add_le _ _ _).trans (max_le ?_ ?_)
    · exact (MvPolynomial.degreeOf_pow_le _ _ 2).trans (Nat.mul_le_mul_left 2 ha)
    · exact (MvPolynomial.degreeOf_pow_le _ _ 2).trans (Nat.mul_le_mul_left 2 hb)
  · exact (MvPolynomial.degreeOf_C_mul_le _ _ _).trans
      ((MvPolynomial.degreeOf_mul_le _ _ _).trans (by omega))



theorem augmentedNumerator_degree {n : ℕ} (k : Fin n) (rr : ℂ) (i j : Fin (n+n%2)) :
    MvPolynomial.degreeOf k (augmentedNumerator (MvPolynomial.C rr) MvPolynomial.X i j) ≤
      scalarEdgeDegree k i j := by
  unfold augmentedNumerator scalarEdgeDegree
  split_ifs with hi hj hd <;> try simp_all
  · apply numerator_degree_bound k rr _ _ 1 <;>
      simp only [MvPolynomial.degreeOf_X] <;> split_ifs <;> omega
  · have hki : k ≠ (⟨i.val,hi⟩ : Fin n) := by intro h; exact hd.1 (congrArg Fin.val h).symm
    have hkj : k ≠ (⟨j.val,hj⟩ : Fin n) := by intro h; exact hd.2 (congrArg Fin.val h).symm
    simpa using numerator_degree_bound k rr (MvPolynomial.X ⟨i.val,hi⟩) (MvPolynomial.X ⟨j.val,hj⟩) 0 (by simp [MvPolynomial.degreeOf_X, hki])
      (by simp [MvPolynomial.degreeOf_X, hkj])

theorem augmentedDenominator_degree {n : ℕ} (k : Fin n) (dd : ℂ) (i j : Fin (n+n%2)) :
    MvPolynomial.degreeOf k (augmentedDenominator (MvPolynomial.C dd) MvPolynomial.X i j) ≤
      scalarEdgeDegree k i j := by
  unfold augmentedDenominator scalarEdgeDegree
  split_ifs with hi hj hd <;> try simp_all
  · apply discriminant_degree_bound k dd _ _ 1 <;>
      simp only [MvPolynomial.degreeOf_X] <;> split_ifs <;> omega
  · have hki : k ≠ (⟨i.val,hi⟩ : Fin n) := by intro h; exact hd.1 (congrArg Fin.val h).symm
    have hkj : k ≠ (⟨j.val,hj⟩ : Fin n) := by intro h; exact hd.2 (congrArg Fin.val h).symm
    simpa using discriminant_degree_bound k dd (MvPolynomial.X ⟨i.val,hi⟩) (MvPolynomial.X ⟨j.val,hj⟩) 0 (by simp [MvPolynomial.degreeOf_X, hki])
      (by simp [MvPolynomial.degreeOf_X, hkj])


 

 


def incidentPair {n : ℕ} (k : Fin n) (j : {j : Fin n // j ≠ k}) : UpperPair n :=
  upperPair k j.val j.property.symm

theorem incidentPair_has_k {n : ℕ} (k : Fin n) (j : {j : Fin n // j ≠ k}) :
    (incidentPair k j).val.1 = k ∨ (incidentPair k j).val.2 = k := by
  unfold incidentPair upperPair
  split_ifs <;> simp

theorem incidentPair_range {n : ℕ} (k : Fin n) (e : UpperPair n) :
    e ∈ Set.range (incidentPair k) ↔ e.val.1 = k ∨ e.val.2 = k := by
  constructor
  · rintro ⟨j,rfl⟩
    exact incidentPair_has_k k j
  · rintro (h | h)
    · refine ⟨⟨e.val.2, by rw [← h]; exact ne_of_gt e.property⟩,?_⟩
      simp only [incidentPair, upperPair, ← h, e.property, dite_true]
    · refine ⟨⟨e.val.1, by rw [← h]; exact ne_of_lt e.property⟩,?_⟩
      have he : ¬ e.val.2 < e.val.1 := not_lt_of_ge e.property.le
      simp only [incidentPair, upperPair, ← h, he, dite_false]

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ScalarDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open Finset

theorem cosine_difference_degree_self {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    MvPolynomial.degreeOf i (MvPolynomial.X i - MvPolynomial.X j : CosineRing n) = 1 := by
  have hlt : MvPolynomial.degreeOf i (-MvPolynomial.X j : CosineRing n) <
      MvPolynomial.degreeOf i (MvPolynomial.X i : CosineRing n) := by
    simp [MvPolynomial.degreeOf_X, hij]
  simpa only [sub_eq_add_neg, MvPolynomial.degreeOf_X_self] using
    MvPolynomial.degreeOf_add_eq_of_degreeOf_lt hlt

theorem cosine_difference_degree {n : ℕ} (k i j : Fin n) (hij : i ≠ j) :
    MvPolynomial.degreeOf k (MvPolynomial.X i - MvPolynomial.X j : CosineRing n) =
      if i = k ∨ j = k then 1 else 0 := by
  by_cases hi : i = k
  · subst i
    simp [cosine_difference_degree_self k j hij]
  · by_cases hj : j = k
    · subst j
      have he : (MvPolynomial.X i - MvPolynomial.X k : CosineRing n) =
          -(MvPolynomial.X k - MvPolynomial.X i) := by ring
      rw [he, MvPolynomial.degreeOf_neg, cosine_difference_degree_self k i hij.symm]
      simp
    · rw [ite_eq_right (not_or.mpr ⟨hi,hj⟩)]
      apply Nat.eq_zero_of_le_zero
      exact (MvPolynomial.degreeOf_sub_le _ _ _).trans (by
        simp [MvPolynomial.degreeOf_X, Ne.symm hi, Ne.symm hj])

end

 

 

noncomputable section
open scoped Classical

 

def firstScalarHom {K:Type*} [CommRing K] (f:ℂ →+* K) {n:ℕ} (a:Fin n → K) :
    CosineRing (n+1) →+* Polynomial K :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp f) (Fin.cons Polynomial.X (fun i => Polynomial.C (a i)))

lemma firstScalarHom_degree {K:Type*} [CommRing K] (f:ℂ →+* K) {n:ℕ}
    (a:Fin n → K) (P:CosineRing (n+1)) :
    (firstScalarHom f a P).natDegree ≤ MvPolynomial.degreeOf 0 P := by
  conv_lhs => rw [MvPolynomial.as_sum P]
  rw [map_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m hm
  have he:firstScalarHom f a (MvPolynomial.monomial m (P.coeff m))=
      Polynomial.C (f (P.coeff m))*Polynomial.X^(m 0)*
        ∏ i:Fin n,Polynomial.C (a i)^(m i.succ) := by
    simp only [firstScalarHom,MvPolynomial.eval₂Hom_monomial,RingHom.comp_apply]
    rw [Finsupp.prod_fintype _ _ (by simp),Fin.prod_univ_succ]
    simp only [Fin.cons_zero,Fin.cons_succ,mul_assoc]
  rw [he]
  have hz:(∏i:Fin n,Polynomial.C (a i)^(m i.succ)).natDegree=0 := by
    have hh:(∏i:Fin n,Polynomial.C (a i)^(m i.succ))=Polynomial.C (∏i:Fin n,(a i)^(m i.succ)) := by
      simp only [map_prod,map_pow]
    rw [hh,Polynomial.natDegree_C]
  exact (Polynomial.natDegree_mul_le.trans (by
    rw [hz,add_zero]
    exact (Polynomial.natDegree_C_mul_le _ _).trans (Polynomial.natDegree_X_pow_le _))) |>.trans
      (MvPolynomial.le_degreeOf_of_mem_support 0 hm)

lemma polynomial_top_discriminant {K:Type*} [CommRing K] (dd a:K) :
    (discriminant (Polynomial.C dd) Polynomial.X (Polynomial.C a)).coeff 2=1 := by
  have he:discriminant (Polynomial.C dd) Polynomial.X (Polynomial.C a)=
      (Polynomial.X^2:Polynomial K)+Polynomial.C (2*dd*a)*Polynomial.X+Polynomial.C (a^2-dd^2) := by
    simp only [discriminant,map_mul,map_pow,map_sub,map_ofNat]; ring
  rw [he]
  have hc (z:K):((Polynomial.C z)^2).coeff 2=0 := by
    rw [←map_pow,Polynomial.coeff_C]; norm_num
  simp [hc]

 

def infinityNumerator {K:Type*} [CommRing K] {n:ℕ} (rr:K) (a:Fin n → K) :=
  fun i j:Fin ((n+1)+(n+1)%2) =>
    (augmentedNumerator (Polynomial.C rr) (Fin.cons Polynomial.X (fun i => Polynomial.C (a i))) i j).coeff
      (scalarEdgeDegree (0:Fin (n+1)) i j)
def infinityDenominator {K:Type*} [CommRing K] {n:ℕ} (dd:K) (a:Fin n → K) :=
  fun i j:Fin ((n+1)+(n+1)%2) =>
    (augmentedDenominator (Polynomial.C dd) (Fin.cons Polynomial.X (fun i => Polynomial.C (a i))) i j).coeff
      (scalarEdgeDegree (0:Fin (n+1)) i j)

lemma augmentedNumerator_first_degree {K:Type*} [CommRing K] (f:ℂ →+* K)
    {n:ℕ} (rr:ℂ) (a:Fin n → K) (i j:Fin ((n+1)+(n+1)%2)) :
      (augmentedNumerator (Polynomial.C (f rr)) (Fin.cons Polynomial.X (fun i => Polynomial.C (a i))) i j).natDegree ≤
        scalarEdgeDegree (0:Fin (n+1)) i j := by
    have hh: firstScalarHom f a (augmentedNumerator (MvPolynomial.C rr) MvPolynomial.X i j)=
        augmentedNumerator (Polynomial.C (f rr)) (Fin.cons Polynomial.X (fun i => Polynomial.C (a i))) i j := by
      simpa only [Matrix.map_apply,firstScalarHom,MvPolynomial.eval₂Hom_C,RingHom.comp_apply,
        MvPolynomial.eval₂Hom_X'] using
          congrFun (congrFun (map_augmentedNumerator (firstScalarHom f a) (MvPolynomial.C rr) MvPolynomial.X) i) j
    rw [←hh]
    exact (firstScalarHom_degree f a _).trans (augmentedNumerator_degree 0 rr i j)

lemma augmentedDenominator_first_degree {K:Type*} [CommRing K] (f:ℂ →+* K)
    {n:ℕ} (dd:ℂ) (a:Fin n → K) (i j:Fin ((n+1)+(n+1)%2)) :
      (augmentedDenominator (Polynomial.C (f dd)) (Fin.cons Polynomial.X (fun i => Polynomial.C (a i))) i j).natDegree ≤
        scalarEdgeDegree (0:Fin (n+1)) i j := by
    have hh: firstScalarHom f a (augmentedDenominator (MvPolynomial.C dd) MvPolynomial.X i j)=
        augmentedDenominator (Polynomial.C (f dd)) (Fin.cons Polynomial.X (fun i => Polynomial.C (a i))) i j := by
      simpa only [Matrix.map_apply,firstScalarHom,MvPolynomial.eval₂Hom_C,RingHom.comp_apply,
        MvPolynomial.eval₂Hom_X'] using
          congrFun (congrFun (map_augmentedDenominator (firstScalarHom f a) (MvPolynomial.C dd) MvPolynomial.X) i) j
    rw [←hh]
    exact (firstScalarHom_degree f a _).trans (augmentedDenominator_degree 0 dd i j)

lemma firstScalarHom_C {K:Type*} [CommRing K] (f:ℂ →+* K)
    {n:ℕ} (a:Fin n → K) (z:ℂ) : firstScalarHom f a (MvPolynomial.C z)=Polynomial.C (f z) := by
  simp only [firstScalarHom,MvPolynomial.eval₂Hom_C,RingHom.comp_apply]
lemma firstScalarHom_X {K:Type*} [CommRing K] (f:ℂ →+* K)
    {n:ℕ} (a:Fin n → K) (i:Fin (n+1)) : firstScalarHom f a (MvPolynomial.X i)=
      (Fin.cons Polynomial.X (fun i => Polynomial.C (a i)) : Fin (n+1) → Polynomial K) i := by
  simp only [firstScalarHom,MvPolynomial.eval₂Hom_X']

lemma scalarNumerator_first_map {K:Type*} [CommRing K] (f:ℂ →+* K)
    (n:ℕ) (dd rr:ℂ) (a:Fin n → K) :
    firstScalarHom f a (scalarNumerator (n+1) dd rr)=
      clearedPfaffian (Polynomial.C (f ((2^(((n+1)+(n+1)%2)/2)*
        (Nat.factorial (((n+1)+(n+1)%2)/2):ℂ))⁻¹)))
          (augmentedNumerator (Polynomial.C (f rr)) (Fin.cons Polynomial.X (fun i => Polynomial.C (a i))))
          (augmentedDenominator (Polynomial.C (f dd)) (Fin.cons Polynomial.X (fun i => Polynomial.C (a i)))) := by
  rw [scalarNumerator,map_clearedPfaffian,map_augmentedNumerator,map_augmentedDenominator]
  simp only [firstScalarHom_C,firstScalarHom_X]








def infinityKernel {K:Type*} [Field K] {n:ℕ} (dd rr:K) (a:Fin n → K) :
    Matrix (Fin ((n+1)+(n+1)%2)) (Fin ((n+1)+(n+1)%2)) K := fun i j =>
  if hi:i.val<n+1 then
    if hj:j.val<n+1 then
      if hi0:i.val=0 then
        if j.val=0 then 0 else 1
      else if hj0:j.val=0 then -1
      else plainKernel dd rr a ⟨i.val-1,by omega⟩ ⟨j.val-1,by omega⟩
    else 1
  else if j.val<n+1 then -1 else 0

lemma infinityNumerator_skew {K:Type*} [CommRing K] {n:ℕ} (rr:K) (a:Fin n → K)
    (i j:Fin ((n+1)+(n+1)%2)) :
    infinityNumerator rr a j i= -infinityNumerator rr a i j := by
  rw [infinityNumerator,infinityNumerator,scalarEdgeDegree_symm 0 j i]
  rw [←Polynomial.coeff_neg]
  congr 1
  unfold augmentedNumerator
  split_ifs <;> try ring_nf

lemma infinityDenominator_symm {K:Type*} [CommRing K] {n:ℕ} (dd:K) (a:Fin n → K)
    (i j:Fin ((n+1)+(n+1)%2)) :
    infinityDenominator dd a i j=infinityDenominator dd a j i := by
  rw [infinityDenominator,infinityDenominator,scalarEdgeDegree_symm 0 i j,
    augmentedDenominator_symm]

lemma infinityDenominator_zero_real {K:Type*} [CommRing K] {n:ℕ} (dd:K) (a:Fin n → K)
    (j:Fin ((n+1)+(n+1)%2)) (hj:j.val<n+1) (hj0:j.val≠0) :
    infinityDenominator dd a 0 j=1 := by
  have he:(⟨j.val,hj⟩:Fin (n+1))=(⟨j.val-1,by omega⟩:Fin n).succ := by ext; simp; omega
  simp only [infinityDenominator,augmentedDenominator,Fin.val_zero,Nat.zero_lt_succ,dite_eq_left,
    hj,he,Fin.cons_succ,scalarEdgeDegree,true_or,ite_true,and_self]
  exact polynomial_top_discriminant dd (a ⟨j.val-1,by omega⟩)

lemma infinityNumerator_zero_real {K:Type*} [CommRing K] {n:ℕ} (rr:K) (a:Fin n → K)
    (j:Fin ((n+1)+(n+1)%2)) (hj:j.val<n+1) (hj0:j.val≠0) :
    infinityNumerator rr a 0 j=1 := by
  have he:(⟨j.val,hj⟩:Fin (n+1))=(⟨j.val-1,by omega⟩:Fin n).succ := by ext; simp; omega
  simp only [infinityNumerator,augmentedNumerator,Fin.val_zero,Nat.zero_lt_succ,dite_eq_left,
    hj,he,Fin.cons_succ,scalarEdgeDegree,true_or,ite_true,and_self]
  exact polynomial_top_numerator rr (a ⟨j.val-1,by omega⟩)

lemma infinityDenominator_pos_real {K:Type*} [CommRing K] {n:ℕ} (dd:K) (a:Fin n → K)
    (i j:Fin ((n+1)+(n+1)%2)) (hi:i.val<n+1) (hi0:i.val≠0)
    (hj:j.val<n+1) (hj0:j.val≠0) :
    infinityDenominator dd a i j=discriminant dd (a ⟨i.val-1,by omega⟩) (a ⟨j.val-1,by omega⟩) := by
  have hei:(⟨i.val,hi⟩:Fin (n+1))=(⟨i.val-1,by omega⟩:Fin n).succ := by ext; simp; omega
  have hej:(⟨j.val,hj⟩:Fin (n+1))=(⟨j.val-1,by omega⟩:Fin n).succ := by ext; simp; omega
  simp only [infinityDenominator,augmentedDenominator,hi,hj,dite_eq_left,hei,hej,Fin.cons_succ,
    scalarEdgeDegree,Fin.val_zero,hi0,hj0,or_false,and_false,ite_false]
  have he:discriminant (Polynomial.C dd) (Polynomial.C (a ⟨i.val-1,by omega⟩))
      (Polynomial.C (a ⟨j.val-1,by omega⟩))=Polynomial.C (discriminant dd
        (a ⟨i.val-1,by omega⟩) (a ⟨j.val-1,by omega⟩)) := by
    simp only [discriminant,map_sub,map_add,map_pow,map_mul,map_ofNat]
  rw [he,Polynomial.coeff_C]; rfl

lemma infinityNumerator_pos_real {K:Type*} [CommRing K] {n:ℕ} (rr:K) (a:Fin n → K)
    (i j:Fin ((n+1)+(n+1)%2)) (hi:i.val<n+1) (hi0:i.val≠0)
    (hj:j.val<n+1) (hj0:j.val≠0) :
    infinityNumerator rr a i j=(a ⟨i.val-1,by omega⟩-a ⟨j.val-1,by omega⟩)*
      (a ⟨i.val-1,by omega⟩+a ⟨j.val-1,by omega⟩+rr) := by
  have hei:(⟨i.val,hi⟩:Fin (n+1))=(⟨i.val-1,by omega⟩:Fin n).succ := by ext; simp; omega
  have hej:(⟨j.val,hj⟩:Fin (n+1))=(⟨j.val-1,by omega⟩:Fin n).succ := by ext; simp; omega
  simp only [infinityNumerator,augmentedNumerator,hi,hj,dite_eq_left,hei,hej,Fin.cons_succ,
    scalarEdgeDegree,Fin.val_zero,hi0,hj0,or_false,and_false,ite_false]
  rw [←map_add,←map_add,←map_sub,←map_mul,Polynomial.coeff_C]; rfl

lemma infinityDenominator_fake {K:Type*} [CommRing K] {n:ℕ} (dd:K) (a:Fin n → K)
    (i j:Fin ((n+1)+(n+1)%2)) (h:¬(i.val<n+1 ∧ j.val<n+1)) :
    infinityDenominator dd a i j=1 := by
  simp only [infinityDenominator,augmentedDenominator,scalarEdgeDegree]
  split_ifs <;> simp_all

lemma infinityKernel_eq {K:Type*} [Field K] {n:ℕ} (dd rr:K) (a:Fin n → K) :
    (fun i j => infinityNumerator rr a i j/infinityDenominator dd a i j)=infinityKernel dd rr a := by
  funext i j
  by_cases hi:i.val<n+1
  · by_cases hj:j.val<n+1
    · by_cases hi0:i.val=0
      · have hie:i=0 := Fin.ext hi0
        subst i
        by_cases hj0:j.val=0
        · have hje:j=0 := Fin.ext hj0
          subst j
          simp [infinityNumerator,augmentedNumerator,infinityKernel]
        · rw [infinityNumerator_zero_real rr a j hj hj0,infinityDenominator_zero_real dd a j hj hj0]
          simp [infinityKernel,hj,hj0]
      · by_cases hj0:j.val=0
        · have hje:j=0 := Fin.ext hj0
          subst j
          rw [infinityNumerator_skew,infinityDenominator_symm,
            infinityNumerator_zero_real rr a i hi hi0,infinityDenominator_zero_real dd a i hi hi0]
          simp [infinityKernel,hi,hi0]
        · rw [infinityNumerator_pos_real rr a i j hi hi0 hj hj0,
            infinityDenominator_pos_real dd a i j hi hi0 hj hj0]
          simp [infinityKernel,hi,hj,hi0,hj0,plainKernel]
    · rw [infinityDenominator_fake dd a i j (by tauto)]
      simp [infinityNumerator,augmentedNumerator,scalarEdgeDegree,infinityKernel,hi,hj]
  · rw [infinityDenominator_fake dd a i j (by tauto)]
    by_cases hj:j.val<n+1 <;>
      simp [infinityNumerator,augmentedNumerator,scalarEdgeDegree,infinityKernel,hi,hj]

lemma infinityKernel_real {K:Type*} [Field K] {n:ℕ} (dd rr:K) (a:Fin n → K)
    (i j:Fin (n+1)) :
    infinityKernel dd rr a ⟨i.val,by omega⟩ ⟨j.val,by omega⟩ =
      frontBorder (plainKernel dd rr a) 1 i j := by
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => simp [infinityKernel]
    | succ j => simp [infinityKernel,show j.val+1<n+1 by omega]
  | succ i =>
    induction j using Fin.cases with
    | zero => simp [infinityKernel,show i.val+1<n+1 by omega]
    | succ j => simp [infinityKernel,show i.val+1<n+1 by omega,
        show j.val+1<n+1 by omega,plainKernel]

lemma pfaffian_infinityKernel {K:Type*} [Field K] [CharZero K] {n:ℕ}
    (dd rr:K) (a:Fin n → K) :
    pfaffian (infinityKernel dd rr a)=pfaffian (augmentedKernel dd rr a) := by
  obtain ⟨m,hm|hm⟩:∃m,n=2*m ∨ n=2*m+1 := ⟨n/2,by omega⟩
  · subst n
    have hs:(2*m+1)+(2*m+1)%2=(2*m+1)+1 := by omega
    apply Eq.trans (pfaffian_cast hs (infinityKernel dd rr a)).symm
    have he:(fun i j => infinityKernel dd rr a (Fin.cast hs.symm i) (Fin.cast hs.symm j))=
        backBorder (frontBorder (plainKernel dd rr a) 1) := by
      funext i j
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => simp [infinityKernel]
        | cast j => simp [infinityKernel,show j.val<2*m+1 by omega]
      | cast i =>
        induction j using Fin.lastCases with
        | last => simp [infinityKernel,show i.val<2*m+1 by omega]
        | cast j =>
          rw [backBorder_cast_cast]
          exact infinityKernel_real dd rr a i j
    rw [he,pfaffian_back_front _ (plainKernel_skew _ _ _),pfaffian_augmented_even]
  · subst n
    have hs:((2*m+1)+1)+((2*m+1)+1)%2=(2*m+1)+1 := by omega
    apply Eq.trans (pfaffian_cast hs (infinityKernel dd rr a)).symm
    have he:(fun i j => infinityKernel dd rr a (Fin.cast hs.symm i) (Fin.cast hs.symm j))=
        frontBorder (plainKernel dd rr a) 1 := by
      funext i j
      exact infinityKernel_real dd rr a i j
    rw [he,pfaffian_front_back _ (plainKernel_skew _ _ _),pfaffian_augmented_odd]


 

 


def infinityPairEmbed (n:ℕ) (e:UpperPair n) : UpperPair ((n+1)+(n+1)%2) :=
  ⟨(⟨e.val.1.val+1,by omega⟩,⟨e.val.2.val+1,by omega⟩),by simpa using e.property⟩

lemma infinityPairEmbed_injective (n:ℕ) : Function.Injective (infinityPairEmbed n) := by
  intro e f h
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext
  · have hh:=congrArg (fun e:UpperPair ((n+1)+(n+1)%2) => e.val.1.val) h
    exact Nat.add_right_cancel hh
  · have hh:=congrArg (fun e:UpperPair ((n+1)+(n+1)%2) => e.val.2.val) h
    exact Nat.add_right_cancel hh

lemma infinityDenominator_product {K:Type*} [CommRing K] {n:ℕ} (dd:K) (a:Fin n → K) :
    (∏e:UpperPair ((n+1)+(n+1)%2),infinityDenominator dd a e.val.1 e.val.2)=
      ∏e:UpperPair n,discriminant dd (a e.val.1) (a e.val.2) := by
  symm
  apply Fintype.prod_of_injective (infinityPairEmbed n) (infinityPairEmbed_injective n)
  · intro e he
    by_cases hi:e.val.1.val<n+1
    · by_cases hj:e.val.2.val<n+1
      · by_cases hi0:e.val.1.val=0
        · have hie:e.val.1=0:=Fin.ext hi0
          rw [hie]
          exact infinityDenominator_zero_real dd a e.val.2 hj (by have := e.property; simp_all; omega)
        · exfalso
          apply he
          refine ⟨⟨(⟨e.val.1.val-1,by omega⟩,⟨e.val.2.val-1,by have:=e.property; omega⟩),?_⟩,?_⟩
          · change e.val.1.val-1<e.val.2.val-1
            have:=e.property; omega
          · apply Subtype.ext; apply Prod.ext <;> apply Fin.ext <;>
              simp only [infinityPairEmbed] <;> have:=e.property <;> omega
      · exact infinityDenominator_fake dd a _ _ (by tauto)
    · exact infinityDenominator_fake dd a _ _ (by tauto)
  · intro e
    rw [infinityDenominator_pos_real dd a _ _ (by dsimp [infinityPairEmbed]; omega)
      (by simp [infinityPairEmbed]) (by dsimp [infinityPairEmbed]; omega) (by simp [infinityPairEmbed])]
    rfl

lemma infinityDenominator_ne {K:Type*} [Field K] {n:ℕ} (dd:K) (a:Fin n → K)
    (hD:∀i j,i≠j → discriminant dd (a i) (a j)≠0)
    (i j:Fin ((n+1)+(n+1)%2)) (hij:i≠j) : infinityDenominator dd a i j≠0 := by
  by_cases hi:i.val<n+1
  · by_cases hj:j.val<n+1
    · by_cases hi0:i.val=0
      · have hie:i=0:=Fin.ext hi0
        subst i
        rw [infinityDenominator_zero_real dd a j hj (by intro h; exact hij (Fin.ext h).symm)]
        exact one_ne_zero
      · by_cases hj0:j.val=0
        · have hje:j=0:=Fin.ext hj0
          subst j
          rw [infinityDenominator_symm,infinityDenominator_zero_real dd a i hi hi0]
          exact one_ne_zero
        · rw [infinityDenominator_pos_real dd a i j hi hi0 hj hj0]
          apply hD
          intro h
          have hh:=congrArg Fin.val h
          dsimp at hh
          apply hij
          apply Fin.ext
          omega
    · rw [infinityDenominator_fake dd a _ _ (by tauto)]; exact one_ne_zero
  · rw [infinityDenominator_fake dd a _ _ (by tauto)]; exact one_ne_zero

lemma firstScalarHom_vandermonde {K:Type*} [CommRing K] (f:ℂ →+* K)
    {n:ℕ} (a:Fin n → K) :
    firstScalarHom f a (sourceVandermonde (MvPolynomial.X:Fin (n+1) → CosineRing (n+1)))=
      (∏i:Fin n,(Polynomial.X-Polynomial.C (a i)))*Polynomial.C (sourceVandermonde a) := by
  rw [map_sourceVandermonde]
  simp only [firstScalarHom_X,sourceVandermonde]
  let v:Fin (n+1) → Polynomial K := Fin.cons Polynomial.X (fun i =>Polynomial.C (a i))
  have h:=prod_upperPair_succ (fun i j:Fin (n+1) => v i-v j)
  apply Eq.trans h
  simp only [v,Fin.cons_zero,Fin.cons_succ,map_prod,map_sub]

lemma firstScalarHom_vandermonde_degree {K:Type*} [CommRing K] (f:ℂ →+* K)
    {n:ℕ} (a:Fin n → K) :
    (firstScalarHom f a (sourceVandermonde (MvPolynomial.X:Fin (n+1) → CosineRing (n+1)))).natDegree ≤ n := by
  rw [firstScalarHom_vandermonde]
  apply (Polynomial.natDegree_mul_C_le _ _).trans
  exact (Polynomial.natDegree_prod_le _ _).trans ((Finset.sum_le_sum
    (fun i _ => Polynomial.natDegree_X_sub_C_le (a i))).trans (by simp))

lemma firstScalarHom_vandermonde_top {K:Type*} [CommRing K] (f:ℂ →+* K)
    {n:ℕ} (a:Fin n → K) :
    (firstScalarHom f a (sourceVandermonde (MvPolynomial.X:Fin (n+1) → CosineRing (n+1)))).coeff n=
      sourceVandermonde a := by
  rw [firstScalarHom_vandermonde,Polynomial.coeff_mul_C]
  have he:n=∑i:Fin n,(1:ℕ) := by simp
  have hh:=coeff_prod_budget Finset.univ (fun i:Fin n => (Polynomial.X-Polynomial.C (a i)))
    (fun _ => 1) (by intro i _; exact Polynomial.natDegree_X_sub_C_le _)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one,
    Polynomial.coeff_sub,Polynomial.coeff_X_one,Polynomial.coeff_C] at hh
  rw [hh]; simp



end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ScalarDeleteContinuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

section Generic
variable {K:Type*} [Field K] {n:ℕ}

lemma discriminant_genericVar_ne (dd:K) (hdd:dd≠0) (i j:Fin n) :
    discriminant (genericConst n dd) (genericVar i) (genericVar j)≠0 := by
  have he:discriminant (genericConst n dd) (genericVar i) (genericVar j)=
      algebraMap (MvPolynomial (Fin n) K) (PolynomialField K n)
        (discriminant (MvPolynomial.C dd) (MvPolynomial.X i) (MvPolynomial.X j)) := by
    simp [genericConst,genericVar,discriminant,map_ofNat]
  rw [he]
  apply (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr
  intro h
  have hh:=congrArg (MvPolynomial.eval (fun _ => (0:K))) h
  simp [discriminant,hdd] at hh

lemma discriminant_const_genericVar_ne (dd x:K) (i:Fin n) :
    discriminant (genericConst n dd) (genericConst n x) (genericVar i)≠0 := by
  have he:discriminant (genericConst n dd) (genericConst n x) (genericVar i)=
      algebraMap (MvPolynomial (Fin n) K) (PolynomialField K n)
        (discriminant (MvPolynomial.C dd) (MvPolynomial.C x) (MvPolynomial.X i)) := by
    simp [genericConst,genericVar,discriminant,map_ofNat]
  rw [he]
  apply (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr
  intro h
  have hh:=congrArg (fun P:MvPolynomial (Fin n) K =>
      (MvPolynomial.eval₂Hom Polynomial.C (fun _ => Polynomial.X) P).coeff 2) h
  simp only [discriminant,map_sub,map_add,map_mul,map_pow,map_ofNat,
    MvPolynomial.eval₂Hom_C,MvPolynomial.eval₂Hom_X',map_zero] at hh
  have hid:(Polynomial.C x)^2+Polynomial.X^2+2*Polynomial.C dd*Polynomial.C x*Polynomial.X-
      (Polynomial.C dd)^2=(Polynomial.X^2 : Polynomial K)+
        Polynomial.C (2*dd*x)*Polynomial.X+Polynomial.C (x^2-dd^2) := by
    simp only [map_mul,map_pow,map_sub,map_ofNat]; ring
  rw [hid] at hh
  have hc (z:K):((Polynomial.C z)^2).coeff 2=0 := by rw [←map_pow,Polynomial.coeff_C]; norm_num
  simp [hc] at hh

lemma generic_twoCons_inj (x y:K) (hxy:x≠y) :
    Function.Injective (twoCons (genericConst n x) (genericConst n y) (@genericVar K _ n)) := by
  have hc:genericConst n x≠genericConst n y := (genericConst n).injective.ne hxy
  intro i j h
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => rfl
    | succ j =>
      induction j using Fin.cases with
      | zero => exact (hc h).elim
      | succ j => exact (genericVar_ne_const j x h.symm).elim
  | succ i =>
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact (hc h.symm).elim
      | succ j =>
        induction j using Fin.cases with
        | zero => rfl
        | succ j => exact (genericVar_ne_const j y h.symm).elim
    | succ i =>
      induction j using Fin.cases with
      | zero => exact (genericVar_ne_const i x h).elim
      | succ j =>
        induction j using Fin.cases with
        | zero => exact (genericVar_ne_const i y h).elim
        | succ j => exact congrArg (fun k:Fin n => k.succ.succ) (genericVar_inj n h)

lemma generic_twoCons_discriminant (dd x y:K) (hdd:dd≠0)
    (i j:Fin (n+2)) (hij:i≠j)
    (hp:¬((i=0 ∧ j=1) ∨ (i=1 ∧ j=0))) :
    discriminant (genericConst n dd)
      (twoCons (genericConst n x) (genericConst n y) genericVar i)
      (twoCons (genericConst n x) (genericConst n y) genericVar j)≠0 := by
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => exact (hij rfl).elim
    | succ j =>
      induction j using Fin.cases with
      | zero => exact (hp (Or.inl ⟨rfl,by simp⟩)).elim
      | succ j => exact discriminant_const_genericVar_ne dd x j
  | succ i =>
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact (hp (Or.inr ⟨by simp,rfl⟩)).elim
      | succ j =>
        induction j using Fin.cases with
        | zero => exact (hij rfl).elim
        | succ j => exact discriminant_const_genericVar_ne dd y j
    | succ i =>
      induction j using Fin.cases with
      | zero => rw [discriminant_symm]; exact discriminant_const_genericVar_ne dd x i
      | succ j =>
        induction j using Fin.cases with
        | zero => rw [discriminant_symm]; exact discriminant_const_genericVar_ne dd y i
        | succ j => exact discriminant_genericVar_ne dd hdd i j
end Generic







lemma map_firstScalarHom {K L:Type*} [CommRing K] [CommRing L] (g:K →+* L)
    (f:ℂ →+* K) {n:ℕ} (a:Fin n → K) (P:CosineRing (n+1)) :
    (firstScalarHom f a P).map g=firstScalarHom (g.comp f) (fun i => g (a i)) P := by
  have he:(Polynomial.mapRingHom g).comp (firstScalarHom f a)=
      firstScalarHom (g.comp f) (fun i =>g (a i)) := by
    apply MvPolynomial.ringHom_ext
    · intro z
      simp only [RingHom.comp_apply,firstScalarHom_C,Polynomial.map_C,Polynomial.coe_mapRingHom]
    · intro z
      simp only [RingHom.comp_apply,firstScalarHom_X,Polynomial.coe_mapRingHom]
      induction z using Fin.cases <;> simp
  exact congrArg (fun h => h P) he



lemma eval_firstScalarHom {K:Type*} [CommRing K] (f:ℂ →+* K)
    {n:ℕ} (a:Fin n → K) (P:CosineRing (n+1)) (z:K) :
    (firstScalarHom f a P).eval z=MvPolynomial.eval₂Hom f (Fin.cons z a) P := by
  have he:(Polynomial.evalRingHom z).comp (firstScalarHom f a)=MvPolynomial.eval₂Hom f (Fin.cons z a) := by
    ext t
    · simp only [RingHom.comp_apply,firstScalarHom_C,Polynomial.coe_evalRingHom,Polynomial.eval_C,MvPolynomial.eval₂Hom_C]
    · simp only [RingHom.comp_apply,firstScalarHom_X,MvPolynomial.eval₂Hom_X',Polynomial.coe_evalRingHom]
      induction t using Fin.cases <;> simp
  exact congrArg (fun h =>h P) he

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ScalarMergeTrig
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section

lemma roots_sum {K:Type*} [Field K] (dd x y z:K)
    (h:∀t,discriminant dd x t=(t-y)*(t-z)) : y+z= -2*dd*x := by
  have h0:=h 0
  have h1:=h 1
  simp only [discriminant] at h0 h1
  linear_combination h1-h0






open scoped Classical

end





end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_PairSelfNode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

lemma pairExponent_mixed {n s:ℕ} (i j:Fin (n+2))
    (hi:pairExponent n s i≠0 ∧ pairExponent n s i≠3)
    (hj:pairExponent n s j≠0 ∧ pairExponent n s j≠3) : i=j := by
  have h₁:i=1 := by by_contra h; exact hi.2 (ite_eq_right h)
  have h₂:j=1 := by by_contra h; exact hj.2 (ite_eq_right h)
  exact h₁.trans h₂.symm







lemma twoRows_omit_one {K:Type*} {n:ℕ} (a b d e:Weights K) (w:Fin n → Weights K) :
    (fun j =>(PartialColumn.twoRows (Fin.cons a (Fin.cons b w)) 0 d e)
      ((1:Fin (n+2)).succAbove j))=Fin.cons d w := by
  funext j
  induction j using Fin.cases with
  | zero => simp [PartialColumn.twoRows,Fin.succAbove]
  | succ j => simp [PartialColumn.twoRows,Fin.succAbove,Fin.lt_def]

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_NodalTorusValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical







lemma phase_four_ne_one : phase^4≠(1:ℂ) := by
  intro h
  have hh:=congrArg (fun z:ℂ =>z^2) h
  rw [←pow_mul,show 4*2=8 by omega,phase_eight] at hh
  norm_num at hh

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ResidualParityCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical LaurentPolynomial

lemma signLaurent_coeff {n:ℕ} (i:Fin n) (f:Laurent n) (e:Fin n → ℤ) :
    (signLaurent i f).coeff e=f.coeff e*(-1:ℂ)^(e i) := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add,AddMonoidAlgebra.coeff_add,Finsupp.add_apply,hf,hg]; ring
  | single a b =>
    change (signLaurent i (monomialL a b)).coeff e=_
    rw [signLaurent_monomial]
    simp only [monomialL,AddMonoidAlgebra.coeff_single,Finsupp.single_apply]
    split_ifs with h
    · subst e; rfl
    · simp

lemma signLaurent_odd_even_coeff_zero {n:ℕ} (i:Fin n) (f:Laurent n)
    (h:signLaurent i f= -f) (e:Fin n → ℤ) (he:Even (e i)) : f.coeff e=0 := by
  have hh:=congrArg (fun g:Laurent n => g.coeff e) h
  rw [signLaurent_coeff,he.neg_one_zpow,mul_one,AddMonoidAlgebra.coeff_neg] at hh
  change f.coeff e= -f.coeff e at hh
  linear_combination (1/2:ℂ)*hh







lemma phase_primitive : IsPrimitiveRoot phase 16 := by
  have h:=Complex.isPrimitiveRoot_exp 16 (by norm_num)
  convert h using 2
  all_goals try with_reducible_and_instances rfl
  unfold phase lambda
  congr 1
  push_cast
  ring



def residualRootExponent {n:ℕ} (i:Fin n) (j:Fin (n+1)) (k:Fin 4) : Fin (n+1) → ℤ :=
  if j=i.castSucc then 0 else if j=Fin.last n ∧ 2≤k.val then -variableExponent j else variableExponent j

lemma residualRootPhase_injective {n:ℕ} (i:Fin n) (j:Fin (n+1)) :
    Function.Injective (residualRootPhase i j) := by
  intro k l h
  by_cases hi:j=i.castSucc
  · fin_cases k <;> fin_cases l <;> simp_all [residualRootPhase]
  · by_cases hj:j=Fin.last n
    · fin_cases k <;> fin_cases l <;> simp_all [residualRootPhase]
    · by_cases hlt:j.val < i.val
      · fin_cases k <;> fin_cases l <;> simp_all [residualRootPhase]
      · simp only [residualRootPhase,ite_eq_right hi,ite_eq_right hj,ite_eq_right hlt] at h
        fin_cases k <;> fin_cases l <;> simp_all

lemma residualRootExponent_support {n:ℕ} (i:Fin n) (j:Fin (n+1)) (k:Fin 4) (l:Fin (n+1)) :
    residualRootExponent i j k l≠0 ↔ j≠i.castSucc ∧ l=j := by
  unfold residualRootExponent
  split_ifs <;> simp_all [variableExponent,Pi.single_apply]

lemma residualRootExponent_index {n:ℕ} (i:Fin n) (j l:Fin (n+1)) (k r:Fin 4)
    (h:residualRootExponent i j k=residualRootExponent i l r) : j=l := by
  by_cases hj:j=i.castSucc
  · by_contra hl
    have hl':l≠i.castSucc:=by intro e; exact hl (hj.trans e.symm)
    have he:residualRootExponent i l r l≠0 := (residualRootExponent_support i l r l).mpr ⟨hl',rfl⟩
    rw [←h] at he
    exact ((residualRootExponent_support i j k l).mp he).1 hj
  · have he:residualRootExponent i j k j≠0 := (residualRootExponent_support i j k j).mpr ⟨hj,rfl⟩
    rw [h] at he
    exact ((residualRootExponent_support i l r j).mp he).2

end

 

 

noncomputable section
open scoped Classical

lemma variableExponent_injective {n:ℕ} : Function.Injective (@variableExponent n) := by
  intro i j h
  by_contra hij
  have hh:=congrFun h i
  simp [variableExponent,hij] at hh

lemma phase_more_powers :
    phase^10= -phase^2 ∧ phase^11= -phase^3 ∧ phase^13=(phase^3)⁻¹ ∧
    phase^14=(phase^2)⁻¹ ∧ phase^5= -(phase^3)⁻¹ ∧ phase^6= -(phase^2)⁻¹ := by
  have h16:phase^16=1 := by
    calc
      phase^16=(phase^8)^2 := by ring
      _=1 := by rw [phase_eight]; norm_num
  have h13:phase^13=(phase^3)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    calc
      phase^13*phase^3=phase^16 := by ring
      _=1 := h16
  have h14:phase^14=(phase^2)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    calc
      phase^14*phase^2=phase^16 := by ring
      _=1 := h16
  have h (k:ℕ):phase^(8+k)= -phase^k := by rw [pow_add,phase_eight,neg_one_mul]
  refine ⟨by simpa using h 2,by simpa using h 3,h13,h14,?_,?_⟩
  · have hh:=h 5; rw [show 8+5=13 from rfl,h13] at hh; linear_combination hh
  · have hh:=h 6; rw [show 8+6=14 from rfl,h14] at hh; linear_combination hh

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_VacuumDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram




noncomputable section
open scoped BigOperators Classical



def horizontalWeights {K : Type*} [Zero K] [One K] : Weights K := ⟨0,1,0,0,0⟩

end




end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_VacuumClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical BigOperators

namespace Tile

def transposeEquiv : Tile ≃ Tile :=
  ⟨transpose,transpose,transpose_transpose,transpose_transpose⟩

end Tile



end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ArchRoots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical BigOperators LaurentPolynomial

def archRootExponent {n : ℕ} : ArchRootIndex n → Fin (n+2) → ℤ
  | none => 0
  | some (j,b,_) => if b then -(variableExponent j.succ) else variableExponent j.succ

end




end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_DeficitBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped BigOperators

open Set MeasureTheory _root_.Matrix



def momentMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i j => ∫ x in Ioo (0 : ℝ) 1, momentBasis i.val x * transformedBasis j.val x

def basisDet (N : ℕ) (x : Fin N → ℝ) : ℝ :=
  (Matrix.of fun i j : Fin N => momentBasis i.val (x j)).det

def transformedDet (N : ℕ) (x : Fin N → ℝ) : ℝ :=
  (Matrix.of fun i j : Fin N => transformedBasis i.val (x j)).det

end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_CauchyMatrices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
section DeterminantBounds
open scoped BigOperators
open Set MeasureTheory _root_.Matrix
def boundedCauchyMatrix {N : ℕ} (x y : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i j => boundedCauchy (x i) (y j)

end DeterminantBounds

 

open Set MeasureTheory Filter
open scoped Topology

end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_PfaffianConfluentLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped BigOperators
open Set MeasureTheory



def pointwiseArchIntegrand (N : ℕ) (y : Fin N → ℝ) (x : ℝ) : ℝ :=
  (1 - reflectionProduct N x y) * omega x / x

def pointwiseArchIntegral (N : ℕ) (y : Fin N → ℝ) : ℝ :=
  ∫ x in Ioo 0 1, pointwiseArchIntegrand N y x


end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_CoordinateBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped BigOperators
open Set MeasureTheory Filter



def positiveLaw (N : ℕ) : Measure (Fin N → ℝ) :=
  (ENNReal.ofReal (normalizer N))⁻¹ •
    (volume.restrict (orderedDomain N)).withDensity (fun y => ENNReal.ofReal (density N y))

end

noncomputable section
open scoped BigOperators
open Set MeasureTheory



def lowerLikelihoodWeight (N : ℕ) (β z : ℝ) : ℝ :=
  omega (mobiusCoordinate z) * (Real.exp (β * z) / (1 + z) ^ (N + 1))



def lowerLikelihood (N : ℕ) (β : ℝ) (z : Fin N → ℝ) : ℝ :=
  (∏ i, lowerLikelihoodWeight N β (z i)) *
    ∏ i, ∏ j ∈ Finset.univ.filter (i < ·), mobiusPairFactor (z i) (z j)


def omegaLogHalf (x : ℝ) : ℝ := Real.log (omega x) + (1 / 2 : ℝ) * Real.log x

end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_WeightComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped BigOperators
open Set MeasureTheory


def upperLikelihoodWeight (β x : ℝ) : ℝ := omega x * x ^ (1 / 2 : ℝ) * Real.exp (β * x)

end

noncomputable section
open scoped BigOperators Pointwise
open Set MeasureTheory Filter


def upperLikelihood (N : ℕ) (β : ℝ) (y : Fin N → ℝ) : ℝ :=
  ∏ i, upperLikelihoodWeight β (y i)

end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ScalarBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/




namespace CriticalStrip
noncomputable section
open scoped BigOperators Classical


def translatePaths (i : ℤ) : List Triangle ≃ List Triangle where
  toFun := List.map (translateTriangle i)
  invFun := List.map (translateTriangle (-i))
  left_inv := by intro p; simp [List.map_map,Function.comp_def]
  right_inv := by intro p; simp [List.map_map,Function.comp_def]

 
def betweenArchWeight (N : ℕ) (i j : ℤ) (p : List Triangle) : ℝ :=
  if i≠j ∧ PathBetween N (up i 0) (up j 0) p then rho^p.length else 0

def betweenArchKernel (N : ℕ) (i j : ℤ) : ℝ := ∑' p, betweenArchWeight N i j p



def cutArchWeight (N : ℕ) (x : (ℕ×ℕ)×List Triangle) : ℝ :=
  betweenArchWeight N (-(x.1.1:ℤ)) ((x.1.2:ℤ)+1) x.2

end
 

 

noncomputable section
open scoped BigOperators Classical
open Filter Topology

 
def steppedDomain (N : ℕ) (s : ℤ) (v : Triangle) : Prop :=
  v.2.1 < N ∨ v.2.1=N ∧ s ≤ v.1

 

def stepArchWeight (N : ℕ) (s i j : ℤ) (p : List Triangle) : ℝ :=
  if ∀ v∈p,steppedDomain N s v then betweenArchWeight (N+1) i j p else 0

def stepArchKernel (N : ℕ) (s i j : ℤ) : ℝ := ∑' p, stepArchWeight N s i j p

def reversePaths : List Triangle ≃ List Triangle where
  toFun := List.reverse
  invFun := List.reverse
  left_inv := List.reverse_reverse
  right_inv := List.reverse_reverse


def stepCutArchWeight (N : ℕ) (s : ℤ) (x : (ℕ×ℕ)×List Triangle) : ℝ :=
  stepArchWeight N s (-(x.1.1:ℤ)) ((x.1.2:ℤ)+1) x.2

end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_BoundaryTree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/







namespace CriticalStrip.HoneycombBranch
noncomputable section
open scoped BigOperators Classical
open FiniteBranchTree


def embedTriangle (v : Triangle) : Vertex := (v.1,(v.2.1:ℤ),v.2.2)

lemma embedTriangle_injective : Function.Injective embedTriangle := by
  rintro ⟨i,j,b⟩ ⟨k,l,c⟩ h
  simp only [embedTriangle,Prod.mk.injEq] at h
  obtain ⟨rfl,hj,rfl⟩ := h
  congr
  exact_mod_cast hj

lemma adjacent_iff (v w : Triangle) :
    adjacent v w ↔ ∃ p : Fin 3, neighbor (embedTriangle v) p = embedTriangle w := by
  rcases v with ⟨i,j,b⟩
  rcases w with ⟨k,l,c⟩
  cases b <;> cases c <;>
    simp [adjacent,upDownAdjacent,neighbor,embedTriangle,Fin.exists_fin_succ] <;> omega


end
end CriticalStrip.HoneycombBranch

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_GraphPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/





namespace CriticalStrip
noncomputable section
open scoped Classical BigOperators
open Diagram.PathGraph



namespace WireConfiguration
variable {N : ℕ} {finish : Triangle}


def weight (D : WireConfiguration N finish) : ℝ := rho ^ D.graph.support.ncard



def equivPaths (N : ℕ) (finish : Triangle) (hf : finish ≠ up 0 0) :
    WireConfiguration N finish ≃ {p : List Triangle // IsPath N finish p} where
  toFun D := ⟨D.path,D.path_isPath hf⟩
  invFun p := ofPath hf p.property
  left_inv D := ofPath_path_isPath D hf
  right_inv p := Subtype.ext (ofPath_path hf p.property)

end WireConfiguration
end





end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ReflectionFractions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped BigOperators
open Set MeasureTheory



def reflectionMomentKernel (n k : ℕ) (z : Fin (n+1) → ℝ) : ℝ :=
  (z 0)^k * omega (z 0) * reflectionProduct n (z 0) (Fin.tail z) * density n (Fin.tail z)



def meanCharacteristic (n : ℕ) : Polynomial ℝ :=
  ∑ s ∈ (Finset.univ : Finset (Fin n)).powerset,
    Polynomial.C ((-1 : ℝ)^s.card *
      ∫ y, (∏ j ∈ Finset.univ \ s, y j) * density n y ∂unitCubeMeasure n) * Polynomial.X^s.card


def reflectionResidueKernel (n : ℕ) (x : ℝ) (i : Fin n) (y : Fin n → ℝ) : ℝ :=
  reflectionResidue n y i * density n y / (x+y i)

end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_RightStieltjes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip





noncomputable section
open Set MeasureTheory Filter Polynomial
open scoped Topology BigOperators Classical



def reflectionCauchyKernel (n : ℕ) (z : ℝ) (y : Fin (n+1) → ℝ) : ℝ :=
  reflectionMomentKernel n 0 y / (z-y 0)


def cauchyDensity (n : ℕ) (z : ℝ) (y : Fin n → ℝ) : ℝ :=
  density n y / ∏ i, (z-y i)

end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_MonicPositive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/





namespace CriticalStrip.Diagram
noncomputable section
open Filter Polynomial
open scoped Topology BigOperators Classical


def separatedHomogeneous (n m : ℕ) (i : Fin n) : ℂ :=
  (C:ℂ)+(i.val:ℂ)*(1/((m:ℂ)+1))

end
end CriticalStrip.Diagram





end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_DeformationWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open _root_.Matrix Set
open scoped BigOperators Classical

def deformationAngles (n : ℕ) (t : ℝ) : Fin (n+1) → ℝ := Fin.cons t (fun _=>lambda)

end
end CriticalStrip.Diagram





end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ReversedConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open _root_.Matrix Set
open scoped BigOperators Classical

def reverseDeformationAngles (n : ℕ) (t : ℝ) : Fin (n+1) → ℝ :=
  Fin.cons (3*lambda-t) (fun _=>2*lambda)

end





end CriticalStrip.Diagram





end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_HoneycombClip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped Classical BigOperators
open Diagram


def turnCell (N : ℕ) (b : ℤ) : Cell ≃ Cell where
  toFun q := (b-q.1,turnRow N q.2)
  invFun q := (b-q.1,turnRow N q.2)
  left_inv := by rintro ⟨i,j⟩; simp only [sub_sub_cancel,turnRow_involutive]
  right_inv := by rintro ⟨i,j⟩; simp only [sub_sub_cancel,turnRow_involutive]

end





noncomputable section
open scoped Classical BigOperators
open Diagram


def windowCell (N m : ℕ) : (Fin m ⊕ Fin m) × Fin N → Cell
  | (.inl k,j) => (-1-(k.val:ℤ),j.val)
  | (.inr k,j) => ((k.val:ℤ),j.val)

end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_SidePaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped BigOperators Classical



def stepSideWeight (N : ℕ) (s i : ℤ) (p : List Triangle) : ℝ :=
  if PathBetween (N+1) (up i 0) (up s N) p ∧ (∀ v∈p,steppedDomain N s v)
  then rho^p.length else 0

def stepSideKernel (N : ℕ) (s i : ℤ) : ℝ := ∑' p,stepSideWeight N s i p

def stepSideMass (N : ℕ) (s : ℤ) : ℝ := ∑' i,stepSideKernel N s i



def sideToTallBridge (N : ℕ) (s : ℤ) (p : List Triangle) : List Triangle :=
  (((p++[down (s-1) N]).reverse).map (rotateTriangle (N+1))).map (translateTriangle (s-1))



def bridgeToSide (N : ℕ) (s k : ℤ) (p : List Triangle) : List Triangle :=
  p.map (translateTriangle (s-k)) ++ [up s N]

end
 

 

noncomputable section
open scoped BigOperators Classical
open Filter Topology


def stepCutKernel (N : ℕ) (s q : ℤ) (x : ℕ×ℕ) : ℝ :=
  stepArchKernel N s (q-(x.1:ℤ)) (q+(x.2:ℤ)+1)

def stepCutMass (N : ℕ) (s q : ℤ) : ℝ := ∑' x,stepCutKernel N s q x

def stepArchLeft (N : ℕ) (s i : ℤ) : ℝ :=
  ∑' j : ℕ,stepArchKernel N s i (i-1-(j:ℤ))

def stepArchRight (N : ℕ) (s i : ℤ) : ℝ :=
  ∑' j : ℕ,stepArchKernel N s i (i+(j:ℤ)+1)



def SteppedBoundaryFlux (N : ℕ) (s : ℤ) : Prop :=
  ∀ i : ℤ, Real.sin (3*lambda)*(stepArchLeft N s i-stepArchRight N s i)+
    Real.sin lambda*stepSideKernel N s i=0

end




end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_RibbonLocal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.HoneycombBranch





noncomputable section
open scoped Classical
open Diagram FiniteBranchTree


def ribbonArcs (b : Bool) (a : Finset (Fin 3 × Fin 3)) : Finset (Fin 6 × Fin 6) :=
  a.image (fun pq=>Pairing.orderedEdge (lane b pq.1 0) (lane b pq.2 1))


def RibbonSimple (s : State) (l : List Bool) : Prop :=
  ∀ v, IsPairing (ribbonArcs v.2.2 (routes s l v))

end





end CriticalStrip.HoneycombBranch

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_RibbonGlobal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
namespace HoneycombBranch
open scoped Classical

open FiniteBranchTree



def retractVertex (v : Vertex) : Triangle := (v.1,v.2.1.toNat,v.2.2)

lemma retract_embed (v : Triangle) : retractVertex (embedTriangle v)=v := by
  rcases v with ⟨i,r,b⟩
  simp [retractVertex,embedTriangle]
lemma embed_retract (v : Vertex) (h : 0≤v.2.1) : embedTriangle (retractVertex v)=v := by
  rcases v with ⟨i,r,b⟩
  simp only [retractVertex,embedTriangle,Int.toNat_of_nonneg h]

lemma visited_retract_path (H : ℕ) (a b : Triangle) (s : State) (l : List Bool) (hl : l≠[])
    (hs : s.1=embedTriangle a) (ht : (back (terminal next s l)).1=embedTriangle b)
    (hn : (visited Prod.fst next s l).Nodup)
    (hband : ∀v∈visited Prod.fst next s l,0≤v.2.1 ∧ v.2.1<(H:ℤ)) :
    PathBetween H a b ((visited Prod.fst next s l).map retractVertex) := by
  have hheads:=visited_head_last s l hl
  have he : ((visited Prod.fst next s l).map retractVertex).map embedTriangle=visited Prod.fst next s l := by
    rw [List.map_map]
    conv_rhs => rw [←List.map_id (visited Prod.fst next s l)]
    apply List.map_congr_left
    intro v hv
    exact embed_retract v (hband v hv).1
  have hc := visited_chain s l
  have hc' : (((visited Prod.fst next s l).map retractVertex).map embedTriangle).IsChain
      (fun v w=>∃q : Fin 3,neighbor v q=w) := by rw [he]; exact hc
  have ha:= (List.isChain_map _).mp hc'
  refine ⟨?_,?_,?_,ha.imp (fun v w h=>(adjacent_iff v w).mpr h),?_⟩
  · rw [List.head?_map,hheads.1,Option.map_some,hs,retract_embed]
  · rw [List.getLast?_map,hheads.2,Option.map_some,ht,retract_embed]
  · apply List.Nodup.of_map (f:=embedTriangle)
    rw [he]
    exact hn
  · intro v hv
    obtain ⟨w,hw,rfl⟩:=List.mem_map.mp hv
    have hb:=hband w hw
    change w.2.1.toNat<H
    omega

end HoneycombBranch
open scoped Classical BigOperators

 

lemma exists_column_to_bottom (H : ℕ) (i : ℤ) (j : ℕ) (b : Bool) (hj : j<H) :
    ∃ p : List Triangle, PathBetween H (i,j,b) (up i 0) p ∧
      (∀ v∈p,v.1=i) ∧ p.length≤2*H := by
  let a : Fin (2*H):=⟨2*j+(if b then 0 else 1),by split <;> omega⟩
  let z : Fin (2*H):=⟨0,by omega⟩
  obtain ⟨w,hw⟩:=((SimpleGraph.pathGraph_preconnected (2*H)) a z).exists_isPath
  let f : Fin (2*H)→Triangle:=fun r=>ladderVertex i r.val
  have hf : Function.Injective f := (ladderVertex_injective i).comp Fin.val_injective
  refine ⟨w.support.map f,⟨?_,?_,hw.support_nodup.map hf,?_,?_⟩,?_,?_⟩
  · simp only [List.head?_map,List.head?_eq_some_head w.support_ne_nil,w.head_support,Option.map_some]
    cases b <;> simp [f,a,ladderVertex]
    omega
  · simp [List.getLast?_map,List.getLast?_eq_some_getLast w.support_ne_nil,w.getLast_support,f,z,ladderVertex,up]
  · apply (List.isChain_map _).mpr
    apply w.isChain_adj_support.imp
    intro v w h
    rcases SimpleGraph.pathGraph_adj.mp h with hh|hh
    · change adjacent (ladderVertex i v.val) (ladderVertex i w.val)
      rw [←hh]
      exact ladderVertex_adjacent i _
    · change adjacent (ladderVertex i v.val) (ladderVertex i w.val)
      rw [←hh]
      exact adjacent_symmetric.symm _ _ (ladderVertex_adjacent i _)
  · intro v hv
    obtain ⟨r,_,rfl⟩:=List.mem_map.mp hv
    change r.val/2<H
    have :=r.isLt
    omega
  · intro v hv
    obtain ⟨r,_,rfl⟩:=List.mem_map.mp hv
    rfl
  · rw [List.length_map]
    have :=List.Nodup.length_le_card hw.support_nodup
    simpa only [Fintype.card_fin] using this

namespace HoneycombBranch
open FiniteBranchTree

namespace SideWord
variable {H : ℕ} {i k : ℤ}

def path (x : SideWord H i k) : List Triangle:=
  (visited Prod.fst next (bottom i) x.val).map retractVertex

lemma connector_exists (x : SideWord H i k) :
    ∃p : List Triangle, PathBetween H (retractVertex x.state.1) (up k 0) p ∧
      (∀v∈p,v.1=k) ∧ p.length≤2*H := by
  have hj : x.state.1.2.1.toNat<H := by have :=x.band; omega
  have hh:=exists_column_to_bottom H k x.state.1.2.1.toNat x.state.1.2.2 hj
  have he : retractVertex x.state.1=(k,x.state.1.2.1.toNat,x.state.1.2.2) := by
    dsimp [retractVertex,state]
    rw [x.property.2.2.2.2]
  rwa [he]

 def connector (x : SideWord H i k) : List Triangle:=x.connector_exists.choose

 def arch (x : SideWord H i k) : List Triangle:=x.path++x.connector

end SideWord
end HoneycombBranch
end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_FluxWindow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.HoneycombBranch





noncomputable section
open scoped Classical BigOperators
open FiniteBranchTree


variable {D : Vertex→Prop} {B : Type*} (P : BoundaryPorts D B) {H : ℕ} {i : ℤ}

def ValidBoundaryPath (H : ℕ) (i : ℤ) (x : B×List Triangle) : Prop :=
  bottom i≠P.port x.1 ∧
  PathBetween H (up i 0) (retractVertex (P.port x.1).1) x.2 ∧
  ∀v∈x.2,D (embedTriangle v)

abbrev BoundaryPath (H : ℕ) (i : ℤ) := {x : B×List Triangle // ValidBoundaryPath P H i x}

def boundaryPathWeight (H : ℕ) (i : ℤ) (x : B×List Triangle) : ℝ :=
  if ValidBoundaryPath P H i x then rho^x.2.length else 0

lemma visited_map_retract (l : List Bool)
    (hrow : ∀v∈visited Prod.fst next (bottom i) l,0≤v.2.1) :
    ((visited Prod.fst next (bottom i) l).map retractVertex).map embedTriangle=
      visited Prod.fst next (bottom i) l := by
  rw [List.map_map]
  conv_rhs => rw [←List.map_id (visited Prod.fst next (bottom i) l)]
  exact List.map_congr_left (fun v hv=>embed_retract v (hrow v hv))

def exitToPath (hD : ∀v,D v→0≤v.2.1 ∧ v.2.1<(H:ℤ)) (x : ExitWord D i) : BoundaryPath P H i := by
  refine ⟨(exitPort P x,(visited Prod.fst next (bottom i) x.val).map retractVertex),?_,?_,?_⟩
  · intro he
    exact word_terminal_ne_source x.property.1 x.property.2.1
      (by calc
        terminal next (bottom i) x.val=back (P.port (exitPort P x)) := exitPort_terminal P x
        _=back (bottom i) := congrArg back he.symm)
  · apply visited_retract_path H (up i 0) _ (bottom i) x.val x.property.1 rfl
      _ x.property.2.1 (fun v hv=>hD v (x.property.2.2.1 v hv))
    rw [←exitPort_spec]
    exact (embed_retract _ (hD _ (P.inside _)).1).symm
  · intro v hv
    obtain ⟨w,hw,rfl⟩:=List.mem_map.mp hv
    rw [embed_retract _ (hD _ (x.property.2.2.1 w hw)).1]
    exact x.property.2.2.1 w hw

lemma exitToPath_injective (hD : ∀v,D v→0≤v.2.1 ∧ v.2.1<(H:ℤ)) :
    Function.Injective (exitToPath P (i:=i) hD) := by
  intro x y he
  have hb:=congrArg (fun z : BoundaryPath P H i=>z.val.1) he
  have hp:=congrArg (fun z : BoundaryPath P H i=>z.val.2.map embedTriangle) he
  change exitPort P x=exitPort P y at hb
  change ((visited Prod.fst next (bottom i) x.val).map retractVertex).map embedTriangle=
    ((visited Prod.fst next (bottom i) y.val).map retractVertex).map embedTriangle at hp
  rw [visited_map_retract _ (fun v hv=>(hD v (x.property.2.2.1 v hv)).1),
    visited_map_retract _ (fun v hv=>(hD v (y.property.2.2.1 v hv)).1)] at hp
  apply Subtype.ext
  exact word_unique _ _ _ hp (by rw [exitPort_terminal P x,exitPort_terminal P y,hb])

lemma exitToPath_surjective (hD : ∀v,D v→0≤v.2.1 ∧ v.2.1<(H:ℤ)) :
    Function.Surjective (exitToPath P (i:=i) hD) := by
  intro x
  have hp:=x.property.2.1
  have hh : (x.val.2.map embedTriangle).head?=some (bottom i).1 := by
    rw [List.head?_map,hp.1]; rfl
  have ht : (x.val.2.map embedTriangle).getLast?=some (back (back (P.port x.val.1))).1 := by
    rw [back_back,List.getLast?_map,hp.2.1,Option.map_some,embed_retract _ (hD _ (P.inside _)).1]
  have hn : (x.val.2.map embedTriangle).Nodup := hp.2.2.1.map embedTriangle_injective
  have hc : (x.val.2.map embedTriangle).IsChain (fun v w=>∃q : Fin 3,neighbor v q=w) :=
    (List.isChain_map _).mpr (hp.2.2.2.1.imp (fun v w h=>(adjacent_iff v w).mp h))
  have hi : (back (bottom i)).1∉x.val.2.map embedTriangle := by
    intro hv
    obtain ⟨v,hv,he⟩:=List.mem_map.mp hv
    exact source_outside hD (he ▸ x.property.2.2 v hv)
  have ho : (back (P.port x.val.1)).1∉x.val.2.map embedTriangle := by
    intro hv
    obtain ⟨v,hv,he⟩:=List.mem_map.mp hv
    exact P.outside _ (he ▸ x.property.2.2 v hv)
  obtain ⟨l,hv,he⟩:=exists_word (bottom i) (back (P.port x.val.1)) (x.val.2.map embedTriangle)
    hh ht hn hc hi ho (by simpa only [back_back] using x.property.1)
  have hne:=word_nonempty_of_head _ _ _ hh hv
  have hl : IsExit D i l := by
    refine ⟨hne,by rw [hv]; exact hn,?_,?_⟩
    · intro v hm
      rw [hv] at hm
      obtain ⟨w,hw,rfl⟩:=List.mem_map.mp hm
      exact x.property.2.2 w hw
    · rw [he]; exact P.outside _
  refine ⟨⟨l,hl⟩,?_⟩
  apply Subtype.ext
  apply Prod.ext
  · apply P.injective
    rw [show (exitToPath P hD ⟨l,hl⟩).val.1=exitPort P ⟨l,hl⟩ from rfl,
      exitPort_spec,he,back_back]
  · change (visited Prod.fst next (bottom i) l).map retractVertex=x.val.2
    rw [hv,List.map_map]
    calc
      List.map (retractVertex ∘ embedTriangle) x.val.2=List.map id x.val.2 :=
        List.map_congr_left (fun v _=>retract_embed v)
      _=x.val.2 := List.map_id x.val.2

def exitPathEquiv (hD : ∀v,D v→0≤v.2.1 ∧ v.2.1<(H:ℤ)) : ExitWord D i ≃ BoundaryPath P H i :=
  Equiv.ofBijective (exitToPath P hD) ⟨exitToPath_injective P hD,exitToPath_surjective P hD⟩

end





end CriticalStrip.HoneycombBranch

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_PhysicalPorts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.HoneycombBranch
noncomputable section
open scoped Classical BigOperators
open FiniteBranchTree

def betweenBridgeWeight (H : ℕ) (i j : ℤ) (p : List Triangle) : ℝ :=
  if 0<H ∧ PathBetween H (up i 0) (down j (H-1)) p then rho^p.length else 0

end

 

 

noncomputable section
open scoped Classical BigOperators
open FiniteBranchTree

 

def extendStepTop (N : ℕ) (s j : ℤ) (p : List Triangle) : List Triangle :=
  if j < s then p++[up j N,down j N] else p

end
end CriticalStrip.HoneycombBranch





end OAI
end


