-- Prove2me | Definitions.Def_OAIQWHT000
-- name    : OAIQWHT000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-23T19:15:35.078004+00:00
-- url     : https://prove2.me/theorems/401d97e5-0095-471c-88ed-0e145a710986
-- title:
--   OpenAI Heilbronn triangle split: definitions bundle
-- statement:
--   The definitions bundle of the split of OpenAI's proof that the Heilbronn triangle problem admits point sets with smallest triangle area at least $n^{-2+\delta}$ for an explicit $\delta > 0$ (`OAI.Problem355.heilbronn_power_lower_bound`, the paper's Theorem 1.1). It holds OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Geometry/HeilbronnTriangle` (OpenAI, *A power improvement in the Heilbronn triangle lower bound*, OpenAI Math Release, September 25, 2026, result family 191, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a. Among them are the auxiliary random cap sets and their weights (`AuxiliarySampling.Law`, `LiftingProbability.auxiliaryWeight`, `AuxiliaryCap.IsCap`), the lattice data of the determinant counts (`ZeroDeterminantCount.RowData`, `PrimePowerData`, `Section04Orbit.slOrbit`, `Homogeneous.InBox`, `PlaneRowTransport.projectedColumn`), the counting constants, and the parameter data and point laws of the construction. The bundle also contains the lemmas those definitions use in their bodies.
--
--   The definitions of the published statement (`Point`, `pointsInUnitSquare`, `triangleAreasAtLeast`, `heilbronnExponent` and the rest) are not repeated: the bundle imports them from the published bundle `Def_HeilbronnTriangle`. It imports no other bundle.
--
--   Modules: `ActualPointLaw`, `ActualPointLawTriples`, `AffineTripleOrbit`, `AllowedShifts`, `AnisotropicCount`, `AnisotropicGeometry`, `AuxiliaryAffineWeights`, `AuxiliaryCap`, `AuxiliarySamplingLaw`, `AuxiliarySet`, `AuxiliaryThreeCase`, `AuxiliaryWeights`, `AuxiliaryZeroCount`, `AveragedBadTripleBound`, `CRTLifting`, `CapInBox`, `ConditionalBadTripleBound`, `ConditionalMatrix`, `ConditionalSamples`, `DesignatedCoefficient`, `DeterminantCoefficients`, `DeterminantFibers`, `DiagonalDetImage`, `DiagonalKernel`, `DiagonalStabilizer`, `DigitBadTripleAverage`, `DigitColumnLaw`, `DigitUniqueness`, `DigitUnits`, `DividingPivot`, `EqualCoordinatePacking`, `EqualCoordinatePlane`, `FiniteFieldLabels`, `FiniteMixtures`, `FixedDetLattice`, `FixedDetReduction`, `GeometricAlteration`, `HomogeneousGeometry`, `IndependentTupleCard`, `IntegerMatrixEvents`, `IntegerMatrixFibers`, `IntegerPlaneEstimates`, `IntegerPointLaw`, `IntegerPointLawTriples`, `IntegerSampling`, `IntegerSamplingPairs`, `IntegralAmbientLattice`, `IntegralPlaneLattice`, `IntegralPlaneReduction`, `LabelResidues`, `LatticeBox`, `LatticeSplit`, `LiftCollisions`, `LiftingProbability`, `MainDigitLaw`, `MainDigitObstruction`, `MainDigitOrbitObstruction`, `MainOrbitObstruction`, `MainResidueSystem`, `MonomialCount`, `NonzeroWeightedCount`, `NormDecomposition`, `NormDeterminant`, `NormEncoding`, `NormFoundation`, `NormHomogeneity`, `NormPolynomial`, `OrbitCardinality`, `OrbitEstimate`, `OrbitSampling`, `PairingDivisor`, `ParameterConclusion`, `ParameterSampling`, `ParameterSequence`, `Parameters`, `PivotAssembly`, `PlaneCount`, `PlaneFiberAssembly`, `PlaneFunctional`, `PlaneRowTransport`, `PointLawBadTripleBound`, `PolynomialCoefficients`, `PrimeLiftParameters`, `PrimePowerData`, `PrimePowerFactors`, `PrimePowerGL`, `PrimePowerRowData`, `PrimitiveNormal`, `ProjectiveBadEvent`, `ProportionalPairs`, `RankOneMinors`, `RowLattice`, `RowLatticeMatrices`, `SampleDeletion`, `SharedGeometricAlteration`, `ShortRelations`, `ShortestIntegralVector`, `SmithDigitMoment`, `StabilizerConjugation`, `SuccessiveVectors`, `TranslateAverage`, `TripleEnumeration`, `TwoByTwoPivot`, `TwoByTwoSmith`, `TypedFixedFiberCount`, `UniformAction`, `UniformFixedFiberCount`, `WeightedNormalReduction`, `WeightedZeroPartition`, `ZModAnnihilator`, `ZeroDeterminantCount`, `ZeroGlobalCount`, `ZeroRowData`.
--
--   The theorems of the development that the definitions do not need are proved in the three solutions of this split. One proves the published intermediate statement `OAI.Problem355.AuxiliaryZeroCount.weighted_count_le_log`, one proves `OAI.Problem355.UniformFixedFiberCount.matrix_fiber_le` from it, and the third proves `OAI.Problem355.heilbronn_power_lower_bound` from that. The split exists because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, A power improvement in the Heilbronn triangle lower bound, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 191; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-power-improvement-in-the-Heilbronn-triangle-lower-bound-September-25-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry/HeilbronnTriangle at commit adc7f12

import Mathlib
import Definitions.Def_HeilbronnTriangle

section
-- module Solutions.OAIQW_Problem355.AffineTripleOrbit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.AffineTripleOrbit
open Affine

variable {F V P ι : Type*} [Field F] [AddCommGroup V] [Module F V]

theorem exists_linearEquiv_map [Finite ι] {u v : ι → V}
    (hu : LinearIndependent F u) (hv : LinearIndependent F v) :
    ∃ g : V ≃ₗ[F] V, ∀ i, g (u i) = v i := by
  classical
  let f := hu.linearCombinationEquiv.symm.trans hv.linearCombinationEquiv
  let : FiniteDimensional F (Submodule.span F (Set.range u)) :=
    FiniteDimensional.span_of_finite F (Set.finite_range u)
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq f
  refine ⟨g, fun i => ?_⟩
  have hi := hg (hu.linearCombinationEquiv (Finsupp.single i 1))
  simpa [f] using hi.symm

instance linearTupleMulAction :
    MulAction (V ≃ₗ[F] V) {u : ι → V // LinearIndependent F u} where
  smul g u := ⟨g ∘ u.1, u.2.map' g.toLinearMap (LinearMap.ker_eq_bot.mpr g.injective)⟩
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp] theorem linearTuple_smul_apply
    (g : V ≃ₗ[F] V) (u : {u : ι → V // LinearIndependent F u}) (i : ι) :
    (g • u).1 i = g (u.1 i) := rfl

instance linearTuplePretransitive [Finite ι] :
    MulAction.IsPretransitive (V ≃ₗ[F] V) {u : ι → V // LinearIndependent F u} where
  exists_smul_eq u v := by
    obtain ⟨g, hg⟩ := exists_linearEquiv_map u.2 v.2
    exact ⟨g, Subtype.ext (funext hg)⟩

theorem exists_affineEquiv_map [Finite ι] [AffineSpace V P]
    {p q : ι → P} (hp : AffineIndependent F p) (hq : AffineIndependent F q)
    (i0 : ι) : ∃ g : P ≃ᵃ[F] P, ∀ i, g (p i) = q i := by
  classical
  have hp' := (affineIndependent_iff_linearIndependent_vsub F p i0).mp hp
  have hq' := (affineIndependent_iff_linearIndependent_vsub F q i0).mp hq
  obtain ⟨g, hg⟩ := exists_linearEquiv_map hp' hq'
  refine ⟨AffineEquiv.ofLinearEquiv g (p i0) (q i0), ?_⟩
  intro i
  by_cases hi : i = i0
  · subst i
    simp [AffineEquiv.ofLinearEquiv_apply]
  · rw [AffineEquiv.ofLinearEquiv_apply, hg ⟨i, hi⟩]
    exact vsub_vadd (q i) (q i0)

instance affineTupleMulAction [AffineSpace V P] :
    MulAction (P ≃ᵃ[F] P) {p : ι → P // AffineIndependent F p} where
  smul g p := ⟨g ∘ p.1, g.affineIndependent_iff.mpr p.2⟩
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp] theorem affineTuple_smul_apply [AffineSpace V P]
    (g : P ≃ᵃ[F] P) (p : {p : ι → P // AffineIndependent F p}) (i : ι) :
    (g • p).1 i = g (p.1 i) := rfl

instance affineTuplePretransitive [Finite ι] [Nonempty ι] [AffineSpace V P] :
    MulAction.IsPretransitive (P ≃ᵃ[F] P) {p : ι → P // AffineIndependent F p} where
  exists_smul_eq p q := by
    classical
    obtain ⟨g, hg⟩ := exists_affineEquiv_map p.2 q.2 (Classical.arbitrary ι)
    exact ⟨g, Subtype.ext (funext hg)⟩

noncomputable def inputShiftEquiv :
    (V ≃ᵃ[F] V) ≃ (V ≃ₗ[F] V) × V where
  toFun e := (e.linear, e.linear.symm (e 0))
  invFun u := AffineEquiv.ofLinearEquiv u.1 0 (u.1 u.2)
  left_inv e := by
    apply AffineEquiv.ext
    intro x
    simp only [AffineEquiv.ofLinearEquiv_apply, vsub_eq_sub, sub_zero,
      vadd_eq_add, LinearEquiv.apply_symm_apply]
    simpa using (e.map_vadd 0 x).symm
  right_inv u := by
    apply Prod.ext
    · rfl
    · simp [AffineEquiv.ofLinearEquiv_apply]

@[simp] theorem inputShiftEquiv_symm_apply (g : V ≃ₗ[F] V) (a x : V) :
    (inputShiftEquiv.symm (g, a)) x = g (a + x) := by
  simp [inputShiftEquiv, AffineEquiv.ofLinearEquiv_apply, map_add, add_comm]

noncomputable def restrictedInputShiftEquiv (A : Set V) :
    {e : V ≃ᵃ[F] V // (inputShiftEquiv e).2 ∈ A} ≃ (V ≃ₗ[F] V) × A where
  toFun e := ((inputShiftEquiv e.1).1, ⟨(inputShiftEquiv e.1).2, e.2⟩)
  invFun u := ⟨inputShiftEquiv.symm (u.1, u.2.1), by simp⟩
  left_inv e := by
    apply Subtype.ext
    exact inputShiftEquiv.symm_apply_apply e.1
  right_inv u := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      simp [inputShiftEquiv, AffineEquiv.ofLinearEquiv_apply]

theorem card_restrictedInputShift (A : Set V) :
    Nat.card {e : V ≃ᵃ[F] V // (inputShiftEquiv e).2 ∈ A} =
      Nat.card (V ≃ₗ[F] V) * Nat.card A := by
  rw [Nat.card_congr (restrictedInputShiftEquiv A), Nat.card_prod]

theorem card_affineEquiv :
    Nat.card (V ≃ᵃ[F] V) = Nat.card (V ≃ₗ[F] V) * Nat.card V := by
  rw [Nat.card_congr (inputShiftEquiv (F := F) (V := V)), Nat.card_prod]

theorem card_affineEquiv_le_two_restricted (A : Set V)
    (hA : Nat.card V ≤ 2 * Nat.card A) :
    Nat.card (V ≃ᵃ[F] V) ≤
      2 * Nat.card {e : V ≃ᵃ[F] V // (inputShiftEquiv e).2 ∈ A} := by
  rw [card_affineEquiv, card_restrictedInputShift]
  simpa [mul_assoc, mul_left_comm] using Nat.mul_le_mul_left (Nat.card (V ≃ₗ[F] V)) hA

end Problem355.AffineTripleOrbit

end OAI
end

section
-- module Solutions.OAIQW_Problem355.IndependentTupleCard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


open scoped BigOperators

namespace Problem355.IndependentTupleCard

variable (K V : Type*) [DivisionRing K] [AddCommGroup V] [Module K V]

theorem affineIndependent_fin_iff {n : ℕ} (p : Fin (n+1) → V) :
    AffineIndependent K p ↔
      LinearIndependent K (fun i : Fin n => p i.succ - p 0) := by
  rw [affineIndependent_iff_linearIndependent_vsub K p 0]
  simpa [Function.comp_def, finSuccAboveEquiv_apply, Fin.succAbove_zero] using
    (linearIndependent_equiv (finSuccAboveEquiv (0 : Fin (n+1)))
      (f := fun i : {x : Fin (n+1) // x ≠ 0} => p i -ᵥ p 0)).symm

def affineTupleEquiv (n : ℕ) :
    {p : Fin (n+1) → V // AffineIndependent K p} ≃
      V × {v : Fin n → V // LinearIndependent K v} where
  toFun p := (p.val 0, ⟨fun i => p.val i.succ - p.val 0,
    (affineIndependent_fin_iff K V p.val).mp p.property⟩)
  invFun xv := ⟨Fin.cons xv.1 (fun i => xv.2.val i + xv.1), by
    apply (affineIndependent_fin_iff K V _).mpr
    simpa using xv.2.property⟩
  left_inv p := by
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp
  right_inv xv := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      funext i
      simp

variable [Fintype K] [Finite V]

theorem card_affineIndependent {n : ℕ} (hn : n ≤ Module.finrank K V) :
    Nat.card {p : Fin (n+1) → V // AffineIndependent K p} =
      Nat.card V * ∏ i : Fin n,
        (Fintype.card K ^ Module.finrank K V - Fintype.card K ^ i.val) := by
  rw [Nat.card_congr (affineTupleEquiv K V n), Nat.card_prod, card_linearIndependent hn]

theorem card_affineIndependent_triples :
    Nat.card {p : Fin 3 → (Fin 3 → K) // AffineIndependent K p} =
      Fintype.card K ^ 3 * (Fintype.card K ^ 3 - 1) *
        (Fintype.card K ^ 3 - Fintype.card K) := by
  have hn : 2 ≤ Module.finrank K (Fin 3 → K) := by simp
  rw [card_affineIndependent K (Fin 3 → K) hn]
  simp [Nat.card_eq_fintype_card, Fin.prod_univ_two, mul_assoc]

end Problem355.IndependentTupleCard

end OAI
end

section
-- module Solutions.OAIQW_Problem355.UniformAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem355.UniformAction

open scoped BigOperators

section Action

variable {G X : Type*} [Group G] [Fintype G] [finiteAction : Fintype X] [DecidableEq X]
  [MulAction G X] [MulAction.IsPretransitive G X]

theorem transporter_card_eq {G X : Type*} [Group G] [Fintype G] [Fintype X]
    [DecidableEq X] [MulAction G X] [MulAction.IsPretransitive G X] (x y z : X) :
    Fintype.card {g : G // g • x = y} =
      Fintype.card {g : G // g • x = z} := by
  classical
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq G y z
  apply Fintype.card_congr
  exact
    { toFun := fun g => ⟨h * g.1, by rw [mul_smul, g.2, hh]⟩
      invFun := fun g => ⟨h⁻¹ * g.1, by
        rw [mul_smul, g.2, ← hh, inv_smul_smul]⟩
      left_inv := fun g => by ext; simp
      right_inv := fun g => by ext; simp }

theorem card_smul_mem (x : X) (S : Finset X) :
    (Finset.univ.filter (fun g : G => g • x ∈ S)).card * Fintype.card X =
      Fintype.card G * S.card := by
  classical
  let c := (Finset.univ.filter (fun g : G => g • x = x)).card
  have hc (y : X) :
      (Finset.univ.filter (fun g : G => g • x = y)).card = c := by
    simpa only [Fintype.card_subtype] using transporter_card_eq (G := G) x y x
  have hs := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset G) S (fun g => g • x)
  simp_rw [hc] at hs
  simp only [Finset.sum_const, smul_eq_mul] at hs
  have ht := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset G) (Finset.univ : Finset X) (fun g => g • x)
  simp_rw [hc] at ht
  simp only [Finset.sum_const, smul_eq_mul, Finset.card_univ,
    Finset.mem_univ, Finset.filter_true] at ht
  rw [← hs, ← ht]
  ring

theorem smul_probability (x : X) (S : Finset X) :
    ((Finset.univ.filter (fun g : G => g • x ∈ S)).card : ℝ) /
        Fintype.card G = (S.card : ℝ) / Fintype.card X := by
  classical
  let : Nonempty X := ⟨x⟩
  have hG : (Fintype.card G : ℝ) ≠ 0 := by positivity
  have hX : (Fintype.card X : ℝ) ≠ 0 := by positivity
  apply (div_eq_div_iff hG hX).2
  exact_mod_cast (card_smul_mem (G := G) x S).trans (Nat.mul_comm _ _)

end Action

section Conditioning

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem conditional_density_le (A E : Finset Ω) (hA : A.Nonempty)
    (K : ℝ) (hsize : (Fintype.card Ω : ℝ) ≤ K * A.card) :
    ((A ∩ E).card : ℝ) / A.card ≤
      K * ((E.card : ℝ) / Fintype.card Ω) := by
  let : Nonempty Ω := ⟨hA.choose⟩
  have hAp : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hNp : (0 : ℝ) < Fintype.card Ω := by positivity
  have hi : ((A ∩ E).card : ℝ) ≤ E.card := by
    exact_mod_cast Finset.card_le_card (Finset.inter_subset_right : A ∩ E ⊆ E)
  have h1 := mul_le_mul_of_nonneg_right hi hNp.le
  have h2 := mul_le_mul_of_nonneg_left hsize (show (0 : ℝ) ≤ E.card by positivity)
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ hAp hNp).2
  nlinarith

theorem conditional_density_le_two (A E : Finset Ω) (hA : A.Nonempty)
    (hsize : Fintype.card Ω ≤ 2 * A.card) :
    ((A ∩ E).card : ℝ) / A.card ≤
      2 * ((E.card : ℝ) / Fintype.card Ω) := by
  apply conditional_density_le A E hA 2
  exact_mod_cast hsize

end Conditioning

variable {G X : Type*} [Group G] [Fintype G] [Fintype X]
  [DecidableEq G] [DecidableEq X] [MulAction G X]
  [MulAction.IsPretransitive G X]

theorem restricted_smul_probability (x : X) (S : Finset X) (A : Finset G)
    (hA : A.Nonempty) (hsize : Fintype.card G ≤ 2 * A.card) :
    ((A.filter (fun g => g • x ∈ S)).card : ℝ) / A.card ≤
      2 * ((S.card : ℝ) / Fintype.card X) := by
  have h := conditional_density_le_two A
    (Finset.univ.filter (fun g : G => g • x ∈ S)) hA hsize
  simpa only [Finset.inter_filter, Finset.inter_univ, smul_probability] using h

open scoped Pointwise in

theorem restricted_inv_smul_probability (x : X) (S : Finset X) (A : Finset G)
    (hA : A.Nonempty) (hsize : Fintype.card G ≤ 2 * A.card) :
    ((A.filter (fun g => g⁻¹ • x ∈ S)).card : ℝ) / A.card ≤
      2 * ((S.card : ℝ) / Fintype.card X) := by
  have hAi : A⁻¹.Nonempty := by
    obtain ⟨a, ha⟩ := hA
    exact ⟨a⁻¹, Finset.inv_mem_inv ha⟩
  have h := restricted_smul_probability x S A⁻¹ hAi (by simpa using hsize)
  have hc : (A⁻¹.filter (fun g => g • x ∈ S)).card =
      (A.filter (fun g => g⁻¹ • x ∈ S)).card := by
    rw [← Finset.card_inv (A.filter (fun g => g⁻¹ • x ∈ S))]
    congr 1
    ext g
    simp
  simpa only [hc, Finset.card_inv] using h

end Problem355.UniformAction

end OAI
end

section
-- module Solutions.OAIQW_Problem355.AuxiliaryWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem355.AuxiliaryWeights

open scoped BigOperators

attribute [local instance] Classical.propDecidable

section Families

variable {ι V : Type*} [Fintype ι] [Fintype V] [DecidableEq V]

theorem card_families_mem_le (Q : (ι → V) → Prop) (S : Finset V) :
    Fintype.card {p : {v : ι → V // Q v} // ∀ i, p.1 i ∈ S} ≤
      S.card ^ Fintype.card ι := by
  let f : {p : {v : ι → V // Q v} // ∀ i, p.1 i ∈ S} → (ι → S) :=
    fun p i => ⟨p.1.1 i, p.2 i⟩
  have hf : Function.Injective f := by
    intro p q hpq
    apply Subtype.ext
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun hpq i)
  have h := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_fun, Fintype.card_coe] using h

end Families

section Affine

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

abbrev AffineFamily (K V ι : Type*) [Field K] [AddCommGroup V] [Module K V] :=
  {p : ι → V // AffineIndependent K p}

end Affine

section AffineInverse

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem affine_family_inverse_probability_le [Fintype V] [Fintype ι] [Nonempty ι]
    [DecidableEq V] [Fintype (V ≃ᵃ[K] V)]
    (p : AffineFamily K V ι) (S : Finset V) (A : Finset (V ≃ᵃ[K] V))
    (hA : A.Nonempty) (hsize : Fintype.card (V ≃ᵃ[K] V) ≤ 2 * A.card) :
    ((A.filter (fun e => ∀ i, e.symm (p.1 i) ∈ S)).card : ℝ) / A.card ≤
      2 * ((S.card : ℝ) ^ Fintype.card ι /
        Nat.card (AffineFamily K V ι)) := by
  classical
  let T : Finset (AffineFamily K V ι) :=
    Finset.univ.filter (fun q => ∀ i, q.1 i ∈ S)
  have h := UniformAction.restricted_inv_smul_probability p T A hA hsize
  have hT : T.card ≤ S.card ^ Fintype.card ι := by
    simpa only [T, Fintype.card_subtype] using
      card_families_mem_le (ι := ι) (AffineIndependent K) S
  have hTr : (T.card : ℝ) ≤ (S.card : ℝ) ^ Fintype.card ι := by
    exact_mod_cast hT
  calc
    _ ≤ 2 * ((T.card : ℝ) / Fintype.card (AffineFamily K V ι)) := by
      simpa only [T, Finset.mem_filter, Finset.mem_univ, true_and,
        AffineTripleOrbit.affineTuple_smul_apply, AffineEquiv.inv_def] using h
    _ ≤ _ := by
      rw [Nat.card_eq_fintype_card]
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hTr (by positivity)) (by norm_num)

end AffineInverse

section Normalization

theorem cubic_space_denominators {q : ℝ} (hq : 2 ≤ q) :
    0 < q ^ 3 - 1 ∧ 0 < q ^ 3 - q ∧
      q ^ 3 ≤ 2 * (q ^ 3 - 1) ∧
      (q ^ 3) ^ 2 ≤ 4 * ((q ^ 3 - 1) * (q ^ 3 - q)) ∧
      (q ^ 3) ^ 3 ≤ 4 * (q ^ 3 * ((q ^ 3 - 1) * (q ^ 3 - q))) := by
  have hq0 : 0 ≤ q := by linarith
  have hsq : 4 ≤ q ^ 2 := by nlinarith [sq_nonneg (q - 2)]
  have hcub : 4 * q ≤ q ^ 3 := by
    nlinarith [mul_nonneg hq0 (sub_nonneg.mpr hsq)]
  have hQ : 0 ≤ q ^ 3 := by positivity
  have h1 : q ^ 3 ≤ 2 * (q ^ 3 - 1) := by nlinarith
  have h2 : q ^ 3 ≤ 2 * (q ^ 3 - q) := by nlinarith
  have hp : (q ^ 3) ^ 2 ≤ 4 * ((q ^ 3 - 1) * (q ^ 3 - q)) := by
    have h := mul_le_mul h1 h2 hQ (by nlinarith : 0 ≤ 2 * (q ^ 3 - 1))
    nlinarith
  refine ⟨by nlinarith, by nlinarith, h1, hp, ?_⟩
  have h := mul_le_mul_of_nonneg_left hp hQ
  nlinarith

theorem affine_weight_le {Q s D p C : ℝ}
    (hQ : 0 ≤ Q) (hs : 0 < s) (hD : 0 < D)
    (hp : p ≤ 2 * s ^ 3 / D) (hden : Q ^ 3 ≤ C * D) :
    (Q / s) ^ 3 * p ≤ 2 * C := by
  calc
    (Q / s) ^ 3 * p ≤ (Q / s) ^ 3 * (2 * s ^ 3 / D) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = 2 * Q ^ 3 / D := by field_simp
    _ ≤ 2 * C := by
      apply (div_le_iff₀ hD).2
      nlinarith

theorem pair_weight_le {Q s D p C : ℝ}
    (hQ : 0 ≤ Q) (hs : 0 < s) (hD : 0 < D)
    (hp : p ≤ s ^ 2 / D) (hden : Q ^ 2 ≤ C * D) :
    (Q / s) ^ 3 * p ≤ C * (Q / s) := by
  calc
    (Q / s) ^ 3 * p ≤ (Q / s) ^ 3 * (s ^ 2 / D) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = (Q / s) * (Q ^ 2 / D) := by field_simp
    _ ≤ (Q / s) * C := mul_le_mul_of_nonneg_left
      ((div_le_iff₀ hD).2 hden) (by positivity)
    _ = C * (Q / s) := mul_comm _ _

theorem affine_weight_le_eight {q s p : ℝ} (hq : 2 ≤ q) (hs : 0 < s)
    (hp : p ≤ 2 * s ^ 3 /
      (q ^ 3 * ((q ^ 3 - 1) * (q ^ 3 - q)))) :
    (q ^ 3 / s) ^ 3 * p ≤ 8 := by
  obtain ⟨h1, h2, -, -, hden⟩ := cubic_space_denominators hq
  have hq0 : 0 < q := by linarith
  convert (affine_weight_le (by positivity) hs (by positivity) hp hden) using 1 ; norm_num

end Normalization

section FiniteFieldWeights

variable {K : Type*} [Field K] [Fintype K]

theorem affine_triple_weight_le_eight
    [Fintype ((Fin 3 → K) ≃ᵃ[K] (Fin 3 → K))]
    (p : AffineFamily K (Fin 3 → K) (Fin 3))
    (S : Finset (Fin 3 → K)) (hS : S.Nonempty)
    (A : Finset ((Fin 3 → K) ≃ᵃ[K] (Fin 3 → K)))
    (hA : A.Nonempty)
    (hsize : Fintype.card ((Fin 3 → K) ≃ᵃ[K] (Fin 3 → K)) ≤ 2 * A.card) :
    ((Fintype.card K : ℝ) ^ 3 / S.card) ^ 3 *
      (((A.filter (fun e => ∀ i, e.symm (p.1 i) ∈ S)).card : ℝ) / A.card) ≤ 8 := by
  have hq : 2 ≤ Fintype.card K := Fintype.one_lt_card
  have hqpow : Fintype.card K ≤ Fintype.card K ^ 3 :=
    Nat.le_self_pow (by decide) _
  have h1 : 1 ≤ Fintype.card K ^ 3 := by omega
  have hp := affine_family_inverse_probability_le p S A hA hsize
  have hcard :
      (Nat.card (AffineFamily K (Fin 3 → K) (Fin 3)) : ℝ) =
        (Fintype.card K : ℝ) ^ 3 *
          (((Fintype.card K : ℝ) ^ 3 - 1) *
            ((Fintype.card K : ℝ) ^ 3 - Fintype.card K)) := by
    change (Nat.card {p : Fin 3 → (Fin 3 → K) // AffineIndependent K p} : ℝ) = _
    rw [IndependentTupleCard.card_affineIndependent_triples K]
    simp only [Nat.cast_mul, Nat.cast_sub h1, Nat.cast_sub hqpow,
      Nat.cast_pow, Nat.cast_one, mul_assoc]
  simp only [Fintype.card_fin, hcard] at hp
  apply affine_weight_le_eight (by exact_mod_cast hq)
    (by exact_mod_cast hS.card_pos)
  convert hp using 1 <;> try ring_nf
  rw [mul_comm]
  congr 2
  congr 1
  ext e
  simp

end FiniteFieldWeights

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype V] [DecidableEq V] [Fintype (V ≃ᵃ[K] V)]

def affineMapsWithInputShift (A : Finset V) : Finset (V ≃ᵃ[K] V) :=
  Finset.univ.filter (fun e => (AffineTripleOrbit.inputShiftEquiv e).2 ∈ A)

theorem affineMapsWithInputShift_halfDensity (A : Finset V)
    (hA : Fintype.card V ≤ 2 * A.card) :
    Fintype.card (V ≃ᵃ[K] V) ≤ 2 * (affineMapsWithInputShift (K := K) A).card := by
  classical
  have h := AffineTripleOrbit.card_affineEquiv_le_two_restricted (F := K)
    (A : Set V) (by simpa [Nat.card_eq_fintype_card] using hA)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype,
    Finset.mem_coe, affineMapsWithInputShift] using h

theorem affineMapsWithInputShift_nonempty (A : Finset V)
    (hA : Fintype.card V ≤ 2 * A.card) :
    (affineMapsWithInputShift (K := K) A).Nonempty := by
  have h := affineMapsWithInputShift_halfDensity (K := K) A hA
  have hp : 0 < Fintype.card (V ≃ᵃ[K] V) := Fintype.card_pos
  apply Finset.card_pos.mp
  omega

end Problem355.AuxiliaryWeights

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.AuxiliaryAffineWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem355.AuxiliaryWeights

open scoped BigOperators

attribute [local instance] Classical.propDecidable

theorem sum_uniform_indicator {Ω : Type*} (A : Finset Ω) (P : Ω → Prop) :
    (∑ a : A, (A.card : ℝ)⁻¹ * (if P a.1 then 1 else 0)) =
      ((A.filter P).card : ℝ) / A.card := by
  classical
  rw [Finset.sum_coe_sort A (fun a : Ω => (A.card : ℝ)⁻¹ * (if P a then 1 else 0)),
    ← Finset.mul_sum, Finset.sum_boole]
  ring

theorem affine_pair_normalization {Q s p : ℝ} (hQ : 2 ≤ Q) (hs : 0 < s)
    (hp : p ≤ 2 * s ^ 2 / (Q * (Q - 1))) :
    (Q / s) ^ 3 * p ≤ 4 * (Q / s) := by
  have hQ0 : 0 < Q := by linarith
  have hD : 0 < Q * (Q - 1) := mul_pos hQ0 (by linarith)
  have hp' : p / 2 ≤ s ^ 2 / (Q * (Q - 1)) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    calc
      p ≤ 2 * s ^ 2 / (Q * (Q - 1)) := hp
      _ = (s ^ 2 / (Q * (Q - 1))) * 2 := by ring
  have hd : Q ^ 2 ≤ 2 * (Q * (Q - 1)) := by nlinarith
  have h := pair_weight_le hQ0.le hs hD hp' hd
  nlinarith

theorem affine_singleton_normalization {Q s p : ℝ} (hQ : 0 < Q) (hs : 0 < s)
    (hp : p ≤ 2 * s / Q) :
    (Q / s) ^ 3 * p ≤ 2 * (Q / s) ^ 2 := by
  calc
    (Q / s) ^ 3 * p ≤ (Q / s) ^ 3 * (2 * s / Q) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = 2 * (Q / s) ^ 2 := by field_simp

section FiniteField

variable {K : Type*} [Field K] [Fintype K]
  [finiteEquivalences : Fintype ((Fin 3 → K) ≃ᵃ[K] (Fin 3 → K))]

theorem affine_pair_weight_le_four
    (p : AffineFamily K (Fin 3 → K) (Fin 2))
    (S : Finset (Fin 3 → K)) (hS : S.Nonempty)
    (A : Finset ((Fin 3 → K) ≃ᵃ[K] (Fin 3 → K)))
    (hA : A.Nonempty)
    (hsize : Fintype.card ((Fin 3 → K) ≃ᵃ[K] (Fin 3 → K)) ≤ 2 * A.card) :
    ((Fintype.card K : ℝ) ^ 3 / S.card) ^ 3 *
      (((A.filter (fun e => ∀ i, e.symm (p.1 i) ∈ S)).card : ℝ) / A.card) ≤
      4 * ((Fintype.card K : ℝ) ^ 3 / S.card) := by
  classical
  have hq : 2 ≤ Fintype.card K := Fintype.one_lt_card
  have hqpow : Fintype.card K ≤ Fintype.card K ^ 3 :=
    Nat.le_self_pow (by decide) _
  have h1 : 1 ≤ Fintype.card K ^ 3 := by omega
  have hp := affine_family_inverse_probability_le p S A hA hsize
  have hc : Nat.card (AffineFamily K (Fin 3 → K) (Fin 2)) =
      Fintype.card K ^ 3 * (Fintype.card K ^ 3 - 1) := by
    change Nat.card {p : Fin (1 + 1) → (Fin 3 → K) // AffineIndependent K p} = _
    rw [IndependentTupleCard.card_affineIndependent K (Fin 3 → K) (by simp)]
    simp [Nat.card_eq_fintype_card]
  simp only [Fintype.card_fin, hc, Nat.cast_mul, Nat.cast_sub h1,
    Nat.cast_pow, Nat.cast_one] at hp
  apply affine_pair_normalization
    (by exact_mod_cast (show 2 ≤ Fintype.card K ^ 3 by omega))
    (by exact_mod_cast hS.card_pos)
  convert hp using 1 <;> try ring_nf
  rw [mul_comm]
  congr 2
  congr 1
  ext e
  simp

theorem affine_singleton_weight_le_two
    (x : Fin 3 → K) (S : Finset (Fin 3 → K)) (hS : S.Nonempty)
    (A : Finset ((Fin 3 → K) ≃ᵃ[K] (Fin 3 → K)))
    (hA : A.Nonempty)
    (hsize : Fintype.card ((Fin 3 → K) ≃ᵃ[K] (Fin 3 → K)) ≤ 2 * A.card) :
    ((Fintype.card K : ℝ) ^ 3 / S.card) ^ 3 *
      (((A.filter (fun e => e.symm x ∈ S)).card : ℝ) / A.card) ≤
      2 * ((Fintype.card K : ℝ) ^ 3 / S.card) ^ 2 := by
  classical
  let p : AffineFamily K (Fin 3 → K) (Fin 1) :=
    ⟨fun _ => x, affineIndependent_of_subsingleton K _⟩
  have hp := affine_family_inverse_probability_le p S A hA hsize
  have hc : Nat.card (AffineFamily K (Fin 3 → K) (Fin 1)) = Fintype.card K ^ 3 := by
    change Nat.card {p : Fin (0 + 1) → (Fin 3 → K) // AffineIndependent K p} = _
    rw [IndependentTupleCard.card_affineIndependent K (Fin 3 → K) (by simp)]
    simp [Nat.card_eq_fintype_card]
  simp only [Fintype.card_fin, hc, Nat.cast_pow, pow_one] at hp
  apply affine_singleton_normalization (by positivity) (by exact_mod_cast hS.card_pos)
  convert hp using 1 <;> try ring_nf
  rw [mul_comm]
  congr 2
  congr 1
  ext e
  simp [p]

end FiniteField

variable {K : Type*} [Field K] [Fintype K]
  [finiteEquivalences : Fintype ((Fin 3 → K) ≃ᵃ[K] (Fin 3 → K))]

def affineInclusionWeight
    (S : Finset (Fin 3 → K))
    (A : Finset ((Fin 3 → K) ≃ᵃ[K] (Fin 3 → K)))
    (p : Fin 3 → (Fin 3 → K)) : ℝ :=
  ((Fintype.card K : ℝ) ^ 3 / S.card) ^ 3 *
    (((A.filter (fun e => ∀ i, e.symm (p i) ∈ S)).card : ℝ) / A.card)

theorem affineInclusionWeight_eq_uniform_sum {K : Type*} [Field K] [Fintype K]
    [Fintype ((Fin 3 → K) ≃ᵃ[K] (Fin 3 → K))]
    (S : Finset (Fin 3 → K))
    (A : Finset ((Fin 3 → K) ≃ᵃ[K] (Fin 3 → K)))
    (p : Fin 3 → (Fin 3 → K)) :
    affineInclusionWeight S A p =
      ((Fintype.card K : ℝ) ^ 3 / S.card) ^ 3 *
        (∑ e : A, (A.card : ℝ)⁻¹ *
          (if ∀ i, p i ∈ S.image (fun x => e.1 x) then 1 else 0)) := by
  classical
  have he (e : (Fin 3 → K) ≃ᵃ[K] (Fin 3 → K)) :
      (∀ i, p i ∈ S.image e) ↔ (∀ i, e.symm (p i) ∈ S) := by
    constructor
    · intro h i
      obtain ⟨x, hx, hxe⟩ := Finset.mem_image.mp (h i)
      simpa only [← hxe, e.symm_apply_apply] using hx
    · intro h i
      exact Finset.mem_image.mpr ⟨e.symm (p i), h i, e.apply_symm_apply (p i)⟩
  have hf : A.filter (fun e : (Fin 3 → K) ≃ᵃ[K] (Fin 3 → K) =>
      ∀ i, p i ∈ S.image (fun x => e x)) =
      A.filter (fun e => ∀ i, e.symm (p i) ∈ S) := by
    ext e
    simp only [Finset.mem_filter, he]
  simp_rw [he]
  unfold affineInclusionWeight
  congr 1
  convert (sum_uniform_indicator A
    (fun e : (Fin 3 → K) ≃ᵃ[K] (Fin 3 → K) =>
      ∀ i, e.symm (p i) ∈ S)).symm using 4 ; try simp
  ext e
  simp

theorem affineInclusionWeight_le_eight
    (S : Finset (Fin 3 → K)) (hS : S.Nonempty)
    (A : Finset ((Fin 3 → K) ≃ᵃ[K] (Fin 3 → K))) (hA : A.Nonempty)
    (hsize : Fintype.card ((Fin 3 → K) ≃ᵃ[K] (Fin 3 → K)) ≤ 2 * A.card)
    (p : Fin 3 → (Fin 3 → K)) (hp : AffineIndependent K p) :
    affineInclusionWeight S A p ≤ 8 := by
  exact affine_triple_weight_le_eight ⟨p, hp⟩ S hS A hA hsize

theorem affineInclusionWeight_le_four_of_ne
    (S : Finset (Fin 3 → K)) (hS : S.Nonempty)
    (A : Finset ((Fin 3 → K) ≃ᵃ[K] (Fin 3 → K))) (hA : A.Nonempty)
    (hsize : Fintype.card ((Fin 3 → K) ≃ᵃ[K] (Fin 3 → K)) ≤ 2 * A.card)
    (p : Fin 3 → (Fin 3 → K)) (i j : Fin 3) (hp : p i ≠ p j) :
    affineInclusionWeight S A p ≤ 4 * ((Fintype.card K : ℝ) ^ 3 / S.card) := by
  classical
  let t : AffineFamily K (Fin 3 → K) (Fin 2) :=
    ⟨![p i, p j], affineIndependent_of_ne K hp⟩
  have hsub : A.filter (fun e => ∀ k, e.symm (p k) ∈ S) ⊆
      A.filter (fun e => ∀ k, e.symm (t.1 k) ∈ S) := by
    intro e he
    obtain ⟨hea, he⟩ := Finset.mem_filter.mp he
    apply Finset.mem_filter.mpr
    refine ⟨hea, ?_⟩
    simpa only [Fin.forall_fin_two, t, Matrix.cons_val_zero,
      Matrix.cons_val_one] using And.intro (he i) (he j)
  have hc : ((A.filter (fun e => ∀ k, e.symm (p k) ∈ S)).card : ℝ) ≤
      (A.filter (fun e => ∀ k, e.symm (t.1 k) ∈ S)).card := by
    exact_mod_cast Finset.card_le_card hsub
  calc
    affineInclusionWeight S A p ≤
        ((Fintype.card K : ℝ) ^ 3 / S.card) ^ 3 *
          (((A.filter (fun e => ∀ k, e.symm (t.1 k) ∈ S)).card : ℝ) / A.card) :=
      mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hc (by positivity)) (by positivity)
    _ ≤ _ := affine_pair_weight_le_four t S hS A hA hsize

theorem affineInclusionWeight_le_two
    (S : Finset (Fin 3 → K)) (hS : S.Nonempty)
    (A : Finset ((Fin 3 → K) ≃ᵃ[K] (Fin 3 → K))) (hA : A.Nonempty)
    (hsize : Fintype.card ((Fin 3 → K) ≃ᵃ[K] (Fin 3 → K)) ≤ 2 * A.card)
    (p : Fin 3 → (Fin 3 → K)) :
    affineInclusionWeight S A p ≤ 2 * ((Fintype.card K : ℝ) ^ 3 / S.card) ^ 2 := by
  classical
  have hsub : A.filter (fun e => ∀ k, e.symm (p k) ∈ S) ⊆
      A.filter (fun e => e.symm (p 0) ∈ S) := by
    intro e he
    obtain ⟨hea, he⟩ := Finset.mem_filter.mp he
    exact Finset.mem_filter.mpr ⟨hea, he 0⟩
  have hc : ((A.filter (fun e => ∀ k, e.symm (p k) ∈ S)).card : ℝ) ≤
      (A.filter (fun e => e.symm (p 0) ∈ S)).card := by
    exact_mod_cast Finset.card_le_card hsub
  calc
    affineInclusionWeight S A p ≤
        ((Fintype.card K : ℝ) ^ 3 / S.card) ^ 3 *
          (((A.filter (fun e => e.symm (p 0) ∈ S)).card : ℝ) / A.card) :=
      mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hc (by positivity)) (by positivity)
    _ ≤ _ := affine_singleton_weight_le_two (p 0) S hS A hA hsize

end Problem355.AuxiliaryWeights

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.AllowedShifts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.Auxiliary

open Finset

section FiniteField

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def badShifts (M S : Finset F) : Finset F :=
  M.biUnion fun m => S.image fun x => m⁻¹ * x

def allowedShifts (M S : Finset F) : Finset F :=
  univ \ badShifts M S

omit [Fintype F] in
lemma mem_badShifts_iff (M S : Finset F)
    (hM : ∀ m ∈ M, m ≠ 0) (a : F) :
    a ∈ badShifts M S ↔ ∃ m ∈ M, m * a ∈ S := by
  simp only [badShifts, mem_biUnion, mem_image]
  constructor
  · rintro ⟨m, hm, x, hx, rfl⟩
    exact ⟨m, hm, by simpa only [mul_inv_cancel_left₀ (hM m hm)] using hx⟩
  · rintro ⟨m, hm, hma⟩
    exact ⟨m, hm, m * a, hma, inv_mul_cancel_left₀ (hM m hm) a⟩

lemma mem_allowedShifts_iff (M S : Finset F)
    (hM : ∀ m ∈ M, m ≠ 0) (a : F) :
    a ∈ allowedShifts M S ↔ ∀ m ∈ M, m * a ∉ S := by
  simp [allowedShifts, mem_badShifts_iff M S hM a]

omit [Fintype F] in
lemma card_badShifts_le (M S : Finset F) :
    (badShifts M S).card ≤ M.card * S.card := by
  exact card_biUnion_le_card_mul M _ S.card fun _ _ => card_image_le

lemma card_le_allowedShifts_add (M S : Finset F) :
    Fintype.card F ≤ (allowedShifts M S).card + M.card * S.card := by
  have h := card_sdiff_add_card_eq_card (subset_univ (badShifts M S))
  rw [card_univ] at h
  calc
    Fintype.card F = (allowedShifts M S).card + (badShifts M S).card := h.symm
    _ ≤ _ := Nat.add_le_add_left (card_badShifts_le M S) _

end FiniteField

def integerWindow (q R : ℕ) : Finset (ZMod q) := by
  classical
  exact (Icc (-(R : ℤ)) (R : ℤ)).image fun z : ℤ => (z : ZMod q)

lemma card_integerWindow_le (q R : ℕ) :
    (integerWindow q R).card ≤ 2 * R + 1 := by
  classical
  calc
    (integerWindow q R).card ≤ (Icc (-(R : ℤ)) (R : ℤ)).card := by
      unfold integerWindow
      exact card_image_le
    _ = 2 * R + 1 := by rw [Int.card_Icc]; omega

lemma intCast_mem_integerWindow (q R : ℕ) (z : ℤ)
    (hz : |z| ≤ (R : ℤ)) : (z : ZMod q) ∈ integerWindow q R := by
  classical
  unfold integerWindow
  apply mem_image.mpr
  exact ⟨z, mem_Icc.mpr (abs_le.mp hz), rfl⟩

def positiveMultipliers (q H : ℕ) : Finset (ZMod q) := by
  classical
  exact (Icc 1 (3 * H)).image fun m : ℕ => (m : ZMod q)

lemma card_positiveMultipliers_le (q H : ℕ) :
    (positiveMultipliers q H).card ≤ 3 * H := by
  classical
  calc
    (positiveMultipliers q H).card ≤ (Icc 1 (3 * H)).card := by
      unfold positiveMultipliers
      exact card_image_le
    _ = 3 * H := by simp

lemma positiveMultipliers_ne_zero (q H : ℕ) (hq : 3 * H < q) :
    ∀ m ∈ positiveMultipliers q H, m ≠ 0 := by
  classical
  intro m hm
  unfold positiveMultipliers at hm
  obtain ⟨n, hn, rfl⟩ := mem_image.mp hm
  intro hz
  exact Nat.not_dvd_of_pos_of_lt (mem_Icc.mp hn).1
    (lt_of_le_of_lt (mem_Icc.mp hn).2 hq) ((ZMod.natCast_eq_zero_iff n q).mp hz)

lemma card_allowed_auxiliary_shifts (q H w : ℕ) [Fact q.Prime] :
    q ≤ (allowedShifts (positiveMultipliers q H) (integerWindow q (3 * H * w))).card +
      3 * H * (6 * H * w + 1) := by
  classical
  have h := card_le_allowedShifts_add (positiveMultipliers q H)
    (integerWindow q (3 * H * w))
  rw [ZMod.card] at h
  refine h.trans (Nat.add_le_add_left ?_ _)
  calc
    (positiveMultipliers q H).card * (integerWindow q (3 * H * w)).card
        ≤ (3 * H) * (2 * (3 * H * w) + 1) :=
      Nat.mul_le_mul (card_positiveMultipliers_le q H)
        (card_integerWindow_le q (3 * H * w))
    _ = _ := by ring

lemma auxiliary_bad_count_lt_half (q H w : ℕ) (hH : 1 ≤ H)
    (hq : 2000 * H ^ 2 ≤ q) (hw : 1000 * H ^ 2 * w ≤ q) :
    2 * (3 * H * (6 * H * w + 1)) < q := by
  have hsq : H ≤ H ^ 2 := by nlinarith
  have hprod : 0 ≤ H ^ 2 * w := Nat.zero_le _
  nlinarith

lemma auxiliary_multiplier_range (q H : ℕ) (hH : 1 ≤ H)
    (hq : 2000 * H ^ 2 ≤ q) : 3 * H < q := by
  have hsq : H ≤ H ^ 2 := by nlinarith
  nlinarith

lemma auxiliary_allowed_card_gt_half (q H w : ℕ) [Fact q.Prime]
    (hH : 1 ≤ H) (hq : 2000 * H ^ 2 ≤ q)
    (hw : 1000 * H ^ 2 * w ≤ q) :
    q < 2 * (allowedShifts (positiveMultipliers q H)
      (integerWindow q (3 * H * w))).card := by
  have hc := card_allowed_auxiliary_shifts q H w
  have hb := auxiliary_bad_count_lt_half q H w hH hq hw
  omega

lemma neg_mem_integerWindow {q R : ℕ} {a : ZMod q}
    (ha : a ∈ integerWindow q R) : -a ∈ integerWindow q R := by
  classical
  unfold integerWindow at *
  obtain ⟨z, hz, rfl⟩ := mem_image.mp ha
  refine mem_image.mpr ⟨-z, ?_, by simp⟩
  apply mem_Icc.mpr
  have hz' := abs_le.mpr (mem_Icc.mp hz)
  exact abs_le.mp (by simpa only [abs_neg] using hz')

lemma int_mul_not_mem_integerWindow (q H R : ℕ) (a : ZMod q)
    (ha : ∀ n : ℕ, 1 ≤ n → n ≤ 3 * H →
      (n : ZMod q) * a ∉ integerWindow q R)
    (m : ℤ) (hm0 : m ≠ 0) (hm : |m| ≤ (3 * H : ℕ)) :
    (m : ZMod q) * a ∉ integerWindow q R := by
  have hn0 : 1 ≤ m.natAbs := Int.natAbs_pos.mpr hm0
  have hnH : m.natAbs ≤ 3 * H := by
    have h : (m.natAbs : ℤ) ≤ (3 * H : ℕ) := by
      simpa only [Int.natCast_natAbs] using hm
    exact_mod_cast h
  have hne := ha m.natAbs hn0 hnH
  by_cases hnonneg : 0 ≤ m
  · have heq : (m.natAbs : ZMod q) = (m : ZMod q) := by
      have h := congrArg (fun z : ℤ => (z : ZMod q)) (Int.natAbs_of_nonneg hnonneg)
      simpa using h
    simpa only [heq] using hne
  · have heq : (m.natAbs : ZMod q) = -(m : ZMod q) := by
      have h : (m.natAbs : ℤ) = -m := by
        rw [Int.natCast_natAbs, abs_of_neg (lt_of_not_ge hnonneg)]
      have h' := congrArg (fun z : ℤ => (z : ZMod q)) h
      simpa using h'
    intro hmem
    apply hne
    rw [heq, neg_mul]
    exact neg_mem_integerWindow hmem

lemma abs_sum_three_le (f : Fin 3 → ℤ) (B : ℤ)
    (hf : ∀ i, |f i| ≤ B) : |∑ i, f i| ≤ 3 * B := by
  calc
    |∑ i, f i| ≤ ∑ i, |f i| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 3, B := sum_le_sum fun i _ => hf i
    _ = 3 * B := by simp

lemma shifted_scalar_short_relation_ne_zero (q H w : ℕ) (a : ZMod q)
    (ha : ∀ n : ℕ, 1 ≤ n → n ≤ 3 * H →
      (n : ZMod q) * a ∉ integerWindow q (3 * H * w))
    (x v : Fin 3 → ℤ) (hx : ∀ i, |x i| ≤ (H : ℤ))
    (hv : ∀ i, 0 ≤ v i ∧ v i ≤ (w : ℤ))
    (hsum : ∑ i, x i ≠ 0) :
    (∑ i, (x i : ZMod q) * (a + (v i : ZMod q))) ≠ 0 := by
  intro hrel
  have hm : |∑ i, x i| ≤ (3 * H : ℕ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using abs_sum_three_le x (H : ℤ) hx
  have hforbid := int_mul_not_mem_integerWindow q H (3 * H * w) a ha
    (∑ i, x i) hsum hm
  have hb : |∑ i, x i * v i| ≤ (3 * H * w : ℕ) := by
    have hb' := abs_sum_three_le (fun i => x i * v i) ((H : ℤ) * w) (by
      intro i
      rw [abs_mul, abs_of_nonneg (hv i).1]
      exact mul_le_mul (hx i) (hv i).2 (hv i).1 (by positivity))
    simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using hb'
  have heq : ((∑ i, x i : ℤ) : ZMod q) * a =
      ((-(∑ i, x i * v i) : ℤ) : ZMod q) := by
    push_cast
    rw [eq_neg_iff_add_eq_zero]
    simpa only [sum_mul, mul_add, sum_add_distrib] using hrel
  apply hforbid
  rw [heq]
  apply intCast_mem_integerWindow
  simpa only [abs_neg] using hb

lemma shifted_vector_short_relation_ne_zero (q H w : ℕ)
    (a : Fin 3 → ZMod q)
    (ha : ∀ n : ℕ, 1 ≤ n → n ≤ 3 * H →
      (n : ZMod q) * a 0 ∉ integerWindow q (3 * H * w))
    (x : Fin 3 → ℤ) (v : Fin 3 → Fin 3 → ℤ)
    (hx : ∀ i, |x i| ≤ (H : ℤ))
    (hv : ∀ i, 0 ≤ v i 0 ∧ v i 0 ≤ (w : ℤ))
    (hsum : ∑ i, x i ≠ 0)
    (G : (Fin 3 → ZMod q) ≃ₗ[ZMod q] (Fin 3 → ZMod q)) :
    (∑ i, (x i : ZMod q) • G (a + fun j => (v i j : ZMod q))) ≠ 0 := by
  intro hrel
  have hrel' : (∑ i, (x i : ZMod q) • (a + fun j => (v i j : ZMod q))) = 0 := by
    apply G.injective
    simpa only [map_sum, map_smul, map_zero] using hrel
  have hzero := congrFun hrel' 0
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.add_apply, Pi.zero_apply, smul_eq_mul] at hzero
  exact shifted_scalar_short_relation_ne_zero q H w (a 0) ha x (fun i => v i 0)
    hx hv hsum hzero

section VectorShifts

variable {F : Type*} [Fintype F] [DecidableEq F]

def vectorShifts (S : Finset F) : Finset (Fin 3 → F) :=
  (S.product (univ.product univ)).image fun p : F × F × F => ![p.1, p.2.1, p.2.2]

lemma mem_vectorShifts_iff (S : Finset F) (a : Fin 3 → F) :
    a ∈ vectorShifts S ↔ a 0 ∈ S := by
  unfold vectorShifts
  constructor
  · rintro h
    obtain ⟨⟨x, y, z⟩, hxyz, rfl⟩ := mem_image.mp h
    exact (mem_product.mp hxyz).1
  · intro ha
    refine mem_image.mpr ⟨(a 0, a 1, a 2), by simp [ha], ?_⟩
    funext i
    fin_cases i <;> rfl

lemma card_vectorShifts (S : Finset F) :
    (vectorShifts S).card = S.card * Fintype.card F ^ 2 := by
  unfold vectorShifts
  rw [card_image_of_injective]
  · simp [pow_two]
  · intro p r h
    apply Prod.ext
    · simpa using congrFun h (0 : Fin 3)
    · apply Prod.ext
      · simpa using congrFun h (1 : Fin 3)
      · simpa using congrFun h (2 : Fin 3)

end VectorShifts

lemma auxiliary_allowed_vector_card_gt_half (q H w : ℕ) [Fact q.Prime]
    (hH : 1 ≤ H) (hq : 2000 * H ^ 2 ≤ q)
    (hw : 1000 * H ^ 2 * w ≤ q) :
    q ^ 3 < 2 * (vectorShifts (allowedShifts (positiveMultipliers q H)
      (integerWindow q (3 * H * w)))).card := by
  rw [card_vectorShifts, ZMod.card]
  have hc := auxiliary_allowed_card_gt_half q H w hH hq hw
  have hqpos : 0 < q := (Fact.out : q.Prime).pos
  have h := Nat.mul_lt_mul_of_pos_right hc (pow_pos hqpos 2)
  nlinarith

end Problem355.Auxiliary

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.AuxiliaryCap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.AuxiliaryCap

variable {F : Type*} [Field F]

def quad (η x y : F) : F := x ^ 2 - η * y ^ 2

theorem quad_eq_zero_iff {η : F} (hη : ¬ IsSquare η) (x y : F) :
    quad η x y = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    have hy : y = 0 := by
      by_contra hy
      apply hη
      refine ⟨x / y, ?_⟩
      have hxy : x ^ 2 = η * y ^ 2 := sub_eq_zero.mp h
      have heq : η = (x / y) ^ 2 := by
        rw [div_pow, eq_div_iff (pow_ne_zero 2 hy)]
        exact hxy.symm
      simpa [pow_two] using heq
    refine ⟨?_, hy⟩
    simpa [quad, hy] using h
  · rintro ⟨rfl, rfl⟩
    simp [quad]

def graph (η : F) : Set (Fin 3 → F) :=
  {p | p 2 = quad η (p 0) (p 1)}

def linePoint (p q : Fin 3 → F) (t : F) : Fin 3 → F :=
  fun i => p i + t * (q i - p i)

theorem linePoint_mem_graph_iff {η : F} (hη : ¬ IsSquare η)
    {p q : Fin 3 → F} (hp : p ∈ graph η) (hq : q ∈ graph η)
    (hpq : p ≠ q) (t : F) :
    linePoint p q t ∈ graph η ↔ t = 0 ∨ t = 1 := by
  constructor
  · intro ht
    have hqdiff : quad η (q 0 - p 0) (q 1 - p 1) ≠ 0 := by
      intro hzero
      obtain ⟨hx, hy⟩ := (quad_eq_zero_iff hη _ _).mp hzero
      have hx' : p 0 = q 0 := (sub_eq_zero.mp hx).symm
      have hy' : p 1 = q 1 := (sub_eq_zero.mp hy).symm
      apply hpq
      funext i
      fin_cases i
      · exact hx'
      · exact hy'
      · exact hp.trans ((congrArg₂ (quad η) hx' hy').trans hq.symm)
    have hprod : t * (t - 1) * quad η (q 0 - p 0) (q 1 - p 1) = 0 := by
      calc
        t * (t - 1) * quad η (q 0 - p 0) (q 1 - p 1) =
            quad η (linePoint p q t 0) (linePoint p q t 1) -
              linePoint p q t 2 := by
                change p 2 = quad η (p 0) (p 1) at hp
                change q 2 = quad η (q 0) (q 1) at hq
                dsimp [linePoint]
                rw [hp, hq]
                dsimp [quad]
                ring
        _ = 0 := sub_eq_zero.mpr ht.symm
    rcases (mul_eq_zero.mp hprod).resolve_right hqdiff with h
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  · rintro (rfl | rfl)
    · simpa [graph, linePoint] using hp
    · simpa [graph, linePoint] using hq

theorem linePoint_eq_lineMap (p q : Fin 3 → F) (t : F) :
    linePoint p q t = AffineMap.lineMap p q t := by
  ext i
  simp [linePoint, AffineMap.lineMap_apply, add_comm]

theorem not_collinear_graph {η : F} (hη : ¬ IsSquare η)
    {p q r : Fin 3 → F} (hp : p ∈ graph η) (hq : q ∈ graph η)
    (hr : r ∈ graph η) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    ¬ Collinear F ({p, q, r} : Set (Fin 3 → F)) := by
  intro hcol
  have hrline := hcol.mem_affineSpan_of_mem_of_ne
    (by simp : p ∈ ({p, q, r} : Set (Fin 3 → F)))
    (by simp : q ∈ ({p, q, r} : Set (Fin 3 → F)))
    (by simp : r ∈ ({p, q, r} : Set (Fin 3 → F))) hpq
  obtain ⟨t, ht⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hrline
  have htgraph : linePoint p q t ∈ graph η := by
    rw [linePoint_eq_lineMap, ht]
    exact hr
  rcases (linePoint_mem_graph_iff hη hp hq hpq t).mp htgraph with ht0 | ht1
  · subst t
    exact hpr (by simpa using ht)
  · subst t
    exact hqr (by simpa using ht)

def graphEquiv (η : F) : (F × F) ≃ graph η where
  toFun xy := ⟨![xy.1, xy.2, quad η xy.1 xy.2], by simp [graph]⟩
  invFun p := (p.val 0, p.val 1)
  left_inv xy := by simp
  right_inv p := by
    apply Subtype.ext
    funext i
    fin_cases i
    · rfl
    · rfl
    · exact p.property.symm

theorem card_graph [Fintype F] (η : F) :
    Nat.card (graph η) = Fintype.card F ^ 2 := by
  rw [Nat.card_congr (graphEquiv η).symm, Nat.card_prod,
    Nat.card_eq_fintype_card, pow_two]

def IsCap (S : Set (Fin 3 → F)) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → p ≠ r → q ≠ r →
    ¬ Collinear F ({p, q, r} : Set (Fin 3 → F))

theorem IsCap.mono {S T : Set (Fin 3 → F)} (hS : IsCap S) (hTS : T ⊆ S) :
    IsCap T := by
  intro p hp q hq r hr hpq hpr hqr
  exact hS p (hTS hp) q (hTS hq) r (hTS hr) hpq hpr hqr

theorem IsCap.image {S : Set (Fin 3 → F)} (hS : IsCap S)
    (f : (Fin 3 → F) →ᵃ[F] (Fin 3 → F)) (hf : Function.Injective f) :
    IsCap (f '' S) := by
  rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ _ ⟨r, hr, rfl⟩ hpq hpr hqr
  have hcol := hS p hp q hq r hr
    (fun h => hpq (congrArg f h)) (fun h => hpr (congrArg f h))
    (fun h => hqr (congrArg f h))
  have hai := (affineIndependent_iff_not_collinear_set).mpr hcol
  have himage := hai.map' f hf
  apply (affineIndependent_iff_not_collinear_set).mp
  convert himage using 1
  funext i
  fin_cases i <;> rfl

theorem IsCap.translate {S : Set (Fin 3 → F)} (hS : IsCap S) (a : Fin 3 → F) :
    IsCap ((fun p => a + p) '' S) := by
  exact hS.image (AffineEquiv.constVAdd F (Fin 3 → F) a).toAffineMap
    (AffineEquiv.constVAdd F (Fin 3 → F) a).injective

theorem isCap_graph {η : F} (hη : ¬ IsSquare η) : IsCap (graph η) := by
  intro p hp q hq r hr hpq hpr hqr
  exact not_collinear_graph hη hp hq hr hpq hpr hqr

noncomputable def graphFinset [Fintype F] (η : F) : Finset (Fin 3 → F) :=
  (Set.toFinite (graph η)).toFinset

@[simp] theorem mem_graphFinset [Fintype F] (η : F) (p : Fin 3 → F) :
    p ∈ graphFinset η ↔ p ∈ graph η := by
  simp [graphFinset]

@[simp] theorem card_graphFinset [Fintype F] (η : F) :
    (graphFinset η).card = Fintype.card F ^ 2 := by
  rw [graphFinset, ← Set.ncard_eq_toFinset_card]
  exact card_graph η

theorem exists_finset_cap [Fintype F] (hF : ringChar F ≠ 2) :
    ∃ S : Finset (Fin 3 → F), S.card = Fintype.card F ^ 2 ∧ IsCap (S : Set (Fin 3 → F)) := by
  obtain ⟨η, hη⟩ := FiniteField.exists_nonsquare hF
  refine ⟨graphFinset η, card_graphFinset η, ?_⟩
  simpa [graphFinset] using isCap_graph hη

end Problem355.AuxiliaryCap

end OAI
end

section
-- module Solutions.OAIQW_Problem355.TranslateAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


open scoped BigOperators

namespace Problem355.TranslateAverage

variable {G : Type*} [AddGroup G] [Fintype G] [DecidableEq G]

omit [Fintype G] in

theorem image_inter_card (S B : Finset G) (a : G) :
    ((S.image (a + ·)) ∩ B).card = (S.filter (fun x => a + x ∈ B)).card := by
  have hset : (S.image (a + ·)) ∩ B =
      (S.filter (fun x => a + x ∈ B)).image (a + ·) := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, hB⟩
      exact ⟨y, ⟨hy, hB⟩, rfl⟩
    · rintro ⟨y, ⟨hy, hB⟩, rfl⟩
      exact ⟨⟨y, hy, rfl⟩, hB⟩
  rw [hset, Finset.card_image_of_injective]
  exact (Equiv.addLeft a).injective

theorem sum_image_inter_card (S B : Finset G) :
    ∑ a : G, ((S.image (a + ·)) ∩ B).card = S.card * B.card := by
  simp_rw [image_inter_card, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  have hin : ∀ x : G, (∑ a : G, if a + x ∈ B then 1 else 0 : ℕ) = B.card := by
    intro x
    calc
      (∑ a : G, if a + x ∈ B then 1 else 0 : ℕ) =
          ∑ a : G, if a ∈ B then 1 else 0 :=
        Equiv.sum_comp (Equiv.addRight x) (fun a => if a ∈ B then (1 : ℕ) else 0)
      _ = B.card := by simp
  simp_rw [hin]
  simp

theorem exists_large_image_inter (S B : Finset G) :
    ∃ a : G, S.card * B.card ≤ Fintype.card G * ((S.image (a + ·)) ∩ B).card := by
  have hsum : (∑ _a : G, S.card * B.card) ≤
      ∑ a : G, Fintype.card G * ((S.image (a + ·)) ∩ B).card := by
    calc
      (∑ _a : G, S.card * B.card) = Fintype.card G * (S.card * B.card) := by simp
      _ = Fintype.card G * (∑ a : G, ((S.image (a + ·)) ∩ B).card) := by
        rw [sum_image_inter_card]
      _ ≤ ∑ a : G, Fintype.card G * ((S.image (a + ·)) ∩ B).card := by
        rw [Finset.mul_sum]
  obtain ⟨a, _, ha⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
  exact ⟨a, ha⟩

end Problem355.TranslateAverage

end OAI
end

section
-- module Solutions.OAIQW_Problem355.CapInBox
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.AuxiliaryCap

variable {F : Type*} [Field F] [Fintype F]

theorem exists_cap_subset (hF : ringChar F ≠ 2) (B : Finset (Fin 3 → F)) :
    ∃ S : Finset (Fin 3 → F), S ⊆ B ∧
      B.card ≤ Fintype.card F * S.card ∧ IsCap (S : Set (Fin 3 → F)) := by
  classical
  obtain ⟨G, hG, hcap⟩ := exists_finset_cap hF
  obtain ⟨a, ha⟩ := TranslateAverage.exists_large_image_inter G B
  refine ⟨G.image (a + ·) ∩ B, Finset.inter_subset_right, ?_, ?_⟩
  · rw [hG, Fintype.card_fun, Fintype.card_fin] at ha
    have hmul : Fintype.card F ^ 2 * B.card ≤
        Fintype.card F ^ 2 *
          (Fintype.card F * (G.image (a + ·) ∩ B).card) := by
      simpa [pow_succ, mul_assoc] using ha
    exact Nat.le_of_mul_le_mul_left hmul (pow_pos Fintype.card_pos 2)
  · apply (hcap.translate a).mono
    intro p hp
    obtain ⟨q, hq, heq⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hp).1
    exact ⟨q, hq, heq⟩

noncomputable def residueInterval (q w : ℕ) : Finset (ZMod q) := by
  classical
  exact (Finset.range w).image (fun x : ℕ => (x : ZMod q))

theorem card_residueInterval {q w : ℕ} (hw : w ≤ q) :
    (residueInterval q w).card = w := by
  classical
  calc
    (residueInterval q w).card = (Finset.range w).card := by
      apply Finset.card_image_iff.mpr
      intro a ha b hb hab
      have hav : a < q := lt_of_lt_of_le (Finset.mem_range.mp ha) hw
      have hbv : b < q := lt_of_lt_of_le (Finset.mem_range.mp hb) hw
      have hv := congrArg ZMod.val hab
      simpa [ZMod.val_natCast_of_lt hav, ZMod.val_natCast_of_lt hbv] using hv
    _ = w := Finset.card_range w

@[simp] theorem mem_residueInterval {q w : ℕ} [NeZero q] (hw : w ≤ q) (x : ZMod q) :
    x ∈ residueInterval q w ↔ x.val < w := by
  classical
  constructor
  · intro hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    have haw := Finset.mem_range.mp ha
    simpa [ZMod.val_natCast_of_lt (lt_of_lt_of_le haw hw)] using haw
  · intro hx
    exact Finset.mem_image.mpr ⟨x.val, Finset.mem_range.mpr hx, ZMod.natCast_zmod_val x⟩

noncomputable def residueBox (q w : ℕ) : Finset (Fin 3 → ZMod q) :=
  Fintype.piFinset (fun _ => residueInterval q w)

@[simp] theorem card_residueBox {q w : ℕ} (hw : w ≤ q) :
    (residueBox q w).card = w ^ 3 := by
  rw [residueBox, Fintype.card_piFinset_const, card_residueInterval hw]

@[simp] theorem mem_residueBox {q w : ℕ} [NeZero q] (hw : w ≤ q)
    (p : Fin 3 → ZMod q) : p ∈ residueBox q w ↔ ∀ i, (p i).val < w := by
  simp [residueBox, Fintype.mem_piFinset, mem_residueInterval hw]

theorem exists_cap_in_residueBox {q w : ℕ} [Fact q.Prime]
    (hq : q ≠ 2) (hw : w ≤ q) :
    ∃ S : Finset (Fin 3 → ZMod q),
      (∀ p ∈ S, ∀ i, (p i).val < w) ∧ w ^ 3 ≤ q * S.card ∧
      IsCap (S : Set (Fin 3 → ZMod q)) := by
  have hchar : ringChar (ZMod q) ≠ 2 := by simpa only [ZMod.ringChar_zmod_n] using hq
  obtain ⟨S, hSB, hcard, hcap⟩ := exists_cap_subset hchar (residueBox q w)
  refine ⟨S, ?_, ?_, hcap⟩
  · intro p hp
    exact (mem_residueBox hw p).mp (hSB hp)
  · simpa [card_residueBox hw, ZMod.card] using hcard

end Problem355.AuxiliaryCap

end OAI
end

section
-- module Solutions.OAIQW_Problem355.ShortRelations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.ShortRelations

open scoped BigOperators

theorem sum_smul_ne_zero_of_sum_eq_zero
    {ι V : Type*} [Fintype ι] {q : ℕ}
    [AddCommGroup V] [Module (ZMod q) V]
    {p : ι → V} (hp : AffineIndependent (ZMod q) p)
    {x : ι → ℤ} (hsum : ∑ i, x i = 0)
    (hshort : ∀ i, |x i| < (q : ℤ)) (hne : x ≠ 0) :
    (∑ i, (x i : ZMod q) • p i) ≠ 0 := by
  classical
  intro hrel
  have hsum' : ∑ i, (x i : ZMod q) = 0 := by
    simpa only [Int.cast_sum, Int.cast_zero] using
      congrArg (fun z : ℤ => (z : ZMod q)) hsum
  have hz : ∀ i, (x i : ZMod q) = 0 := by
    intro i
    exact hp.eq_zero_of_sum_eq_zero hsum' hrel i (Finset.mem_univ i)
  apply hne
  funext i
  exact Int.eq_zero_of_abs_lt_dvd
    ((ZMod.intCast_zmod_eq_zero_iff_dvd (x i) q).1 (hz i)) (hshort i)

theorem sum_smul_ne_zero_of_bounded_coefficients
    {ι V : Type*} [Fintype ι] {q H : ℕ}
    [AddCommGroup V] [Module (ZMod q) V]
    {p : ι → V} (hp : AffineIndependent (ZMod q) p)
    {x : ι → ℤ} (hsum : ∑ i, x i = 0)
    (hshort : ∀ i, |x i| ≤ (H : ℤ)) (hHq : H < q) (hne : x ≠ 0) :
    (∑ i, (x i : ZMod q) • p i) ≠ 0 := by
  apply sum_smul_ne_zero_of_sum_eq_zero hp hsum ?_ hne
  intro i
  exact lt_of_le_of_lt (hshort i) (by exact_mod_cast hHq)

end Problem355.ShortRelations

end OAI
end

section
-- module Solutions.OAIQW_Problem355.AuxiliarySet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.AuxiliarySet

open scoped BigOperators

variable {F : Type*} [Field F]

theorem affineIndependent_of_mem_cap
    {S : Set (Fin 3 → F)} (hS : AuxiliaryCap.IsCap S)
    {p : Fin 3 → (Fin 3 → F)} (hp : ∀ i, p i ∈ S)
    (hinj : Function.Injective p) : AffineIndependent F p := by
  have hcol := hS (p 0) (hp 0) (p 1) (hp 1) (p 2) (hp 2)
    (hinj.ne (by decide)) (hinj.ne (by decide)) (hinj.ne (by decide))
  have h := affineIndependent_iff_not_collinear_set.mpr hcol
  convert h using 1
  funext i
  fin_cases i <;> rfl

noncomputable def transformed (S : Finset (Fin 3 → F)) (a : Fin 3 → F)
    (G : (Fin 3 → F) ≃ₗ[F] (Fin 3 → F)) : Finset (Fin 3 → F) := by
  classical
  exact S.image (fun v => G (a + v))

@[simp] theorem mem_transformed (S : Finset (Fin 3 → F)) (a : Fin 3 → F)
    (G : (Fin 3 → F) ≃ₗ[F] (Fin 3 → F)) (u : Fin 3 → F) :
    u ∈ transformed S a G ↔ ∃ v ∈ S, G (a + v) = u := by
  classical
  simp [transformed]

@[simp] theorem card_transformed (S : Finset (Fin 3 → F)) (a : Fin 3 → F)
    (G : (Fin 3 → F) ≃ₗ[F] (Fin 3 → F)) :
    (transformed S a G).card = S.card := by
  classical
  apply Finset.card_image_iff.mpr
  intro v hv w hw heq
  exact add_left_cancel (G.injective heq)

theorem isCap_transformed {S : Finset (Fin 3 → F)}
    (hS : AuxiliaryCap.IsCap (S : Set (Fin 3 → F)))
    (a : Fin 3 → F) (G : (Fin 3 → F) ≃ₗ[F] (Fin 3 → F)) :
    AuxiliaryCap.IsCap (transformed S a G : Set (Fin 3 → F)) := by
  have h := (hS.translate a).image G.toAffineEquiv.toAffineMap G.injective
  convert h using 1
  ext v
  simp only [Finset.mem_coe, mem_transformed, Set.mem_image]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨a + w, ⟨w, hw, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨w, hw, rfl⟩

theorem short_sum_zero_relation_excluded
    {q H : ℕ} [Fact q.Prime]
    {S : Finset (Fin 3 → ZMod q)}
    (hS : AuxiliaryCap.IsCap (S : Set (Fin 3 → ZMod q)))
    (a : Fin 3 → ZMod q)
    (G : (Fin 3 → ZMod q) ≃ₗ[ZMod q] (Fin 3 → ZMod q))
    {p : Fin 3 → (Fin 3 → ZMod q)}
    (hp : ∀ i, p i ∈ transformed S a G) (hinj : Function.Injective p)
    {x : Fin 3 → ℤ} (hsum : ∑ i, x i = 0)
    (hshort : ∀ i, |x i| ≤ (H : ℤ)) (hHq : H < q) (hne : x ≠ 0) :
    (∑ i, (x i : ZMod q) • p i) ≠ 0 := by
  exact ShortRelations.sum_smul_ne_zero_of_bounded_coefficients
    (affineIndependent_of_mem_cap (isCap_transformed hS a G) hp hinj)
    hsum hshort hHq hne

theorem short_nonzero_sum_relation_excluded
    {q H w : ℕ} [Fact q.Prime]
    {S : Finset (Fin 3 → ZMod q)}
    (hbox : ∀ v ∈ S, (v 0).val < w)
    (a : Fin 3 → ZMod q)
    (ha : ∀ n : ℕ, 1 ≤ n → n ≤ 3 * H →
      (n : ZMod q) * a 0 ∉ Auxiliary.integerWindow q (3 * H * w))
    (G : (Fin 3 → ZMod q) ≃ₗ[ZMod q] (Fin 3 → ZMod q))
    {p : Fin 3 → (Fin 3 → ZMod q)}
    (hp : ∀ i, p i ∈ transformed S a G)
    {x : Fin 3 → ℤ} (hsum : ∑ i, x i ≠ 0)
    (hshort : ∀ i, |x i| ≤ (H : ℤ)) :
    (∑ i, (x i : ZMod q) • p i) ≠ 0 := by
  classical
  choose v hv heq using fun i => (mem_transformed S a G (p i)).mp (hp i)
  let z : Fin 3 → Fin 3 → ℤ := fun i j => (v i j).val
  have hz : ∀ i, (fun j => (z i j : ZMod q)) = v i := by
    intro i
    funext j
    simp [z]
  have hb : ∀ i, 0 ≤ z i 0 ∧ z i 0 ≤ (w : ℤ) := by
    intro i
    constructor
    · exact Int.natCast_nonneg _
    · dsimp [z]
      exact_mod_cast (hbox (v i) (hv i)).le
  have h := Auxiliary.shifted_vector_short_relation_ne_zero q H w a ha x z
    hshort hb hsum G
  simpa only [hz, heq] using h

theorem zero_not_mem_of_allowed
    {q H w : ℕ} [Fact q.Prime] (hH : 1 ≤ H)
    {S : Finset (Fin 3 → ZMod q)}
    (hbox : ∀ v ∈ S, (v 0).val < w)
    (a : Fin 3 → ZMod q)
    (ha : ∀ n : ℕ, 1 ≤ n → n ≤ 3 * H →
      (n : ZMod q) * a 0 ∉ Auxiliary.integerWindow q (3 * H * w))
    (G : (Fin 3 → ZMod q) ≃ₗ[ZMod q] (Fin 3 → ZMod q)) :
    (0 : Fin 3 → ZMod q) ∉ transformed S a G := by
  intro hzero
  have h := short_nonzero_sum_relation_excluded hbox a ha G
    (p := fun _ => 0) (fun _ => hzero) (x := ![1, 0, 0])
    (by norm_num [Fin.sum_univ_succ])
    (by
      intro i
      fin_cases i
      · simpa using (show (1 : ℤ) ≤ H by exact_mod_cast hH)
      · simp
      · simp)
  exact h (by simp)

theorem short_relation_excluded
    {q H w : ℕ} [Fact q.Prime]
    {S : Finset (Fin 3 → ZMod q)}
    (hS : AuxiliaryCap.IsCap (S : Set (Fin 3 → ZMod q)))
    (hbox : ∀ v ∈ S, (v 0).val < w)
    (a : Fin 3 → ZMod q)
    (ha : ∀ n : ℕ, 1 ≤ n → n ≤ 3 * H →
      (n : ZMod q) * a 0 ∉ Auxiliary.integerWindow q (3 * H * w))
    (G : (Fin 3 → ZMod q) ≃ₗ[ZMod q] (Fin 3 → ZMod q))
    {p : Fin 3 → (Fin 3 → ZMod q)}
    (hp : ∀ i, p i ∈ transformed S a G) (hinj : Function.Injective p)
    {x : Fin 3 → ℤ} (hshort : ∀ i, |x i| ≤ (H : ℤ))
    (hHq : H < q) (hne : x ≠ 0) :
    (∑ i, (x i : ZMod q) • p i) ≠ 0 := by
  by_cases hsum : ∑ i, x i = 0
  · exact short_sum_zero_relation_excluded hS a G hp hinj hsum hshort hHq hne
  · exact short_nonzero_sum_relation_excluded hbox a ha G hp hsum hshort

theorem transformed_properties
    {q H w : ℕ} [Fact q.Prime] (hH : 1 ≤ H) (hHq : H < q)
    {S : Finset (Fin 3 → ZMod q)}
    (hS : AuxiliaryCap.IsCap (S : Set (Fin 3 → ZMod q)))
    (hbox : ∀ v ∈ S, (v 0).val < w)
    (a : Fin 3 → ZMod q)
    (ha : ∀ n : ℕ, 1 ≤ n → n ≤ 3 * H →
      (n : ZMod q) * a 0 ∉ Auxiliary.integerWindow q (3 * H * w))
    (G : (Fin 3 → ZMod q) ≃ₗ[ZMod q] (Fin 3 → ZMod q)) :
    (transformed S a G).card = S.card ∧
      (0 : Fin 3 → ZMod q) ∉ transformed S a G ∧
      AuxiliaryCap.IsCap (transformed S a G : Set (Fin 3 → ZMod q)) ∧
      ∀ p : Fin 3 → (Fin 3 → ZMod q),
        (∀ i, p i ∈ transformed S a G) → Function.Injective p →
        ∀ x : Fin 3 → ℤ, (∀ i, |x i| ≤ (H : ℤ)) → x ≠ 0 →
          (∑ i, (x i : ZMod q) • p i) ≠ 0 := by
  refine ⟨card_transformed S a G, zero_not_mem_of_allowed hH hbox a ha G,
    isCap_transformed hS a G, ?_⟩
  intro p hp hinj x hx hne
  exact short_relation_excluded hS hbox a ha G hp hinj hx hHq hne

theorem le_twice_mul_div {q d : ℕ} (hd : 0 < d) (hdq : d ≤ q) :
    q ≤ 2 * d * (q / d) := by
  have hquot : 1 ≤ q / d := (Nat.le_div_iff_mul_le hd).mpr (by simpa using hdq)
  have hrem := Nat.mod_lt q hd
  have hsplit := Nat.mod_add_div q d
  have hprod : d ≤ d * (q / d) := by
    simpa using Nat.mul_le_mul_left d hquot
  nlinarith

end Problem355.AuxiliarySet

end OAI
end

section
-- module Solutions.OAIQW_Problem355.LiftingProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

open scoped BigOperators

namespace Problem355.LiftingProbability

theorem sum_comp_of_constant_fibres {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    (f : X → Y) (M : ℕ)
    (hf : ∀ y, (Finset.univ.filter (fun x => f x = y)).card = M)
    (p : Y → ℝ) :
    (∑ x, p (f x)) = (M : ℝ) * ∑ y, p y := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ f (fun x => p (f x)), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  calc
    (∑ x ∈ Finset.univ.filter (fun x => f x = y), p (f x)) =
        ∑ _x ∈ Finset.univ.filter (fun x => f x = y), p y := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [(Finset.mem_filter.mp hx).2]
    _ = (M : ℝ) * p y := by simp [hf]

theorem sum_uniform_lift {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    (f : X → Y) (M : ℕ) (hM : 0 < M)
    (hf : ∀ y, (Finset.univ.filter (fun x => f x = y)).card = M)
    (p : Y → ℝ) (hp : ∑ y, p y = 1) :
    (∑ x, p (f x) / (M : ℝ)) = 1 := by
  classical
  rw [← Finset.sum_div, sum_comp_of_constant_fibres f M hf p, hp, mul_one]
  exact div_self (by exact_mod_cast Nat.ne_of_gt hM)

abbrev TripleIn {B : Type*} (V : Finset B) (b : Fin 3 → B) : Prop :=
  ∀ i, b i ∈ V

def inclusionMass {Ω B : Type*} [Fintype Ω]
    (w : Ω → ℝ) (V : Ω → Finset B) (b : Fin 3 → B) : ℝ := by
  classical
  exact ∑ ω, if TripleIn (V ω) b then w ω else 0

def mainMass {A : Type*} (O : Finset A) (a : A) : ℝ := by
  classical
  exact if a ∈ O then 1 / (O.card : ℝ) else 0

theorem sum_mainMass {A : Type*} [Fintype A] (O : Finset A) (hO : O.Nonempty) :
    (∑ a, mainMass O a) = 1 := by
  classical
  unfold mainMass
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  have hc : (O.card : ℝ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr hO
  exact mul_one_div_cancel hc

def auxiliaryMass {Ω B : Type*} [Fintype Ω]
    (w : Ω → ℝ) (V : Ω → Finset B) (s : ℕ) (b : Fin 3 → B) : ℝ :=
  inclusionMass w V b / (s : ℝ) ^ 3

def residueMass {A Ω B : Type*} [Fintype Ω]
    (O : Finset A) (w : Ω → ℝ) (V : Ω → Finset B) (s : ℕ)
    (r : A × (Fin 3 → B)) : ℝ :=
  mainMass O r.1 * auxiliaryMass w V s r.2

def liftedMass {X A Ω B : Type*} [Fintype Ω]
    (f : X → A) (g : X → (Fin 3 → B))
    (O : Finset A) (w : Ω → ℝ) (V : Ω → Finset B) (s M : ℕ) (x : X) : ℝ :=
  residueMass O w V s (f x, g x) / (M : ℝ)

def auxiliaryWeight {Ω B : Type*} [Fintype Ω]
    (q s : ℕ) (w : Ω → ℝ) (V : Ω → Finset B) (b : Fin 3 → B) : ℝ :=
  (((q : ℝ) ^ 3) / (s : ℝ)) ^ 3 * inclusionMass w V b

def conditionalColumnMass {X A B : Type*}
    (f : X → A) (g : X → B) (a : A) (V : Finset B) (s L : ℕ) (x : X) : ℝ := by
  classical
  exact if f x = a ∧ g x ∈ V then 1 / ((s : ℝ) * (L : ℝ) ^ 3) else 0

theorem conditionalColumnMass_nonneg {X A B : Type*}
    (f : X → A) (g : X → B) (a : A) (V : Finset B) (s L : ℕ) (x : X) :
    0 ≤ conditionalColumnMass f g a V s L x := by
  classical
  unfold conditionalColumnMass
  split_ifs <;> positivity

theorem sum_conditionalColumnMass {X A B : Type*} [Fintype X] [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (f : X → A) (g : X → B) (a : A) (V : Finset B) (s L : ℕ)
    (hs : 0 < s) (hL : 0 < L) (hV : V.card = s)
    (hf : ∀ r : A × B, (Finset.univ.filter (fun x => (f x, g x) = r)).card = L ^ 3) :
    (∑ x, conditionalColumnMass f g a V s L x) = 1 := by
  classical
  have hVne : V.Nonempty := Finset.card_pos.mp (by omega)
  let p : A × B → ℝ := fun r => (if r.1 = a then 1 else 0) * mainMass V r.2
  have hp : (∑ r, p r) = 1 := by
    dsimp [p]
    rw [Fintype.sum_prod_type]
    change (∑ x : A, ∑ y : B, ((if x = a then 1 else 0) : ℝ) * mainMass V y) = 1
    simp_rw [← Finset.mul_sum]
    simp_rw [sum_mainMass V hVne]
    simp only [mul_one]
    simp
  have hnormal := sum_uniform_lift (fun x => (f x, g x)) (L ^ 3)
    (pow_pos hL _) hf p hp
  calc
    (∑ x, conditionalColumnMass f g a V s L x) =
        ∑ x, p (f x, g x) / ((L ^ 3 : ℕ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro x hx
      dsimp [p]
      by_cases hfa : f x = a <;> by_cases hgv : g x ∈ V <;>
        simp [conditionalColumnMass, mainMass, hfa, hgv, hV, div_eq_mul_inv, mul_inv_rev,
          mul_comm]
    _ = 1 := hnormal

def pushforwardMass {Θ A : Type*} [Fintype Θ]
    (ρ : Θ → ℝ) (F : Θ → A) (a : A) : ℝ := by
  classical
  exact ∑ θ, if a = F θ then ρ θ else 0

end Problem355.LiftingProbability

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.AuxiliarySamplingLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.AuxiliarySampling

open scoped BigOperators

structure Law (q H : ℕ) [Fact q.Prime] where
  Outcome : Type
  outcomeFintype : Fintype Outcome
  weight : Outcome → ℝ
  sets : Outcome → Finset (Fin 3 → ZMod q)
  size : ℕ
  size_pos : 0 < size
  weight_nonneg : ∀ ω, 0 ≤ weight ω
  weight_sum : @Finset.sum Outcome ℝ _ (@Finset.univ Outcome outcomeFintype) weight = 1
  sets_card : ∀ ω, (sets ω).card = size
  size_lower : q ^ 2 ≤ 2000 ^ 3 * H ^ 6 * size
  zero_not_mem : ∀ ω, (0 : Fin 3 → ZMod q) ∉ sets ω
  isCap : ∀ ω, AuxiliaryCap.IsCap (sets ω : Set (Fin 3 → ZMod q))
  short_relation : ∀ ω (p : Fin 3 → (Fin 3 → ZMod q)),
    (∀ i, p i ∈ sets ω) → Function.Injective p →
    ∀ x : Fin 3 → ℤ, (∀ i, |x i| ≤ (H : ℤ)) → x ≠ 0 →
      (∑ i, (x i : ZMod q) • p i) ≠ 0
  weight_le_eight : ∀ p : Fin 3 → (Fin 3 → ZMod q),
    AffineIndependent (ZMod q) p →
    @LiftingProbability.auxiliaryWeight Outcome (Fin 3 → ZMod q) outcomeFintype
      q size weight sets p ≤ 8
  weight_le_four : ∀ (p : Fin 3 → (Fin 3 → ZMod q)) (i j : Fin 3), p i ≠ p j →
    @LiftingProbability.auxiliaryWeight Outcome (Fin 3 → ZMod q) outcomeFintype
      q size weight sets p ≤ 4 * ((q : ℝ) ^ 3 / size)
  weight_le_two : ∀ p : Fin 3 → (Fin 3 → ZMod q),
    @LiftingProbability.auxiliaryWeight Outcome (Fin 3 → ZMod q) outcomeFintype
      q size weight sets p ≤ 2 * ((q : ℝ) ^ 3 / size) ^ 2

attribute [instance] Law.outcomeFintype

theorem affine_apply_inputShift {q : ℕ} [Fact q.Prime]
    (e : (Fin 3 → ZMod q) ≃ᵃ[ZMod q] (Fin 3 → ZMod q))
    (x : Fin 3 → ZMod q) :
    e x = (AffineTripleOrbit.inputShiftEquiv e).1
      ((AffineTripleOrbit.inputShiftEquiv e).2 + x) := by
  have h := congrArg
    (fun f : (Fin 3 → ZMod q) ≃ᵃ[ZMod q] (Fin 3 → ZMod q) => f x)
    (AffineTripleOrbit.inputShiftEquiv.symm_apply_apply e)
  exact h.symm.trans (AffineTripleOrbit.inputShiftEquiv_symm_apply
    (AffineTripleOrbit.inputShiftEquiv e).1 (AffineTripleOrbit.inputShiftEquiv e).2 x)

theorem nonempty_law_of_cap {q H w : ℕ} [Fact q.Prime]
    (hH : 1 ≤ H) (hHq : H < q)
    (S : Finset (Fin 3 → ZMod q)) (hS : S.Nonempty)
    (hcap : AuxiliaryCap.IsCap (S : Set (Fin 3 → ZMod q)))
    (hbox : ∀ v ∈ S, (v 0).val < w)
    (hsize : q ^ 2 ≤ 2000 ^ 3 * H ^ 6 * S.card)
    (A : Finset (Fin 3 → ZMod q)) (hA : q ^ 3 ≤ 2 * A.card)
    (hallowed : ∀ a ∈ A, ∀ n : ℕ, 1 ≤ n → n ≤ 3 * H →
      (n : ZMod q) * a 0 ∉ Auxiliary.integerWindow q (3 * H * w)) :
    Nonempty (Law q H) := by
  classical
  let Aff := (Fin 3 → ZMod q) ≃ᵃ[ZMod q] (Fin 3 → ZMod q)
  let : Finite Aff := Finite.of_injective
    (fun e : Aff => (e : (Fin 3 → ZMod q) → (Fin 3 → ZMod q)))
    DFunLike.coe_injective
  let : Fintype Aff := Fintype.ofFinite Aff
  let T : Finset Aff := AuxiliaryWeights.affineMapsWithInputShift A
  have hA' : Fintype.card (Fin 3 → ZMod q) ≤ 2 * A.card := by
    simpa using hA
  have hT : T.Nonempty := AuxiliaryWeights.affineMapsWithInputShift_nonempty A hA'
  have hTsize : Fintype.card Aff ≤ 2 * T.card :=
    AuxiliaryWeights.affineMapsWithInputShift_halfDensity A hA'
  let μ : T → ℝ := fun _ => (T.card : ℝ)⁻¹
  let V : T → Finset (Fin 3 → ZMod q) := fun e => S.image e.1
  have hV (e : T) : V e = AuxiliarySet.transformed S
      (AffineTripleOrbit.inputShiftEquiv e.1).2
      (AffineTripleOrbit.inputShiftEquiv e.1).1 := by
    ext y
    simp only [V, Finset.mem_image, AuxiliarySet.mem_transformed]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, (affine_apply_inputShift e.1 x).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, affine_apply_inputShift e.1 x⟩
  have hall (e : T) : ∀ n : ℕ, 1 ≤ n → n ≤ 3 * H →
      (n : ZMod q) * (AffineTripleOrbit.inputShiftEquiv e.1).2 0 ∉
        Auxiliary.integerWindow q (3 * H * w) := by
    apply hallowed
    exact (Finset.mem_filter.mp e.2).2
  have hprops (e : T) := AuxiliarySet.transformed_properties hH hHq hcap hbox
    (AffineTripleOrbit.inputShiftEquiv e.1).2 (hall e)
    (AffineTripleOrbit.inputShiftEquiv e.1).1
  have hW (p : Fin 3 → (Fin 3 → ZMod q)) :
      LiftingProbability.auxiliaryWeight q S.card μ V p =
        AuxiliaryWeights.affineInclusionWeight S T p := by
    rw [AuxiliaryWeights.affineInclusionWeight_eq_uniform_sum]
    simp only [LiftingProbability.auxiliaryWeight, LiftingProbability.inclusionMass,
      ZMod.card]
    congr 1
    apply Finset.sum_congr rfl
    intro e he
    simp only [LiftingProbability.TripleIn, μ, V, Finset.mem_image]
    split_ifs <;> simp_all
  refine ⟨{
    Outcome := T
    outcomeFintype := inferInstance
    weight := μ
    sets := V
    size := S.card
    size_pos := hS.card_pos
    weight_nonneg := ?_
    weight_sum := ?_
    sets_card := ?_
    size_lower := hsize
    zero_not_mem := ?_
    isCap := ?_
    short_relation := ?_
    weight_le_eight := ?_
    weight_le_four := ?_
    weight_le_two := ?_ }⟩
  · intro e
    dsimp [μ]
    positivity
  · simp only [μ, Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast hT.card_pos.ne')
  · intro e
    rw [hV]
    exact (hprops e).1
  · intro e
    rw [hV]
    exact (hprops e).2.1
  · intro e
    rw [hV]
    exact (hprops e).2.2.1
  · intro e p hp hinj x hx hne
    exact (hprops e).2.2.2 p (fun i => hV e ▸ hp i) hinj x hx hne
  · intro p hp
    rw [hW]
    exact AuxiliaryWeights.affineInclusionWeight_le_eight S hS T hT hTsize p hp
  · intro p i j hp
    rw [hW]
    simpa only [ZMod.card] using
      AuxiliaryWeights.affineInclusionWeight_le_four_of_ne S hS T hT hTsize p i j hp
  · intro p
    rw [hW]
    simpa only [ZMod.card] using
      AuxiliaryWeights.affineInclusionWeight_le_two S hS T hT hTsize p

theorem nonempty_law {q H : ℕ} [Fact q.Prime]
    (hH : 1 ≤ H) (hq : 2000 * H ^ 2 ≤ q) : Nonempty (Law q H) := by
  classical
  let w := q / (1000 * H ^ 2)
  have hd : 0 < 1000 * H ^ 2 := by positivity
  have hdq : 1000 * H ^ 2 ≤ q := by omega
  have hwq : w ≤ q := Nat.div_le_self _ _
  have hq2 : q ≠ 2 := by
    have hHsq : 1 ≤ H ^ 2 := by nlinarith
    omega
  obtain ⟨S, hbox, hsize, hcap⟩ := AuxiliaryCap.exists_cap_in_residueBox hq2 hwq
  have hfloor : q ≤ 2000 * H ^ 2 * w := by
    calc
      q ≤ 2 * (1000 * H ^ 2) * w := AuxiliarySet.le_twice_mul_div hd hdq
      _ = 2000 * H ^ 2 * w := by ring
  have hc : q ^ 2 ≤ 2000 ^ 3 * H ^ 6 * S.card := by
    have hcube : q ^ 3 ≤ (2000 * H ^ 2 * w) ^ 3 := by gcongr
    have hm : q * q ^ 2 ≤ q * (2000 ^ 3 * H ^ 6 * S.card) := by
      calc
        q * q ^ 2 = q ^ 3 := by ring
        _ ≤ (2000 * H ^ 2 * w) ^ 3 := hcube
        _ = (2000 ^ 3 * H ^ 6) * w ^ 3 := by ring
        _ ≤ (2000 ^ 3 * H ^ 6) * (q * S.card) := Nat.mul_le_mul_left _ hsize
        _ = q * (2000 ^ 3 * H ^ 6 * S.card) := by ring
    exact Nat.le_of_mul_le_mul_left hm (Fact.out : q.Prime).pos
  have hS : S.Nonempty := by
    apply Finset.card_pos.mp
    by_contra hn
    have hz : S.card = 0 := by omega
    have hp : 0 < q ^ 2 := pow_pos (Fact.out : q.Prime).pos 2
    simp only [hz, mul_zero] at hc
    omega
  let A := Auxiliary.vectorShifts (Auxiliary.allowedShifts
    (Auxiliary.positiveMultipliers q H) (Auxiliary.integerWindow q (3 * H * w)))
  have hw : 1000 * H ^ 2 * w ≤ q := Nat.mul_div_le _ _
  have hA : q ^ 3 ≤ 2 * A.card :=
    (Auxiliary.auxiliary_allowed_vector_card_gt_half q H w hH hq hw).le
  have hmult : 3 * H < q := Auxiliary.auxiliary_multiplier_range q H hH hq
  apply nonempty_law_of_cap hH (by omega) S hS hcap (fun v hv => hbox v hv 0) hc A hA
  intro a ha n hn hnH
  have ha' := (Auxiliary.mem_vectorShifts_iff _ a).mp ha
  have ha'' := (Auxiliary.mem_allowedShifts_iff _ _
    (Auxiliary.positiveMultipliers_ne_zero q H hmult) (a 0)).mp ha'
  apply ha''
  exact Finset.mem_image.mpr ⟨n, Finset.mem_Icc.mpr ⟨hn, hnH⟩, rfl⟩

end Problem355.AuxiliarySampling

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.DigitUniqueness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.Digits

theorem ofDigits_ofFn_eq_sum (b : ℕ) {k : ℕ} (d : Fin k → ℕ) :
    Nat.ofDigits b (List.ofFn d) = ∑ i : Fin k, d i * b ^ i.val := by
  simp [Nat.ofDigits_eq_sum_mapIdx, List.mapIdx_eq_ofFn,
    List.length_ofFn, Fin.val_cast, List.sum_ofFn]

end Problem355.Digits

end OAI
end

section
-- module Solutions.OAIQW_Problem355.DigitUnits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.DigitUnits

open scoped BigOperators

lemma count_mod_period {r a : ℕ} (ha : a < r) :
    Nat.count (fun n => n % r = a) r = 1 := by
  rw [Nat.count_eq_card_filter_range]
  have hset : (Finset.range r).filter (fun n => n % r = a) = {a} := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨hn, he⟩
      simpa [Nat.mod_eq_of_lt hn] using he
    · rintro rfl
      exact ⟨ha, Nat.mod_eq_of_lt ha⟩
  rw [hset]
  simp

lemma count_mod_mul {r a : ℕ} (ha : a < r) (m : ℕ) :
    Nat.count (fun n => n % r = a) (r * m) = m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ, Nat.count_add, ih]
    simp only [Nat.add_mod, Nat.mul_mod_right, Nat.zero_add, Nat.mod_mod]
    rw [count_mod_period ha]

theorem card_positive_residue_fiber {r a : ℕ} (ha : a < r) (m : ℕ) :
    ((Finset.Icc 1 (r * m)).filter (fun n => n % r = a)).card = m := by
  have hperiod : Function.Periodic (fun n : ℕ => n % r = a) (r * m) := by
    intro n
    simp [Nat.add_mod]
  have hinterval : Finset.Icc 1 (r * m) = Finset.Ico 1 (1 + r * m) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hinterval, Nat.filter_Ico_card_eq_of_periodic 1 (r * m)
    (fun n => n % r = a) hperiod, count_mod_mul ha]

theorem card_positive_zmod_fiber {r : ℕ} [NeZero r] (a : ZMod r) (m : ℕ) :
    ((Finset.Icc 1 (r * m)).filter (fun n : ℕ => (n : ZMod r) = a)).card = m := by
  have heq (n : ℕ) : (n : ZMod r) = a ↔ n % r = a.val := by
    constructor
    · intro h
      simpa using congrArg ZMod.val h
    · intro h
      apply ZMod.val_injective r
      simpa using h
  simp_rw [heq]
  exact card_positive_residue_fiber a.val_lt m

def digitFiber (r m : ℕ) (a : ZMod r) : Finset ℕ :=
  (Finset.Icc 1 (r * m)).filter (fun n : ℕ => (n : ZMod r) = a)

noncomputable def digitFiberEquiv {r : ℕ} [NeZero r] (a : ZMod r) (m : ℕ) :
    Fin m ≃ ↥(digitFiber r m a) :=
  (Fintype.equivFinOfCardEq (by
    exact (Fintype.card_coe (digitFiber r m a)).trans (card_positive_zmod_fiber a m))).symm

lemma digitFiberEquiv_bounds {r : ℕ} [NeZero r] (a : ZMod r) (m : ℕ) (i : Fin m) :
    1 ≤ (digitFiberEquiv a m i).val ∧ (digitFiberEquiv a m i).val ≤ r * m ∧
      ((digitFiberEquiv a m i).val : ZMod r) = a := by
  have h := (digitFiberEquiv a m i).property
  simpa only [digitFiber, Finset.mem_filter, Finset.mem_Icc, and_assoc] using h

end Problem355.DigitUnits

end OAI
end

section
-- module Solutions.OAIQW_Problem355.RankOneMinors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.UnitPivot

variable {R : Type*} [CommRing R]
variable {m n : Type*}

def MinorsVanish (A : Matrix m n R) : Prop :=
  ∀ i k j l, A i j * A k l = A i l * A k j

end Problem355.UnitPivot

end OAI
end

section
-- module Solutions.OAIQW_Problem355.ConditionalMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.ConditionalMatrix

open scoped BigOperators

abbrev Header (X : Type*) (k : ℕ) :=
  (Fin 3 → Fin k → X) × (Fin 2 → Fin k → X)

abbrev Draw (X : Type*) (k : ℕ) :=
  Header X k × ((Fin 2 × Fin 2) → Fin k → X)

def picked {X : Type*} {k : ℕ} (z : Draw X k) (a c : Fin 3) (v : Fin k) : X :=
  Fin.cases (z.1.1 c v)
    (fun i => Fin.cases (z.1.2 i v) (fun l => z.2 (i, l) v) c) a

def drawEquiv {X : Type*} {k : ℕ} : Draw X k ≃ (Fin 3 → Fin 3 → Fin k → X) where
  toFun z := picked z
  invFun f := ((fun c v => f 0 c v, fun i v => f i.succ 0 v),
    fun i v => f i.1.succ i.2.succ v)
  left_inv z := by
    apply Prod.ext
    · apply Prod.ext <;> rfl
    · funext i v
      rfl
  right_inv f := by
    funext a c v
    refine Fin.cases ?_ (fun i => ?_) a
    · rfl
    · refine Fin.cases ?_ (fun l => ?_) c <;> rfl

def entryValue {X : Type*} {B k : ℕ}
    (digit : Fin 3 → Fin 3 → Fin k → X → Fin B)
    (z : Draw X k) (a c : Fin 3) : ℕ :=
  ∑ v : Fin k, (digit a c v (picked z a c v)).val * B ^ v.val

def residueMatrix {X : Type*} {B k : ℕ}
    (digit : Fin 3 → Fin 3 → Fin k → X → Fin B)
    (z : Draw X k) (j : ℕ) : Matrix (Fin 3) (Fin 3) (ZMod (B ^ j)) :=
  fun a c => (entryValue digit z a c : ZMod (B ^ j))

def arrayMatrix {X : Type*} {B k : ℕ}
    (digit : Fin 3 → Fin 3 → Fin k → X → Fin B)
    (f : Fin 3 → Fin 3 → Fin k → X) (j : ℕ) :
    Matrix (Fin 3) (Fin 3) (ZMod (B ^ j)) :=
  fun a c => ((∑ v : Fin k, (digit a c v (f a c v)).val * B ^ v.val : ℕ) : ZMod (B ^ j))

theorem encoded_isUnit {B k j : ℕ} (hB : B.Prime) (hk : 0 < k) (hj : 0 < j)
    (d : Fin k → Fin B) (hpos : ∀ v, 0 < (d v).val) :
    IsUnit (((∑ v : Fin k, (d v).val * B ^ v.val : ℕ)) : ZMod (B ^ j)) := by
  apply (ZMod.isUnit_natCast_iff_not_dvd_pow hB hj).mpr
  intro hdiv
  have hm := Nat.mod_eq_zero_of_dvd hdiv
  cases k with
  | zero => omega
  | succ k =>
    rw [← Digits.ofDigits_ofFn_eq_sum, Nat.ofDigits_mod_eq_head!, List.ofFn_succ] at hm
    have heq : (d 0).val % B = 0 := by simpa using hm
    rw [Nat.mod_eq_of_lt (d 0).isLt] at heq
    exact (Nat.ne_of_gt (hpos 0)) heq

noncomputable def prescribedDigit {r m B k : ℕ} [NeZero r] (hbound : r * m < B)
    (residue : Fin 3 → Fin 3 → Fin k → ZMod r)
    (a c : Fin 3) (v : Fin k) (x : Fin m) : Fin B :=
  ⟨(DigitUnits.digitFiberEquiv (residue a c v) m x).val,
    lt_of_le_of_lt (DigitUnits.digitFiberEquiv_bounds (residue a c v) m x).2.1 hbound⟩

lemma prescribedDigit_positive {r m B k : ℕ} [NeZero r] (hbound : r * m < B)
    (residue : Fin 3 → Fin 3 → Fin k → ZMod r) (a c : Fin 3) (v : Fin k) (x : Fin m) :
    0 < (prescribedDigit hbound residue a c v x).val :=
  (DigitUnits.digitFiberEquiv_bounds (residue a c v) m x).1

end Problem355.ConditionalMatrix

end OAI
end

section
-- module Solutions.OAIQW_Problem355.ConditionalSamples
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.ConditionalSamples

noncomputable section

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]

def productWeight (μ : α → ℝ) (x : ι → α) : ℝ := ∏ i, μ (x i)

variable {Θ : Type*}

def sharedWeight (ρ : Θ → ℝ) (μ : Θ → α → ℝ) (z : Θ × (ι → α)) : ℝ :=
  ρ z.1 * productWeight (μ z.1) z.2

end
end Problem355.ConditionalSamples

end OAI
end

section
-- module Solutions.OAIQW_Problem355.DigitColumnLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.DigitColumnLaw

noncomputable section
open scoped BigOperators

abbrev Column (X : Type*) (k : ℕ) := Fin 3 → Fin k → X
abbrev Latent (Λ X : Type*) (k : ℕ) := Λ × Column X k
abbrev Array (X : Type*) (k : ℕ) := Fin 3 → Fin 3 → Fin k → X

def uniformWeight (α : Type*) [Fintype α] (_ : α) : ℝ := 1 / Fintype.card α

lemma uniformWeight_nonneg (α : Type*) [Fintype α] (a : α) :
    0 ≤ uniformWeight α a := by unfold uniformWeight; positivity

lemma sum_uniformWeight (α : Type*) [Fintype α] [Nonempty α] :
    ∑ a : α, uniformWeight α a = 1 := by
  have hcard : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  simp only [uniformWeight, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_one_div_cancel hcard.ne'

def tripleEquiv {Λ X : Type*} {k : ℕ} :
    (Fin 3 → Latent Λ X k) ≃ ((Fin 3 → Λ) × Array X k) where
  toFun s := (fun c => (s c).1, fun a c v => (s c).2 a v)
  invFun t := fun c => (t.1 c, fun a v => t.2 a c v)
  left_inv s := by funext c; rfl
  right_inv t := by cases t; rfl

def residueColumn {Λ X : Type*} {B k : ℕ}
    (digit : Λ → Fin 3 → Fin k → X → Fin B)
    (x : Latent Λ X k) : Fin 3 → ZMod (B ^ k) :=
  fun a => ((∑ v : Fin k, (digit x.1 a v (x.2 a v)).val * B ^ v.val : ℕ) : ZMod (B ^ k))

end
end Problem355.DigitColumnLaw

end OAI
end

section
-- module Solutions.OAIQW_Problem355.DesignatedCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.DesignatedCoefficient

open Polynomial

def position (T : ℕ) (i : Fin 3) (a : Fin T) : ℕ :=
  ![a.val, T * a.val, T ^ 2 - (T + 1) * a.val] i

def polynomialMatrix {R : Type*} [CommRing R] (T : ℕ)
    (f : Fin 3 → Fin T → Fin 3 → R) : Matrix (Fin 3) (Fin 3) R[X] :=
  fun i j => ∑ a : Fin T, monomial (position T i a) (f i a j)

end Problem355.DesignatedCoefficient

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.DeterminantCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.DigitCoefficients
noncomputable section
open scoped BigOperators
open Polynomial

def digitPolynomial (k : ℕ) (a : ℕ → ℤ) : ℤ[X] :=
  ∑ i ∈ Finset.range k, monomial i (a i)

def determinantPolynomial (k : ℕ) (d : Fin 3 → Fin 3 → ℕ → ℤ) : ℤ[X] :=
  Matrix.det (Matrix.of (fun i j => digitPolynomial k (d i j)))

end
end Problem355.DigitCoefficients

end OAI
end

section
-- module Solutions.OAIQW_Problem355.LabelResidues
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace Problem355.LabelResidues

open DesignatedCoefficient

def residue {R Λ : Type*} [AddCommMonoid R] (T : ℕ)
    (f : Fin 3 → Fin T → Λ → R) (i : Fin 3) (v : ℕ) (x : Λ) : R :=
  ∑ a : Fin T, if position T i a = v then f i a x else 0

end Problem355.LabelResidues

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.NormFoundation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.NormFoundation

open Matrix

def momentColumn {K : Type*} [CommRing K] (x : K) : Fin 3 → K :=
  ![1, x, x ^ 2]

def momentMatrix {K : Type*} [CommRing K] (x y z : K) : Matrix (Fin 3) (Fin 3) K :=
  !![1, 1, 1; x, y, z; x ^ 2, y ^ 2, z ^ 2]

end Problem355.NormFoundation

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.NormPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.NormPolynomial

open scoped BigOperators

variable {F K V : Type*} [Field F] [Field K] [Algebra F K]
  [FiniteDimensional F K]

def galoisProduct (P : MvPolynomial V K) : MvPolynomial V K :=
  ∏ σ : K ≃ₐ[F] K, MvPolynomial.map σ.toRingHom P

theorem map_galoisProduct (P : MvPolynomial V K) (τ : K ≃ₐ[F] K) :
    MvPolynomial.map τ.toRingHom (galoisProduct (F := F) P) =
      galoisProduct (F := F) P := by
  classical
  rw [galoisProduct, map_prod]
  change (∏ σ : K ≃ₐ[F] K, MvPolynomial.map τ.toRingHom
    (MvPolynomial.map σ.toRingHom P)) = _
  simp_rw [MvPolynomial.map_map]
  exact Fintype.prod_equiv (Equiv.mulLeft τ) _ _ (fun _ => rfl)

theorem coeff_galoisProduct_mem_range [IsGalois F K]
    (P : MvPolynomial V K) (m : V →₀ ℕ) :
    (galoisProduct (F := F) P).coeff m ∈ Set.range (algebraMap F K) := by
  rw [IsGalois.mem_range_algebraMap_iff_fixed]
  intro τ
  have h := congrArg (fun polynomial : MvPolynomial V K => polynomial.coeff m) (map_galoisProduct P τ)
  simpa [MvPolynomial.coeff_map] using h

theorem exists_map_of_coeff_mem_range {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (P : MvPolynomial V S)
    (h : ∀ m, P.coeff m ∈ Set.range f) :
    ∃ Q : MvPolynomial V R, MvPolynomial.map f Q = P := by
  classical
  choose c hc using h
  refine ⟨∑ m ∈ P.support, MvPolynomial.monomial m (c m), ?_⟩
  simp only [map_sum, MvPolynomial.map_monomial, hc]
  exact MvPolynomial.support_sum_monomial_coeff P

theorem exists_normPolynomial [IsGalois F K] (P : MvPolynomial V K) :
    ∃ Q : MvPolynomial V F,
      MvPolynomial.map (algebraMap F K) Q = galoisProduct (F := F) P :=
  exists_map_of_coeff_mem_range _ _ (coeff_galoisProduct_mem_range P)

def normPolynomial [IsGalois F K] (P : MvPolynomial V K) : MvPolynomial V F :=
  Classical.choose (exists_normPolynomial P)

@[simp] theorem map_normPolynomial [IsGalois F K] (P : MvPolynomial V K) :
    MvPolynomial.map (algebraMap F K) (normPolynomial (F := F) P) =
      galoisProduct (F := F) P :=
  Classical.choose_spec (exists_normPolynomial P)

end Problem355.NormPolynomial

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.NormDeterminant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem355.NormDeterminant

open Matrix
open scoped BigOperators

abbrev Variables (ι : Type*) := Fin 3 × Fin 3 × ι

variable {ι K : Type*} [Fintype ι] [Field K]

def coordinateForm (β : ι → K) (j i : Fin 3) : MvPolynomial (Variables ι) K :=
  ∑ ν, MvPolynomial.C (β ν) * MvPolynomial.X (j, i, ν)

def determinantPolynomial (β : ι → K) : MvPolynomial (Variables ι) K :=
  Matrix.det (Matrix.of (fun i j => coordinateForm β j i))

def groupRename (e : Equiv.Perm (Fin 3)) (v : Variables ι) : Variables ι :=
  (e v.1, v.2)

@[simp] theorem rename_coordinateForm (β : ι → K) (e : Equiv.Perm (Fin 3))
    (j i : Fin 3) :
    MvPolynomial.rename (groupRename (ι := ι) e) (coordinateForm β j i) =
      coordinateForm β (e j) i := by
  simp [coordinateForm, groupRename]

variable {F : Type*} [Field F] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]

def normDeterminantPolynomial (β : ι → K) : MvPolynomial (Variables ι) F :=
  NormPolynomial.normPolynomial (F := F) (determinantPolynomial β)

def matrixCoordinates (b : Module.Basis ι F K) (A : Matrix (Fin 3) (Fin 3) K)
    (v : Variables ι) : F :=
  b.repr (A v.2.1 v.1) v.2.2

def labelCoordinates (b : Module.Basis ι F K) (x : K) (v : Fin 3 × ι) : F :=
  b.repr (NormFoundation.momentColumn x v.1) v.2

def labelTriple (b : Module.Basis ι F K) (x y z : K) (v : Variables ι) : F :=
  labelCoordinates b (![x, y, z] v.1) v.2

end Problem355.NormDeterminant

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.FiniteFieldLabels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.FiniteFieldLabels

variable (p : ℕ) [Fact p.Prime]

abbrev Label := GaloisField p heilbronnD

def labelBasis : Module.Basis (Fin heilbronnD) (ZMod p) (Label p) :=
  (Module.finBasis (ZMod p) (Label p)).reindex
    (finCongr (GaloisField.finrank p (by norm_num [heilbronnD])))

def labelNormPolynomial :
    MvPolynomial (NormDeterminant.Variables (Fin heilbronnD)) (ZMod p) :=
  NormDeterminant.normDeterminantPolynomial (F := ZMod p) (labelBasis p)

def labelVector (x : Label p) : Fin 3 × Fin heilbronnD → ZMod p :=
  NormDeterminant.labelCoordinates (labelBasis p) x

end Problem355.FiniteFieldLabels

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.MonomialCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.Monomials

abbrev DegreeIndex (α : Type*) (d : ℕ) :=
  {m : α →₀ ℕ // m.degree = d}

instance degreeIndexFintype (α : Type*) [Fintype α] [DecidableEq α] (d : ℕ) :
    Fintype (DegreeIndex α d) :=
  Fintype.ofEquiv (Sym α d) (Sym.equivNatSum α d)

theorem card_degreeIndex (α : Type*) [Fintype α] [DecidableEq α] (d : ℕ) :
    Fintype.card (DegreeIndex α d) = Nat.choose (Fintype.card α + d - 1) d := by
  let e : Sym α d ≃ DegreeIndex α d := Sym.equivNatSum α d
  rw [← Fintype.card_congr e, Sym.card_sym_eq_choose]

def coordinateDegreeEquivFin (d : ℕ) :
    DegreeIndex (Fin 3 × Fin d) d ≃ Fin (Nat.choose (4 * d - 1) d) :=
  Fintype.equivFinOfCardEq (by
    rw [card_degreeIndex, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    congr 2
    omega)

def heilbronnCoordinateMonomialEquiv :
    DegreeIndex (Fin 3 × Fin heilbronnD) heilbronnD ≃ Fin heilbronnM :=
  coordinateDegreeEquivFin heilbronnD

end Problem355.Monomials

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.NormHomogeneity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Problem355.NormHomogeneity
open scoped BigOperators
open MvPolynomial

open NormDeterminant
variable {ι K : Type*} [Fintype ι] [Field K]

def groupWeight (g : Fin 3) (v : Variables ι) : ℕ := if v.1 = g then 1 else 0

end Problem355.NormHomogeneity

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.PolynomialCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem355.PolynomialCoefficients

open MvPolynomial

variable {σ R : Type*}

def combine (a b c : σ →₀ ℕ) : (Fin 3 × σ) →₀ ℕ :=
  (Finsupp.equivFunOnFinite.symm ![a, b, c]).uncurry

@[simp] lemma combine_apply_zero (a b c : σ →₀ ℕ) (i : σ) :
    combine a b c (0, i) = a i := rfl

@[simp] lemma combine_apply_one (a b c : σ →₀ ℕ) (i : σ) :
    combine a b c (1, i) = b i := rfl

@[simp] lemma combine_apply_two (a b c : σ →₀ ℕ) (i : σ) :
    combine a b c (2, i) = c i := rfl

def groupSwap (i j : Fin 3) : Equiv.Perm (Fin 3 × σ) :=
  Equiv.prodCongr (Equiv.swap i j) (Equiv.refl σ)

@[simp] lemma combine_map_swap01 (a b c : σ →₀ ℕ) :
    (combine a b c).mapDomain (groupSwap (σ := σ) 0 1) = combine b a c := by
  ext ⟨i, s⟩
  rw [Finsupp.mapDomain_equiv_apply]
  fin_cases i <;> simp [groupSwap, combine, Finsupp.uncurry_apply, Equiv.swap_apply_def]

@[simp] lemma combine_map_swap12 (a b c : σ →₀ ℕ) :
    (combine a b c).mapDomain (groupSwap (σ := σ) 1 2) = combine a c b := by
  ext ⟨i, s⟩
  rw [Finsupp.mapDomain_equiv_apply]
  fin_cases i <;> simp [groupSwap, combine, Finsupp.uncurry_apply, Equiv.swap_apply_def]

section Expansion

variable [CommSemiring R]

def inGroup (j : Fin 3) (a : σ →₀ ℕ) : (Fin 3 × σ) →₀ ℕ :=
  a.mapDomain (fun s => (j, s))

@[simp] lemma inGroup_apply_same (j : Fin 3) (a : σ →₀ ℕ) (s : σ) :
    inGroup j a (j, s) = a s :=
  Finsupp.mapDomain_apply (fun _ _ h => (Prod.mk.inj h).2) _ _

def groupMonomial (j : Fin 3) (a : σ →₀ ℕ) : MvPolynomial (Fin 3 × σ) R :=
  rename (fun s => (j, s)) (monomial a 1)

end Expansion

variable [CommRing R]

def tensorCoeff (P : MvPolynomial (Fin 3 × σ) R) (a b c : σ →₀ ℕ) : R :=
  P.coeff (combine a b c)

end Problem355.PolynomialCoefficients

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.NormDecomposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.NormDecomposition

open scoped BigOperators

variable {ι R : Type*} [Fintype ι] [CommRing R]

variable [LinearOrder ι]

def increasingSum (f : ι → ι → ι → R) : R :=
  ∑ i, ∑ j, ∑ k, if i < j ∧ j < k then f i j k else 0

end Problem355.NormDecomposition

end OAI
end

section
-- module Solutions.OAIQW_Problem355.TripleEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.NormDecomposition

open scoped BigOperators

variable {ι : Type*} [LinearOrder ι]

abbrev IncreasingTriple (ι : Type*) [LinearOrder ι] :=
  {t : ι × ι × ι // t.1 < t.2.1 ∧ t.2.1 < t.2.2}

def tripleToSet (t : IncreasingTriple ι) : {s : Finset ι // s.card = 3} :=
  ⟨{t.val.1, t.val.2.1, t.val.2.2},
    Finset.card_eq_three.mpr ⟨_, _, _, ne_of_lt t.property.1,
      ne_of_lt (lt_trans t.property.1 t.property.2), ne_of_lt t.property.2, rfl⟩⟩

def tripleFromSet (s : {s : Finset ι // s.card = 3}) : IncreasingTriple ι :=
  ⟨(s.val.orderEmbOfFin s.property 0, s.val.orderEmbOfFin s.property 1,
      s.val.orderEmbOfFin s.property 2),
    (s.val.orderEmbOfFin s.property).strictMono (by decide),
    (s.val.orderEmbOfFin s.property).strictMono (by decide)⟩

theorem triple_vector_strictMono (t : IncreasingTriple ι) :
    StrictMono (![t.val.1, t.val.2.1, t.val.2.2] : Fin 3 → ι) := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  fin_cases i
  · exact t.property.1
  · exact t.property.2

@[simp] theorem tripleFromSet_tripleToSet (t : IncreasingTriple ι) :
    tripleFromSet (tripleToSet t) = t := by
  have h : (![t.val.1, t.val.2.1, t.val.2.2] : Fin 3 → ι) =
      (tripleToSet t).val.orderEmbOfFin (tripleToSet t).property := by
    apply Finset.orderEmbOfFin_unique
    · intro i
      fin_cases i <;> simp [tripleToSet]
    · exact triple_vector_strictMono t
  apply Subtype.ext
  apply Prod.ext
  · exact (congrFun h 0).symm
  · apply Prod.ext
    · exact (congrFun h 1).symm
    · exact (congrFun h 2).symm

@[simp] theorem tripleToSet_tripleFromSet (s : {s : Finset ι // s.card = 3}) :
    tripleToSet (tripleFromSet s) = s := by
  apply Subtype.ext
  have h := Finset.image_orderEmbOfFin_univ s.val s.property
  simpa [tripleToSet, tripleFromSet, Fin.univ_succ] using h

def tripleSetEquiv : IncreasingTriple ι ≃ {s : Finset ι // s.card = 3} where
  toFun := tripleToSet
  invFun := tripleFromSet
  left_inv := tripleFromSet_tripleToSet
  right_inv := tripleToSet_tripleFromSet

variable [Fintype ι]

theorem card_increasingTriple :
    Fintype.card (IncreasingTriple ι) = Nat.choose (Fintype.card ι) 3 := by
  rw [Fintype.card_congr tripleSetEquiv, Fintype.card_finset_len]

def increasingTripleEquivFin :
    IncreasingTriple ι ≃ Fin (Nat.choose (Fintype.card ι) 3) :=
  Fintype.equivFinOfCardEq card_increasingTriple

variable {R : Type*} [CommRing R]

def decompositionRows {X : Type*} (c : ι → ι → ι → R) (m : ι → X → R)
    (a : Fin (Nat.choose (Fintype.card ι) 3)) : Fin 3 → X → R :=
  let t := (increasingTripleEquivFin (ι := ι)).symm a
  ![fun x => c t.val.1 t.val.2.1 t.val.2.2 * m t.val.1 x,
    m t.val.2.1, m t.val.2.2]

end Problem355.NormDecomposition

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.NormEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.NormEncoding

open scoped BigOperators
open MvPolynomial

abbrev Coordinate := Fin 3 × Fin heilbronnD

def monomialExponent (i : Fin heilbronnM) : Coordinate →₀ ℕ :=
  (Monomials.heilbronnCoordinateMonomialEquiv.symm i).val

variable (p : ℕ) [Fact p.Prime]

def normCoefficient (i j k : Fin heilbronnM) : ZMod p :=
  PolynomialCoefficients.tensorCoeff (FiniteFieldLabels.labelNormPolynomial p)
    (monomialExponent i) (monomialExponent j) (monomialExponent k)

def monomialValue (i : Fin heilbronnM) (x : FiniteFieldLabels.Label p) : ZMod p :=
  MvPolynomial.eval (FiniteFieldLabels.labelVector p x) (monomial (monomialExponent i) 1)

def determinantIndexEquiv :
    Fin (Nat.choose (Fintype.card (Fin heilbronnM)) 3) ≃ Fin heilbronnT :=
  finCongr (by rw [Fintype.card_fin]; rfl)

def normRowFunctions (i : Fin 3) (a : Fin heilbronnT)
    (x : FiniteFieldLabels.Label p) : ZMod p :=
  NormDecomposition.decompositionRows (normCoefficient p) (monomialValue p)
    (determinantIndexEquiv.symm a) i x

end Problem355.NormEncoding

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.Parameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355

lemma heilbronnM_ge_three : 3 ≤ heilbronnM := by
  have h : Nat.choose (41 + 1) 41 ≤ Nat.choose (4 * 41 - 1) 41 :=
    Nat.choose_le_choose 41 (by norm_num)
  rw [Nat.choose_succ_self_right] at h
  exact le_trans (by norm_num : 3 ≤ 42) h

lemma heilbronnT_pos : 0 < heilbronnT := by
  exact Nat.choose_pos (n := heilbronnM) (k := 3) heilbronnM_ge_three

def squareAddOne (t : ℕ) : ℕ := t ^ 2 + 1

lemma squareAddOne_ge {t : ℕ} (ht : 0 < t) : 2 ≤ squareAddOne t := by
  unfold squareAddOne
  nlinarith

lemma heilbronnK_ge_two : 2 ≤ heilbronnK := by
  with_unfolding_all exact squareAddOne_ge (t := heilbronnT) heilbronnT_pos

lemma heilbronnK_pos : 0 < heilbronnK :=
  lt_of_lt_of_le (by norm_num : 0 < 2) heilbronnK_ge_two

end Problem355

namespace Problem355.Parameters

def threshold (B k : ℕ) : ℕ := B ^ (k - 1) / 2

end Problem355.Parameters

end OAI
end

section
-- module Solutions.OAIQW_Problem355.MainResidueSystem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace Problem355.MainResidueSystem

open FiniteFieldLabels

variable (p : ℕ) [Fact p.Prime]

def prescribedResidue (i : Fin 3) (v : ℕ) (x : Label p) : ZMod p :=
  LabelResidues.residue heilbronnT (NormEncoding.normRowFunctions p) i v x

def finiteResidue (i : Fin 3) (v : Fin heilbronnK) (x : Label p) : ZMod p :=
  prescribedResidue p i v.val x

end Problem355.MainResidueSystem

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.ParameterSequence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.Parameters

structure PrimeParameterData (k r : ℕ) where
  two_le_k : 2 ≤ k
  large_r : 200 * k ^ 2 ≤ r
  large_for_moment : 400 * k ^ 2 ≤ r
  B : ℕ
  q : ℕ
  base_prime : B.Prime
  auxiliary_prime : q.Prime
  base_lower : 100 * k ^ 2 * r ^ 30 < B
  base_upper : B ≤ 200 * k ^ 2 * r ^ 30
  base_polynomial : B ≤ r ^ 31
  auxiliary_lower : (B ^ k) ^ 100 < q
  auxiliary_upper : q ≤ 2 * (B ^ k) ^ 100
  auxiliary_polynomial : q ≤ (B ^ k) ^ 101
  coprime : (B ^ k).Coprime q
  auxiliary_large : 2000 * ((B ^ k) ^ 2) ^ 2 ≤ q

namespace PrimeParameterData

variable {k r : ℕ} (P : PrimeParameterData k r)

def h : ℕ := P.B ^ k
def M : ℕ := P.h * P.q
def N : ℕ := P.M ^ 10
def tau : ℕ := threshold P.B k

include P in
lemma r_pos : 0 < r := by
  have hk := P.two_le_k
  have hp : 0 < 200 * k ^ 2 := by positivity
  exact lt_of_lt_of_le hp P.large_r

lemma base_ge_three : 3 ≤ P.B := by
  have hk : 0 < k := by have := P.two_le_k; omega
  have hr := P.r_pos
  have hp : 1 ≤ k ^ 2 * r ^ 30 := Nat.succ_le_of_lt (by positivity)
  have hc : 100 ≤ 100 * k ^ 2 * r ^ 30 := by
    calc
      100 = 100 * 1 := by norm_num
      _ ≤ 100 * (k ^ 2 * r ^ 30) := Nat.mul_le_mul_left 100 hp
      _ = 100 * k ^ 2 * r ^ 30 := by ring
  have := P.base_lower
  omega

lemma base_le_h : P.B ≤ P.h := by
  unfold h
  simpa using (Nat.pow_le_pow_right P.base_prime.pos (show 1 ≤ k by have := P.two_le_k; omega))

lemma h_ge_three : 3 ≤ P.h := P.base_ge_three.trans P.base_le_h

lemma h_le_M : P.h ≤ P.M := by
  unfold M
  exact Nat.le_mul_of_pos_right _ P.auxiliary_prime.pos

lemma r_le_M : r ≤ P.M := by
  have hr := P.r_pos
  have hk : 0 < k := by have := P.two_le_k; omega
  have hc : 1 ≤ 100 * k ^ 2 := Nat.succ_le_of_lt (by positivity)
  have hpow : r ≤ r ^ 30 := by
    simpa using Nat.pow_le_pow_right hr (by norm_num : 1 ≤ 30)
  calc
    r ≤ r ^ 30 := hpow
    _ ≤ 100 * k ^ 2 * r ^ 30 := Nat.le_mul_of_pos_left _ hc
    _ ≤ P.B := P.base_lower.le
    _ ≤ P.h := P.base_le_h
    _ ≤ P.M := P.h_le_M

lemma M_pos : 0 < P.M := lt_of_lt_of_le P.r_pos P.r_le_M

lemma alphabet_lt_base : r ^ 10 < P.B := by
  have hk : 0 < k := by have := P.two_le_k; omega
  have hc : 1 ≤ 100 * k ^ 2 := Nat.succ_le_of_lt (by positivity)
  calc
    r ^ 10 ≤ r ^ 30 := Nat.pow_le_pow_right P.r_pos (by norm_num)
    _ ≤ 100 * k ^ 2 * r ^ 30 := Nat.le_mul_of_pos_left _ hc
    _ < P.B := P.base_lower

end PrimeParameterData

end Problem355.Parameters

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.ZModAnnihilator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355

theorem zmod_card_mul_eq_zero (m d : ℕ) [NeZero m] :
    Nat.card {x : ZMod m // (d : ZMod m) * x = 0} = Nat.gcd m d := by
  simpa only [Nat.card_zmod, AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply,
    nsmul_eq_mul] using IsAddCyclic.card_nsmulAddMonoidHom_ker (ZMod m) d

theorem zmod_card_mul_eq_zero_of_dvd (m d : ℕ) [NeZero m] (hd : d ∣ m) :
    Nat.card {x : ZMod m // (d : ZMod m) * x = 0} = d := by
  rw [zmod_card_mul_eq_zero, Nat.gcd_eq_right hd]

theorem zmod_card_pow_mul_eq_zero (B k e : ℕ) [NeZero B] (he : e ≤ k) :
    Nat.card {x : ZMod (B ^ k) // (B ^ e : ZMod (B ^ k)) * x = 0} = B ^ e := by
  simpa only [Nat.cast_pow] using
    zmod_card_mul_eq_zero_of_dvd (B ^ k) (B ^ e) (pow_dvd_pow B he)

def matrixFixedDiagonalEquiv {ι R : Type*} [Fintype ι] [DecidableEq ι]
    [Ring R] (d : ι → R) :
    {A : Matrix ι ι R // A * Matrix.diagonal d = Matrix.diagonal d} ≃
      (ι → (j : ι) → {x : R // x * d j = 0}) where
  toFun A i j := ⟨(A.1 - 1) i j, by
    have hzero : (A.1 - 1) * Matrix.diagonal d = 0 := by
      rw [Matrix.sub_mul, A.2, Matrix.one_mul, sub_self]
    simpa only [Matrix.mul_diagonal, Matrix.zero_apply] using
      congrArg (fun M : Matrix ι ι R => M i j) hzero⟩
  invFun f := ⟨(Matrix.of (fun i j => (f i j).1)) + 1, by
    have hzero : (Matrix.of (fun i j => (f i j).1)) * Matrix.diagonal d = 0 := by
      ext i j
      simpa only [Matrix.mul_diagonal, Matrix.zero_apply, Matrix.of_apply] using (f i j).2
    rw [Matrix.add_mul, hzero, Matrix.one_mul, zero_add]⟩
  left_inv A := by
    apply Subtype.ext
    exact sub_add_cancel A.1 1
  right_inv f := by
    funext i j
    apply Subtype.ext
    change ((Matrix.of (fun i j => (f i j).1)) + 1 - 1) i j = (f i j).1
    rw [add_sub_cancel_right]
    rfl

end Problem355

end OAI
end

section
-- module Solutions.OAIQW_Problem355.DiagonalDetImage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.DiagonalDetImage

open Matrix

variable {R : Type*} [CommRing R]

def diagonalThree (D E : R) : Matrix (Fin 3) (Fin 3) R :=
  Matrix.diagonal ![1, D, E]

def finalDiagonalUnit (u : Rˣ) : Matrix.GeneralLinearGroup (Fin 3) R :=
  Matrix.GeneralLinearGroup.mk'' (Matrix.diagonal ![1, 1, (u : R)]) (by
    simp [Matrix.det_diagonal, Fin.prod_univ_succ])

@[simp] theorem finalDiagonalUnit_val (u : Rˣ) :
    (finalDiagonalUnit u : Matrix (Fin 3) (Fin 3) R) =
      Matrix.diagonal ![1, 1, (u : R)] := by
  simp [finalDiagonalUnit]

@[simp] theorem finalDiagonalUnit_det (u : Rˣ) :
    Matrix.GeneralLinearGroup.det (finalDiagonalUnit u) = u := by
  apply Units.ext
  simp [Matrix.GeneralLinearGroup.det, Matrix.det_diagonal, Fin.prod_univ_succ]

def determinantValues (D E : R) : Set Rˣ :=
  {u | ∃ g : Matrix.GeneralLinearGroup (Fin 3) R,
    (g : Matrix (Fin 3) (Fin 3) R) * diagonalThree D E = diagonalThree D E ∧
      Matrix.GeneralLinearGroup.det g = u}

def annihilatorEquivCongruenceUnits (E : R)
    (hunit : ∀ x : R, x * E = 0 → IsUnit (1 + x)) :
    {x : R // x * E = 0} ≃ {u : Rˣ // ((u : R) - 1) * E = 0} where
  toFun x := ⟨(hunit x.val x.property).unit, by
    rw [IsUnit.unit_spec]
    simpa using x.property⟩
  invFun u := ⟨(u.val : R) - 1, u.property⟩
  left_inv x := by
    apply Subtype.ext
    simp only [IsUnit.unit_spec, add_sub_cancel_left]
  right_inv u := by
    apply Subtype.ext
    apply Units.ext
    simp only [IsUnit.unit_spec]
    ring

end Problem355.DiagonalDetImage

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.OrbitCardinality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.OrbitCardinality

variable {G U X : Type*} [Group G] [Group U] [MulAction G X]

def orbitFiberEquivStabilizer (x : X) (g : G) :
    {a : G // a • x = g • x} ≃ MulAction.stabilizer G x where
  toFun a := ⟨g⁻¹ * a.1, by
    change (g⁻¹ * a.1) • x = x
    rw [mul_smul, a.2, inv_smul_smul]⟩
  invFun a := ⟨g * a.1, by
    rw [mul_smul, a.2]⟩
  left_inv a := by
    apply Subtype.ext
    simp
  right_inv a := by
    apply Subtype.ext
    simp

end Problem355.OrbitCardinality

end OAI
end

section
-- module Solutions.OAIQW_Problem355.PrimePowerGL
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.PrimePowerGL

open Matrix

noncomputable def fiberEquivKer {R S : Type*} [AddGroup R] [AddGroup S]
    (f : R →+ S) (hf : Function.Surjective f) (y : S) :
    {x : R // f x = y} ≃ f.ker := by
  classical
  let r := Classical.choose (hf y)
  have hr : f r = y := Classical.choose_spec (hf y)
  refine
    { toFun := fun x => ⟨x.1 - r, ?_⟩
      invFun := fun x => ⟨x.1 + r, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · change f (x.1 - r) = 0
    simp [map_sub, x.2, hr]
  · have hx : f x.1 = 0 := x.2
    simp [map_add, hx, hr]
  · intro x
    apply Subtype.ext
    simp
  · intro x
    apply Subtype.ext
    simp

noncomputable def unitsEquivSigmaFiber {R S : Type*} [Ring R] [Ring S]
    (f : R →+* S) (hu : ∀ x, IsUnit (f x) → IsUnit x) :
    Rˣ ≃ Σ y : Sˣ, {x : R // f x = (y : S)} where
  toFun x := ⟨Units.map f.toMonoidHom x, ⟨x, rfl⟩⟩
  invFun x := (hu x.2.1 (by rw [x.2.2]; exact x.1.isUnit)).unit
  left_inv x := by apply Units.ext; simp
  right_inv x := by
    rcases x with ⟨y, x, hx⟩
    apply Sigma.ext
    · apply Units.ext
      simp [hx]
    · apply (Subtype.heq_iff_coe_eq (fun z => by simp [hx])).mpr
      simp

noncomputable def matrixKernelEquiv {R S n : Type*} [Ring R] [Ring S]
    [Fintype n] [DecidableEq n] (f : R →+* S) :
    (f.mapMatrix (m := n)).toAddMonoidHom.ker ≃
      (n → n → f.toAddMonoidHom.ker) where
  toFun A i j := ⟨A.1 i j, by
    have hA : f.mapMatrix A.1 = 0 := A.2
    exact congrFun (congrFun hA i) j⟩
  invFun A := ⟨fun i j => (A i j).1, by
    ext i j
    exact (A i j).2⟩
  left_inv A := by rfl
  right_inv A := by rfl

end Problem355.PrimePowerGL

end OAI
end

section
-- module Solutions.OAIQW_Problem355.StabilizerConjugation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355

def unitLeftStabilizerEquiv {M : Type*} [Monoid M] (P Q : Mˣ) (D : M) :
    {A : Mˣ // (A : M) * D = D} ≃
      {A : Mˣ // (A : M) * ((P : M) * D * (Q : M)) =
        (P : M) * D * (Q : M)} :=
  (MulAut.conj P).toEquiv.subtypeEquiv fun A => by
    change (A : M) * D = D ↔
      ((P : M) * (A : M) * ((P⁻¹ : Mˣ) : M)) *
        ((P : M) * D * (Q : M)) = (P : M) * D * (Q : M)
    constructor
    · intro h
      simpa only [mul_assoc, Units.inv_mul_cancel_left] using
        congrArg (fun x : M => (P : M) * x * (Q : M)) h
    · intro h
      have hh := congrArg (fun x : M => ((P⁻¹ : Mˣ) : M) * x * ((Q⁻¹ : Mˣ) : M)) h
      simpa only [mul_assoc, Units.inv_mul_cancel_left, Units.mul_inv, one_mul, mul_one] using hh

end Problem355

end OAI
end

section
-- module Solutions.OAIQW_Problem355.OrbitEstimate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.Section04Orbit

open Matrix

variable {R : Type*} [CommRing R]

def slOrbit (C : Matrix (Fin 3) (Fin 3) R) : Set (Matrix (Fin 3) (Fin 3) R) :=
  Set.range fun g : Matrix.SpecialLinearGroup (Fin 3) R => (g : Matrix _ _ _) * C

end Problem355.Section04Orbit

end OAI
end

section
-- module Solutions.OAIQW_Problem355.PivotAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.PivotAssembly

open Matrix

variable {R : Type*} [CommRing R]

theorem exists_unit_pivot_reduction
    (C : Matrix (Fin 3) (Fin 3) R) (h : IsUnit (C 0 0)) :
    ∃ P Q : Matrix (Fin 3) (Fin 3) R,
      IsUnit P.det ∧ IsUnit Q.det ∧
      ∃ a b c d : R, P * C * Q = !![1, 0, 0; 0, a, b; 0, c, d] := by
  obtain ⟨u, hu⟩ := h
  let v : R := ↑u⁻¹
  have huv : C 0 0 * v = 1 := by simp [v, ← hu]
  have hvu : v * C 0 0 = 1 := by simp [v, ← hu]
  have hvux (x : R) : v * (C 0 0 * x) = x := by rw [← mul_assoc, hvu, one_mul]
  let P : Matrix (Fin 3) (Fin 3) R :=
    !![v, 0, 0; -(C 1 0 * v), 1, 0; -(C 2 0 * v), 0, 1]
  let Q : Matrix (Fin 3) (Fin 3) R :=
    !![1, -(v * C 0 1), -(v * C 0 2); 0, 1, 0; 0, 0, 1]
  refine ⟨P, Q, ?_, ?_,
    C 1 1 - C 1 0 * v * C 0 1,
    C 1 2 - C 1 0 * v * C 0 2,
    C 2 1 - C 2 0 * v * C 0 1,
    C 2 2 - C 2 0 * v * C 0 2, ?_⟩
  · simp [P, v, Matrix.det_fin_three]
  · simp [Q, Matrix.det_fin_three]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [P, Q, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ, add_mul,
        mul_assoc, hvu] <;> ring_nf <;>
      simp [pow_two, mul_assoc, hvux] <;> ring

def embedTwo (A : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 3) (Fin 3) R :=
  !![1, 0, 0; 0, A 0 0, A 0 1; 0, A 1 0, A 1 1]

theorem embedTwo_mul (A B : Matrix (Fin 2) (Fin 2) R) :
    embedTwo (A * B) = embedTwo A * embedTwo B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [embedTwo, Matrix.mul_apply, Fin.sum_univ_succ]

theorem det_embedTwo (A : Matrix (Fin 2) (Fin 2) R) :
    (embedTwo A).det = A.det := by
  simp [embedTwo, Matrix.det_fin_three, Matrix.det_fin_two]

theorem embedTwo_diagonal (a b : R) :
    embedTwo (Matrix.diagonal ![a, b]) = Matrix.diagonal ![1, a, b] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedTwo, Matrix.diagonal]

theorem exists_diagonal_of_two_by_two (rel : R → R → Prop)
    (hdiag : ∀ A : Matrix (Fin 2) (Fin 2) R,
      ∃ P Q : Matrix (Fin 2) (Fin 2) R,
        IsUnit P.det ∧ IsUnit Q.det ∧ ∃ a b : R,
          rel a b ∧ P * A * Q = Matrix.diagonal ![a, b])
    (C : Matrix (Fin 3) (Fin 3) R) (h : IsUnit (C 0 0)) :
    ∃ P Q : Matrix (Fin 3) (Fin 3) R,
      IsUnit P.det ∧ IsUnit Q.det ∧ ∃ a b : R,
        rel a b ∧ P * C * Q = Matrix.diagonal ![1, a, b] := by
  obtain ⟨P, Q, hP, hQ, a, b, c, d, hblock⟩ := exists_unit_pivot_reduction C h
  let A : Matrix (Fin 2) (Fin 2) R := !![a, b; c, d]
  obtain ⟨P', Q', hP', hQ', x, y, hxy, heq⟩ := hdiag A
  refine ⟨embedTwo P' * P, Q * embedTwo Q', ?_, ?_, x, y, hxy, ?_⟩
  · rw [Matrix.det_mul, det_embedTwo]
    exact hP'.mul hP
  · rw [Matrix.det_mul, det_embedTwo]
    exact hQ.mul hQ'
  · calc
      (embedTwo P' * P) * C * (Q * embedTwo Q') =
          embedTwo P' * (P * C * Q) * embedTwo Q' := by noncomm_ring
      _ = embedTwo P' * embedTwo A * embedTwo Q' := by rw [hblock]; rfl
      _ = embedTwo (P' * A * Q') := by rw [embedTwo_mul, embedTwo_mul]
      _ = Matrix.diagonal ![1, x, y] := by rw [heq, embedTwo_diagonal]

theorem factorization_of_reduction {n : Type*} [Fintype n] [DecidableEq n]
    (C D P Q : Matrix n n R) (hP : IsUnit P.det) (hQ : IsUnit Q.det)
    (h : P * C * Q = D) :
    ∃ U V : Matrix.GeneralLinearGroup n R,
      C = (U : Matrix n n R) * D * (V : Matrix n n R) := by
  obtain ⟨u, rfl⟩ := (Matrix.isUnit_iff_isUnit_det P).2 hP
  obtain ⟨v, rfl⟩ := (Matrix.isUnit_iff_isUnit_det Q).2 hQ
  refine ⟨u⁻¹, v⁻¹, ?_⟩
  rw [← h]
  calc
    C = ((↑u⁻¹ : Matrix n n R) * ↑u) * C * (↑v * ↑v⁻¹) := by simp
    _ = ↑u⁻¹ * (↑u * C * ↑v) * ↑v⁻¹ := by noncomm_ring

theorem exists_factorization_of_two_by_two (rel : R → R → Prop)
    (hdiag : ∀ A : Matrix (Fin 2) (Fin 2) R,
      ∃ P Q : Matrix (Fin 2) (Fin 2) R,
        IsUnit P.det ∧ IsUnit Q.det ∧ ∃ a b : R,
          rel a b ∧ P * A * Q = Matrix.diagonal ![a, b])
    (C : Matrix (Fin 3) (Fin 3) R) (h : IsUnit (C 0 0)) :
    ∃ U V : Matrix.GeneralLinearGroup (Fin 3) R, ∃ a b : R,
      rel a b ∧ C = (U : Matrix (Fin 3) (Fin 3) R) *
        Matrix.diagonal ![1, a, b] * (V : Matrix (Fin 3) (Fin 3) R) := by
  obtain ⟨P, Q, hP, hQ, a, b, hab, heq⟩ :=
    exists_diagonal_of_two_by_two rel hdiag C h
  obtain ⟨U, V, hUV⟩ := factorization_of_reduction C _ P Q hP hQ heq
  exact ⟨U, V, a, b, hab, hUV⟩

theorem exists_factorization_of_two_by_two_units (rel : R → R → Prop)
    (hdiag : ∀ A : Matrix (Fin 2) (Fin 2) R,
      ∃ P Q : Matrix.GeneralLinearGroup (Fin 2) R, ∃ a b : R,
        rel a b ∧ A = (P : Matrix (Fin 2) (Fin 2) R) *
          Matrix.diagonal ![a, b] * (Q : Matrix (Fin 2) (Fin 2) R))
    (C : Matrix (Fin 3) (Fin 3) R) (h : IsUnit (C 0 0)) :
    ∃ U V : Matrix.GeneralLinearGroup (Fin 3) R, ∃ a b : R,
      rel a b ∧ C = (U : Matrix (Fin 3) (Fin 3) R) *
        Matrix.diagonal ![1, a, b] * (V : Matrix (Fin 3) (Fin 3) R) := by
  apply exists_factorization_of_two_by_two rel ?_ C h
  intro A
  obtain ⟨P, Q, a, b, hab, heq⟩ := hdiag A
  refine ⟨↑P⁻¹, ↑Q⁻¹, Matrix.isUnits_det_units P⁻¹,
    Matrix.isUnits_det_units Q⁻¹, a, b, hab, ?_⟩
  rw [heq]
  simp [← Matrix.mul_assoc]

end Problem355.PivotAssembly

end OAI
end

section
-- module Solutions.OAIQW_Problem355.DiagonalStabilizer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.DiagonalStabilizer

open Matrix

variable {R : Type*} [CommRing R]

def diagonal3 (D E : R) : Matrix (Fin 3) (Fin 3) R :=
  Matrix.diagonal ![1, D, E]

abbrev Ann (a : R) := {x : R // x * a = 0}

end Problem355.DiagonalStabilizer

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.RowLattice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.RowLattice

open Matrix DiagonalStabilizer

variable {R : Type*} [CommRing R]

abbrev RowKernel (C : Matrix (Fin 3) (Fin 3) R) :=
  {v : Fin 3 → R // v ᵥ* C = 0}

def rowImage (C : Matrix (Fin 3) (Fin 3) R) : AddSubgroup (Fin 3 → R) :=
  C.vecMulLinear.toAddMonoidHom.range

lemma rowImage_index_eq_card_kernel [Finite R] (C : Matrix (Fin 3) (Fin 3) R) :
    (rowImage C).index = Nat.card (RowKernel C) := by
  exact AddSubgroup.index_range

def diagonalKernelEquiv (D E : R) :
    RowKernel (diagonal3 D E) ≃ Ann D × Ann E where
  toFun v :=
    (⟨v.val 1, by
      have h := congrFun v.property 1
      simpa [diagonal3, Matrix.vecMul_diagonal] using h⟩,
     ⟨v.val 2, by
      have h := congrFun v.property 2
      simpa [diagonal3, Matrix.vecMul_diagonal] using h⟩)
  invFun v := ⟨![0, v.1.val, v.2.val], by
    funext i
    fin_cases i
    · simp [diagonal3, Matrix.vecMul_diagonal]
    · simpa [diagonal3, Matrix.vecMul_diagonal] using v.1.property
    · simpa [diagonal3, Matrix.vecMul_diagonal] using v.2.property⟩
  left_inv v := by
    apply Subtype.ext
    funext i
    fin_cases i
    · have h := congrFun v.property 0
      simpa [diagonal3, Matrix.vecMul_diagonal] using h.symm
    · rfl
    · rfl
  right_inv v := by
    apply Prod.ext <;> apply Subtype.ext <;> rfl

lemma card_diagonal_kernel (D E : R) :
    Nat.card (RowKernel (diagonal3 D E)) = Nat.card (Ann D) * Nat.card (Ann E) := by
  rw [Nat.card_congr (diagonalKernelEquiv D E), Nat.card_prod]

def kernelEquivOfDiagonalForm {C D : Matrix (Fin 3) (Fin 3) R}
    (P Q : Matrix.GeneralLinearGroup (Fin 3) R)
    (hC : C = (P : Matrix (Fin 3) (Fin 3) R) * D *
      (Q : Matrix (Fin 3) (Fin 3) R)) : RowKernel C ≃ RowKernel D where
  toFun v := ⟨v.val ᵥ* P.val, by
    apply Matrix.vecMul_injective_of_isUnit Q.isUnit
    simpa only [Matrix.vecMul_vecMul, hC, Matrix.zero_vecMul] using v.property⟩
  invFun v := ⟨v.val ᵥ* (P⁻¹).val, by
    calc
      (v.val ᵥ* (P⁻¹).val) ᵥ* C =
          (((v.val ᵥ* (P⁻¹).val) ᵥ* P.val) ᵥ* D) ᵥ* Q.val := by
        simp only [Matrix.vecMul_vecMul, hC, Matrix.mul_assoc]
      _ = 0 := by
        have hp : (v.val ᵥ* (P⁻¹).val) ᵥ* P.val = v.val := by
          rw [Matrix.vecMul_vecMul, Units.inv_mul, Matrix.vecMul_one]
        rw [hp, v.property, Matrix.zero_vecMul]⟩
  left_inv v := by
    apply Subtype.ext
    simp only [Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one]
  right_inv v := by
    apply Subtype.ext
    simp only [Matrix.vecMul_vecMul, Units.inv_mul, Matrix.vecMul_one]

lemma rowImage_index_of_diagonal_form [Finite R]
    (C : Matrix (Fin 3) (Fin 3) R) (D E : R)
    (P Q : Matrix.GeneralLinearGroup (Fin 3) R)
    (hC : C = (P : Matrix (Fin 3) (Fin 3) R) * diagonal3 D E *
      (Q : Matrix (Fin 3) (Fin 3) R)) :
    (rowImage C).index = Nat.card (Ann D) * Nat.card (Ann E) := by
  rw [rowImage_index_eq_card_kernel,
    Nat.card_congr (kernelEquivOfDiagonalForm P Q hC), card_diagonal_kernel]

def reduction (h : ℕ) : (Fin 3 → ℤ) →+ (Fin 3 → ZMod h) where
  toFun v i := (v i : ZMod h)
  map_zero' := by ext i; simp
  map_add' v w := by ext i; simp

lemma reduction_surjective (h : ℕ) : Function.Surjective (reduction h) := by
  intro v
  choose w hw using fun i : Fin 3 => ZMod.intCast_surjective (v i)
  exact ⟨w, funext hw⟩

def integerRowLattice (h : ℕ) (C : Matrix (Fin 3) (Fin 3) (ZMod h)) :
    AddSubgroup (Fin 3 → ℤ) :=
  (rowImage C).comap (reduction h)

lemma integerRowLattice_index (h : ℕ) (C : Matrix (Fin 3) (Fin 3) (ZMod h)) :
    (integerRowLattice h C).index = (rowImage C).index := by
  exact AddSubgroup.index_comap_of_surjective _ (reduction_surjective h)

theorem integerRowLattice_index_prime_power
    (B k b e : ℕ) [NeZero B] (hb : b ≤ k) (he : e ≤ k)
    (C : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k)))
    (P Q : Matrix.GeneralLinearGroup (Fin 3) (ZMod (B ^ k)))
    (hC : C = (P : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k))) *
      diagonal3 (R := ZMod (B ^ k)) (B ^ b) (B ^ e) *
      (Q : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k)))) :
    (integerRowLattice (B ^ k) C).index = B ^ b * B ^ e := by
  have hD : Nat.card (Ann (R := ZMod (B ^ k)) (B ^ b)) = B ^ b := by
    simpa only [Ann, mul_comm] using zmod_card_pow_mul_eq_zero B k b hb
  have hE : Nat.card (Ann (R := ZMod (B ^ k)) (B ^ e)) = B ^ e := by
    simpa only [Ann, mul_comm] using zmod_card_pow_mul_eq_zero B k e he
  rw [integerRowLattice_index, rowImage_index_of_diagonal_form C _ _ P Q hC, hD, hE]

lemma smul_mem_rowImage_diagonal (D E : R) (hDE : D ∣ E) (v : Fin 3 → R) :
    E • v ∈ rowImage (diagonal3 D E) := by
  obtain ⟨a, ha⟩ := hDE
  refine ⟨![E * v 0, a * v 1, v 2], ?_⟩
  change ![E * v 0, a * v 1, v 2] ᵥ* diagonal3 D E = E • v
  funext i
  fin_cases i <;> simp [diagonal3, Matrix.vecMul_diagonal, ha] <;> ring

lemma smul_mem_rowImage_of_diagonal_form
    (C : Matrix (Fin 3) (Fin 3) R) (D E : R) (hDE : D ∣ E)
    (P Q : Matrix.GeneralLinearGroup (Fin 3) R)
    (hC : C = (P : Matrix (Fin 3) (Fin 3) R) * diagonal3 D E *
      (Q : Matrix (Fin 3) (Fin 3) R)) (v : Fin 3 → R) :
    E • v ∈ rowImage C := by
  obtain ⟨w, hw⟩ := smul_mem_rowImage_diagonal D E hDE (v ᵥ* (Q⁻¹).val)
  change w ᵥ* diagonal3 D E = E • (v ᵥ* (Q⁻¹).val) at hw
  refine ⟨w ᵥ* (P⁻¹).val, ?_⟩
  change (w ᵥ* (P⁻¹).val) ᵥ* C = E • v
  calc
    (w ᵥ* (P⁻¹).val) ᵥ* C = (w ᵥ* diagonal3 D E) ᵥ* Q.val := by
      simp only [hC, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, Units.inv_mul, one_mul]
    _ = (E • (v ᵥ* (Q⁻¹).val)) ᵥ* Q.val := by rw [hw]
    _ = E • v := by
      rw [Matrix.smul_vecMul, Matrix.vecMul_vecMul, Units.inv_mul, Matrix.vecMul_one]

theorem nsmul_mem_integerRowLattice_prime_power
    (B k b e : ℕ) (hbe : b ≤ e)
    (C : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k)))
    (P Q : Matrix.GeneralLinearGroup (Fin 3) (ZMod (B ^ k)))
    (hC : C = (P : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k))) *
      diagonal3 (R := ZMod (B ^ k)) (B ^ b) (B ^ e) *
      (Q : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k)))) (v : Fin 3 → ℤ) :
    (B ^ e) • v ∈ integerRowLattice (B ^ k) C := by
  change reduction (B ^ k) ((B ^ e) • v) ∈ rowImage C
  have hv := smul_mem_rowImage_of_diagonal_form C
    (B ^ b : ZMod (B ^ k)) (B ^ e : ZMod (B ^ k))
    (pow_dvd_pow (B : ZMod (B ^ k)) hbe) P Q hC (reduction (B ^ k) v)
  have hcast : reduction (B ^ k) ((B ^ e) • v) =
      (B ^ e : ZMod (B ^ k)) • reduction (B ^ k) v := by
    ext i
    simp [reduction, nsmul_eq_mul]
  rw [hcast]
  exact hv

instance integerRowLattice_finiteIndex (h : ℕ) [NeZero h]
    (C : Matrix (Fin 3) (Fin 3) (ZMod h)) : (integerRowLattice h C).FiniteIndex where
  index_ne_zero := by
    rw [integerRowLattice_index]
    exact AddSubgroup.FiniteIndex.index_ne_zero

lemma row_mem_integerRowLattice_of_reduction_eq (h : ℕ)
    (A : Matrix (Fin 3) (Fin 3) ℤ)
    (C G : Matrix (Fin 3) (Fin 3) (ZMod h))
    (hA : A.map (Int.castRingHom (ZMod h)) = G * C) (i : Fin 3) :
    A.row i ∈ integerRowLattice h C := by
  change reduction h (A.row i) ∈ rowImage C
  refine ⟨G.row i, ?_⟩
  have hrow := congrArg (fun M : Matrix (Fin 3) (Fin 3) (ZMod h) => M.row i) hA
  exact hrow.symm

end Problem355.RowLattice

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.DividingPivot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.DividingPivot

variable {R : Type*} [CommRing R]

def lowerShear (t : R) : (Matrix (Fin 2) (Fin 2) R)ˣ where
  val := !![1, 0; -t, 1]
  inv := !![1, 0; t, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]

def upperShear (s : R) : (Matrix (Fin 2) (Fin 2) R)ˣ where
  val := !![1, -s; 0, 1]
  inv := !![1, s; 0, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]

theorem reduce_dividing_pivot (C : Matrix (Fin 2) (Fin 2) R) (s t : R)
    (hs : C 0 1 = C 0 0 * s) (ht : C 1 0 = t * C 0 0) :
    (lowerShear t : Matrix (Fin 2) (Fin 2) R) * C *
      (upperShear s : Matrix (Fin 2) (Fin 2) R) =
        Matrix.diagonal ![C 0 0, C 1 1 - t * C 0 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowerShear, upperShear, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_succ, hs, ht]
  ring

theorem divides_remaining_pivot (C : Matrix (Fin 2) (Fin 2) R) (t : R)
    (hb : C 0 0 ∣ C 0 1) (hd : C 0 0 ∣ C 1 1) :
    C 0 0 ∣ C 1 1 - t * C 0 1 :=
  dvd_sub hd (dvd_mul_of_dvd_right hb t)

theorem undo_reduction {M : Type*} [Monoid M] (P Q : Mˣ) (C D : M)
    (h : (P : M) * C * (Q : M) = D) :
    C = (P⁻¹ : Mˣ) * D * (Q⁻¹ : Mˣ) := by
  rw [← h]
  simp [← mul_assoc]

theorem exists_dividing_pivot_factorization (C : Matrix (Fin 2) (Fin 2) R)
    (h : ∀ i j, C 0 0 ∣ C i j) :
    ∃ (d : R) (P Q : (Matrix (Fin 2) (Fin 2) R)ˣ),
      C 0 0 ∣ d ∧
      C = (P : Matrix (Fin 2) (Fin 2) R) * Matrix.diagonal ![C 0 0, d] *
        (Q : Matrix (Fin 2) (Fin 2) R) := by
  obtain ⟨s, hs⟩ := h 0 1
  obtain ⟨t, ht⟩ := h 1 0
  refine ⟨C 1 1 - t * C 0 1, (lowerShear t)⁻¹, (upperShear s)⁻¹,
    divides_remaining_pivot C t (h 0 1) (h 1 1), ?_⟩
  exact undo_reduction _ _ _ _
    (reduce_dividing_pivot C s t hs (by simpa [mul_comm] using ht))

end Problem355.DividingPivot

end OAI
end

section
-- module Solutions.OAIQW_Problem355.PrimePowerFactors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.PrimePowerFactors

theorem exists_pow_mul_unit {p : ℕ} (hp : p.Prime) (k : ℕ)
    (x : ZMod (p ^ k)) :
    ∃ e ≤ k, ∃ u : (ZMod (p ^ k))ˣ,
      x = (p : ZMod (p ^ k)) ^ e * (u : ZMod (p ^ k)) := by
  obtain ⟨d, hd, v, hv, hx⟩ := ZMod.eq_unit_mul_divisor x
  obtain ⟨e, he, rfl⟩ := (Nat.dvd_prime_pow hp).mp hd
  obtain ⟨u, rfl⟩ := hv
  exact ⟨e, he, u, by simpa [Nat.cast_pow, mul_comm] using hx⟩

theorem exists_least_power_factor {ι : Type*} [Fintype ι] [Nonempty ι]
    {p : ℕ} (hp : p.Prime) (k : ℕ) (x : ι → ZMod (p ^ k)) :
    ∃ i : ι, ∃ e ≤ k, ∃ u : (ZMod (p ^ k))ˣ,
      x i = (p : ZMod (p ^ k)) ^ e * (u : ZMod (p ^ k)) ∧
      ∀ j, (p : ZMod (p ^ k)) ^ e ∣ x j := by
  classical
  choose e he u hu using fun i => exists_pow_mul_unit hp k (x i)
  obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image Finset.univ e Finset.univ_nonempty
  refine ⟨i, e i, he i, u i, hu i, ?_⟩
  intro j
  rw [hu j]
  exact dvd_mul_of_dvd_left (pow_dvd_pow _ (hmin j (Finset.mem_univ j))) _

theorem exists_dvd_all {ι : Type*} [Fintype ι] [Nonempty ι]
    {p : ℕ} (hp : p.Prime) (k : ℕ) (x : ι → ZMod (p ^ k)) :
    ∃ i : ι, ∀ j, x i ∣ x j := by
  obtain ⟨i, e, he, u, hu, hdiv⟩ := exists_least_power_factor hp k x
  refine ⟨i, fun j => ?_⟩
  rw [hu]
  obtain ⟨z, hz⟩ := hdiv j
  refine ⟨(↑(u⁻¹) : ZMod (p ^ k)) * z, ?_⟩
  simpa [mul_assoc] using hz

theorem pow_dvd_pow_iff {p : ℕ} (hp : p.Prime) {k b e : ℕ}
    (hb : b ≤ k) :
    ((p : ZMod (p ^ k)) ^ b ∣ (p : ZMod (p ^ k)) ^ e) ↔ b ≤ e := by
  constructor
  · intro hd
    by_contra hbe
    have heb : e + 1 ≤ b := by omega
    have hek : e + 1 ≤ k := heb.trans hb
    let f : ZMod (p ^ k) →+* ZMod (p ^ (e + 1)) :=
      ZMod.castHom (pow_dvd_pow p hek) (ZMod (p ^ (e + 1)))
    have hzero : (p : ZMod (p ^ (e + 1))) ^ b = 0 := by
      rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
      exact pow_dvd_pow p heb
    obtain ⟨z, hz⟩ := hd
    have hcast := congrArg f hz
    have hsmallzero : (p : ZMod (p ^ (e + 1))) ^ e = 0 := by
      simpa only [map_pow, map_natCast, map_mul, hzero, zero_mul] using hcast
    have hnat : p ^ (e + 1) ∣ p ^ e := by
      apply (ZMod.natCast_eq_zero_iff _ _).mp
      simpa only [Nat.cast_pow] using hsmallzero
    have hbad := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hnat
    omega
  · exact fun hbe => pow_dvd_pow _ hbe

theorem pow_dvd_pow_mul_unit_iff {p : ℕ} (hp : p.Prime) {k b e : ℕ}
    (hb : b ≤ k) (u : (ZMod (p ^ k))ˣ) :
    ((p : ZMod (p ^ k)) ^ b ∣ (p : ZMod (p ^ k)) ^ e * ↑u) ↔ b ≤ e := by
  rw [← pow_dvd_pow_iff hp hb]
  constructor
  · intro hd
    simpa [mul_assoc] using dvd_mul_of_dvd_left hd (↑(u⁻¹) : ZMod (p ^ k))
  · exact fun hd => dvd_mul_of_dvd_left hd _

theorem exists_ordered_factors {p : ℕ} (hp : p.Prime) (k : ℕ)
    (x y : ZMod (p ^ k)) (hxy : x ∣ y) :
    ∃ b e : ℕ, b ≤ e ∧ e ≤ k ∧
      ∃ u v : (ZMod (p ^ k))ˣ,
        x = (p : ZMod (p ^ k)) ^ b * ↑u ∧
        y = (p : ZMod (p ^ k)) ^ e * ↑v := by
  obtain ⟨b, hb, u, hx⟩ := exists_pow_mul_unit hp k x
  obtain ⟨e, he, v, hy⟩ := exists_pow_mul_unit hp k y
  refine ⟨b, e, ?_, he, u, v, hx, hy⟩
  apply (pow_dvd_pow_mul_unit_iff hp hb v).mp
  rw [← hy]
  apply dvd_trans ?_ hxy
  rw [hx]
  exact dvd_mul_right _ _

end Problem355.PrimePowerFactors

end OAI
end

section
-- module Solutions.OAIQW_Problem355.TwoByTwoPivot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem355.TwoByTwoPivot
variable {R : Type*} [CommRing R]
def swapUnit : (Matrix (Fin 2) (Fin 2) R)ˣ where
  val := !![0, 1; 1, 0]
  inv := !![0, 1; 1, 0]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
def pivotUnit (i : Fin 2) : (Matrix (Fin 2) (Fin 2) R)ˣ :=
  if i = 0 then 1 else swapUnit
theorem pivotUnit_mul_apply (A : Matrix (Fin 2) (Fin 2) R) (i a b : Fin 2) :
    ((pivotUnit (R := R) i : Matrix (Fin 2) (Fin 2) R) * A) a b =
      A (Equiv.swap 0 i a) b := by
  fin_cases i <;> fin_cases a <;>
    simp [pivotUnit, swapUnit, Matrix.mul_apply, Fin.sum_univ_two]
theorem mul_pivotUnit_apply (A : Matrix (Fin 2) (Fin 2) R) (j a b : Fin 2) :
    (A * (pivotUnit (R := R) j : Matrix (Fin 2) (Fin 2) R)) a b =
      A a (Equiv.swap 0 j b) := by
  fin_cases j <;> fin_cases b <;>
    simp [pivotUnit, swapUnit, Matrix.mul_apply, Fin.sum_univ_two]
theorem move_pivot_apply (A : Matrix (Fin 2) (Fin 2) R) (i j a b : Fin 2) :
    ((pivotUnit (R := R) i : Matrix (Fin 2) (Fin 2) R) * A *
      (pivotUnit (R := R) j : Matrix (Fin 2) (Fin 2) R)) a b =
      A (Equiv.swap 0 i a) (Equiv.swap 0 j b) := by
  rw [mul_pivotUnit_apply, pivotUnit_mul_apply]
theorem move_dividing_entry (A : Matrix (Fin 2) (Fin 2) R) (i j : Fin 2)
    (h : ∀ a b, A i j ∣ A a b) :
    ∃ P Q : (Matrix (Fin 2) (Fin 2) R)ˣ,
      ((P : Matrix (Fin 2) (Fin 2) R) * A * Q) 0 0 = A i j ∧
      ∀ a b, ((P : Matrix (Fin 2) (Fin 2) R) * A * Q) 0 0 ∣
        ((P : Matrix (Fin 2) (Fin 2) R) * A * Q) a b := by
  refine ⟨pivotUnit i, pivotUnit j, ?_, ?_⟩
  · simp only [move_pivot_apply, Equiv.swap_apply_left]
  · intro a b
    simpa only [move_pivot_apply, Equiv.swap_apply_left] using
      h (Equiv.swap 0 i a) (Equiv.swap 0 j b)
end Problem355.TwoByTwoPivot

end OAI
end

section
-- module Solutions.OAIQW_Problem355.TwoByTwoSmith
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.TwoByTwoSmith
variable {R : Type*} [CommRing R]

def diagonalUnit (u v : Rˣ) : (Matrix (Fin 2) (Fin 2) R)ˣ where
  val := Matrix.diagonal ![(u : R), (v : R)]
  inv := Matrix.diagonal ![(↑(u⁻¹) : R), (↑(v⁻¹) : R)]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.diagonal_apply]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.diagonal_apply]

theorem diagonal_factor (x y : R) (u v : Rˣ) :
    Matrix.diagonal ![x * ↑u, y * ↑v] =
      Matrix.diagonal ![x, y] * (diagonalUnit u v : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonalUnit, Matrix.mul_apply, Matrix.diagonal_apply]

theorem exists_ordered_diagonal (A : Matrix (Fin 2) (Fin 2) R)
    (h : ∃ i j, ∀ a b, A i j ∣ A a b) :
    ∃ (x y : R) (P Q : (Matrix (Fin 2) (Fin 2) R)ˣ),
      x ∣ y ∧ A = (P : Matrix (Fin 2) (Fin 2) R) *
        Matrix.diagonal ![x, y] * (Q : Matrix (Fin 2) (Fin 2) R) := by
  obtain ⟨i, j, hij⟩ := h
  obtain ⟨S, T, hpivot, hdiv⟩ := TwoByTwoPivot.move_dividing_entry A i j hij
  let C := (S : Matrix (Fin 2) (Fin 2) R) * A * (T : Matrix (Fin 2) (Fin 2) R)
  obtain ⟨d, P, Q, hd, hfac⟩ := DividingPivot.exists_dividing_pivot_factorization C hdiv
  refine ⟨C 0 0, d, S⁻¹ * P, Q * T⁻¹, hd, ?_⟩
  have hu := DividingPivot.undo_reduction S T A
    ((P : Matrix (Fin 2) (Fin 2) R) * Matrix.diagonal ![C 0 0, d] * Q) hfac
  simpa only [Units.val_mul, mul_assoc] using hu

theorem exists_prime_power_diagonal {p : ℕ} (hp : p.Prime) (k : ℕ)
    (A : Matrix (Fin 2) (Fin 2) (ZMod (p ^ k))) :
    ∃ b e : ℕ, b ≤ e ∧ e ≤ k ∧
      ∃ P Q : (Matrix (Fin 2) (Fin 2) (ZMod (p ^ k)))ˣ,
        A = (P : Matrix (Fin 2) (Fin 2) (ZMod (p ^ k))) *
          Matrix.diagonal ![(p : ZMod (p ^ k)) ^ b, (p : ZMod (p ^ k)) ^ e] *
          (Q : Matrix (Fin 2) (Fin 2) (ZMod (p ^ k))) := by
  obtain ⟨ij, hij⟩ := PrimePowerFactors.exists_dvd_all hp k
    (fun ij : Fin 2 × Fin 2 => A ij.1 ij.2)
  obtain ⟨x, y, P, Q, hxy, hfac⟩ := exists_ordered_diagonal A
    ⟨ij.1, ij.2, fun a b => hij (a, b)⟩
  obtain ⟨b, e, hbe, hek, u, v, hx, hy⟩ :=
    PrimePowerFactors.exists_ordered_factors hp k x y hxy
  refine ⟨b, e, hbe, hek, P, diagonalUnit u v * Q, ?_⟩
  rw [hx, hy, diagonal_factor] at hfac
  simpa only [Units.val_mul, mul_assoc] using hfac

end Problem355.TwoByTwoSmith

end OAI
end

section
-- module Solutions.OAIQW_Problem355.PrimePowerData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355

structure PrimePowerData (p k : ℕ) (C : Matrix (Fin 3) (Fin 3) (ZMod (p ^ k))) where
  b : ℕ
  e : ℕ
  b_le_e : b ≤ e
  e_le_k : e ≤ k
  left : Matrix.GeneralLinearGroup (Fin 3) (ZMod (p ^ k))
  right : Matrix.GeneralLinearGroup (Fin 3) (ZMod (p ^ k))
  diagonalization : C = (left : Matrix _ _ _) *
    Matrix.diagonal ![1, ((p ^ b : ℕ) : ZMod (p ^ k)),
      ((p ^ e : ℕ) : ZMod (p ^ k))] * (right : Matrix _ _ _)

namespace PrimePowerData

variable {p k : ℕ} {C : Matrix (Fin 3) (Fin 3) (ZMod (p ^ k))}

theorem nonempty_of_unit (hp : p.Prime) (hunit : IsUnit (C 0 0)) :
    Nonempty (PrimePowerData p k C) := by
  let rel : ZMod (p ^ k) → ZMod (p ^ k) → Prop := fun x y =>
    ∃ b e : ℕ, b ≤ e ∧ e ≤ k ∧
      x = (p : ZMod (p ^ k)) ^ b ∧ y = (p : ZMod (p ^ k)) ^ e
  have hdiag : ∀ A : Matrix (Fin 2) (Fin 2) (ZMod (p ^ k)),
      ∃ P Q : Matrix.GeneralLinearGroup (Fin 2) (ZMod (p ^ k)),
      ∃ x y : ZMod (p ^ k), rel x y ∧
        A = (P : Matrix _ _ _) * Matrix.diagonal ![x, y] * (Q : Matrix _ _ _) := by
    intro A
    obtain ⟨b, e, hbe, hek, P, Q, hA⟩ := TwoByTwoSmith.exists_prime_power_diagonal hp k A
    exact ⟨P, Q, _, _, ⟨b, e, hbe, hek, rfl, rfl⟩, hA⟩
  obtain ⟨P, Q, x, y, hrel, hC⟩ :=
    PivotAssembly.exists_factorization_of_two_by_two_units rel hdiag C hunit
  obtain ⟨b, e, hbe, hek, hx, hy⟩ := hrel
  refine ⟨⟨b, e, hbe, hek, P, Q, ?_⟩⟩
  rw [hx, hy] at hC
  simpa only [Nat.cast_pow] using hC

noncomputable def ofUnit (hp : p.Prime) (hunit : IsUnit (C 0 0)) :
    PrimePowerData p k C :=
  Classical.choice (nonempty_of_unit hp hunit)

lemma b_le_k (d : PrimePowerData p k C) : d.b ≤ k :=
  d.b_le_e.trans d.e_le_k

theorem row_lattice_index (d : PrimePowerData p k C) (hp : p ≠ 0) :
    (RowLattice.integerRowLattice (p ^ k) C).index = p ^ d.b * p ^ d.e := by
  let : NeZero p := ⟨hp⟩
  apply RowLattice.integerRowLattice_index_prime_power p k d.b d.e
    d.b_le_k d.e_le_k C d.left d.right
  simpa only [DiagonalStabilizer.diagonal3, Nat.cast_pow] using d.diagonalization

theorem multiple_mem_row_lattice (d : PrimePowerData p k C) (v : Fin 3 → ℤ) :
    (p ^ d.e) • v ∈ RowLattice.integerRowLattice (p ^ k) C := by
  apply RowLattice.nsmul_mem_integerRowLattice_prime_power p k d.b d.e
    d.b_le_e C d.left d.right _ v
  simpa only [DiagonalStabilizer.diagonal3, Nat.cast_pow] using d.diagonalization

end PrimePowerData

end Problem355

end OAI
end

section
-- module Solutions.OAIQW_Problem355.SmithDigitMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.PrimePowerData

open scoped BigOperators

noncomputable def ofArray {X : Type*} {B k : ℕ}
    (hB : B.Prime) (hk : 0 < k)
    (digit : Fin 3 → Fin 3 → Fin k → X → Fin B)
    (hpos : ∀ a c v x, 0 < (digit a c v x).val)
    (f : Fin 3 → Fin 3 → Fin k → X) :
    PrimePowerData B k (ConditionalMatrix.arrayMatrix digit f k) :=
  ofUnit hB (ConditionalMatrix.encoded_isUnit hB hk hk
    (fun v => digit 0 0 v (f 0 0 v)) (fun v => hpos 0 0 v (f 0 0 v)))

end Problem355.PrimePowerData

end OAI
end

section
-- module Solutions.OAIQW_Problem355.MainDigitLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

attribute [local irreducible] Problem355.heilbronnT Problem355.heilbronnM

namespace Problem355.MainDigitLaw

open Parameters FiniteFieldLabels
open scoped BigOperators

variable {r : ℕ} [Fact r.Prime]

abbrev Sample (r : ℕ) := Fin (r ^ 9)
abbrev Latent (r : ℕ) [Fact r.Prime] :=
  DigitColumnLaw.Latent (Label r) (Sample r) heilbronnK
abbrev Array (r : ℕ) := DigitColumnLaw.Array (Sample r) heilbronnK

variable (D : PrimeParameterData heilbronnK r)

omit [Fact r.Prime] in
lemma alphabet_bound : r * r ^ 9 < D.B := by
  convert D.alphabet_lt_base using 1
  ring

def digit (label : Label r) (a : Fin 3) (v : Fin heilbronnK)
    (x : Sample r) : Fin D.B :=
  ConditionalMatrix.prescribedDigit (alphabet_bound D)
    (fun i _ w => MainResidueSystem.finiteResidue r i w label) a 0 v x

lemma digit_positive (label : Label r) (a : Fin 3) (v : Fin heilbronnK)
    (x : Sample r) : 0 < (digit D label a v x).val :=
  ConditionalMatrix.prescribedDigit_positive (alphabet_bound D)
    (fun i _ w => MainResidueSystem.finiteResidue r i w label) a 0 v x

def column (x : Latent r) : Fin 3 → ZMod (D.B ^ heilbronnK) :=
  @DigitColumnLaw.residueColumn (Label r) (Sample r) D.B heilbronnK (digit D) x

def arrayDigit (labels : Fin 3 → Label r) :
    Fin 3 → Fin 3 → Fin heilbronnK → Sample r → Fin D.B :=
  fun a c v x => digit D (labels c) a v x

def matrix (labels : Fin 3 → Label r) (f : Array r) :
    Matrix (Fin 3) (Fin 3) (ZMod (D.B ^ heilbronnK)) :=
  @ConditionalMatrix.arrayMatrix (Sample r) D.B heilbronnK
    (arrayDigit D labels) f heilbronnK

def smith (labels : Fin 3 → Label r) (f : Array r) :
    PrimePowerData D.B heilbronnK (matrix D labels f) :=
  PrimePowerData.ofArray (X := Sample r) (B := D.B) (k := heilbronnK)
    D.base_prime heilbronnK_pos (arrayDigit D labels)
    (fun a c v x => digit_positive D (labels c) a v x) f

end Problem355.MainDigitLaw

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.FiniteMixtures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.ConditionalSamples

noncomputable section

variable {α β ι : Type*}

def mixtureWeight [Fintype β] (p : β → ℝ) (ν : β → α → ℝ) (a : α) : ℝ :=
  ∑ b, p b * ν b a

lemma mixtureWeight_nonneg [Fintype β] (p : β → ℝ) (ν : β → α → ℝ)
    (hp : ∀ b, 0 ≤ p b) (hν : ∀ b a, 0 ≤ ν b a) (a : α) :
    0 ≤ mixtureWeight p ν a :=
  Finset.sum_nonneg fun b _ => mul_nonneg (hp b) (hν b a)

lemma sum_mixtureWeight [Fintype α] [Fintype β]
    (p : β → ℝ) (ν : β → α → ℝ)
    (hp : ∑ b, p b = 1) (hν : ∀ b, ∑ a, ν b a = 1) :
    ∑ a, mixtureWeight p ν a = 1 := by
  unfold mixtureWeight
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hν, mul_one]
  exact hp

end
end Problem355.ConditionalSamples

end OAI
end

section
-- module Solutions.OAIQW_Problem355.CRTLifting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.CRT

def zmodResidueLiftEquiv (m t : ℕ) [NeZero m] (r : ZMod m) :
    {x : Fin (t * m) // (x.val : ZMod m) = r} ≃ Fin t where
  toFun x := x.val.divNat
  invFun y := ⟨finProdFinEquiv (y, ⟨r.val, r.val_lt⟩), by
    change ((r.val + m * y.val : ℕ) : ZMod m) = r
    simp⟩
  left_inv x := by
    apply Subtype.ext
    apply Fin.ext
    change r.val + m * (x.val.val / m) = x.val.val
    have hr : x.val.val % m = r.val := by
      simpa using congrArg ZMod.val x.property
    rw [← hr]
    exact Nat.mod_add_div _ _
  right_inv y := by
    apply Fin.ext
    change (r.val + m * y.val) / m = y.val
    rw [Nat.add_mul_div_left _ _ (Nat.pos_of_ne_zero (NeZero.ne m)),
      Nat.div_eq_of_lt r.val_lt, Nat.zero_add]

theorem crt_residue_iff (h q : ℕ) (hc : h.Coprime q)
    (a : ZMod h) (b : ZMod q) (x : ℕ) :
    ((x : ZMod h) = a ∧ (x : ZMod q) = b) ↔
      (x : ZMod (h * q)) = (ZMod.chineseRemainder hc).symm (a, b) := by
  constructor
  · intro hx
    apply (ZMod.chineseRemainder hc).injective
    simpa only [map_natCast, RingEquiv.apply_symm_apply, Prod.ext_iff, Prod.fst_natCast, Prod.snd_natCast] using hx
  · intro hx
    have hh := congrArg (ZMod.chineseRemainder hc) hx
    simpa only [map_natCast, RingEquiv.apply_symm_apply, Prod.ext_iff, Prod.fst_natCast, Prod.snd_natCast] using hh

def crtLiftEquiv (h q t : ℕ) [NeZero h] [NeZero q]
    (hc : h.Coprime q) (a : ZMod h) (b : ZMod q) :
    {x : Fin (t * (h * q)) //
      (x.val : ZMod h) = a ∧ (x.val : ZMod q) = b} ≃ Fin t :=
  (Equiv.subtypeEquivRight fun (x : Fin (t * (h * q))) => crt_residue_iff h q hc a b x.val).trans
    (zmodResidueLiftEquiv (h * q) t ((ZMod.chineseRemainder hc).symm (a, b)))

def intIntervalEquiv (N : ℕ) (s : ℤ) : Fin N ≃ Set.Ico s (s + N) where
  toFun x := ⟨s + x.val, by
    constructor
    · omega
    · have hx := x.is_lt
      omega⟩
  invFun x := ⟨(x.val - s).toNat, by
    rcases x.property with ⟨hx0, hx1⟩
    omega⟩
  left_inv x := by
    apply Fin.ext
    simp
  right_inv x := by
    apply Subtype.ext
    rcases x.property with ⟨hx0, hx1⟩
    dsimp
    omega

def intCRTLiftEquiv (h q t : ℕ) [NeZero h] [NeZero q]
    (hc : h.Coprime q) (s : ℤ) (a : ZMod h) (b : ZMod q) :
    {x : Set.Ico s (s + (t * (h * q) : ℕ)) //
      (x.val : ZMod h) = a ∧ (x.val : ZMod q) = b} ≃ Fin t := by
  let e := (intIntervalEquiv (t * (h * q)) s).subtypeEquiv
    (p := fun x => (x.val : ZMod h) = a - (s : ZMod h) ∧
      (x.val : ZMod q) = b - (s : ZMod q))
    (q := fun x => (x.val : ZMod h) = a ∧ (x.val : ZMod q) = b)
    (by
      intro x
      change ((x.val : ZMod h) = a - (s : ZMod h) ∧
        (x.val : ZMod q) = b - (s : ZMod q)) ↔
        (((s + x.val : ℤ) : ZMod h) = a ∧ ((s + x.val : ℤ) : ZMod q) = b)
      simp only [eq_sub_iff_add_eq, Int.cast_add, Int.cast_natCast]
      simp only [add_comm])
  exact e.symm.trans (crtLiftEquiv h q t hc (a - (s : ZMod h)) (b - (s : ZMod q)))

def intCRTVectorLiftEquiv (h q t d : ℕ) [NeZero h] [NeZero q]
    (hc : h.Coprime q) (s : Fin d → ℤ)
    (a : Fin d → ZMod h) (b : Fin d → ZMod q) :
    {x : (i : Fin d) → Set.Ico (s i) (s i + (t * (h * q) : ℕ)) // ∀ i,
      ((x i).val : ZMod h) = a i ∧ ((x i).val : ZMod q) = b i} ≃
      (Fin d → Fin t) :=
  Equiv.subtypePiEquivPi.trans
    (Equiv.piCongrRight fun i => intCRTLiftEquiv h q t hc (s i) (a i) (b i))

theorem card_int_crt_vector_lifts (h q t d : ℕ) [NeZero h] [NeZero q]
    (hc : h.Coprime q) (s : Fin d → ℤ)
    (a : Fin d → ZMod h) (b : Fin d → ZMod q) :
    Fintype.card
      {x : (i : Fin d) → Set.Ico (s i) (s i + (t * (h * q) : ℕ)) // ∀ i,
        ((x i).val : ZMod h) = a i ∧ ((x i).val : ZMod q) = b i} = t ^ d := by
  rw [Fintype.card_congr (intCRTVectorLiftEquiv h q t d hc s a b)]
  simp

end Problem355.CRT

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.IntegerSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.IntegerSampling

abbrev Box (N d : ℕ) (shift : Fin d → ℤ) :=
  (i : Fin d) → Set.Ico (shift i) (shift i + N)

def residue (m : ℕ) {N d : ℕ} {shift : Fin d → ℤ} (x : Box N d shift) :
    Fin d → ZMod m := fun i => ((x i).val : ZMod m)

theorem card_joint_residue_fibre (h q L d : ℕ) [NeZero h] [NeZero q]
    (hc : h.Coprime q) (shift : Fin d → ℤ)
    (r : (Fin d → ZMod h) × (Fin d → ZMod q)) :
    (Finset.univ.filter (fun x : Box (L * (h * q)) d shift =>
      (residue h x, residue q x) = r)).card = L ^ d := by
  classical
  calc
    (Finset.univ.filter (fun x : Box (L * (h * q)) d shift =>
      (residue h x, residue q x) = r)).card =
        Fintype.card {x : Box (L * (h * q)) d shift //
          (residue h x, residue q x) = r} := (Fintype.card_subtype _).symm
    _ = Fintype.card {x : Box (L * (h * q)) d shift // ∀ i,
        ((x i).val : ZMod h) = r.1 i ∧ ((x i).val : ZMod q) = r.2 i} := by
      apply Fintype.card_congr
      exact Equiv.subtypeEquivRight fun x => by
        simp only [Prod.ext_iff, residue, funext_iff, forall_and]
    _ = L ^ d := CRT.card_int_crt_vector_lifts h q L d hc shift r.1 r.2

def columnLaw (h q L : ℕ) (shift : Fin 3 → ℤ)
    (a : Fin 3 → ZMod h) (V : Finset (Fin 3 → ZMod q)) (s : ℕ)
    (x : Box (L * (h * q)) 3 shift) : ℝ :=
  LiftingProbability.conditionalColumnMass (residue h) (residue q) a V s L x

 theorem columnLaw_nonneg (h q L : ℕ) (shift : Fin 3 → ℤ)
    (a : Fin 3 → ZMod h) (V : Finset (Fin 3 → ZMod q)) (s : ℕ)
    (x : Box (L * (h * q)) 3 shift) : 0 ≤ columnLaw h q L shift a V s x :=
  LiftingProbability.conditionalColumnMass_nonneg (residue h) (residue q) a V s L x

theorem sum_columnLaw (h q L : ℕ) [NeZero h] [NeZero q]
    (hc : h.Coprime q) (hL : 0 < L) (shift : Fin 3 → ℤ)
    (a : Fin 3 → ZMod h) (V : Finset (Fin 3 → ZMod q)) (s : ℕ)
    (hs : 0 < s) (hV : V.card = s) :
    (∑ x, columnLaw h q L shift a V s x) = 1 := by
  classical
  apply LiftingProbability.sum_conditionalColumnMass (residue h) (residue q)
    a V s L hs hL hV
  exact card_joint_residue_fibre h q L 3 hc shift

def samplingShift (N : ℕ) : Fin 3 → ℤ := ![0, 0, (N : ℤ)]

def project {N : ℕ} (x : Box N 3 (samplingShift N)) : Point :=
  (((x 0).val : ℝ) / ((x 2).val : ℝ), ((x 1).val : ℝ) / ((x 2).val : ℝ))

theorem project_in_unitSquare {N : ℕ} (hN : 0 < N)
    (x : Box N 3 (samplingShift N)) : pointInUnitSquare (project x) := by
  have hx : 0 ≤ (x 0).val ∧ (x 0).val < (N : ℤ) := by
    simpa [samplingShift] using (x 0).property
  have hy : 0 ≤ (x 1).val ∧ (x 1).val < (N : ℤ) := by
    simpa [samplingShift] using (x 1).property
  have hz : (N : ℤ) ≤ (x 2).val ∧ (x 2).val < (N : ℤ) + N := by
    exact (x 2).property
  have hzpos : 0 < ((x 2).val : ℝ) := by
    have : (0 : ℤ) < (x 2).val := lt_of_lt_of_le (by exact_mod_cast hN) hz.1
    exact_mod_cast this
  unfold pointInUnitSquare project
  exact ⟨div_nonneg (by exact_mod_cast hx.1) hzpos.le,
    (div_le_one hzpos).mpr (by exact_mod_cast hx.2.le.trans hz.1),
    div_nonneg (by exact_mod_cast hy.1) hzpos.le,
    (div_le_one hzpos).mpr (by exact_mod_cast hy.2.le.trans hz.1)⟩

end Problem355.IntegerSampling

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.SampleDeletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.Alteration

noncomputable def collisionEdges {ι β : Type*} [DecidableEq ι] (S : Finset ι) (f : ι → β) :
    Finset (Finset ι) := by
  classical
  exact (S.powersetCard 2).filter (fun e =>
    ∃ i ∈ e, ∃ j ∈ e, i ≠ j ∧ f i = f j)

noncomputable def badTripleEdges {ι β : Type*} [DecidableEq ι] (S : Finset ι) (f : ι → β)
    (bad : β → β → β → Prop) : Finset (Finset ι) := by
  classical
  exact (S.powersetCard 3).filter (fun e =>
    ∃ i ∈ e, ∃ j ∈ e, ∃ k ∈ e,
      i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ bad (f i) (f j) (f k))

end Problem355.Alteration

end OAI
end

section
-- module Solutions.OAIQW_Problem355.GeometricAlteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.Alteration

def smallTriangle (a : ℝ) (p q r : Point) : Prop :=
  p ≠ q ∧ p ≠ r ∧ q ≠ r ∧ triangleArea p q r < a

end Problem355.Alteration

end OAI
end

section
-- module Solutions.OAIQW_Problem355.ParameterConclusion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.Parameters

namespace PrimeParameterData

variable {k r : ℕ}

def sampleCard (P : PrimeParameterData k r) : ℕ :=
  ⌊(r : ℝ) * Real.sqrt ((P.N : ℝ) ^ 3 / (P.tau : ℝ))⌋₊

end PrimeParameterData

end Problem355.Parameters

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.SharedGeometricAlteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


open Finset

noncomputable section

namespace Problem355.SharedGeometricAlteration

variable {Θ X : Type*} [Fintype Θ] [Fintype X]

def pairMass (ρ : Θ → ℝ) (μ : Θ → X → ℝ) (point : Θ → X → Point) : ℝ := by
  classical
  exact ∑ z : Θ × (Fin 2 → X),
    if point z.1 (z.2 0) = point z.1 (z.2 1)
      then ConditionalSamples.sharedWeight ρ μ z else 0

def tripleMass (ρ : Θ → ℝ) (μ : Θ → X → ℝ) (point : Θ → X → Point) (a : ℝ) : ℝ := by
  classical
  exact ∑ z : Θ × (Fin 3 → X),
    if Alteration.smallTriangle a (point z.1 (z.2 0)) (point z.1 (z.2 1))
        (point z.1 (z.2 2))
      then ConditionalSamples.sharedWeight ρ μ z else 0

end Problem355.SharedGeometricAlteration

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.ParameterSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.ParameterSampling

open Parameters Parameters.PrimeParameterData

structure PointLaw where
  Environment : Type
  Column : Type
  environmentFintype : Fintype Environment
  columnFintype : Fintype Column
  rho : Environment → ℝ
  mu : Environment → Column → ℝ
  point : Environment → Column → Point
  rho_nonneg : ∀ θ, 0 ≤ rho θ
  rho_sum : @Finset.sum Environment ℝ _ Finset.univ rho = 1
  mu_nonneg : ∀ θ x, 0 ≤ mu θ x
  mu_sum : ∀ θ, @Finset.sum Column ℝ _ Finset.univ (mu θ) = 1
  in_square : ∀ θ x, pointInUnitSquare (point θ x)

attribute [instance] PointLaw.environmentFintype PointLaw.columnFintype

def PointLaw.pairProbability (L : PointLaw) : ℝ :=
  SharedGeometricAlteration.pairMass L.rho L.mu L.point

def PointLaw.tripleProbability (L : PointLaw) (a : ℝ) : ℝ :=
  SharedGeometricAlteration.tripleMass L.rho L.mu L.point a

end Problem355.ParameterSampling

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.IntegerPointLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.IntegerPointLaw

open IntegerSampling ConditionalSamples ParameterSampling

def ofMixture {Θ D : Type} [Fintype Θ] [Fintype D]
    (h q L s : ℕ) [NeZero h] [NeZero q]
    (hc : h.Coprime q) (hL : 0 < L) (hs : 0 < s)
    (rho : Θ → ℝ) (p : D → ℝ)
    (a : Θ → D → Fin 3 → ZMod h)
    (V : Θ → Finset (Fin 3 → ZMod q))
    (hrho : ∀ θ, 0 ≤ rho θ) (hsum : ∑ θ, rho θ = 1)
    (hp : ∀ d, 0 ≤ p d) (hpsum : ∑ d, p d = 1)
    (hV : ∀ θ, (V θ).card = s) : PointLaw where
  Environment := Θ
  Column := Box (L * (h * q)) 3 (samplingShift (L * (h * q)))
  environmentFintype := inferInstance
  columnFintype := inferInstance
  rho := rho
  mu := fun θ => mixtureWeight p (fun d => columnLaw h q L
    (samplingShift (L * (h * q))) (a θ d) (V θ) s)
  point := fun _ x => project x
  rho_nonneg := hrho
  rho_sum := hsum
  mu_nonneg := fun θ x => mixtureWeight_nonneg p _ hp
    (fun d x => columnLaw_nonneg h q L _ (a θ d) (V θ) s x) x
  mu_sum := fun θ => sum_mixtureWeight p _ hpsum
    (fun d => sum_columnLaw h q L hc hL _ (a θ d) (V θ) s hs (hV θ))
  in_square := fun _ x => project_in_unitSquare
    (mul_pos hL (mul_pos (NeZero.pos h) (NeZero.pos q))) x

def ofIndependentEnvironments {Θ Ω D : Type}
    [Fintype Θ] [Fintype Ω] [Fintype D]
    (h q L s : ℕ) [NeZero h] [NeZero q]
    (hc : h.Coprime q) (hL : 0 < L) (hs : 0 < s)
    (rho : Θ → ℝ) (w : Ω → ℝ) (p : D → ℝ)
    (a : Θ → D → Fin 3 → ZMod h)
    (V : Ω → Finset (Fin 3 → ZMod q))
    (hrho : ∀ θ, 0 ≤ rho θ) (hsum : ∑ θ, rho θ = 1)
    (hw : ∀ ω, 0 ≤ w ω) (hwsum : ∑ ω, w ω = 1)
    (hp : ∀ d, 0 ≤ p d) (hpsum : ∑ d, p d = 1)
    (hV : ∀ ω, (V ω).card = s) : PointLaw :=
  ofMixture h q L s hc hL hs (fun z : Θ × Ω => rho z.1 * w z.2) p
    (fun z d => a z.1 d) (fun z => V z.2)
    (fun z => mul_nonneg (hrho z.1) (hw z.2))
    (by
      rw [Fintype.sum_prod_type]
      simp_rw [← Finset.mul_sum, hwsum, mul_one]
      exact hsum)
    hp hpsum (fun z => hV z.2)

def ofSpecialLinear {Ω D : Type} [Fintype Ω] [Fintype D]
    (h q L s : ℕ) [NeZero h] [NeZero q]
    (hc : h.Coprime q) (hL : 0 < L) (hs : 0 < s)
    (w : Ω → ℝ) (p : D → ℝ) (c : D → Fin 3 → ZMod h)
    (V : Ω → Finset (Fin 3 → ZMod q))
    (hw : ∀ ω, 0 ≤ w ω) (hwsum : ∑ ω, w ω = 1)
    (hp : ∀ d, 0 ≤ p d) (hpsum : ∑ d, p d = 1)
    (hV : ∀ ω, (V ω).card = s) : PointLaw := by
  classical
  let G := Matrix.SpecialLinearGroup (Fin 3) (ZMod h)
  apply ofIndependentEnvironments h q L s hc hL hs
    (fun _ : G => 1 / (Nat.card G : ℝ)) w p (fun g d => g • c d) V
  · intro g
    positivity
  · simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Nat.card_eq_fintype_card]
    exact mul_one_div_cancel (by positivity)
  · exact hw
  · exact hwsum
  · exact hp
  · exact hpsum
  · exact hV

end Problem355.IntegerPointLaw

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.ProportionalPairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


open Finset

noncomputable section

namespace Problem355.ProportionalPairs

def coordinatePairs (N a b : ℕ) : Finset (ℕ × ℕ) :=
  (range N ×ˢ range N).filter fun p => a * p.2 = b * p.1

def proportionalPairParameters (N : ℕ) : Finset (Σ _a : ℕ, Σ _b : ℕ, (ℕ × ℕ) × (ℕ × ℕ)) :=
  (Ico N (2 * N)).sigma fun a =>
    (Ico N (2 * N)).sigma fun b => coordinatePairs N a b ×ˢ coordinatePairs N a b

abbrev NatColumn := (ℕ × ℕ) × ℕ

def columnBox (N : ℕ) : Finset NatColumn :=
  (range N ×ˢ range N) ×ˢ Ico N (2 * N)

def Proportional (u v : NatColumn) : Prop :=
  u.2 * v.1.1 = v.2 * u.1.1 ∧ u.2 * v.1.2 = v.2 * u.1.2

instance instDecidableProportional (u v : NatColumn) : Decidable (Proportional u v) :=
  inferInstanceAs (Decidable (_ ∧ _))

def proportionalPairs (N : ℕ) : Finset (NatColumn × NatColumn) :=
  (columnBox N ×ˢ columnBox N).filter fun p => Proportional p.1 p.2

def project (u : NatColumn) : ℝ × ℝ :=
  ((u.1.1 : ℝ) / u.2, (u.1.2 : ℝ) / u.2)

end Problem355.ProportionalPairs

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.LiftCollisions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


open Finset

noncomputable section

namespace Problem355.LiftCollisions

abbrev Column := Fin 3 → ℤ

def InBox (N : ℕ) (u : Column) : Prop :=
  0 ≤ u 0 ∧ u 0 < N ∧ 0 ≤ u 1 ∧ u 1 < N ∧ (N : ℤ) ≤ u 2 ∧ u 2 < 2 * N

def natColumn (u : Column) : ProportionalPairs.NatColumn :=
  (((u 0).toNat, (u 1).toNat), (u 2).toNat)

def intColumn (u : ProportionalPairs.NatColumn) : Column :=
  ![(u.1.1 : ℤ), (u.1.2 : ℤ), (u.2 : ℤ)]

def project (u : Column) : ℝ × ℝ :=
  ((u 0 : ℝ) / (u 2 : ℝ), (u 1 : ℝ) / (u 2 : ℝ))

end Problem355.LiftCollisions

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.IntegerSamplingPairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

open scoped BigOperators

namespace Problem355.IntegerSamplingPairs

open LiftCollisions

def collisionMass {X : Type*} [Fintype X] (col : X → Column)
    (p q : X → ℝ) : ℝ := by
  classical
  exact ∑ x, ∑ y, if project (col x) = project (col y) then p x * q y else 0

def boxColumn {N : ℕ} (x : IntegerSampling.Box N 3 (IntegerSampling.samplingShift N)) :
    Column := fun i => (x i).val

@[simp] theorem project_boxColumn {N : ℕ}
    (x : IntegerSampling.Box N 3 (IntegerSampling.samplingShift N)) :
    project (boxColumn x) = IntegerSampling.project x := rfl

end Problem355.IntegerSamplingPairs

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.PrimeLiftParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.Parameters.PrimeParameterData

variable {k r : ℕ} (D : PrimeParameterData k r)

def liftMultiplicity : ℕ := D.M ^ 9

lemma liftMultiplicity_pos : 0 < D.liftMultiplicity :=
  pow_pos D.M_pos _

lemma h_pos : 0 < D.h := lt_of_lt_of_le (by norm_num : 0 < 3) D.h_ge_three

end Problem355.Parameters.PrimeParameterData

namespace Problem355.PrimeLiftParameters

open Parameters Parameters.PrimeParameterData ParameterSampling

variable {k r : ℕ}

def pointLaw (D : PrimeParameterData k r)
    {Ω Δ : Type} [Fintype Ω] [Fintype Δ]
    (s : ℕ) (hs : 0 < s)
    (w : Ω → ℝ) (p : Δ → ℝ)
    (c : Δ → Fin 3 → ZMod D.h)
    (V : Ω → Finset (Fin 3 → ZMod D.q))
    (hw : ∀ ω, 0 ≤ w ω) (hwsum : ∑ ω, w ω = 1)
    (hp : ∀ δ, 0 ≤ p δ) (hpsum : ∑ δ, p δ = 1)
    (hV : ∀ ω, (V ω).card = s) : PointLaw := by
  letI : NeZero D.h := ⟨ne_of_gt D.h_pos⟩
  letI : NeZero D.q := ⟨D.auxiliary_prime.ne_zero⟩
  exact IntegerPointLaw.ofSpecialLinear D.h D.q D.liftMultiplicity s
    D.coprime D.liftMultiplicity_pos hs w p c V hw hwsum hp hpsum hV

end Problem355.PrimeLiftParameters

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.ActualPointLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

attribute [local irreducible] Problem355.heilbronnT Problem355.heilbronnM

namespace Problem355.ActualPointLaw

open Parameters FiniteFieldLabels

section WithAuxiliary
variable {r : ℕ} [Fact r.Prime] [Fintype (Label r)]

def withAuxiliary (D : PrimeParameterData heilbronnK r)
    [Fact D.q.Prime] (A : AuxiliarySampling.Law D.q (D.h ^ 2)) :
    ParameterSampling.PointLaw := by
  letI : NeZero (r ^ 9) := ⟨pow_ne_zero _ D.r_pos.ne'⟩
  exact PrimeLiftParameters.pointLaw D A.size A.size_pos A.weight
    (DigitColumnLaw.uniformWeight (MainDigitLaw.Latent r))
    (MainDigitLaw.column D) A.sets A.weight_nonneg A.weight_sum
    (DigitColumnLaw.uniformWeight_nonneg _) (DigitColumnLaw.sum_uniformWeight _)
    A.sets_card

end WithAuxiliary

variable {r : ℕ} [Fact r.Prime]

def pointLaw (D : PrimeParameterData heilbronnK r) : ParameterSampling.PointLaw := by
  letI : Fintype (Label r) := Fintype.ofFinite (Label r)
  letI : Fact D.q.Prime := ⟨D.auxiliary_prime⟩
  have hH : 1 ≤ D.h ^ 2 := Nat.one_le_pow _ _ D.h_pos
  exact withAuxiliary D (Classical.choice
    (AuxiliarySampling.nonempty_law hH D.auxiliary_large))

end Problem355.ActualPointLaw

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.DigitBadTripleAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.DigitColumnLaw

open scoped BigOperators

def labelsEquiv (Λ : Type*) : (Fin 3 → Λ) ≃ Λ × Λ × Λ where
  toFun l := (l 0, l 1, l 2)
  invFun t := ![t.1, t.2.1, t.2.2]
  left_inv l := by funext i; fin_cases i <;> rfl
  right_inv t := rfl

end Problem355.DigitColumnLaw

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.OrbitSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.OrbitSampling

def orbitFinset (G : Type*) {X : Type*} [Group G] [MulAction G X] [Fintype X]
    (x : X) : Finset X := by
  classical
  exact Finset.univ.filter (fun y => y ∈ MulAction.orbit G x)

abbrev MainGroup (h : ℕ) := Matrix.SpecialLinearGroup (Fin 3) (ZMod h)

theorem sl_action_transpose (h : ℕ) (G : MainGroup h)
    (C : Fin 3 → Fin 3 → ZMod h) :
    Matrix.transpose (G • C) = G.val * Matrix.transpose C := by
  ext i j
  rfl

def integralMatrix {N : ℕ} {shift : Fin 3 → ℤ}
    (x : Fin 3 → IntegerSampling.Box N 3 shift) : Matrix (Fin 3) (Fin 3) ℤ :=
  fun i j => (x j i).val

end Problem355.OrbitSampling

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.HomogeneousGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.Homogeneous

abbrev Column := Fin 3 → ℝ

def project (u : Column) : ℝ × ℝ := (u 0 / u 2, u 1 / u 2)

def columns (u v w : Column) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![u 0, v 0, w 0; u 1, v 1, w 1; u 2, v 2, w 2]

def InBox (N : ℝ) (u : Column) : Prop :=
  0 ≤ u 0 ∧ u 0 < N ∧ 0 ≤ u 1 ∧ u 1 < N ∧ N ≤ u 2 ∧ u 2 < 2 * N

end Problem355.Homogeneous

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.ProjectiveBadEvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.Homogeneous

open Finset
noncomputable section
attribute [local instance] Classical.propDecidable

def projectedDistinct (u v w : Column) : Prop :=
  project u ≠ project v ∧ project u ≠ project w ∧ project v ≠ project w

def integerColumn (A : Matrix (Fin 3) (Fin 3) ℤ) (j : Fin 3) : Column :=
  fun i => (A i j : ℝ)

end
end Problem355.Homogeneous

end OAI
end

section
-- module Solutions.OAIQW_Problem355.IntegerPointLawTriples
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.IntegerPointLaw

open IntegerSampling ConditionalSamples ParameterSampling
open Finset
attribute [local instance] Classical.propDecidable

def triangleEvent {N : ℕ} (a : ℝ)
    (x : Fin 3 → Box N 3 (samplingShift N)) : Prop :=
  Alteration.smallTriangle a (project (x 0)) (project (x 1)) (project (x 2))

def badDeterminantEvent {N : ℕ} (τ : ℤ)
    (x : Fin 3 → Box N 3 (samplingShift N)) : Prop :=
  project (x 0) ≠ project (x 1) ∧ project (x 0) ≠ project (x 2) ∧
    project (x 1) ≠ project (x 2) ∧ |(OrbitSampling.integralMatrix x).det| ≤ τ

end Problem355.IntegerPointLaw

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.MainDigitObstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.MainDigitObstruction

open FiniteFieldLabels Parameters

def extendDigits {k : ℕ} (d : Fin k → ℕ) (v : ℕ) : ℤ :=
  if hv : v < k then d ⟨v, hv⟩ else 0

end Problem355.MainDigitObstruction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.MainOrbitObstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.MainOrbitObstruction

open OrbitSampling

def columnResidue (h : ℕ) (A : Matrix (Fin 3) (Fin 3) ℤ) :
    Fin 3 → Fin 3 → ZMod h := fun j i => (A i j : ZMod h)

end Problem355.MainOrbitObstruction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.MainDigitOrbitObstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

attribute [local irreducible] Problem355.heilbronnT Problem355.heilbronnM

namespace Problem355.MainDigitOrbitObstruction

open Parameters FiniteFieldLabels MainDigitLaw OrbitSampling

attribute [local instance] Classical.propDecidable

variable {r : ℕ} [Fact r.Prime]
variable (D : PrimeParameterData heilbronnK r)

def columns (h : ℕ) (labels : Fin 3 → Label r) (f : MainDigitLaw.Array r) :
    Fin 3 → Fin 3 → ZMod h :=
  fun j i => ((∑ v : Fin heilbronnK,
    (digit D (labels j) i v (f i j v)).val * D.B ^ v.val : ℕ) : ZMod h)

end Problem355.MainDigitOrbitObstruction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.ConditionalBadTripleBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.ConditionalBadTripleBound

open OrbitSampling IntegerSampling LiftingProbability

def orbitTransposeEquiv (h : ℕ) (C : Fin 3 → Fin 3 → ZMod h) :
    MulAction.orbit (MainGroup h) C ≃ Section04Orbit.slOrbit (Matrix.transpose C) where
  toFun A := ⟨Matrix.transpose A.val, by
    obtain ⟨G, hG⟩ := A.property
    exact ⟨G, by rw [← hG, sl_action_transpose]⟩⟩
  invFun A := ⟨Matrix.transpose A.val, by
    obtain ⟨G, hG⟩ := A.property
    refine ⟨G, ?_⟩
    have ht := (sl_action_transpose h G C).trans hG
    exact funext fun i => funext fun j => congrFun (congrFun ht j) i⟩
  left_inv A := by apply Subtype.ext; exact Matrix.transpose_transpose _
  right_inv A := by apply Subtype.ext; exact Matrix.transpose_transpose _

end Problem355.ConditionalBadTripleBound

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.AveragedBadTripleBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.ConditionalBadTripleBound

open OrbitSampling IntegerSampling LiftingProbability DigitColumnLaw

def smallMass {Ω : Type*} [Fintype Ω]
    (h q L s : ℕ) [NeZero h] (shift : Fin 3 → ℤ)
    (C : Fin 3 → Fin 3 → ZMod h)
    (w : Ω → ℝ) (V : Ω → Finset (Fin 3 → ZMod q))
    (S : Finset (Fin 3 → Box (L * (h * q)) 3 shift)) (τ : ℤ) : ℝ := by
  classical
  exact ∑ x ∈ S.filter (fun x => |(integralMatrix x).det| ≤ τ),
    liftedMass (fun x i => residue h (x i)) (fun x i => residue q (x i))
      (orbitFinset (MainGroup h) C) w V s (L ^ 9) x

end Problem355.ConditionalBadTripleBound

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.PointLawBadTripleBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.IntegerPointLaw

open IntegerSampling ConditionalSamples ParameterSampling
open ConditionalBadTripleBound DigitColumnLaw OrbitSampling LiftingProbability
attribute [local instance] Classical.propDecidable

def projectedDistinctTriples (N : ℕ) :
    Finset (Fin 3 → Box N 3 (samplingShift N)) := by
  classical
  exact Finset.univ.filter fun x =>
    project (x 0) ≠ project (x 1) ∧ project (x 0) ≠ project (x 2) ∧
      project (x 1) ≠ project (x 2)

end Problem355.IntegerPointLaw

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.ActualPointLawTriples
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

attribute [local irreducible] Problem355.heilbronnT
  Problem355.heilbronnM

namespace Problem355.ActualPointLaw

open Parameters FiniteFieldLabels DigitColumnLaw OrbitSampling IntegerSampling
open scoped BigOperators

variable {r : ℕ} [Fact r.Prime]

def latentSmith (D : PrimeParameterData heilbronnK r)
    (z : Fin 3 → MainDigitLaw.Latent r) :
    PrimePowerData D.B heilbronnK
      (Matrix.transpose (fun j => MainDigitLaw.column D (z j))) :=
  MainDigitLaw.smith D (tripleEquiv z).1 (tripleEquiv z).2

def WeightedFiberBound (D : PrimeParameterData heilbronnK r)
    [Fact D.q.Prime] (A : AuxiliarySampling.Law D.q (D.h ^ 2)) (K : ℝ) : Prop := by
  classical
  letI : NeZero (D.B ^ heilbronnK) := ⟨pow_ne_zero _ D.base_prime.ne_zero⟩
  exact ∀ z : Fin 3 → MainDigitLaw.Latent r, ∀ t : ℤ, |t| ≤ (D.tau : ℤ) →
    (∑ x ∈ ((IntegerPointLaw.projectedDistinctTriples D.N).filter
      (fun x => (fun i => residue (D.B ^ heilbronnK) (x i)) ∈
        orbitFinset (MainGroup (D.B ^ heilbronnK))
          (fun j => MainDigitLaw.column D (z j)))).filter
      (fun x => (integralMatrix x).det = t),
      LiftingProbability.auxiliaryWeight D.q A.size A.weight A.sets
        (fun i => residue D.q (x i))) ≤
      K * (Real.log (2 * (D.N : ℝ))) ^ 2 * (D.N : ℝ) ^ 6 /
        (((D.B ^ (latentSmith D z).b : ℕ) : ℝ) ^ 2 *
          ((D.B ^ (latentSmith D z).e : ℕ) : ℝ) ^ 2)

end Problem355.ActualPointLaw

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.PrimitiveNormal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.PrimitiveNormal

open Matrix
open scoped Matrix

abbrev Vector := Fin 3 → ℤ

def coordGcd (v : Vector) : ℕ :=
  Int.gcd (Int.gcd (v 0) (v 1) : ℤ) (v 2)

def IsPrimitive (v : Vector) : Prop := coordGcd v = 1

def rowNormals (A : Matrix (Fin 3) (Fin 3) ℤ) : Fin 3 → Vector :=
  ![A 1 ⨯₃ A 2, A 2 ⨯₃ A 0, A 0 ⨯₃ A 1]

def toEuclidean (v : Vector) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (fun i => (v i : ℝ))

end Problem355.PrimitiveNormal

end OAI
end

section
-- module Solutions.OAIQW_Problem355.LatticeBox
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.LatticeBox

open Finset

def box (d N : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset (fun _ => Finset.Icc (-(N : ℤ)) N)

@[simp] theorem mem_box {d N : ℕ} {v : Fin d → ℤ} :
    v ∈ box d N ↔ ∀ i, |v i| ≤ (N : ℤ) := by
  simp [box, abs_le]

@[simp] theorem card_box (d N : ℕ) :
    (box d N).card = (2 * N + 1) ^ d := by
  simp [box, Int.card_Icc]
  congr 1
  omega

def realVector {d : ℕ} (v : Fin d → ℤ) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i => (v i : ℝ))

end Problem355.LatticeBox

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.AnisotropicGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.Anisotropic

open Matrix
open scoped Matrix
open PrimitiveNormal

abbrev IntVector := Fin 3 → ℤ

abbrev length (v : IntVector) : ℝ := ‖LatticeBox.realVector v‖

structure PlaneData (y : IntVector) where
  first : ℝ
  second : ℝ
  one_le_first : 1 ≤ first
  first_le_second : first ≤ second
  second_le_length : second ≤ length y
  first_le : ∀ v : IntVector, v ⬝ᵥ y = 0 → v ≠ 0 → first ≤ length v
  second_le : ∀ v w : IntVector, v ⬝ᵥ y = 0 → w ⬝ᵥ y = 0 →
    v ⨯₃ w ≠ 0 → second ≤ max (length v) (length w)
  shortest : ∃ z : IntVector, IsPrimitive z ∧ z ⬝ᵥ y = 0 ∧ length z = first
  large_count : ∀ (S : Finset IntVector) (R : ℝ), second ≤ R →
    (∀ v ∈ S, v ⬝ᵥ y = 0 ∧ length v ≤ R) →
    (S.card : ℝ) ≤ 9 * Real.pi * R ^ 2 / length y
  small_count : ∀ (S : Finset IntVector) (R : ℝ), first ≤ R → R < second →
    (∀ v ∈ S, v ⬝ᵥ y = 0 ∧ length v ≤ R) →
    (S.card : ℝ) ≤ 3 * R / first

end Problem355.Anisotropic

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.LatticeSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem355.LatticeSplit
open Module

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

def kernelProdEquiv (f : M →ₗ[R] R) (u : M) (hu : f u = 1) :
    M ≃ₗ[R] (LinearMap.ker f) × R where
  toFun x := (⟨x - f x • u, by simp [LinearMap.mem_ker, hu]⟩, f x)
  invFun p := (p.1 : M) + p.2 • u
  left_inv x := sub_add_cancel x (f x • u)
  right_inv p := by
    rcases p with ⟨⟨w, hw⟩, t⟩
    have hw' : f w = 0 := hw
    ext <;> simp [hw', hu]
  map_add' x y := by
    apply Prod.ext
    · apply Subtype.ext
      change x + y - f (x + y) • u = (x - f x • u) + (y - f y • u)
      simp only [map_add, add_smul]
      abel
    · exact f.map_add x y
  map_smul' a x := by
    ext <;> simp [smul_sub, smul_smul]

@[simp] theorem kernelProdEquiv_snd (f : M →ₗ[R] R) (u : M) (hu : f u = 1)
    (x : M) : (kernelProdEquiv f u hu x).2 = f x := rfl

@[simp] theorem kernelProdEquiv_fst_coe (f : M →ₗ[R] R) (u : M) (hu : f u = 1)
    (x : M) : ((kernelProdEquiv f u hu x).1 : M) = x - f x • u := rfl

@[simp] theorem kernelProdEquiv_symm_apply (f : M →ₗ[R] R) (u : M)
    (hu : f u = 1) (p : LinearMap.ker f × R) :
    (kernelProdEquiv f u hu).symm p = (p.1 : M) + p.2 • u := rfl

noncomputable def extendKernelBasis {ι : Type*} (f : M →ₗ[R] R) (u : M) (hu : f u = 1)
    (b : Basis ι R (LinearMap.ker f)) : Basis (ι ⊕ Unit) R M :=
  (b.prod (Basis.singleton Unit R)).map (kernelProdEquiv f u hu).symm

@[simp] theorem extendKernelBasis_inl {ι : Type*} (f : M →ₗ[R] R)
    (u : M) (hu : f u = 1) (b : Basis ι R (LinearMap.ker f)) (i : ι) :
    extendKernelBasis f u hu b (Sum.inl i) = (b i : M) := by
  simp [extendKernelBasis]

@[simp] theorem extendKernelBasis_inr {ι : Type*} (f : M →ₗ[R] R)
    (u : M) (hu : f u = 1) (b : Basis ι R (LinearMap.ker f)) (i : Unit) :
    extendKernelBasis f u hu b (Sum.inr i) = u := by
  simp [extendKernelBasis]

@[simp] theorem extendKernelBasis_repr_inr {ι : Type*} (f : M →ₗ[R] R)
    (u : M) (hu : f u = 1) (b : Basis ι R (LinearMap.ker f))
    (x : M) (i : Unit) :
    (extendKernelBasis f u hu b).repr x (Sum.inr i) = f x := by
  simp [extendKernelBasis]

def restrictedKernelEquiv (L : Submodule R M) (f : M →ₗ[R] R) :
    LinearMap.ker (f.comp L.subtype) ≃ₗ[R] ↥(L ⊓ LinearMap.ker f) where
  toFun x := ⟨x.1.1, x.1.2, x.2⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem restrictedKernelEquiv_apply_coe
    (L : Submodule R M) (f : M →ₗ[R] R)
    (x : LinearMap.ker (f.comp L.subtype)) :
    (restrictedKernelEquiv L f x : M) = x.1 := rfl

variable {A : Type*} [AddCommGroup A]

def divideIntFunctional (f : A →ₗ[ℤ] ℤ) (g : ℤ) (hdiv : ∀ x, g ∣ f x) :
    A →ₗ[ℤ] ℤ where
  toFun x := f x / g
  map_add' x y := by
    simp only [map_add]
    exact Int.add_ediv_of_dvd_left (hdiv x)
  map_smul' a x := by
    simp only [map_smul, smul_eq_mul, RingHom.id_apply]
    exact Int.mul_ediv_assoc a (hdiv x)

@[simp] theorem divideIntFunctional_apply (f : A →ₗ[ℤ] ℤ) (g : ℤ)
    (hdiv : ∀ x, g ∣ f x) (x : A) :
    divideIntFunctional f g hdiv x = f x / g := rfl

def integerKernelProdEquiv (f : A →ₗ[ℤ] ℤ) (g : ℤ) (hg : g ≠ 0)
    (hdiv : ∀ x, g ∣ f x) (u : A) (hu : f u = g) :
    A ≃ₗ[ℤ] (LinearMap.ker f) × ℤ where
  toFun x := (⟨x - (f x / g) • u, by
    simp only [LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul, hu]
    exact sub_eq_zero.mpr (Int.ediv_mul_cancel (hdiv x)).symm⟩, f x / g)
  invFun p := (p.1 : A) + p.2 • u
  left_inv x := sub_add_cancel x ((f x / g) • u)
  right_inv p := by
    rcases p with ⟨⟨w, hw⟩, t⟩
    have hw' : f w = 0 := hw
    have ht : f (w + t • u) / g = t := by
      simp only [map_add, map_smul, hw', hu, smul_eq_mul, zero_add]
      rw [mul_comm, Int.mul_ediv_cancel_left _ hg]
    apply Prod.ext
    · apply Subtype.ext
      change w + t • u - (f (w + t • u) / g) • u = w
      rw [ht]
      abel
    · exact ht
  map_add' x y := by
    have h := (divideIntFunctional f g hdiv).map_add x y
    change (f (x + y) / g) = (f x / g) + (f y / g) at h
    apply Prod.ext
    · apply Subtype.ext
      change x + y - (f (x + y) / g) • u =
        (x - (f x / g) • u) + (y - (f y / g) • u)
      rw [h, add_smul]
      abel
    · exact h
  map_smul' a x := by
    have h := (divideIntFunctional f g hdiv).map_smul a x
    change (f (a • x) / g) = a * (f x / g) at h
    apply Prod.ext
    · apply Subtype.ext
      change a • x - (f (a • x) / g) • u = a • (x - (f x / g) • u)
      rw [h, smul_sub, smul_smul]
    · exact h

@[simp] theorem integerKernelProdEquiv_snd
    (f : A →ₗ[ℤ] ℤ) (g : ℤ) (hg : g ≠ 0) (hdiv : ∀ x, g ∣ f x)
    (u : A) (hu : f u = g) (x : A) :
    (integerKernelProdEquiv f g hg hdiv u hu x).2 = f x / g := rfl

@[simp] theorem integerKernelProdEquiv_fst_coe
    (f : A →ₗ[ℤ] ℤ) (g : ℤ) (hg : g ≠ 0) (hdiv : ∀ x, g ∣ f x)
    (u : A) (hu : f u = g) (x : A) :
    ((integerKernelProdEquiv f g hg hdiv u hu x).1 : A) = x - (f x / g) • u := rfl

@[simp] theorem integerKernelProdEquiv_symm_apply
    (f : A →ₗ[ℤ] ℤ) (g : ℤ) (hg : g ≠ 0) (hdiv : ∀ x, g ∣ f x)
    (u : A) (hu : f u = g) (p : LinearMap.ker f × ℤ) :
    (integerKernelProdEquiv f g hg hdiv u hu).symm p = (p.1 : A) + p.2 • u := rfl

noncomputable def extendIntegerKernelBasis {ι : Type*}
    (f : A →ₗ[ℤ] ℤ) (g : ℤ) (hg : g ≠ 0) (hdiv : ∀ x, g ∣ f x)
    (u : A) (hu : f u = g) (b : Basis ι ℤ (LinearMap.ker f)) :
    Basis (ι ⊕ Unit) ℤ A :=
  (b.prod (Basis.singleton Unit ℤ)).map (integerKernelProdEquiv f g hg hdiv u hu).symm

@[simp] theorem extendIntegerKernelBasis_inl {ι : Type*}
    (f : A →ₗ[ℤ] ℤ) (g : ℤ) (hg : g ≠ 0) (hdiv : ∀ x, g ∣ f x)
    (u : A) (hu : f u = g) (b : Basis ι ℤ (LinearMap.ker f)) (i : ι) :
    extendIntegerKernelBasis f g hg hdiv u hu b (Sum.inl i) = (b i : A) := by
  simp [extendIntegerKernelBasis]

@[simp] theorem extendIntegerKernelBasis_inr {ι : Type*}
    (f : A →ₗ[ℤ] ℤ) (g : ℤ) (hg : g ≠ 0) (hdiv : ∀ x, g ∣ f x)
    (u : A) (hu : f u = g) (b : Basis ι ℤ (LinearMap.ker f)) (i : Unit) :
    extendIntegerKernelBasis f g hg hdiv u hu b (Sum.inr i) = u := by
  simp [extendIntegerKernelBasis]

@[simp] theorem extendIntegerKernelBasis_repr_inr {ι : Type*}
    (f : A →ₗ[ℤ] ℤ) (g : ℤ) (hg : g ≠ 0) (hdiv : ∀ x, g ∣ f x)
    (u : A) (hu : f u = g) (b : Basis ι ℤ (LinearMap.ker f))
    (x : A) (i : Unit) :
    (extendIntegerKernelBasis f g hg hdiv u hu b).repr x (Sum.inr i) = f x / g := by
  simp [extendIntegerKernelBasis]

theorem finrank_kernel_add_one [Module.Free ℤ A] [Module.Finite ℤ A]
    (f : A →ₗ[ℤ] ℤ) (g : ℤ) (hg : g ≠ 0) (hdiv : ∀ x, g ∣ f x)
    (u : A) (hu : f u = g) :
    Module.finrank ℤ (LinearMap.ker f) + 1 = Module.finrank ℤ A := by
  have h := (integerKernelProdEquiv f g hg hdiv u hu).finrank_eq
  simpa only [Module.finrank_prod, Module.finrank_self] using h.symm

noncomputable def integerKernelBasisFin [Module.Free ℤ A] [Module.Finite ℤ A]
    (f : A →ₗ[ℤ] ℤ) (g : ℤ) (hg : g ≠ 0) (hdiv : ∀ x, g ∣ f x)
    (u : A) (hu : f u = g) (n : ℕ) (hdim : Module.finrank ℤ A = n + 1) :
    Basis (Fin n) ℤ (LinearMap.ker f) := by
  apply Module.finBasisOfFinrankEq
  have h := finrank_kernel_add_one f g hg hdiv u hu
  omega

end Problem355.LatticeSplit

end OAI
end

section
-- module Solutions.OAIQW_Problem355.IntegralPlaneLattice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.IntegralPlaneLattice

open Module Matrix

abbrev Ambient := EuclideanSpace ℝ (Fin 3)

def stdBasis : Basis (Fin 3) ℝ Ambient := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis

def standardLattice : Submodule ℤ Ambient := Submodule.span ℤ (Set.range stdBasis)

instance instDiscreteTopologySubtypeAmbientMemSubmoduleIntStandardLattice : DiscreteTopology standardLattice := by
  unfold standardLattice
  infer_instance

def castVec (x : Fin 3 → ℤ) : Ambient := WithLp.toLp 2 (fun i => (x i : ℝ))

@[simp] lemma castVec_apply (x : Fin 3 → ℤ) (i : Fin 3) : castVec x i = (x i : ℝ) := rfl

lemma stdBasis_repr (v : Ambient) (i : Fin 3) : stdBasis.repr v i = v i := rfl

lemma mem_standardLattice (v : Ambient) :
    v ∈ standardLattice ↔ ∀ i, ∃ z : ℤ, (z : ℝ) = v i := by
  change v ∈ Submodule.span ℤ (Set.range stdBasis) ↔ _
  rw [stdBasis.mem_span_iff_repr_mem ℤ v]
  simp [stdBasis_repr]

lemma castVec_mem (x : Fin 3 → ℤ) : castVec x ∈ standardLattice :=
  (mem_standardLattice _).mpr (fun i => ⟨x i, rfl⟩)

def realDot (x : Fin 3 → ℤ) : Ambient →ₗ[ℝ] ℝ where
  toFun v := ∑ i, (x i : ℝ) * v i
  map_add' v w := by simp [Finset.sum_add_distrib, mul_add]
  map_smul' t v := by simp [Finset.mul_sum, mul_left_comm]

@[simp] lemma realDot_apply (x : Fin 3 → ℤ) (v : Ambient) :
    realDot x v = ∑ i, (x i : ℝ) * v i := rfl

@[simp] lemma realDot_castVec (x z : Fin 3 → ℤ) :
    realDot x (castVec z) = (x ⬝ᵥ z : ℤ) := by
  simp [realDot, castVec, dotProduct]

def plane (x : Fin 3 → ℤ) : Submodule ℝ Ambient := (realDot x).ker

def lattice (x : Fin 3 → ℤ) : Submodule ℤ (plane x) :=
  standardLattice.comap ((plane x).subtype.restrictScalars ℤ)

instance lattice_discrete (x : Fin 3 → ℤ) : DiscreteTopology (lattice x) := by
  let : DiscreteTopology (standardLattice : Set Ambient) :=
    inferInstanceAs (DiscreteTopology standardLattice)
  exact DiscreteTopology.preimage_of_continuous_injective (standardLattice : Set Ambient)
    (LinearMap.continuous_of_finiteDimensional (plane x).subtype) (Submodule.injective_subtype _)

lemma realDot_stdBasis (x : Fin 3 → ℤ) (i : Fin 3) : realDot x (stdBasis i) = (x i : ℝ) := by
  simp [realDot, stdBasis, EuclideanSpace.basisFun_apply]

def projection (x z : Fin 3 → ℤ) (hz : x ⬝ᵥ z = 1) : Ambient →ₗ[ℝ] plane x :=
  (LinearMap.id - (realDot x).smulRight (castVec z)).codRestrict (plane x) (by
    intro v
    change realDot x (v - realDot x v • castVec z) = 0
    rw [map_sub, map_smul, realDot_castVec, hz]
    simp)

lemma projection_on_plane (x z : Fin 3 → ℤ) (hz : x ⬝ᵥ z = 1) (v : plane x) :
    projection x z hz v = v := by
  apply Subtype.ext
  change (v : Ambient) - realDot x v • castVec z = v
  have hv : realDot x v = 0 := v.property
  simp [hv]

lemma projection_basis_mem (x z : Fin 3 → ℤ) (hz : x ⬝ᵥ z = 1) (i : Fin 3) :
    projection x z hz (stdBasis i) ∈ lattice x := by
  change stdBasis i - realDot x (stdBasis i) • castVec z ∈ standardLattice
  rw [realDot_stdBasis]
  apply standardLattice.sub_mem
  · exact Submodule.subset_span ⟨i, rfl⟩
  · rw [Int.cast_smul_eq_zsmul ℝ]
    exact standardLattice.smul_mem _ (castVec_mem z)

lemma lattice_spans (x z : Fin 3 → ℤ) (hz : x ⬝ᵥ z = 1) :
    Submodule.span ℝ (lattice x : Set (plane x)) = ⊤ := by
  apply top_unique
  intro v hv
  rw [← projection_on_plane x z hz v, ← stdBasis.sum_repr (v : Ambient), map_sum]
  apply Submodule.sum_mem
  intro i hi
  rw [map_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (projection_basis_mem x z hz i))

lemma isZLattice (x z : Fin 3 → ℤ) (hz : x ⬝ᵥ z = 1) : IsZLattice ℝ (lattice x) :=
  ⟨lattice_spans x z hz⟩

lemma plane_finrank (x z : Fin 3 → ℤ) (hz : x ⬝ᵥ z = 1) :
    finrank ℝ (plane x) = 2 := by
  have hn : realDot x ≠ 0 := by
    intro h
    have he := LinearMap.congr_fun h (castVec z)
    change realDot x (castVec z) = 0 at he
    rw [realDot_castVec, hz] at he
    norm_num at he
  have h := Module.Dual.finrank_ker_add_one_of_ne_zero hn
  change finrank ℝ (plane x) + 1 = finrank ℝ Ambient at h
  norm_num [Ambient] at h
  omega

def integerDot (x : Fin 3 → ℤ) : (Fin 3 → ℤ) →ₗ[ℤ] ℤ where
  toFun v := x ⬝ᵥ v
  map_add' v w := by simp [dotProduct, mul_add, Finset.sum_add_distrib]
  map_smul' t v := by simp [dotProduct, Finset.mul_sum, mul_left_comm]

def integerPlane (x : Fin 3 → ℤ) : Submodule ℤ (Fin 3 → ℤ) := (integerDot x).ker

def kernelMap (x : Fin 3 → ℤ) : integerPlane x →ₗ[ℤ] lattice x where
  toFun v := ⟨⟨castVec v, by
    change realDot x (castVec v) = 0
    rw [realDot_castVec]
    have hv : x ⬝ᵥ (v : Fin 3 → ℤ) = 0 := v.property
    exact_mod_cast hv⟩, castVec_mem v⟩
  map_add' v w := by
    apply Subtype.ext
    apply Subtype.ext
    ext i
    simp [castVec]
  map_smul' t v := by
    apply Subtype.ext
    apply Subtype.ext
    ext i
    simp [castVec]

lemma kernelMap_injective (x : Fin 3 → ℤ) : Function.Injective (kernelMap x) := by
  intro u v h
  apply Subtype.ext
  funext i
  have he := congrArg (fun w : lattice x => ((w : plane x) : Ambient) i) h
  change (u.val i : ℝ) = (v.val i : ℝ) at he
  exact_mod_cast he

lemma kernelMap_surjective (x : Fin 3 → ℤ) : Function.Surjective (kernelMap x) := by
  intro y
  have hy : ((y : plane x) : Ambient) ∈ standardLattice := y.property
  choose z hz using (mem_standardLattice _).mp hy
  have he : castVec z = ((y : plane x) : Ambient) := by
    ext i
    exact hz i
  have hzker : z ∈ integerPlane x := by
    have hyker : realDot x ((y : plane x) : Ambient) = 0 := (y : plane x).property
    rw [← he, realDot_castVec] at hyker
    change x ⬝ᵥ z = 0
    exact_mod_cast hyker
  refine ⟨⟨z, hzker⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact he

def kernelEquiv (x : Fin 3 → ℤ) : integerPlane x ≃ₗ[ℤ] lattice x :=
  LinearEquiv.ofBijective (kernelMap x) ⟨kernelMap_injective x, kernelMap_surjective x⟩

def castLinear : (Fin 3 → ℤ) →ₗ[ℤ] Ambient where
  toFun := castVec
  map_add' v w := by ext i; simp [castVec]
  map_smul' t v := by ext i; simp [castVec]

def realLattice (L : Submodule ℤ (Fin 3 → ℤ)) : Submodule ℤ Ambient := L.map castLinear

lemma realLattice_le_standard (L : Submodule ℤ (Fin 3 → ℤ)) :
    realLattice L ≤ standardLattice := by
  rintro y ⟨v, hv, rfl⟩
  exact castVec_mem v

instance realLattice_discrete (L : Submodule ℤ (Fin 3 → ℤ)) :
    DiscreteTopology (realLattice L) := by
  exact DiscreteTopology.of_subset (inferInstanceAs (DiscreteTopology standardLattice))
    (realLattice_le_standard L)

def latticeIn (x : Fin 3 → ℤ) (L : Submodule ℤ (Fin 3 → ℤ)) :
    Submodule ℤ (plane x) := (realLattice L).comap ((plane x).subtype.restrictScalars ℤ)

instance latticeIn_discrete (x : Fin 3 → ℤ) (L : Submodule ℤ (Fin 3 → ℤ)) :
    DiscreteTopology (latticeIn x L) := by
  let : DiscreteTopology (realLattice L : Set Ambient) :=
    inferInstanceAs (DiscreteTopology (realLattice L))
  exact DiscreteTopology.preimage_of_continuous_injective (realLattice L : Set Ambient)
    (LinearMap.continuous_of_finiteDimensional (plane x).subtype) (Submodule.injective_subtype _)

lemma latticeIn_spans (x z : Fin 3 → ℤ) (hz : x ⬝ᵥ z = 1)
    (L : Submodule ℤ (Fin 3 → ℤ)) (E : ℤ) (hE : E ≠ 0)
    (hL : ∀ v : Fin 3 → ℤ, E • v ∈ L) :
    Submodule.span ℝ (latticeIn x L : Set (plane x)) = ⊤ := by
  apply top_unique
  rw [← lattice_spans x z hz]
  apply Submodule.span_le.mpr
  intro v hv
  obtain ⟨u, hu⟩ := kernelMap_surjective x ⟨v, hv⟩
  have hm : E • v ∈ latticeIn x L := by
    change (E • (v : Ambient)) ∈ realLattice L
    refine ⟨E • u.val, hL u.val, ?_⟩
    rw [map_smul]
    have he := congrArg (fun w : lattice x => ((w : plane x) : Ambient)) hu
    change castVec u.val = (v : Ambient) at he
    exact congrArg (fun a : Ambient => E • a) he
  have hs : (E : ℝ) • v ∈ Submodule.span ℝ (latticeIn x L : Set (plane x)) := by
    rw [Int.cast_smul_eq_zsmul ℝ]
    exact Submodule.subset_span hm
  exact (Submodule.smul_mem_iff _ (by exact_mod_cast hE : (E : ℝ) ≠ 0)).mp hs

lemma latticeIn_isZLattice (x z : Fin 3 → ℤ) (hz : x ⬝ᵥ z = 1)
    (L : Submodule ℤ (Fin 3 → ℤ)) (E : ℤ) (hE : E ≠ 0)
    (hL : ∀ v : Fin 3 → ℤ, E • v ∈ L) : IsZLattice ℝ (latticeIn x L) :=
  ⟨latticeIn_spans x z hz L E hE hL⟩

lemma latticeIn_finrank (x z : Fin 3 → ℤ) (hz : x ⬝ᵥ z = 1)
    (L : Submodule ℤ (Fin 3 → ℤ)) (E : ℤ) (hE : E ≠ 0)
    (hL : ∀ v : Fin 3 → ℤ, E • v ∈ L) : finrank ℤ (latticeIn x L) = 2 := by
  let := latticeIn_isZLattice x z hz L E hE hL
  rw [ZLattice.rank ℝ (latticeIn x L), plane_finrank x z hz]

def basisIn (x z : Fin 3 → ℤ) (hz : x ⬝ᵥ z = 1)
    (L : Submodule ℤ (Fin 3 → ℤ)) (E : ℤ) (hE : E ≠ 0)
    (hL : ∀ v : Fin 3 → ℤ, E • v ∈ L) : Basis (Fin 2) ℤ (latticeIn x L) := by
  letI := latticeIn_isZLattice x z hz L E hE hL
  exact (Module.finBasis ℤ (latticeIn x L)).reindex
    (finCongr (latticeIn_finrank x z hz L E hE hL))

def integerPlaneIn (x : Fin 3 → ℤ) (L : Submodule ℤ (Fin 3 → ℤ)) :
    Submodule ℤ (Fin 3 → ℤ) := L ⊓ integerPlane x

def kernelMapIn (x : Fin 3 → ℤ) (L : Submodule ℤ (Fin 3 → ℤ)) :
    integerPlaneIn x L →ₗ[ℤ] latticeIn x L where
  toFun v := ⟨⟨castVec v, by
    change realDot x (castVec v) = 0
    rw [realDot_castVec]
    have hv : x ⬝ᵥ (v : Fin 3 → ℤ) = 0 := v.property.2
    exact_mod_cast hv⟩, ⟨v.val, v.property.1, rfl⟩⟩
  map_add' v w := by
    apply Subtype.ext
    apply Subtype.ext
    ext i
    simp [castVec]
  map_smul' t v := by
    apply Subtype.ext
    apply Subtype.ext
    ext i
    simp [castVec]

lemma kernelMapIn_injective (x : Fin 3 → ℤ) (L : Submodule ℤ (Fin 3 → ℤ)) :
    Function.Injective (kernelMapIn x L) := by
  intro u v h
  apply Subtype.ext
  funext i
  have he := congrArg (fun w : latticeIn x L => ((w : plane x) : Ambient) i) h
  change (u.val i : ℝ) = (v.val i : ℝ) at he
  exact_mod_cast he

lemma kernelMapIn_surjective (x : Fin 3 → ℤ) (L : Submodule ℤ (Fin 3 → ℤ)) :
    Function.Surjective (kernelMapIn x L) := by
  intro y
  obtain ⟨v, hv, he⟩ := y.property
  have hvker : v ∈ integerPlane x := by
    have hyker : realDot x ((y : plane x) : Ambient) = 0 := (y : plane x).property
    change castVec v = ((y : plane x) : Ambient) at he
    rw [← he, realDot_castVec] at hyker
    change x ⬝ᵥ v = 0
    exact_mod_cast hyker
  refine ⟨⟨v, hv, hvker⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact he

def kernelEquivIn (x : Fin 3 → ℤ) (L : Submodule ℤ (Fin 3 → ℤ)) :
    integerPlaneIn x L ≃ₗ[ℤ] latticeIn x L :=
  LinearEquiv.ofBijective (kernelMapIn x L)
    ⟨kernelMapIn_injective x L, kernelMapIn_surjective x L⟩

def integerBasisIn (x z : Fin 3 → ℤ) (hz : x ⬝ᵥ z = 1)
    (L : Submodule ℤ (Fin 3 → ℤ)) (E : ℤ) (hE : E ≠ 0)
    (hL : ∀ v : Fin 3 → ℤ, E • v ∈ L) :
    Basis (Fin 2) ℤ (integerPlaneIn x L) :=
  (basisIn x z hz L E hE hL).map (kernelEquivIn x L).symm

end Problem355.IntegralPlaneLattice

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.SuccessiveVectors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.SuccessiveVectors

variable {E : Type*} [NormedAddCommGroup E] [ProperSpace E]

theorem exists_shortest_with_property (L : Submodule ℤ E) [DiscreteTopology L]
    (P : E → Prop) (hP : ∃ v ∈ L, P v) :
    ∃ v ∈ L, P v ∧ ∀ w ∈ L, P w → ‖v‖ ≤ ‖w‖ := by
  classical
  obtain ⟨x, hxL, hxP⟩ := hP
  have : DiscreteTopology L.toAddSubgroup := inferInstanceAs (DiscreteTopology L)
  have hf : (Metric.closedBall (0 : E) ‖x‖ ∩ (L : Set E)).Finite :=
    Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
      Metric.isBounded_closedBall (AddSubgroup.isClosed_of_discrete (H := L.toAddSubgroup))
  let S : Set E := {v | v ∈ L ∧ P v ∧ ‖v‖ ≤ ‖x‖}
  have hSfin : S.Finite := hf.subset (by
    intro v hv
    exact ⟨by simpa using hv.2.2, hv.1⟩)
  obtain ⟨v, hv, hmin⟩ := Set.exists_min_image S norm hSfin ⟨x, hxL, hxP, le_rfl⟩
  refine ⟨v, hv.1, hv.2.1, ?_⟩
  intro w hwL hwP
  by_cases hw : ‖w‖ ≤ ‖x‖
  · exact hmin w ⟨hwL, hwP, hw⟩
  · exact hv.2.2.trans (le_of_not_ge hw)

variable [NormedSpace ℝ E]

theorem exists_shortest_outside (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] (W : Submodule ℝ E) (hW : W ≠ ⊤) :
    ∃ v ∈ L, v ∉ W ∧ 0 < ‖v‖ ∧
      ∀ w ∈ L, w ∉ W → ‖v‖ ≤ ‖w‖ := by
  have hex : ∃ v ∈ L, v ∉ W := by
    by_contra h
    have hle : Submodule.span ℝ (L : Set E) ≤ W := by
      apply Submodule.span_le.mpr
      intro v hv
      by_contra hvW
      exact h ⟨v, hv, hvW⟩
    rw [IsZLattice.span_top] at hle
    exact hW (top_le_iff.mp hle)
  obtain ⟨v, hvL, hvW, hmin⟩ := exists_shortest_with_property L (fun v => v ∉ W) hex
  refine ⟨v, hvL, hvW, norm_pos_iff.mpr ?_, hmin⟩
  intro hv0
  exact hvW (hv0 ▸ W.zero_mem)

def earlier {n : ℕ} (v : Fin n → E) (i : Fin n) : Set E :=
  v '' {j | j < i}

omit [NormedAddCommGroup E] [ProperSpace E] [NormedSpace ℝ E] in
lemma earlier_snoc_castSucc {n : ℕ} (v : Fin n → E) (x : E) (i : Fin n) :
    earlier (Fin.snoc v x) i.castSucc = earlier v i := by
  ext y
  constructor
  · rintro ⟨j, hj, rfl⟩
    revert hj
    refine Fin.lastCases ?_ (fun k hj => ?_) j
    · intro hj
      exact (not_lt_of_ge (Fin.le_last _) hj).elim
    · exact ⟨k, hj, by simp⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j.castSucc, hj, by simp⟩

omit [NormedAddCommGroup E] [ProperSpace E] [NormedSpace ℝ E] in
lemma earlier_snoc_last {n : ℕ} (v : Fin n → E) (x : E) :
    earlier (Fin.snoc v x) (Fin.last n) = Set.range v := by
  ext y
  constructor
  · rintro ⟨j, hj, rfl⟩
    revert hj
    refine Fin.lastCases ?_ (fun k _ => ?_) j
    · intro hj
      simp at hj
    · exact ⟨k, by simp⟩
  · rintro ⟨j, rfl⟩
    exact ⟨j.castSucc, Fin.castSucc_lt_last j, by simp⟩

structure IsSuccessive (L : Submodule ℤ E) {n : ℕ} (v : Fin n → E) : Prop where
  mem_lattice : ∀ i, v i ∈ L
  independent : LinearIndependent ℝ v
  minimal : ∀ i, ∀ w ∈ L, w ∉ Submodule.span ℝ (earlier v i) → ‖v i‖ ≤ ‖w‖

theorem exists_successive (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] [FiniteDimensional ℝ E] (n : ℕ)
    (hn : n ≤ Module.finrank ℝ E) :
    ∃ v : Fin n → E, IsSuccessive L v := by
  induction n with
  | zero =>
    refine ⟨Fin.elim0, ?_⟩
    exact ⟨by intro i; exact i.elim0, linearIndependent_empty_type, by intro i; exact i.elim0⟩
  | succ n ih =>
    obtain ⟨v, hv⟩ := ih (Nat.le_of_succ_le hn)
    have hW : Submodule.span ℝ (Set.range v) ≠ ⊤ := by
      intro htop
      have hdim := finrank_span_eq_card hv.independent
      rw [htop] at hdim
      have hdim' : Module.finrank ℝ E = n := by simpa using hdim
      omega
    obtain ⟨x, hxL, hxW, _, hxmin⟩ := exists_shortest_outside L _ hW
    refine ⟨Fin.snoc v x, ?_⟩
    refine ⟨?_, linearIndependent_finSnoc.mpr ⟨hv.independent, hxW⟩, ?_⟩
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hxL
      · simpa using hv.mem_lattice j
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [earlier_snoc_last, Fin.snoc_last] using hxmin
      · simpa only [earlier_snoc_castSucc, Fin.snoc_castSucc] using hv.minimal j

end Problem355.SuccessiveVectors

end OAI
end

section
-- module Solutions.OAIQW_Problem355.PlaneCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.PlaneCount

open MeasureTheory

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in

theorem exists_successive_plane_basis
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hdim : Module.finrank ℝ E = 2) :
    ∃ b : Module.Basis (Fin 2) ℝ E,
      (∀ i, b i ∈ L) ∧
      (∀ u ∈ L, u ≠ 0 → ‖b 0‖ ≤ ‖u‖) ∧
      (∀ u ∈ L, u ∉ Submodule.span ℝ {b 0} → ‖b 1‖ ≤ ‖u‖) := by
  obtain ⟨v, hv⟩ := SuccessiveVectors.exists_successive L 2 (by omega)
  let b := basisOfLinearIndependentOfCardEqFinrank' v hv.independent (by simp [hdim])
  have hb : (b : Fin 2 → E) = v := coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _
  have hzero : SuccessiveVectors.earlier v 0 = ∅ := by
    simp [SuccessiveVectors.earlier]
  have hone : SuccessiveVectors.earlier v 1 = {v 0} := by
    simp [SuccessiveVectors.earlier]
  refine ⟨b, ?_, ?_, ?_⟩
  · simpa only [hb] using hv.mem_lattice
  · intro u hu hne
    rw [hb]
    apply hv.minimal 0 u hu
    simpa only [hzero, Submodule.span_empty, Submodule.mem_bot] using hne
  · intro u hu hout
    rw [hb] at hout ⊢
    apply hv.minimal 1 u hu
    simpa only [hone] using hout

end Problem355.PlaneCount

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.ShortestIntegralVector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.IntegralMinima

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

def toEuclidean (x : ι → ℤ) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i => (x i : ℝ))

def normSq (x : ι → ℤ) : ℕ := ∑ i, (x i).natAbs ^ 2

end Problem355.IntegralMinima

end OAI
end

section
-- module Solutions.OAIQW_Problem355.IntegerPlaneEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.IntegerPlaneEstimates

open Module Matrix IntegralPlaneLattice

abbrev Vec := Fin 3 → ℤ

@[simp] lemma castVec_zero : castVec (0 : Vec) = 0 := by
  ext i
  simp [castVec]

def toLattice (y v : Vec) (hv : y ⬝ᵥ v = 0) : lattice y :=
  kernelMap y ⟨v, hv⟩

@[simp] lemma toLattice_coe (y v : Vec) (hv : y ⬝ᵥ v = 0) :
    ((toLattice y v hv : plane y) : Ambient) = castVec v := rfl

@[simp] lemma norm_toLattice (y v : Vec) (hv : y ⬝ᵥ v = 0) :
    ‖(toLattice y v hv : plane y)‖ = ‖LatticeBox.realVector v‖ := rfl

lemma toLattice_injective (y v w : Vec) (hv : y ⬝ᵥ v = 0) (hw : y ⬝ᵥ w = 0)
    (h : toLattice y v hv = toLattice y w hw) : v = w := by
  exact congrArg Subtype.val (kernelMap_injective y h)

def liftFinset (y : Vec) (S : Finset Vec) (hS : ∀ v ∈ S, y ⬝ᵥ v = 0) :
    Finset (lattice y) :=
  S.attach.map ⟨fun v : {v // v ∈ S} => toLattice y v (hS v v.property), by
    intro v w h
    apply Subtype.ext
    exact toLattice_injective y v w _ _ h⟩

@[simp] lemma card_liftFinset (y : Vec) (S : Finset Vec)
    (hS : ∀ v ∈ S, y ⬝ᵥ v = 0) :
    (liftFinset y S hS).card = S.card := by simp [liftFinset]

def successiveBasis (y z : Vec) (hz : y ⬝ᵥ z = 1) : Basis (Fin 2) ℝ (plane y) := by
  letI := isZLattice y z hz
  exact Classical.choose (PlaneCount.exists_successive_plane_basis (lattice y)
    (plane_finrank y z hz))

def first (y z : Vec) (hz : y ⬝ᵥ z = 1) : ℝ := ‖successiveBasis y z hz 0‖
def second (y z : Vec) (hz : y ⬝ᵥ z = 1) : ℝ := ‖successiveBasis y z hz 1‖

def fromLattice (y : Vec) (v : lattice y) : Vec :=
  ((kernelEquiv y).symm v : integerPlane y)

end Problem355.IntegerPlaneEstimates

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.DeterminantFibers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.DeterminantFibers

open scoped Matrix
open LatticeBox

@[simp] theorem realVector_sub {d : ℕ} (u v : Fin d → ℤ) :
    realVector (u - v) = realVector u - realVector v := by
  ext i
  simp [realVector]

end Problem355.DeterminantFibers

end OAI
end

section
-- module Solutions.OAIQW_Problem355.PlaneFiberAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.PlaneFiberAssembly

open scoped Matrix
open LatticeBox

abbrev Vec := Fin 3 → ℤ
abbrev Triple := Vec × Vec × Vec

end Problem355.PlaneFiberAssembly

end OAI
end

section
-- module Solutions.OAIQW_Problem355.AnisotropicCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.Anisotropic

open Matrix
open scoped Matrix
open PrimitiveNormal

abbrev Triple := PlaneFiberAssembly.Triple

end Problem355.Anisotropic

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.WeightedZeroPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.WeightedZeroPartition

open scoped BigOperators
attribute [local instance] Classical.propDecidable

def columnPair : Fin 3 → Fin 3 × Fin 3 := ![(0, 1), (0, 2), (1, 2)]

def EqualPair {F : Type*} (v : Fin 3 → (Fin 3 → F)) (p : Fin 3) : Prop :=
  v (columnPair p).1 = v (columnPair p).2

abbrev IntMatrix := Matrix (Fin 3) (Fin 3) ℤ

def residueColumns (q : ℕ) (A : IntMatrix) : Fin 3 → (Fin 3 → ZMod q) :=
  fun j i => (A i j : ZMod q)

def Exceptional (q : ℕ) (x : Fin 3 → ℤ) (p : Fin 3) : Prop :=
  (fun i => (x i : ZMod q)) ∈ Submodule.span (ZMod q)
    {Pi.single (columnPair p).1 (1 : ZMod q) - Pi.single (columnPair p).2 1}

end Problem355.WeightedZeroPartition

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.AuxiliaryThreeCase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.AuxiliaryThreeCase

open WeightedZeroPartition
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def ExceptionalVector {F : Type*} [Field F] (x : Fin 3 → F) (p : Fin 3) : Prop :=
  x ∈ Submodule.span F
    {Pi.single (columnPair p).1 (1 : F) - Pi.single (columnPair p).2 1}

@[simp] theorem exceptionalVector_reduction (q : ℕ) [Fact q.Prime]
    (x : Fin 3 → ℤ) (p : Fin 3) :
    ExceptionalVector (fun i => (x i : ZMod q)) p ↔ Exceptional q x p := Iff.rfl

end Problem355.AuxiliaryThreeCase

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.PlaneRowTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.PlaneRowTransport

open Matrix IntegralPlaneLattice

abbrev IntMatrix := Matrix (Fin 3) (Fin 3) ℤ

abbrev PlaneMatrices (x : Fin 3 → ℤ) := {A : IntMatrix // A *ᵥ x = 0}

def rows (x : Fin 3 → ℤ) (A : PlaneMatrices x) (i : Fin 3) : lattice x :=
  ⟨⟨castVec (A.val i), by
    change realDot x (castVec (A.val i)) = 0
    rw [realDot_castVec]
    have hi : A.val i ⬝ᵥ x = 0 := congrFun A.property i
    rw [dotProduct_comm] at hi
    exact_mod_cast hi⟩, castVec_mem _⟩

@[simp] theorem rows_coordinate (x : Fin 3 → ℤ) (A : PlaneMatrices x)
    (i j : Fin 3) : (((rows x A i : lattice x) : plane x) : Ambient) j =
      (A.val i j : ℝ) := rfl

@[simp] theorem norm_rows (x : Fin 3 → ℤ) (A : PlaneMatrices x) (i : Fin 3) :
    ‖rows x A i‖ = ‖castVec (A.val i)‖ := rfl

def projectedColumn (A : IntMatrix) (j : Fin 3) : ℝ × ℝ :=
  ((A 0 j : ℝ) / (A 2 j : ℝ), (A 1 j : ℝ) / (A 2 j : ℝ))

end Problem355.PlaneRowTransport

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.RowLatticeMatrices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.RowLatticeMatrices

open Matrix IntegralPlaneLattice

abbrev IntMatrix := Matrix (Fin 3) (Fin 3) ℤ

abbrev RowMatrices (x : Fin 3 → ℤ) (L : Submodule ℤ (Fin 3 → ℤ)) :=
  {A : IntMatrix // A *ᵥ x = 0 ∧ ∀ i, A i ∈ L}

def rowsEquiv (x : Fin 3 → ℤ) (L : Submodule ℤ (Fin 3 → ℤ)) :
    RowMatrices x L ≃ (Fin 3 → latticeIn x L) where
  toFun A i := kernelEquivIn x L ⟨A.val i, A.property.2 i, by
    change x ⬝ᵥ A.val i = 0
    rw [dotProduct_comm]
    exact congrFun A.property.1 i⟩
  invFun u := ⟨fun i => ((kernelEquivIn x L).symm (u i)).val, by
    constructor
    · funext i
      change (((kernelEquivIn x L).symm (u i)).val) ⬝ᵥ x = 0
      rw [dotProduct_comm]
      exact ((kernelEquivIn x L).symm (u i)).property.2
    · intro i
      exact ((kernelEquivIn x L).symm (u i)).property.1⟩
  left_inv A := by
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val ((kernelEquivIn x L).symm_apply_apply
      ⟨A.val i, A.property.2 i, by
        change x ⬝ᵥ A.val i = 0
        rw [dotProduct_comm]
        exact congrFun A.property.1 i⟩)
  right_inv u := by
    funext i
    exact (kernelEquivIn x L).apply_symm_apply (u i)

@[simp] theorem rowsEquiv_coordinate (x : Fin 3 → ℤ)
    (L : Submodule ℤ (Fin 3 → ℤ)) (A : RowMatrices x L) (i j : Fin 3) :
    (((rowsEquiv x L A i : plane x) : Ambient) j) = (A.val i j : ℝ) := rfl

@[simp] theorem rowsEquiv_norm (x : Fin 3 → ℤ)
    (L : Submodule ℤ (Fin 3 → ℤ)) (A : RowMatrices x L) (i : Fin 3) :
    ‖rowsEquiv x L A i‖ = ‖castVec (A.val i)‖ := rfl

def rowFamily (x : Fin 3 → ℤ) (L : Submodule ℤ (Fin 3 → ℤ))
    (S : Finset IntMatrix) (hS : ∀ A ∈ S, A *ᵥ x = 0 ∧ ∀ i, A i ∈ L) :
    Finset (Fin 3 → latticeIn x L) := by
  classical
  exact S.attach.image (fun A => rowsEquiv x L ⟨A.val, hS A.val A.property⟩)

@[simp] theorem mem_rowFamily (x : Fin 3 → ℤ) (L : Submodule ℤ (Fin 3 → ℤ))
    (S : Finset IntMatrix) (hS : ∀ A ∈ S, A *ᵥ x = 0 ∧ ∀ i, A i ∈ L)
    (u : Fin 3 → latticeIn x L) :
    u ∈ rowFamily x L S hS ↔ ((rowsEquiv x L).symm u).val ∈ S := by
  classical
  constructor
  · intro hu
    obtain ⟨A, _, rfl⟩ := Finset.mem_image.mp hu
    simp
  · intro hu
    apply Finset.mem_image.mpr
    refine ⟨⟨((rowsEquiv x L).symm u).val, hu⟩, Finset.mem_attach _ _, ?_⟩
    change rowsEquiv x L ((rowsEquiv x L).symm u) = u
    exact (rowsEquiv x L).apply_symm_apply u

end Problem355.RowLatticeMatrices

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.DiagonalKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.DiagonalKernel

open scoped BigOperators Matrix

variable {R ι : Type*} [Semiring R] [Fintype ι] [DecidableEq ι]

abbrev Kernel (A : Matrix ι ι R) := {x : ι → R // A.mulVec x = 0}

def diagonalKernelEquiv (d : ι → R) :
    Kernel (Matrix.diagonal d) ≃ (∀ i, {x : R // d i * x = 0}) where
  toFun x i := ⟨x.1 i, by
    have h := congrFun x.2 i
    simpa only [Matrix.mulVec_diagonal, Pi.zero_apply] using h⟩
  invFun x := ⟨fun i => (x i).1, by
    funext i
    simpa only [Matrix.mulVec_diagonal, Pi.zero_apply] using (x i).2⟩
  left_inv x := by rfl
  right_inv x := by rfl

def unitMulVecEquiv (Q : (Matrix ι ι R)ˣ) : (ι → R) ≃ (ι → R) where
  toFun := (Q : Matrix ι ι R).mulVec
  invFun := ((Q⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R).mulVec
  left_inv x := by
    rw [Matrix.mulVec_mulVec]
    simp
  right_inv x := by
    rw [Matrix.mulVec_mulVec]
    simp

def changeKernelEquiv (A : Matrix ι ι R) (P Q : (Matrix ι ι R)ˣ) :
    Kernel ((P : Matrix ι ι R) * A * (Q : Matrix ι ι R)) ≃ Kernel A := by
  apply Equiv.subtypeEquiv (unitMulVecEquiv Q)
  intro x
  change (((P : Matrix ι ι R) * A * (Q : Matrix ι ι R)).mulVec x = 0) ↔
    A.mulVec ((Q : Matrix ι ι R).mulVec x) = 0
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  exact (Matrix.mulVec_injective_of_isUnit P.isUnit).eq_iff' (by simp)

end Problem355.DiagonalKernel

end OAI
end

section
-- module Solutions.OAIQW_Problem355.PairingDivisor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.PairingDivisor

variable {ι : Type*} [Fintype ι]

def dotHom (x : ι → ℤ) : (ι → ℤ) →+ ℤ :=
  (dotProductBilin ℤ ℤ x).toAddMonoidHom

@[simp] theorem dotHom_apply (x v : ι → ℤ) : dotHom x v = dotProduct x v := rfl

noncomputable def pairingDivisor (L : AddSubgroup (ι → ℤ)) (x : ι → ℤ) : ℕ :=
  (L.map (dotHom x)).index

end Problem355.PairingDivisor

end OAI
end

section
-- module Solutions.OAIQW_Problem355.PlaneFunctional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.PlaneFunctional

variable {ι K : Type*} [Fintype ι] [Field K]

def modularDotHom (q : ℕ) (d : ι → ZMod q) : (ι → ℤ) →+ ZMod q where
  toFun u := dotProduct d (fun i => (u i : ZMod q))
  map_zero' := by simp [dotProduct]
  map_add' u v := by
    simp only [Pi.add_apply, Int.cast_add, dotProduct, mul_add, Finset.sum_add_distrib]

end Problem355.PlaneFunctional

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.EqualCoordinatePlane
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.PlaneFunctional

variable {ι K : Type*} [Fintype ι] [Field K]

def coordinateDifference (i j : ι) : ι → K := by
  classical
  exact Pi.single i 1 - Pi.single j 1

@[simp] theorem coordinateDifference_dot (i j : ι) (v : ι → K) :
    dotProduct (coordinateDifference i j) v = v i - v j := by
  classical
  simp only [coordinateDifference, sub_dotProduct, single_dotProduct, one_mul]

def equalCoordinateSubgroup (q : ℕ) [Fact q.Prime] (L : AddSubgroup (ι → ℤ)) (i j : ι) :
    AddSubgroup L :=
  ((modularDotHom q (coordinateDifference i j)).comp L.subtype).ker

@[simp] theorem mem_equalCoordinateSubgroup (q : ℕ) [Fact q.Prime] (L : AddSubgroup (ι → ℤ))
    (i j : ι) (v : L) :
    v ∈ equalCoordinateSubgroup q L i j ↔
      (((v : ι → ℤ) i : ℤ) : ZMod q) = (((v : ι → ℤ) j : ℤ) : ZMod q) := by
  change dotProduct (coordinateDifference i j)
    (fun a => (((v : ι → ℤ) a : ℤ) : ZMod q)) = 0 ↔ _
  rw [coordinateDifference_dot, sub_eq_zero]

end Problem355.PlaneFunctional

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.IntegralPlaneReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace Problem355.IntegralPlaneReduction

abbrev Vector := Fin 3 → ℤ

def integralNormal (x : Vector) : Vector →ₗ[ℤ] ℤ := dotProductBilin ℤ ℤ x

def integralPlane (Λ : Submodule ℤ Vector) (x : Vector) : Submodule ℤ Vector :=
  Λ ⊓ (integralNormal x).ker

def reducedNormal (q : ℕ) (x : Vector) : Fin 3 → ZMod q := fun i => (x i : ZMod q)

@[simp] theorem mem_integralPlane (Λ : Submodule ℤ Vector) (x v : Vector) :
    v ∈ integralPlane Λ x ↔ v ∈ Λ ∧ dotProduct x v = 0 := Iff.rfl

open scoped LinearAlgebra.Projectivization

end Problem355.IntegralPlaneReduction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.EqualCoordinatePacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.EqualCoordinatePacking

open IntegralPlaneLattice

abbrev Vector := Fin 3 → ℤ

def embedding (x : Vector) (L : Submodule ℤ Vector) :
    integerPlaneIn x L →ₗ[ℤ] plane x :=
  (latticeIn x L).subtype.comp (kernelEquivIn x L).toLinearMap

@[simp] theorem embedding_coe (x : Vector) (L : Submodule ℤ Vector)
    (v : integerPlaneIn x L) :
    ((embedding x L v : plane x) : Ambient) = castVec v := rfl

def equalLattice (q : ℕ) [Fact q.Prime] (x : Vector)
    (L : Submodule ℤ Vector) (i j : Fin 3) : Submodule ℤ (plane x) :=
  ((PlaneFunctional.equalCoordinateSubgroup q (integerPlaneIn x L).toAddSubgroup i j).map
    (embedding x L).toAddMonoidHom).toIntSubmodule

def row (q : ℕ) [Fact q.Prime] (x : Vector) (L : Submodule ℤ Vector)
    (i j : Fin 3) (v : integerPlaneIn x L)
    (hv : ((v : Vector) i : ZMod q) = ((v : Vector) j : ZMod q)) :
    equalLattice q x L i j :=
  ⟨embedding x L v, ⟨v,
    (PlaneFunctional.mem_equalCoordinateSubgroup q
      (integerPlaneIn x L).toAddSubgroup i j v).mpr hv, rfl⟩⟩

end Problem355.EqualCoordinatePacking

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.ZeroDeterminantCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.ZeroDeterminantCount

open Matrix PrimitiveNormal
open scoped Matrix BigOperators
attribute [local instance] Classical.propDecidable

abbrev IntMatrix := Matrix (Fin 3) (Fin 3) ℤ
abbrev IntVector := Fin 3 → ℤ

structure RowData where
  B : ℕ
  b : ℕ
  e : ℕ
  k : ℕ
  prime : B.Prime
  e_le_k : e ≤ k
  L : Submodule ℤ IntVector
  C : IntMatrix
  P : (Matrix (Fin 3) (Fin 3) (ZMod (B ^ k)))ˣ
  Q : (Matrix (Fin 3) (Fin 3) (ZMod (B ^ k)))ˣ
  diagonal : C.map (Int.castRingHom (ZMod (B ^ k))) =
    (P : Matrix _ _ _) * Matrix.diagonal
      ![1, (B : ZMod (B ^ k)) ^ b, (B : ZMod (B ^ k)) ^ e] *
      (Q : Matrix _ _ _)
  contains : ∀ v : IntVector, (B ^ e) • v ∈ L
  rows : ∀ i, C i ∈ L
  index_eq : L.toAddSubgroup.index = B ^ (b + e)

def RowData.h (D : RowData) : ℝ := (D.B : ℝ) ^ D.k
def RowData.I (D : RowData) : ℕ := D.B ^ (D.b + D.e)
def RowData.E (D : RowData) : ℕ := D.B ^ D.e

def planeConstant : ℝ := (144 * Real.pi) ^ 3

end Problem355.ZeroDeterminantCount

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.WeightedNormalReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.PrimitiveNormal

open Matrix
open scoped Matrix BigOperators

noncomputable def normalBox (X : ℤ) : Finset Vector := by
  classical
  exact (Finset.Icc (fun _ => -(2 * X ^ 2)) (fun _ => 2 * X ^ 2)).filter
    (fun w => IsPrimitive w ∧ ∀ i, w i ≠ 0)

end Problem355.PrimitiveNormal

end OAI
end

section
-- module Solutions.OAIQW_Problem355.ZeroGlobalCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace Problem355.ZeroGlobalCount

open Matrix PrimitiveNormal ZeroDeterminantCount
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def countConstant (Ca Cg Cd : ℝ) : ℝ :=
  4 * (1024 * Ca + 3 * (125 * Cg + 512 * Cd)) * planeConstant

end Problem355.ZeroGlobalCount

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.AuxiliaryZeroCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.AuxiliaryZeroCount

open Matrix PrimitiveNormal ZeroDeterminantCount LiftingProbability
open scoped BigOperators

def countConstant : ℝ :=
  ZeroGlobalCount.countConstant 8 (2 * 2000 ^ 6) (4 * 2000 ^ 3)

end Problem355.AuxiliaryZeroCount

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.FixedDetReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.FixedDetReduction

open scoped BigOperators

def radius (X : ℝ) (ℓ : Fin 3 → ℝ) (j : Fin 3) : ℝ := 1000 * X / ℓ j

def AnisotropicEstimate (a : ℝ) : Prop :=
  ∀ (r : Fin 3 → ℝ) (u : ℤ) (T : Finset (Matrix (Fin 3) (Fin 3) ℤ)),
    Antitone r → 1 ≤ r 2 → u ≠ 0 →
    (∀ Q ∈ T, Q.det = u ∧ ∀ j,
      ‖(WithLp.toLp 2 (fun i => (Q i j : ℝ)) : EuclideanSpace ℝ (Fin 3))‖ ≤ r j) →
    (T.card : ℝ) ≤ a * (∏ j, r j) ^ 2 * Real.log (2 * r 0) ^ 2

end Problem355.FixedDetReduction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.FixedDetLattice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.FixedDetLattice

open Module Submodule MeasureTheory
open scoped BigOperators

abbrev E := EuclideanSpace ℝ (Fin 3)

def basisMatrix (b : Basis (Fin 3) ℝ E) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => b i j

end Problem355.FixedDetLattice

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.IntegerMatrixEvents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.IntegerMatrixEvents
attribute [local instance] Classical.propDecidable

open Finset Matrix
open IntegerSampling OrbitSampling

abbrev IntMatrix := Matrix (Fin 3) (Fin 3) ℤ

def matrices (N : ℕ) (shift : Fin 3 → ℤ) : Finset IntMatrix := by
  classical
  exact Finset.univ.image (@integralMatrix N shift)

@[simp] theorem integralMatrix_residue {N : ℕ} {shift : Fin 3 → ℤ}
    (m : ℕ) (x : Fin 3 → Box N 3 shift) :
    (integralMatrix x).map (Int.cast : ℤ → ZMod m) =
      Matrix.transpose (fun j => residue m (x j)) := rfl

@[simp] theorem integralMatrix_project {N : ℕ}
    (x : Fin 3 → Box N 3 (samplingShift N)) (j : Fin 3) :
    Homogeneous.project (Homogeneous.integerColumn (integralMatrix x) j) =
      IntegerSampling.project (x j) := rfl

def matrixWeight {Ω : Type*} [Fintype Ω] (q s : ℕ)
    (w : Ω → ℝ) (V : Ω → Finset (Fin 3 → ZMod q)) (A : IntMatrix) : ℝ :=
  LiftingProbability.auxiliaryWeight q s w V
    (fun j i => (A i j : ZMod q))

@[simp] theorem matrixWeight_integralMatrix {Ω : Type*} [Fintype Ω]
    {N : ℕ} {shift : Fin 3 → ℤ} (q s : ℕ)
    (w : Ω → ℝ) (V : Ω → Finset (Fin 3 → ZMod q))
    (x : Fin 3 → Box N 3 shift) :
    matrixWeight q s w V (integralMatrix x) =
      LiftingProbability.auxiliaryWeight q s w V
        (fun j => residue q (x j)) := rfl

end Problem355.IntegerMatrixEvents

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.IntegerMatrixFibers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace Problem355.IntegerMatrixEvents
open Finset Matrix IntegerSampling OrbitSampling
attribute [local instance] Classical.propDecidable

def fixedDetProperty (h : ℕ) [NeZero h]
    (C : Fin 3 → Fin 3 → ZMod h) (t : ℤ) (A : IntMatrix) : Prop :=
  Homogeneous.projectedDistinct (Homogeneous.integerColumn A 0)
      (Homogeneous.integerColumn A 1) (Homogeneous.integerColumn A 2) ∧
    (fun j i => (A i j : ZMod h)) ∈ orbitFinset (MainGroup h) C ∧ A.det = t

def fixedDetEvent (N h : ℕ) [NeZero h]
    (C : Fin 3 → Fin 3 → ZMod h) (t : ℤ) : Finset IntMatrix :=
  (matrices N (samplingShift N)).filter (fixedDetProperty h C t)

end Problem355.IntegerMatrixEvents

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.IntegralAmbientLattice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace Problem355.IntegralPlaneLattice
open Module MeasureTheory

instance standardLattice_isZLattice : IsZLattice ℝ standardLattice := by
  unfold standardLattice
  infer_instance

end Problem355.IntegralPlaneLattice

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.NonzeroWeightedCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace Problem355.NonzeroWeightedCount

open Matrix
open scoped BigOperators Matrix

abbrev IntMatrix := Matrix (Fin 3) (Fin 3) ℤ

def columnTriple (A : IntMatrix) : Anisotropic.Triple :=
  (A.col 0, A.col 1, A.col 2)

def anisotropicConstant : ℝ := 35721000 * Real.pi ^ 3 / (Real.log 2) ^ 2

def latticeConstant : ℝ := anisotropicConstant * 1000 ^ 6 * 144

def boxConstant : ℝ := latticeConstant * 144 * 4 ^ 6

end Problem355.NonzeroWeightedCount

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.PrimePowerRowData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.PrimePowerRowData

open Matrix PrimitiveNormal PairingDivisor

def integerLift {h : ℕ} (C : Matrix (Fin 3) (Fin 3) (ZMod h)) :
    Matrix (Fin 3) (Fin 3) ℤ :=
  C.map (fun z => (z.val : ℤ))

@[simp] theorem integerLift_reduction {h : ℕ} [NeZero h]
    (C : Matrix (Fin 3) (Fin 3) (ZMod h)) :
    (integerLift C).map (Int.castRingHom (ZMod h)) = C := by
  ext i j
  simp [integerLift]

abbrev rowModule {h : ℕ} (C : Matrix (Fin 3) (Fin 3) (ZMod h)) :
    Submodule ℤ (Fin 3 → ℤ) :=
  (RowLattice.integerRowLattice h C).toIntSubmodule

variable {B k : ℕ} {C : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k))}

theorem integerLift_row_mem (hB : B.Prime) (i : Fin 3) :
    integerLift C i ∈ rowModule C := by
  let : NeZero B := ⟨hB.ne_zero⟩
  exact RowLattice.row_mem_integerRowLattice_of_reduction_eq (B ^ k)
    (integerLift C) C 1 (by simpa only [Matrix.one_mul] using integerLift_reduction C) i

theorem integerLift_diagonalization (d : PrimePowerData B k C) (hB : B.Prime) :
    (integerLift C).map (Int.castRingHom (ZMod (B ^ k))) =
      (d.left : Matrix _ _ _) * Matrix.diagonal
        ![1, (B : ZMod (B ^ k)) ^ d.b, (B : ZMod (B ^ k)) ^ d.e] *
          (d.right : Matrix _ _ _) := by
  let : NeZero B := ⟨hB.ne_zero⟩
  rw [integerLift_reduction]
  simpa only [Nat.cast_pow] using d.diagonalization

theorem rowModule_index (d : PrimePowerData B k C) (hB : B.Prime) :
    (rowModule C).toAddSubgroup.index = B ^ (d.b + d.e) := by
  change (RowLattice.integerRowLattice (B ^ k) C).index = _
  rw [d.row_lattice_index hB.ne_zero, pow_add]

theorem larger_divisor_nsmul_mem (d : PrimePowerData B k C) (v : Fin 3 → ℤ) :
    (B ^ d.e) • v ∈ rowModule C :=
  d.multiple_mem_row_lattice v

end Problem355.PrimePowerRowData

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.ZeroRowData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.PrimePowerData

open ZeroDeterminantCount

variable {B k : ℕ} {C : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k))}

def toZeroRowData (d : PrimePowerData B k C) (hB : B.Prime) : RowData where
  B := B
  b := d.b
  e := d.e
  k := k
  prime := hB
  e_le_k := d.e_le_k
  L := PrimePowerRowData.rowModule C
  C := PrimePowerRowData.integerLift C
  P := d.left
  Q := d.right
  diagonal := PrimePowerRowData.integerLift_diagonalization d hB
  contains := PrimePowerRowData.larger_divisor_nsmul_mem d
  rows := PrimePowerRowData.integerLift_row_mem hB
  index_eq := PrimePowerRowData.rowModule_index d hB

@[simp] theorem toZeroRowData_L (d : PrimePowerData B k C) (hB : B.Prime) :
    (d.toZeroRowData hB).L =
      (RowLattice.integerRowLattice (B ^ k) C).toIntSubmodule := rfl

@[simp] theorem toZeroRowData_h (d : PrimePowerData B k C) (hB : B.Prime) :
    (d.toZeroRowData hB).h = (B : ℝ) ^ k := rfl

@[simp] theorem toZeroRowData_I (d : PrimePowerData B k C) (hB : B.Prime) :
    (d.toZeroRowData hB).I = B ^ (d.b + d.e) := rfl

@[simp] theorem toZeroRowData_E (d : PrimePowerData B k C) (hB : B.Prime) :
    (d.toZeroRowData hB).E = B ^ d.e := rfl

end Problem355.PrimePowerData

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.UniformFixedFiberCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.UniformFixedFiberCount

open Finset

def commonConstant (Czero Cnonzero : ℝ) : ℝ :=
  Cnonzero + 2 * Czero / (Real.log 2) ^ 2

def countConstant : ℝ :=
  commonConstant AuxiliaryZeroCount.countConstant (8 * NonzeroWeightedCount.boxConstant)

end Problem355.UniformFixedFiberCount

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.TypedFixedFiberCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace Problem355.TypedFixedFiberCount

open Matrix IntegerSampling OrbitSampling IntegerMatrixEvents
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def orbitEvent (N h : ℕ) [NeZero h]
    (C : Fin 3 → Fin 3 → ZMod h) : Finset IntMatrix :=
  (matrices N (samplingShift N)).filter (fun A =>
    Homogeneous.projectedDistinct (Homogeneous.integerColumn A 0)
      (Homogeneous.integerColumn A 1) (Homogeneous.integerColumn A 2) ∧
    (fun j i => (A i j : ZMod h)) ∈ orbitFinset (MainGroup h) C)

end Problem355.TypedFixedFiberCount

end

end OAI
end


