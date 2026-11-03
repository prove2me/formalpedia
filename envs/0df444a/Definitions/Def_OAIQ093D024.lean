-- Prove2me | Definitions.Def_OAIQ093D024
-- name    : OAIQ093D024
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-02T18:51:42.362591+00:00
-- url     : https://prove2.me/theorems/ba98a20f-d23a-4091-b34d-aecc951e9909
-- title:
--   Definitions bundle OAIQ093D024 of the split of OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 5 declarations of OpenAI's Lean: 4 definitions and 1 theorem. The definitions and types are `OAI.PolycyclicRecognition.IntegralNilshadowData.powerGraphEmbedding`, `OAI.PolycyclicRecognition.IntegralNilshadowData.realPowerEmbedding`, `OAI.PolycyclicRecognition.JointFixedReductionData.layerAction`, `OAI.PolycyclicRecognition.JointFixedReductionData.layerEnd`.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: [`PolycyclicRecognition_Lattices_JointFixedLayerAction`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Lattices/JointFixedLayerAction.lean), [`PolycyclicRecognition_Lattices_NilshadowPowerGraph`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Lattices/NilshadowPowerGraph.lean).
--
--   **Imports.** It imports the bundle `OAIQ093D021` of this split.
--
--   **Imported by** (directly, in this split): the proof of `OAI.PolycyclicRecognition.nilpotent_by_abelian_uniform_lattice`.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ093D021

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_JointFixedLayerAction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer_normal _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instLocallyCompactSpaceFactorExtension _root_.OAI.PolycyclicRecognition.instT2SpaceFactorExtension _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # The abelian quotient acts on the residual lower-central layers

Inner section factors disappear on these layers, so this is an actual linear
representation of the quotient. Its selected generators are unipotent.
-/

noncomputable section
namespace PolycyclicRecognition
open LieModule
open scoped Manifold ContDiff IsMulCommutative
attribute [local instance] polynomialSubalgebraGroup
variable {L G Q : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]
  [Group G] [Group Q]
  {E : GroupExtension L G Q}
  {hsmooth : ∀ g : G, ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ∞ (E.conjAct g)} {qs : List Q}

namespace JointFixedReductionData
variable (D : JointFixedReductionData E hsmooth qs)

def layerEnd (k : ℕ) (q : Q) : Module.End ℝ (D.lowerCentralLayer k) :=
  invariantLayerEnd _ _ (jointFixedLinearAction D.operators (D.action q)
    (fun S hS => D.action_commutes S hS q))
    (jointFixed_action_preserves_lowerCentral D.operators (D.action q)
      (fun S hS => D.action_commutes S hS q) k)
    (jointFixed_action_preserves_lowerCentral D.operators (D.action q)
      (fun S hS => D.action_commutes S hS q) (k + 1))

def layerAction (k : ℕ) : Q →* Module.End ℝ (D.lowerCentralLayer k) where
  toFun := D.layerEnd k
  map_one' := by
    apply LinearMap.ext
    intro y
    refine Quotient.inductionOn' y ?_
    intro x
    apply congrArg Submodule.Quotient.mk
    apply Subtype.ext
    apply Subtype.ext
    change D.action 1 (x : jointFixedLieSubalgebra D.operators) = (x : L)
    rw [action, polynomialModelLieEquiv_apply, D.normalized, map_one]
    rfl
  map_mul' q r := by
    apply LinearMap.ext
    intro y
    refine Quotient.inductionOn' y ?_
    intro x
    let K := jointFixedLieSubalgebra D.operators
    let R := D.residualSystem
    have hx : (x : K) ∈ lowerCentralSeries ℝ K K k := x.property
    have hy : R.action (q * r) x ∈ lowerCentralSeries ℝ K K k :=
      jointFixed_action_preserves_lowerCentral D.operators (D.action (q * r))
        (fun S hS => D.action_commutes S hS _) k x hx
    have hh := polynomialSubalgebra_inner_difference K (R.factor q r) k (R.action (q * r) x) hy
    rw [← R.action_mul_apply] at hh
    symm
    apply (Submodule.Quotient.eq _).mpr
    exact hh

end JointFixedReductionData
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_NilshadowPowerGraph
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.latticeNormalFlag_normal _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.NilpotentLatticeCoordinates.automorphism_mul _root_.OAI.PolycyclicRecognition.NilpotentLatticeCoordinates.automorphism_on_lattice _root_.OAI.PolycyclicRecognition.NilpotentLatticeCoordinates.automorphism_one _root_.OAI.PolycyclicRecognition.rotationalTwistCharacter_apply _root_.OAI.PolycyclicRecognition.rotationalTwistLift_left _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Embedding the finite-power extension in the real invariant graph -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff

namespace IntegralNilshadowData
variable {L G : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [Group G] {n : ℕ}
  {E : GroupExtension L G (IntegralLatticeGroup n)} (D : IntegralNilshadowData E)

def realPowerEmbedding (m : ℕ)
    (φ : Multiplicative (Fin n → ℝ) →* MulAut D.completion.carrier)
    (he : ∀ z x, D.completedAction (latticePowerHom n m z) x = φ (integerVectorHom n z) x) :
    FactorExtension (D.system.pullback (latticePowerHom n m)) →*
      (D.completion.carrier ⋊[φ] Multiplicative (Fin n → ℝ)) where
  toFun a := ⟨D.completion.embed ⟨a.left, latticePowerHom n m a.right⟩, integerVectorHom n a.right⟩
  map_one' := by
    apply SemidirectProduct.ext
    · change D.completion.embed (1 : FactorExtension D.twistedSystem) = 1
      exact map_one _
    · exact map_one _
  map_mul' a b := by
    apply SemidirectProduct.ext
    · have h := congrArg (fun x => x.left)
        ((D.factorEmbedding.comp (factorPullbackMap D.system (latticePowerHom n m))).map_mul a b)
      change D.completion.embed
          ⟨(a * b).left, latticePowerHom n m (a * b).right⟩ =
        D.completion.embed ⟨a.left, latticePowerHom n m a.right⟩ *
          D.completedAction (latticePowerHom n m a.right)
            (D.completion.embed ⟨b.left, latticePowerHom n m b.right⟩) at h
      rw [he] at h
      exact h
    · exact map_mul (integerVectorHom n) _ _

theorem realPowerEmbedding_mem_graph {m : ℕ} (hm : 0 < m)
    (φ : Multiplicative (Fin n → ℝ) →* MulAut D.completion.carrier)
    (he : ∀ z x, D.completedAction (latticePowerHom n m z) x = φ (integerVectorHom n z) x)
    (hinv : ∀ v x, D.height (φ v x) = D.height x)
    (a : FactorExtension (D.system.pullback (latticePowerHom n m))) :
    D.realPowerEmbedding m φ he a ∈ rotationalTwist φ (D.inverseScaledHeight m)
      (fun v x => congrArg (scaleRealHeight n (-((m : ℝ)⁻¹))) (hinv v x)) := by
  change integerVectorHom n a.right =
    (D.inverseScaledHeight m (D.completion.embed ⟨a.left, latticePowerHom n m a.right⟩))⁻¹
  apply Multiplicative.ext
  change integerVectorMap n a.right.toAdd =
    -(-((m : ℝ)⁻¹) • D.height (D.completion.embed ⟨a.left, latticePowerHom n m a.right⟩))
  rw [D.height_embed]
  change integerVectorMap n a.right.toAdd =
    -(-((m : ℝ)⁻¹) • integralRealHeight (a.right ^ m))
  rw [map_pow]
  change integerVectorMap n a.right.toAdd =
    -(-((m : ℝ)⁻¹) • (m • integerVectorMap n a.right.toAdd))
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  simp [hm']

def powerGraphEmbedding {m : ℕ} (hm : 0 < m)
    (φ : Multiplicative (Fin n → ℝ) →* MulAut D.completion.carrier)
    (he : ∀ z x, D.completedAction (latticePowerHom n m z) x = φ (integerVectorHom n z) x)
    (hinv : ∀ v x, D.height (φ v x) = D.height x) :
    FactorExtension (D.system.pullback (latticePowerHom n m)) →*
      rotationalTwist φ (D.inverseScaledHeight m)
        (fun v x => congrArg (scaleRealHeight n (-((m : ℝ)⁻¹))) (hinv v x)) :=
  (D.realPowerEmbedding m φ he).codRestrict _ (D.realPowerEmbedding_mem_graph hm φ he hinv)

end IntegralNilshadowData
end PolycyclicRecognition

end

end OAI
end


