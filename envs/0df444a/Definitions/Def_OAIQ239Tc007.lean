-- Prove2me | Definitions.Def_OAIQ239Tc007
-- name    : OAIQ239Tc007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T22:15:05.150035+00:00
-- url     : https://prove2.me/theorems/58c9975a-233e-4452-9a6a-1ab3a8cea058
-- title:
--   Definitions bundle OAIQ239Tc007 of the split of OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 112 declarations of OpenAI's Lean: 31 definitions and 81 theorems. The definitions and types are `OAI.TamingCompatibility.GeometricChart.cutoffForm`, `OAI.TamingCompatibility.GeometricHilbert.CoordinateOperator.pullCoefficient`, `OAI.TamingCompatibility.GeometricSymbol.coords`, `OAI.TamingCompatibility.HermitianHodge.star`, `OAI.TamingCompatibility.HodgeFrame.basisForm`, `OAI.TamingCompatibility.HodgeFrame.combineThree`, `OAI.TamingCompatibility.HodgeFrozenEnergy.coefficient`, `OAI.TamingCompatibility.HodgeGeometricCoefficients.frame`, `OAI.TamingCompatibility.HodgeGeometricCoefficients.principal`, `OAI.TamingCompatibility.HodgeNormalOperator.join`, `OAI.TamingCompatibility.HodgeNormalOperator.joinCLM`, `OAI.TamingCompatibility.HodgeNormalOperator.left`, `OAI.TamingCompatibility.HodgeNormalOperator.right`, `OAI.TamingCompatibility.HodgeNormalSymbol.normalSymbol`, `OAI.TamingCompatibility.HodgeNormalSymbol.symbol`, `OAI.TamingCompatibility.HodgeNormalSymbol.symbolMap`, `OAI.TamingCompatibility.HodgeStarGeometry.starMap`, `OAI.TamingCompatibility.LocalMatrixOperator.combine`, `OAI.TamingCompatibility.LocalMatrixOperator.evaluationConstant`, `OAI.TamingCompatibility.LocalMatrixOperator.frameTest`, `OAI.TamingCompatibility.LocalMatrixOperator.frameVector`, `OAI.TamingCompatibility.LocalMatrixOperator.oneCoordinates`, `OAI.TamingCompatibility.LocalMatrixOperator.oneVector`, `OAI.TamingCompatibility.ManifoldForms.liftSupport`, `OAI.TamingCompatibility.MatrixEnergy.patchLower`, `OAI.TamingCompatibility.MetricForms.instNormedAddCommGroupContinuousLinearMapRealIdForm`, `OAI.TamingCompatibility.MetricForms.instNormedSpaceRealContinuousLinearMapIdForm`, `OAI.TamingCompatibility.MetricForms.pairingCLM`, `OAI.TamingCompatibility.UnitaryFrame.fundamental`, `OAI.TamingCompatibility.UnitaryFrame.interior`, `OAI.TamingCompatibility.UnitaryFrame.star`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `TamingCompatibility_Charts_ChartEnergyIntegral`, `TamingCompatibility_Charts_ChartLift`, `TamingCompatibility_Charts_CoefficientCutoff`, `TamingCompatibility_Charts_LocalMatrixOperator`, `TamingCompatibility_Charts_UnitaryFrames`, `TamingCompatibility_DifferentialForms_ComplexEquiv`, `TamingCompatibility_DifferentialForms_ContDiffLinearEmbedding`, `TamingCompatibility_DifferentialForms_DirectionalEnergy`, `TamingCompatibility_DifferentialForms_Form`, `TamingCompatibility_DifferentialForms_FormEquiv`, `TamingCompatibility_DifferentialForms_FunSmul`, `TamingCompatibility_DifferentialForms_InnerJLeft`, `TamingCompatibility_DifferentialForms_MetricCoords`, `TamingCompatibility_DifferentialForms_MetricL2Core`, `TamingCompatibility_DifferentialForms_MetricPairingCLM`, `TamingCompatibility_DifferentialForms_RadialCoefficientProfiles`, `TamingCompatibility_DifferentialForms_Sign`, `TamingCompatibility_DifferentialForms_SingleFamily`, `TamingCompatibility_DifferentialForms_Star`, `TamingCompatibility_DifferentialForms_SymbolMap`, `TamingCompatibility_DifferentialForms_UnitaryFrame`, `TamingCompatibility_DifferentialForms_UnitaryVectors`, `TamingCompatibility_DifferentialForms_Wedge`, `TamingCompatibility_Elliptic_NormalSystem`, `TamingCompatibility_Functional_GramOrthonormalBasis`, `TamingCompatibility_Functional_NormalSymbol`, `TamingCompatibility_Hodge_HodgeFrameDifferential`, `TamingCompatibility_Hodge_HodgeFrozenEnergy`, `TamingCompatibility_Hodge_HodgeGeometricCoefficients`, `TamingCompatibility_Hodge_HodgeMatrixEnergy`, `TamingCompatibility_Hodge_HodgeStarGeometry`.
--
--   **Imports.** It imports the published bundle `Def_TamingCompatibility`; the bundles `OAIQ239Tc000`, `OAIQ239Tc001`, `OAIQ239Tc002` and `OAIQ239Tc003` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ239Tc010`, `OAIQ239Tc011`, `OAIQ239Tc012` and `OAIQ239Tc013`; the statement `OAI.TamingCompatibility.GeometricHilbert.NormalMetricCalculus.pulled_principal`; the proofs of `OAI.TamingCompatibility.GeometricHilbert.FirstJetGauge.transformedFirst_zero` and `OAI.TamingCompatibility.GeometricHilbert.OrthogonalJets.gauge_contDiff`.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc000
import Definitions.Def_OAIQ239Tc001
import Definitions.Def_OAIQ239Tc002
import Definitions.Def_OAIQ239Tc003

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_UnitaryFrame
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set _root_.MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
open scoped BigOperators
open scoped RealInnerProductSpace
namespace TamingCompatibility.UnitaryFrame

def star (a : W) : W := WithLp.toLp 2 ![a 5, -a 4, a 3, a 2, -a 1, a 0]

def fundamental : W := WithLp.toLp 2 ![1, 0, 0, 0, 0, 1]

lemma star_square (a : W) : star (star a) = a := by
  ext i
  fin_cases i <;> simp [star]

lemma star_add (a b : W) : star (a + b) = star a + star b := by
  ext i
  fin_cases i <;> simp [star, add_comm]

lemma star_smul (c : ℝ) (a : W) : star (c • a) = c • star a := by
  ext i
  fin_cases i <;> simp [star]

lemma star_self_adjoint (a b : W) : ⟪star a, b⟫ = ⟪a, star b⟫ := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_succ, star]
  ring

lemma star_antiInvariantPart (a : W) : star (antiInvariantPart a) = antiInvariantPart a := by
  ext i
  fin_cases i <;> simp [star, antiInvariantPart, jAction] <;> ring

def interior (ξ : V) (a : W) : V := WithLp.toLp 2
  ![-ξ 1 * a 0 - ξ 2 * a 1 - ξ 3 * a 2,
    ξ 0 * a 0 - ξ 2 * a 3 - ξ 3 * a 4,
    ξ 0 * a 1 + ξ 1 * a 3 - ξ 3 * a 5,
    ξ 0 * a 2 + ξ 1 * a 4 + ξ 2 * a 5]

end TamingCompatibility.UnitaryFrame

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_InnerJLeft
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set _root_.MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
open scoped BigOperators
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
namespace TamingCompatibility.UnitaryBasis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable [FiniteDimensional ℝ E]

theorem exists_unitary_basis (J : E →ₗᵢ[ℝ] E) (hJ : ∀ v, J (J v) = -v)
    (hdim : Module.finrank ℝ E = 4) :
    ∃ b : OrthonormalBasis (Fin 4) ℝ E,
      J (b 0) = b 1 ∧ J (b 1) = -b 0 ∧ J (b 2) = b 3 ∧ J (b 3) = -b 2 := by
  classical
  let b₀ : OrthonormalBasis (Fin 4) ℝ E :=
    (stdOrthonormalBasis ℝ E).reindex (finCongr hdim)
  let v := b₀ 0
  have hv : ‖v‖ = 1 := b₀.orthonormal.norm_eq_one _
  let a : Fin 4 → E := ![v,J v,0,0]
  let s : Set (Fin 4) := {0,1}
  have ha : Orthonormal ℝ (s.domRestrict a) := by
    rw [orthonormal_iff_ite]
    intro i j
    rcases i with ⟨i,hi⟩
    rcases j with ⟨j,hj⟩
    have hi' : i = 0 ∨ i = 1 := hi
    have hj' : j = 0 ∨ j = 1 := hj
    rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl <;>
      simp [s, a, Set.domRestrict, hv,
        inner_self_J J hJ, inner_J_left J hJ]
  obtain ⟨b,hb⟩ := ha.exists_orthonormalBasis_extension_of_card_eq (by simpa using hdim)
  have hb0 : b 0 = v := hb 0 (by simp [s])
  have hb1 : b 1 = J v := hb 1 (by simp [s])
  let w := b 2
  have hw : ‖w‖ = 1 := b.orthonormal.norm_eq_one _
  have hvw : ⟪v,w⟫ = 0 := by
    rw [← hb0]
    exact b.orthonormal.inner_eq_zero (by decide : (0 : Fin 4) ≠ 2)
  have hJvw : ⟪J v,w⟫ = 0 := by
    rw [← hb1]
    exact b.orthonormal.inner_eq_zero (by decide : (1 : Fin 4) ≠ 2)
  have hvJw : ⟪v,J w⟫ = 0 := by
    have h := inner_J_left J hJ v w
    linarith
  have hwv : ⟪w,v⟫ = 0 := by rw [real_inner_comm, hvw]
  have hwJv : ⟪w,J v⟫ = 0 := by rw [real_inner_comm, hJvw]
  have hJwv : ⟪J w,v⟫ = 0 := by rw [real_inner_comm, hvJw]
  let c : Fin 4 → E := ![v,J v,w,J w]
  have hc : Orthonormal ℝ c := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [c, hv, hw, inner_self_J J hJ,
        hvw, hJvw, hvJw, hwv, hwJv, hJwv, inner_J_left J hJ, hJ]
  let b' := OrthonormalBasis.mk hc
    (hc.linearIndependent.span_eq_top_of_card_eq_finrank (by simpa using hdim.symm)).ge
  refine ⟨b', ?_⟩
  simp [b', OrthonormalBasis.coe_mk, c, hJ]

end TamingCompatibility.UnitaryBasis

open ContinuousAlternatingMap
namespace TamingCompatibility.GeometricSymbol
open UnitaryFrame
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def coords (b : OrthonormalBasis (Fin 4) ℝ E) (α : TwoForm E) : W :=
  WithLp.toLp 2 ![α ![b 0,b 1], α ![b 0,b 2], α ![b 0,b 3],
    α ![b 1,b 2], α ![b 1,b 3], α ![b 2,b 3]]

lemma coords_injective (b : OrthonormalBasis (Fin 4) ℝ E) : Function.Injective (coords b) := by
  intro α β h
  have h0 := congrArg (fun a : W => a 0) h
  have h1 := congrArg (fun a : W => a 1) h
  have h2 := congrArg (fun a : W => a 2) h
  have h3 := congrArg (fun a : W => a 3) h
  have h4 := congrArg (fun a : W => a 4) h
  have h5 := congrArg (fun a : W => a 5) h
  dsimp [coords] at h0 h1 h2 h3 h4 h5
  have he : ∀ i j : Fin 4, α ![b i,b j] = β ![b i,b j] := by
    intro i j
    fin_cases i <;> fin_cases j
    all_goals try assumption
    all_goals simp only [eval_self]
    all_goals rw [eval_swap α, eval_swap β]; congr 1
  apply ContinuousAlternatingMap.toContinuousMultilinearMap_injective
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  apply Module.Basis.ext_multilinear (fun _ => b.toBasis)
  intro v
  change α (fun i => b (v i)) = β (fun i => b (v i))
  have hv : (fun i => b (v i)) = ![b (v 0), b (v 1)] := by
    ext i; fin_cases i <;> rfl
  rw [hv]
  exact he (v 0) (v 1)

lemma coords_antiInvariant (b : OrthonormalBasis (Fin 4) ℝ E) (J : E →L[ℝ] E)
    (h0 : J (b 0) = b 1) (h1 : J (b 1) = -b 0)
    (h2 : J (b 2) = b 3) (h3 : J (b 3) = -b 2) (α : TwoForm E) :
    coords b (antiInvariant J α) = UnitaryFrame.antiInvariantPart (coords b α) := by
  have hc (u v : E) : (α.compContinuousLinearMap J) ![u,v] = α ![J u,J v] := by
    change α (fun i => J (![u,v] i)) = _
    congr 1; ext i; fin_cases i <;> rfl
  have hs := eval_swap α (b 0) (b 1)
  have ht := eval_swap α (b 2) (b 3)
  ext i
  fin_cases i <;>
    simp [coords, antiInvariant, UnitaryFrame.antiInvariantPart, UnitaryFrame.jAction, hc, h0,h1,h2,h3,
      eval_neg_left, eval_neg_right, hs, ht]

lemma coords_smul (b : OrthonormalBasis (Fin 4) ℝ E) (c : ℝ) (α : TwoForm E) :
    coords b (c • α) = c • coords b α := by
  ext i; fin_cases i <;> rfl

end TamingCompatibility.GeometricSymbol

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_Star
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set _root_.MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
open scoped BigOperators
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open ContinuousAlternatingMap
namespace TamingCompatibility.HodgeThree
open RealInnerProductSpace FormMetric ExteriorForms ContinuousAlternatingMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

section Frame
variable (b : OrthonormalBasis (Fin 4) ℝ E) (J : E →L[ℝ] E)
  (h0 : J (b 0) = b 1) (h1 : J (b 1) = -b 0)
  (h2 : J (b 2) = b 3) (h3 : J (b 3) = -b 2)
  (F : Form (E := E) 2) (hF : ∀ u v, F ![u,v] = ⟪J u,v⟫)

include h0 h1 h2 h3 hF in
omit [FiniteDimensional ℝ E] in
lemma volume_on_frame (i j : Fin 4) :
    (volumeSquare F).curryLeft (b i) (fun l => b (tripleIndices j l)) =
      if i = j then (-1 : ℝ) ^ (i : ℕ) else 0 := by
  have hb := orthonormal_iff_ite.mp b.orthonormal
  have ht : (volumeSquare F).curryLeft (b i) (fun l => b (tripleIndices j l)) =
      (volumeSquare F) ![b i, b (tripleIndices j 0), b (tripleIndices j 1),
        b (tripleIndices j 2)] := by
    change (volumeSquare F) (Matrix.vecCons (b i) (fun l => b (tripleIndices j l))) = _
    congr 1
    ext l
    fin_cases l <;> rfl
  rw [ht, volumeSquare_apply]
  fin_cases i <;> fin_cases j <;>
    simp [tripleIndices, hF, h0, h1, h2, h3, hb]
  norm_num

include h0 h1 h2 h3 hF in
lemma star_on_frame (α : Form (E := E) 3) (i : Fin 4) :
    star F α ![b i] = -((-1 : ℝ) ^ (i : ℕ) * α (fun l => b (tripleIndices i l))) := by
  rw [star_apply, pairing_three b]
  simp_rw [volume_on_frame b J h0 h1 h2 h3 F hF]
  simp [mul_comm]

end Frame

lemma star_zero (F : Form (E := E) 2) : star F 0 = 0 := by
  ext v
  have hv : v = ![v 0] := by ext i; fin_cases i; rfl
  rw [hv, star_apply]
  simp only [FormMetric.pairing, _root_.map_zero, inner_zero_left, neg_zero,
    ContinuousAlternatingMap.coe_zero, Pi.zero_apply]

end TamingCompatibility.HodgeThree

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_Form
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set _root_.MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
open scoped BigOperators
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open ContinuousAlternatingMap
namespace TamingCompatibility.MetricForms
open scoped BigOperators
open RealInnerProductSpace ContinuousAlternatingMap
open MetricModel
variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup D] [NormedSpace ℝ D]
  [FiniteDimensional ℝ D]

lemma pairing_two_comp (g : Metric E) (h : Metric D) (L : E ≃L[ℝ] D)
    (hL : ∀ u v, h.bilinear (L u) (L v) = g.bilinear u v)
    (hdim : Module.finrank ℝ E = 4) (α β : Form D 2) :
    pairing g (α.compContinuousLinearMap L) (β.compContinuousLinearMap L) =
      pairing h α β := by
  let b : OrthonormalBasis (Fin 4) ℝ (MetricModel.Model g) :=
    (stdOrthonormalBasis ℝ (MetricModel.Model g)).reindex (finCongr ((finrank_model g).trans hdim))
  rw [pairing, pairing, FormMetric.pairing_eq_sum b,
    FormMetric.pairing_eq_sum (b.map (isometryEquiv g h L hL))]
  simp only [comp_two, OrthonormalBasis.map_apply]
  rfl

end TamingCompatibility.MetricForms

namespace TamingCompatibility.HermitianHodge
open RealInnerProductSpace FormMetric GeometricSymbol UnitaryBasis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma pairing_coords (b : OrthonormalBasis (Fin 4) ℝ E)
    (α β : GeometricSymbol.TwoForm E) : pairing α β = ⟪coords b α, coords b β⟫ := by
  rw [pairing_eq_sum b]
  simp [coords, pairLeft, pairRight, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, Fin.sum_univ_succ]
  ring

def star (J : E →L[ℝ] E) (F α : GeometricSymbol.TwoForm E) : GeometricSymbol.TwoForm E :=
  pairing α F • F - α.compContinuousLinearMap J

omit [FiniteDimensional ℝ E] in
lemma coords_sub (b : OrthonormalBasis (Fin 4) ℝ E) (α β : GeometricSymbol.TwoForm E) :
    coords b (α - β) = coords b α - coords b β := by
  ext i
  fin_cases i <;> rfl

lemma unitary_star_formula (a : UnitaryFrame.W) :
    (a 0 + a 5) • UnitaryFrame.fundamental - UnitaryFrame.jAction a =
      UnitaryFrame.star a := by
  ext i
  fin_cases i <;>
    simp [UnitaryFrame.star, UnitaryFrame.fundamental, UnitaryFrame.jAction]

section UnitaryFrame
variable (b : OrthonormalBasis (Fin 4) ℝ E) (J : E →L[ℝ] E)
  (h0 : J (b 0) = b 1) (h1 : J (b 1) = -b 0)
  (h2 : J (b 2) = b 3) (h3 : J (b 3) = -b 2)

include h0 h1 h2 h3 in
omit [FiniteDimensional ℝ E] in
lemma coords_jAction (α : GeometricSymbol.TwoForm E) :
    coords b (α.compContinuousLinearMap J) = UnitaryFrame.jAction (coords b α) := by
  have hc (u v : E) : (α.compContinuousLinearMap J) ![u,v] = α ![J u,J v] := by
    change α (fun i => J (![u,v] i)) = _
    congr 1
    ext i
    fin_cases i <;> rfl
  have h10 := GeometricSymbol.eval_swap α (b 0) (b 1)
  have h32 := GeometricSymbol.eval_swap α (b 2) (b 3)
  ext i
  fin_cases i <;>
    simp [coords, UnitaryFrame.jAction, hc,
      h0, h1, h2, h3, GeometricSymbol.eval_neg_left, GeometricSymbol.eval_neg_right, h10, h32]

variable (F : GeometricSymbol.TwoForm E) (hF : ∀ u v, F ![u,v] = ⟪J u,v⟫)

include h0 h1 h2 hF in
omit [FiniteDimensional ℝ E] in
lemma coords_fundamental : coords b F = UnitaryFrame.fundamental := by
  have hb := orthonormal_iff_ite.mp b.orthonormal
  ext i
  fin_cases i <;> simp [coords, UnitaryFrame.fundamental, hF, h0, h1, h2, hb]

include h0 h1 h2 hF in
lemma pairing_fundamental (α : GeometricSymbol.TwoForm E) : pairing α F = coords b α 0 + coords b α 5 := by
  rw [pairing_coords b α F, coords_fundamental b J h0 h1 h2 F hF]
  simp [UnitaryFrame.fundamental, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    Fin.sum_univ_succ]

include h0 h1 h2 h3 hF in
lemma coords_star (α : GeometricSymbol.TwoForm E) : coords b (star J F α) = UnitaryFrame.star (coords b α) := by
  rw [star, coords_sub, coords_smul, coords_fundamental b J h0 h1 h2 F hF,
    coords_jAction b J h0 h1 h2 h3 α, pairing_fundamental b J h0 h1 h2 F hF]
  exact unitary_star_formula _

end UnitaryFrame

variable (J : E →ₗᵢ[ℝ] E) (hJ : ∀ u, J (J u) = -u)
  (hdim : Module.finrank ℝ E = 4) (F : GeometricSymbol.TwoForm E)
  (hF : ∀ u v, F ![u,v] = ⟪J u,v⟫)

include hJ hdim hF

lemma star_square (α : GeometricSymbol.TwoForm E) : star J.toContinuousLinearMap F (star J.toContinuousLinearMap F α) = α := by
  obtain ⟨b,h0,h1,h2,h3⟩ := exists_unitary_basis J hJ hdim
  apply coords_injective b
  rw [coords_star b _ h0 h1 h2 h3 F hF, coords_star b _ h0 h1 h2 h3 F hF,
    UnitaryFrame.star_square]

lemma star_self_adjoint (α β : GeometricSymbol.TwoForm E) :
    pairing (star J.toContinuousLinearMap F α) β = pairing α (star J.toContinuousLinearMap F β) := by
  obtain ⟨b,h0,h1,h2,h3⟩ := exists_unitary_basis J hJ hdim
  rw [pairing_coords b, pairing_coords b, coords_star b _ h0 h1 h2 h3 F hF,
    coords_star b _ h0 h1 h2 h3 F hF, UnitaryFrame.star_self_adjoint]

lemma star_antiInvariant (α : GeometricSymbol.TwoForm E) :
    star J.toContinuousLinearMap F (antiInvariant J.toContinuousLinearMap α) =
      antiInvariant J.toContinuousLinearMap α := by
  obtain ⟨b,h0,h1,h2,h3⟩ := exists_unitary_basis J hJ hdim
  apply coords_injective b
  rw [coords_star b _ h0 h1 h2 h3 F hF, coords_antiInvariant b _ h0 h1 h2 h3,
    UnitaryFrame.star_antiInvariantPart]

end TamingCompatibility.HermitianHodge

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_ContDiffLinearEmbedding
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
open scoped Manifold ContDiff
noncomputable section
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

namespace TamingCompatibility.ManifoldForms

open TamingCompatibility.FormSmoothness

variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X] {k : ℕ}

omit [IsManifold Model ∞ X] in
lemma pullback_add (α β : Form X k) (f : Space → X) :
    pullback (α + β) f = pullback α f + pullback β f := rfl

omit [IsManifold Model ∞ X] in
lemma Smooth.zero : Smooth (0 : Form X k) := by
  intro f U hU hf
  change ContDiffOn ℝ ∞ (fun _ : Space => (0 : Space [⋀^Fin k]→L[ℝ] ℝ)) U
  exact contDiffOn_const

omit [IsManifold Model ∞ X] in
lemma Smooth.add {α β : Form X k} (hα : Smooth α) (hβ : Smooth β) :
    Smooth (α + β) := by
  intro f U hU hf
  rw [pullback_add]
  exact (hα f U hU hf).add (hβ f U hU hf)

end TamingCompatibility.ManifoldForms

end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_MetricCoords
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
open scoped Manifold ContDiff
noncomputable section
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
noncomputable section
open scoped Manifold ContDiff Topology
open Bundle Filter Set
noncomputable section
open Set
namespace TamingCompatibility
open Bundle Set
open scoped Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X]

lemma metricCoords_chart_apply (J : AlmostComplexStructure X) (α : TwoForm X)
    (x : X) {z : Space} (hz : z ∈ (extChartAt Model x).target) (u v : Space) :
    metricCoords J α x ((extChartAt Model x).symm z) u v =
      ManifoldForms.pullback α (extChartAt Model x).symm z
        ![u, SmoothAlmostComplex.coord
          (⟨J.endomorphism, J.square, J.smooth⟩ : SmoothAlmostComplex.AlmostComplexStructure X)
          (trivializationAt Space (TangentSpace Model) x)
          ((extChartAt Model x).symm z) v] := by
  let e := extChartAt Model x
  let te := trivializationAt Space (TangentSpace Model) x
  have hs : e.symm z ∈ (chartAt Space x).source := by
    simpa only [e, extChartAt_source] using e.map_target hz
  have ht : e.symm z ∈ te.baseSet := by
    simpa only [te, TangentBundle.trivializationAt_baseSet] using hs
  have hd : mfderiv Model Model e.symm z = te.symmL ℝ (e.symm z) := by
    rw [TangentBundle.symmL_trivializationAt hs]
    change mfderiv Model Model e.symm z =
      mfderivWithin Model Model e.symm (Set.range Model) (e (e.symm z))
    rw [e.right_inv hz]
    simp only [Model, modelWithCornersSelf_coe, Set.range_id, mfderivWithin_univ]
  unfold metricCoords
  rw [inCoordinates_apply_eq₂ ht ht (Set.mem_univ _)]
  rw [associatedBilinear_apply]
  change (Bundle.Trivial.trivialization X ℝ).linearMapAt ℝ (e.symm z) _ = _
  rw [Bundle.Trivial.linearMapAt_trivialization, LinearMap.id_apply]
  change (α (e.symm z)) ![te.symm (e.symm z) u,
    J.endomorphism (e.symm z) (te.symm (e.symm z) v)] = _
  change _ = (α (e.symm z)) (fun i => mfderiv Model Model e.symm z
    (![u, te.continuousLinearMapAt ℝ (e.symm z) (J.endomorphism (e.symm z)
      (te.symmL ℝ (e.symm z) v))] i))
  rw [hd]
  apply congrArg (α (e.symm z))
  ext i
  fin_cases i
  · change te.symm (e.symm z) u = te.symmL ℝ (e.symm z) u
    exact (te.symmL_apply ht u).symm
  · change J.endomorphism (e.symm z) (te.symm (e.symm z) v) =
      te.symmL ℝ (e.symm z) (te.continuousLinearMapAt ℝ (e.symm z)
        (J.endomorphism (e.symm z) (te.symmL ℝ (e.symm z) v)))
    rw [te.symmL_continuousLinearMapAt ht, te.symmL_apply ht]

end TamingCompatibility

end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_UnitaryFrames
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set _root_.MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
open scoped BigOperators
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open ContinuousAlternatingMap
namespace TamingCompatibility.LocalUnitaryFrame
open Set Filter
open scoped Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma frame_gram (B : Bilinear E) (J : E →L[ℝ] E)
    (hB : ∀ u v, B u v = B v u)
    (hJ : ∀ u, J (J u) = -u) (hBJ : ∀ u v, B (J u) (J v) = B u v)
    (u w : E) (hu : B u u = 1) (hw : B w w = 1)
    (huw : B u w = 0) (hjuw : B (J u) w = 0) :
    ∀ i j : Fin 4, B (frame J u w i) (frame J u w j) = if i = j then 1 else 0 := by
  have huz := orthogonal_J B J hB hJ hBJ u
  have hwz := orthogonal_J B J hB hJ hBJ w
  have huw' : B u (J w) = 0 := by have h := skew B J hJ hBJ u w; linarith
  have hwu : B w u = 0 := by rw [hB, huw]
  have hwju : B w (J u) = 0 := by rw [hB, hjuw]
  have hjwu : B (J w) u = 0 := by rw [hB, huw']
  have hjuu : B (J u) u = 0 := by rw [hB, huz]
  have hjww : B (J w) w = 0 := by rw [hB, hwz]
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [frame, hu, hw, hBJ, huz, hwz, huw, hjuw, huw', hwu, hwju, hjwu, hjuu, hjww]

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
variable {B : D → Bilinear E} {v w : D → E} {J : D → E →L[ℝ] E}
variable {U : Set D}

lemma exists_smooth_frame_near (x₀ : D) (hU : IsOpen U) (hx : x₀ ∈ U)
    (hB : ContDiffOn ℝ ∞ B U) (hJ : ContDiffOn ℝ ∞ J U)
    (hBs : ∀ x ∈ U, ∀ u v, B x u v = B x v u)
    (hJs : ∀ x ∈ U, ∀ u, J x (J x u) = -u)
    (hBJ : ∀ x ∈ U, ∀ u v, B x (J x u) (J x v) = B x u v)
    (u₀ w₀ : E) (hu₀ : B x₀ u₀ u₀ = 1) (hw₀ : B x₀ w₀ w₀ = 1)
    (huw : B x₀ u₀ w₀ = 0) (hjuw : B x₀ (J x₀ u₀) w₀ = 0) :
    ∃ V : Set D, IsOpen V ∧ x₀ ∈ V ∧ V ⊆ U ∧
      ∃ u w : D → E, ContDiffOn ℝ ∞ u V ∧ ContDiffOn ℝ ∞ w V ∧
        u x₀ = u₀ ∧ w x₀ = w₀ ∧
        ∀ x ∈ V, ∀ i j : Fin 4,
          B x (frame (J x) (u x) (w x) i) (frame (J x) (u x) (w x) j) =
            if i = j then 1 else 0 := by
  let u : D → E := fun x => normalize (B x) u₀
  have hc : ContinuousOn (fun x => B x u₀ u₀) U :=
    (contDiffOn_evaluate hB contDiffOn_const contDiffOn_const).continuousOn
  let U₁ := {x ∈ U | 0 < B x u₀ u₀}
  have hopen : IsOpen U₁ := hc.isOpen_inter_preimage hU isOpen_Ioi
  have hx₁ : x₀ ∈ U₁ := ⟨hx, by simp [hu₀]⟩
  have hsub : U₁ ⊆ U := fun _ hx => hx.1
  have hu : ContDiffOn ℝ ∞ u U₁ :=
    contDiffOn_normalize (hB.mono hsub) contDiffOn_const (fun _ hx => hx.2)
  have hueq : u x₀ = u₀ := normalize_eq_of_unit _ _ hu₀
  let t : D → E := fun x => transverse (B x) (J x) (u x) w₀
  have ht : ContDiffOn ℝ ∞ t U₁ :=
    contDiffOn_transverse (hB.mono hsub) (hJ.mono hsub) hu contDiffOn_const
  have hteq : t x₀ = w₀ := by
    dsimp only [t]
    rw [hueq]
    exact transverse_eq _ _ _ _ huw hjuw
  have htc : ContinuousOn (fun x => B x (t x) (t x)) U₁ :=
    (contDiffOn_evaluate (hB.mono hsub) ht ht).continuousOn
  let V := {x ∈ U₁ | 0 < B x (t x) (t x)}
  have hV : IsOpen V := htc.isOpen_inter_preimage hopen isOpen_Ioi
  have hxV : x₀ ∈ V := ⟨hx₁, by rw [hteq, hw₀]; norm_num⟩
  have hVU : V ⊆ U₁ := fun _ hx => hx.1
  let w : D → E := fun x => normalize (B x) (t x)
  have hw : ContDiffOn ℝ ∞ w V :=
    contDiffOn_normalize (hB.mono (fun _ hx => hsub (hVU hx))) (ht.mono hVU) (fun _ hx => hx.2)
  refine ⟨V,hV,hxV,(fun _ hx => hsub (hVU hx)),u,w,hu.mono hVU,hw,hueq,?_,?_⟩
  · dsimp only [w]
    rw [hteq]
    exact normalize_eq_of_unit _ _ hw₀
  · intro x hxV
    have hxU : x ∈ U := hsub (hVU hxV)
    have hun : B x (u x) (u x) = 1 := normalize_unit _ _ hxV.1.2
    have hwn : B x (w x) (w x) = 1 := normalize_unit _ _ hxV.2
    have horth := transverse_orthogonal (B x) (J x) (hBs x hxU)
      (hJs x hxU) (hBJ x hxU) (u x) w₀ hun
    apply frame_gram (B x) (J x) (hBs x hxU) (hJs x hxU) (hBJ x hxU)
      (u x) (w x) hun hwn
    · change B x (u x) ((Real.sqrt (B x (t x) (t x)))⁻¹ • t x) = 0
      simp only [map_smul, smul_eq_mul]
      exact mul_eq_zero.mpr (Or.inr horth.1)
    · change B x (J x (u x)) ((Real.sqrt (B x (t x) (t x)))⁻¹ • t x) = 0
      simp only [map_smul, smul_eq_mul]
      exact mul_eq_zero.mpr (Or.inr horth.2)

end TamingCompatibility.LocalUnitaryFrame

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_FormEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set _root_.MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
open scoped BigOperators
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open ContinuousAlternatingMap
namespace TamingCompatibility.MetricHodge
open ContinuousAlternatingMap MetricForms MetricModel ExteriorForms
variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup D] [NormedSpace ℝ D]
  [FiniteDimensional ℝ D]

variable (g : Metric E) (J : E →L[ℝ] E)
  (hJ : ∀ u, J (J u) = -u)
  (horth : ∀ u v, g.bilinear (J u) (J v) = g.bilinear u v)
  (hdim : Module.finrank ℝ E = 4) (F : MetricForms.Form E 2)
  (hF : ∀ u v, F ![u,v] = g.bilinear (J u) v)

include hJ horth hdim hF

omit hJ horth hdim hF in
lemma starThree_zero : starThree g F 0 = 0 := by
  rw [starThree,_root_.map_zero,HodgeThree.star_zero,_root_.map_zero]

end TamingCompatibility.MetricHodge

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_UnitaryVectors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set _root_.MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
open scoped BigOperators
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open ContinuousAlternatingMap
namespace TamingCompatibility.SmoothMetric
open RealInnerProductSpace MetricModel MetricForms FormSmooth LocalUnitaryFrame
open scoped ContDiff BigOperators
variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup D] [NormedSpace ℝ D]

lemma exists_unitary_vectors (g : Metric E) (J : E →L[ℝ] E)
    (hJ : ∀ u, J (J u) = -u) (hBJ : ∀ u v, g.bilinear (J u) (J v) = g.bilinear u v)
    (hdim : Module.finrank ℝ E = 4) :
    ∃ u w : E, g.bilinear u u = 1 ∧ g.bilinear w w = 1 ∧
      g.bilinear u w = 0 ∧ g.bilinear (J u) w = 0 := by
  let j := MetricModel.isometry g J hBJ
  have hj : ∀ u : MetricModel.Model g, j (j u) = -u := hJ
  obtain ⟨b,h0,h1,h2,h3⟩ := UnitaryBasis.exists_unitary_basis j hj ((finrank_model g).trans hdim)
  refine ⟨equiv g (b 0), equiv g (b 2), ?_, ?_, ?_, ?_⟩
  · exact (orthonormal_iff_ite.mp b.orthonormal 0 0).trans (ite_eq_left rfl)
  · exact (orthonormal_iff_ite.mp b.orthonormal 2 2).trans (ite_eq_left rfl)
  · exact (orthonormal_iff_ite.mp b.orthonormal 0 2).trans (ite_eq_right (by decide))
  · change ⟪j (b 0), b 2⟫ = 0
    rw [h0]
    exact (orthonormal_iff_ite.mp b.orthonormal 1 2).trans (ite_eq_right (by decide))

lemma exists_orthonormalFrame_near (g : D → Metric E) (J : D → E →L[ℝ] E)
    (hdim : Module.finrank ℝ E = 4) {U : Set D} (hU : IsOpen U)
    (hg : ContDiffOn ℝ ∞ (fun x => (g x).bilinear) U) (hJ : ContDiffOn ℝ ∞ J U)
    (hJs : ∀ x ∈ U, ∀ u, J x (J x u) = -u)
    (hgJ : ∀ x ∈ U, ∀ u v, (g x).bilinear (J x u) (J x v) = (g x).bilinear u v)
    {x : D} (hx : x ∈ U) :
    ∃ V : Set D, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      ∃ b : Fin 4 → D → E, (∀ i, ContDiffOn ℝ ∞ (b i) V) ∧
        ∀ y ∈ V, ∀ i j, (g y).bilinear (b i y) (b j y) = if i = j then 1 else 0 := by
  obtain ⟨u₀,w₀,hu,hw,huw,hjuw⟩ := exists_unitary_vectors (g x) (J x) (hJs x hx) (hgJ x hx) hdim
  obtain ⟨V,hV,hxV,hVU,u,w,hus,hws,_,_,hgram⟩ :=
    exists_smooth_frame_near (B := fun y => (g y).bilinear) x hU hx hg hJ
      (fun y _ => (g y).symm) hJs hgJ u₀ w₀ hu hw huw hjuw
  refine ⟨V,hV,hxV,hVU,(fun i y => frame (J y) (u y) (w y) i),?_,hgram⟩
  intro i
  fin_cases i
  · exact hus
  · exact (hJ.mono hVU).clm_apply hus
  · exact hws
  · exact (hJ.mono hVU).clm_apply hws

lemma contDiffOn_pairing_two_frame (g : D → Metric E) (hdim : Module.finrank ℝ E = 4)
    {U : Set D} (b : Fin 4 → D → E) (hbs : ∀ i, ContDiffOn ℝ ∞ (b i) U)
    (hb : ∀ x ∈ U, ∀ i j, (g x).bilinear (b i x) (b j x) = if i = j then 1 else 0)
    {α β : D → Form E 2} (hα : ContDiffOn ℝ ∞ α U) (hβ : ContDiffOn ℝ ∞ β U) :
    ContDiffOn ℝ ∞ (fun x => pairing (g x) (α x) (β x)) U := by
  have hs : ContDiffOn ℝ ∞ (fun x => ∑ i : Fin 6,
      α x ![b (FormMetric.pairLeft i) x,b (FormMetric.pairRight i) x] *
      β x ![b (FormMetric.pairLeft i) x,b (FormMetric.pairRight i) x]) U := by
    apply ContDiffOn.sum
    intro i hi
    exact (contDiffOn_apply_two hα (hbs _) (hbs _)).mul
      (contDiffOn_apply_two hβ (hbs _) (hbs _))
  exact hs.congr (fun x hx => pairing_two_eq_sum (g x) hdim (fun i => b i x) (hb x hx) _ _)

lemma contDiffOn_pairing_three_frame (g : D → Metric E) (hdim : Module.finrank ℝ E = 4)
    {U : Set D} (b : Fin 4 → D → E) (hbs : ∀ i, ContDiffOn ℝ ∞ (b i) U)
    (hb : ∀ x ∈ U, ∀ i j, (g x).bilinear (b i x) (b j x) = if i = j then 1 else 0)
    {α β : D → Form E 3} (hα : ContDiffOn ℝ ∞ α U) (hβ : ContDiffOn ℝ ∞ β U) :
    ContDiffOn ℝ ∞ (fun x => pairing (g x) (α x) (β x)) U := by
  have hs : ContDiffOn ℝ ∞ (fun x => ∑ i : Fin 4,
      α x (fun j => b (FormMetric.tripleIndices i j) x) *
      β x (fun j => b (FormMetric.tripleIndices i j) x)) U := by
    apply ContDiffOn.sum
    intro i hi
    exact (contDiffOn_apply hα (fun j => hbs _)).mul
      (contDiffOn_apply hβ (fun j => hbs _))
  exact hs.congr (fun x hx => pairing_three_eq_sum (g x) hdim (fun i => b i x) (hb x hx) _ _)

lemma contDiffOn_pairing_two (g : D → Metric E) (J : D → E →L[ℝ] E)
    (hdim : Module.finrank ℝ E = 4) {U : Set D} (hU : IsOpen U)
    (hg : ContDiffOn ℝ ∞ (fun x => (g x).bilinear) U) (hJ : ContDiffOn ℝ ∞ J U)
    (hJs : ∀ x ∈ U, ∀ u, J x (J x u) = -u)
    (hgJ : ∀ x ∈ U, ∀ u v, (g x).bilinear (J x u) (J x v) = (g x).bilinear u v)
    {α β : D → Form E 2} (hα : ContDiffOn ℝ ∞ α U) (hβ : ContDiffOn ℝ ∞ β U) :
    ContDiffOn ℝ ∞ (fun x => pairing (g x) (α x) (β x)) U := by
  apply contDiffOn_of_locally_contDiffOn
  intro x hx
  obtain ⟨V,hV,hxV,hVU,b,hbs,hb⟩ := exists_orthonormalFrame_near g J hdim hU hg hJ hJs hgJ hx
  exact ⟨V,hV,hxV,(contDiffOn_pairing_two_frame g hdim b hbs hb
    (hα.mono hVU) (hβ.mono hVU)).mono Set.inter_subset_right⟩

lemma contDiffOn_pairing_three (g : D → Metric E) (J : D → E →L[ℝ] E)
    (hdim : Module.finrank ℝ E = 4) {U : Set D} (hU : IsOpen U)
    (hg : ContDiffOn ℝ ∞ (fun x => (g x).bilinear) U) (hJ : ContDiffOn ℝ ∞ J U)
    (hJs : ∀ x ∈ U, ∀ u, J x (J x u) = -u)
    (hgJ : ∀ x ∈ U, ∀ u v, (g x).bilinear (J x u) (J x v) = (g x).bilinear u v)
    {α β : D → Form E 3} (hα : ContDiffOn ℝ ∞ α U) (hβ : ContDiffOn ℝ ∞ β U) :
    ContDiffOn ℝ ∞ (fun x => pairing (g x) (α x) (β x)) U := by
  apply contDiffOn_of_locally_contDiffOn
  intro x hx
  obtain ⟨V,hV,hxV,hVU,b,hbs,hb⟩ := exists_orthonormalFrame_near g J hdim hU hg hJ hJs hgJ hx
  exact ⟨V,hV,hxV,(contDiffOn_pairing_three_frame g hdim b hbs hb
    (hα.mono hVU) (hβ.mono hVU)).mono Set.inter_subset_right⟩

end TamingCompatibility.SmoothMetric

namespace TamingCompatibility.SmoothHodge
open ContinuousAlternatingMap MetricForms MetricModel MetricHodge FormSmooth
open scoped ContDiff
variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup D] [NormedSpace ℝ D]

lemma volumeSquare_contDiffOn {F : D → MetricForms.Form E 2} {U : Set D}
    (hF : ContDiffOn ℝ ∞ F U) : ContDiffOn ℝ ∞ (fun x => ExteriorForms.volumeSquare (F x)) U := by
  apply contDiffOn_of_basis (Module.finBasis ℝ E)
  intro a
  have he : (fun i => Module.finBasis ℝ E (a i)) =
      ![Module.finBasis ℝ E (a 0),Module.finBasis ℝ E (a 1),
        Module.finBasis ℝ E (a 2),Module.finBasis ℝ E (a 3)] := by
    ext i; fin_cases i <;> rfl
  simp only [he,ExteriorForms.volumeSquare_apply]
  exact ((contDiffOn_apply_two hF contDiffOn_const contDiffOn_const).mul
    (contDiffOn_apply_two hF contDiffOn_const contDiffOn_const)).sub
    ((contDiffOn_apply_two hF contDiffOn_const contDiffOn_const).mul
    (contDiffOn_apply_two hF contDiffOn_const contDiffOn_const)) |>.add
    ((contDiffOn_apply_two hF contDiffOn_const contDiffOn_const).mul
    (contDiffOn_apply_two hF contDiffOn_const contDiffOn_const))

end TamingCompatibility.SmoothHodge

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_GramOrthonormalBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set _root_.MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
open scoped BigOperators
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open ContinuousAlternatingMap
namespace TamingCompatibility.VolumeNormalization
open ContinuousAlternatingMap MetricModel MetricForms ExteriorForms MetricDensity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma gram_orthonormal_basis (g : Metric E) (b c : Module.Basis (Fin 4) ℝ E)
    (hc : ∀ i j, g.bilinear (c i) (c j) = if i = j then 1 else 0) :
    gram b g.bilinear = (c.toMatrix b).transpose * c.toMatrix b := by
  ext i j
  change g.bilinear (b i) (b j) = _
  conv_lhs => rw [← c.sum_repr (b i), ← c.sum_repr (b j)]
  simp only [_root_.map_sum,_root_.map_smul,_root_.sum_apply,_root_.smul_apply,smul_eq_mul,hc,
    mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true, if_true,
    Matrix.mul_apply,Matrix.transpose_apply,Module.Basis.toMatrix_apply]
  apply Finset.sum_congr rfl
  intro l _
  ring

omit [FiniteDimensional ℝ E] in
lemma abs_eval_of_orthonormal (g : Metric E) (b c : Module.Basis (Fin 4) ℝ E)
    (hc : ∀ i j, g.bilinear (c i) (c j) = if i = j then 1 else 0)
    (ν : MetricForms.Form E 4) (hν : ν c = 1) :
    |ν b| = density (gram b g.bilinear) := by
  rw [TopForms.eval_eq_det_mul c ν b,hν,one_mul,Module.Basis.det_apply,
    gram_orthonormal_basis g b c hc,density,Matrix.det_mul,Matrix.det_transpose]
  rw [← pow_two,Real.sqrt_sq_eq_abs]

lemma exists_metric_unitary_basis (g : Metric E) (J : E →L[ℝ] E)
    (hJ : ∀ u, J (J u) = -u)
    (horth : ∀ u v, g.bilinear (J u) (J v) = g.bilinear u v)
    (hdim : Module.finrank ℝ E = 4) :
    ∃ b : Module.Basis (Fin 4) ℝ E,
      (∀ i j, g.bilinear (b i) (b j) = if i = j then 1 else 0) ∧
      J (b 0) = b 1 ∧ J (b 1) = -b 0 ∧ J (b 2) = b 3 ∧ J (b 3) = -b 2 := by
  obtain ⟨b,h0,h1,h2,h3⟩ := UnitaryBasis.exists_unitary_basis (isometry g J horth) hJ
    ((finrank_model g).trans hdim)
  refine ⟨b.toBasis.map (linearEquiv g), ?_,h0,h1,h2,h3⟩
  intro i j
  exact orthonormal_iff_ite.mp b.orthonormal i j

omit [FiniteDimensional ℝ E] in
lemma volume_on_frame (g : Metric E) (J : E →L[ℝ] E)
    (b : Module.Basis (Fin 4) ℝ E)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i = j then 1 else 0)
    (h0 : J (b 0) = b 1) (h1 : J (b 1) = -b 0)
    (h2 : J (b 2) = b 3) (_h3 : J (b 3) = -b 2)
    (F : MetricForms.Form E 2) (hF : ∀ u v, F ![u,v] = g.bilinear (J u) v) :
    volumeSquare F b = 1 := by
  have he : (b : Fin 4 → E) = ![b 0,b 1,b 2,b 3] := by ext i; fin_cases i <;> rfl
  rw [he,volumeSquare_apply]
  simp [hF,h0,h1,h2,hb]

lemma abs_volume_eq_density (g : Metric E) (J : E →L[ℝ] E)
    (hJ : ∀ u, J (J u) = -u)
    (horth : ∀ u v, g.bilinear (J u) (J v) = g.bilinear u v)
    (hdim : Module.finrank ℝ E = 4) (F : MetricForms.Form E 2)
    (hF : ∀ u v, F ![u,v] = g.bilinear (J u) v)
    (b : Module.Basis (Fin 4) ℝ E) :
    |volumeSquare F b| = density (gram b g.bilinear) := by
  obtain ⟨c,hc,h0,h1,h2,h3⟩ := exists_metric_unitary_basis g J hJ horth hdim
  exact abs_eval_of_orthonormal g b c hc _ (volume_on_frame g J c hc h0 h1 h2 h3 F hF)

lemma volume_ne_zero (g : Metric E) (J : E →L[ℝ] E)
    (hJ : ∀ u, J (J u) = -u)
    (horth : ∀ u v, g.bilinear (J u) (J v) = g.bilinear u v)
    (hdim : Module.finrank ℝ E = 4) (F : MetricForms.Form E 2)
    (hF : ∀ u v, F ![u,v] = g.bilinear (J u) v) : volumeSquare F ≠ 0 := by
  obtain ⟨c,hc,h0,h1,h2,h3⟩ := exists_metric_unitary_basis g J hJ horth hdim
  intro h
  have he := volume_on_frame g J c hc h0 h1 h2 h3 F hF
  rw [h] at he
  change (0 : ℝ) = 1 at he
  norm_num at he

end TamingCompatibility.VolumeNormalization

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_Sign
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set _root_.MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
open scoped BigOperators
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open ContinuousAlternatingMap
namespace TamingCompatibility.OrientationSign
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma abs_mul_div (t a : ℝ) (ht : t ≠ 0) : |t| * (a / t) = sign t * a := by
  by_cases h : 0 < t
  · rw [abs_of_pos h,sign,ite_eq_left h]
    field_simp
  · have hn : t < 0 := lt_of_le_of_ne (le_of_not_gt h) ht
    rw [abs_of_neg hn,sign,ite_eq_right h]
    field_simp

omit [NormedSpace ℝ E] in
lemma locally_constant {U : Set E} (hU : IsOpen U) {f : E → ℝ}
    (hf : ContinuousOn f U) {x : E} (hx : x ∈ U) (hn : f x ≠ 0) :
    (fun y => sign (f y)) =ᶠ[𝓝 x] (fun _ => sign (f x)) := by
  have hc := (hf x hx).continuousAt (hU.mem_nhds hx)
  by_cases h : 0 < f x
  · filter_upwards [continuousAt_const.eventually_lt hc h] with y hy
    simp only [sign,ite_eq_left h,ite_eq_left hy]
  · have hp : f x < 0 := lt_of_le_of_ne (le_of_not_gt h) hn
    filter_upwards [hc.eventually_lt continuousAt_const hp] with y hy
    simp only [sign,ite_eq_right h,ite_eq_right (not_lt_of_ge hy.le)]

lemma contDiffOn {U : Set E} (hU : IsOpen U) {f : E → ℝ}
    (hf : ContinuousOn f U) (hn : ∀ x ∈ U, f x ≠ 0) :
    ContDiffOn ℝ ∞ (fun x => sign (f x)) U := by
  intro x hx
  exact (contDiffAt_const.congr_of_eventuallyEq (locally_constant hU hf hx (hn x hx))).contDiffWithinAt

lemma extDeriv_smul {U : Set E} (hU : IsOpen U) {f : E → ℝ}
    (hf : ContinuousOn f U) {x : E} (hx : x ∈ U) (hn : f x ≠ 0)
    {k : ℕ} (α : E → E [⋀^Fin k]→L[ℝ] ℝ) :
    extDeriv (fun y => sign (f y) • α y) x = sign (f x) • extDeriv α x := by
  have he : (fun y => sign (f y) • α y) =ᶠ[𝓝 x] (fun y => sign (f x) • α y) :=
    (locally_constant hU hf hx hn).smul (Filter.EventuallyEq.refl _ _)
  rw [he.extDeriv_eq]
  exact _root_.extDeriv_fun_smul (sign (f x)) α

end TamingCompatibility.OrientationSign

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_FunSmul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set _root_.MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
open scoped BigOperators
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open ContinuousAlternatingMap
namespace TamingCompatibility.ManifoldForms
open Bundle ContinuousAlternatingMap
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X] {k : ℕ}

omit [IsManifold Model ∞ X] in
lemma Smooth.fun_smul {f : X → ℝ} (hf : ContMDiff Model 𝓘(ℝ,ℝ) ∞ f)
    {β : Form X k} (hβ : Smooth β) : Smooth (fun x => f x • β x) := by
  intro g U hU hg
  change ContDiffOn ℝ ∞ (fun z => f (g z) • pullback β g z) U
  exact (hf.comp_contMDiffOn hg).contDiffOn.smul (hβ g U hU hg)

omit [IsManifold Model ∞ X] in
lemma exteriorDerivative_eq_zero_of_eventually (β : Form X k) (x : X)
    (hβ : ∀ᶠ y in 𝓝 x, β y = 0) : exteriorDerivative β x = 0 := by
  have h : pullback β (extChartAt Model x).symm =ᶠ[𝓝 ((extChartAt Model x) x)]
      (fun _ => (0 : Space [⋀^Fin k]→L[ℝ] ℝ)) := by
    have hc := continuousAt_extChartAt_symm (I := Model) x
    have hβ' : ∀ᶠ y in 𝓝 ((extChartAt Model x).symm ((extChartAt Model x) x)), β y = 0 := by
      rwa [(extChartAt Model x).left_inv (mem_extChartAt_source x)]
    filter_upwards [hc.eventually hβ'] with z hz
    simp only [pullback,hz]
    ext v
    rfl
  change extDeriv (pullback β (extChartAt Model x).symm) ((extChartAt Model x) x) = 0
  rw [h.extDeriv_eq]
  simp [extDeriv,← alternatizeUncurryFinCLM_apply]

omit [IsManifold Model ∞ X] in
lemma exteriorDerivative_fun_smul_vanishes {f : X → ℝ} (β : Form X k) {x : X}
    (hx : x ∉ tsupport f) : exteriorDerivative (fun y => f y • β y) x = 0 := by
  apply exteriorDerivative_eq_zero_of_eventually
  filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hx] with y hy
  rw [image_eq_zero_of_notMem_tsupport hy,zero_smul]

end TamingCompatibility.ManifoldForms

namespace TamingCompatibility.SignedStokes
open _root_.MeasureTheory Set ContinuousAlternatingMap
open scoped ContDiff Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

lemma integral_extDeriv_on_open {k : ℕ} {U K : Set E} (hU : IsOpen U)
    (hK : IsCompact K) (hKU : K ⊆ U) {ν : E → ℝ}
    (hν : ContDiffOn ℝ ∞ ν U) (hn : ∀ x ∈ U, ν x ≠ 0)
    {β : E → E [⋀^Fin k]→L[ℝ] ℝ} (hβ : ContDiffOn ℝ ∞ β U)
    (hz : ∀ x ∈ U, x ∉ K → β x = 0) (v : Fin (k+1) → E) :
    (∫ x in U, OrientationSign.sign (ν x) * extDeriv β x v ∂μ) = 0 := by
  let G : E → E [⋀^Fin k]→L[ℝ] ℝ := U.indicator (fun x => OrientationSign.sign (ν x) • β x)
  have hGz (x : E) (hx : x ∉ K) : G x = 0 := by
    by_cases hxU : x ∈ U
    · rw [show G x = OrientationSign.sign (ν x) • β x from indicator_of_mem hxU _,hz x hxU hx,smul_zero]
    · exact indicator_of_notMem hxU _
  have hG := ManifoldLocalization.smooth_indicator_of_compact hU hK hKU
    ((OrientationSign.contDiffOn hU hν.continuousOn hn).smul hβ)
    (fun x hx hxK => by change OrientationSign.sign (ν x) • β x = 0; rw [hz x hx hxK,smul_zero])
  have he (x : E) : extDeriv G x = U.indicator
      (fun y => OrientationSign.sign (ν y) • extDeriv β y) x := by
    by_cases hx : x ∈ U
    · have hg : G =ᶠ[𝓝 x] (fun y => OrientationSign.sign (ν y) • β y) := by
        filter_upwards [hU.mem_nhds hx] with y hy
        exact indicator_of_mem hy _
      rw [hg.extDeriv_eq,OrientationSign.extDeriv_smul hU hν.continuousOn hx (hn x hx),indicator_of_mem hx]
    · have hxK : x ∉ K := fun h => hx (hKU h)
      have hg : G =ᶠ[𝓝 x] (fun _ => (0 : E [⋀^Fin k]→L[ℝ] ℝ)) := by
        filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hxK] with y hy
        exact hGz y hy
      rw [hg.extDeriv_eq,indicator_of_notMem hx]
      simp [extDeriv,← alternatizeUncurryFinCLM_apply]
  rw [← integral_indicator hU.measurableSet]
  have hev : U.indicator (fun x => OrientationSign.sign (ν x) * extDeriv β x v) =
      fun x => extDeriv G x v := by
    funext x
    rw [he]
    by_cases hx : x ∈ U
    · rw [indicator_of_mem hx,indicator_of_mem hx]
      rfl
    · simp only [indicator_of_notMem hx,ContinuousAlternatingMap.coe_zero,Pi.zero_apply]
  rw [hev]
  exact EuclideanStokes.integral_extDeriv_eq_zero hG.1 hG.2 v

end TamingCompatibility.SignedStokes

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_SingleFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set _root_.MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
open scoped BigOperators
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open ContinuousAlternatingMap

namespace TamingCompatibility.WedgePairing
open RealInnerProductSpace ContinuousAlternatingMap ExteriorForms FormMetric GeometricSymbol
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma top_ext (b : Module.Basis (Fin 4) ℝ E) {a c : Form (E := E) 4} (h : a b = c b) : a = c := by
  ext v
  rw [TopForms.eval_eq_det_mul b a v,TopForms.eval_eq_det_mul b c v,h]

section Frame
variable (b : OrthonormalBasis (Fin 4) ℝ E) (J : E →L[ℝ] E)
  (h0 : J (b 0) = b 1) (h1 : J (b 1) = -b 0)
  (h2 : J (b 2) = b 3) (h3 : J (b 3) = -b 2)
  (F : Form (E := E) 2) (hF : ∀ u v, F ![u,v] = ⟪J u,v⟫)
include h0 h1 h2 h3 hF

omit [FiniteDimensional ℝ E] in
lemma volume_on_frame : volumeSquare F b = 1 := by
  have h := HodgeThree.volume_on_frame b J h0 h1 h2 h3 F hF 0 0
  have he : Matrix.vecCons (b 0) (fun l => b (FormMetric.tripleIndices 0 l)) = (b : Fin 4 → E) := by
    ext i
    fin_cases i <;> rfl
  change volumeSquare F (Matrix.vecCons (b 0) (fun l => b (FormMetric.tripleIndices 0 l))) = _ at h
  simpa only [he,ite_true, if_true,Fin.val_zero,pow_zero] using h

end Frame

end TamingCompatibility.WedgePairing

namespace TamingCompatibility.MetricWedgePairing
open ContinuousAlternatingMap ExteriorForms MetricHodge MetricModel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma formEquiv_volume (g : Metric E) (F : ExteriorForms.Form (E := E) 2) :
    formEquiv g 4 (volumeSquare F) = volumeSquare (formEquiv g 2 F) := by
  exact (MetricHodge.volumeSquare_comp F (equiv g).toContinuousLinearMap).symm

end TamingCompatibility.MetricWedgePairing

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_Wedge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set _root_.MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
open scoped BigOperators
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open ContinuousAlternatingMap
namespace TamingCompatibility.ManifoldForms
open Bundle ContinuousAlternatingMap
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X] {k : ℕ}

lemma pullback_at_center (a : Form X k) (x : X) :
    pullback a (extChartAt Model x).symm ((extChartAt Model x) x) = a x := by
  have hd : mfderiv Model Model (extChartAt Model x).symm ((extChartAt Model x) x) =
      ContinuousLinearMap.id ℝ Space := by
    have h := mfderivWithin_range_extChartAt_symm (I := Model) (x := x)
    simp only [Model,modelWithCornersSelf_coe,Set.range_id,mfderivWithin_univ] at h
    ext v
    exact congrArg (fun L => L v) h
  ext v
  change (a ((extChartAt Model x).symm ((extChartAt Model x) x)))
    (fun i => mfderiv Model Model (extChartAt Model x).symm ((extChartAt Model x) x) (v i)) = (a x) v
  rw [hd,(extChartAt Model x).left_inv (mem_extChartAt_source x)]
  rfl

end TamingCompatibility.ManifoldForms

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_ComplexEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set _root_.MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
open scoped BigOperators
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open ContinuousAlternatingMap

namespace TamingCompatibility.MetricForms
open ContinuousAlternatingMap MetricModel
variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup D] [NormedSpace ℝ D]
  [FiniteDimensional ℝ D]
omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ D] in
lemma comp_one (α : Form D 1) (L : E →L[ℝ] D) (u : E) :
    (α.compContinuousLinearMap L) ![u] = α ![L u] := by
  change α (fun i => L (![u] i)) = _
  congr 1
  ext i
  fin_cases i
  rfl
lemma pairing_one_comp (g : Metric E) (h : Metric D) (L : E ≃L[ℝ] D)
    (hL : ∀ u v, h.bilinear (L u) (L v) = g.bilinear u v)
    (hdim : Module.finrank ℝ E = 4) (α β : Form D 1) :
    pairing g (α.compContinuousLinearMap L) (β.compContinuousLinearMap L) = pairing h α β := by
  let b : OrthonormalBasis (Fin 4) ℝ (MetricModel.Model g) :=
    (stdOrthonormalBasis ℝ (MetricModel.Model g)).reindex (finCongr ((finrank_model g).trans hdim))
  rw [pairing,pairing,FormMetric.pairing_one b,
    FormMetric.pairing_one (b.map (isometryEquiv g h L hL))]
  simp only [comp_one,OrthonormalBasis.map_apply]
  rfl
end TamingCompatibility.MetricForms

namespace TamingCompatibility.SmoothMetric
open MetricModel MetricForms FormSmooth
open scoped ContDiff
variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup D] [NormedSpace ℝ D]
lemma contDiffOn_pairing_one_frame (g : D → Metric E) (hdim : Module.finrank ℝ E = 4)
    {U : Set D} (b : Fin 4 → D → E) (hbs : ∀ i, ContDiffOn ℝ ∞ (b i) U)
    (hb : ∀ x ∈ U, ∀ i j, (g x).bilinear (b i x) (b j x) = if i = j then 1 else 0)
    {α β : D → Form E 1} (hα : ContDiffOn ℝ ∞ α U) (hβ : ContDiffOn ℝ ∞ β U) :
    ContDiffOn ℝ ∞ (fun x => pairing (g x) (α x) (β x)) U := by
  have hs : ContDiffOn ℝ ∞ (fun x => ∑ i : Fin 4, α x ![b i x] * β x ![b i x]) U := by
    apply ContDiffOn.sum
    intro i hi
    have he (x : D) : ![b i x] = (fun _ : Fin 1 => b i x) := by ext j; fin_cases j; rfl
    simp_rw [he]
    exact (contDiffOn_apply hα (fun _ => hbs i)).mul (contDiffOn_apply hβ (fun _ => hbs i))
  exact hs.congr (fun x hx => pairing_one_eq_sum (g x) hdim (fun i => b i x) (hb x hx) _ _)
lemma contDiffOn_pairing_one (g : D → Metric E) (J : D → E →L[ℝ] E)
    (hdim : Module.finrank ℝ E = 4) {U : Set D} (hU : IsOpen U)
    (hg : ContDiffOn ℝ ∞ (fun x => (g x).bilinear) U) (hJ : ContDiffOn ℝ ∞ J U)
    (hJs : ∀ x ∈ U, ∀ u, J x (J x u) = -u)
    (hgJ : ∀ x ∈ U, ∀ u v, (g x).bilinear (J x u) (J x v) = (g x).bilinear u v)
    {α β : D → Form E 1} (hα : ContDiffOn ℝ ∞ α U) (hβ : ContDiffOn ℝ ∞ β U) :
    ContDiffOn ℝ ∞ (fun x => pairing (g x) (α x) (β x)) U := by
  apply contDiffOn_of_locally_contDiffOn
  intro x hx
  obtain ⟨V,hV,hxV,hVU,b,hbs,hb⟩ := exists_orthonormalFrame_near g J hdim hU hg hJ hJs hgJ hx
  exact ⟨V,hV,hxV,(contDiffOn_pairing_one_frame g hdim b hbs hb
    (hα.mono hVU) (hβ.mono hVU)).mono Set.inter_subset_right⟩
end TamingCompatibility.SmoothMetric

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_LocalMatrixOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section

noncomputable section
namespace TamingCompatibility.LocalMatrixOperator
open MetricModel MetricForms MetricHodge ExteriorForms ContinuousAlternatingMap
open EuclideanEnergy
open scoped ContDiff RealInnerProductSpace SchwartzMap

def oneVector : MetricForms.Form V 1 →L[ℝ] V :=
  (InnerProductSpace.toDual ℝ V).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    (ofSubsingletonLIE (0 : Fin 1)).symm.toContinuousLinearEquiv.toContinuousLinearMap

def combine {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] (u v : D) : Pair →L[ℝ] D :=
  (EuclideanSpace.proj (0 : Fin 2)).smulRight u + (EuclideanSpace.proj (1 : Fin 2)).smulRight v
lemma combine_pair {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] (u v : D) (a b : ℝ) :
    combine u v (pair a b) = a • u + b • v := rfl

lemma covector_expansion (ξ : V →L[ℝ] ℝ) : ξ = ∑ i, (ξ (e i)) • EuclideanSpace.proj i := by
  ext x
  have he := (EuclideanSpace.basisFun (Fin 4) ℝ).sum_repr x
  have hv : (∑ i, x i • e i) = x := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply, e] using he
  calc
    ξ x = ξ (∑ i, x i • e i) := congrArg ξ hv.symm
    _ = ∑ i, x i * ξ (e i) := by simp only [_root_.map_sum,map_smul,smul_eq_mul]
    _ = _ := by simp [mul_comm]

end TamingCompatibility.LocalMatrixOperator

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_DirectionalEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section

noncomputable section

namespace TamingCompatibility.LocalMatrixOperator
open EuclideanEnergy MetricForms ExteriorForms MetricHodge AntiInvariantFrame
open scoped RealInnerProductSpace SchwartzMap LineDeriv

def oneCoordinates (b : Fin 4 → V) (a : MetricForms.Form V 1) : V :=
  WithLp.toLp 2 (fun i => a ![b i])

def evaluationConstant (b : Fin 4 → V) : ℝ := 1 + ∑ i, ‖b i‖^2
lemma evaluationConstant_pos (b : Fin 4 → V) : 0 < evaluationConstant b := by
  unfold evaluationConstant
  positivity

end TamingCompatibility.LocalMatrixOperator

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_CoefficientCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open _root_.MeasureTheory
open scoped SchwartzMap
namespace TamingCompatibility.MatrixEnergy
open EuclideanEnergy

lemma continuous_cutoff {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {U : Set V} (hU : IsOpen U) {f : V → D} (hf : ContinuousOn f U)
    {x₀ : V} (φ : ContDiffBump x₀) (hφ : tsupport φ ⊆ U) :
    Continuous (fun x => φ x • f x) := by
  apply continuous_of_tsupport
  intro x hx
  exact φ.continuous.continuousAt.smul (hf.continuousAt
    (hU.mem_nhds (hφ (tsupport_smul_subset_left _ _ hx))))

lemma cutoff_bound {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {U : Set V} {f : V → D} {C : ℝ} (hC : 0 ≤ C) (hf : ∀ x ∈ U, ‖f x‖ ≤ C)
    {x₀ : V} (φ : ContDiffBump x₀) (hφ : tsupport φ ⊆ U) (x : V) :
    ‖φ x • f x‖ ≤ C := by
  by_cases hx : φ x = 0
  · simpa only [hx,zero_smul,norm_zero] using hC
  have hxU : x ∈ U := hφ (subset_tsupport _ hx)
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg φ.nonneg]
  calc
    φ x * ‖f x‖ ≤ φ x * C := mul_le_mul_of_nonneg_left (hf x hxU) φ.nonneg
    _ ≤ 1*C := mul_le_mul_of_nonneg_right φ.le_one hC
    _ = C := one_mul _

def patchLower (b : V → Pair →L[ℝ] V) {x₀ : V} (φ : ContDiffBump x₀) : V → Pair →L[ℝ] V :=
  fun x => φ x • b x

end TamingCompatibility.MatrixEnergy

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_ChartEnergyIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section

noncomputable section
namespace TamingCompatibility.GeometricChart
open Bundle ManifoldForms ManifoldLocalization ManifoldVolume ManifoldHodge
open Set _root_.MeasureTheory
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)

def cutoffForm {k : ℕ} (p : A.centers) (a : ManifoldForms.Form X k) : ManifoldForms.Form X k :=
  fun x => A.partition p x • a x

lemma cutoffForm_smooth {k : ℕ} (p : A.centers) {a : ManifoldForms.Form X k} (ha : Smooth a) :
    Smooth (cutoffForm A p a) := Smooth.fun_smul (A.partition p).contMDiff ha

lemma cutoffForm_anti (p : A.centers) {a : TwoForm X} (ha : antiInvariantPart J a = a) :
    antiInvariantPart J (cutoffForm A p a) = cutoffForm A p a := by
  funext x
  have h := congrFun ha x
  change (1/2:ℝ) • (A.partition p x • a x -
    (A.partition p x • a x).compContinuousLinearMap (J.endomorphism x)) = A.partition p x • a x
  have hc : (A.partition p x • a x).compContinuousLinearMap (J.endomorphism x) =
      A.partition p x • (a x).compContinuousLinearMap (J.endomorphism x) := by ext v; rfl
  rw [hc]
  change (1/2:ℝ) • (a x - (a x).compContinuousLinearMap (J.endomorphism x)) = a x at h
  ext v
  have hv := congrArg (fun q => q v) h
  simp only [ContinuousAlternatingMap.smul_apply,ContinuousAlternatingMap.sub_apply,
    smul_eq_mul] at hv ⊢
  calc
    _ = A.partition p x * ((1/2:ℝ) * (a x v - (a x).compContinuousLinearMap (J.endomorphism x) v)) := by ring
    _ = _ := congrArg (A.partition p x * ·) hv

end TamingCompatibility.GeometricChart

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_ChartLift
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.ManifoldForms
open FormSmoothness Set
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X] [T2Space X] {k : ℕ}

def liftSupport (p : X) (β : Space → Space [⋀^Fin k]→L[ℝ] ℝ) : Set X :=
  (extChartAt Model p).symm '' tsupport β

end TamingCompatibility.ManifoldForms

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_MetricL2Core
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.MetricForms
open MetricModel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
lemma pairing_add_left' (g : Metric E) {k : ℕ} (a b c : Form E k) :
    pairing g (a+b) c = pairing g a c + pairing g b c := by
  change FormMetric.pairing (MetricHodge.formEquiv g k (a+b)) (MetricHodge.formEquiv g k c) = _
  rw [map_add]
  simp only [FormMetric.pairing,map_add,inner_add_left]
  rfl
end TamingCompatibility.MetricForms

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_MetricPairingCLM
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section

noncomputable section
namespace TamingCompatibility.MetricForms
open MetricModel MetricHodge
open scoped ContDiff
variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup D] [NormedSpace ℝ D]

local instance instNormedAddCommGroupContinuousLinearMapRealIdForm {k : ℕ} : NormedAddCommGroup (Form E k →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealContinuousLinearMapIdForm {k : ℕ} : NormedSpace ℝ (Form E k →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

def pairingCLM (g : Metric E) (k : ℕ) : Form E k →L[ℝ] Form E k →L[ℝ] ℝ :=
  (FormMetric.pairingCLM (E := MetricModel.Model g) (k := k)).bilinearComp
    (formEquiv g k).toContinuousLinearMap (formEquiv g k).toContinuousLinearMap

attribute [local instance] OAI.TamingCompatibility.MetricForms.instFiniteDimensionalRealContinuousMultilinearMapFin_solutions
attribute [local instance] OAI.TamingCompatibility.MetricForms.instFiniteDimensionalRealContinuousAlternatingMapFin_solutions
lemma pairingCLM_one_smooth {U : Set D} (g : D → Metric E)
    (hdim : Module.finrank ℝ E = 4) (b : Fin 4 → D → E)
    (hbs : ∀ i, ContDiffOn ℝ ∞ (b i) U)
    (hb : ∀ x ∈ U, ∀ i j, (g x).bilinear (b i x) (b j x) = if i=j then 1 else 0) :
    ContDiffOn ℝ ∞ (fun x => pairingCLM (g x) 1) U := by
  apply contDiffOn_clm_apply.mpr
  intro a
  apply contDiffOn_clm_apply.mpr
  intro c
  exact SmoothMetric.contDiffOn_pairing_one_frame g hdim b hbs hb contDiffOn_const contDiffOn_const

lemma pairingCLM_two_smooth {U : Set D} (g : D → Metric E)
    (hdim : Module.finrank ℝ E = 4) (b : Fin 4 → D → E)
    (hbs : ∀ i, ContDiffOn ℝ ∞ (b i) U)
    (hb : ∀ x ∈ U, ∀ i j, (g x).bilinear (b i x) (b j x) = if i=j then 1 else 0) :
    ContDiffOn ℝ ∞ (fun x => pairingCLM (g x) 2) U := by
  apply contDiffOn_clm_apply.mpr
  intro a
  apply contDiffOn_clm_apply.mpr
  intro c
  exact SmoothMetric.contDiffOn_pairing_two_frame g hdim b hbs hb contDiffOn_const contDiffOn_const
end TamingCompatibility.MetricForms

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_NormalSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.LocalMatrixOperator
open MetricModel MetricForms MetricHodge ExteriorForms ContinuousAlternatingMap
open EuclideanEnergy AntiInvariantFrame Function Set
open scoped ContDiff RealInnerProductSpace SchwartzMap Topology

def frameTest (ψ χ : V → MetricForms.Form V 2) (q : V → Pair) : V → MetricForms.Form V 2 :=
  fun x => q x 0 • ψ x + q x 1 • χ x

lemma frameTest_zero {ψ χ : V → MetricForms.Form V 2} {q : V → Pair} {x : V}
    (hq : q x = 0) : frameTest ψ χ q x = 0 := by
  simp [frameTest,hq]

lemma frameTest_tsupport (ψ χ : V → MetricForms.Form V 2) (q : V → Pair) :
    tsupport (frameTest ψ χ q) ⊆ tsupport q := by
  apply closure_minimal _ (isClosed_tsupport q)
  intro x hx
  by_contra h
  exact hx (frameTest_zero (image_eq_zero_of_notMem_tsupport h))

lemma frameTest_smooth {U : Set V} (hU : IsOpen U) {ψ χ : V → MetricForms.Form V 2}
    (hψ : ContDiffOn ℝ ∞ ψ U) (hχ : ContDiffOn ℝ ∞ χ U) {q : V → Pair}
    (hq : ContDiff ℝ ∞ q) (hqU : tsupport q ⊆ U) : ContDiff ℝ ∞ (frameTest ψ χ q) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ tsupport q
  · have hxU := hU.mem_nhds (hqU hx)
    exact (((EuclideanSpace.proj 0).contDiff.comp hq).contDiffAt.smul
      ((hψ x (hqU hx)).contDiffAt hxU)).add
      (((EuclideanSpace.proj 1).contDiff.comp hq).contDiffAt.smul
        ((hχ x (hqU hx)).contDiffAt hxU))
  · have he : frameTest ψ χ q =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [(isClosed_tsupport q).isOpen_compl.mem_nhds hx] with y hy
      exact frameTest_zero (image_eq_zero_of_notMem_tsupport hy)
    exact contDiffAt_const.congr_of_eventuallyEq he

end TamingCompatibility.LocalMatrixOperator

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_RadialCoefficientProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.RadialPotential
open Set Filter Function Metric
open scoped ContDiff Topology RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [HasContDiffBump E]

omit [HasContDiffBump E] in
lemma firstOrderSource_tsupport (V : E → E) (u : E → ℝ) :
    tsupport (firstOrderSource V u) ⊆ tsupport u := by
  apply (closure_mono ?_).trans (tsupport_fderiv_subset ℝ)
  intro z hz
  change fderiv ℝ u z ≠ 0
  intro h
  exact hz (by simp [firstOrderSource,h])

end TamingCompatibility.RadialPotential

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_NormalSystem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.LocalMatrixOperator
open MetricModel MetricForms MetricHodge ExteriorForms ContinuousAlternatingMap
open EuclideanEnergy AntiInvariantFrame
open scoped ContDiff RealInnerProductSpace SchwartzMap

def frameVector (b : Fin 4 → V) : MetricForms.Form V 1 →L[ℝ] V :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (fun i => ContinuousAlternatingMap.apply ℝ V ℝ ![b i])

end TamingCompatibility.LocalMatrixOperator

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeMatrixEnergy
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
open scoped RealInnerProductSpace
namespace TamingCompatibility.HodgeNormalSymbol
open EuclideanEnergy

def symbol (ξ : V) (a : W) : Q := WithLp.toLp 2
  ![(UnitaryFrame.interior ξ a) 0,(UnitaryFrame.interior ξ a) 1,
    (UnitaryFrame.interior ξ a) 2,(UnitaryFrame.interior ξ a) 3,
    (UnitaryFrame.interior ξ (UnitaryFrame.star a)) 0,
    (UnitaryFrame.interior ξ (UnitaryFrame.star a)) 1,
    (UnitaryFrame.interior ξ (UnitaryFrame.star a)) 2,
    (UnitaryFrame.interior ξ (UnitaryFrame.star a)) 3]

lemma symbol_add (ξ : V) (a b : W) : symbol ξ (a+b) = symbol ξ a+symbol ξ b := by
  ext i
  fin_cases i <;> simp [symbol,UnitaryFrame.interior,UnitaryFrame.star] <;> ring
lemma symbol_smul (ξ : V) (c : ℝ) (a : W) : symbol ξ (c • a) = c • symbol ξ a := by
  ext i
  fin_cases i <;> simp [symbol,UnitaryFrame.interior,UnitaryFrame.star] <;> ring

def normalSymbol (ξ : V) : W →L[ℝ] Q :=
  LinearMap.toContinuousLinearMap {
    toFun := symbol ξ
    map_add' := symbol_add ξ
    map_smul' := symbol_smul ξ }

lemma normalSymbol_apply (ξ : V) (a : W) : normalSymbol ξ a = symbol ξ a := rfl
end TamingCompatibility.HodgeNormalSymbol

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeFrozenEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
open _root_.MeasureTheory
open scoped SchwartzMap LineDeriv
namespace TamingCompatibility.HodgeFrozenEnergy
open EuclideanEnergy HodgeMatrixEnergy HodgeNormalSymbol

def coefficient (b : Fin 4 → V) (i : Fin 4) : HodgeMatrixEnergy.W →L[ℝ] Q :=
  normalSymbol (WithLp.toLp 2 (fun j => b j i))
end TamingCompatibility.HodgeFrozenEnergy

end
end

section
noncomputable section
open scoped ContDiff RealInnerProductSpace
namespace TamingCompatibility.HodgeFrame
open MetricModel MetricForms MetricHodge ExteriorForms ContinuousAlternatingMap
open FormMetric (pairLeft pairRight)
open HodgeNormalSymbol (W)
variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup D] [NormedSpace ℝ D]

def basisForm (g : Metric E) (b : Fin 4 → E) (j : Fin 6) : MetricForms.Form E 2 :=
  AntiInvariantFrame.covectorWedge (g.bilinear (b (pairLeft j))) (g.bilinear (b (pairRight j)))

end TamingCompatibility.HodgeFrame

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeFrameDifferential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.HodgeFrame
open ContinuousAlternatingMap ExteriorForms MetricForms MetricModel
open EuclideanEnergy
open HodgeNormalSymbol (W)

def combineThree (a : Fin 6 → MetricForms.Form V 3) : W →L[ℝ] MetricForms.Form V 3 :=
  ∑ j, (EuclideanSpace.proj j).smulRight (a j)

end TamingCompatibility.HodgeFrame

end
end

section
noncomputable section
open scoped RealInnerProductSpace
namespace TamingCompatibility.HodgeNormalOperator
open MetricModel MetricForms MetricHodge ExteriorForms ContinuousAlternatingMap
open EuclideanEnergy HodgeFrame
open HodgeNormalSymbol (W Q)

def join (u v : V) : Q := WithLp.toLp 2 ![u 0,u 1,u 2,u 3,v 0,v 1,v 2,v 3]
def joinCLM : (V × V) →L[ℝ] Q := LinearMap.toContinuousLinearMap {
  toFun := fun p => join p.1 p.2
  map_add' := by intro a b; ext i; fin_cases i <;> simp [join]
  map_smul' := by intro c a; ext i; fin_cases i <;> simp [join] }

def left (b : Fin 4 → V) : MetricForms.Form V 1 →L[ℝ] Q :=
  joinCLM ∘L (LocalMatrixOperator.frameVector b).prod 0
def right (b : Fin 4 → V) : MetricForms.Form V 1 →L[ℝ] Q :=
  joinCLM ∘L (0 : MetricForms.Form V 1 →L[ℝ] V).prod (LocalMatrixOperator.frameVector b)
end TamingCompatibility.HodgeNormalOperator

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeGeometricCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
open scoped ContDiff RealInnerProductSpace
namespace TamingCompatibility.HodgeGeometricCoefficients
open MetricModel MetricForms MetricHodge ExteriorForms ContinuousAlternatingMap
open EuclideanEnergy HodgeFrame HodgeNormalOperator
open HodgeNormalSymbol (W Q)

def frame (g : V → Metric V) (b : Fin 4 → V → V) (j : Fin 6) (x : V) : MetricForms.Form V 2 :=
  basisForm (g x) (fun i => b i x) j
def principal (b : Fin 4 → V → V) (i : Fin 4) (x : V) : W →L[ℝ] Q :=
  HodgeFrozenEnergy.coefficient (fun j => b j x) i
end TamingCompatibility.HodgeGeometricCoefficients

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_SymbolMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace TamingCompatibility.HodgeNormalSymbol
open EuclideanEnergy
open scoped RealInnerProductSpace

lemma normalSymbol_add_covector (ξ η : V) :
    normalSymbol (ξ+η) = normalSymbol ξ + normalSymbol η := by
  apply ContinuousLinearMap.ext
  intro a
  ext i
  fin_cases i <;> simp [normalSymbol_apply,symbol,UnitaryFrame.interior,UnitaryFrame.star] <;> ring

lemma normalSymbol_smul_covector (c : ℝ) (ξ : V) :
    normalSymbol (c • ξ) = c • normalSymbol ξ := by
  apply ContinuousLinearMap.ext
  intro a
  ext i
  fin_cases i <;> simp [normalSymbol_apply,symbol,UnitaryFrame.interior,UnitaryFrame.star] <;> ring

def symbolMap : V →L[ℝ] (W →L[ℝ] Q) :=
  LinearMap.toContinuousLinearMap {
    toFun := normalSymbol
    map_add' := normalSymbol_add_covector
    map_smul' := normalSymbol_smul_covector }

@[simp] lemma symbolMap_apply (ξ : V) : symbolMap ξ = normalSymbol ξ := rfl
end TamingCompatibility.HodgeNormalSymbol

namespace TamingCompatibility.GeometricHilbert.CoordinateOperator
open HodgeNormalSymbol EuclideanEnergy
open scoped RealInnerProductSpace ContDiff
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

def pullCoefficient (a : Fin 4 → W →L[ℝ] Q) (C : V →L[ℝ] V) (j : Fin 4) :
    W →L[ℝ] Q := ∑ i, (C (e i) j) • a i

end TamingCompatibility.GeometricHilbert.CoordinateOperator

namespace TamingCompatibility.GeometricHilbert.OrthogonalJets
open scoped RealInnerProductSpace ContDiff
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

omit [CompleteSpace W] in
@[simp] lemma gauge_zero (A : V →L[ℝ] End (W := W)) : gauge A 0 = 1 := by
  simp [gauge]

end TamingCompatibility.GeometricHilbert.OrthogonalJets


end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeStarGeometry
attribute [-simp] _root_.OAI.TamingCompatibility.HodgeNormalSymbol.symbolMap_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.HodgeStarGeometry
open HodgeNormalSymbol HodgeNormalOperator HodgeFrame MetricModel MetricForms MetricHodge
open scoped ContDiff Topology RealInnerProductSpace
open ContinuousAlternatingMap Filter
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

def starMap : W →L[ℝ] W := LinearMap.toContinuousLinearMap {
  toFun := UnitaryFrame.star
  map_add' := UnitaryFrame.star_add
  map_smul' := UnitaryFrame.star_smul }
@[simp] lemma starMap_apply (u : W) : starMap u = UnitaryFrame.star u := rfl

end TamingCompatibility.HodgeStarGeometry

end
end

end

end OAI
end


