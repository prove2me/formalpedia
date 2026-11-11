-- Prove2me | Definitions.Def_OAIQ240Bp005
-- name    : OAIQ240Bp005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T22:47:12.092094+00:00
-- url     : https://prove2.me/theorems/1e9f07e4-fa1e-4d85-b4ce-ae35126a2cd7
-- title:
--   Definitions bundle OAIQ240Bp005 of the split of OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 68 declarations of OpenAI's Lean: 20 definitions and 48 theorems. The definitions and types are `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.coefficientAction`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.coefficientDerivAction`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.coefficientValueAction`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.instNormedAddCommGroupContinuousLinearMapRealId_solutions_1`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.instNormedAddCommGroupContinuousLinearMapRealId_solutions_2`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.instNormedAddCommGroupSubtypeAmbientComplexMemSubmoduleRealHMap`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.instNormedAddCommGroupSubtypeAmbientComplexMemSubmoduleRealHMapSupportedHolder`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.instNormedAddCommGroupSubtypeJetAmbientComplexHDivRealOfNatMemSubmoduleCOne`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.instNormedAddCommGroupSubtypeJetAmbientHDivRealOfNatMemSubmoduleCOne_1`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.instNormedAddCommGroupSubtypeJetAmbientHDivRealOfNatMemSubmoduleCOne_2`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.instNormedSpaceRealContinuousLinearMapId_solutions_2`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.instNormedSpaceRealSubtypeJetAmbientHDivOfNatMemSubmoduleCOne_1`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.instNormedSpaceRealSubtypeJetAmbientHDivOfNatMemSubmoduleCOne_2`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.mapJet`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.mapJetBilinear`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ofBoundedCThree`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.supportedHolder`, `OAI.PackingSufficiencySupport.Hamiltonian.closedRoundDisk`, `OAI.SymplecticBallPacking.Hamiltonian.planarArea`, `OAI.SymplecticBallPacking.Hamiltonian.radiusSq`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: [`BallPacking_Holder_BanachSpace`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Holder/BanachSpace.lean), [`BallPacking_Holder_HolderTaylor`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Holder/HolderTaylor.lean), [`BallPacking_Holder_KernelSchauder`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Holder/KernelSchauder.lean), [`BallPacking_Holder_NonlinearCR`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Holder/NonlinearCR.lean), [`BallPacking_Holder_SchauderSplit`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Holder/SchauderSplit.lean), [`BallPacking_Moser_CircleCorrection`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Moser/CircleCorrection.lean), [`BallPacking_Rigidity_RadialForm`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Rigidity/RadialForm.lean).
--
--   **Imports.** It imports the bundles `OAIQ240Bp000`, `OAIQ240Bp001` and `OAIQ240Bp003` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ240Bp008`, `OAIQ240Bp009` and `OAIQ240Bp010`.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ240Bp000
import Definitions.Def_OAIQ240Bp001
import Definitions.Def_OAIQ240Bp003

section
-- module Solutions.OAIQ240_BP.BallPacking_Holder_BanachSpace
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.coefficient_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.superpose_value _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
open scoped BoundedContinuousFunction Topology ContDiff
open Set Filter
section

variable (X E : Type*) [MetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {X E}

variable {α : ℝ}

lemma norm_le_of_bounds (u : Holder X E α) {M H : ℝ} (hM0 : 0 ≤ M) (hH0 : 0 ≤ H)
    (hM : ∀ x, ‖valueCLM α u x‖ ≤ M)
    (hH : ∀ x y, ‖valueCLM α u x - valueCLM α u y‖ ≤ H * dist x y ^ α) :
    ‖u‖ ≤ max M H := by
  have he : u = ofBound (valueCLM α u) (valueCLM α u).continuous M H hM hH0 hH := by
    apply value_ext
    intro x
    rfl
  rw [he]
  exact ofBound_norm_le _ _ _ _ hM0 _ _ _

variable (D : Type*) [NormedAddCommGroup D] [NormedSpace ℝ D]

variable {D}

lemma jetValue_norm_le (u : COneHolder (E := E) D α) : ‖jetValueCLM α u‖ ≤ ‖u‖ :=
  le_max_left _ _

end
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.instNormedAddCommGroupContinuousLinearMapRealId_solutions
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.instNormedSpaceRealContinuousLinearMapId_solutions
local instance instNormedAddCommGroupContinuousLinearMapRealId_solutions_1 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) := ContinuousLinearMap.toNormedAddCommGroup
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.instNormedSpaceRealContinuousLinearMapId_solutions_1
local instance instNormedAddCommGroupContinuousLinearMapRealId_solutions_2 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] F) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealContinuousLinearMapId_solutions_2 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] F) := ContinuousLinearMap.toNormedSpace

lemma boundedCThree_of_compactSupport {f : E → F} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) : BoundedCThree f := by
  have h1 : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have h2 : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ f)) := h1.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have h3 : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ (fderiv ℝ f))) := h2.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  obtain ⟨M0,h0⟩ := hf.continuous.bounded_above_of_compact_support hc
  obtain ⟨M1,h1b⟩ := h1.continuous.bounded_above_of_compact_support (hc.fderiv (𝕜 := ℝ))
  obtain ⟨M2,h2b⟩ := h2.continuous.bounded_above_of_compact_support
    (hc.fderiv (𝕜 := ℝ) |>.fderiv (𝕜 := ℝ))
  obtain ⟨M3,h3b⟩ := h3.continuous.bounded_above_of_compact_support
    (hc.fderiv (𝕜 := ℝ) |>.fderiv (𝕜 := ℝ) |>.fderiv (𝕜 := ℝ))
  refine ⟨hf, max 0 (max M0 (max M1 (max M2 M3))), le_max_left _ _, ?_, ?_, ?_, ?_⟩
  · intro x; exact (h0 x).trans ((le_max_left _ _).trans (le_max_right _ _))
  · intro x; exact (h1b x).trans ((le_max_left _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _)))
  · intro x; exact (h2b x).trans ((le_max_left _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))
  · intro x; exact (h3b x).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))

end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Holder_NonlinearCR
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter

namespace HolderCompletion
variable {D E F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma c_fderiv (u : COne D E) (x : D) : fderiv ℝ (cValue u) x = cDeriv u x :=
  (c_hasFDerivAt u x).fderiv

section Superposition
variable {f : E → F} (hf : BoundedCThree f)
  {b : D → E} (hb : Differentiable ℝ b) {B : ℝ} (hB : 0 ≤ B)
  (hbB : ∀ x, ‖fderiv ℝ b x‖ ≤ B)

@[simp] lemma superposeDeriv_value (u h : COne D E) (x : D) :
    valueCLM _ (superposeDeriv hf hb hB hbB u h) x =
      fderiv ℝ f (b x+cValue u x) (cValue h x) := rfl

end Superposition
end HolderCompletion

end
section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
namespace HolderCompletion
variable {D E F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ D] in
lemma mapCLM_norm_le (L : E →L[ℝ] F) (u : HMap D E) :
    ‖mapCLM ((1:ℝ)/3) L u‖ ≤ ‖L‖ * ‖u‖ := by
  apply (norm_le_of_bounds (mapCLM ((1:ℝ)/3) L u) (by positivity) (by positivity) ?_ ?_).trans
    (max_self _).le
  · intro x
    rw [mapCLM_value]
    exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (norm_value_le u x) (norm_nonneg L))
  · intro x y
    simp only [mapCLM_value, ← map_sub]
    exact (L.le_opNorm _).trans (by
      calc
        _ ≤ ‖L‖ * (‖u‖ * dist x y ^ ((1:ℝ)/3)) :=
          mul_le_mul_of_nonneg_left (norm_sub_value_le u x y) (norm_nonneg L)
        _ = _ := by ring)

def mapJet (L : E →L[ℝ] F) (u : COne D E) : COne D F :=
  ⟨(mapCLM _ L (jetValueCLM _ u),
    mapCLM _ ((ContinuousLinearMap.compL ℝ D E F) L) (jetDerivCLM _ u)), by
      intro x
      convert! L.hasFDerivAt.comp x (c_hasFDerivAt u x) using 1⟩

@[simp] lemma mapJet_value (L : E →L[ℝ] F) (u : COne D E) (x : D) :
    cValue (mapJet L u) x = L (cValue u x) := rfl

@[simp] lemma mapJet_deriv (L : E →L[ℝ] F) (u : COne D E) (x : D) :
    cDeriv (mapJet L u) x = L.comp (cDeriv u x) := rfl

lemma cValue_ext {u v : COne D E} (h : ∀ x, cValue u x = cValue v x) : u = v := by
  apply Subtype.ext
  apply Prod.ext
  · apply value_ext
    exact h
  · apply value_ext
    intro x
    have he : (cValue u : D → E) = cValue v := funext h
    change cDeriv u x = cDeriv v x
    rw [← c_fderiv u x, ← c_fderiv v x, he]

lemma mapJet_norm_le (L : E →L[ℝ] F) (u : COne D E) : ‖mapJet L u‖ ≤ ‖L‖*‖u‖ := by
  change max ‖mapCLM _ L (jetValueCLM _ u)‖
    ‖mapCLM _ ((ContinuousLinearMap.compL ℝ D E F) L) (jetDerivCLM _ u)‖ ≤ _
  apply max_le
  · exact (mapCLM_norm_le L _).trans
      (mul_le_mul_of_nonneg_left (jetValue_norm_le u) (norm_nonneg L))
  · apply (mapCLM_norm_le _ _).trans
    apply mul_le_mul _ (jetDeriv_norm_le u) (norm_nonneg _) (norm_nonneg L)
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg L)
    intro A
    exact ContinuousLinearMap.opNorm_comp_le L A

local instance instNormedAddCommGroupSubtypeJetAmbientHDivRealOfNatMemSubmoduleCOne_1 : NormedAddCommGroup (COne D E) := inferInstance
local instance instNormedSpaceRealSubtypeJetAmbientHDivOfNatMemSubmoduleCOne_1 : NormedSpace ℝ (COne D E) := inferInstance
local instance instNormedAddCommGroupSubtypeJetAmbientHDivRealOfNatMemSubmoduleCOne_2 : NormedAddCommGroup (COne D F) := inferInstance
local instance instNormedSpaceRealSubtypeJetAmbientHDivOfNatMemSubmoduleCOne_2 : NormedSpace ℝ (COne D F) := inferInstance

local instance instNormedAddCommGroupContinuousLinearMapRealIdSubtypeJetAmbientHDivOfNatMemSubmoduleCOne_r93e0b2_1 : NormedAddCommGroup (COne D E →L[ℝ] COne D F) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealContinuousLinearMapIdSubtypeJetAmbientHDivOfNatMemSubmoduleCOne_r93e0b2_1 : NormedSpace ℝ (COne D E →L[ℝ] COne D F) := ContinuousLinearMap.toNormedSpace
def mapJetBilinear : (E →L[ℝ] F) →L[ℝ] COne D E →L[ℝ] COne D F :=
  LinearMap.mkContinuous₂
    { toFun := fun L =>
        { toFun := mapJet (D := D) L
          map_add' := fun u v => by
            apply cValue_ext
            intro x
            simp only [mapJet_value, cValue_add, map_add]
          map_smul' := fun c u => by
            apply cValue_ext
            intro x
            simp only [mapJet_value, cValue_smul, map_smul, RingHom.id_apply] }
      map_add' := fun L M => by
        apply LinearMap.ext
        intro u
        apply cValue_ext
        intro x
        rfl
      map_smul' := fun c L => by
        apply LinearMap.ext
        intro u
        apply cValue_ext
        intro x
        rfl }
    1 (by intro L u; convert! mapJet_norm_le L u using 1; simp only [one_mul])

@[simp] lemma mapJetBilinear_value (L : E →L[ℝ] F) (u : COne D E) (x : D) :
    cValue (mapJetBilinear (D := D) (E := E) (F := F) L u) x = L (cValue u x) := rfl

def ofBoundedCThree {f : D → E} (hf : BoundedCThree f) : COne D E :=
  ⟨(ofBoundedDeriv f (hf.smooth.differentiable (by simp)) hf.bound hf.bound
      hf.bound_nonneg hf.bound_nonneg hf.norm_le hf.norm_fderiv_le,
    ofBoundedDeriv (fderiv ℝ f) (hf.fderiv_smooth.differentiable (by simp)) hf.bound hf.bound
      hf.bound_nonneg hf.bound_nonneg hf.norm_fderiv_le hf.norm_fderiv₂_le), by
      intro x
      exact (hf.smooth.differentiable (by simp) x).hasFDerivAt⟩

@[simp] lemma ofBoundedCThree_value {f : D → E} (hf : BoundedCThree f) (x : D) :
    cValue (ofBoundedCThree hf) x = f x := rfl

@[simp] lemma ofBoundedCThree_deriv {f : D → E} (hf : BoundedCThree f) (x : D) :
    cDeriv (ofBoundedCThree hf) x = fderiv ℝ f x := rfl

def supportedHolder (K : Set D) : Submodule ℝ (HMap D E) :=
  ⨅ x ∈ Kᶜ, ((BoundedContinuousFunction.evalCLM ℝ x).comp (valueCLM _)).ker

omit [NormedSpace ℝ D] in
lemma mem_supportedHolder (u : HMap D E) (K : Set D) :
    u ∈ supportedHolder K ↔ ∀ x ∉ K, valueCLM _ u x = 0 := by
  simp [supportedHolder]

end HolderCompletion

end
section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
namespace HolderCompletion
variable {D E F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

local instance jetCoeffInst1_r93e0b2_1 : NormedAddCommGroup (E →L[ℝ] F) := ContinuousLinearMap.toNormedAddCommGroup
local instance jetCoeffInst2_r93e0b2_1 : NormedSpace ℝ (E →L[ℝ] F) := ContinuousLinearMap.toNormedSpace
local instance jetCoeffInst3_r93e0b2_1 : NormedAddCommGroup (D →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance jetCoeffInst4_r93e0b2_1 : NormedSpace ℝ (D →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetCoeffInst5
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetCoeffInst6
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetCoeffInst7
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetCoeffInst8
local instance jetCoeffInst9_r93e0b2_1 : NormedAddCommGroup (COne D E) := inferInstance
local instance jetCoeffInst10_r93e0b2_1 : NormedSpace ℝ (COne D E) := inferInstance
local instance jetCoeffInst11_r93e0b2_1 : NormedAddCommGroup (COne D F) := inferInstance
local instance jetCoeffInst12_r93e0b2_1 : NormedSpace ℝ (COne D F) := inferInstance
local instance jetCoeffInst13_r93e0b2_1 : NormedAddCommGroup (HMap D E) := inferInstance
local instance jetCoeffInst14_r93e0b2_1 : NormedSpace ℝ (HMap D E) := inferInstance
local instance jetCoeffInst15_r93e0b2_1 : NormedAddCommGroup (HMap D F) := inferInstance
local instance jetCoeffInst16_r93e0b2_1 : NormedSpace ℝ (HMap D F) := inferInstance
local instance jetCoeffInst17_r93e0b2_1 : NormedAddCommGroup (HMap D (D →L[ℝ] F)) := inferInstance
local instance jetCoeffInst18_r93e0b2_1 : NormedSpace ℝ (HMap D (D →L[ℝ] F)) := inferInstance
def coefficientValueAction (M : COne D (E →L[ℝ] F)) : COne D E →L[ℝ] HMap D F :=
  (bilinCLM (X := D) (α := (1:ℝ)/3) (ContinuousLinearMap.apply (E := E) ℝ F).flip
    (jetValueCLM _ M)).comp (jetValueCLM _)

def coefficientDerivAction (M : COne D (E →L[ℝ] F)) : COne D E →L[ℝ] HMap D (D →L[ℝ] F) :=
  (bilinCLM (X := D) (α := (1:ℝ)/3) (ContinuousLinearMap.compL ℝ D E F)
    (jetValueCLM _ M)).comp (jetDerivCLM _) +
  (bilinCLM (X := D) (α := (1:ℝ)/3)
    (ContinuousLinearMap.flipₗᵢ ℝ D E F).toContinuousLinearEquiv.toContinuousLinearMap
    (jetDerivCLM _ M)).comp (jetValueCLM _)

def coefficientAction (M : COne D (E →L[ℝ] F)) : COne D E →L[ℝ] COne D F :=
  ((coefficientValueAction M).prod (coefficientDerivAction M)).codRestrict
    (jetGraph (E := F) D ((1:ℝ)/3)) (fun u => by
      intro z
      change HasFDerivAt (fun x => cValue M x (cValue u x))
        ((cValue M z).comp (cDeriv u z)+(cDeriv M z).flip (cValue u z)) z
      exact (c_hasFDerivAt M z).clm_apply (c_hasFDerivAt u z))

@[simp] lemma coefficientAction_value (M : COne D (E →L[ℝ] F)) (u : COne D E) (z : D) :
    cValue (coefficientAction M u) z = cValue M z (cValue u z) := rfl

@[simp] lemma coefficientAction_deriv (M : COne D (E →L[ℝ] F)) (u : COne D E) (z : D) :
    cDeriv (coefficientAction M u) z =
      (cValue M z).comp (cDeriv u z)+(cDeriv M z).flip (cValue u z) := rfl

end HolderCompletion

end
section
open scoped ContDiff Topology RealInnerProductSpace
open Set Filter MeasureTheory

 theorem smoothCauchyKernel_norm {δ : ℝ} (hδ : 0<δ) (z : ℂ) :
    ‖smoothCauchyKernel δ z‖ ≤ ‖z‖⁻¹ := by
  rw [smoothCauchyKernel,norm_smul,norm_star,Real.norm_of_nonneg
    (inv_nonneg.mpr (add_nonneg (sq_nonneg _) hδ.le))]
  by_cases hz : z=0
  · simp [hz]
  have hp : 0<‖z‖ := norm_pos_iff.mpr hz
  have hq : 0<‖z‖^2+δ := add_pos_of_nonneg_of_pos (sq_nonneg _) hδ
  rw [inv_mul_eq_div,←one_div (‖z‖)]
  apply (div_le_div_iff₀ hq hp).mpr
  nlinarith

 theorem smoothCauchyKernel_fderiv_norm {δ : ℝ} (hδ : 0<δ) {z : ℂ} (hz : z≠0) (v : ℂ) :
    ‖fderiv ℝ (smoothCauchyKernel δ) z v‖ ≤ (3/‖z‖^2)*‖v‖ := by
  have hp : 0<‖z‖ := norm_pos_iff.mpr hz
  have hq : 0<‖z‖^2+δ := add_pos_of_nonneg_of_pos (sq_nonneg _) hδ
  have hib : |inner ℝ z v| ≤ ‖z‖*‖v‖ := abs_real_inner_le_norm z v
  have h1 : (‖z‖^2+δ)⁻¹ ≤ (‖z‖^2)⁻¹ := by
    exact inv_anti₀ (sq_pos_of_pos hp) (by linarith)
  have h2 : 2*|inner ℝ z v|/(‖z‖^2+δ)^2*‖z‖ ≤ (2/‖z‖^2)*‖v‖ := by
    calc
      _ ≤ (2*(‖z‖*‖v‖)/(‖z‖^2+δ)^2)*‖z‖ := by gcongr
      _ ≤ (2*(‖z‖*‖v‖)/‖z‖^4)*‖z‖ := by
        gcongr
        nlinarith [sq_nonneg δ]
      _ = _ := by field_simp
  rw [smoothCauchyKernel_fderiv hδ]
  calc
    _ ≤ ‖(‖z‖^2+δ)⁻¹ • star v‖ + ‖(2*inner ℝ z v/(‖z‖^2+δ)^2) • star z‖ := norm_sub_le _ _
    _ = (‖z‖^2+δ)⁻¹*‖v‖ + (2*|inner ℝ z v|/(‖z‖^2+δ)^2)*‖z‖ := by
      simp only [norm_smul,norm_star,Real.norm_eq_abs,abs_inv,abs_of_pos hq,
        abs_div,abs_mul,abs_pow]
      norm_num
    _ ≤ (‖z‖^2)⁻¹*‖v‖+(2/‖z‖^2)*‖v‖ :=
      add_le_add (mul_le_mul_of_nonneg_right h1 (norm_nonneg _)) h2
    _ = _ := by ring


end
section
open scoped ContDiff Topology
open Set Filter MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

 theorem compact_kernel_derivative_integral_zero {K : ℂ → ℂ}
    (hK : ContDiff ℝ ∞ K) (hc : HasCompactSupport K) (v : ℂ) :
    (∫ w : ℂ, fderiv ℝ K w v)=0 := by
  have hi : Integrable (fun w => fderiv ℝ K w v) :=
    (((hK.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).continuous).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hc.fderiv_apply (𝕜 := ℝ) v)
  have hi0 : Integrable (fun w : ℂ => K w) := hK.continuous.integrable_of_hasCompactSupport hc
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (f := K) (g := fun _ : ℂ => (1:ℂ)) (v := v) (μ := volume)
    (by simpa only [mul_one] using hi) (by simp) (by simpa only [mul_one] using hi0)
    (fun w _ => hK.differentiable (by simp) w) (fun _ _ => differentiableAt_const _)
  have he : (fun x : ℂ => K x*fderiv ℝ (fun _ : ℂ => (1:ℂ)) x v)=0 := by
    funext x
    simp only [fderiv_const_apply,zero_apply,mul_zero,Pi.zero_apply]
  rw [he] at h
  change (∫ x : ℂ, (0:ℂ)) = -(∫ x : ℂ, fderiv ℝ K x v * 1) at h
  simpa only [integral_zero,mul_one,zero_eq_neg] using h

omit [CompleteSpace E] in
 theorem compact_kernel_convolution_fderiv {K : ℂ → ℂ}
    (hK : ContDiff ℝ ∞ K) (hc : HasCompactSupport K) {g : ℂ → E}
    (hg : Continuous g) (x v : ℂ) :
    fderiv ℝ (convolution K g (ContinuousLinearMap.lsmul ℝ ℂ) volume) x v =
      ∫ w : ℂ, fderiv ℝ K w v • g (x-w) := by
  have hd := hc.hasFDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℂ)
    (hK.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) (hg.locallyIntegrable (μ := volume)) x
  rw [hd.fderiv,convolution]
  have hi : Integrable (fun w : ℂ =>
      ((ContinuousLinearMap.lsmul ℝ ℂ).precompL ℂ) (fderiv ℝ K w) (g (x-w))) :=
    (hc.fderiv ℝ).convolutionExists_left _
      (hK.continuous_fderiv (by simp)) (hg.locallyIntegrable (μ := volume)) x
  rw [ContinuousLinearMap.integral_apply hi]
  rfl

 theorem compact_kernel_convolution_cancel {K : ℂ → ℂ}
    (hK : ContDiff ℝ ∞ K) (hc : HasCompactSupport K) {g : ℂ → E}
    (hg : Continuous g) (x v : ℂ) :
    fderiv ℝ (convolution K g (ContinuousLinearMap.lsmul ℝ ℂ) volume) x v =
      ∫ w : ℂ, fderiv ℝ K w v • (g (x-w)-g x) := by
  rw [compact_kernel_convolution_fderiv hK hc hg]
  have hi : Integrable (fun w : ℂ => fderiv ℝ K w v • g (x-w)) :=
    ((((hK.fderiv_right (m := ∞) (by simp)).continuous.clm_apply continuous_const).smul
      (hg.comp (continuous_const.sub continuous_id)))).integrable_of_hasCompactSupport
        ((hc.fderiv_apply (𝕜 := ℝ) v).smul_right)
  have hi0 : Integrable (fun w : ℂ => fderiv ℝ K w v) :=
    (((hK.fderiv_right (m := ∞) (by simp)).continuous).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hc.fderiv_apply (𝕜 := ℝ) v)
  simp_rw [smul_sub]
  rw [integral_sub hi (hi0.smul_const _),integral_smul_const,
    compact_kernel_derivative_integral_zero hK hc,zero_smul,sub_zero]

 theorem compact_kernel_convolution_derivative_bound {K : ℂ → ℂ}
    (hK : ContDiff ℝ ∞ K) (hc : HasCompactSupport K) {g : ℂ → E}
    (hg : Continuous g) {W : ℂ → ℝ} (hW : Integrable W)
    (hb : ∀ x w v, ‖fderiv ℝ K w v‖*‖g (x-w)-g x‖ ≤ W w*‖v‖) (x : ℂ) :
    ‖fderiv ℝ (convolution K g (ContinuousLinearMap.lsmul ℝ ℂ) volume) x‖ ≤
      ∫ w : ℂ, W w := by
  have hW0 : 0≤ ∫ w : ℂ, W w := by
    apply integral_nonneg
    intro w
    change (0:ℝ) ≤ W w
    have h := hb 0 w 1
    simpa only [norm_one,mul_one] using (mul_nonneg (norm_nonneg _) (norm_nonneg _)).trans h
  apply ContinuousLinearMap.opNorm_le_bound _ hW0
  intro v
  rw [compact_kernel_convolution_cancel hK hc hg]
  calc
    _ ≤ ∫ w : ℂ, W w*‖v‖ := norm_integral_le_of_norm_le (hW.mul_const _)
      (Eventually.of_forall fun w => by rw [norm_smul]; exact hb x w v)
    _ = _ := integral_mul_const _ _


end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Holder_KernelSchauder
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Filter MeasureTheory

lemma scaledSchauderBump_homogeneous_bounds :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ r : ℝ, 0 < r → ∀ z : ℂ, z ≠ 0 →
      ‖fderiv ℝ (scaledSchauderBump r) z‖ ≤ 2*M/‖z‖ ∧
      ‖iteratedFDeriv ℝ 2 (scaledSchauderBump r) z‖ ≤ 4*M/‖z‖^2 := by
  obtain ⟨M,hM,h0,h1,h2,h3⟩ :=
    (HolderCompletion.boundedCThree_of_compactSupport schauderBump.contDiff
      schauderBump.hasCompactSupport).bounded
  refine ⟨M,hM,?_⟩
  intro r hr z hz
  have hp : 0 < ‖z‖ := norm_pos_iff.mpr hz
  by_cases ht : z ∈ tsupport (scaledSchauderBump r)
  · have hz2 : ‖z‖ ≤ 2*r := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using scaledSchauderBump_tsupport hr ht
    constructor
    · change ‖fderiv ℝ (fun w => schauderBump (r⁻¹ • w)) z‖ ≤ _
      rw [norm_first_rescale schauderBump.contDiff hr]
      calc
        _ ≤ r⁻¹*M := mul_le_mul_of_nonneg_left (h1 _) (inv_nonneg.mpr hr.le)
        _ ≤ _ := by rw [inv_mul_eq_div, div_le_div_iff₀ hr hp]; nlinarith
    · change ‖iteratedFDeriv ℝ 2 (fun w => schauderBump (r⁻¹ • w)) z‖ ≤ _
      rw [norm_second_rescale schauderBump.contDiff hr]
      calc
        _ ≤ (r^2)⁻¹*M := mul_le_mul_of_nonneg_left (by rw [norm_second_jet]; exact h2 _)
          (inv_nonneg.mpr (sq_nonneg r))
        _ ≤ _ := by
          rw [inv_mul_eq_div, div_le_div_iff₀ (sq_pos_of_pos hr) (sq_pos_of_pos hp)]
          have : ‖z‖^2 ≤ 4*r^2 := by nlinarith
          nlinarith [mul_le_mul_of_nonneg_left this hM]
  · have hd : fderiv ℝ (scaledSchauderBump r) z = 0 := fderiv_of_notMem_tsupport (𝕜 := ℝ) ht
    have hd2 : iteratedFDeriv ℝ 2 (scaledSchauderBump r) z = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      exact fun h => ht (tsupport_iteratedFDeriv_subset 2 h)
    simp only [hd, hd2, norm_zero]
    constructor <;> positivity



lemma smoothCauchyKernel_first_opNorm {δ : ℝ} (hδ : 0 < δ) {z : ℂ} (hz : z ≠ 0) :
    ‖fderiv ℝ (smoothCauchyKernel δ) z‖ ≤ 3/‖z‖^2 :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    (smoothCauchyKernel_fderiv_norm hδ hz)

lemma cutoff_smoothCauchyKernel_jet_bounds (b : ContDiffBump (0:ℂ)) :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ ∀ δ : ℝ, 0 < δ → ∀ z : ℂ, z ≠ 0 →
      ‖b z • smoothCauchyKernel δ z‖ ≤ ‖z‖⁻¹ ∧
      ‖fderiv ℝ (fun w => b w • smoothCauchyKernel δ w) z‖ ≤ C₁/‖z‖^2 ∧
      ‖iteratedFDeriv ℝ 2 (fun w => b w • smoothCauchyKernel δ w) z‖ ≤ C₂/‖z‖^3 := by
  obtain ⟨M,hM,h0,h1,h2,h3⟩ :=
    (HolderCompletion.boundedCThree_of_compactSupport b.contDiff b.hasCompactSupport).bounded
  have hR := b.rOut_pos
  refine ⟨M*b.rOut+3, M*b.rOut^2+6*M*b.rOut+14, by positivity, by positivity, ?_⟩
  intro δ hδ z hz
  have hp : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hbn : ‖b z‖ ≤ 1 := by simpa only [Real.norm_of_nonneg b.nonneg] using b.le_one
  refine ⟨?_, ?_⟩
  · rw [norm_smul]
    exact (mul_le_mul hbn (smoothCauchyKernel_norm hδ z) (norm_nonneg _) zero_le_one).trans_eq
      (one_mul _)
  by_cases ht : z ∈ tsupport (fun w => b w • smoothCauchyKernel δ w)
  · have ht' : ‖z‖ ≤ b.rOut := by
      have := tsupport_smul_subset_left b (smoothCauchyKernel δ) ht
      simpa only [b.tsupport_eq, Metric.mem_closedBall, dist_zero_right] using this
    constructor
    · calc
        _ ≤ ‖b z‖*‖fderiv ℝ (smoothCauchyKernel δ) z‖ +
            ‖fderiv ℝ b z‖*‖smoothCauchyKernel δ z‖ :=
          norm_first_smul_le b.contDiff (smoothCauchyKernel_smooth hδ) z
        _ ≤ 1*(3/‖z‖^2) + M*‖z‖⁻¹ := by
          exact add_le_add (mul_le_mul hbn (smoothCauchyKernel_first_opNorm hδ hz)
            (norm_nonneg _) zero_le_one) (mul_le_mul (h1 z)
            (smoothCauchyKernel_norm hδ z) (norm_nonneg _) hM)
        _ = (3+M*‖z‖)/‖z‖^2 := by field_simp
        _ ≤ _ := by
          apply div_le_div_of_nonneg_right _ (sq_nonneg _)
          nlinarith [mul_le_mul_of_nonneg_left ht' hM]
    · calc
        _ ≤ ‖b z‖*‖iteratedFDeriv ℝ 2 (smoothCauchyKernel δ) z‖ +
            2*‖fderiv ℝ b z‖*‖fderiv ℝ (smoothCauchyKernel δ) z‖ +
            ‖iteratedFDeriv ℝ 2 b z‖*‖smoothCauchyKernel δ z‖ :=
          norm_second_smul_le b.contDiff (smoothCauchyKernel_smooth hδ) z
        _ ≤ 1*(14/‖z‖^3) + 2*M*(3/‖z‖^2) + M*‖z‖⁻¹ := by
          apply add_le_add _ (mul_le_mul (by rw [norm_second_jet]; exact h2 z)
            (smoothCauchyKernel_norm hδ z) (norm_nonneg _) hM)
          exact add_le_add (mul_le_mul hbn (smoothCauchyKernel_second_opNorm hδ hz)
            (norm_nonneg _) zero_le_one) (mul_le_mul
            (mul_le_mul_of_nonneg_left (h1 z) (by norm_num))
            (smoothCauchyKernel_first_opNorm hδ hz) (norm_nonneg _) (by positivity))
        _ = (14+6*M*‖z‖+M*‖z‖^2)/‖z‖^3 := by field_simp <;> ring
        _ ≤ _ := by
          have hh : ‖z‖^2 ≤ b.rOut^2 := by nlinarith [b.rOut_pos]
          have ha := mul_le_mul_of_nonneg_left ht' (show 0 ≤ 6*M from by positivity)
          have hb := mul_le_mul_of_nonneg_left hh hM
          apply div_le_div_of_nonneg_right _ (by positivity)
          linarith
  · have hdz := fderiv_of_notMem_tsupport (𝕜 := ℝ) ht
    have hd2 : iteratedFDeriv ℝ 2 (fun w => b w • smoothCauchyKernel δ w) z = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      exact fun h => ht (tsupport_iteratedFDeriv_subset 2 h)
    simp only [hdz, hd2, norm_zero]
    constructor <;> positivity


end
open scoped ContDiff Topology
open Set Filter MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma compact_kernel_convolution_direction {K : ℂ → ℂ}
    (hK : ContDiff ℝ ∞ K) (hc : HasCompactSupport K) {g : ℂ → E}
    (hg : Continuous g) (x v : ℂ) :
    fderiv ℝ (convolution K g (ContinuousLinearMap.lsmul ℝ ℂ) volume) x v =
      convolution (fun w => fderiv ℝ K w v) g (ContinuousLinearMap.lsmul ℝ ℂ) volume x := by
  rw [compact_kernel_convolution_fderiv hK hc hg]
  rfl

lemma compact_kernel_convolution_derivative_lipschitz {K : ℂ → ℂ}
    (hK : ContDiff ℝ ∞ K) (hc : HasCompactSupport K) {g : ℂ → E}
    (hg : Continuous g) {W : ℂ → ℝ} (hW : Integrable W) (hW0 : ∀ w, 0 ≤ W w)
    (hb : ∀ x w v t : ℂ,
      ‖fderiv ℝ (fun y => fderiv ℝ K y v) w t‖ * ‖g (x-w)-g x‖ ≤
        W w * ‖v‖ * ‖t‖) (x y : ℂ) :
    ‖fderiv ℝ (convolution K g (ContinuousLinearMap.lsmul ℝ ℂ) volume) x -
        fderiv ℝ (convolution K g (ContinuousLinearMap.lsmul ℝ ℂ) volume) y‖ ≤
      (∫ w, W w) * ‖x-y‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (integral_nonneg hW0) (norm_nonneg _))
  intro v
  simp only [sub_apply, compact_kernel_convolution_direction hK hc hg]
  have hKv : ContDiff ℝ ∞ (fun w => fderiv ℝ K w v) :=
    (hK.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const
  have hcKv : HasCompactSupport (fun w => fderiv ℝ K w v) := hc.fderiv_apply (𝕜 := ℝ) v
  have hMv (z : ℂ) :
      ‖fderiv ℝ (convolution (fun w => fderiv ℝ K w v) g
        (ContinuousLinearMap.lsmul ℝ ℂ) volume) z‖ ≤ (∫ w, W w) * ‖v‖ := by
    have he := compact_kernel_convolution_derivative_bound hKv hcKv hg (hW.mul_const ‖v‖)
      (fun a w t => hb a w v t) z
    simpa only [integral_mul_const] using he
  have he := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
    (s := (univ : Set ℂ))
    (fun z _ => (hcKv.hasFDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℂ)
      (hKv.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) hg.locallyIntegrable z).differentiableAt)
    (fun z _ => hMv z) convex_univ (mem_univ y) (mem_univ x)
  convert! he using 1
  all_goals try with_reducible_and_instances rfl
  ring

lemma compact_convolution_split_derivative_bound {K N F : ℂ → ℂ}
    (hN : ContDiff ℝ ∞ N) (hcN : HasCompactSupport N)
    (hF : ContDiff ℝ ∞ F) (hcF : HasCompactSupport F)
    (hKF : ∀ w, K w = N w + F w) {g : ℂ → E} (hg : Continuous g)
    {WN WF : ℂ → ℝ} (hWN : Integrable WN) (hWF : Integrable WF)
    (hWF0 : ∀ w, 0 ≤ WF w)
    (hbN : ∀ x w v : ℂ, ‖fderiv ℝ N w v‖ * ‖g (x-w)-g x‖ ≤ WN w * ‖v‖)
    (hbF : ∀ x w v t : ℂ,
      ‖fderiv ℝ (fun y => fderiv ℝ F y v) w t‖ * ‖g (x-w)-g x‖ ≤
        WF w * ‖v‖ * ‖t‖) (x y : ℂ) :
    ‖fderiv ℝ (convolution K g (ContinuousLinearMap.lsmul ℝ ℂ) volume) x -
        fderiv ℝ (convolution K g (ContinuousLinearMap.lsmul ℝ ℂ) volume) y‖ ≤
      2*(∫ w, WN w) + (∫ w, WF w)*‖x-y‖ := by
  rw [compact_convolution_split_fderiv hN hcN hF hcF hKF hg x,
    compact_convolution_split_fderiv hN hcN hF hcF hKF hg y]
  have hbr := compact_kernel_convolution_derivative_lipschitz hF hcF hg hWF hWF0 hbF x y
  have hx := compact_kernel_convolution_derivative_bound hN hcN hg hWN hbN x
  have hy := compact_kernel_convolution_derivative_bound hN hcN hg hWN hbN y
  have halg {A B C D : ℂ →L[ℝ] E} : ‖(A+B)-(C+D)‖ ≤ ‖A‖+‖C‖+‖B-D‖ := by
    calc
      _ = ‖(A-C)+(B-D)‖ := by congr 1; abel
      _ ≤ ‖A-C‖+‖B-D‖ := norm_add_le _ _
      _ ≤ _ := add_le_add (norm_sub_le A C) le_rfl
  exact halg.trans (by linarith)



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Holder_SchauderSplit
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Filter MeasureTheory

lemma schauderSplit_exists_uniform {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ K : ℂ → ℂ,
      ContDiff ℝ ∞ K → HasCompactSupport K →
      (∀ z, z ≠ 0 → ‖K z‖ ≤ ‖z‖⁻¹ ∧ ‖fderiv ℝ K z‖ ≤ C₁/‖z‖^2 ∧
        ‖iteratedFDeriv ℝ 2 K z‖ ≤ C₂/‖z‖^3) →
      ∀ r : ℝ, 0 < r → Nonempty (SchauderSplit K r A B) := by
  obtain ⟨M,hM,hMjet⟩ := scaledSchauderBump_homogeneous_bounds
  refine ⟨C₁+2*M, C₂+4*M*C₁+4*M, by positivity, by positivity, ?_⟩
  intro K hK hcK hjet r hr
  let b : ℂ → ℝ := scaledSchauderBump r
  have hb : ContDiff ℝ ∞ b := scaledSchauderBump_smooth r
  have hb0 (w : ℂ) : 0 ≤ b w := (scaledSchauderBump_range r w).1
  have hb1 (w : ℂ) : b w ≤ 1 := (scaledSchauderBump_range r w).2
  refine ⟨{
    near := fun w => b w • K w
    far := fun w => (1-b w) • K w
    smooth_near := hb.smul hK
    smooth_far := (contDiff_const.sub hb).smul hK
    compact_near := hcK.smul_left (f := b)
    compact_far := hcK.smul_left (f := fun w => (1:ℝ)-b w)
    sum_eq := fun w => by rw [← add_smul]; simp
    support_near := (tsupport_smul_subset_left b K).trans (scaledSchauderBump_tsupport hr)
    support_far := ?_
    bound_near := ?_
    bound_far := ?_ }⟩
  · intro w hw
    rw [notMem_tsupport_iff_eventuallyEq]
    filter_upwards [scaledSchauderBump_eventually_one hr hw] with z hz
    simp only [b, hz, sub_self, zero_smul, Pi.zero_apply]
  · intro w hw
    apply first_near_bound hK hb hM hC₁ hw
    · rw [Real.norm_of_nonneg (hb0 w)]; exact hb1 w
    · exact (hMjet r hr w hw).1
    · exact (hjet w hw).1
    · exact (hjet w hw).2.1
  · intro w hw
    apply second_far_bound hK hb hM hC₁ hC₂ hw
    · rw [Real.norm_of_nonneg (sub_nonneg.mpr (hb1 w))]; linarith [hb0 w]
    · exact (hMjet r hr w hw).1
    · exact (hMjet r hr w hw).2
    · exact (hjet w hw).1
    · exact (hjet w hw).2.1
    · exact (hjet w hw).2.2

lemma cutoff_smoothCauchyKernel_splits (b : ContDiffBump (0:ℂ)) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ δ : ℝ, 0 < δ → ∀ r : ℝ, 0 < r →
      Nonempty (SchauderSplit (fun w => b w • smoothCauchyKernel δ w) r A B) := by
  obtain ⟨C₁,C₂,hC₁,hC₂,hjet⟩ := cutoff_smoothCauchyKernel_jet_bounds b
  obtain ⟨A,B,hA,hB,h⟩ := schauderSplit_exists_uniform hC₁ hC₂
  refine ⟨A,B,hA,hB,fun δ hδ r hr => h _ (b.contDiff.smul (smoothCauchyKernel_smooth hδ))
    (b.hasCompactSupport.smul_right (f' := smoothCauchyKernel δ)) (hjet δ hδ) r hr⟩


end
section
open scoped ContDiff Topology
open Set Filter MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

lemma SchauderSplit.holder_bound {K : ℂ → ℂ} {r A B H : ℝ}
    (s : SchauderSplit K r A B) (hr : 0 < r) (hA : 0 ≤ A) (hB : 0 ≤ B) (hH : 0 ≤ H)
    {g : ℂ → E} (hgC : Continuous g)
    (hg : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) {x y : ℂ} (hxy : ‖x-y‖ = r) :
    ‖fderiv ℝ (convolution K g (ContinuousLinearMap.lsmul ℝ ℂ) volume) x -
        fderiv ℝ (convolution K g (ContinuousLinearMap.lsmul ℝ ℂ) volume) y‖ ≤
      (2*A*(∫ w, schauderNearWeight w)+B*(∫ w, schauderFarWeight w))*H*r^((1:ℝ)/3) := by
  let WN := fun w => A*H*scaledSchauderWeight (-(5:ℝ)/3) schauderNearWeight r w
  let WF := fun w => B*H*scaledSchauderWeight (-(8:ℝ)/3) schauderFarWeight r w
  have hN : Integrable WN := (scaledSchauderWeight_integrable schauderNearWeight_integrable _ hr).const_mul _
  have hF : Integrable WF := (scaledSchauderWeight_integrable schauderFarWeight_integrable _ hr).const_mul _
  have hF0 (w : ℂ) : 0 ≤ WF w := by
    dsimp [WF, scaledSchauderWeight]
    exact mul_nonneg (mul_nonneg hB hH) (mul_nonneg (Real.rpow_nonneg hr.le _) (schauderFarWeight_nonneg _))
  have he := compact_convolution_split_derivative_bound s.smooth_near s.compact_near
    s.smooth_far s.compact_far s.sum_eq hgC hN hF hF0
    (s.near_weight_bound hr hA hH hg) (s.far_weight_bound hr hB hH hg) x y
  apply he.trans_eq
  simp only [WN, WF, integral_const_mul, integral_scaledSchauderWeight _ _ hr, hxy]
  have hpow : r^(-(8:ℝ)/3+2)*r = r^((1:ℝ)/3) := by
    calc
      _ = r^(-(8:ℝ)/3+2)*r^(1:ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hr]; norm_num
  have hpowN : r^(-(5:ℝ)/3+2) = r^((1:ℝ)/3) := by norm_num
  rw [hpowN]
  calc
    _ = (2*A*(∫ w, schauderNearWeight w))*H*r^((1:ℝ)/3) +
        (B*(∫ w, schauderFarWeight w))*H*(r^(-(8:ℝ)/3+2)*r) := by ring
    _ = _ := by rw [hpow]; ring

lemma cutoff_smoothCauchyKernel_full_schauder (b : ContDiffBump (0:ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : ℂ → E, Continuous g → ∀ H : ℝ, 0 ≤ H →
      (∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) → ∀ δ : ℝ, 0 < δ → ∀ x y : ℂ,
      ‖fderiv ℝ (convolution (fun w => b w • smoothCauchyKernel δ w) g
          (ContinuousLinearMap.lsmul ℝ ℂ) volume) x -
        fderiv ℝ (convolution (fun w => b w • smoothCauchyKernel δ w) g
          (ContinuousLinearMap.lsmul ℝ ℂ) volume) y‖ ≤ C*H*‖x-y‖^((1:ℝ)/3) := by
  obtain ⟨A,B,hA,hB,h⟩ := cutoff_smoothCauchyKernel_splits b
  refine ⟨2*A*(∫ w, schauderNearWeight w)+B*(∫ w, schauderFarWeight w), ?_, ?_⟩
  · have hN : 0 ≤ ∫ w, schauderNearWeight w := integral_nonneg schauderNearWeight_nonneg
    have hF : 0 ≤ ∫ w, schauderFarWeight w := integral_nonneg schauderFarWeight_nonneg
    positivity
  · intro g hgC H hH hg δ hδ x y
    by_cases hxy : x = y
    · subst y; simp only [sub_self, norm_zero,
        Real.zero_rpow (by norm_num : (1:ℝ)/3 ≠ 0), mul_zero, le_refl]
    · obtain ⟨s⟩ := h δ hδ ‖x-y‖ (norm_pos_iff.mpr (sub_ne_zero.mpr hxy))
      exact s.holder_bound (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) hA hB hH hgC hg rfl


end
section
open scoped ContDiff Topology
open Set Filter MeasureTheory

 theorem cutoff_smoothCauchyKernel_bound (b : ContDiffBump (0:ℂ)) :
    ∃ C : ℝ, 0≤C ∧ ∀ δ : ℝ, 0<δ → ∀ z v : ℂ, z≠0 →
      ‖fderiv ℝ (fun w => b w • smoothCauchyKernel δ w) z v‖ ≤
        (C*‖z‖⁻¹+3/‖z‖^2)*‖v‖ := by
  have hbs : ContDiff ℝ ∞ b := b.contDiff
  obtain ⟨D,hD⟩ := (isCompact_closedBall (0:ℂ) b.rOut).exists_bound_of_continuousOn
    ((hbs.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).continuous.continuousOn)
  refine ⟨max D 0,le_max_right _ _,?_⟩
  intro δ hδ z v hz
  by_cases hzb : z ∈ Metric.closedBall (0:ℂ) b.rOut
  · have hDb : ‖fderiv ℝ b z v‖ ≤ max D 0*‖v‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right
        ((hD z hzb).trans (le_max_left _ _)) (norm_nonneg _))
    have hd := (hbs.differentiable (by simp) z).hasFDerivAt.smul
      ((smoothCauchyKernel_smooth hδ).differentiable (by simp) z).hasFDerivAt
    rw [show fderiv ℝ (fun w => b w • smoothCauchyKernel δ w) z = _ from hd.fderiv]
    simp only [add_apply,smul_apply,ContinuousLinearMap.smulRight_apply]
    calc
      _ ≤ |b z| *‖fderiv ℝ (smoothCauchyKernel δ) z v‖+
        ‖fderiv ℝ b z v‖*‖smoothCauchyKernel δ z‖ := by
        simpa only [norm_smul,Real.norm_eq_abs] using norm_add_le
          (b z • fderiv ℝ (smoothCauchyKernel δ) z v)
          (fderiv ℝ b z v • smoothCauchyKernel δ z)
      _ ≤ 1*((3/‖z‖^2)*‖v‖)+(max D 0*‖v‖)*‖z‖⁻¹ := by
        exact add_le_add (mul_le_mul (by simpa only [abs_of_nonneg b.nonneg] using b.le_one)
          (smoothCauchyKernel_fderiv_norm hδ hz v) (norm_nonneg _) zero_le_one)
          (mul_le_mul hDb (smoothCauchyKernel_norm hδ z) (norm_nonneg _) (by positivity))
      _ = _ := by ring
  · have ht : z ∉ tsupport (fun w => b w • smoothCauchyKernel δ w) := by
      intro hh
      apply hzb
      exact (b.tsupport_eq ▸ tsupport_smul_subset_left _ _ hh)
    rw [fderiv_of_notMem_tsupport (𝕜 := ℝ) ht,zero_apply,norm_zero]
    positivity


end
section
open scoped ContDiff Topology
open Set Filter MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
 theorem cutoff_smoothCauchyKernel_convolution_tendsto
    (b : ContDiffBump (0:ℂ)) {g : ℂ → E} (hg : Continuous g) (x : ℂ) :
    Tendsto (fun δ : ℝ => convolution (fun w => b w • smoothCauchyKernel δ w)
      g (ContinuousLinearMap.lsmul ℝ ℂ) volume x) (𝓝[>] 0)
      (𝓝 (convolution (fun w => b w • w⁻¹) g (ContinuousLinearMap.lsmul ℝ ℂ) volume x)) := by
  have hv : Continuous (fun w : ℂ => b w • g (x-w)) :=
    b.continuous.smul (hg.comp (continuous_const.sub continuous_id))
  have hc : HasCompactSupport (fun w : ℂ => b w • g (x-w)) := b.hasCompactSupport.smul_right
  have hi := locallyIntegrable_complex_inv.integrable_smul_right_of_hasCompactSupport hv hc
  apply tendsto_integral_filter_of_dominated_convergence
    (fun w : ℂ => ‖w⁻¹ • (b w • g (x-w))‖)
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact (((b.continuous.smul (smoothCauchyKernel_smooth hδ).continuous).smul
      (hg.comp (continuous_const.sub continuous_id))).aestronglyMeasurable)
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    apply Eventually.of_forall
    intro w
    change ‖(b w • smoothCauchyKernel δ w) • g (x-w)‖ ≤ _
    simp only [norm_smul,norm_inv,Real.norm_eq_abs]
    nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (smoothCauchyKernel_norm hδ w) (abs_nonneg (b w))) (norm_nonneg (g (x-w)))]
  · exact hi.norm
  · apply Eventually.of_forall
    intro w
    exact (tendsto_const_nhds.smul (smoothCauchyKernel_tendsto w)).smul tendsto_const_nhds


end
section
open scoped ContDiff Topology
open Set Filter MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

lemma cutoff_smoothCauchyKernel_derivative_tendsto (b : ContDiffBump (0:ℂ))
    {g : ℂ → E} (hgC : Continuous g) {H : ℝ} (hH : 0 ≤ H)
    (hg : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) (x : ℂ) :
    Tendsto (fun δ : ℝ => fderiv ℝ
      (convolution (fun w => b w • smoothCauchyKernel δ w) g
        (ContinuousLinearMap.lsmul ℝ ℂ) volume) x) (𝓝[>] 0)
      (𝓝 (cutoffCauchyDerivative b g x)) := by
  obtain ⟨C,hC,hCb⟩ := cutoff_smoothCauchyKernel_bound b
  let W : ℂ → ℝ := fun w => (C+3)*H*cauchySchauderWeight b.rOut w
  have hW : Integrable W := (cauchySchauderWeight_integrable b.rOut).const_mul _
  have hi (δ : ℝ) (hδ : 0 < δ) : Integrable (cancellationJetIntegrand b δ g x) :=
    hW.mono' (cancellationJetIntegrand_continuous b hδ hgC x).aestronglyMeasurable
      (Eventually.of_forall (cancellationJetIntegrand_bound b hC hCb hH hg hδ x))
  have he (δ : ℝ) (hδ : 0 < δ) : fderiv ℝ
      (convolution (fun w => b w • smoothCauchyKernel δ w) g
        (ContinuousLinearMap.lsmul ℝ ℂ) volume) x =
      ∫ w : ℂ, cancellationJetIntegrand b δ g x w := by
    ext v
    rw [ContinuousLinearMap.integral_apply (hi δ hδ)]
    rw [compact_kernel_convolution_cancel (K := fun w => b w • smoothCauchyKernel δ w) (b.contDiff.smul (smoothCauchyKernel_smooth hδ))
      (b.hasCompactSupport.smul_right (f' := smoothCauchyKernel δ)) hgC]
    apply integral_congr_ae
    exact Eventually.of_forall fun w => by
      dsimp only
      rw [cancellationJetIntegrand_apply, cutoffCauchyJet_eq b hδ]
  have hEq : (fun δ : ℝ => ∫ w : ℂ, cancellationJetIntegrand b δ g x w) =ᶠ[𝓝[>] 0]
      (fun δ : ℝ => fderiv ℝ (convolution (fun w => b w • smoothCauchyKernel δ w) g
        (ContinuousLinearMap.lsmul ℝ ℂ) volume) x) := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact (he δ hδ).symm
  apply Tendsto.congr' hEq
  apply tendsto_integral_filter_of_dominated_convergence W
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact (cancellationJetIntegrand_continuous b hδ hgC x).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact Eventually.of_forall (cancellationJetIntegrand_bound b hC hCb hH hg hδ x)
  · exact hW
  · exact Eventually.of_forall (cancellationJetIntegrand_tendsto b g x)


end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Holder_HolderTaylor
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity
open scoped Topology
open Set Filter
open scoped ContDiff
open MeasureTheory
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

lemma cutoffCauchyDerivative_holder (b : ContDiffBump (0:ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : ℂ → E, Continuous g → ∀ H : ℝ, 0 ≤ H →
      (∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) → ∀ x y : ℂ,
      ‖cutoffCauchyDerivative b g x-cutoffCauchyDerivative b g y‖ ≤ C*H*‖x-y‖^((1:ℝ)/3) := by
  obtain ⟨C,hC,h⟩ := cutoff_smoothCauchyKernel_full_schauder (E := E) b
  refine ⟨C,hC,?_⟩
  intro g hgC H hH hg x y
  apply le_of_tendsto (((cutoff_smoothCauchyKernel_derivative_tendsto b hgC hH hg x).sub
    (cutoff_smoothCauchyKernel_derivative_tendsto b hgC hH hg y)).norm)
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact h g hgC H hH hg δ hδ x y

lemma cutoffCauchy_hasFDerivAt (b : ContDiffBump (0:ℂ)) {g : ℂ → E}
    (hgC : Continuous g) {H : ℝ} (hH : 0 ≤ H)
    (hg : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) (x : ℂ) :
    HasFDerivAt (convolution (fun w => b w • w⁻¹) g (ContinuousLinearMap.lsmul ℝ ℂ) volume)
      (cutoffCauchyDerivative b g x) x := by
  obtain ⟨C,hC,h⟩ := cutoff_smoothCauchyKernel_full_schauder (E := E) b
  apply hasFDerivAt_of_holder_remainder (C := C*H) (α := (1:ℝ)/3) _ x (by norm_num)
  intro v
  have hd := (ContinuousLinearMap.apply ℝ E v).continuous.tendsto (cutoffCauchyDerivative b g x)
    |>.comp (cutoff_smoothCauchyKernel_derivative_tendsto b hgC hH hg x)
  have ht := (((cutoff_smoothCauchyKernel_convolution_tendsto b hgC (x+v)).sub
    (cutoff_smoothCauchyKernel_convolution_tendsto b hgC x)).sub hd).norm
  apply le_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hK : ContDiff ℝ ∞ (fun w => b w • smoothCauchyKernel δ w) :=
    b.contDiff.smul (smoothCauchyKernel_smooth hδ)
  have hcK : HasCompactSupport (fun w => b w • smoothCauchyKernel δ w) :=
    b.hasCompactSupport.smul_right (f' := smoothCauchyKernel δ)
  have hf : Differentiable ℝ
      (convolution (fun w => b w • smoothCauchyKernel δ w) g (ContinuousLinearMap.lsmul ℝ ℂ) volume) :=
    fun z => (hcK.hasFDerivAt_convolution_left _ (hK.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) hgC.locallyIntegrable z).differentiableAt
  exact holder_taylor_remainder hf (mul_nonneg hC hH) (by norm_num : (0:ℝ) ≤ (1:ℝ)/3)
    (h g hgC H hH hg δ hδ) x v

end
section

lemma tailCauchyKernel_uniform_bounds :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ δ : ℝ, 0 < δ → ∀ z : ℂ,
      ‖tailCauchyKernel δ z‖ ≤ 1 ∧ ‖fderiv ℝ (tailCauchyKernel δ) z‖ ≤ A ∧
        ‖iteratedFDeriv ℝ 2 (tailCauchyKernel δ) z‖ ≤ B := by
  obtain ⟨M,hM,hjet⟩ := scaledSchauderBump_homogeneous_bounds
  refine ⟨3+2*M,14+4*M*3+4*M,by positivity,by positivity,?_⟩
  intro δ hδ z
  by_cases hz : ‖z‖ ≤ 1
  · have he := tailCauchyKernel_eventually_zero δ hz
    have hd : fderiv ℝ (tailCauchyKernel δ) z = 0 := he.fderiv_eq.trans (by simp)
    have hd2 : iteratedFDeriv ℝ 2 (tailCauchyKernel δ) z = 0 :=
      (he.iteratedFDeriv (𝕜 := ℝ) 2).eq_of_nhds.trans (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    simp only [he.eq_of_nhds, hd, hd2, norm_zero]
    exact ⟨zero_le_one, by positivity, by positivity⟩
  · have hz1 : 1 < ‖z‖ := lt_of_not_ge hz
    have hz0 : z ≠ 0 := norm_pos_iff.mp (by linarith)
    have hb := scaledSchauderBump_range 1 z
    have hbn : ‖1-scaledSchauderBump 1 z‖ ≤ 1 := by
      rw [Real.norm_of_nonneg (sub_nonneg.mpr hb.2)]
      linarith [hb.1]
    have h0 := smoothCauchyKernel_norm hδ z
    have h1 := smoothCauchyKernel_first_opNorm hδ hz0
    have h2 := smoothCauchyKernel_second_opNorm hδ hz0
    have hj := hjet 1 (by norm_num) z hz0
    refine ⟨?_,?_,?_⟩
    · calc
        _ ≤ 1*‖z‖⁻¹ := by
          rw [tailCauchyKernel, norm_smul]
          exact mul_le_mul hbn h0 (norm_nonneg _) zero_le_one
        _ ≤ 1 := by rw [one_mul]; exact inv_le_one_of_one_le₀ hz1.le
    · have hd := first_near_bound (smoothCauchyKernel_smooth hδ)
        (contDiff_const.sub (scaledSchauderBump_smooth 1)) hM (by norm_num : (0:ℝ) ≤ 3)
        hz0 hbn (by rw [fderiv_const_sub, norm_neg]; exact hj.1) h0 h1
      exact hd.trans (div_le_self (by positivity) (one_le_pow₀ hz1.le))
    · have hd := second_far_bound (smoothCauchyKernel_smooth hδ) (scaledSchauderBump_smooth 1)
        hM (by norm_num : (0:ℝ) ≤ 3) (by norm_num : (0:ℝ) ≤ 14)
        hz0 hbn hj.1 hj.2 h0 h1 h2
      exact hd.trans (div_le_self (by positivity) (one_le_pow₀ hz1.le))

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.instNormedAddCommGroupContinuousLinearMapRealIdComplex_solutions_2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.instNormedSpaceRealContinuousLinearMapIdComplex_solutions_2
local instance instNormedAddCommGroupContinuousLinearMapRealIdComplex_solutions_3_r93e0b2_1 : NormedAddCommGroup (ℂ →L[ℝ] ℂ →L[ℝ] ℂ) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealContinuousLinearMapIdComplex_solutions_3_r93e0b2_1 : NormedSpace ℝ (ℂ →L[ℝ] ℂ →L[ℝ] ℂ) := ContinuousLinearMap.toNormedSpace
lemma tailCauchyKernel_hasFDerivAt (z : ℂ) :
    HasFDerivAt (tailCauchyKernel 0) (tailCauchyJet 0 z) z := by
  obtain ⟨A,B,hA,hB,hjet⟩ := tailCauchyKernel_uniform_bounds
  apply hasFDerivAt_limit_of_holder_derivative (M := B) (α := 1) hB (by norm_num)
    (l := 𝓝[>] (0:ℝ)) (f := tailCauchyKernel) (L := tailCauchyJet)
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    intro w
    rw [← tailCauchyJet_eq hδ]
    exact ((tailCauchyKernel_smooth hδ).differentiable (by simp) w).hasFDerivAt
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    intro w t
    simp_rw [← tailCauchyJet_eq hδ]
    rw [Real.rpow_one]
    apply HolderCompletion.norm_sub_le_of_deriv_bound
      (((tailCauchyKernel_smooth hδ).fderiv_right (m := ∞) (by simp)).differentiable (by simp))
    intro u
    rw [← norm_second_jet]
    exact (hjet δ hδ u).2.2
  · exact tailCauchyKernel_tendsto
  · exact tailCauchyJet_tendsto

lemma tailCauchyKernel_bounds :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      (∀ z : ℂ, ‖tailCauchyKernel 0 z‖ ≤ 1 ∧ ‖tailCauchyJet 0 z‖ ≤ A) ∧
      (∀ z w : ℂ, ‖tailCauchyJet 0 z-tailCauchyJet 0 w‖ ≤ B*‖z-w‖) := by
  obtain ⟨A,B,hA,hB,hjet⟩ := tailCauchyKernel_uniform_bounds
  refine ⟨A,B,hA,hB,?_,?_⟩
  · intro z
    constructor
    · apply le_of_tendsto (tailCauchyKernel_tendsto z).norm
      filter_upwards [self_mem_nhdsWithin] with δ hδ
      exact (hjet δ hδ z).1
    · apply le_of_tendsto (tailCauchyJet_tendsto z).norm
      filter_upwards [self_mem_nhdsWithin] with δ hδ
      rw [← tailCauchyJet_eq hδ]
      exact (hjet δ hδ z).2.1
  · intro z w
    apply le_of_tendsto ((tailCauchyJet_tendsto z).sub (tailCauchyJet_tendsto w)).norm
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    simp_rw [← tailCauchyJet_eq hδ]
    apply HolderCompletion.norm_sub_le_of_deriv_bound
      (((tailCauchyKernel_smooth hδ).fderiv_right (m := ∞) (by simp)).differentiable (by simp))
    intro u
    rw [← norm_second_jet]
    exact (hjet δ hδ u).2.2

lemma tailCauchyKernel_contDiff_one : ContDiff ℝ 1 (tailCauchyKernel 0) := by
  rw [contDiff_one_iff_fderiv]
  refine ⟨fun z => (tailCauchyKernel_hasFDerivAt z).differentiableAt,?_⟩
  have he : fderiv ℝ (tailCauchyKernel 0) = tailCauchyJet 0 :=
    funext fun z => (tailCauchyKernel_hasFDerivAt z).fderiv
  rw [he]
  obtain ⟨A,B,hA,hB,hjet,hL⟩ := tailCauchyKernel_bounds
  exact holder_continuous (α := 1) (by norm_num) (by simpa only [Real.rpow_one] using hL)

end

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

lemma tailCauchyJet_continuous : Continuous (tailCauchyJet 0) := by
  obtain ⟨A,B,hA,hB,hjet,hL⟩ := tailCauchyKernel_bounds
  exact holder_continuous (α := 1) (by norm_num) (by simpa only [Real.rpow_one] using hL)

omit [CompleteSpace E] in
lemma tailIntegralJet_continuous {g : ℂ → E} (hg : Continuous g) (x : ℂ) :
    Continuous (tailIntegralJet g x) :=
  (((ContinuousLinearMap.lsmul ℝ ℂ).flip).continuous.comp hg).clm_comp
    (tailCauchyJet_continuous.comp (continuous_const.sub continuous_id))

omit [CompleteSpace E] in
lemma cauchy_kernel_convolution_split {g : ℂ → E} (hg : Continuous g) (hi : Integrable g) :
    convolution (fun w : ℂ => w⁻¹) g (ContinuousLinearMap.lsmul ℝ ℂ) volume =
      (fun x => convolution (fun w => schauderBump w • w⁻¹) g
        (ContinuousLinearMap.lsmul ℝ ℂ) volume x + tailCauchyTransform g x) := by
  funext x
  have htail : Integrable (fun w : ℂ => tailCauchyKernel 0 w • g (x-w)) := by
    have hc : Continuous (fun w => tailCauchyKernel 0 (x-w) • g w) :=
      (tailCauchyKernel_contDiff_one.continuous.comp (continuous_const.sub continuous_id)).smul hg
    obtain ⟨A,B,hA,hB,hjet,hL⟩ := tailCauchyKernel_bounds
    have hh : Integrable (fun w : ℂ => tailCauchyKernel 0 (x-w) • g w) :=
      hi.norm.mono' hc.aestronglyMeasurable (Eventually.of_forall fun w => by
        rw [norm_smul]
        exact (mul_le_mul_of_nonneg_right (hjet _).1 (norm_nonneg _)).trans_eq (one_mul _))
    simpa only [sub_sub_self] using hh.comp_sub_left x
  have he (w : ℂ) : w⁻¹ = (schauderBump w • w⁻¹) + tailCauchyKernel 0 w := by
    rw [tailCauchyKernel_zero, ← add_smul]; simp
  change (∫ w : ℂ, w⁻¹ • g (x-w)) =
    (∫ w : ℂ, (schauderBump w • w⁻¹) • g (x-w)) +
    (∫ w : ℂ, tailCauchyKernel 0 w • g (x-w))
  rw [← integral_add (cutoffCauchy_convolution_integrable schauderBump hg x) htail]
  apply integral_congr_ae
  exact Eventually.of_forall fun w => by dsimp only; rw [← add_smul, ← he]

end HigherDimensionalBallPacking.Rigidity

namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable {K : Set ℂ} (hK : IsCompact K)
local instance instNormedAddCommGroupSubtypeAmbientComplexMemSubmoduleRealHMap : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance instNormedSpaceRealSubtypeAmbientComplexMemSubmoduleHMap_r93e0b2_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
local instance instNormedAddCommGroupSubtypeAmbientComplexMemSubmoduleRealHMapSupportedHolder : NormedAddCommGroup (supportedHolder (E := E) K) := inferInstance
local instance instNormedSpaceRealSubtypeAmbientComplexMemSubmoduleHMapSupportedHolder_r93e0b2_1 : NormedSpace ℝ (supportedHolder (E := E) K) := inferInstance
local instance instNormedAddCommGroupSubtypeJetAmbientComplexHDivRealOfNatMemSubmoduleCOne : NormedAddCommGroup (COne ℂ E) := inferInstance
include hK

local instance instNormedSpaceRealSubtypeJetAmbientComplexHDivOfNatMemSubmoduleCOne_r93e0b2_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
omit [CompleteSpace E] in
lemma supportedHolder_hasCompactSupport (g : supportedHolder (E := E) K) :
    HasCompactSupport (valueCLM _ g.val) := by
  apply HasCompactSupport.intro hK
  exact (mem_supportedHolder g.val K).mp g.property

omit [CompleteSpace E] in
lemma supportedHolder_integrable (g : supportedHolder (E := E) K) :
    Integrable (valueCLM _ g.val) :=
  (valueCLM _ g.val).continuous.integrable_of_hasCompactSupport
    (supportedHolder_hasCompactSupport hK g)

omit [CompleteSpace E] in
lemma supportedHolder_integral_norm_le (g : supportedHolder (E := E) K) :
    (∫ x : ℂ, ‖valueCLM _ g.val x‖) ≤ ‖g‖ * volume.real K := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := K)
    (fun x hx => by rw [(mem_supportedHolder g.val K).mp g.property x hx, norm_zero])]
  apply le_trans (le_abs_self _)
  exact norm_setIntegral_le_of_norm_le_const (f := fun x => ‖valueCLM _ g.val x‖) hK.measure_lt_top (fun x _ => by
    rw [Real.norm_eq_abs, abs_norm]
    exact norm_value_le g.val x)

end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moser_CircleCorrection
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology NNReal
open Set Metric
open scoped Classical
open Function MeasureTheory

def closedRoundDisk (R : ℝ) : Set Plane := {p | radiusSq p ≤ R^2}

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Rigidity_RadialForm
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SymplecticBallPacking.Hamiltonian
open scoped ContDiff Topology
open Set Function Filter MeasureTheory

def planarArea : Plane →L[ℝ] Plane →L[ℝ] ℝ :=
  (ContinuousLinearMap.mul ℝ ℝ).bilinearComp (ContinuousLinearMap.fst ℝ ℝ ℝ)
    (ContinuousLinearMap.snd ℝ ℝ ℝ) -
  (ContinuousLinearMap.mul ℝ ℝ).bilinearComp (ContinuousLinearMap.snd ℝ ℝ ℝ)
    (ContinuousLinearMap.fst ℝ ℝ ℝ)

@[simp] theorem planarArea_apply (v w : Plane) : planarArea v w = v.1*w.2-v.2*w.1 := rfl
def radiusSq (p : Plane) : ℝ := p.1^2+p.2^2

end SymplecticBallPacking.Hamiltonian
end

end OAI
end


