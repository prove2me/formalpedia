-- Prove2me | Definitions.Def_OAIErdos3B1400
-- name    : OAIErdos3B1400
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-16T08:44:44.089091+00:00
-- url     : https://prove2.me/theorems/92da6c42-10eb-4daa-b542-229f7f18e8d6
-- title:
--   OpenAI Erdős-3 split, definitions bundle 1401 of 1413
-- statement:
--   Definitions bundle 1401 of 1413 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B1399`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 1401 available.
--
--   Modules: `OAI.Erdos3.VectorPolynomial.NormalizedPolynomialTwist.forecastShortGridTest_bounds`, `OAI.Erdos3.VectorPolynomial.affineFixedPathCRTModulusNeZero`, `OAI.Erdos3.VectorPolynomial.allocatedAffineFixedPath_crtRationalForecast_reference`, `OAI.Erdos3.VectorPolynomial.allocatedContainedKernel_supported_narrow_physical_dist`, `OAI.Erdos3.VectorPolynomial.allocatedFixedSpatialKernelMap_narrow_physical_dist`, `OAI.Erdos3.VectorPolynomial.allocatedFixedSpatialKernelMap_supported_narrow_physical_dist`, `OAI.Erdos3.VectorPolynomial.allocatedJointResidueOutput_join`, `OAI.Erdos3.VectorPolynomial.forecastInactiveFixedOutput_congr_restrict`, `OAI.Erdos3.VectorPolynomial.forecastInactiveFixedOutput_congr_selected`, `OAI.Erdos3.VectorPolynomial.forecastInactiveFixedOutput_congr_short_restrict`, `OAI.Erdos3.VectorPolynomial.forecastInactiveFixedOutput_eq_shortGrid`, `OAI.Erdos3.arbitraryStepForecastModulusNeZero`, `OAI.Erdos3.containedKernelCubeMap_normalized`, `OAI.Erdos3.containedKernelCubeMap_value`, `OAI.Erdos3.fixedSpatialKernelMap_integer`, `OAI.Erdos3.fixedSpatialKernelMap_narrow_physical_dist`, `OAI.Erdos3.fixedSpatialKernelRest_measurable`, `OAI.Erdos3.rationalInactivePolynomialForecast_arbitraryStepCRT_tsum_marginal`, `OAI.Erdos3.rectangularWeightIndices_normalized_norm_le`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1389

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ContainedKernelPhysicalDisplacement
namespace OAI

section

namespace Erdos3
open BooleanCubeKernel
open scoped BigOperators Classical NNReal
variable {G X : Type*} [Fintype G] [Fintype X]

variable [DecidableEq G]

omit [Fintype X] in
theorem fixedSpatialKernelMap_integer (s : Empty ↪ G) (root : G → ℤ)
    (D : Matrix Empty G ℤ) {W L : ℝ} (hW : 0 ≤ W) (hL : L ≠ 0)
    (z : Option G × X → ℝ) :
    fixedSpatialKernelMap W L z (fun g => (root g : ℝ) / L) =
      canonicalZeroSpatialInputMap s root D W L z := by
  funext a
  rcases a with ⟨x, a⟩
  cases a with
  | inr e => exact Empty.elim e
  | inl u =>
    cases u
    rw [canonicalZeroSpatialInputMap_apply s root D W L hW]
    unfold fixedSpatialKernelMap
    simp only
    congr 1
    rw [Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro g _
    field_simp

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical
variable {G X T : Type*} [Fintype G] [Fintype X] [Fintype T]

omit [Fintype G] [Fintype X] in
theorem fixedSpatialKernelRest_measurable (e : G ≃ X ⊕ (X ⊕ T))
    (W L : ℝ) (z : Option G × X → ℝ) :
    Measurable (fixedSpatialKernelRest e W L z) := by
  unfold fixedSpatialKernelRest
  fun_prop

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators Classical NNReal

theorem rectangularWeightIndices_normalized_norm_le
    {K : Type*} [Fintype K] (V : K → ℝ) (hV : ∀ k, 0 < V k)
    {z : K → ℤ} (hz : z ∈ rectangularWeightIndices 0 V 1) :
    ‖fun k => (z k : ℝ) / V k‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro k
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (hV k), div_le_one (hV k)]
  exact rectangularWeightIndices_zero_bound V hz k

variable {G N X : Type*} [Fintype G] [DecidableEq G]
  [Fintype N] [DecidableEq N] [Fintype X]

theorem fixedSpatialKernelMap_narrow_physical_dist
    (root : G → ℤ) (principal : N → ℤ) {W L τ ξ : ℝ}
    (hW : 0 ≤ W) (hL : L ≠ 0) (hξ : 0 < ξ)
    (hbudget : (∑ k : G ⊕ N, |((Sum.elim root principal k : ℤ) : ℝ)|) ≤ W)
    (box : X → ℕ) (z : Option (G ⊕ N) × X → ℤ)
    (hz : ‖fun k => (z k : ℝ) / narrowTrimmedSpatialWidths W τ ξ box k‖ ≤ 1) :
    dist (fun o : Σ _ : X, Unit ⊕ Empty =>
        (integerPhysicalSite (Sum.elim root principal) z o.1 : ℝ) /
          (τ * (box o.1 : ℝ) / 8))
      (fixedSpatialKernelMap W L
        ((fun k => (z k : ℝ) / narrowTrimmedSpatialWidths W τ ξ box k) ∘
          canonicalZeroSpatialKernelEmbedding G N X)
        (fun g => (root g : ℝ) / L)) ≤ ξ := by
  let s : Empty ↪ G := ⟨Empty.elim, fun e => Empty.elim e⟩
  let sf : Empty ↪ (G ⊕ N) := ⟨Empty.elim, fun e => Empty.elim e⟩
  let D : Matrix Empty G ℤ := fun e => Empty.elim e
  let Df : Matrix Empty (G ⊕ N) ℤ := fun e => Empty.elim e
  have hsite : canonicalZeroSpatialInputMap sf (Sum.elim root principal) Df W L
      (canonicalZeroSpatialNarrowInput ξ
        (fun k => (z k : ℝ) / narrowTrimmedSpatialWidths W τ ξ box k)) =
      fun o : Σ _ : X, Unit ⊕ Empty =>
        (integerPhysicalSite (Sum.elim root principal) z o.1 : ℝ) /
          (τ * (box o.1 : ℝ) / 8) := by
    funext o
    rcases o with ⟨x, a⟩
    cases a with
    | inr e => exact Empty.elim e
    | inl a =>
      cases a
      exact canonicalZeroSpatialNarrowInputMap_physicalSite sf _ Df hW hξ.ne' L τ box z x
  rw [fixedSpatialKernelMap_integer s root D hW hL, ← hsite, dist_eq_norm]
  exact (canonicalZeroSpatialNarrowPrincipal_norm_le s sf root principal D Df W L
    hW ξ hξ.le _ hz).trans (mul_le_of_le_one_right hξ.le
      (canonicalZeroSpatialPrincipal_mass_ratio_le_one root principal W hW hbudget))

namespace VectorPolynomial

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "principal" => PrincipalTupleIndex B (layerSamplerDegree I n)
local notation "vars" => LayerSamplerVariables G I n B
local notation "budget" => allocatedPhysicalRootBudget B U basis S (fun _ => 0)

theorem allocatedFixedSpatialKernelMap_narrow_physical_dist
    (x : G → IntegerScalarCubeBox Empty S.value)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S))
    {τ ξ : ℝ} (hξ : 0 < ξ) (box : X → ℕ)
    (z : Option vars × X → ℤ)
    (hz : ‖fun k => (z k : ℝ) /
      narrowTrimmedSpatialWidths (G := G) (J := principal) budget τ ξ box k‖ ≤ 1) :
    dist (fun o : Σ _ : X, Unit ⊕ Empty =>
        (integerPhysicalSite (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y) z o.1 : ℝ) /
          (τ * (box o.1 : ℝ) / 8))
      (fixedSpatialKernelMap budget (S.value : ℝ)
        ((fun k => (z k : ℝ) / narrowTrimmedSpatialWidths budget τ ξ box k) ∘
          canonicalZeroSpatialKernelEmbedding G principal X)
        (fun g => ((x g none : ℤ) : ℝ) / (S.value : ℝ))) ≤ ξ := by
  have hr : allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y =
      Sum.elim (fun g => (x g none : ℤ)) (fun j => (y j none : ℤ)) := by
    funext k
    simp only [allocatedPhysicalCubeRoot, zero_add]
  have hbudget : (∑ k : vars,
      |((Sum.elim (fun g => (x g none : ℤ)) (fun j => (y j none : ℤ)) k : ℤ) : ℝ)|) ≤ budget := by
    simpa only [hr] using allocatedPhysicalCube_root_sum B U basis S (fun _ => 0) x y
  rw [hr]
  exact fixedSpatialKernelMap_narrow_physical_dist _ _
    (allocatedPhysicalRootBudget_nonneg B U basis S (fun _ => 0))
    (Nat.cast_ne_zero.mpr S.positive.ne') hξ hbudget box z hz

theorem allocatedFixedSpatialKernelMap_supported_narrow_physical_dist
    (x : G → IntegerScalarCubeBox Empty S.value)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S))
    {τ ξ : ℝ} (hτ : 0 < τ) (hξ : 0 < ξ) (box : X → ℕ) (hbox : ∀ o, 0 < box o)
    (z : Option vars × X → ℤ)
    (hz : z ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths (G := G) (J := principal) budget τ ξ box) 1) :
    dist (fun o : Σ _ : X, Unit ⊕ Empty =>
        (integerPhysicalSite (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y) z o.1 : ℝ) /
          (τ * (box o.1 : ℝ) / 8))
      (fixedSpatialKernelMap budget (S.value : ℝ)
        ((fun k => (z k : ℝ) / narrowTrimmedSpatialWidths budget τ ξ box k) ∘
          canonicalZeroSpatialKernelEmbedding G principal X)
        (fun g => ((x g none : ℤ) : ℝ) / (S.value : ℝ))) ≤ ξ := by
  exact allocatedFixedSpatialKernelMap_narrow_physical_dist B U basis S x y hξ box z
    (rectangularWeightIndices_normalized_norm_le _
      (narrowTrimmedSpatialWidths_pos
        (allocatedPhysicalRootBudget_nonneg B U basis S (fun _ => 0)) hτ hξ box hbox) hz)

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

variable {G X T : Type*} [Fintype G] [Fintype X] [Fintype T]

variable [DecidableEq X]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {G X : Type*} [Fintype G]

variable {T : Type*} [Fintype X]

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {G : Type*} [Fintype G]

theorem containedKernelCubeMap_value (S : ℕ) (H step : G → ℕ) (c : G → ℤ)
    (hS : 0 < S) (hH : ∀ g, 0 < H g)
    (hsubset : ∀ g, integerProgressionSupport (c g) (step g : ℤ) (H g) ⊆
      Finset.Ico (0 : ℤ) (S : ℤ))
    (x : ∀ g, IntegerScalarCubeBox Empty (H g))
    (hx : (FiniteProbabilityWeights.pi
      (fun g => integerScalarCubeWeights Empty (H g) (hH g))).weight x ≠ 0)
    (g : G) :
    (containedKernelCubeMap S H step c hS hsubset x g none : ℤ) =
      c g + (step g : ℤ) * (x g none : ℤ) := by
  have hpos := lt_of_le_of_ne ((FiniteProbabilityWeights.pi
    (fun g => integerScalarCubeWeights Empty (H g) (hH g))).nonneg x) hx.symm
  have hg := FiniteProbabilityWeights.pi_weight_pos_component
    (fun g => integerScalarCubeWeights Empty (H g) (hH g)) x hpos g
  have hcube := (mem_integerScalarCubeSet (H g) (x g)).mp
    ((FiniteProbabilityWeights.condition_weight_pos_iff _ _ _ (x g)).mp hg).1
  simpa only [containedKernelCubeMap, ite_true] using
    (containedProgressionCubeMap_value Empty S (H g) (step g) (c g) hS
      (hsubset g) (x g) hcube none)

theorem containedKernelCubeMap_normalized (S : ℕ) (H step : G → ℕ) (c : G → ℤ)
    (hS : 0 < S) (hH : ∀ g, 0 < H g)
    (hsubset : ∀ g, integerProgressionSupport (c g) (step g : ℤ) (H g) ⊆
      Finset.Ico (0 : ℤ) (S : ℤ))
    (x : ∀ g, IntegerScalarCubeBox Empty (H g))
    (hx : (FiniteProbabilityWeights.pi
      (fun g => integerScalarCubeWeights Empty (H g) (hH g))).weight x ≠ 0) :
    (fun g => ((containedKernelCubeMap S H step c hS hsubset x g none : ℤ) : ℝ) / S) =
      fun g => ((c g : ℝ) + (step g : ℝ) * (x g none : ℝ)) / S := by
  funext g
  rw [containedKernelCubeMap_value S H step c hS hH hsubset x hx g]
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast]

namespace VectorPolynomial

variable {m : ℕ} {X : Type*} [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "principal" => PrincipalTupleIndex B (layerSamplerDegree I n)
local notation "vars" => LayerSamplerVariables G I n B
local notation "budget" => allocatedPhysicalRootBudget B U basis S (fun _ => 0)

theorem allocatedContainedKernel_supported_narrow_physical_dist
    (H step : G → ℕ) (c : G → ℤ) (hH : ∀ g, 0 < H g)
    (hsubset : ∀ g, integerProgressionSupport (c g) (step g : ℤ) (H g) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
    (x : ∀ g, IntegerScalarCubeBox Empty (H g))
    (hx : (FiniteProbabilityWeights.pi
      (fun g => integerScalarCubeWeights Empty (H g) (hH g))).weight x ≠ 0)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S))
    {τ ξ : ℝ} (hτ : 0 < τ) (hξ : 0 < ξ) (box : X → ℕ) (hbox : ∀ o, 0 < box o)
    (integerFrame : Option vars × X → ℤ)
    (hframe : integerFrame ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths (G := G) (J := principal) budget τ ξ box) 1) :
    dist (fun o : Σ _ : X, Unit ⊕ Empty =>
        (integerPhysicalSite (allocatedPhysicalCubeRoot B U basis S (fun _ => 0)
          (containedKernelCubeMap S.value H step c S.positive hsubset x) y) integerFrame o.1 : ℝ) /
          (τ * (box o.1 : ℝ) / 8))
      (fixedSpatialKernelMap budget (S.value : ℝ)
        ((fun k => (integerFrame k : ℝ) / narrowTrimmedSpatialWidths budget τ ξ box k) ∘
          canonicalZeroSpatialKernelEmbedding G principal X)
        (fun g => ((c g : ℝ) + (step g : ℝ) * (x g none : ℝ)) / S.value)) ≤ ξ := by
  rw [← containedKernelCubeMap_normalized S.value H step c S.positive hH hsubset x hx]
  exact allocatedFixedSpatialKernelMap_supported_narrow_physical_dist B U basis S
    (containedKernelCubeMap S.value H step c S.positive hsubset x) y
    hτ hξ box hbox integerFrame hframe

end VectorPolynomial
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastNativeJointTestBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {A : Type*}

theorem forecastInactiveFixedOutput_congr_selected
    (selected : A → Σ j : Fin m, Fin (n j))
    (hsmall : ∀ a, basisAxisScale (basis (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (c : ∀ a, BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1) → ℤ)
    (hc : ∀ a d, c a d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S
      (selected a).1 (selected a).2 d).support)
    (x x' : G → IntegerScalarCubeBox Empty S.value)
    (y y' : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
      (allocatedPrincipalSides B U basis S))
    (hy : ∀ a (b : B ⟨(selected a).1, Sum.inr (selected a).2⟩)
      (v : Fin ((selected a).1.val + 1)) (o : Option Empty),
      y ⟨⟨(selected a).1, Sum.inr (selected a).2⟩, b, v⟩ o =
        y' ⟨⟨(selected a).1, Sum.inr (selected a).2⟩, b, v⟩ o) :
    forecastInactiveFixedOutput B U basis S selected c x y =
      forecastInactiveFixedOutput B U basis S selected c x' y' := by
  funext a row
  have hmoderate := (hsmall a).trans (Nat.pow_le_pow_right S.positive
    ((layerDegree_le_tailDegree (selected a).1).trans (Nat.le_succ _)))
  unfold forecastInactiveFixedOutput
  rw [allocatedPhysicalGridJet_blocks B U basis hR hσ S (selected a).1 (selected a).2
    hmoderate (c a) (hc a) x y,
    allocatedPhysicalGridJet_blocks B U basis hR hσ S (selected a).1 (selected a).2
      hmoderate (c a) (hc a) x' y']
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  apply congrArg (fun f => integerBooleanBlockJet f (row : Finset Empty))
  funext v o
  exact congrArg Subtype.val (hy a b v o)

theorem forecastInactiveFixedOutput_congr_restrict
    (selected : A → Σ j : Fin m, Fin (n j))
    (hsmall : ∀ a, basisAxisScale (basis (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (c : ∀ a, BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1) → ℤ)
    (hc : ∀ a d, c a d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S
      (selected a).1 (selected a).2 d).support)
    (P : LayerSamplerAxis I n → Prop)
    (hselected : ∀ a, P ⟨(selected a).1, Sum.inr (selected a).2⟩)
    (x x' : G → IntegerScalarCubeBox Empty S.value)
    (y y' : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
      (allocatedPrincipalSides B U basis S))
    (hy : principalAxisRestrict P y = principalAxisRestrict P y') :
    forecastInactiveFixedOutput B U basis S selected c x y =
      forecastInactiveFixedOutput B U basis S selected c x' y' := by
  apply forecastInactiveFixedOutput_congr_selected B U basis S hR hσ
    selected hsmall c hc x x' y y'
  intro a b v o
  exact congrFun (congrFun hy ⟨⟨_, hselected a⟩, b, v⟩) o

theorem forecastInactiveFixedOutput_congr_short_restrict
    (selected : A → Σ j : Fin m, Fin (n j))
    (hsmall : ∀ a, basisAxisScale (basis (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (c : ∀ a, BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1) → ℤ)
    (hc : ∀ a d, c a d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S
      (selected a).1 (selected a).2 d).support)
    (x x' : G → IntegerScalarCubeBox Empty S.value)
    (y y' : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
      (allocatedPrincipalSides B U basis S))
    (hy : principalAxisRestrict (allocatedShortAxis U basis S.value) y =
      principalAxisRestrict (allocatedShortAxis U basis S.value) y') :
    forecastInactiveFixedOutput B U basis S selected c x y =
      forecastInactiveFixedOutput B U basis S selected c x' y' :=
  forecastInactiveFixedOutput_congr_restrict B U basis S hR hσ selected hsmall c hc
    (allocatedShortAxis U basis S.value) hsmall x x' y y' hy

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {A : Type*}

theorem forecastInactiveFixedOutput_eq_shortGrid
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (selected : A → Σ j : Fin m, Fin (n j))
    (hsmall : ∀ a, basisAxisScale (basis (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (c : ∀ a, BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1) → ℤ)
    (hc : ∀ a d, c a d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S
      (selected a).1 (selected a).2 d).support)
    (x : G → IntegerScalarCubeBox Empty S.value)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
      (allocatedPrincipalSides B U basis S)) :
    forecastInactiveFixedOutput B U basis S selected c x y =
      forecastInactiveShortGrid B U basis S selected c
        (principalAxisRestrict (allocatedShortAxis U basis S.value) y) := by
  unfold forecastInactiveShortGrid
  apply forecastInactiveFixedOutput_congr_short_restrict B U basis S hR hσ
    selected hsmall c hc
  exact (principalAxisRestrict_join_left (allocatedShortAxis U basis S.value) _ _).symm

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module
open scoped Classical NNReal
variable {m : ℕ} {X : Type*} [Fintype X]
variable {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (Lsize : ℕ)
local notation "short" => allocatedShortAxis (I := I) U b Lsize
local notation "Grid" => AllocatedShortIntegerAxis U b Lsize →
  ((Finset.univ : Finset (Finset Empty)) : Type) → ℤ

variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (R : Fin m → ℝ)
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E short)
local notation "Output" => (Σ _a : {a : LayerSamplerAxis I n // ¬short a}, Unit)

namespace NormalizedPolynomialTwist
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)

theorem forecastShortGridTest_bounds (q : ℕ) [NeZero q] (hm : 0 < m)
    (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
    (center : X → ℝ) (τ : ℝ) (grid : Grid) (out : Out → ZMod q) :
    (∀ y, ‖W.forecastShortGridTest U b Lsize hb o bW R q hm hperiod hcover center τ grid out y‖ ≤ 1) ∧
      LipschitzWith (Lip * max ‖τ / 8‖₊ (forecastNativeAmbientLip U b o R))
        (W.forecastShortGridTest U b Lsize hb o bW R q hm hperiod hcover center τ grid out) :=
  W.forecastResidueTest_bounds U b hb o bW R short q hm hperiod hcover _ _ center τ out

end NormalizedPolynomialTwist

section OriginalSample
variable {G : Type*} [Fintype G]
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U b S j)
  (allocatedLayerWidths B U b S j) (allocatedLayerIntegerPMFs B U b hR hσ S j) (sample j))
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable (v : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U b S))

namespace NormalizedPolynomialTwist
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)

end NormalizedPolynomialTwist
end OriginalSample
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module
open scoped Classical NNReal

variable {m : ℕ} {X : Type*} [Fintype X]
variable {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

namespace NormalizedPolynomialTwist

variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}

end NormalizedPolynomialTwist
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module
open scoped Classical NNReal

variable {m : ℕ} {X : Type*} [Fintype X]
variable {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (Lsize : ℕ)
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (R : Fin m → ℝ)

local notation "short" => allocatedShortAxis (I := I) U b Lsize
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E short)

namespace NormalizedPolynomialTwist
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)

end NormalizedPolynomialTwist
end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedAffineFixedPathRationalReference
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {L V Short Out : Type*} [Fintype L] [Fintype V]
  [Fintype Out] [DecidableEq Out]

local instance arbitraryStepForecastModulusNeZero (p e : L → ℕ) [∀ l, NeZero (p l)] :
    NeZero (∏ l, p l ^ e l) :=
  ⟨Finset.prod_ne_zero_iff.mpr (fun l _ => pow_ne_zero _ (NeZero.ne (p l)))⟩

theorem rationalInactivePolynomialForecast_arbitraryStepCRT_tsum_marginal
    {I Z : Type*} [Fintype I]
    (inactive : FiniteProbabilityWeights I) (gridPoint : I → Z)
    (p e : L → ℕ) [∀ l, NeZero (p l)] (step : ℕ)
    (hp : ∀ l, (p l).Prime) (hstep : step ≠ 0)
    (hcoprime : Pairwise (fun l k => (p l ^ e l).Coprime (p k ^ e k)))
    (cLong : V → ℤ)
    (poly : Out → MvPolynomial (V ⊕ Short) ℤ) (inactiveCoord : I → Short → ℤ)
    {q : ℕ} [NeZero q] (hdiv : q ∣ ∏ l, p l ^ e l)
    {gridVolume : ℝ} (hV : gridVolume ≠ 0) (test : Z → (Out → ZMod q) → ℂ) :
    (∑' z, 𝔼 b : Out → ZMod (∏ l, p l ^ e l),
      ((rationalInactiveForecast inactive
        (fun _ => crtPolynomialInputLaw p e (fun l => padicValNat (p l) step) hcoprime
          (fun l v => (cLong v : ZMod (p l ^ e l)))) gridPoint
        (fun i => integerLongPolynomialOutput poly (inactiveCoord i) (∏ l, p l ^ e l))
        (∏ l, p l ^ e l) gridVolume z b / gridVolume : ℝ) : ℂ) *
          test z (fun j => ZMod.castHom hdiv (ZMod q) (b j))) =
      inactive.complexMean (fun i =>
        (FiniteProbabilityWeights.uniform (V → ZMod q)).complexMean (fun r =>
          test (gridPoint i) (fun j => MvPolynomial.eval₂ (Int.castRingHom (ZMod q))
            (Sum.elim (fun v => (cLong v : ZMod q) + (step : ZMod q) * r v)
              (fun a => (inactiveCoord i a : ZMod q))) (poly j)))) := by
  rw [rationalInactiveForecast_divisor_tsum_test _ _ _ _ hdiv hV]
  apply congrArg inactive.complexMean
  funext i
  simp_rw [integerLongPolynomialOutput_reduce poly (inactiveCoord i) hdiv]
  exact crtPolynomialInputLaw_arbitrary_step_divisor_complexMean p e step hp hstep
    hcoprime cLong hdiv
    (fun r => test (gridPoint i) (fun j => MvPolynomial.eval₂ (Int.castRingHom (ZMod q))
      (Sum.elim r (fun a => (inactiveCoord i a : ZMod q))) (poly j)))

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (start : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ)
variable (hinside : ∀ j (t : Fin (H j)),
  0 ≤ start j + (step j : ℤ) * t.val ∧ start j + (step j : ℤ) * t.val < (allocatedPrincipalSides B U basis S) j)
variable (hH : ∀ j, 0 < H j)

variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)

variable {Ω Out : Type*} [Fintype Ω] [Fintype Out] [DecidableEq Out]
variable (active : (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)) → FiniteProbabilityWeights Ω) (Y : (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)) → Ω → Out → ℤ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G]
variable {I E : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "AI" => PrincipalTupleIndex (fun a : Active => B (Subtype.val a))
  (fun a : Active => degree (Subtype.val a))
local notation "sides" => allocatedPrincipalSides B U basis S

variable (base : X → ℤ) (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
variable (deck : ∀ j : Fin m,
  BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
variable (projection : ∀ j, AllocatedDegreeActiveAxis short j →
  BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)

theorem allocatedJointResidueOutput_join
    (base : X → ℤ) (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (deck : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis short j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (q : ℕ) (rG : G → ZMod q)
    (u : PrincipalAxisTuples (α := Empty) short sides) (ar : AI → ZMod q) :
    allocatedJointResidueOutput B U basis S base noise deck projection q rG
        (allocatedPrincipalResidueJoin B U basis S q u ar) =
      fun o => MvPolynomial.eval₂ (Int.castRingHom (ZMod q))
        (Sum.elim (Sum.elim rG ar)
          (fun k => (allocatedShortPrincipalRaw B U basis S u k : ZMod q)))
        (allocatedForecastPolynomial short base noise deck projection o) := by
  funext o
  have hlong : (fun j : AI => allocatedPrincipalResidueJoin B U basis S q u ar
      ⟨j.1.val, j.2⟩ none) = ar := by
    funext j
    simp only [allocatedPrincipalResidueJoin, principalAxisResidueJoin, j.1.property, dite_false]
  unfold allocatedJointResidueOutput
  rw [hlong]
  apply allocatedForecastPolynomial_eval₂_raw_congr
  intro j hj
  simp only [allocatedPrincipalResidueJoin, principalAxisResidueJoin,
    allocatedShortPrincipalRaw, hj, dite_true]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Fintype (E j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Long" => LayerSamplerLongVariables short G B
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E short)

variable (H parameterStep : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (start : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ)
variable (hinside : ∀ j (t : Fin (H j)),
  0 ≤ start j + (parameterStep j : ℤ) * t.val ∧
    start j + (parameterStep j : ℤ) * t.val < allocatedPrincipalSides B U basis S j)
variable (hH : ∀ j, 0 < H j)

variable {PrimeIndex : Type*} [Fintype PrimeIndex]
variable (primes exponent : PrimeIndex → ℕ) [∀ l, NeZero (primes l)]
local notation "N" => (∏ l, primes l ^ exponent l)
local instance affineFixedPathCRTModulusNeZero : NeZero N :=
  ⟨Finset.prod_ne_zero_iff.mpr (fun l _ => pow_ne_zero _ (NeZero.ne (primes l)))⟩

theorem allocatedAffineFixedPath_crtRationalForecast_reference
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))
    (hsmall : ∀ a, basisAxisScale (basis (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (xref : G → IntegerScalarCubeBox Empty S.value)
    (base : X → ℤ) (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (deck : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis short j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (commonStep : ℕ) (hstep : commonStep ≠ 0) (cLong : Long → ℤ)
    (hp : ∀ l, (primes l).Prime)
    (hcoprime : Pairwise (fun l k => (primes l ^ exponent l).Coprime (primes k ^ exponent k)))
    {q : ℕ} [NeZero q] (hq : q ∣ N)
    {gridVolume : ℝ} (hV : gridVolume ≠ 0)
    (test : (A → ((Finset.univ : Finset (Finset Empty)) : Type) → ℤ) →
      (Out → ZMod q) → ℂ) :
    let poly := allocatedForecastPolynomial short base noise deck projection
    let c := allocatedOriginalSampleInactiveCoefficients B selected sample
    (allocatedInactiveAffineIntervalLaw B U basis S H parameterStep start hinside hH).complexMean (fun u =>
      (FiniteProbabilityWeights.uniform (Long → ZMod q)).complexMean (fun r =>
        test (forecastInactiveShortGrid B U basis S selected c u)
          (fun o => MvPolynomial.eval₂ (Int.castRingHom (ZMod q))
            (Sum.elim (fun v => (cLong v : ZMod q) + (commonStep : ZMod q) * r v)
              (fun k => (allocatedShortPrincipalRaw B U basis S u k : ZMod q))) (poly o)))) =
      ∑' z, 𝔼 b : Out → ZMod N,
        ((rationalInactiveForecast (principalAffineIntervalLaw B (layerSamplerDegree I n) (allocatedPrincipalSides B U basis S)
      H parameterStep start hinside hH)
          (fun _ => crtPolynomialInputLaw primes exponent
            (fun l => padicValNat (primes l) commonStep) hcoprime
            (fun l v => (cLong v : ZMod (primes l ^ exponent l))))
          (forecastInactiveFixedOutput B U basis S selected c xref)
          (fun v => integerLongPolynomialOutput poly (fun k => (v k.1 k.2 : ℤ)) N)
          N gridVolume z b / gridVolume : ℝ) : ℂ) *
            test z (fun j => ZMod.castHom hq (ZMod q) (b j)) := by
  intro poly c
  symm
  rw [rationalInactivePolynomialForecast_arbitraryStepCRT_tsum_marginal (principalAffineIntervalLaw B (layerSamplerDegree I n) (allocatedPrincipalSides B U basis S)
      H parameterStep start hinside hH)
    (forecastInactiveFixedOutput B U basis S selected c xref)
    primes exponent commonStep hp hstep hcoprime cLong poly
    (fun v k => (v k.1 k.2 : ℤ)) hq hV test]
  change _ = ((principalAffineIntervalLaw B (layerSamplerDegree I n) (allocatedPrincipalSides B U basis S)
      H parameterStep start hinside hH).finitePushforward (principalAxisRestrict short)).complexMean _
  rw [FiniteProbabilityWeights.complexMean_finitePushforward]
  apply congrArg (principalAffineIntervalLaw B (layerSamplerDegree I n) (allocatedPrincipalSides B U basis S)
      H parameterStep start hinside hH).complexMean
  funext v
  rw [forecastInactiveFixedOutput_eq_shortGrid B U basis S hR hσ selected hsmall c
    (allocatedOriginalSampleInactiveCoefficients_supported B selected U basis hR hσ S sample hs)
    xref v]
  apply congrArg (FiniteProbabilityWeights.uniform (Long → ZMod q)).complexMean
  funext r
  congr 1
  funext o
  exact allocatedForecastPolynomial_short_raw B U basis S base noise deck projection q
    (fun k => (cLong k : ZMod q) + (commonStep : ZMod q) * r k) v o

end Erdos3.VectorPolynomial

end

end OAI

end


