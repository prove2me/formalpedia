-- Prove2me | Definitions.Def_OAIQ093D013
-- name    : OAIQ093D013
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T16:22:26.594186+00:00
-- url     : https://prove2.me/theorems/9cfaaa61-f27b-4fb3-b4f7-d43c76b92e25
-- title:
--   Definitions bundle OAIQ093D013 of the split of OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 5 declarations of OpenAI's Lean: 2 definitions and 3 inductive types or structures. The definitions and types are `OAI.PolycyclicRecognition.CartanWordModel.AffineNeighborRow.reindex`, `OAI.PolycyclicRecognition.CartanWordModel.BoxProbeChains`, `OAI.PolycyclicRecognition.CartanWordModel.BoxProbeChains.reparametrize`, `OAI.PolycyclicRecognition.CartanWordModel.LinkedProbeChains`, `OAI.PolycyclicRecognition.CartanWordModel.LinkedRootProbeFrames`.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: [`PolycyclicRecognition_Geometry_CartanBoxProbeChains`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanBoxProbeChains.lean), [`PolycyclicRecognition_Geometry_CartanLinkedProbeChains`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanLinkedProbeChains.lean), [`PolycyclicRecognition_Geometry_CartanNeighborRowProfile`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanNeighborRowProfile.lean), [`PolycyclicRecognition_Geometry_LinkedRootProbeFrames`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/LinkedRootProbeFrames.lean).
--
--   **Imports.** It imports the published bundle `Def_PolycyclicRecognition`; the bundle `OAIQ093D007` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ093D016`; the statements `OAI_PolycyclicRecognition_CartanWordModel_cartan_linked_chain_concentration`, `OAI.PolycyclicRecognition.CartanWordModel.exists_concentrated_profile_frames`, `OAI_PolycyclicRecognition_CartanWordModel_exists_linked_probe_paths_with_pivot`, `OAI_PolycyclicRecognition_CartanWordModel_exists_original_neighbor_root_frames`, `OAI_PolycyclicRecognition_CartanWordModel_nonempty_boxProbeChains`, `OAI.PolycyclicRecognition.CartanWordModel.original_neighbor_offset_nonpos` and `OAI.PolycyclicRecognition.CartanWordModel.select_linked_profiles_of_published_inputs`; the proofs of `OAI_PolycyclicRecognition_CartanWordModel_cartan_linked_chain_concentration`, `OAI.PolycyclicRecognition.CartanWordModel.exists_concentrated_profile_frames`, `OAI_PolycyclicRecognition_CartanWordModel_exists_linked_probe_paths_with_pivot`, `OAI_PolycyclicRecognition_CartanWordModel_exists_original_neighbor_root_frames`, `OAI_PolycyclicRecognition_CartanWordModel_nonempty_boxProbeChains`, `OAI.PolycyclicRecognition.CartanWordModel.original_neighbor_offset_nonpos` and `OAI.PolycyclicRecognition.CartanWordModel.select_linked_profiles_of_published_inputs`.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit 7ef5c0c

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D007

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanBoxProbeChains
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurable chains for actual group-valued probes -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Metric
open scoped Manifold

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H) [Nonempty (Fin M.letterCount)]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
/-- The data retained for each of the three probe templates. The common
length and constants are independent of the scale and the probe point. -/
structure BoxProbeChains
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Set W) (γ : M.Bases) (t : Fin M.letterCount → ℝ) (scale : ℕ → ℝ)
    {Y : ℕ → Type*} [∀ n, MeasurableSpace (Y n)]
    (probe : ∀ n, Y n → F.N.carrier) where
  length : ℕ
  amplitude : ℝ
  prefixRadius : ℝ
  amplitude_ge_one : 1 ≤ amplitude
  prefixRadius_nonneg : 0 ≤ prefixRadius
  mode : ℕ → Fin length → Fin M.letterCount
  coefficient : ∀ n, Y n → Fin length → ℝ
  vertex : ∀ n, Y n → Fin (length + 1) → cartanRootIdeal H
  coefficient_measurable : ∀ n j, Measurable (fun q => coefficient n q j)
  vertex_measurable : ∀ n j, Measurable (fun q => b₀.equivFun (vertex n q j))
  coefficient_bound : ∀ n q j, |coefficient n q j| ≤ amplitude * Real.exp (scale n *
    (M.supportIn T hunimod eW).weightSupport E (mode n j))
  vertex_zero : ∀ n q, vertex n q 0 = 0
  vertex_last : ∀ n q, F.ExpN (F.N.equiv (vertex n q (Fin.last length))) = probe n q
  vertex_bound : ∀ n q j,
    ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList γ)
      (fun k => bracketWordExponent t (γ.val k)) (scale n)).equivFun (vertex n q j)‖ ≤
      prefixRadius
  vertex_step : ∀ n q j, F.ExpN (F.N.equiv (vertex n q j.succ)) =
    F.ExpN (F.N.equiv (vertex n q j.castSucc)) *
      F.ExpN (F.N.equiv (coefficient n q j • M.letter (mode n j)))

set_option maxHeartbeats 1000000 in
omit [SimplyConnectedSpace G] [FiniteDimensional ℝ W] [Nonempty (Fin M.letterCount)] in
/-- Use the original quotient/kernel probability cell as the probe space.
Measurable reparametrization keeps every prefix, coefficient and endpoint,
so the independent probe law can be chosen directly on that cell. -/
def BoxProbeChains.reparametrize
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Set W) (γ : M.Bases) (t : Fin M.letterCount → ℝ) (scale : ℕ → ℝ)
    {Y Z : ℕ → Type*} [∀ n, MeasurableSpace (Y n)] [∀ n, MeasurableSpace (Z n)]
    (probe : ∀ n, Y n → F.N.carrier)
    (P : M.BoxProbeChains T F hunimod eW b₀ E γ t scale probe)
    (ψ : ∀ n, Z n → Y n) (hψ : ∀ n, Measurable (ψ n)) :
    M.BoxProbeChains T F hunimod eW b₀ E γ t scale (fun n z => probe n (ψ n z)) where
  length := P.length
  amplitude := P.amplitude
  prefixRadius := P.prefixRadius
  amplitude_ge_one := P.amplitude_ge_one
  prefixRadius_nonneg := P.prefixRadius_nonneg
  mode := P.mode
  coefficient := fun n z => P.coefficient n (ψ n z)
  vertex := fun n z => P.vertex n (ψ n z)
  coefficient_measurable := fun n j => (P.coefficient_measurable n j).comp (hψ n)
  vertex_measurable := fun n j => (P.vertex_measurable n j).comp (hψ n)
  coefficient_bound := fun n z => P.coefficient_bound n (ψ n z)
  vertex_zero := fun n z => P.vertex_zero n (ψ n z)
  vertex_last := fun n z => P.vertex_last n (ψ n z)
  vertex_bound := fun n z => P.vertex_bound n (ψ n z)
  vertex_step := fun n z => P.vertex_step n (ψ n z)

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanLinkedProbeChains
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Consecutive actual chains with one vanishing prefix bound -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Filter
open scoped Manifold Topology

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H) [Nonempty (Fin M.letterCount)]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
/-- All three logarithmic chains in the original neighboring-sheet coordinates.
The first starts at the allowed suffix, the second at its neighbor, and the third starts at the second's actual
last vertex. Their coefficients retain their original template bounds. -/
structure LinkedProbeChains
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Fin 3 → Set W) (γ : M.Bases) (t : Fin M.letterCount → ℝ) (scale : ℕ → ℝ)
    {Y : ℕ → Type*} [∀ n, MeasurableSpace (Y n)]
    (probe : Fin 3 → ∀ n, Y n → F.N.carrier)
    (P : ∀ k, M.BoxProbeChains T F hunimod eW b₀ (E k) γ t scale (probe k))
    (origin base : ∀ n, Y n → cartanRootIdeal H) (ε : ℕ → ℝ) where
  vertex : ∀ k n, Y n → Fin ((P k).length + 1) → cartanRootIdeal H
  measurable : ∀ k n j, Measurable (fun y => b₀.equivFun (vertex k n y j))
  first_start : ∀ n y, vertex 0 n y 0 = origin n y
  first_exp : ∀ n y j, F.ExpN (F.N.equiv (vertex 0 n y j)) =
    F.ExpN (F.N.equiv (origin n y)) * F.ExpN (F.N.equiv ((P 0).vertex n y j))
  second_start : ∀ n y, vertex 1 n y 0 = base n y
  third_start : ∀ n y, vertex 2 n y 0 = vertex 1 n y (Fin.last (P 1).length)
  second_exp : ∀ n y j, F.ExpN (F.N.equiv (vertex 1 n y j)) =
    F.ExpN (F.N.equiv (base n y)) * F.ExpN (F.N.equiv ((P 1).vertex n y j))
  third_exp : ∀ n y j, F.ExpN (F.N.equiv (vertex 2 n y j)) =
    F.ExpN (F.N.equiv (vertex 1 n y (Fin.last (P 1).length))) *
      F.ExpN (F.N.equiv ((P 2).vertex n y j))
  bound : ∀ k n y j,
    ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList γ)
      (fun i => bracketWordExponent t (γ.val i)) (scale n)).equivFun (vertex k n y j)‖ ≤
        Real.exp (scale n * ε n)
  step : ∀ k n y j, F.ExpN (F.N.equiv (vertex k n y j.succ)) =
    F.ExpN (F.N.equiv (vertex k n y j.castSucc)) *
      F.ExpN (F.N.equiv ((P k).coefficient n y j • M.letter ((P k).mode n j)))

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanNeighborRowProfile
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One actual profile map for both cells of an affine neighboring row -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Filter Set
open scoped Manifold Topology ENNReal NNReal

variable {EG G W I : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  [IsTopologicalGroup F.N.carrier]
  [SecondCountableTopology F.N.carrier]


variable [Fintype I] [DecidableEq I]


variable (π : G →* Multiplicative W)
  (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
  (cell : Set W) (βcell : M.Bases)
  (X : I → H) {d : ℕ} (βD : WordBasisSelections X (boundedBracketWords d))
  (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
  (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
  (hchartN : ∀ x, chartN x = F.ExpN x)
  (pivot : Fin M.letterCount → H) (shrink B δ : ℝ)
  (S : Set C((Fin (finrank ℝ H) → ℝ), W))
  [MeasurableSpace S] [BorelSpace S] [BorelSpace (S × S)]
  {Λ : ℝ≥0}
  (D : AffineNeighborRow T M F hunimod eW π b₀ cell βcell X βD
    haarN chartN hchartN pivot shrink B δ S (Λ := Λ))

set_option maxHeartbeats 1000000 in
/-- Restricting to a cofinal subsequence keeps the original neighboring
law, affine profiles and offsets. -/
def AffineNeighborRow.reindex (u : ℕ → ℕ) (hu : StrictMono u) :
    AffineNeighborRow T M F hunimod eW π b₀ cell βcell X βD
      haarN chartN hchartN pivot shrink B δ S (Λ := Λ) where
  scale := D.scale ∘ u
  grows := D.grows.comp hu.tendsto_atTop
  pair := D.pair ∘ u
  center := D.center ∘ u
  radius := D.radius ∘ u
  radius_nonneg := fun n => D.radius_nonneg (u n)
  radius_subexponential := fun ε hε => hu.tendsto_atTop.eventually (D.radius_subexponential ε hε)
  base := D.base ∘ u
  step := D.step ∘ u
  basis := D.basis ∘ u
  base_mem := fun n => D.base_mem (u n)
  step_mem := fun n => D.step_mem (u n)
  mode := D.mode
  time := D.time ∘ u
  time_bound := fun n => D.time_bound (u n)
  root_step := fun n => D.root_step (u n)
  profile := D.profile ∘ u
  measurable_profile := fun n => D.measurable_profile (u n)
  actual := fun n => D.actual (u n)
  law := D.law
  converges := D.converges.comp hu.tendsto_atTop
  point := D.point
  supported := D.supported
  label₁ := D.label₁
  label₂ := D.label₂
  offset₁ := D.offset₁
  offset₂ := D.offset₂
  affine₁ := D.affine₁
  affine₂ := D.affine₂

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_LinkedRootProbeFrames
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Linked root chains with their prescribed group endpoints -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Filter
open scoped Manifold Topology

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

/-- Retain the logarithmic chains together with the group equalities used
by the measured comparison. The sampling domain stays an abstract parameter
so that its coordinate construction is not repeated in every projection. -/
structure LinkedRootProbeFrames
    {Y : ℕ → Type*} [∀ n, MeasurableSpace (Y n)]
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Fin 3 → Set W) (γ : M.Bases) (width : Fin M.letterCount → ℝ)
    (scale : ℕ → ℝ) (probe : Fin 3 → ∀ n, Y n → F.N.carrier)
    (base step : ℕ → F.N.carrier)
    (first anchor second : ∀ n, Y n → F.N.carrier) where
  origin : ℕ → cartanRootIdeal H
  finish : ℕ → cartanRootIdeal H
  error : ℕ → ℝ
  error_nonneg : ∀ n, 0 ≤ error n
  error_tendsto : Tendsto error atTop (𝓝 0)
  chains : ∀ k, M.BoxProbeChains T F hunimod eW bN (E k) γ width scale (probe k)
  linked : M.LinkedProbeChains T F hunimod eW bN E γ width scale probe chains
    (fun n _ => origin n) (fun n _ => finish n) error
  origin_eq : ∀ n, F.ExpN (F.N.equiv (origin n)) = base n
  finish_eq : ∀ n, F.ExpN (F.N.equiv (finish n)) = base n * step n
  first_endpoint : ∀ n y,
    F.ExpN (F.N.equiv (linked.vertex 0 n y (Fin.last (chains 0).length))) = first n y
  anchor_endpoint : ∀ n y,
    F.ExpN (F.N.equiv (linked.vertex 1 n y (Fin.last (chains 1).length))) = anchor n y
  second_endpoint : ∀ n y,
    F.ExpN (F.N.equiv (linked.vertex 2 n y (Fin.last (chains 2).length))) = second n y

end PolycyclicRecognition.CartanWordModel

end

end OAI
end


