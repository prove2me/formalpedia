-- Prove2me | Definitions.Def_OAIW2HM000
-- name    : OAIW2HM000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-25T07:08:52.169103+00:00
-- url     : https://prove2.me/theorems/5fa1a4b0-153c-4d67-82d3-b8d7980faf74
-- title:
--   Definitions bundle OAIW2HM000 of the split of OpenAI, Spontaneous magnetization in the quantum Heisenberg ferromagnet
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Heisenberg.spontaneous_magnetization`, carved from OpenAI's openai/math development (OpenAI, *Spontaneous magnetization in the quantum Heisenberg ferromagnet*, OpenAI Math Release, September 24, 2026, result family 271, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 508 declarations of OpenAI's Lean: 352 definitions, 5 inductive types or structures, 15 instances and 136 theorems. The definitions and types are `OAI.GibbsStrip.evolve`, `OAI.GibbsStrip.instNormedAlgebraRat_solutions`, `OAI.GibbsStrip.instNormedAlgebraRat_solutions_1`, `OAI.Heisenberg.Bernoulli.doubleRates`, `OAI.Heisenberg.Bernoulli.fresh`, `OAI.Heisenberg.Bernoulli.join`, `OAI.Heisenberg.Bernoulli.original`, `OAI.Heisenberg.Bernoulli.test`, `OAI.Heisenberg.Bernoulli.weight`, `OAI.Heisenberg.Bootstrap.retDecEq`, `OAI.Heisenberg.Clocks.Follows`, `OAI.Heisenberg.Clocks.WeakTimes`, `OAI.Heisenberg.Clocks.edgeWords`, `OAI.Heisenberg.Clocks.functionWords`, `OAI.Heisenberg.Clocks.mixedCoins`, `OAI.Heisenberg.Clocks.mixedSource`, `OAI.Heisenberg.Clocks.moveList`, `OAI.Heisenberg.Clocks.shifted`, `OAI.Heisenberg.Clocks.timeSet`, `OAI.Heisenberg.Clocks.weakTimes`, `OAI.Heisenberg.Clocks.witnessMarks`, `OAI.Heisenberg.Clocks.witnesses`, `OAI.Heisenberg.Conditioning.conditional`, `OAI.Heisenberg.Conditioning.mass`, `OAI.Heisenberg.Cycle.Classes`, `OAI.Heisenberg.Cycle.MissingClasses`, `OAI.Heisenberg.Cycle.MissingSet`, `OAI.Heisenberg.Cycle.OutsideHit`, `OAI.Heisenberg.Cycle.classInclusion`, `OAI.Heisenberg.Cycle.classOf`, `OAI.Heisenberg.Cycle.colorEquiv`, `OAI.Heisenberg.Cycle.colorSpace`, `OAI.Heisenberg.Cycle.missingCount`, `OAI.Heisenberg.Cycle.missingInclusion`, `OAI.Heisenberg.Cycle.missingOption`, `OAI.Heisenberg.Cycle.projection`, `OAI.Heisenberg.ExchangeMatrix.Clock`, `OAI.Heisenberg.ExchangeMatrix.bernoulliStep`, `OAI.Heisenberg.ExchangeMatrix.clockGenerator`, `OAI.Heisenberg.ExchangeMatrix.linearMesh` and 317 more.
--
--   **Sources.** They come from these modules of lean/OAI/MathematicalPhysics, in whole or in part: `Heisenberg_BoundaryWitness`, `Heisenberg_BoundedStrip`, `Heisenberg_ClockInsertions`, `Heisenberg_ClockWitnesses`, `Heisenberg_ColorClockLimit`, `Heisenberg_ConditionalMoments`, `Heisenberg_CubeSurface`, `Heisenberg_CutColors`, `Heisenberg_CutContractions`, `Heisenberg_CycleWeights`, `Heisenberg_CyclicEnergy`, `Heisenberg_DeterminantExposure`, `Heisenberg_ExchangeCycles`, `Heisenberg_ExchangeDeterminants`, `Heisenberg_ExchangeOnMesh`, `Heisenberg_ExponentialEvolution`, `Heisenberg_ExposedEnergy`, `Heisenberg_FiniteHistories`, `Heisenberg_FiniteTilt`, `Heisenberg_FirstReturns`, `Heisenberg_FlowCongestion`, `Heisenberg_FlowRouting`, `Heisenberg_HistoryMarginals`, `Heisenberg_HittingEnergy`, `Heisenberg_HittingKernels`, `Heisenberg_HoleReturns`, `Heisenberg_HullComponents`, `Heisenberg_HullRouting`, `Heisenberg_KilledContractions`, `Heisenberg_LatticeCuts`, `Heisenberg_LatticeFlows`, `Heisenberg_LatticeHulls`, `Heisenberg_LatticePaths`, `Heisenberg_LayerEnergy`, `Heisenberg_LayerExposure`, `Heisenberg_LayerRegularity`, `Heisenberg_LocalAlgebra`, `Heisenberg_LocalDynamics`, `Heisenberg_MatrixUnitLift`, `Heisenberg_MeshCompletion`, `Heisenberg_MeshMatrixSurface`, `Heisenberg_MeshProduct`, `Heisenberg_Model`, `Heisenberg_NetworkEnergy`, `Heisenberg_PeriodicLeakage`, `Heisenberg_PeriodicReturnEstimate`, `Heisenberg_PermutationSymbols`, `Heisenberg_PhysicalClock`, `Heisenberg_PinBridge`, `Heisenberg_PinDensity`, `Heisenberg_PinSplicing`, `Heisenberg_PinSymmetrization`, `Heisenberg_PinnedColors`, `Heisenberg_PinnedMagnetization`, `Heisenberg_PolynomialLimits`, `Heisenberg_QuietSweeps`, `Heisenberg_RegularComponents`, `Heisenberg_RegularKernels`, `Heisenberg_ReturnConditioning`, `Heisenberg_RoundEnergy`, `Heisenberg_RoutedDissipation`, `Heisenberg_RoutedNetworks`, `Heisenberg_ScheduledResiduals`, `Heisenberg_SimultaneousPins`, `Heisenberg_SlotColorTrace`, `Heisenberg_SlotOnMesh`, `Heisenberg_SparseCrossings`, `Heisenberg_SpatialClocks`, `Heisenberg_SpectralTransfer`, `Heisenberg_SpinAverage`, `Heisenberg_SpinAverageBoundary`, `Heisenberg_SpinCubeAverage`, `Heisenberg_SpinField`, `Heisenberg_SpinFieldDynamics`, `Heisenberg_SpinTensorRepresentation`, `Heisenberg_StablePinLaw`, `Heisenberg_StablePolynomials`, `Heisenberg_StableSections`, `Heisenberg_StateCompactness`, `Heisenberg_SurfaceTail`, `Heisenberg_SymmetrizedSurface`, `Heisenberg_TensorLift`, `Heisenberg_TensorLiftIndex`, `Heisenberg_TensorUnitSystem`, `Heisenberg_TwoEndedReturns`, `Heisenberg_WeightedLeakage`.
--
--   **Imports.** It imports the published bundle `Def_Heisenberg`.
--
--   **Imported by** (directly, in this split): the bundle `OAIW2HM002`; the statements `OAI.Heisenberg.Bootstrap.periodic_return_estimate`, `OAI.Heisenberg.Flow.indexed_prefix_leakage`, `OAI.Heisenberg.Surface.mesh_matrix_surface`, `OAI.Heisenberg.cubeBoundary_error`, `OAI.Heisenberg.cubeBoundary_lower`, `OAI.Heisenberg.cubeBoundary_upper`, `OAI.Heisenberg.field_local_small`, `OAI.Heisenberg.finiteRepresentation_field` and `OAI.Heisenberg.state_limit_locallyUniform`; the proofs of `OAI.Heisenberg.Bootstrap.periodic_return_estimate`, `OAI.Heisenberg.Flow.indexed_prefix_leakage`, `OAI.Heisenberg.Surface.mesh_matrix_surface` and `OAI.Heisenberg.finiteRepresentation_field`.
-- source:
--   OpenAI, Spontaneous magnetization in the quantum Heisenberg ferromagnet, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 271; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Spontaneous-magnetization-in-the-quantum-Heisenberg-ferromagnet-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/MathematicalPhysics at commit adc7f12

import Mathlib
import Definitions.Def_Heisenberg

section
-- module Solutions.OAIW2_Heis.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_Model
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v


noncomputable section
open scoped ComplexConjugate ENNReal Classical

namespace Heisenberg

@[simp] theorem l2Reindex_apply {ι : Type u} {κ : Type v} (e : ι ≃ κ) (f : L2 ι) (j : κ) :
    l2Reindex e f j = f (e.symm j) := rfl

@[simp] theorem l2Projection_apply {ι : Type u} (p : ι → Prop) (v : L2 ι) (i : ι) :
    l2Projection p v i = if p i then v i else 0 := by classical rfl

@[simp] theorem matrixUnit_apply (d ℓ : ℕ) (x : Site d) (a b : Level ℓ)
    (v : SpinHilbert d ℓ) (c : Configuration d ℓ) :
    matrixUnit d ℓ x a b v c = if c x = a then v (c.update x b) else 0 := by
  simp only [matrixUnit, ContinuousLinearMap.comp_apply, l2Projection_apply]
  split_ifs with h
  · change v (c.update x ((Equiv.swap a b).symm (c x))) = v (c.update x b)
    simp [h]
  · rfl

@[simp] theorem l2Reindex_symm_apply {ι : Type u} {κ : Type v} (e : ι ≃ κ) (v : L2 κ) (i : ι) :
    (l2Reindex e).symm v i = v (e i) := rfl

@[simp] theorem relabel_matrixUnit (d ℓ : ℕ) (e : Equiv.Perm (Site d))
    (x : Site d) (a b : Level ℓ) :
    operatorRelabel d ℓ e (matrixUnit d ℓ x a b) = matrixUnit d ℓ (e x) a b := by
  ext v c
  simp only [operatorRelabel, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    l2Reindex_apply, matrixUnit_apply]
  change (if c (e x) = a then
    (l2Reindex (Finsupp.equivCongrLeft e)).symm v
      (((Finsupp.equivCongrLeft e).symm c).update x b) else 0) = _
  rw [l2Reindex_symm_apply]
  by_cases h : c (e x) = a
  · simp only [h, ite_eq_left]
    apply congrArg v
    ext y
    simp only [Finsupp.equivCongrLeft_apply, Finsupp.equivMapDomain_apply,
      Finsupp.update_apply]
    by_cases hy : y = e x
    · subst y; simp
    · have hy' : e.symm y ≠ x := fun hxy => hy (by simpa using congrArg e hxy)
      simp [hy, hy']
  · simp only [h, ite_false]

end Heisenberg
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_LocalAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate ENNReal Classical

open scoped ComplexConjugate BigOperators
namespace Heisenberg

instance quasiLocalNormedRing (d ℓ : ℕ) : NormedRing (QuasiLocal d ℓ) :=
  SubringClass.toNormedRing (quasiLocalAlgebra d ℓ)

instance quasiLocalStarRing (d ℓ : ℕ) : StarRing (QuasiLocal d ℓ) :=
  (quasiLocalAlgebra d ℓ).starRing

instance quasiLocalNormedAlgebra (d ℓ : ℕ) : NormedAlgebra ℂ (QuasiLocal d ℓ) :=
  SubalgebraClass.toNormedAlgebra (quasiLocalAlgebra d ℓ)

instance quasiLocalAddCommGroup (d ℓ : ℕ) : AddCommGroup (QuasiLocal d ℓ) :=
  (SubringClass.toRing (quasiLocalAlgebra d ℓ)).toAddCommGroup

instance quasiLocalAddCommMonoid (d ℓ : ℕ) : AddCommMonoid (QuasiLocal d ℓ) :=
  (quasiLocalAddCommGroup d ℓ).toAddCommMonoid

instance quasiLocalAddMonoid (d ℓ : ℕ) : AddMonoid (QuasiLocal d ℓ) :=
  (quasiLocalAddCommMonoid d ℓ).toAddMonoid

instance quasiLocalAddZeroClass (d ℓ : ℕ) : AddZeroClass (QuasiLocal d ℓ) :=
  (quasiLocalAddMonoid d ℓ).toAddZeroClass

instance quasiLocalAddCommMagma (d ℓ : ℕ) : AddCommMagma (QuasiLocal d ℓ) :=
  (quasiLocalAddCommMonoid d ℓ).toAddCommMagma

instance quasiLocalModule (d ℓ : ℕ) : Module ℂ (QuasiLocal d ℓ) :=
  (SubalgebraClass.toNormedAlgebra (quasiLocalAlgebra d ℓ)).toNormedSpace.toModule

@[simp] theorem matrixUnit_mul_same (d ℓ : ℕ) (x : Site d) (a b c e : Level ℓ) :
    matrixUnit d ℓ x a b * matrixUnit d ℓ x c e =
      if b = c then matrixUnit d ℓ x a e else 0 := by
  classical
  ext v z
  change (matrixUnit d ℓ x a b) ((matrixUnit d ℓ x c e) v) z = _
  by_cases hbc : b = c
  · subst c
    simp only [matrixUnit_apply, Finsupp.update_apply, ite_true]
    by_cases hza : z x = a <;> simp [hza]
  · simp only [matrixUnit_apply, Finsupp.update_apply, hbc, ite_false]
    by_cases hza : z x = a <;> simp [hza, hbc]

@[simp] theorem matrixUnit_diagonal_sum (d ℓ : ℕ) (x : Site d) :
    ∑ a : Level ℓ, matrixUnit d ℓ x a a = 1 := by
  classical
  ext v z
  simp only [sum_apply, lp.coeFn_sum, Finset.sum_apply,
    matrixUnit_apply, one_apply_eq_self]
  rw [Finset.sum_ite_eq]
  simp [Finsupp.update_self]

theorem matrixUnits_commute {d ℓ : ℕ} {x y : Site d} (hxy : x ≠ y)
    (a b c e : Level ℓ) :
    Commute (matrixUnit d ℓ x a b) (matrixUnit d ℓ y c e) := by
  classical
  change _ * _ = _ * _
  ext v z
  change matrixUnit d ℓ x a b (matrixUnit d ℓ y c e v) z =
    matrixUnit d ℓ y c e (matrixUnit d ℓ x a b v) z
  simp only [matrixUnit_apply]
  by_cases hx : z x = a <;> by_cases hy : z y = c <;>
    simp [hx, hy, Finsupp.update_apply, hxy, Ne.symm hxy, Finsupp.update_comm z hxy]

@[simp] theorem localUnit_mul_same (d ℓ : ℕ) (x : Site d) (a b c e : Level ℓ) :
    localUnit d ℓ x a b * localUnit d ℓ x c e =
      if b = c then localUnit d ℓ x a e else 0 := by
  classical
  apply Subtype.ext
  change matrixUnit d ℓ x a b * matrixUnit d ℓ x c e = _
  rw [matrixUnit_mul_same]
  split_ifs <;> rfl

@[simp] theorem localUnit_diagonal_sum (d ℓ : ℕ) (x : Site d) :
    ∑ a : Level ℓ, localUnit d ℓ x a a = 1 := by
  apply Subtype.ext
  change (quasiLocalAlgebra d ℓ).subtype (∑ a : Level ℓ, localUnit d ℓ x a a) =
    (quasiLocalAlgebra d ℓ).subtype 1
  rw [map_sum, map_one]
  exact matrixUnit_diagonal_sum d ℓ x

theorem localUnits_commute {d ℓ : ℕ} {x y : Site d} (hxy : x ≠ y)
    (a b c e : Level ℓ) :
    Commute (localUnit d ℓ x a b) (localUnit d ℓ y c e) := by
  change _ * _ = _ * _
  apply Subtype.ext
  exact (matrixUnits_commute hxy a b c e).eq

@[simp] theorem star_l2Projection {ι : Type*} (p : ι → Prop) :
    star (l2Projection p) = l2Projection p := by
  classical
  rw [ContinuousLinearMap.star_eq_adjoint, eq_comm,
    ContinuousLinearMap.eq_adjoint_iff]
  intro v w
  simp only [lp.inner_eq_tsum, l2Projection_apply]
  apply tsum_congr
  intro i
  by_cases h : p i <;> simp [h]

@[simp] theorem star_l2Reindex {ι : Type*} (e : Equiv.Perm ι) :
    star ((l2Reindex e).toContinuousLinearEquiv.toContinuousLinearMap) =
      (l2Reindex e.symm).toContinuousLinearEquiv.toContinuousLinearMap := by
  rw [ContinuousLinearMap.star_eq_adjoint, eq_comm,
    ContinuousLinearMap.eq_adjoint_iff]
  intro v w
  have h := (l2Reindex e).inner_map_map (l2Reindex e.symm v) w
  have he : l2Reindex e (l2Reindex e.symm v) = v := by
    ext i
    simp
  rw [he] at h
  exact h.symm

@[simp] theorem configPerm_swap_symm (d ℓ : ℕ) (x : Site d) (a b : Level ℓ) :
    (configPerm d ℓ x (Equiv.swap a b)).symm = configPerm d ℓ x (Equiv.swap a b) := by
  classical
  ext c
  simp [configPerm, Equiv.symm_swap]

@[simp] theorem star_matrixUnit (d ℓ : ℕ) (x : Site d) (a b : Level ℓ) :
    star (matrixUnit d ℓ x a b) = matrixUnit d ℓ x b a := by
  classical
  change star (l2Projection (fun c : Configuration d ℓ => c x = a) *
    (l2Reindex (configPerm d ℓ x (Equiv.swap a b))).toContinuousLinearEquiv.toContinuousLinearMap) = _
  rw [star_mul, star_l2Projection, star_l2Reindex, configPerm_swap_symm]
  ext v z
  change l2Reindex (configPerm d ℓ x (Equiv.swap a b))
    (l2Projection (fun c : Configuration d ℓ => c x = a) v) z = _
  simp only [l2Reindex_apply, l2Projection_apply, matrixUnit_apply]
  change (if ((z.update x ((Equiv.swap a b).symm (z x))) x) = a then
      v (z.update x ((Equiv.swap a b).symm (z x))) else 0) =
    if z x = b then v (z.update x a) else 0
  simp only [Finsupp.update_apply, ite_true, Equiv.symm_swap]
  by_cases h : z x = b
  · simp [h]
  · have hn : Equiv.swap a b (z x) ≠ a := by
      intro he
      have := congrArg (Equiv.swap a b) he
      simp at this
      exact h this
    simp only [h, hn, ite_false]

@[simp] theorem star_localUnit (d ℓ : ℕ) (x : Site d) (a b : Level ℓ) :
    star (localUnit d ℓ x a b) = localUnit d ℓ x b a := by
  apply Subtype.ext
  exact star_matrixUnit d ℓ x a b

@[simp] theorem star_spinZ (d ℓ : ℕ) (x : Site d) :
    star (spinZ d ℓ x) = spinZ d ℓ x := by
  simp [spinZ, star_sum, star_smul]

@[simp] theorem star_spinX (d ℓ : ℕ) (x : Site d) :
    star (spinX d ℓ x) = spinX d ℓ x := by
  simp [spinX, spinMinus, star_smul, add_comm]

@[simp] theorem star_spinY (d ℓ : ℕ) (x : Site d) :
    star (spinY d ℓ x) = spinY d ℓ x := by
  simp only [spinY, spinMinus, star_smul, star_sub, star_star]
  rw [← neg_sub (spinPlus d ℓ x) (star (spinPlus d ℓ x)), smul_neg, ← neg_smul]
  congr 1
  simp

@[simp] theorem spinZ_mul_localUnit (d ℓ : ℕ) (x : Site d) (a b : Level ℓ) :
    spinZ d ℓ x * localUnit d ℓ x a b =
      (magneticLevel ℓ a : ℂ) • localUnit d ℓ x a b := by
  classical
  simp only [spinZ, Finset.sum_mul, smul_mul_assoc, localUnit_mul_same]
  simp [smul_ite]

@[simp] theorem localUnit_mul_spinZ (d ℓ : ℕ) (x : Site d) (a b : Level ℓ) :
    localUnit d ℓ x a b * spinZ d ℓ x =
      (magneticLevel ℓ b : ℂ) • localUnit d ℓ x a b := by
  classical
  simp only [spinZ, Finset.mul_sum, mul_smul_comm, localUnit_mul_same]
  simp [smul_ite]

def localAlgebra (d ℓ : ℕ) (F : Set (Site d)) : StarSubalgebra ℂ (QuasiLocal d ℓ) :=
  StarAlgebra.adjoin ℂ {A | ∃ x ∈ F, ∃ a b, A = localUnit d ℓ x a b}

@[simp] theorem finiteDynamics_zero (d ℓ : ℕ) (Λ : Finset (Site d)) (A : QuasiLocal d ℓ) :
    finiteDynamics d ℓ Λ 0 A = A := by
  simp [finiteDynamics]

@[simp] lemma translation_localUnit (d ℓ : ℕ) (x y : Site d) (a b : Level ℓ) :
    translation d ℓ x (localUnit d ℓ y a b) = localUnit d ℓ (x+y) a b := by
  apply Subtype.ext
  exact relabel_matrixUnit d ℓ (Equiv.addLeft x) y a b

lemma norm_translation (d ℓ : ℕ) (x : Site d) (A : QuasiLocal d ℓ) :
    ‖translation d ℓ x A‖ = ‖A‖ :=
  (StarAlgEquiv.isometry (operatorRelabel d ℓ (Equiv.addLeft x))).norm_map_of_map_zero
    (map_zero _) _

@[simp] lemma translation_spinZ (d ℓ : ℕ) (x y : Site d) :
    translation d ℓ x (spinZ d ℓ y) = spinZ d ℓ (x+y) := by
  simp only [spinZ, map_sum, map_smul, translation_localUnit]
@[simp] lemma translation_spinPlus (d ℓ : ℕ) (x y : Site d) :
    translation d ℓ x (spinPlus d ℓ y) = spinPlus d ℓ (x+y) := by
  simp only [spinPlus, map_sum, map_smul, translation_localUnit]
@[simp] lemma translation_spinMinus (d ℓ : ℕ) (x y : Site d) :
    translation d ℓ x (spinMinus d ℓ y) = spinMinus d ℓ (x+y) := by
  simp only [spinMinus, map_star, translation_spinPlus]
@[simp] lemma translation_spinX (d ℓ : ℕ) (x y : Site d) :
    translation d ℓ x (spinX d ℓ y) = spinX d ℓ (x+y) := by simp [spinX]
@[simp] lemma translation_spinY (d ℓ : ℕ) (x y : Site d) :
    translation d ℓ x (spinY d ℓ y) = spinY d ℓ (x+y) := by simp [spinY]

def bond (d ℓ : ℕ) (x y : Site d) : QuasiLocal d ℓ :=
  spinX d ℓ x * spinX d ℓ y + spinY d ℓ x * spinY d ℓ y + spinZ d ℓ x * spinZ d ℓ y

def bondBound (d ℓ : ℕ) : ℝ :=
  ‖spinX d ℓ 0‖^2 + ‖spinY d ℓ 0‖^2 + ‖spinZ d ℓ 0‖^2

end Heisenberg
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_ExponentialEvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate ENNReal Classical
open scoped ComplexConjugate BigOperators

namespace SpinEvolution

section
variable {E : Type*} [NormedRing E] [NormedAlgebra ℂ E]

def leftRegular : E →ₐ[ℂ] (E →L[ℂ] E) where
  toFun := ContinuousLinearMap.mul ℂ E
  map_zero' := by ext A; simp
  map_one' := by ext A; simp
  map_add' H K := by ext A; simp
  map_mul' H K := by ext A; simp [mul_assoc]
  commutes' z := by ext A; simp [Algebra.algebraMap_eq_smul_one]

@[simp] lemma leftRegular_apply (H A : E) : leftRegular H A = H*A := rfl

def rightRegular : Eᵐᵒᵖ →ₐ[ℂ] (E →L[ℂ] E) where
  toFun H := (ContinuousLinearMap.mul ℂ E).flip H.unop
  map_zero' := by ext A; simp
  map_one' := by ext A; simp
  map_add' H K := by ext A; simp
  map_mul' H K := by ext A; simp [mul_assoc]
  commutes' z := by ext A; simp [Algebra.algebraMap_eq_smul_one]

@[simp] lemma rightRegular_apply (H : Eᵐᵒᵖ) (A : E) : rightRegular H A = A*H.unop := rfl

variable [CompleteSpace E]

def generator (H : E) : E →L[ℂ] E :=
  leftRegular (Complex.I • H) + rightRegular (MulOpposite.op ((-Complex.I) • H))

omit [CompleteSpace E] in
@[simp] lemma generator_apply (H A : E) : generator H A = Complex.I • (H*A-A*H) := by
  simp [generator, sub_eq_add_neg]

end

end SpinEvolution

namespace Heisenberg
def neighbors {d : ℕ} (x : Site d) : Finset (Site d) :=
  Finset.univ.biUnion fun i =>
    {Function.update x i (x i + 1), Function.update x i (x i - 1)}

end Heisenberg
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_LocalDynamics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate ENNReal Classical
open scoped ComplexConjugate BigOperators

namespace Heisenberg

def finiteGenerator (d ℓ : ℕ) (Λ : Finset (Site d)) : QuasiLocal d ℓ →L[ℂ] QuasiLocal d ℓ :=
  SpinEvolution.generator (hamiltonian d ℓ Λ)

def commutatorTerm (d ℓ : ℕ) (e : Site d × Site d) (A : QuasiLocal d ℓ) : QuasiLocal d ℓ :=
  (-Complex.I) • (bond d ℓ e.1 e.2 * A - A * bond d ℓ e.1 e.2)

def activeEdges {d : ℕ} (Λ F : Finset (Site d)) : Finset (Site d × Site d) :=
  (volumeEdges Λ).filter fun e => e.1 ∈ F ∨ e.2 ∈ F

def SupportedOnAtMost (d ℓ k : ℕ) (A : QuasiLocal d ℓ) : Prop :=
  ∃ F : Finset (Site d), F.card ≤ k+1 ∧ A ∈ localAlgebra d ℓ (F : Set (Site d))

end Heisenberg

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_StateCompactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate ENNReal Classical
open scoped ComplexConjugate BigOperators
open Filter Topology Metric
open scoped NNReal
open scoped NNReal

namespace Heisenberg
instance quasiLocalClosed (d ℓ : ℕ) : IsClosed (quasiLocalAlgebra d ℓ : Set (SpinOperator d ℓ)) :=
  StarSubalgebra.isClosed_topologicalClosure _

open scoped ComplexOrder

open scoped InnerProductSpace

def operatorInclusion (d ℓ : ℕ) : QuasiLocal d ℓ →L[ℂ] SpinOperator d ℓ :=
  (quasiLocalAlgebra d ℓ).toSubalgebra.toSubmodule.subtypeL

def vectorFunctional {d ℓ : ℕ} (v : SpinHilbert d ℓ) : QuasiLocal d ℓ →L[ℂ] ℂ :=
  (innerSL ℂ v).comp ((ContinuousLinearMap.apply ℂ (SpinHilbert d ℓ) v).comp
    (operatorInclusion d ℓ))

@[simp] theorem vectorFunctional_apply {d ℓ : ℕ} (v : SpinHilbert d ℓ)
    (A : QuasiLocal d ℓ) : vectorFunctional v A = ⟪v, (A : SpinOperator d ℓ) v⟫_ℂ := rfl

def vectorState {d ℓ : ℕ} (v : SpinHilbert d ℓ) (hv : ‖v‖ = 1) : State d ℓ where
  functional := vectorFunctional v
  normalized := by
    change ⟪v, v⟫_ℂ = 1
    rw [inner_self_eq_norm_sq_to_K, hv]
    norm_num
  positive A := by
    have h : vectorFunctional v (star A * A) =
        ⟪(A : SpinOperator d ℓ) v, (A : SpinOperator d ℓ) v⟫_ℂ := by
      change ⟪v, (star (A : SpinOperator d ℓ)) ((A : SpinOperator d ℓ) v)⟫_ℂ = _
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
    rw [h]
    exact ⟨inner_self_im (𝕜 := ℂ) _, inner_self_nonneg (𝕜 := ℂ)⟩

def configVector {d ℓ : ℕ} (c : Configuration d ℓ) : SpinHilbert d ℓ :=
  lp.single 2 c 1

@[simp] theorem norm_configVector {d ℓ : ℕ} (c : Configuration d ℓ) :
    ‖configVector c‖ = 1 := by
  simp [configVector, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]

@[simp] theorem vectorFunctional_configVector {d ℓ : ℕ} (c : Configuration d ℓ)
    (A : QuasiLocal d ℓ) : vectorFunctional (configVector c) A =
      (A : SpinOperator d ℓ) (configVector c) c := by
  simp [vectorFunctional_apply, configVector, lp.inner_single_left]

abbrev FiniteConfiguration {d : ℕ} (ℓ : ℕ) (F : Finset (Site d)) := F → Level ℓ

def extendConfig {d ℓ : ℕ} (F : Finset (Site d)) (c : FiniteConfiguration ℓ F) :
    Configuration d ℓ :=
  Finsupp.onFinset F (fun x => if hx : x ∈ F then c ⟨x,hx⟩ else 0)
    (by intro x; contrapose!; simp_all)

@[simp] theorem extendConfig_apply {d ℓ : ℕ} (F : Finset (Site d))
    (c : FiniteConfiguration ℓ F) (x : Site d) :
    extendConfig F c x = if hx : x ∈ F then c ⟨x,hx⟩ else 0 := by
  rfl

def finiteTraceFunctional (d ℓ : ℕ) (F : Finset (Site d)) : QuasiLocal d ℓ →L[ℂ] ℂ :=
  (Fintype.card (FiniteConfiguration ℓ F) : ℂ)⁻¹ •
    ∑ c : FiniteConfiguration ℓ F, vectorFunctional (configVector (extendConfig F c))

@[simp] theorem finiteTraceFunctional_apply (d ℓ : ℕ) (F : Finset (Site d))
    (A : QuasiLocal d ℓ) : finiteTraceFunctional d ℓ F A =
    (Fintype.card (FiniteConfiguration ℓ F) : ℂ)⁻¹ *
      ∑ c : FiniteConfiguration ℓ F, (A : SpinOperator d ℓ)
        (configVector (extendConfig F c)) (extendConfig F c) := by
  simp only [finiteTraceFunctional, smul_apply, sum_apply, smul_eq_mul,
    vectorFunctional_configVector]

def finiteTraceState (d ℓ : ℕ) (F : Finset (Site d)) : State d ℓ where
  functional := finiteTraceFunctional d ℓ F
  normalized := by
    have hcard : (Fintype.card (FiniteConfiguration ℓ F) : ℂ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    have h (c : FiniteConfiguration ℓ F) :
        vectorFunctional (configVector (extendConfig F c)) 1 = 1 :=
      (vectorState _ (norm_configVector _)).normalized
    simp only [finiteTraceFunctional, smul_apply, sum_apply, h, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mul_one, smul_eq_mul]
    exact inv_mul_cancel₀ hcard
  positive A := by
    have h (c : FiniteConfiguration ℓ F) :=
      (vectorState (configVector (extendConfig F c)) (norm_configVector _)).positive A
    change ((finiteTraceFunctional d ℓ F) (star A * A)).im = 0 ∧
      0 ≤ ((finiteTraceFunctional d ℓ F) (star A * A)).re
    simp only [finiteTraceFunctional, smul_apply,
      sum_apply, smul_eq_mul]
    simp only [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      Complex.mul_re, sub_zero]
    rw [Complex.im_sum, Complex.re_sum]
    constructor
    · convert mul_zero ((Fintype.card (FiniteConfiguration ℓ F) : ℝ)⁻¹) using 1
      congr 1
      apply Finset.sum_eq_zero
      intro c _
      exact (h c).1
    · exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
        (Finset.sum_nonneg fun c _ => (h c).2)

@[simp] theorem configVector_apply {d ℓ : ℕ} (c z : Configuration d ℓ) :
    configVector c z = if z = c then 1 else 0 := by
  simp only [configVector, lp.single_apply, Pi.single_apply, eq_comm]

@[simp] theorem matrixUnit_configVector {d ℓ : ℕ} (x : Site d) (a b : Level ℓ)
    (c : Configuration d ℓ) : matrixUnit d ℓ x a b (configVector c) =
      if c x = b then configVector (c.update x a) else 0 := by
  ext z
  simp only [matrixUnit_apply, configVector_apply]
  by_cases hc : c x = b
  · simp only [hc, ite_true, configVector_apply]
    by_cases hz : z x = a
    · simp only [hz, ite_true]
      have hh : z.update x b = c ↔ z = c.update x a := by
        constructor
        · intro he
          have hh := congrArg (fun q : Configuration d ℓ => q.update x a) he
          simpa only [Finsupp.update_idem, ← hz, Finsupp.update_self] using hh
        · rintro rfl
          simp [← hc]
      simp only [hh]
    · have hne : z ≠ c.update x a := by
        intro he
        have hh := congrArg (fun q : Configuration d ℓ => q x) he
        simp only [Finsupp.update_apply, ite_true] at hh
        exact hz hh
      simp [hz, hne]
  · simp only [hc, ite_false, lp.coeFn_zero, Pi.zero_apply]
    have hne : z.update x b ≠ c := by
      intro he
      have hh := congrArg (fun q : Configuration d ℓ => q x) he
      simp only [Finsupp.update_apply, ite_true] at hh
      exact hc hh.symm
    simp [hne]

def finiteConfigPerm {d ℓ : ℕ} {F : Finset (Site d)} (x : F)
    (σ : Equiv.Perm (Level ℓ)) : Equiv.Perm (FiniteConfiguration ℓ F) where
  toFun c := Function.update c x (σ (c x))
  invFun c := Function.update c x (σ.symm (c x))
  left_inv c := by ext y; by_cases h : y = x <;> simp [h]
  right_inv c := by ext y; by_cases h : y = x <;> simp [h]

@[simp] theorem extendConfig_perm {d ℓ : ℕ} {F : Finset (Site d)} (x : F)
    (σ : Equiv.Perm (Level ℓ)) (c : FiniteConfiguration ℓ F) :
    extendConfig F (finiteConfigPerm x σ c) =
      (extendConfig F c).update x (σ (c x)) := by
  ext y
  by_cases h : y = x
  · subst y
    simp [extendConfig_apply, finiteConfigPerm, Finsupp.update_apply, x.property]
  · by_cases hy : y ∈ F
    · have hn : (⟨y, hy⟩ : F) ≠ x := fun he => h (congrArg Subtype.val he)
      simp [extendConfig_apply, finiteConfigPerm,
        Finsupp.update_apply, hy, h, hn]
    · simp [extendConfig_apply, Finsupp.update_apply, hy, h]

end Heisenberg
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_BoundedStrip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate ENNReal Classical
open scoped ComplexConjugate BigOperators
open Filter Topology Metric
open scoped NNReal
open scoped NNReal

open scoped ComplexConjugate Topology
namespace GibbsStrip
variable {E : Type*} [CStarAlgebra E]

local instance instNormedAlgebraRat_solutions : NormedAlgebra ℚ E := NormedAlgebra.restrictScalars ℚ ℂ E

def evolve (K : E) (z : ℂ) (A : E) : E :=
  NormedSpace.exp ((Complex.I*z) • K) * A * NormedSpace.exp ((-(Complex.I*z)) • K)

end GibbsStrip

open Set Filter Complex
open scoped Topology

namespace HeisenbergStrip

def openStrip (β : ℝ) : Set ℂ := Complex.im ⁻¹' Ioo 0 β
def closedStrip (β : ℝ) : Set ℂ := Complex.im ⁻¹' Icc 0 β

def gaussian (z : ℂ) : ℂ := Complex.exp (-(z * z))

end HeisenbergStrip
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_TensorUnitSystem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace Heisenberg.TensorUnits

lemma prod_interleave {X E : Type*} [Monoid E] (L : List X) (hL : L.Nodup)
    (f g : X → E) (hfg : ∀ x∈L,∀ y∈L,x≠y → Commute (f x) (g y)) :
    (L.map f).prod*(L.map g).prod=(L.map (fun x=>f x*g x)).prod := by
  induction L with
  | nil=>simp
  | cons a L ih=>
    obtain ⟨ha,hL⟩:=List.nodup_cons.mp hL
    have hc : Commute (L.map f).prod (g a) := by
      apply Commute.list_prod_left
      intro z hz
      obtain ⟨x,hx,rfl⟩:=List.mem_map.mp hz
      exact hfg x (List.mem_cons_of_mem a hx) a (List.mem_cons_self ..)
        (fun he=>ha (he ▸ hx))
    simp only [List.map_cons,List.prod_cons]
    calc
      _=f a*((L.map f).prod*g a)*(L.map g).prod := by simp only [mul_assoc]
      _=(f a*g a)*((L.map f).prod*(L.map g).prod) := by rw [hc.eq]; simp only [mul_assoc]
      _=_ := by rw [ih hL (fun x hx y hy hxy=>hfg x (List.mem_cons_of_mem a hx) y (List.mem_cons_of_mem a hy) hxy)]

variable {R E : Type*} [CommSemiring R] [Semiring E] [Algebra R E]
variable {n : ℕ} {K : Type*} [Fintype K] [DecidableEq K]

def system (u : Fin n → K → K → E) (a b : Fin n → K) : E :=
  (List.ofFn (fun i=>u i (a i) (b i))).prod

omit [Fintype K] in
lemma system_mul (u : Fin n → K → K → E)
    (hu : ∀ i a b c d,u i a b*u i c d=if b=c then u i a d else 0)
    (hc : ∀ i j,i≠j → ∀ a b c d,Commute (u i a b) (u j c d))
    (a b c d : Fin n → K) :
    system u a b*system u c d=if b=c then system u a d else 0 := by
  have he := prod_interleave (List.ofFn (id : Fin n → Fin n))
    (List.nodup_ofFn.mpr Function.injective_id) (fun i=>u i (a i) (b i))
    (fun i=>u i (c i) (d i)) (fun i _ j _ hij=>hc i j hij ..)
  simp only [List.map_ofFn,Function.comp_def,id_eq] at he
  unfold system
  rw [he]
  by_cases hbc : b=c
  · subst c
    simp only [hu,ite_true]
  · rw [ite_eq_right hbc]
    obtain ⟨i,hi⟩:=Function.ne_iff.mp hbc
    apply List.prod_eq_zero
    apply List.mem_ofFn.mpr
    exact ⟨i,by rw [hu,ite_eq_right hi]⟩

omit [DecidableEq K] in
lemma system_diagonal_sum (R : Type*) [CommSemiring R] [Algebra R E] (u : Fin n → K → K → E) (hu : ∀ i,∑ a,u i a a=1) :
    ∑ a : Fin n → K,system u a a=1 := by
  have hh:=(MultilinearMap.mkPiAlgebraFin R n E).map_sum (fun i a=>u i a a)
  simp only [hu,MultilinearMap.mkPiAlgebraFin_apply] at hh
  simpa only [system,List.ofFn_const,List.prod_replicate,one_pow] using hh.symm

end Heisenberg.TensorUnits
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_MatrixUnitLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical BigOperators Matrix
namespace Heisenberg.TensorUnits
variable {R E K : Type*} [CommSemiring R] [Semiring E] [Algebra R E]
  [Fintype K] [DecidableEq K]

def liftLinear (u : K → K → E) : Matrix K K R →ₗ[R] E where
  toFun M:=∑ a,∑ b,M a b • u a b
  map_add' M N:=by simp only [Matrix.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' c M:=by simp only [Matrix.smul_apply,smul_eq_mul,mul_smul,Finset.smul_sum,RingHom.id_apply]

lemma unit_mul_lift (u : K → K → E)
    (hu : ∀ a b c d,u a b*u c d=if b=c then u a d else 0)
    (a b : K) (N : Matrix K K R) :
    u a b*liftLinear u N=∑ d,N b d • u a d := by
  simp only [liftLinear,LinearMap.coe_mk,AddHom.coe_mk,Finset.mul_sum,mul_smul_comm,hu]
  simp only [smul_ite,smul_zero]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]

lemma lift_mul (u : K → K → E)
    (hu : ∀ a b c d,u a b*u c d=if b=c then u a d else 0)
    (M N : Matrix K K R) : liftLinear u (M*N)=liftLinear u M*liftLinear u N := by
  change (∑ a,∑ b,(M*N) a b • u a b)=(∑ a,∑ b,M a b • u a b)*liftLinear u N
  simp only [Matrix.mul_apply,Finset.sum_smul,Finset.sum_mul,smul_mul_assoc,
    unit_mul_lift u hu,Finset.smul_sum,smul_smul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]

lemma lift_one (u : K → K → E) (hu : ∑ a,u a a=1) : liftLinear u (1:Matrix K K R)=1 := by
  unfold liftLinear
  simp only [LinearMap.coe_mk,AddHom.coe_mk,Matrix.one_apply,ite_smul,one_smul,zero_smul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  exact hu

def liftAlg (u : K → K → E)
    (hu : ∀ a b c d,u a b*u c d=if b=c then u a d else 0)
    (hs : ∑ a,u a a=1) : Matrix K K R →ₐ[R] E :=
  AlgHom.ofLinearMap (liftLinear u) (lift_one u hs) (lift_mul u hu)

end Heisenberg.TensorUnits
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_TensorLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical BigOperators Matrix
namespace Heisenberg.TensorUnits
variable {R E K : Type*} [CommSemiring R] [Semiring E] [Algebra R E]
  [Fintype K] [DecidableEq K]

def pairConfigEquiv (n : ℕ) (K : Type*) : (Fin n → K×K) ≃ (Fin n → K)×(Fin n → K) where
  toFun f:=(fun i=>(f i).1,fun i=>(f i).2)
  invFun f i:=(f.1 i,f.2 i)
  left_inv _:=rfl
  right_inv _:=rfl

end Heisenberg.TensorUnits
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_DeterminantExposure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open scoped Classical
open Matrix
namespace Heisenberg.Exposure

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {R : Type*} [CommRing R]

def swapMix (i j : n) (u : R) : Matrix n n R :=
  (1 - u) • (1 : Matrix n n R) + u • (Equiv.swap i j).permMatrix R

def DeterminantLaw {Ω : Type*} [Fintype Ω]
    (p : Ω → R) (X : Ω → Matrix n n R) : Prop :=
  ∀ D : Matrix n n R,
    ∑ ω, p ω * (1 - D * X ω).det =
      (1 - D * ∑ ω, p ω • X ω).det

end Heisenberg.Exposure

open scoped Classical
open Matrix
namespace Heisenberg.Exposure

variable {Q : Type*} [Fintype Q] [DecidableEq Q]
variable (R : Type*) [Field R]

def partialMatrix (f : Q → Option Q) : Matrix Q Q R :=
  fun i j => if f i = some j then 1 else 0

def walk (f : Q → Option Q) : ℕ → Q → Option Q
  | 0, i => some i
  | n + 1, i => (f i).bind (walk f n)

def Escapes (f : Q → Option Q) (i : Q) : Prop := ∃ n, walk f n i = none

end Heisenberg.Exposure
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_FirstReturns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped Classical
open Matrix
namespace Heisenberg.Exposure

section
variable {J Q : Type*} [Fintype J] [Fintype Q] [DecidableEq J] [DecidableEq Q]
variable (R : Type*) [Field R]

def restrictPerm (π : Equiv.Perm (J ⊕ Q)) (q : Q) : Option Q :=
  match π (Sum.inr q) with
  | Sum.inl _ => none
  | Sum.inr r => some r

def AllHit (π : Equiv.Perm (J ⊕ Q)) : Prop :=
  ∀ x, ∃ j, π.SameCycle x (Sum.inl j)

def columnPerm (π : Equiv.Perm (J ⊕ Q)) : Matrix (J ⊕ Q) (J ⊕ Q) R :=
  (π.permMatrix R).transpose

def pinTestMatrix (W : Matrix J J R) : Matrix (J ⊕ Q) (J ⊕ Q) R :=
  Matrix.fromBlocks W 0 0 1

end

section
variable {J Q : Type*} [Fintype J] [Fintype Q] [DecidableEq J] [DecidableEq Q]
variable (R : Type*) [Field R]

def hittingResolvent (K : Matrix (J ⊕ Q) (J ⊕ Q) R) : Matrix J J R :=
  K.toBlocks₁₁ + K.toBlocks₁₂ * (1 - K.toBlocks₂₂)⁻¹ * K.toBlocks₂₁

end

section

variable {J Q Ω : Type*} [Fintype J] [Fintype Q] [Fintype Ω]
  [DecidableEq J] [DecidableEq Q]
variable {R : Type*} [Field R]

def hitWeight (μ : Ω → R) (π : Ω → Equiv.Perm (J ⊕ Q)) : R :=
  ∑ ω, if AllHit (π ω) then μ ω else 0

end

end Heisenberg.Exposure
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_ConditionalMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open Matrix

namespace Heisenberg.Exposure

section
variable {J Q : Type*} [Fintype J] [Fintype Q]

lemma reachesPin (π : Equiv.Perm (J ⊕ Q)) (h : AllHit π) (x : J ⊕ Q) :
    ∃ n : ℕ, ∃ j : J, (π ^ n) x = Sum.inl j := by
  obtain ⟨j, hj⟩ := h x
  obtain ⟨n, hn⟩ := hj.exists_nat_pow_eq
  exact ⟨n, j, hn⟩

def firstPinTime (π : Equiv.Perm (J ⊕ Q)) (h : AllHit π) (x : J ⊕ Q) : ℕ :=
  Nat.find (reachesPin π h x)

def firstPin (π : Equiv.Perm (J ⊕ Q)) (h : AllHit π) (x : J ⊕ Q) : J :=
  Classical.choose (Nat.find_spec (reachesPin π h x))

def nextPin (π : Equiv.Perm (J ⊕ Q)) (h : AllHit π) (j : J) : J :=
  firstPin π h (π (Sum.inl j))

end

section
variable {J Q : Type*} [Fintype J] [Fintype Q] [DecidableEq J] [DecidableEq Q]
variable (R : Type*) [Field R]

def firstPinMatrix (π : Equiv.Perm (J ⊕ Q)) (h : AllHit π) : Matrix J (J ⊕ Q) R :=
  fun i x => if firstPin π h x = i then 1 else 0

def nextPinMatrix (π : Equiv.Perm (J ⊕ Q)) (h : AllHit π) : Matrix J J R :=
  fun i j => if nextPin π h j = i then 1 else 0

end

end Heisenberg.Exposure
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_ExchangeDeterminants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open Matrix

namespace Heisenberg.Exposure

variable {N Ω Ψ B R : Type*} [Fintype N] [DecidableEq N]
  [Fintype Ω] [Fintype Ψ] [Fintype B] [CommRing R]

omit [Fintype N] [DecidableEq N] [Fintype Ω] [Fintype Ψ] [Fintype B] [CommRing R] in
def splitArray (n : ℕ) : (Fin (n+1) → B) ≃ B × (Fin n → B) where
  toFun f := (f 0,fun i => f i.succ)
  invFun z := Fin.cons z.1 z.2
  left_inv f := by funext i; refine Fin.cases rfl (fun i => rfl) i
  right_inv z := by rfl

omit [Fintype N] [DecidableEq N] [Fintype Ω] [Fintype Ψ] [Fintype B] [CommRing R] in
def orderedProduct {A : Type*} [Monoid A] : (n : ℕ) → (Fin n → A) → A
  | 0, _ => 1
  | n+1, f => f 0 * orderedProduct n (fun i => f i.succ)

end Heisenberg.Exposure

namespace Heisenberg.LayeredExchange
variable {T V : Type*}

def fibers (σ : T → Equiv.Perm V) : Equiv.Perm (T × V) where
  toFun z := (z.1, σ z.1 z.2)
  invFun z := (z.1, (σ z.1).symm z.2)
  left_inv z := by simp
  right_inv z := by simp

@[simp] lemma fibers_apply (σ : T → Equiv.Perm V) (t : T) (v : V) :
    fibers σ (t,v) = (t,σ t v) := rfl

@[simp] lemma fibers_one : fibers (fun _ : T => (1 : Equiv.Perm V)) = 1 := by
  ext ⟨t,v⟩ <;> rfl

lemma fibers_mul (σ τ : T → Equiv.Perm V) :
    fibers (fun t => σ t * τ t) = fibers σ * fibers τ := by rfl

def wiring (s : Equiv.Perm T) (σ : T → Equiv.Perm V) : Equiv.Perm (T × V) :=
  (Equiv.prodCongr s (Equiv.refl V)) * fibers σ

@[simp] lemma wiring_apply (s : Equiv.Perm T) (σ : T → Equiv.Perm V) (t : T) (v : V) :
    wiring s σ (t,v) = (s t,σ t v) := rfl

end Heisenberg.LayeredExchange

namespace Heisenberg.LayeredExchange

section
open Exposure
variable {T V : Type*}

def fibersHom : (T → Equiv.Perm V) →* Equiv.Perm (T × V) where
  toFun := fibers
  map_one' := fibers_one
  map_mul' := fibers_mul

end

open Exposure
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {R : Type*} [CommRing R]

def forwardHom : Equiv.Perm V →* Matrix V V R where
  toFun π := (π.permMatrix R).transpose
  map_one' := by simp
  map_mul' π σ := by rw [Matrix.permMatrix_mul, Matrix.transpose_mul]

end Heisenberg.LayeredExchange
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_ExchangeCycles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open Matrix

open scoped Classical
namespace Heisenberg.Cycle

section
open Equiv
variable {V : Type*}
abbrev Classes (π : Perm V) := Quotient (Perm.SameCycle.setoid π)
def classOf (π : Perm V) (i : V) : Classes π := Quotient.mk _ i
lemma classOf_eq_iff (π : Perm V) (i j : V) :
    classOf π i = classOf π j ↔ π.SameCycle i j := Quotient.eq
@[simp] lemma classOf_apply (π : Perm V) (i : V) :
    classOf π (π i) = classOf π i :=
  (classOf_eq_iff π _ _).mpr ((Perm.SameCycle.refl π i).apply_left)
abbrev MissingClasses (π : Perm V) (P : Set V) :=
  {c : Classes π // ∀ i ∈ P, c ≠ classOf π i}
noncomputable def missingCount (π : Perm V) (P : Set V) : ℕ :=
  Nat.card (MissingClasses π P)

def colorSpace (π : Perm V) (P : Set V) : Submodule (ZMod 2) (V → ZMod 2) where
  carrier := {f | (∀ i, f (π i) = f i) ∧ ∀ i ∈ P, f i = 0}
  zero_mem' := by simp
  add_mem' := by
    rintro f g ⟨hf,hfP⟩ ⟨hg,hgP⟩
    exact ⟨fun i => by simp [hf,hg],fun i hi => by simp [hfP i hi,hgP i hi]⟩
  smul_mem' := by
    rintro r f ⟨hf,hfP⟩
    exact ⟨fun i => by simp [hf],fun i hi => by simp [hfP i hi]⟩

variable [Fintype V]

lemma color_eq_of_sameCycle (π : Perm V) (P : Set V) (f : colorSpace π P)
    {i j : V} (h : π.SameCycle i j) : f.val i = f.val j := by
  obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
  have ha : ∀ n, f.val ((π^n) i) = f.val i := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ',Perm.mul_apply,f.property.1,ih]
  rw [← hn,ha]

def colorEquiv (π : Perm V) (P : Set V) :
    colorSpace π P ≃ (MissingClasses π P → ZMod 2) where
  toFun f c := Quotient.lift f.val (fun i j h => color_eq_of_sameCycle π P f h) c.val
  invFun c := ⟨fun i => if h : ∀ j ∈ P, classOf π i ≠ classOf π j then c ⟨classOf π i,h⟩ else 0, by
    constructor
    · intro i
      simp only [classOf_apply]
    · intro i hi
      exact dite_eq_right (by intro h; exact h i hi rfl)⟩
  left_inv f := by
    apply Subtype.ext
    funext i
    dsimp
    split_ifs with h
    · rfl
    · obtain ⟨j,hj,hij⟩ := by simpa only [not_forall,not_not] using h
      have he := color_eq_of_sameCycle π P f ((classOf_eq_iff π i j).mp hij)
      exact (he.trans (f.property.2 j hj)).symm
  right_inv c := by
    funext q
    rcases q with ⟨q,hq⟩
    induction q using Quotient.inductionOn with | _ i =>
      dsimp
      split_ifs with h
      · rfl
      · exact (h hq).elim

end

open Equiv
variable {V : Type*} [Fintype V]

def MissingSet (π : Perm V) (P : Set V) : Set V :=
  {i | ∀ j ∈ P, classOf π i ≠ classOf π j}

def OutsideHit (τ : Perm V) (P A : Set V) : Prop :=
  ∀ i ∉ A, ∃ j ∈ P, τ.SameCycle i j

end Heisenberg.Cycle
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_FiniteHistories
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical

open scoped BigOperators Classical
namespace Heisenberg.Exposure

section History
variable {V : Type*}

def trajectory (τ : ℕ → Equiv.Perm V) (c : ℕ → Bool) : ℕ → Equiv.Perm V
  | 0 => 1
  | n+1 => (if c n then τ n else 1) * trajectory τ c n

@[simp] lemma trajectory_zero (τ : ℕ → Equiv.Perm V) (c : ℕ → Bool) :
    trajectory τ c 0 = 1 := rfl

@[simp] lemma trajectory_succ (τ : ℕ → Equiv.Perm V) (c : ℕ → Bool) (n : ℕ) (a : V) :
    trajectory τ c (n+1) a = if c n then τ n (trajectory τ c n a) else trajectory τ c n a := by
  cases hc : c n <;> simp [trajectory, hc]

end History

variable {I B : Type*} [Fintype I] [Fintype B]

def productWeight (w : I → B → ℝ) (c : I → B) : ℝ := ∏ i, w i (c i)

def merge (M : I → Prop) [DecidablePred M] (a : {i // M i} → B) (b : {i // ¬M i} → B) : I → B :=
  (Equiv.piEquivPiSubtypeProd M (fun _ => B)).symm (a,b)


end Heisenberg.Exposure

open scoped Classical

namespace Heisenberg.LayeredExchange
variable {T V : Type*}

def transport (s : Equiv.Perm T) (σ : T → Equiv.Perm V) (t : T) : ℕ → Equiv.Perm V
  | 0 => 1
  | n+1 => σ ((s^n) t) * transport s σ t n

lemma wiring_pow (s : Equiv.Perm T) (σ : T → Equiv.Perm V) (t : T) (v : V) (n : ℕ) :
    (wiring s σ ^ n) (t,v) = ((s^n) t, transport s σ t n v) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ',Equiv.Perm.mul_apply,ih,wiring_apply,pow_succ',Equiv.Perm.mul_apply]
    rfl

lemma invariant_propagates {B : Type*} (s : Equiv.Perm T) (σ : T → Equiv.Perm V)
    (c : T × V → B) (hc : ∀ z, c (wiring s σ z) = c z) (t : T) (v : V) (n : ℕ) :
    c ((s^n) t,transport s σ t n v) = c (t,v) := by
  rw [← wiring_pow]
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ',Equiv.Perm.mul_apply,hc,ih]

lemma invariant_cut {B : Type*} (s : Equiv.Perm T) (σ : T → Equiv.Perm V)
    (c : T × V → B) (hc : ∀ z, c (wiring s σ z) = c z)
    (t : T) (n : ℕ) (hn : (s^n) t = t) :
    ∀ v, c (t,transport s σ t n v) = c (t,v) := by
  intro v
  simpa only [hn] using invariant_propagates s σ c hc t v n

end Heisenberg.LayeredExchange

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_LayerExposure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open scoped BigOperators Classical
open scoped Classical

namespace Heisenberg.Exposure

section
open Heisenberg.Cycle Heisenberg.LayeredExchange
variable {T V : Type*} [Fintype T] [Fintype V]

def layerHistory (s : Equiv.Perm T) (τ : T → Equiv.Perm V) (b : T → Bool) :
    Equiv.Perm (T × V) := wiring s (fun t => if b t then τ t else 1)

def layerRevealed (τ : T → Equiv.Perm V) (A : Set (T × V)) (t : T) : Prop :=
  ∃ v, (t,v) ∈ A ∧ τ t v ≠ v

def layerExposure (s : Equiv.Perm T) (τ : T → Equiv.Perm V)
    (P : Set (T × V)) (b c : T → Bool) : Prop :=
  (∀ z ∈ MissingSet (layerHistory s τ b) P, layerHistory s τ b z = layerHistory s τ c z) ∧
    MissingSet (layerHistory s τ c) P = MissingSet (layerHistory s τ b) P

end

section
open LayeredExchange Heisenberg.Cycle
variable {V : Type*} [Fintype V] [DecidableEq V]

def residualCoins {n : ℕ} (M : Fin n → Prop) (base c : Fin n → Bool) : Fin n → Bool :=
  fun i => if M i then base i else c i

attribute [local irreducible] MissingSet layerHistory

end

open Heisenberg.Cycle LayeredExchange
variable {V W : Type*}

def splitHolePerm (σ : Equiv.Perm V) (A P : Set V)
    (hA : ∀ x,σ x ∉ A ↔ x ∉ A) :
    Equiv.Perm ({x : {z : V // z ∉ A} // x.val ∈ P} ⊕
      {x : {z : V // z ∉ A} // x.val ∉ P}) :=
  (Equiv.sumCompl (fun x : {z : V // z ∉ A} => x.val ∈ P)).symm.permCongr
    (σ.subtypePerm hA)

end Heisenberg.Exposure
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_HittingKernels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open scoped BigOperators Classical
open scoped Classical

namespace Heisenberg.Hitting
open Filter
variable {V : Type*} [Fintype V]

def affineIter (A : Matrix V V ℝ) (b : V → ℝ) : ℕ → V → ℝ
  | 0 => 0
  | n+1 => b + A *ᵥ affineIter A b n

def affineHit (A : Matrix V V ℝ) (b : V → ℝ) (i : V) : ℝ := ⨆ n, affineIter A b n i

end Heisenberg.Hitting
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_HittingEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open scoped BigOperators Classical
open scoped Classical

open scoped Classical
open Filter
namespace Heisenberg.Hitting

variable {V : Type*} [Fintype V]

structure DoublySubstochastic (U : Matrix V V ℝ) : Prop where
  nonneg : ∀ i j, 0 ≤ U i j
  row : ∀ i, ∑ j, U i j ≤ 1
  col : ∀ j, ∑ i, U i j ≤ 1

def backward (U : Matrix V V ℝ) (f : V → ℝ) (i : V) : ℝ := ∑ j, U j i * f j

def hitStep (U : Matrix V V ℝ) (T : Finset V) (f : V → ℝ) (i : V) : ℝ :=
  if i ∈ T then 1 else backward U f i

def hitIter (U : Matrix V V ℝ) (T : Finset V) : ℕ → V → ℝ
  | 0 => fun i => if i ∈ T then 1 else 0
  | n + 1 => hitStep U T (hitIter U T n)

def hitting (U : Matrix V V ℝ) (T : Finset V) (i : V) : ℝ :=
  ⨆ n, hitIter U T n i

def energy (U : Matrix V V ℝ) (f : V → ℝ) : ℝ :=
  ∑ i, f i * (f i - ∑ j, U i j * f j)

end Heisenberg.Hitting

namespace Heisenberg.Exposure
open Matrix Heisenberg.Hitting
variable {V Ω : Type*} [Fintype V] [DecidableEq V] [Fintype Ω]

def killedMean (μ : Ω → ℝ) (σ : Ω → Equiv.Perm V) (D : Set V) : Matrix V V ℝ :=
  fun i j => if i∈D ∧ j∈D then ∑ c,μ c*(if i=σ c j then 1 else 0) else 0

end Heisenberg.Exposure
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_ReturnConditioning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open scoped BigOperators Classical
open scoped Classical
open scoped Classical
open Filter

open scoped Classical
namespace Heisenberg.Return
open Equiv
variable {V : Type*}

def HasHit (π : Perm V) (P : Set V) (x : V) : Prop := ∃ n : ℕ, (π ^ n) x ∈ P

lemma hasHit_iff_cycle [Fintype V] (π : Perm V) (P : Set V) (x : V) :
    HasHit π P x ↔ ∃ p ∈ P, π.SameCycle x p := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨(π ^ n) x, hn, (Perm.SameCycle.refl π x).pow_right⟩
  · rintro ⟨p, hp, hc⟩
    obtain ⟨n, hn⟩ := hc.exists_nat_pow_eq
    exact ⟨n, hn ▸ hp⟩

lemma hasHit_apply [Fintype V] (π : Perm V) (P : Set V) (x : V) :
    HasHit π P (π x) ↔ HasHit π P x := by
  simp only [hasHit_iff_cycle, Perm.sameCycle_apply_left]

lemma hasHit_of_mem (π : Perm V) {P : Set V} {x : V} (hx : x ∈ P) : HasHit π P x :=
  ⟨0, hx⟩

def hitTime (π : Perm V) (P : Set V) (x : V) (h : HasHit π P x) := Nat.find h

def hitPoint (π : Perm V) (P : Set V) (x : V) (h : HasHit π P x) : V :=
  (π ^ hitTime π P x h) x

lemma hitPoint_mem (π : Perm V) (P : Set V) (x : V) (h : HasHit π P x) :
    hitPoint π P x h ∈ P := Nat.find_spec h

lemma hitTime_le (π : Perm V) (P : Set V) (x : V) (h : HasHit π P x)
    {n : ℕ} (hn : (π ^ n) x ∈ P) : hitTime π P x h ≤ n := Nat.find_min' h hn

variable [Fintype V]

def firstValue (π : Perm V) (P : Set V) (x : V) : Option V :=
  if h : HasHit π P x then some (hitPoint π P x h) else none

def nextTime (π : Perm V) (P : Set V) (i : P) : ℕ :=
  hitTime π P (π i) ((hasHit_apply π P i).mpr (hasHit_of_mem π i.property)) + 1

def nextPoint (π : Perm V) (P : Set V) (i : P) : P :=
  ⟨hitPoint π P (π i) ((hasHit_apply π P i).mpr (hasHit_of_mem π i.property)),
    hitPoint_mem π P _ _⟩

lemma nextTime_pos (π : Perm V) (P : Set V) (i : P) : 0 < nextTime π P i := Nat.succ_pos _

lemma nextPoint_spec (π : Perm V) (P : Set V) (i : P) :
    (π ^ nextTime π P i) i = (nextPoint π P i : V) := by
  simp only [nextTime, nextPoint, hitPoint, pow_succ, Perm.mul_apply]

lemma nextTime_min (π : Perm V) (P : Set V) (i : P) {n : ℕ}
    (hn : 0 < n) (hp : (π ^ n) i ∈ P) : nextTime π P i ≤ n := by
  have he : (π ^ (n - 1)) (π i) ∈ P := by
    rw [← Perm.mul_apply, ← pow_succ, Nat.sub_add_cancel hn]
    exact hp
  have hm := hitTime_le π P (π i) ((hasHit_apply π P i).mpr (hasHit_of_mem π i.property)) he
  exact Nat.succ_le_of_lt (lt_of_le_of_lt hm (Nat.sub_lt hn (by omega)))

lemma nextPoint_injective (π : Perm V) (P : Set V) : Function.Injective (nextPoint π P) := by
  have haux (i j : P) (hn : nextTime π P i ≤ nextTime π P j)
      (he : nextPoint π P i = nextPoint π P j) : i = j := by
    let n := nextTime π P i
    let m := nextTime π P j
    have hn0 : 0 < n := nextTime_pos π P i
    have hm0 : 0 < m := nextTime_pos π P j
    have hb : (π ^ (m - n)) (j : V) = (i : V) := by
      apply (π ^ n).injective
      calc
        (π ^ n) ((π ^ (m - n)) (j : V)) = (π ^ m) (j : V) := by
          rw [← Perm.mul_apply, ← pow_add, Nat.add_sub_cancel' hn]
        _ = (nextPoint π P j : V) := nextPoint_spec π P j
        _ = (nextPoint π P i : V) := congrArg Subtype.val he.symm
        _ = (π ^ n) (i : V) := (nextPoint_spec π P i).symm
    have hz : m - n = 0 := by
      by_contra hne
      have ht := nextTime_min π P j (Nat.pos_of_ne_zero hne) (hb ▸ i.property)
      change m ≤ m - n at ht
      omega
    apply Subtype.ext
    simpa only [hz, pow_zero, Perm.one_apply] using hb.symm
  intro i j he
  rcases le_total (nextTime π P i) (nextTime π P j) with hle | hle
  · exact haux i j hle he
  · exact (haux j i hle he.symm).symm

def nextPermutation (π : Perm V) (P : Set V) : Perm P :=
  Equiv.ofBijective (nextPoint π P) ((Finite.injective_iff_bijective).mp (nextPoint_injective π P))

end Heisenberg.Return

open scoped Classical
namespace Heisenberg.Conditioning
variable {Ω : Type*} [Fintype Ω]

def mass (μ : Ω → ℝ) (E : Ω → Ω → Prop) (b : Ω) : ℝ :=
  ∑ c,if E b c then μ c else 0

def conditional (μ : Ω → ℝ) (E : Ω → Ω → Prop) (F : Ω → ℝ) (b : Ω) : ℝ :=
  (∑ c,if E b c then μ c * F c else 0)/mass μ E b

end Heisenberg.Conditioning
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_LayerEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open scoped BigOperators Classical
open scoped Classical
open scoped Classical
open Filter
open scoped Classical
open scoped Classical

open Filter Topology
open scoped RealInnerProductSpace Classical
namespace Heisenberg.MeshEnergy
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
abbrev Op := E →L[ℝ] E

variable [CompleteSpace E]

def sweep (D : ℕ → Op (E:=E)) : ℕ → ℝ → Op (E:=E)
  | 0, _ => 1
  | n+1, t => (1+t • D n) * sweep D n t

omit [CompleteSpace E] in
@[simp] lemma sweep_zero (D : ℕ → Op (E:=E)) (n : ℕ) : sweep D n 0 = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [sweep,ih]

end Heisenberg.MeshEnergy
namespace Heisenberg.MeshPair
open MeshEnergy
open scoped RealInnerProductSpace Classical
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def generator (w : E) : E →L[ℝ] E := (-1/2:ℝ) • (innerSL ℝ w).smulRight w

variable {V : Type*} [Fintype V] [DecidableEq V]

def edgeVector (I : Set V) (a b : V) : EuclideanSpace ℝ V :=
  EuclideanSpace.single a (if a ∈ I then 1 else 0) -
    EuclideanSpace.single b (if b ∈ I then 1 else 0)

end Heisenberg.MeshPair
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_KilledContractions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open scoped BigOperators Classical
open scoped Classical
open scoped Classical
open Filter
open scoped Classical
open scoped Classical
open Filter Topology
open scoped RealInnerProductSpace Classical

namespace Heisenberg.MeshPair
open scoped RealInnerProductSpace Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

def killedPermutation (I : Set V) (σ : Equiv.Perm V) (v : EuclideanSpace ℝ V) :
    EuclideanSpace ℝ V := WithLp.toLp 2 (fun i => if i ∈ I then v.ofLp (σ.symm i) else 0)

def killedCoin (I : Set V) (a b : V) (t : ℝ) (v : EuclideanSpace ℝ V) :
    EuclideanSpace ℝ V := (1-t/2) • v + (t/2) • killedPermutation I (Equiv.swap a b) v

end Heisenberg.MeshPair

namespace Heisenberg.MatrixContraction

variable {V : Type*} [Fintype V]

structure DoublySubstochastic (U : Matrix V V ℝ) : Prop where
  nonneg : ∀ i j, 0 ≤ U i j
  row : ∀ i, ∑ j, U i j ≤ 1
  col : ∀ j, ∑ i, U i j ≤ 1

def squareNorm (f : V → ℝ) : ℝ := ∑ i, f i ^ 2

def dot (f g : V → ℝ) : ℝ := ∑ i, f i * g i

end Heisenberg.MatrixContraction

namespace Heisenberg.MeshPair
open Heisenberg.MatrixContraction Matrix
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

def killedMatrix (D : Set V) (σ : Equiv.Perm V) : Matrix V V ℝ := fun i j =>
  if j ∈ D ∧ σ j ∈ D then if i=σ j then 1 else 0 else 0

def residualMatrix (D : Set V) (R : Prop) (c : Bool) (a b : V) (p : ℝ) : Matrix V V ℝ :=
  if R then killedMatrix D (if c then Equiv.swap a b else 1)
  else (1-p) • killedMatrix D 1 + p • killedMatrix D (Equiv.swap a b)

def euclideanMap (K : Matrix V V ℝ) : EuclideanSpace ℝ V →ₗ[ℝ] EuclideanSpace ℝ V where
  toFun v := WithLp.toLp 2 (K *ᵥ v.ofLp)
  map_add' v w := by ext i; simp [Matrix.mulVec_add]
  map_smul' r v := by ext i; simp [Matrix.mulVec_smul]

omit [DecidableEq V] in
@[simp] lemma euclideanMap_apply (K : Matrix V V ℝ) (v : EuclideanSpace ℝ V) (i : V) :
    (euclideanMap K v).ofLp i=(K *ᵥ v.ofLp) i := rfl

end Heisenberg.MeshPair
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_QuietSweeps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open scoped BigOperators Classical
open scoped Classical
open scoped Classical
open Filter
open scoped Classical
open scoped Classical
open Filter Topology
open scoped RealInnerProductSpace Classical

namespace Heisenberg.MeshPair

section
open Heisenberg.MeshEnergy Heisenberg.MatrixContraction Matrix Filter Topology
open scoped RealInnerProductSpace
variable {V : Type*} [Fintype V] [DecidableEq V]

def quietSweep (H D : Set V) (a b : ℕ → V) (t : ℝ) : ℕ → EuclideanSpace ℝ V → EuclideanSpace ℝ V
  | 0,v => v
  | n+1,v => euclideanMap (residualMatrix D (a n ∉ H ∨ b n ∉ H) false (a n) (b n) (t/2))
      (quietSweep H D a b t n v)

def maskedGenerator (H D : Set V) (a b : ℕ → V) (i : ℕ) :
    EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V :=
  if a i ∈ H ∧ b i ∈ H then generator (edgeVector D (a i) (b i)) else 0

def quietEnergy (H : Set V) (a b : ℕ → V) (n : ℕ) (v : EuclideanSpace ℝ V) : ℝ :=
  ∑ i ∈ Finset.range n,if a i ∈ H ∧ b i ∈ H then (v.ofLp (a i)-v.ofLp (b i))^2 else 0

end

open Heisenberg.MatrixContraction
variable {V : Type*} [Fintype V] [DecidableEq V]

def killedBetween (D E : Set V) (σ : Equiv.Perm V) : Matrix V V ℝ :=
  fun i j => if j∈D ∧ i∈E ∧ i=σ j then 1 else 0

def residualBetween (D E : Set V) (revealed : Prop)
    (c : Bool) (a b : V) (p : ℝ) : Matrix V V ℝ :=
  if revealed then killedBetween D E (if c then Equiv.swap a b else 1)
  else (1-p) • killedBetween D E 1+p • killedBetween D E (Equiv.swap a b)

end Heisenberg.MeshPair

namespace Heisenberg.Exposure
open Heisenberg.Cycle Heisenberg.LayeredExchange Heisenberg.MeshPair
variable {T V : Type*} [Fintype T] [Fintype V] [DecidableEq V]

def holeCut (s : Equiv.Perm T) (τ : T → Equiv.Perm V) (base : T → Bool)
    (P : Set (T×V)) (t : T) : Set V :=
  {v | (t,v)∉MissingSet (layerHistory s τ base) P}

def exposedStep (s : Equiv.Perm T) (a b : T → V) (base : T → Bool)
    (P : Set (T×V)) (I : Set V) (p : T → ℝ) (t : T) : Matrix V V ℝ :=
  let τ := fun i => Equiv.swap (a i) (b i)
  residualBetween (holeCut s τ base P t∩I) (holeCut s τ base P (s t)∩I)
    (layerRevealed τ (MissingSet (layerHistory s τ base) P) t) (base t) (a t) (b t) (p t)

def exposedSweep (s : Equiv.Perm T) (a b : T → V) (base : T → Bool)
    (P : Set (T×V)) (I : Set V) (p : T → ℝ) (r : ℕ → T) :
    ℕ → EuclideanSpace ℝ V → EuclideanSpace ℝ V
  | 0,v => v
  | n+1,v => euclideanMap (exposedStep s a b base P I p (r n))
      (exposedSweep s a b base P I p r n v)

end Heisenberg.Exposure
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_ExposedEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open scoped BigOperators Classical
open scoped Classical
open scoped Classical
open Filter
open scoped Classical
open scoped Classical
open Filter Topology
open scoped RealInnerProductSpace Classical

open scoped BigOperators Classical
namespace Heisenberg.Bernoulli
variable {I : Type*} [Fintype I]

def weight (p : I → ℝ) (c : I → Bool) : ℝ := ∏ i, if c i then p i else 1-p i

def join (i : I) (b : Bool) (d : {j // j ≠ i} → Bool) : I → Bool :=
  (Equiv.funSplitAt i Bool).symm (b,d)

omit [Fintype I] in
@[simp] lemma join_at (i : I) (b : Bool) (d : {j // j ≠ i} → Bool) :
    join i b d i = b := by simp [join,Equiv.funSplitAt]

omit [Fintype I] in
@[simp] lemma join_ne (i : I) (b : Bool) (d : {j // j ≠ i} → Bool) (j : {j // j ≠ i}) :
    join i b d j = d j := by simp [join,Equiv.funSplitAt,j.property]

def test (s : Finset I) (c : I → Bool) : ℝ := if ∀ i ∈ s, c i = true then 1 else 0

end Heisenberg.Bernoulli
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_CycleWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix
open Filter
open scoped Classical
open Filter Topology
open scoped RealInnerProductSpace Classical
open scoped BigOperators Classical

namespace Heisenberg.Exposure

section
open Heisenberg.Cycle Heisenberg.LayeredExchange Heisenberg.Bernoulli
variable {T V : Type*} [Fintype T] [Fintype V]

def layerWeight (s : Equiv.Perm T) (a b : T → V) (P : Set (T × V)) (c : T → Bool) : ℝ :=
  2^missingCount (layerHistory s (fun j => Equiv.swap (a j) (b j)) c) P

def layerPartition (s : Equiv.Perm T) (a b : T → V) (P : Set (T × V)) (p : T → ℝ) : ℝ :=
  ∑ c,weight p c*layerWeight s a b P c

def layerMass (s : Equiv.Perm T) (a b : T → V) (P : Set (T × V)) (p : T → ℝ) (c : T → Bool) : ℝ :=
  weight p c*layerWeight s a b P c / layerPartition s a b P p

end

open Heisenberg.MeshPair Heisenberg.Bernoulli

end Heisenberg.Exposure

open scoped Classical
namespace Heisenberg.Geometry
abbrev Site (d : ℕ) := Fin d → ℤ

def Step {d : ℕ} (x y : Site d) : Prop :=
  ∃ j, (y j = x j + 1 ∨ x j = y j + 1) ∧ ∀ k, k ≠ j → y k = x k

def Box {d : ℕ} (r : ℤ) : Set (Site d) := {x | ∀ j, |x j| ≤ r}
def Shell {d : ℕ} (r : ℤ) : Set (Site d) := {x | x ∈ Box r ∧ ∃ j, |x j| = r}

def Reach {d : ℕ} (U : Set (Site d)) (x y : Site d) : Prop :=
  Relation.ReflTransGen (fun a b => Step a b ∧ a ∈ U ∧ b ∈ U) x y

lemma step_symm {d : ℕ} {x y : Site d} (h : Step x y) : Step y x := by
  obtain ⟨j, h, hj⟩ := h
  exact ⟨j, h.symm, fun k hk => (hj k hk).symm⟩

end Heisenberg.Geometry

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_LatticePaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical

namespace Heisenberg.Geometry


abbrev Direction (d : ℕ) := Fin d × Bool

def Ray {d : ℕ} (x : Site d) (q : Direction d) (z : Site d) : Prop :=
  (if q.2 then x q.1 < z q.1 else z q.1 < x q.1) ∧
    ∀ k, k ≠ q.1 → z k = x k

def latticeGraph {d : ℕ} (U : Set (Site d)) : SimpleGraph (Site d) where
  Adj x y := Step x y ∧ x ∈ U ∧ y ∈ U
  symm := ⟨fun _ _ h => ⟨step_symm h.1, h.2.2, h.2.1⟩⟩
  loopless := ⟨by
    intro x h
    obtain ⟨j, h, _⟩ := h.1
    omega⟩

def boxFinset (d r : ℕ) : Finset (Site d) :=
  Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(r : ℤ)) r)

@[simp] lemma mem_boxFinset (d r : ℕ) (x : Site d) :
    x ∈ boxFinset d r ↔ x ∈ Box r := by
  simp only [boxFinset, Fintype.mem_piFinset, Finset.mem_Icc, Box, Set.mem_ofPred_eq, abs_le]

end Heisenberg.Geometry
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_LatticeCuts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical

namespace Heisenberg.Geometry

def Ball {d : ℕ} (r : ℤ) (x : Site d) : Set (Site d) :=
  {z | ∀ j, |z j - x j| ≤ r}

lemma translate_mem_ball {d : ℕ} (u z : Site d) (r : ℤ) :
    u + z ∈ Ball r u ↔ z ∈ Box r := by
  simp [Ball, Box]

def ballFinset (d r : ℕ) (u : Site d) : Finset (Site d) :=
  (boxFinset d r).image (fun z => u + z)

@[simp] lemma mem_ballFinset (d r : ℕ) (u z : Site d) :
    z ∈ ballFinset d r u ↔ z ∈ Ball r u := by
  constructor
  · intro hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
    exact (translate_mem_ball u a r).mpr ((mem_boxFinset ..).mp ha)
  · intro hz
    apply Finset.mem_image.mpr
    refine ⟨z - u, ?_, by abel⟩
    exact (mem_boxFinset ..).mpr hz

end Heisenberg.Geometry

namespace Heisenberg.LatticePotential
variable {A : Type*} [AddCommGroup A]

def integral (f : ℤ → A) : ℤ → A
  | .ofNat n => ∑ k ∈ Finset.range n, f k
  | .negSucc n => -(∑ k ∈ Finset.range (n+1), f (-(k:ℤ)-1))

@[simp] lemma integral_zero (f : ℤ → A) : integral f 0 = 0 := by simp [integral]

abbrev Site (d : ℕ) := Fin d → ℤ

def shift {d : ℕ} (x : Site d) (i : Fin d) : Site d := Function.update x i (x i+1)

def Closed {d : ℕ} (F : Site d → Fin d → A) : Prop :=
  ∀ x i j, F x i+F (shift x i) j = F x j+F (shift x j) i

end Heisenberg.LatticePotential

namespace Heisenberg.LatticeCut
open Heisenberg.LatticePotential
abbrev Edge (d : ℕ) := Site d × Fin d

def color {d : ℕ} (H : Set (Site d)) (x : Site d) : ℤ := if x ∈ H then 1 else 0

def Cut {d : ℕ} (H : Set (Site d)) (e : Edge d) : Prop := color H e.1 ≠ color H (shift e.1 e.2)

def square {d : ℕ} (x : Site d) (i j : Fin d) : Finset (Edge d) :=
  {(x,i),(shift x i,j),(x,j),(shift x j,i)}

def Linked {d : ℕ} (H : Set (Site d)) (e f : Edge d) : Prop :=
  Cut H e ∧ Cut H f ∧ ∃ x i j, i ≠ j ∧ e ∈ square x i j ∧ f ∈ square x i j

def CutReach {d : ℕ} (H : Set (Site d)) (e f : Edge d) := Relation.ReflTransGen (Linked H) e f

def gradient {d : ℕ} (H : Set (Site d)) (e : Edge d) (x : Site d) (i : Fin d) : ℤ :=
  if CutReach H e (x,i) then color H (shift x i)-color H x else 0

def Connected {d : ℕ} (H : Set (Site d)) : Prop :=
  ∀ x ∈ H, ∀ y ∈ H, Heisenberg.Geometry.Reach H x y

end Heisenberg.LatticeCut
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_LatticeHulls
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical

namespace Heisenberg.LatticeHull
open Heisenberg.Geometry

def Hull {d : ℕ} (A : Set (Site d)) (b : Site d) : Set (Site d) :=
  {x | ¬ Reach Aᶜ b x}

end Heisenberg.LatticeHull
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_HullComponents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical

namespace Heisenberg.LatticeCut
open Heisenberg.Geometry
open Heisenberg.LatticePotential (shift)

def Boundary {d : ℕ} (H : Set (Site d)) : Set (Site d) :=
  {v | v ∉ H ∧ ∃ u ∈ H, Step u v}

def outer {d : ℕ} (H : Set (Site d)) (e : Edge d) : Site d :=
  if e.1 ∈ H then shift e.1 e.2 else e.1

end Heisenberg.LatticeCut

namespace Heisenberg.Geometry

lemma step_ball_one {d : ℕ} {x y : Site d} (h : Step x y) : y ∈ Ball 1 x := by
  obtain ⟨j,hj,hother⟩ := h
  intro k
  by_cases hk : k = j
  · subst k; rw [abs_le]; rcases hj with hj | hj <;> omega
  · rw [hother k hk,sub_self,abs_zero]; omega

end Heisenberg.Geometry

namespace Heisenberg.LatticeComponents
open Heisenberg.Geometry

def Component {d : ℕ} (Z : Set (Site d)) (x : Site d) : Set (Site d) :=
  {y | y ∈ Z ∧ Relation.ReflTransGen (fun a b => b ∈ Ball 8 a ∧ a ∈ Z ∧ b ∈ Z) x y}

def Thick {d : ℕ} (r : ℤ) (C : Set (Site d)) : Set (Site d) :=
  {z | ∃ x ∈ C, z ∈ Ball r x}

end Heisenberg.LatticeComponents

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_HullRouting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
namespace Heisenberg.LatticeComponents
open Heisenberg.Geometry Heisenberg.LatticeHull

lemma component_finite {d : ℕ} (Z : Set (Site d)) (hZ : Z.Finite) (x : Site d) :
    (Component Z x).Finite := hZ.subset (fun _ h => h.1)

end Heisenberg.LatticeComponents

namespace Heisenberg.HullRouting
open Heisenberg.Geometry Heisenberg.LatticeCut Heisenberg.LatticeHull Heisenberg.LatticeComponents

variable {d : ℕ}

def DisjointFamily (F : Finset (Set (Site d))) : Prop :=
  ∀ H ∈ F, ∀ K ∈ F, H ≠ K → Disjoint H K

def collapse (F : Finset (Set (Site d))) (rep : Set (Site d) → Site d) (x : Site d) : Site d :=
  if h : ∃ H ∈ F, x ∈ H then rep h.choose else x

def RouteRegion (Z : Set (Site d)) (F : Finset (Set (Site d)))
    (E : Set (Site d) → Set (Site d)) (u v : Site d) : Set (Site d) :=
  {z | (z = u ∨ z = v ∨ ∃ H ∈ F, (u ∈ H ∨ v ∈ H) ∧ z ∈ E H) ∧ z ∉ Z}

def allHulls (Z : Set (Site d)) (hZ : Z.Finite) (b : Site d) : Finset (Set (Site d)) :=
  hZ.toFinset.image (fun x => Hull (Thick 4 (Component Z x)) b)

def maxHulls (Z : Set (Site d)) (hZ : Z.Finite) (b : Site d) : Finset (Set (Site d)) :=
  (allHulls Z hZ b).filter (fun H => Maximal (· ∈ allHulls Z hZ b) H)

end Heisenberg.HullRouting
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_RegularComponents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped Classical

namespace Heisenberg.Geometry
lemma dist_le_iff_mem_ball {d r : ℕ} (x y : Site d) :
    dist x y ≤ (r:ℝ) ↔ y ∈ Ball r x := by
  rw [dist_pi_le_iff (by positivity)]
  change (∀ j, dist (x j) (y j) ≤ (r:ℝ)) ↔ ∀ j, |y j-x j| ≤ (r:ℤ)
  simp only [Int.dist_eq', abs_sub_comm (x _) (y _)]
  exact forall_congr' (fun j => by exact_mod_cast (Iff.rfl :
    ((|y j-x j|:ℤ):ℝ) ≤ (r:ℝ) ↔ ((|y j-x j|:ℤ):ℝ) ≤ (r:ℝ)))

lemma step_dist_le_one {d : ℕ} {u v : Site d} (h : Step u v) : dist u v ≤ 1 := by
  simpa only [Nat.cast_one] using (dist_le_iff_mem_ball (r:=1) u v).mpr (step_ball_one h)
end Heisenberg.Geometry

namespace Heisenberg.LatticeRegular
open Heisenberg.Geometry Heisenberg.LatticeComponents
variable {d : ℕ}

def Regular (Z : Set (Site d)) (x : Site d) (R M : ℕ) (ν : ℝ) : Prop :=
  (∀ z ∈ Ball (11*R : ℕ) x, ((ballFinset d M z).filter (· ∈ Z)).card < 2*d) ∧
  (∀ z ∈ Z, z ∉ Ball (10*R : ℕ) x → ∀ w ∈ Component Z z,
    dist z w ≤ (1+dist z x)^ν)

end Heisenberg.LatticeRegular

open scoped Classical
open Filter Topology

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_RoutedNetworks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped Classical
open scoped Classical
open Filter Topology

open scoped Classical
namespace Heisenberg.RoutedFlow

lemma sum_eq_of_zero_off {E : Type*} (s t : Finset E) (f : E → ℝ)
    (hs : ∀ e ∈ s, e ∉ t → f e = 0) (ht : ∀ e ∈ t, e ∉ s → f e = 0) :
    (∑ e ∈ s, f e) = ∑ e ∈ t, f e := by
  calc
    _ = ∑ e ∈ s ∩ t, f e := by
      symm
      apply Finset.sum_subset Finset.inter_subset_left
      intro e he hne
      exact hs e he (fun h => hne (Finset.mem_inter.mpr ⟨he,h⟩))
    _ = ∑ e ∈ t, f e := by
      apply Finset.sum_subset Finset.inter_subset_right
      intro e he hne
      exact ht e he (fun h => hne (Finset.mem_inter.mpr ⟨h,he⟩))

structure Network (V E : Type*) where
  src : E → V
  dst : E → V
  incidentFinite : ∀ v, {e | src e = v ∨ dst e = v}.Finite

namespace Network
variable {V E : Type*} (N : Network V E)

def gradient (g : V → ℝ) (e : E) : ℝ := g (N.src e) - g (N.dst e)

def edges (g : V →₀ ℝ) : Finset E :=
  g.support.biUnion (fun v => (N.incidentFinite v).toFinset)

lemma mem_edges (g : V →₀ ℝ) (e : E) :
    e ∈ N.edges g ↔ N.src e ∈ g.support ∨ N.dst e ∈ g.support := by
  simp only [edges,Finset.mem_biUnion,Set.Finite.mem_toFinset,Set.mem_ofPred_eq]
  constructor
  · rintro ⟨v,hv,h|h⟩
    · exact Or.inl (h ▸ hv)
    · exact Or.inr (h ▸ hv)
  · rintro (h|h)
    · exact ⟨N.src e,h,Or.inl rfl⟩
    · exact ⟨N.dst e,h,Or.inr rfl⟩

lemma gradient_zero_of_not_mem (g : V →₀ ℝ) {e : E} (he : e ∉ N.edges g) :
    N.gradient g e = 0 := by
  have h := mt (N.mem_edges g e).mpr he
  push Not at h
  simp only [Finsupp.notMem_support_iff] at h
  simp [gradient,h.1,h.2]

def pairing (F : E → ℝ) (g : V →₀ ℝ) : ℝ :=
  ∑ e ∈ N.edges g, F e * N.gradient g e

def UnitFlow (F : E → ℝ) (y : V) : Prop := ∀ g : V →₀ ℝ, N.pairing F g = g y

lemma pairing_finsupp (F : E →₀ ℝ) (g : V →₀ ℝ) :
    N.pairing F g = ∑ e ∈ F.support, F e * N.gradient g e := by
  unfold pairing
  apply sum_eq_of_zero_off
  · intro e he hne
    rw [Finsupp.notMem_support_iff.mp hne,zero_mul]
  · intro e he hne
    rw [N.gradient_zero_of_not_mem g hne,mul_zero]

end Network

variable {V E W T : Type*}

def pullback (ψ : V → W) (hψ : ∀ w, (ψ ⁻¹' {w}).Finite) (g : W →₀ ℝ) : V →₀ ℝ :=
  Finsupp.ofSupportFinite (fun v => g (ψ v)) (by
    apply Set.Finite.subset (Set.Finite.biUnion g.support.finite_toSet (fun w _ => hψ w))
    intro v hv
    simp only [Set.mem_iUnion]
    exact ⟨ψ v,Finsupp.mem_support_iff.mpr hv,rfl⟩)

@[simp] lemma pullback_apply (ψ : V → W) (hψ : ∀ w, (ψ ⁻¹' {w}).Finite)
    (g : W →₀ ℝ) (v : V) : pullback ψ hψ g v = g (ψ v) := rfl

structure Routing (S : Network V E) (N : Network W T) (ψ : V → W) where
  current : E → T →₀ ℝ
  locallyFinite : ∀ t, {e | current e t ≠ 0}.Finite
  telescopes : ∀ e (g : W →₀ ℝ), N.pairing (current e) g = g (ψ (S.src e)) - g (ψ (S.dst e))

namespace Routing
variable {S : Network V E} {N : Network W T} {ψ : V → W} (R : Routing S N ψ)

def sources (s : Finset T) : Finset E := s.biUnion (fun t => (R.locallyFinite t).toFinset)

def push (F : E → ℝ) (t : T) : ℝ :=
  ∑ e ∈ (R.locallyFinite t).toFinset, F e * R.current e t

end Routing
end Heisenberg.RoutedFlow

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_NetworkEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped Classical
open scoped Classical
open Filter Topology
open scoped Classical

namespace Heisenberg.RoutedFlow.Network
variable {V E : Type*} (N : Network V E)

def boundary (e : E) (v : V) : ℝ :=
  (if N.src e = v then 1 else 0) - (if N.dst e = v then 1 else 0)

def divergence (F : E → ℝ) (v : V) : ℝ :=
  ∑ e ∈ (N.incidentFinite v).toFinset, F e * N.boundary e v

lemma pairing_single (e : E) (g : V →₀ ℝ) :
    N.pairing (Finsupp.single e 1) g = N.gradient g e := by
  rw [N.pairing_finsupp]
  simp

lemma pairing_add (F H : E → ℝ) (g : V →₀ ℝ) :
    N.pairing (F+H) g = N.pairing F g + N.pairing H g := by
  simp [pairing,add_mul,Finset.sum_add_distrib]

end Heisenberg.RoutedFlow.Network

namespace Heisenberg.RoutedFlow
variable {V : Type*} (G : SimpleGraph V) (hG : ∀ v, (G.neighborSet v).Finite)

def graphNetwork : Network V G.Dart where
  src e := e.fst
  dst e := e.snd
  incidentFinite v := by
    have hi : Function.Injective (fun e : G.Dart => e.toProd) := by
      intro e f h
      exact SimpleGraph.Dart.ext e f h
    apply (((Set.finite_singleton v).prod (hG v)).union
      ((hG v).prod (Set.finite_singleton v))).preimage hi.injOn |>.subset
    intro e he
    rcases he with h|h
    · exact Or.inl ⟨h,by simpa only [← h,SimpleGraph.mem_neighborSet] using e.adj⟩
    · exact Or.inr ⟨by simpa [← h] using e.adj.symm,h⟩

variable {G}

def pathCurrent {u v : V} : G.Walk u v → G.Dart →₀ ℝ
  | .nil => 0
  | .cons h p => Finsupp.single ⟨(u,_),h⟩ 1 + pathCurrent p

lemma pathCurrent_pairing {u v : V} (p : G.Walk u v) (g : V →₀ ℝ) :
    (graphNetwork G hG).pairing (pathCurrent p) g = g u - g v := by
  induction p with
  | nil => simp [pathCurrent,Network.pairing]
  | @cons u v w h p ih =>
    rw [pathCurrent,Finsupp.coe_add,Network.pairing_add,Network.pairing_single,ih]
    change (g u-g v)+(g v-g w) = g u-g w
    ring

omit hG in
lemma pathCurrent_eq_count {u v : V} (p : G.Walk u v) (e : G.Dart) :
    pathCurrent p e = (p.darts.count e : ℝ) := by
  induction p with
  | nil => simp [pathCurrent]
  | @cons u v w h p ih =>
    simp only [pathCurrent,Finsupp.add_apply,ih,SimpleGraph.Walk.darts_cons,
      List.count_cons]
    by_cases he : (⟨(u,v),h⟩ : G.Dart) = e
    · subst e; simp [add_comm]
    · simp [he,Ne.symm he]

omit hG in
lemma pathCurrent_ne_zero_iff {u v : V} (p : G.Walk u v) (e : G.Dart) :
    pathCurrent p e ≠ 0 ↔ e ∈ p.darts := by
  rw [pathCurrent_eq_count,Nat.cast_ne_zero,← Nat.pos_iff_ne_zero,List.count_pos_iff]

def routingOfPaths {W E : Type*} (S : Network W E) (ψ : W → V)
    (P : ∀ e, G.Walk (ψ (S.src e)) (ψ (S.dst e)))
    (hP : ∀ t, {e | t ∈ (P e).darts}.Finite) : Routing S (graphNetwork G hG) ψ where
  current e := pathCurrent (P e)
  locallyFinite t := by simpa only [pathCurrent_ne_zero_iff] using hP t
  telescopes e g := pathCurrent_pairing hG (P e) g

end Heisenberg.RoutedFlow

open scoped Classical
open Module
namespace Heisenberg.LatticeSum

abbrev Site (d : ℕ) := Fin d → ℤ

def radius {d : ℕ} (x : Site d) : ℕ := Finset.univ.sup (fun j => (x j).natAbs)

def integerLattice (d : ℕ) : Submodule ℤ (Fin d → ℝ) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin d)))

instance instDiscreteTopologySubtypeForallFinRealMemSubmoduleIntIntegerLattice (d : ℕ) : DiscreteTopology (integerLattice d) := by
  unfold integerLattice
  infer_instance

instance instIsZLatticeRealForallFinIntegerLattice (d : ℕ) : IsZLattice ℝ (integerLattice d) := by
  unfold integerLattice
  infer_instance

def embed {d : ℕ} (x : Site d) : integerLattice d :=
  ⟨fun j => (x j : ℝ), by
    apply ((Pi.basisFun ℝ (Fin d)).mem_span_iff_repr_mem ℤ _).mpr
    intro j
    exact ⟨x j, by simp⟩⟩

end Heisenberg.LatticeSum

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_LatticeFlows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped Classical
open scoped Classical
open Filter Topology
open scoped Classical
open scoped Classical
open Module

open scoped Classical

namespace Heisenberg.Flow

abbrev Orthant (k : ℕ) := Fin (k + 1) → ℕ

def level {k : ℕ} (n : Orthant k) : ℕ := ∑ j, n j

def layerMass (k N : ℕ) : ℝ := ((N + k).choose k : ℝ)⁻¹

def orthantFlow {k : ℕ} (n : Orthant k) (j : Fin (k + 1)) : ℝ :=
  layerMass k (level n) * (n j + 1) / (level n + k + 1)

def predecessor {k : ℕ} (n : Orthant k) (j : Fin (k + 1)) : Orthant k :=
  Function.update n j (n j - 1)

abbrev ZSite (k : ℕ) := Fin (k + 1) → ℤ

def PositiveOrthant {k : ℕ} (x : ZSite k) : Prop := ∀ j, 0 ≤ x j

def natPart {k : ℕ} (x : ZSite k) : Orthant k := fun j => (x j).toNat

def down {k : ℕ} (x : ZSite k) (j : Fin (k + 1)) : ZSite k :=
  Function.update x j (x j - 1)

def latticeFlow {k : ℕ} (x : ZSite k) (j : Fin (k + 1)) : ℝ :=
  if PositiveOrthant x then orthantFlow (natPart x) j else 0

def radius {k : ℕ} (x : ZSite k) : ℕ := Finset.univ.sup (fun j => (x j).natAbs)

end Heisenberg.Flow

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_FlowRouting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped Classical
open scoped Classical
open Filter Topology
open scoped Classical
open scoped Classical
open Module
open scoped Classical

namespace Heisenberg.Flow

open RoutedFlow
variable {k : ℕ}

def next (x : ZSite k) (j : Fin (k+1)) : ZSite k := Function.update x j (x j+1)

@[simp] lemma next_down (x : ZSite k) (j : Fin (k+1)) : next (down x j) j = x := by
  ext i
  by_cases hi : i=j <;> simp [next,down,hi]

@[simp] lemma down_next (x : ZSite k) (j : Fin (k+1)) : down (next x j) j = x := by
  ext i
  by_cases hi : i=j <;> simp [next,down,hi]

def latticeNetwork (k : ℕ) : Network (ZSite k) (ZSite k × Fin (k+1)) where
  src e := e.1
  dst e := next e.1 e.2
  incidentFinite v := by
    apply ((Set.finite_range (fun j : Fin (k+1) => (v,j))).union
      (Set.finite_range (fun j : Fin (k+1) => (down v j,j)))).subset
    rintro ⟨x,j⟩ (h|h)
    · change x = v at h
      exact Or.inl ⟨j,by rw [h]⟩
    · change next x j = v at h
      exact Or.inr ⟨j,by dsimp; rw [← h,down_next]⟩

end Heisenberg.Flow

namespace Heisenberg.Geometry
lemma lattice_neighbor_finite {d : ℕ} (U : Set (Site d)) (v : Site d) :
    ((latticeGraph U).neighborSet v).Finite := by
  apply (ballFinset d 1 v).finite_toSet.subset
  intro z hz
  apply (mem_ballFinset ..).mpr
  apply (dist_le_iff_mem_ball v z).mp
  simpa only [Nat.cast_one] using step_dist_le_one hz.1
end Heisenberg.Geometry

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_FlowCongestion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped Classical
open scoped Classical
open Filter Topology
open scoped Classical
open scoped Classical
open Module
open scoped Classical

namespace Heisenberg.Flow

open Heisenberg.Geometry Heisenberg.LatticeSum
variable {k : ℕ}

def edgeCode {Z : Set (ZSite k)} (e : (latticeGraph Zᶜ).Dart) :
    ↥(ballFinset (k+1) 1 0) × ZSite k :=
  (⟨e.snd-e.fst, by
    apply (mem_ballFinset ..).mpr
    apply (dist_le_iff_mem_ball ..).mp
    simpa only [Nat.cast_one,dist_eq_norm,zero_sub,norm_neg] using step_dist_le_one (step_symm e.adj.1)⟩,e.fst)

end Heisenberg.Flow

open scoped Classical BigOperators

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_RegularKernels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped Classical
open scoped Classical
open Filter Topology
open scoped Classical
open scoped Classical
open Module
open scoped Classical
open scoped Classical BigOperators
open scoped Classical BigOperators

namespace Heisenberg.SlotMaximum
variable {X I : Type*}

def value (s : Finset I) (v : I → ℝ) : ℝ :=
  if h : s.Nonempty then (s.image v).max' (h.image v) else 0

lemma attained {s : Finset I} (hs : s.Nonempty) (v : I → ℝ) :
    ∃ i ∈ s, value s v = v i := by
  rw [value,dite_eq_left hs]
  obtain ⟨i,hi,he⟩ := Finset.mem_image.mp (Finset.max'_mem (s.image v) (hs.image v))
  exact ⟨i,hi,he.symm⟩

lemma zero_of_zero (s : Finset I) (v : I → ℝ) (hv : ∀ i ∈ s,v i=0) :
    value s v=0 := by
  by_cases hs : s.Nonempty
  · obtain ⟨i,hi,he⟩ := attained hs v
    rw [he,hv i hi]
  · simp [value,hs]

def test (s : X → Finset I) (v : X → I → ℝ) (F : Finset X)
    (hv : ∀ x,x ∉ F → ∀ i ∈ s x,v x i=0) : X →₀ ℝ :=
  Finsupp.ofSupportFinite (fun x => value (s x) (v x)) (by
    apply F.finite_toSet.subset
    intro x hx
    by_contra hn
    exact hx (zero_of_zero (s x) (v x) (hv x hn)))

@[simp] lemma test_apply (s : X → Finset I) (v : X → I → ℝ) (F : Finset X)
    (hv : ∀ x,x ∉ F → ∀ i ∈ s x,v x i=0) (x : X) :
    test s v F hv x=value (s x) (v x) := rfl

end Heisenberg.SlotMaximum

namespace Heisenberg.Flow

open Heisenberg.Geometry Heisenberg.LatticeRegular Heisenberg.RoutedFlow Heisenberg.SlotMaximum
variable {k : ℕ}

def goodMass {I V : Type*} (K : V → I → ℝ) (x : I → ZSite k) (y : V → ZSite k)
    (Z : Set (ZSite k)) (R M : ℕ) (i : I) (j : V) : ℝ :=
  if Regular Z (x i) R M (1/(100*(k+1:ℝ))) ∧ dist (y j) (x i)≤R then K j i else 0

end Heisenberg.Flow

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_RoutedDissipation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped Classical
open scoped Classical
open Filter Topology
open scoped Classical
open scoped Classical
open Module
open scoped Classical
open scoped Classical BigOperators
open scoped Classical BigOperators

namespace Heisenberg.Flow
open Heisenberg.Geometry Heisenberg.LatticeRegular Heisenberg.RoutedFlow Heisenberg.SlotMaximum
variable {X B : Type*}

def frameEnergy (R : X → X → Prop) (Λ : Finset X) (s : X → Finset B)
    (v : X → B → ℝ) : ℝ :=
  ∑ x∈Λ,∑ y∈Λ,if R x y then ∑ a∈s x,∑ b∈s y,(v x a-v y b)^2 else 0

end Heisenberg.Flow

namespace Heisenberg.Exposure
variable {V : Type*} [Fintype V]
def quietEnergy (H : Set V) (a b : ℕ → V) (n : ℕ) (v : EuclideanSpace ℝ V) : ℝ :=
  ∑ i ∈ Finset.range n,if a i ∈ H ∧ b i ∈ H then (v.ofLp (a i)-v.ofLp (b i))^2 else 0
end Heisenberg.Exposure

namespace Heisenberg.SpatialFrame

section
variable {X B : Type*} [Fintype B]
abbrev Slots (Λ : Finset X) := Λ × B

def available (Λ : Finset X) (H : Set (Slots (B:=B) Λ)) (x : X) : Finset B :=
  if hx : x∈Λ then Finset.univ.filter (fun a => (⟨x,hx⟩,a)∈H) else Finset.univ

def extend (Λ : Finset X) (v : Slots (B:=B) Λ → ℝ) (x : X) (a : B) : ℝ :=
  if hx : x∈Λ then v (⟨x,hx⟩,a) else 0

abbrev Edges (R : X → X → Prop) (Λ : Finset X) :=
  {e : Slots (B:=B) Λ × Slots (B:=B) Λ // R e.1.1 e.2.1}

end

variable {X B : Type*} [Fintype B]
def blocked (Λ : Finset X) (H : Set (Slots (B:=B) Λ)) : Set X :=
  {x | ∃ h : x∈Λ,∀ a : B,(⟨x,h⟩,a)∉H}

end Heisenberg.SpatialFrame

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_WeightedLeakage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped Classical
open scoped Classical
open Filter Topology
open scoped Classical
open scoped Classical
open Module
open scoped Classical
open scoped Classical BigOperators
open scoped Classical BigOperators

open scoped BigOperators Classical
namespace Heisenberg.FiniteLeakage

section

def triangle {n : ℕ} (i : Fin n) : ℝ := 2*(((i:ℕ):ℝ)+1)/((n:ℝ)*((n:ℝ)+1))

open scoped RealInnerProductSpace

end

open scoped RealInnerProductSpace

end Heisenberg.FiniteLeakage

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_RoundEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter Topology
open Module
open scoped Classical
open scoped Classical BigOperators
open scoped BigOperators Classical

open scoped BigOperators Classical RealInnerProductSpace
namespace Heisenberg.MeshPair
open Heisenberg.MatrixContraction
variable {V : Type*} [Fintype V] [DecidableEq V]

@[simp] lemma euclideanMap_one : euclideanMap (1 : Matrix V V ℝ) = LinearMap.id := by
  ext v i
  simp [euclideanMap_apply]

def prefixMatrix (K : ℕ → Matrix V V ℝ) : ℕ → Matrix V V ℝ
  | 0 => 1
  | n+1 => K n*prefixMatrix K n

end Heisenberg.MeshPair

open scoped BigOperators Classical RealInnerProductSpace
open Filter Topology
open scoped BigOperators Classical RealInnerProductSpace
open Filter Topology

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_CyclicEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Classical RealInnerProductSpace
namespace Heisenberg.MeshPair
variable {V : Type*} [Fintype V] [DecidableEq V]

def indicatorVector (J : Finset V) : EuclideanSpace ℝ V :=
  WithLp.toLp 2 (fun j=>if j∈J then (1:ℝ) else 0)

end Heisenberg.MeshPair

open Filter Topology
open scoped RealInnerProductSpace Classical

open scoped Classical
open Filter
namespace Heisenberg.Serial

section
open Matrix Heisenberg.MeshPair
variable {V B : Type*} [Fintype V] [DecidableEq V] [Fintype B]

def product : (n : ℕ) → (Fin n → Matrix V V ℝ) → Matrix V V ℝ
  | 0,_ => 1
  | n+1,K => product n (fun i => K i.succ)*K 0

def follow : (n : ℕ) → (Fin n → Equiv.Perm V) → V → V
  | 0,_,v => v
  | n+1,σ,v => follow n (fun i => σ i.succ) (σ 0 v)

def survives : (n : ℕ) → (Fin (n+1) → Set V) → (Fin n → Equiv.Perm V) → V → Prop
  | 0,D,_,v => v∈D 0
  | n+1,D,σ,v => v∈D 0 ∧ survives n (fun i => D i.succ) (fun i => σ i.succ) (σ 0 v)

def projection (D : Set V) : Matrix V V ℝ := killedBetween D D 1

def walkKernel (n : ℕ) (D : Fin (n+1) → Set V) (σ : Fin n → Equiv.Perm V) : Matrix V V ℝ :=
  product n (fun i => killedBetween (D i.castSucc) (D i.succ) (σ i))*projection (D 0)

end

open Matrix Heisenberg.Hitting
variable {V : Type*} [Fintype V] [DecidableEq V]

def cyclicKernel (n : ℕ) (K : Fin (n+1) → Matrix V V ℝ) :
    Matrix (Fin (n+1) × V) (Fin (n+1) × V) ℝ :=
  fun i j => if i.1=finRotate (n+1) j.1 then K j.1 i.2 j.2 else 0

end Heisenberg.Serial

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_HistoryMarginals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter Topology
open scoped RealInnerProductSpace Classical
open scoped Classical
open Filter

open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped BigOperators Classical
namespace Heisenberg.Clocks

def WeakTimes (n r : ℕ) := {f : Fin r → Fin n // Monotone f}
instance instFintypeWeakTimes (n r : ℕ) : Fintype (WeakTimes n r) := inferInstanceAs (Fintype {f : Fin r → Fin n // Monotone f})

def shifted {n r : ℕ} (f : WeakTimes n r) (i : Fin r) : Fin (n+r) :=
  ⟨(f.val i).val+i.val, by have h := (f.val i).isLt; have hi := i.isLt; omega⟩

def timeSet {n r : ℕ} (f : WeakTimes n r) : Finset (Fin (n+r)) :=
  Finset.univ.image (shifted f)

variable {X E : Type*}

def edgeWords (choices : X → Finset E) (next : X → E → X) : ℕ → X → Finset (List E)
  | 0,_ => {[]}
  | r+1,x => (choices x).biUnion (fun e => (edgeWords choices next r (next x e)).image (List.cons e))

def Follows (choices : X → Finset E) (next : X → E → X) : X → List E → Prop
  | _,[] => True
  | x,e::l => e ∈ choices x ∧ Follows choices next (next x e) l

end Heisenberg.Clocks

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_ClockWitnesses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter Topology
open scoped RealInnerProductSpace Classical
open scoped Classical
open Filter
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical

namespace Heisenberg.Clocks

section
variable {X E I : Type*} [Fintype E]

def weakTimes (r N : ℕ) : Finset (Fin r → Fin N) := Finset.univ.filter Monotone

def functionWords (choices : X → Finset E) (next : X → E → X) (r : ℕ) (x : X) :
    Finset (Fin r → E) := Finset.univ.filter (fun w => List.ofFn w ∈ edgeWords choices next r x)

def witnesses (choices : X → Finset E) (next : X → E → X) (r N : ℕ) (x : X)
    (index : Fin N → E → Bool → I) :
    Finset ((Fin r → Fin N) × (Fin r → E) × (Fin r → Bool)) :=
  ((weakTimes r N).product ((functionWords choices next r x).product Finset.univ)).filter
    (fun q => Function.Injective (fun k => index (q.1 k) (q.2.1 k) (q.2.2 k)))

def witnessMarks {r N : ℕ} (index : Fin N → E → Bool → I)
    (q : (Fin r → Fin N) × (Fin r → E) × (Fin r → Bool)) : Finset I :=
      Finset.univ.image (fun k => index (q.1 k) (q.2.1 k) (q.2.2 k))

end

variable {X E I : Type*}

def moveList (x : ℕ → X) (m : ℕ) : ℕ → List ℕ
  | 0 => []
  | k+1 => if x (m+1)=x m then moveList x (m+1) k
      else m :: moveList x (m+1) k

end Heisenberg.Clocks

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_ClockInsertions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter Topology
open scoped RealInnerProductSpace Classical
open scoped Classical
open Filter
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical

namespace Heisenberg.Bernoulli
variable {I : Type*} [Fintype I]

def doubleRates (p : I → ℝ) : I ⊕ I → ℝ := Sum.elim p p

def original (c : I ⊕ I → Bool) : I → Bool := c ∘ Sum.inl

def fresh (c : I ⊕ I → Bool) : I → Bool := c ∘ Sum.inr

end Heisenberg.Bernoulli

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_SpatialClocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter Topology
open scoped RealInnerProductSpace Classical
open scoped Classical
open Filter
open scoped BigOperators Classical

namespace Heisenberg.Clocks
open Heisenberg.Exposure Heisenberg.Bernoulli
variable {V X E I : Type*} [PseudoMetricSpace X] [Fintype E] [Fintype I]

def mixedCoins (M : (I → Bool) → I → Prop) (c : I ⊕ I → Bool) (r : ℕ → I) : ℕ → Bool :=
  fun j=>if M (original c) (r j) then original c (r j) else fresh c (r j)

def mixedSource (M : (I → Bool) → I → Prop) (c : I ⊕ I → Bool) (r : ℕ → I) : ℕ → Bool :=
  fun j=>decide (M (original c) (r j))

end Heisenberg.Clocks

open scoped BigOperators Classical
namespace Heisenberg.Serial

section
open Heisenberg.Exposure Heisenberg.Bernoulli Heisenberg.Clocks Heisenberg.MeshPair
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]

def sampledPrefix (τ : ℕ → Equiv.Perm V) (p : I → ℝ) (r : ℕ → I)
    (M : (I → Bool) → I → Prop) (n : ℕ) (D : (I → Bool) → Fin (n+1) → Set V)
    (base : I → Bool) : Matrix V V ℝ :=
  product n (fun i=>∑ b : Bool,(if b then p (r i) else 1-p (r i)) •
    killedBetween (D base i.castSucc) (D base i.succ)
      (if (if M base (r i) then base (r i) else b) then τ i else 1)) * projection (D base 0)

end

open Heisenberg.Exposure Heisenberg.Bernoulli Heisenberg.Clocks Heisenberg.MeshPair

end Heisenberg.Serial

open scoped Classical

open scoped Classical BigOperators
namespace Heisenberg.SparseWitness

variable (V : Type*)
def Tree : ℕ → Type _
  | 0 => V
  | n+1 => Tree n × Tree n
variable {V}

def root : {n : ℕ} → Tree V n → V
  | 0, t => t
  | _+1, t => root t.1

def leaves [DecidableEq V] : {n : ℕ} → Tree V n → Finset V
  | 0, t => {t}
  | _+1, t => leaves t.1 ∪ leaves t.2

variable [PseudoMetricSpace V]

def Admissible (h : ℕ → ℝ) : {n : ℕ} → Tree V n → Prop
  | 0, _ => True
  | n+1, t => Admissible h t.1 ∧ Admissible h t.2 ∧
      dist (root t.1) (root t.2) ≤ h (n+1) + 8 ∧
      ∀ a ∈ leaves t.1, ∀ b ∈ leaves t.2, h (n+1)/4 ≤ dist a b

def Sparse (α L : ℝ) (F : Finset V) : Prop :=
  ∀ z r, 0 ≤ r → (((F.filter (fun a => dist a z ≤ r)).card : ℕ) : ℝ) ≤ L*(1+r)^α

end Heisenberg.SparseWitness

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_SparseCrossings
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped Classical
open scoped Classical BigOperators

namespace Heisenberg.SparseWitness

section
variable {V : Type*}

def candidates (B : ℕ → V → Finset V) : (n : ℕ) → V → Finset (Tree V n)
  | 0, z => {z}
  | n+1, z => (B (n+1) z).biUnion (fun y => (candidates B n z).product (candidates B n y))

variable [PseudoMetricSpace V]

def assignmentBound (a c : ℕ) : ℕ → ℕ
  | 0 => 1
  | n+1 => (a*c^(n+1))*assignmentBound a c n^2

end

variable {V Ω : Type*} [PseudoMetricSpace V] [Fintype Ω]

def Crosses (Z : Set V) (z : V) (r : ℝ) : Prop :=
  ∃ (p : ℕ → V) (m : ℕ), p 0 = z ∧ (∀ i ≤ m, p i ∈ Z) ∧
    (∀ i < m, dist (p i) (p (i+1)) ≤ 8) ∧ r ≤ dist (p 0) (p m)

end Heisenberg.SparseWitness

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_LayerRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped Classical BigOperators
open Module
open scoped BigOperators

open scoped Classical

open scoped BigOperators Classical
namespace Heisenberg.Exposure

section
open Heisenberg.Cycle Heisenberg.LayeredExchange
variable {T V : Type*} [Fintype T] [Fintype V]

def layerHoles (s : Equiv.Perm T) (τ : T → Equiv.Perm V)
    (P : Set (T × V)) (b : T → Bool) (t : T) : Set V :=
  {v | (t,v) ∉ MissingSet (layerHistory s τ b) P}

def layerBlocked {X : Type*} (loc : V → X) (s : Equiv.Perm T)
    (τ : T → Equiv.Perm V) (P : Set (T × V)) (b : T → Bool) (t : T) : Set X :=
  {x | (∃ v,loc v=x) ∧ ∀ v,loc v=x → v ∉ layerHoles s τ P b t}

def localGrowth {X Y : Type*} [PseudoMetricSpace X] (loc : Y → X)
    (α L : ℝ) (U : Finset Y) : Prop :=
  ∀ (x : X) (h : ℝ), 0 ≤ h →
    ((U.filter (fun v => dist (loc v) x ≤ h)).card : ℝ) ≤ L*(1+h)^α

end

open Heisenberg.Geometry Heisenberg.SparseWitness Heisenberg.LatticeRegular

end Heisenberg.Exposure

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_HoleReturns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical
open Matrix
noncomputable section
open scoped Classical
open Matrix
noncomputable section
open scoped Classical
open Matrix
noncomputable section
open scoped Classical
noncomputable section
open scoped BigOperators Classical
noncomputable section
open scoped Classical

noncomputable section
open scoped Classical
open Filter

noncomputable section
open scoped Classical

noncomputable section
open scoped Classical

namespace Heisenberg.Exposure
open Heisenberg.Return Heisenberg.Hitting Heisenberg.Cycle
variable {V Ω : Type*} [Fintype V] [Fintype Ω]
variable [DecidableEq V]

def holePinEquiv (A P : Set V) (hP : Disjoint A P) :
    {x : {z : V // z∉A} // x.val∈P} ≃ P where
  toFun j := ⟨j.val.val,j.property⟩
  invFun j := ⟨⟨j.val,fun h => Set.disjoint_left.mp hP h j.property⟩,j.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def returnCount (σ : Equiv.Perm V) (P : Set V) (T : Finset P) : ℝ :=
  ∑ j∈T, if nextPermutation σ P j∈T then 1 else 0

end Heisenberg.Exposure

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
-- module Solutions.OAIW2_Heis.Heisenberg_CutContractions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Filter Topology
open scoped RealInnerProductSpace Classical

noncomputable section
open scoped Classical BigOperators

namespace Heisenberg.Exposure
open Heisenberg.Serial Heisenberg.Hitting Heisenberg.MeshPair Heisenberg.Cycle
variable {V : Type*} [Fintype V] [DecidableEq V]

def cutFactors (n : ℕ) (a b : Fin (n+1) → V) (p : Fin (n+1) → ℝ)
    (P : Set (Fin (n+1)×V)) (D : (Fin (n+1) → Bool) → Fin (n+1) → Set V)
    (base : Fin (n+1) → Bool) (i : Fin (n+1)) : Matrix V V ℝ :=
  residualBetween (D base i) (D base (finRotate (n+1) i))
    (layerRevealed (fun j => Equiv.swap (a j) (b j))
      (MissingSet (layerHistory (finRotate (n+1)) (fun j => Equiv.swap (a j) (b j)) base) P) i)
    (base i) (a i) (b i) (p i)

end Heisenberg.Exposure

end
end

noncomputable section
open scoped Classical Fin.NatCast
namespace Heisenberg.Schedule
variable {m Q : ℕ} [NeZero m]

def run (t : Fin m) (j : ℕ) : Fin m := t+(↑j:Fin m)

@[simp] lemma run_zero (t : Fin m) : run t 0=t := by simp [run]

def warm (t : Fin m) (Q : ℕ) : ℕ := Q-t.val%Q
def cut (t : Fin m) (Q : ℕ) (i : ℕ) : ℕ := warm t Q+i*Q

def round (t : Fin m) (Q j : ℕ) : ℕ := (t.val%Q+j)/Q

def clock (t : Fin m) (Q g l : ℕ) : Fin m :=
  ⟨((t.val/Q+g)*Q+l)%m,Nat.mod_lt _ (NeZero.pos m)⟩

end Heisenberg.Schedule
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_ScheduledResiduals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Classical
namespace Heisenberg.SpatialFrame
open Heisenberg.Geometry
variable {d : ℕ} {B : Type} [Fintype B]

def neighbors (x : Site d) : Finset (Site d) :=
  Finset.univ.image fun j : Fin d × Bool=>Function.update x j.1 (x j.1+if j.2 then 1 else -1)

def choices (Λ : Finset (Site d)) (x : Site d) : Finset (Edges (B:=B) Step Λ) :=
  Finset.univ.filter fun e=>e.val.1.1.val=x ∨ e.val.2.1.val=x

def next (x : Site d) {Λ : Finset (Site d)} (e : Edges (B:=B) Step Λ) : Site d :=
  if x=e.val.1.1.val then e.val.2.1.val else e.val.1.1.val

end Heisenberg.SpatialFrame
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_PeriodicLeakage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Classical BigOperators Fin.NatCast

noncomputable section
open scoped Classical BigOperators Fin.NatCast RealInnerProductSpace
open Filter Topology
namespace Heisenberg.Flow
@[reducible] local instance periodicDecEq (α : Type*) : DecidableEq α := Classical.decEq α
open Heisenberg.Geometry Heisenberg.Schedule Heisenberg.SpatialFrame Heisenberg.MeshPair Heisenberg.Exposure Heisenberg.LatticeRegular

end Heisenberg.Flow

end
end

noncomputable section
open scoped Classical BigOperators Fin.NatCast
open Matrix
namespace Heisenberg.Schedule
variable {m : ℕ} [NeZero m]
@[simp] lemma run_period (t : Fin m) : run t m=t := by simp [run]
end Heisenberg.Schedule
namespace Heisenberg.Serial
open Heisenberg.Schedule Heisenberg.Hitting
variable {V : Type} [Fintype V] [DecidableEq V]

def targetsAt (n : ℕ) (t : Fin (n+1)) (J : Finset V) : Finset (Fin (n+1)×V) :=
  J.image (fun j=>(t,j))
omit [Fintype V] in
@[simp] lemma mem_targetsAt (n : ℕ) (t u : Fin (n+1)) (J : Finset V) (j : V) :
    (u,j)∈targetsAt n t J ↔ u=t ∧ j∈J := by simp [targetsAt,and_comm,eq_comm]

end Heisenberg.Serial

end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_PolynomialLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Classical Fin.NatCast
namespace Heisenberg.Schedule
variable {m Q q : ℕ} [NeZero m] [NeZero Q]

def phaseHom (h : Q∣m) : Fin m →+ Fin Q where
  toFun j := (j.val : Fin Q)
  map_zero' := by simp
  map_add' i j := by
    apply Fin.ext
    simp only [Fin.val_natCast,Fin.val_add]
    rw [Nat.mod_mod_of_dvd _ h,Nat.add_mod]

def reverseIndex (q : ℕ) : Equiv.Perm (Fin m) where
  toFun j := (q:Fin m)-j
  invFun j := (q:Fin m)-j
  left_inv j := sub_sub_cancel _ j
  right_inv j := sub_sub_cancel _ j

end Heisenberg.Schedule

end

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_StablePolynomials
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical Topology
open Set Filter Metric

namespace Heisenberg.Pin

def Upper {σ : Type*} : Set (σ → ℂ) := {z | ∀ j, 0 < (z j).im}

def Stable {σ : Type*} (p : MvPolynomial σ ℂ) : Prop :=
  ∀ z ∈ Upper, MvPolynomial.eval z p ≠ 0

def linePolynomial {σ : Type*} (p : MvPolynomial σ ℂ) (z v : σ → ℂ) : Polynomial ℂ :=
  MvPolynomial.eval₂ Polynomial.C (fun j => Polynomial.C (z j) +
    Polynomial.X * Polynomial.C (v j)) p

def variablePolynomial {σ : Type*} (p : MvPolynomial σ ℂ) (z : σ → ℂ) (j : σ) : Polynomial ℂ :=
  MvPolynomial.eval₂ Polynomial.C (fun k => if k = j then Polynomial.X
    else Polynomial.C (z k)) p

end Heisenberg.Pin
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_StableSections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical Topology
open Set Filter Metric

open scoped ComplexConjugate
namespace Heisenberg.Pin

section

def biaffine (a b c e z w : ℂ) : ℂ := a + b * z + c * w + e * z * w

def StableSection (a b c e : ℂ) : Prop :=
  ∀ z w : ℂ, 0 < z.im → 0 < w.im → biaffine a b c e z w ≠ 0

def rootCriterion (a b c e z : ℂ) : ℝ :=
  ((a + b * z) * conj (c + e * z)).im

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def subsetMonomial (A : Finset σ) : MvPolynomial σ ℂ := ∏ i ∈ A, MvPolynomial.X i

omit [Fintype σ] [DecidableEq σ] in
@[simp] lemma subsetMonomial_empty : subsetMonomial (∅ : Finset σ) = 1 := by
  simp [subsetMonomial]

def presence (μ : Finset σ → ℝ) (B : Finset σ) : ℝ :=
  ∑ A : Finset σ, if B ⊆ A then μ A else 0

def presencePolynomial (μ : Finset σ → ℝ) (B : Finset σ) : MvPolynomial σ ℂ :=
  ∑ A : Finset σ, if B ⊆ A then MvPolynomial.C (μ A : ℂ) * subsetMonomial (A \ B) else 0

end

def boundarySection {σ τ : Type*} (p : MvPolynomial σ ℂ) (f : σ → Option τ)
    (a : σ → ℂ) : MvPolynomial τ ℂ :=
  MvPolynomial.eval₂ MvPolynomial.C
    (fun j => (f j).elim (MvPolynomial.C (a j)) MvPolynomial.X) p

end Heisenberg.Pin
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_PinSymmetrization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical Topology
open Set Filter Metric
open scoped ComplexConjugate

namespace Heisenberg.Pin

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def pairAssignment (i j : σ) (z w : ℂ) (k : σ) : ℂ :=
  if k = i then z else if k = j then w else 1

end Heisenberg.Pin

namespace Heisenberg.Pin

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def MultiAffine (p : MvPolynomial σ ℂ) : Prop := ∀ i, p.degreeOf i ≤ 1

def symmetrize (p : MvPolynomial σ ℂ) (i j : σ) (u : ℝ) : MvPolynomial σ ℂ :=
  MvPolynomial.C (1 - (u : ℂ)) * p +
    MvPolynomial.C (u : ℂ) * MvPolynomial.rename (Equiv.swap i j) p

end Heisenberg.Pin
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_PermutationSymbols
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical Topology
open Set Filter Metric
open scoped ComplexConjugate

namespace Heisenberg.Pin

variable {V : Type*} [Fintype V] [DecidableEq V]

def permutationSymbol (π : Equiv.Perm V) : MvPolynomial (V ⊕ V) ℂ :=
  ∏ i, (MvPolynomial.X (Sum.inl i) + MvPolynomial.X (Sum.inr (π i)))

end Heisenberg.Pin

namespace Heisenberg.Pin

variable {V Ω : Type*} [Fintype V] [DecidableEq V] [Fintype Ω]

def lawSymbol (μ : Ω → ℝ) (π : Ω → Equiv.Perm V) : MvPolynomial (V ⊕ V) ℂ :=
  ∑ ω, MvPolynomial.C (μ ω : ℂ) * permutationSymbol (π ω)

end Heisenberg.Pin

namespace Heisenberg.Pin
variable {V Ω : Type*} [Fintype V] [DecidableEq V] [Fintype Ω]

def partialSymbol (π : V → V) (U : Finset V) : MvPolynomial (V ⊕ V) ℂ :=
  ∏ i ∈ U, (MvPolynomial.X (Sum.inl i) + MvPolynomial.X (Sum.inr (π i)))

def partialLawSymbol (μ : Ω → ℝ) (π : Ω → V → V) (U : Finset V) :
    MvPolynomial (V ⊕ V) ℂ := ∑ ω, MvPolynomial.C (μ ω : ℂ) * partialSymbol (π ω) U

def outputSymbol (μ : Ω → ℝ) (π : Ω → V → V) (T : Finset V) : MvPolynomial V ℂ :=
  ∑ ω, MvPolynomial.C (μ ω : ℂ) * ∏ i ∈ T, MvPolynomial.X (π ω i)

end Heisenberg.Pin
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_PinSplicing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped Classical Topology
open Set Filter Metric
open scoped ComplexConjugate

open scoped Classical
namespace Heisenberg.Pin

section

variable {V : Type*} [Fintype V] [DecidableEq V]

def spliceVariables : Option V ⊕ Option V → Option (V ⊕ V)
  | Sum.inl none => none
  | Sum.inr none => none
  | Sum.inl (some i) => some (Sum.inl i)
  | Sum.inr (some i) => some (Sum.inr i)

def eraseNone {σ : Type*} : MvPolynomial (Option σ) ℂ →ₐ[ℂ] MvPolynomial σ ℂ :=
  MvPolynomial.aeval (fun j => j.elim 0 MvPolynomial.X)

def splice (p : MvPolynomial (Option V ⊕ Option V) ℂ) : MvPolynomial (V ⊕ V) ℂ :=
  eraseNone (MvPolynomial.pderiv none (MvPolynomial.rename spliceVariables p))

end

variable {V Ω : Type*} [Fintype V] [DecidableEq V] [Fintype Ω]

def spliceWeight (π : Equiv.Perm (Option V)) : ℝ := if π none = none then 2 else 1

end Heisenberg.Pin

namespace Heisenberg.Cycle

open Equiv

variable {V : Type*}

def projection (π : Perm (Option V)) : Option V → Option (Classes (removeNone π))
  | some i => some (classOf (removeNone π) i)
  | none => (π none).map (classOf (removeNone π))

lemma projection_apply (π : Perm (Option V)) (i : Option V) :
    projection π (π i) = projection π i := by
  cases i with
  | none =>
    cases h : π none <;> simp [projection, h]
  | some i =>
    cases h : π (some i) with
    | none =>
      have he := removeNone_none π h
      change (π none).map (classOf (removeNone π)) = _
      rw [← he]
      simp [projection]
    | some j =>
      have he := removeNone_some π ⟨j, h⟩
      have he' : removeNone π i = j := Option.some.inj (he.trans h)
      simp only [projection]
      rw [← he', classOf_apply]

lemma projection_pow (π : Perm (Option V)) (n : ℕ) (i : Option V) :
    projection π ((π ^ n) i) = projection π i := by
  induction n with
  | zero => rfl
  | succ n hn =>
    rw [pow_succ', Perm.mul_apply, projection_apply, hn]

variable [Fintype V]

lemma sameCycle_removeNone_iff (π : Perm (Option V)) (i j : V) :
    Perm.SameCycle (removeNone π) i j ↔ π.SameCycle (some i) (some j) := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    have hstep (k : V) : π.SameCycle (some k) (some (removeNone π k)) := by
      cases he : π (some k) with
      | none =>
        rw [removeNone_none π he]
        have h1 : π.SameCycle (some k) none := by
          rw [← he]
          exact (Perm.SameCycle.refl π _).apply_right
        exact h1.apply_right
      | some l =>
        rw [removeNone_some π ⟨l, he⟩]
        exact (Perm.SameCycle.refl π _).apply_right
    have hall (m : ℕ) : π.SameCycle (some i) (some ((removeNone π ^ m) i)) := by
      induction m with
      | zero => exact Perm.SameCycle.refl _ _
      | succ m hm =>
        rw [pow_succ', Perm.mul_apply]
        exact hm.trans (hstep _)
    simpa [hn] using hall n
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    have he := projection_pow π n (some i)
    rw [hn] at he
    exact (classOf_eq_iff _ _ _).mp (Option.some.inj he).symm

def classInclusion (π : Perm (Option V)) : Classes (removeNone π) → Classes π :=
  Quotient.map some (fun i j h => (sameCycle_removeNone_iff π i j).mp h)

@[simp] lemma classInclusion_mk (π : Perm (Option V)) (i : V) :
    classInclusion π (classOf (removeNone π) i) = classOf π (some i) := rfl

lemma classInclusion_injective (π : Perm (Option V)) :
    Function.Injective (classInclusion π) := by
  intro a b h
  induction a using Quotient.inductionOn with | _ i =>
    induction b using Quotient.inductionOn with | _ j =>
      exact (classOf_eq_iff _ _ _).mpr
        ((sameCycle_removeNone_iff π i j).mpr ((classOf_eq_iff _ _ _).mp h))

lemma missingInclusion_condition (π : Perm (Option V)) (P : Set V)
    (c : Classes (removeNone π)) :
    (∀ i ∈ some '' P, classInclusion π c ≠ classOf π i) ↔
      ∀ i ∈ P, c ≠ classOf (removeNone π) i := by
  constructor
  · intro h i hi he
    apply h (some i) ⟨i, hi, rfl⟩
    rw [he, classInclusion_mk]
  · rintro h _ ⟨i, hi, rfl⟩ he
    exact h i hi (classInclusion_injective π he)

def missingInclusion (π : Perm (Option V)) (P : Set V) :
    MissingClasses (removeNone π) P → MissingClasses π (some '' P) :=
  fun c => ⟨classInclusion π c.val, (missingInclusion_condition π P c.val).mpr c.property⟩

omit [Fintype V] in
lemma none_missing (π : Perm (Option V)) (P : Set V) (hf : π none = none) :
    ∀ i ∈ some '' P, classOf π none ≠ classOf π i := by
  rintro _ ⟨i, _, rfl⟩ he
  have hs := (classOf_eq_iff π none (some i)).mp he
  exact Option.some_ne_none i (hs.eq_of_left hf).symm

def missingOption (π : Perm (Option V)) (P : Set V) (hf : π none = none) :
    Option (MissingClasses (removeNone π) P) → MissingClasses π (some '' P)
  | none => ⟨classOf π none, none_missing π P hf⟩
  | some c => missingInclusion π P c

end Heisenberg.Cycle

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_StablePinLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical Topology
open Set Filter Metric
open scoped ComplexConjugate
noncomputable section
open scoped Classical

noncomputable section
open scoped Classical

noncomputable section
open scoped Classical
namespace Heisenberg.Transport
open Equiv
open Heisenberg.Cycle Heisenberg.Return
variable {V W : Type*} [Fintype V] [Fintype W]

omit [Fintype V] [Fintype W] in
lemma pow_congr (e : V ≃ W) (π : Perm V) (n : ℕ) (x : V) :
    (e.permCongr π ^ n) (e x) = e ((π ^ n) x) := by
  induction n with
  | zero => rfl
  | succ n hn => simp only [pow_succ', Perm.mul_apply, hn, permCongr_apply, symm_apply_apply]

lemma sameCycle_congr (e : V ≃ W) (π : Perm V) (i j : V) :
    π.SameCycle i j ↔ (e.permCongr π).SameCycle (e i) (e j) := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    have he : (e.permCongr π ^ n) (e i) = e j := by rw [pow_congr, hn]
    rw [← he]
    exact (Perm.SameCycle.refl _ _).pow_right
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    rw [pow_congr] at hn
    have he := e.injective hn
    rw [← he]
    exact (Perm.SameCycle.refl _ _).pow_right

def classCongr (e : V ≃ W) (π : Perm V) : Classes π ≃ Classes (e.permCongr π) :=
  Quotient.congr e (sameCycle_congr e π)

@[simp] lemma classCongr_mk (e : V ≃ W) (π : Perm V) (i : V) :
    classCongr e π (classOf π i) = classOf (e.permCongr π) (e i) := rfl

def somePins (P : Set V) : P ≃ (some '' P : Set (Option V)) :=
  Equiv.ofBijective (fun i => ⟨some (i : V), ⟨i, i.property, rfl⟩⟩)
    ⟨by intro i j h; exact Subtype.ext (Option.some.inj (congrArg Subtype.val h)),
      by rintro ⟨_, i, hi, rfl⟩; exact ⟨⟨i, hi⟩, rfl⟩⟩

omit [Fintype V] in
@[simp] lemma somePins_apply (P : Set V) (i : P) :
    (somePins P i : Option V) = some i := rfl

end Heisenberg.Transport

noncomputable section
open scoped Classical
namespace Heisenberg.Pin
open Heisenberg.Cycle Heisenberg.Return Heisenberg.Transport
open Equiv
variable {V W Ω : Type*} [Fintype V] [Fintype W] [Fintype Ω]

def pinLaw (μ : Ω → ℝ) (π : Ω → Perm V) (P : Set V) : MvPolynomial (P ⊕ P) ℂ :=
  lawSymbol (fun ω => μ ω * (2 : ℝ) ^ missingCount (π ω) P)
    (fun ω => nextPermutation (π ω) P)

universe u

end Heisenberg.Pin
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_SimultaneousPins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical Topology
open Set Filter Metric
open scoped ComplexConjugate
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical

noncomputable section
open scoped Classical
namespace Heisenberg.Pin
variable {V Ω : Type*} [Fintype V] [Fintype Ω]

def subsetLaw (μ : Ω → ℝ) (A : Ω → Finset V) (B : Finset V) : ℝ :=
  ∑ ω, if A ω = B then μ ω else 0

end Heisenberg.Pin

noncomputable section
open scoped Classical

noncomputable section
open scoped Classical

noncomputable section
open scoped Classical
namespace Heisenberg.Pin
attribute [-instance] Subtype.instDecidableEq
open Heisenberg.Cycle Heisenberg.Return
variable {V Ω : Type*} [Fintype V] [Fintype Ω]

def pinPartition (μ : Ω → ℝ) (π : Ω → Equiv.Perm V) (P : Set V) : ℝ :=
  ∑ ω, μ ω * (2 : ℝ) ^ missingCount (π ω) P

def pinDensity (μ : Ω → ℝ) (π : Ω → Equiv.Perm V) (P : Set V) (ω : Ω) : ℝ :=
  (μ ω * (2 : ℝ) ^ missingCount (π ω) P) / pinPartition μ π P

end Heisenberg.Pin
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
-- module Solutions.OAIW2_Heis.Heisenberg_PinDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical Topology
open Set Filter Metric
open scoped ComplexConjugate
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical

namespace Heisenberg.Pin
attribute [-instance] Subtype.instDecidableEq
open Heisenberg.Cycle Heisenberg.Return
variable {V Ω : Type*} [Fintype V] [Fintype Ω]

def testPins (E : Set V) (T : Finset V) : Finset ↥(E ∪ (T : Set V)) :=
  T.subtype (fun i => i ∈ E ∪ (T : Set V))

omit [Fintype V] in
@[simp] lemma mem_testPins (E : Set V) (T : Finset V) (i : ↥(E ∪ (T : Set V))) :
    i ∈ testPins E T ↔ (i : V) ∈ T := Finset.mem_subtype

omit [Fintype V] in
@[simp] lemma card_testPins (E : Set V) (T : Finset V) :
    (testPins E T).card = T.card := by
  rw [testPins, Finset.card_subtype, Finset.filter_eq_self.mpr]
  intro i hi
  exact Or.inr hi

def returnFraction (μ : Ω → ℝ) (π : Ω → Equiv.Perm V) (E : Set V) (T : Finset V) : ℝ :=
  (∑ i ∈ testPins E T, ∑ ω,
    if nextPermutation (π ω) (E ∪ (T : Set V)) i ∈ testPins E T
    then pinDensity μ π (E ∪ (T : Set V)) ω else 0) / T.card

end Heisenberg.Pin

namespace Heisenberg.LayeredExchange
attribute [-instance] instDecidableEqProd
open Exposure Pin Return
variable {V : Type*} [Fintype V]

def layerWeight {n : ℕ} (p : Fin n → ℝ) (c : Fin n → Bool) : ℝ :=
  ∏ i,if c i then p i else 1-p i

def coinWiring {n : ℕ} (s : Equiv.Perm (Fin n)) (a b : Fin n → V)
    (c : Fin n → Bool) : Equiv.Perm (Fin n × V) :=
  wiring s (fun i => if c i then Equiv.swap (a i) (b i) else 1)

attribute [local irreducible] pinDensity returnFraction lawSymbol wiring fibers layerWeight coinWiring

end Heisenberg.LayeredExchange
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
-- module Solutions.OAIW2_Heis.Heisenberg_TwoEndedReturns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Classical BigOperators
namespace Heisenberg.Pin
open Heisenberg.Cycle Heisenberg.Return
variable {V Ω : Type*} [Fintype V] [Fintype Ω]

def unpinned (E : Set V) : Finset V := Finset.univ.filter (fun j=>j∉E)

end Heisenberg.Pin

end

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_BoundaryWitness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Classical BigOperators
namespace Heisenberg.Surface
open Heisenberg.Cycle Heisenberg.LayeredExchange
variable {V : Type*} [Fintype V]

local instance instFintypeClasses (π : Equiv.Perm V) : Fintype (Classes π) := Fintype.ofFinite _

def hitClasses (π : Equiv.Perm V) (B : Set V) : Finset (Classes π) :=
  Finset.univ.filter fun c=>∃ z∈B,classOf π z=c

def witnesses (π : Equiv.Perm V) (B C : Set V) : Finset V :=
  Finset.univ.filter fun z=>z∈B ∧ (z∈C ∨ π z∉B)

end Heisenberg.Surface
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_SlotColorTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Classical BigOperators Matrix.Norms.Operator
namespace Heisenberg.SlotColor
variable {V : Type*}
abbrev Color := V → Bool

def permute (π : Equiv.Perm V) : Equiv.Perm (Color (V:=V)) where
  toFun c := c ∘ π.symm
  invFun c := c ∘ π
  left_inv c := by ext i; simp
  right_inv c := by ext i; simp

@[simp] lemma permute_apply (π : Equiv.Perm V) (c : Color (V:=V)) (i : V) :
    permute π c i = c (π.symm i) := rfl

variable [Fintype V]

def matrix (π : Equiv.Perm V) : Matrix (Color (V:=V)) (Color (V:=V)) ℝ :=
  fun c b => if permute π b = c then 1 else 0

abbrev ClosedColor (π : Equiv.Perm V) := {c : Color (V:=V) // ∀ i, c (π i) = c i}
instance instFintypeClosedColor (π : Equiv.Perm V) : Fintype (ClosedColor π) := Fintype.ofFinite _

lemma const_cycle (π : Equiv.Perm V) (c : ClosedColor π) {i j : V}
    (h : π.SameCycle i j) : c.val i = c.val j := by
  obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
  have hh : ∀ n, c.val ((π^n) i) = c.val i := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ',Equiv.Perm.mul_apply,c.property,ih]
  rw [← hn,hh]

def magnetization (c : Color (V:=V)) : ℝ := ∑ i, if c i then (1:ℝ)/2 else -1/2

end Heisenberg.SlotColor
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_PinnedColors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Classical BigOperators
namespace Heisenberg.Surface
open Heisenberg.Cycle Heisenberg.Pin Heisenberg.Return
variable {V : Type*} [Fintype V]

abbrev PinnedColor (π : Equiv.Perm V) (P : Set V) :=
  {c : V → Bool // (∀ i,c (π i)=c i) ∧ ∀ i∈P,c i=true}
instance instFintypePinnedColor (π : Equiv.Perm V) (P : Set V) : Fintype (PinnedColor π P) := Fintype.ofFinite _
local instance instFintypeMissingClasses (π : Equiv.Perm V) (P : Set V) : Fintype (MissingClasses π P) := Fintype.ofFinite _

lemma pinnedColor_sameCycle (π : Equiv.Perm V) (P : Set V) (c : PinnedColor π P)
    {i j : V} (h : π.SameCycle i j) : c.val i=c.val j :=
  SlotColor.const_cycle π ⟨c.val,c.property.1⟩ h

def pinnedColorEquiv (π : Equiv.Perm V) (P : Set V) :
    PinnedColor π P ≃ (MissingClasses π P → Bool) where
  toFun c q := Quotient.lift c.val (fun _ _ h=>pinnedColor_sameCycle π P c h) q.val
  invFun ε := ⟨fun i=>if h : ∀ j∈P,classOf π i≠classOf π j then ε ⟨classOf π i,h⟩ else true,by
    constructor
    · intro i; simp only [classOf_apply]
    · intro i hi; exact dite_eq_right (by intro h; exact h i hi rfl)⟩
  left_inv c := by
    apply Subtype.ext
    funext i
    dsimp
    split_ifs with h
    · rfl
    · obtain ⟨j,hj,hij⟩:=by simpa only [not_forall,not_not] using h
      exact ((pinnedColor_sameCycle π P c ((classOf_eq_iff π i j).mp hij)).trans (c.property.2 j hj)).symm
  right_inv ε := by
    funext q
    rcases q with ⟨q,hq⟩
    induction q using Quotient.inductionOn with | _ i =>
      dsimp
      split_ifs with h
      · rfl
      · exact (h hq).elim

def halfSpin (b : Bool) : ℝ := if b then 1/2 else -1/2

end Heisenberg.Surface
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_PinnedMagnetization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Classical BigOperators
namespace Heisenberg.Surface
open Heisenberg.Cycle Heisenberg.Pin Heisenberg.Return
variable {V Ω : Type*} [Fintype V] [Fintype Ω]

def cutSpin (C : Finset V) (c : V → Bool) : ℝ := ∑ i∈C,halfSpin (c i)

end Heisenberg.Surface
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_SurfaceTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Classical BigOperators
namespace Heisenberg.Surface
open Heisenberg.Cycle Heisenberg.Pin Heisenberg.Return
variable {V Ω : Type*} [Fintype V] [Fintype Ω]

def colorTail (μ : Ω → ℝ) (π : Ω → Equiv.Perm V) (C : Finset V) : ℝ :=
  ∑ ω,μ ω * Matrix.trace (SlotColor.matrix (π ω) *
    Matrix.diagonal (fun c=>if C.card/4≤cutSpin C c then (1:ℝ) else 0))

end Heisenberg.Surface
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_CutColors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Classical BigOperators Fin.NatCast
attribute [-instance] instDecidableEqFin instDecidableEqProd
@[reducible] local instance cutDecEq (α : Type*) : DecidableEq α := Classical.decEq α
namespace Heisenberg.Surface
open Heisenberg.LayeredExchange
variable {V : Type*} [Fintype V]

lemma rotate_pow_zero (n k : ℕ) : ((finRotate (n+1))^k) 0=(k : Fin (n+1)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ',Equiv.Perm.mul_apply,ih,finRotate_apply]
    simp

omit [Fintype V] in
lemma transport_succ_zero (n : ℕ) (σ : Fin (n+1) → Equiv.Perm V) (k : ℕ) :
    transport (finRotate (n+1)) σ 0 (k+1)=σ (k : Fin (n+1))*transport (finRotate (n+1)) σ 0 k := by
  rw [transport,rotate_pow_zero]

def extendCut (n : ℕ) (σ : Fin (n+1) → Equiv.Perm V) (c : V → Bool) : Fin (n+1)×V → Bool :=
  fun z=>c ((transport (finRotate (n+1)) σ 0 z.1.val).symm z.2)

omit [Fintype V] in
lemma extendCut_invariant (n : ℕ) (σ : Fin (n+1) → Equiv.Perm V)
    (c : V → Bool) (hc : ∀ v,c (transport (finRotate (n+1)) σ 0 (n+1) v)=c v) :
    ∀ z,extendCut n σ c (wiring (finRotate (n+1)) σ z)=extendCut n σ c z := by
  rintro ⟨t,v⟩
  rw [wiring_apply]
  unfold extendCut
  dsimp only
  by_cases ht : t=Fin.last n
  · subst t
    simp only [finRotate_last,Fin.val_zero]
    change c (σ (Fin.last n) v)=c ((transport (finRotate (n+1)) σ 0 n).symm v)
    have hh:=hc ((transport (finRotate (n+1)) σ 0 n).symm v)
    rw [transport_succ_zero] at hh
    simp only [Equiv.Perm.mul_apply,Equiv.apply_symm_apply] at hh
    have hn : (n : Fin (n+1))=Fin.last n := by ext; simp
    rw [hn] at hh
    exact hh
  · rw [coe_finRotate_of_ne_last ht,transport_succ_zero]
    have ht' : ((t.val : ℕ) : Fin (n+1))=t := by simp
    rw [ht']
    change c ((transport (finRotate (n+1)) σ 0 t.val).symm ((σ t).symm ((σ t) v))) = _
    rw [Equiv.symm_apply_apply]

def cutColorEquiv (n : ℕ) (σ : Fin (n+1) → Equiv.Perm V) :
    SlotColor.ClosedColor (wiring (finRotate (n+1)) σ) ≃
      SlotColor.ClosedColor (transport (finRotate (n+1)) σ 0 (n+1)) where
  toFun c := ⟨fun v=>c.val (0,v),invariant_cut _ _ c.val c.property 0 (n+1) (by rw [rotate_pow_zero]; simp)⟩
  invFun c := ⟨extendCut n σ c.val,extendCut_invariant n σ c.val c.property⟩
  left_inv c := by
    apply Subtype.ext
    funext z
    obtain ⟨t,v⟩:=z
    have hh:=invariant_propagates (finRotate (n+1)) σ c.val c.property 0
      ((transport (finRotate (n+1)) σ 0 t.val).symm v) t.val
    rw [rotate_pow_zero,Equiv.apply_symm_apply] at hh
    simpa [extendCut] using hh.symm
  right_inv c := by
    apply Subtype.ext
    funext v
    rfl

end Heisenberg.Surface
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_PinBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical
attribute [-instance] instDecidableEqFin
@[reducible] local instance pinDecEq (α : Type*) : DecidableEq α := Classical.decEq α

namespace Heisenberg.Exposure
open Heisenberg.Cycle Heisenberg.Pin Heisenberg.Return Heisenberg.Serial Heisenberg.SparseWitness
variable {V : Type} [Fintype V]

def cutAdmissible {X : Type} [PseudoMetricSpace X] {m : ℕ} (loc : V → X)
    (α L : ℝ) (U : Finset (Fin m×V)) : Prop :=
  ∃ t J, U=J.image (fun j=>(t,j)) ∧ localGrowth loc α L J

end Heisenberg.Exposure
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_PeriodicReturnEstimate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Classical BigOperators Fin.NatCast
open Filter Topology
namespace Heisenberg.Bootstrap
attribute [-instance] instDecidableEqFin
@[reducible] local instance retDecEq (α : Type*) : DecidableEq α := Classical.decEq α
attribute [local irreducible] Pin.pinDensity LayeredExchange.layerWeight LayeredExchange.coinWiring Heisenberg.Exposure.layerMass Heisenberg.Exposure.layerHistory Heisenberg.Cycle.MissingSet Heisenberg.Return.HasHit Heisenberg.Exposure.exposedSweep
open Heisenberg.Geometry Heisenberg.Schedule Heisenberg.SpatialFrame Heisenberg.MeshPair Heisenberg.Exposure Heisenberg.LatticeRegular Heisenberg.Cycle

end Heisenberg.Bootstrap
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_MeshProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Classical BigOperators Fin.NatCast
attribute [-instance] instDecidableEqFin instDecidableEqProd
@[reducible] local instance meshProductDecEq (α : Type*) : DecidableEq α := Classical.decEq α
namespace Heisenberg.Surface
open LayeredExchange
variable {V : Type} [Fintype V]

def colorCoin (a b : V) (r : ℝ) : Matrix (V → Bool) (V → Bool) ℝ :=
  (1-r) • 1+r • SlotColor.matrix (Equiv.swap a b)

end Heisenberg.Surface
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_MeshCompletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Classical BigOperators Fin.NatCast
attribute [-instance] instDecidableEqFin instDecidableEqProd
@[reducible] local instance completionDecEq (α : Type*) : DecidableEq α := Classical.decEq α
namespace Heisenberg.Surface
open LayeredExchange MeshPair
variable {V : Type} [Fintype V]

def completedEndpoint (a u : ℕ → V) (q c : ℕ) (j : ℕ) : V :=
  if j%(q+c)<q then a (j%(q+c)) else u (j%(q+c)-q)

def completedRate (δ : ℝ) (q c k : ℕ) (j : ℕ) : ℝ :=
  if j%(q+c)<q then δ/2 else if k*(q+c)≤j then 1 else 0

@[simp] lemma colorCoin_zero (a b : V) : colorCoin a b 0=1 := by simp [colorCoin]
@[simp] lemma colorCoin_one (a b : V) : colorCoin a b 1=SlotColor.matrix (Equiv.swap a b) := by simp [colorCoin]

end Heisenberg.Surface
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_SlotOnMesh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped Classical
namespace Heisenberg.SpinSlots
abbrev Config (ℓ : ℕ) := Finset (Fin ℓ)
abbrev Level (ℓ : ℕ) := Fin (ℓ+1)

def basis (ℓ : ℕ) : Matrix (Config ℓ) (Level ℓ) ℝ :=
  fun A k => if A.card = k.val then (Real.sqrt (ℓ.choose k.val))⁻¹ else 0

def raising (ℓ : ℕ) : Matrix (Config ℓ) (Config ℓ) ℝ :=
  fun A B => ∑ j ∈ A, if B = A.erase j then 1 else 0

def diagonalZ (ℓ : ℕ) : Matrix (Config ℓ) (Config ℓ) ℝ :=
  Matrix.diagonal (fun A => (A.card : ℝ) - (ℓ : ℝ)/2)

def physicalZ (ℓ : ℕ) : Matrix (Level ℓ) (Level ℓ) ℝ :=
  Matrix.diagonal (fun k => (k.val : ℝ) - (ℓ : ℝ)/2)

def physicalPlus (ℓ : ℕ) : Matrix (Level ℓ) (Level ℓ) ℝ :=
  fun m k => if m.val = k.val+1 then Real.sqrt (((ℓ-k.val : ℕ) : ℝ)*(k.val+1)) else 0

def average (ℓ : ℕ) : Matrix (Config ℓ) (Config ℓ) ℝ :=
  fun A B => (Fintype.card (Equiv.Perm (Fin ℓ)) : ℝ)⁻¹ *
    ∑ σ : Equiv.Perm (Fin ℓ), if A = B.map σ.toEmbedding then 1 else 0

end Heisenberg.SpinSlots

open scoped Classical BigOperators
namespace Heisenberg.TensorMatrix
variable {X α β γ R : Type*} [Fintype X] [DecidableEq X] [CommSemiring R]

def tensor (M : X → Matrix α β R) : Matrix (X → α) (X → β) R :=
  fun a b => ∏ x, M x (a x) (b x)

def onsite [DecidableEq α] (x : X) (M : Matrix α α R) :
    Matrix (X → α) (X → α) R :=
  tensor (Function.update (fun _ => 1) x M)

end Heisenberg.TensorMatrix

namespace Heisenberg.SlotTensor
open SpinSlots TensorMatrix
variable {X : Type*} [Fintype X] [DecidableEq X]

def configEquiv (ℓ : ℕ) : SlotColor.Color (V:=X × Fin ℓ) ≃ (X → Config ℓ) where
  toFun c x := Finset.univ.filter (fun a => c (x,a) = true)
  invFun A p := decide (p.2 ∈ A p.1)
  left_inv c := by
    funext ⟨x,a⟩
    cases h : c (x,a) <;> simp [h]
  right_inv A := by ext x a; simp

omit [Fintype X] [DecidableEq X] in
@[simp] lemma mem_configEquiv (ℓ : ℕ) (c : SlotColor.Color (V:=X × Fin ℓ))
    (x : X) (a : Fin ℓ) : a ∈ configEquiv ℓ c x ↔ c (x,a) = true := by
  simp [configEquiv]

def fiberPerm {ℓ : ℕ} (κ : X → Equiv.Perm (Fin ℓ)) : Equiv.Perm (X × Fin ℓ) where
  toFun p := (p.1,κ p.1 p.2)
  invFun p := (p.1,(κ p.1).symm p.2)
  left_inv p := by simp
  right_inv p := by simp

def matrix {ℓ : ℕ} (π : Equiv.Perm (X × Fin ℓ)) :
    Matrix (X → Config ℓ) (X → Config ℓ) ℝ :=
  Matrix.reindex (configEquiv ℓ) (configEquiv ℓ) (SlotColor.matrix π)

end Heisenberg.SlotTensor
namespace Heisenberg.SlotHalf
open SlotColor
variable {V : Type*} [Fintype V] [DecidableEq V]

def change (i : V) (s : Bool) : Matrix (Color (V:=V)) (Color (V:=V)) ℝ :=
  fun a b => if b i ≠ s ∧ a = Function.update b i s then 1 else 0

def z (i : V) : Matrix (Color (V:=V)) (Color (V:=V)) ℝ :=
  Matrix.diagonal (fun a => if a i then (1:ℝ)/2 else -1/2)

end Heisenberg.SlotHalf

namespace Heisenberg.SlotHalf
variable {X : Type*} [Fintype X] [DecidableEq X]

def totalPlus (ℓ : ℕ) (x : X) := ∑ a : Fin ℓ, change (x,a) true
def totalMinus (ℓ : ℕ) (x : X) := ∑ a : Fin ℓ, change (x,a) false
def totalZ (ℓ : ℕ) (x : X) := ∑ a : Fin ℓ, z (x,a)

end Heisenberg.SlotHalf

namespace Heisenberg.SlotTensor
open TensorMatrix SpinSlots
variable {X : Type*} [Fintype X] [DecidableEq X]

def spinBond (ℓ : ℕ) (x y : X) : Matrix (X → Level ℓ) (X → Level ℓ) ℝ :=
    (1/2:ℝ) • (onsite x (physicalPlus ℓ)*onsite y (physicalPlus ℓ).transpose +
      onsite x (physicalPlus ℓ).transpose*onsite y (physicalPlus ℓ)) +
      onsite x (physicalZ ℓ)*onsite y (physicalZ ℓ)

def slotBond (ℓ : ℕ) (x y : X) : Matrix (SlotColor.Color (V:=X × Fin ℓ))
    (SlotColor.Color (V:=X × Fin ℓ)) ℝ :=
    (1/2:ℝ) • (∑ a : Fin ℓ, ∑ b : Fin ℓ, SlotColor.matrix (Equiv.swap (x,a) (y,b))) -
      ((ℓ:ℝ)^2/4) • 1

end Heisenberg.SlotTensor

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_TensorLiftIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical BigOperators Matrix
namespace Heisenberg.TensorUnits
variable {R E K : Type*} [CommSemiring R] [Semiring E] [Algebra R E]
  [Fintype K] [DecidableEq K]

variable {X : Type*} [Fintype X] [DecidableEq X]

def functionReindex {n : ℕ} (e : X ≃ Fin n) : (X → K) ≃ (Fin n → K) where
  toFun f:=f ∘ e.symm
  invFun f:=f ∘ e
  left_inv f:=by ext x; simp
  right_inv f:=by ext x; simp

end Heisenberg.TensorUnits
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_SpinTensorRepresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical BigOperators Matrix Matrix.Norms.Operator
namespace Heisenberg
open TensorUnits
variable {d ℓ : ℕ} {X : Type} [Fintype X] [DecidableEq X]

def tensorUnits (site : X → Site d) (a b : Fin (Fintype.card X) → Level ℓ) : QuasiLocal d ℓ :=
  system (fun i=>localUnit d ℓ (site ((Fintype.equivFin X).symm i))) a b

omit [DecidableEq X] in
lemma tensorUnits_mul (site : X → Site d) (hinj : Function.Injective site)
    (a b c e : Fin (Fintype.card X) → Level ℓ) :
    tensorUnits site a b*tensorUnits site c e=if b=c then tensorUnits site a e else 0 := by
  apply system_mul _ (fun i=>localUnit_mul_same d ℓ _)
  intro i j hij a b c e
  exact localUnits_commute (fun h=>hij ((Fintype.equivFin X).symm.injective (hinj h))) a b c e

omit [DecidableEq X] in
lemma tensorUnits_sum (site : X → Site d) :
    ∑ a : Fin (Fintype.card X) → Level ℓ,tensorUnits site a a=1 :=
  system_diagonal_sum ℝ _ (fun _=>localUnit_diagonal_sum d ℓ _)

def finiteRepresentation (site : X → Site d) (hinj : Function.Injective site) :
    Matrix (X → Level ℓ) (X → Level ℓ) ℝ →ₐ[ℝ] QuasiLocal d ℓ :=
  (liftAlg (tensorUnits site) (tensorUnits_mul site hinj) (tensorUnits_sum site)).comp
    (Matrix.reindexAlgEquiv ℝ ℝ (functionReindex (Fintype.equivFin X))).toAlgHom

end Heisenberg
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_SpectralTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical BigOperators Matrix Matrix.Norms.Operator

namespace Heisenberg.SlotTensor
open TensorMatrix SpinSlots
variable {X : Type} [Fintype X] [DecidableEq X]

def physicalMagnetization (ℓ : ℕ) (k : X → Level ℓ) : ℝ :=
  ∑ x,((k x:ℝ)-(ℓ:ℝ)/2)

def configMagnetization (ℓ : ℕ) (A : X → Config ℓ) : ℝ :=
  ∑ x,((A x).card-(ℓ:ℝ)/2)

end Heisenberg.SlotTensor
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_PhysicalClock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical BigOperators Matrix Matrix.Norms.Operator
namespace Heisenberg.SlotTensor
open TensorMatrix SpinSlots
variable {X : Type} [Fintype X] [DecidableEq X]

abbrev SiteEdges (R : X → X → Prop) := {e : X×X // R e.1 e.2}
abbrev ClockEdges (R : X → X → Prop) (ℓ : ℕ) := {e : (X×Fin ℓ)×(X×Fin ℓ) // R e.1.1 e.2.1}

def clockEdgeEquiv (R : X → X → Prop) (ℓ : ℕ) : ClockEdges R ℓ ≃ SiteEdges R × (Fin ℓ×Fin ℓ) where
  toFun e:=⟨⟨(e.val.1.1,e.val.2.1),e.property⟩,(e.val.1.2,e.val.2.2)⟩
  invFun e:=⟨((e.1.val.1,e.2.1),(e.1.val.2,e.2.2)),e.1.property⟩
  left_inv _:=rfl
  right_inv _:=rfl

def clockGenerator (R : X → X → Prop) (ℓ : ℕ) : Matrix ((X×Fin ℓ) → Bool) ((X×Fin ℓ) → Bool) ℝ :=
  ∑ e : ClockEdges R ℓ,(1/2:ℝ) • (SlotColor.matrix (Equiv.swap e.val.1 e.val.2)-1)

def spinGenerator (R : X → X → Prop) (ℓ : ℕ) : Matrix (X → Level ℓ) (X → Level ℓ) ℝ :=
  ∑ e : SiteEdges R,(spinBond ℓ e.val.1 e.val.2-((ℓ:ℝ)^2/4) • 1)

end Heisenberg.SlotTensor
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_ExchangeOnMesh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section

open scoped Matrix Matrix.Norms.Operator
namespace Heisenberg.Heat
open MatrixContraction
variable {V : Type*} [Fintype V] [DecidableEq V]

def kernel (G : Matrix V V ℝ) (t : ℝ) : Matrix V V ℝ :=
  NormedSpace.exp (t • G)

def entry (i j : V) : Matrix V V ℝ →L[ℝ] ℝ :=
  (Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap

omit [DecidableEq V] in
@[simp] lemma entry_apply (i j : V) (P : Matrix V V ℝ) : entry i j P = P i j := rfl

structure SubMarkovGenerator (G : Matrix V V ℝ) : Prop where
  offdiag : ∀ i j, i ≠ j → 0 ≤ G i j
  row : ∀ i, ∑ j, G i j ≤ 0
  col : ∀ j, ∑ i, G i j ≤ 0

end Heisenberg.Heat

noncomputable section
open Filter Topology

namespace Heisenberg.ExchangeMatrix
open MatrixContraction Heat
open scoped Matrix Matrix.Norms.Operator NNReal
variable {V : Type*} [Fintype V] [DecidableEq V]

def permutationMatrix (σ : Equiv.Perm V) : Matrix V V ℝ := fun i j => if σ j = i then 1 else 0

@[simp] lemma permutationMatrix_col (σ : Equiv.Perm V) (j : V) :
    ∑ i, permutationMatrix σ i j = 1 := by simp [permutationMatrix]

@[simp] lemma permutationMatrix_row (σ : Equiv.Perm V) (i : V) :
    ∑ j, permutationMatrix σ i j = 1 := by
  simp only [permutationMatrix,← σ.eq_symm_apply]
  simp

def bernoulliStep (r : ℝ) (σ : Equiv.Perm V) (t : ℝ) : Matrix V V ℝ :=
  Real.exp (-r*t) • 1 + (1-Real.exp (-r*t)) • permutationMatrix σ

abbrev Clock (V : Type*) := ℝ≥0 × Equiv.Perm V

def meshStep : List (Clock V) → ℝ → Matrix V V ℝ
  | [], _ => 1
  | e::L,t => bernoulliStep e.1 e.2 t * meshStep L t

def clockGenerator : List (Clock V) → Matrix V V ℝ
  | [] => 0
  | e::L => (e.1:ℝ) • (permutationMatrix e.2 - 1) + clockGenerator L

end Heisenberg.ExchangeMatrix
end

noncomputable section
open Filter Topology

namespace Heisenberg.ExchangeMatrix
open MatrixContraction Heat
open scoped Matrix Matrix.Norms.Operator NNReal
variable {V : Type*} [fV : Fintype V] [DecidableEq V]

def linearStep (r : ℝ) (σ : Equiv.Perm V) (t : ℝ) : Matrix V V ℝ :=
  (1-r*t) • 1 + (r*t) • permutationMatrix σ

def linearMesh : List (Clock V) → ℝ → Matrix V V ℝ
  | [],_=>1
  | e::L,t=>linearStep e.1 e.2 t*linearMesh L t

end Heisenberg.ExchangeMatrix
end
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_ColorClockLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical BigOperators Matrix Matrix.Norms.Operator NNReal
open Filter Topology
namespace Heisenberg.Surface
open ExchangeMatrix MeshPair
variable {V : Type} [Fintype V]

def colorClocks (a b : ℕ → V) : ℕ → List (Clock (V → Bool))
  | 0=>[]
  | n+1=>(⟨1/2,by norm_num⟩,SlotColor.permute (Equiv.swap (a n) (b n)))::colorClocks a b n

end Heisenberg.Surface
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_MeshMatrixSurface
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical BigOperators Fin.NatCast
open Filter Topology
attribute [-instance] instDecidableEqFin instDecidableEqProd
namespace Heisenberg.Surface
open Heisenberg.Cycle Pin Return LayeredExchange Exposure LatticeRegular SpatialFrame Heisenberg.Geometry

def tailProjection (V : Type) [Fintype V] : Matrix (V → Bool) (V → Bool) ℝ :=
  Matrix.diagonal (fun c=>if (Fintype.card V:ℝ)/4≤SlotColor.magnetization c then (1:ℝ) else 0)

end Heisenberg.Surface
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_SymmetrizedSurface
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical BigOperators Fin.NatCast Matrix Matrix.Norms.Operator
open Filter Topology
attribute [-instance] instDecidableEqFin instDecidableEqProd
@[reducible] local instance symSurfaceDecEq (α : Type*) : DecidableEq α := Classical.decEq α
namespace Heisenberg.Surface
open Heisenberg.Geometry LatticeRegular SpatialFrame MeshPair

def colorSymmetrizer (X : Type) [Fintype X] (ℓ : ℕ) :
    Matrix ((X×Fin ℓ) → Bool) ((X×Fin ℓ) → Bool) ℝ :=
  (Fintype.card (X → Equiv.Perm (Fin ℓ)):ℝ)⁻¹ •
    ∑ κ : X → Equiv.Perm (Fin ℓ),SlotColor.matrix (SlotTensor.fiberPerm κ)

end Heisenberg.Surface
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_FiniteTilt
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical BigOperators
namespace Heisenberg.Selection
variable {I : Type*} [Fintype I]

def weightedTail (w : I → ℝ) (m : I → ℝ) (a : ℝ) : ℝ :=
  ∑ i,if a≤ m i then w i else 0

def tiltPartition (w m : I → ℝ) (b : ℝ) : ℝ := ∑ i,w i*Real.exp (b*m i)

def tiltLowerMass (w m : I → ℝ) (b a : ℝ) : ℝ :=
  (∑ i,if m i<a then w i*Real.exp (b*m i) else 0)/tiltPartition w m b

end Heisenberg.Selection
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_SpinField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical BigOperators Matrix Matrix.Norms.Operator
namespace Heisenberg
open SlotTensor TensorMatrix
variable {d ℓ : ℕ}

def totalZ (Λ : Finset (Site d)) : QuasiLocal d ℓ:=∑ x∈Λ,spinZ d ℓ x

def shiftedField (Λ : Finset (Site d)) (h : ℝ) : QuasiLocal d ℓ:=
  hamiltonian d ℓ Λ+
    (((Fintype.card (SiteEdges (fun x y : Λ=>NearestNeighbor x.val y.val)):ℝ)*(ℓ:ℝ)^2/8)) • 1-
      h • totalZ (ℓ:=ℓ) Λ

end Heisenberg
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_CubeSurface
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical BigOperators
open Filter Topology
namespace Heisenberg
open SpatialFrame
variable {d ℓ : ℕ}

lemma box_mem (d n : ℕ) (x : Site d) : x∈box d n ↔ ∀ j,|x j|≤(n:ℤ) := Geometry.mem_boxFinset d n x
lemma box_nonempty (d n : ℕ) : (box d n).Nonempty:=⟨0,(box_mem d n 0).mpr (by intro j; simp)⟩

end Heisenberg
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_SpinAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Classical BigOperators ComplexConjugate
open Filter Topology
namespace Heisenberg

variable {d ℓ : ℕ}

def averageState {I : Type*} [Fintype I] (μ : I → ℝ) (hμ : ∀ i,0≤μ i)
    (hm : ∑ i,μ i=1) (ω : I → State d ℓ) : State d ℓ where
  functional:=∑ i,(μ i:ℂ) • (ω i).functional
  normalized:=by
    simp only [sum_apply,smul_apply,smul_eq_mul,State.normalized,mul_one]
    exact_mod_cast hm
  positive:=by
    intro A
    simp only [sum_apply,smul_apply,smul_eq_mul,
      Complex.im_sum,Complex.re_sum,Complex.mul_im,Complex.ofReal_im,zero_mul,add_zero,
      Complex.mul_re,Complex.ofReal_re,sub_zero]
    constructor
    · simp only [(ω _).positive A |>.1,mul_zero,Finset.sum_const_zero]
    · exact Finset.sum_nonneg (fun i _=>mul_nonneg (hμ i) ((ω i).positive A).2)

def translationLinear (d ℓ : ℕ) (x : Site d) : QuasiLocal d ℓ →L[ℂ] QuasiLocal d ℓ :=
  (translation d ℓ x).toLinearMap.mkContinuous 1 (fun A=>by change ‖translation d ℓ x A‖≤1*‖A‖; rw [norm_translation,one_mul])

@[simp] lemma translationLinear_apply (x : Site d) (A : QuasiLocal d ℓ) :
    translationLinear d ℓ x A=translation d ℓ x A := rfl

def translatedState (ω : State d ℓ) (x : Site d) : State d ℓ where
  functional:=ω.functional.comp (translationLinear d ℓ x)
  normalized:=by simp only [ContinuousLinearMap.comp_apply,translationLinear_apply,map_one,State.normalized]
  positive:=by
    intro A
    simpa only [ContinuousLinearMap.comp_apply,translationLinear_apply,map_mul,map_star] using
      ω.positive (translation d ℓ x A)

end Heisenberg
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_SpinFieldDynamics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate
open Filter Topology
namespace GibbsStrip
variable {E : Type*} [CStarAlgebra E]
local instance instNormedAlgebraRat_solutions_1 : NormedAlgebra ℚ E:=NormedAlgebra.restrictScalars ℚ ℂ E

end GibbsStrip
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_SpinCubeAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical BigOperators ComplexConjugate
open Filter Topology
namespace Heisenberg
variable {d ℓ : ℕ}

def cubeAverage (Λ : Finset (Site d)) (hΛ : Λ.Nonempty) (ω : State d ℓ) : State d ℓ :=
  averageState (fun _ : Λ=>(Λ.card:ℝ)⁻¹) (fun _=>by positivity)
    (by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul]; exact mul_inv_cancel₀ (show (Λ.card:ℝ)≠0 by exact_mod_cast Finset.card_ne_zero.mpr hΛ))
    (fun x=>translatedState ω x.val)

end Heisenberg
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_SpinAverageBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical BigOperators ComplexConjugate
open Filter Topology
namespace Heisenberg
variable {d ℓ : ℕ}

def cubeBoundary (Λ : Finset (Site d)) (ω : State d ℓ) (h : ℝ)
    (M : QuasiLocal d ℓ →L[ℂ] QuasiLocal d ℓ) (B : QuasiLocal d ℓ) (t : ℝ) : ℂ :=
  (Λ.card:ℂ)⁻¹*∑ x∈Λ,ω.functional (translation d ℓ x
    (M (GibbsStrip.evolve (shiftedField (Λ.image (fun y=>-x+y)) h) t B)))

end Heisenberg
end
end

end OAI
end


