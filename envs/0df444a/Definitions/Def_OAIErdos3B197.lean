-- Prove2me | Definitions.Def_OAIErdos3B197
-- name    : OAIErdos3B197
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-10T13:18:03.480414+00:00
-- url     : https://prove2.me/theorems/99cce1ba-a76e-401a-b4ad-91abc84fc78b
-- title:
--   OpenAI Erdős-3 split, definitions bundle 198 of 207
-- statement:
--   Definitions bundle 198 of 207 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B196`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 198 available.
--
--   Modules: `OAI.Erdos3.FreimanModel.cyclicProductBlock`, `OAI.Erdos3.FreimanModel.cyclicProductLift`, `OAI.Erdos3.FreimanModel.cyclicProductLift_injective`, `OAI.Erdos3.FreimanModel.cyclicProductLift_sum_apply`, `OAI.Erdos3.FreimanModel.cyclicProductLift_sum_eq_iff`, `OAI.Erdos3.FreimanModel.cyclicProduct_sum_apply`, `OAI.Erdos3.FreimanModel.exists_bounded_affine_box_of_cyclic_model`, `OAI.Erdos3.FreimanModel.exists_dense_cyclicProduct_integer_model`, `OAI.Erdos3.FreimanModel.exists_dense_cyclic_model_of_integer_vectors`, `OAI.Erdos3.FreimanModel.exists_large_cyclicProduct_integer_lift`, `OAI.Erdos3.FreimanModel.exists_variableIntegerGraph_cyclic_model`, `OAI.Erdos3.FreimanModel.isAddFreimanIso_cyclicProductLift`, `OAI.Erdos3.FreimanModel.residueBlock`, `OAI.Erdos3.FreimanModel.residueBlock_bounds`, `OAI.Erdos3.FreimanModel.residueLift`, `OAI.Erdos3.FreimanModel.residueLift_sum_bounds`, `OAI.Erdos3.FreimanModel.residueLift_sum_cast`, `OAI.Erdos3.FreimanModel.residueLift_sum_eq_iff`, `OAI.Erdos3.FreimanModel.residueLift_sum_sub_abs_lt`, `OAI.Erdos3.FreimanModel.variableIntegerGraphLift`, `OAI.Erdos3.FreimanModel.variableIntegerGraphLift_none`, `OAI.Erdos3.FreimanModel.variableIntegerGraphLift_some`, `OAI.Erdos3.FreimanModel.variableIntegerGraphReduction`, `OAI.Erdos3.FreimanModel.variableIntegerGraphReduction_lift`, `OAI.Erdos3.NativeRankRelation.CommonData.degreewise_proper_affine_recovery`, `OAI.Erdos3.NativeRankRelation.CommonData.exists_shared_free_affine_orbit_family`, `OAI.Erdos3.NativeRankRelation.CommonData.exists_shared_free_affine_petal`, `OAI.Erdos3.NativeRankRelation.CommonData.exists_shared_free_affine_recovery`, `OAI.Erdos3.NativeRankRelation.CommonData.integer_graph_affine_model`, `OAI.Erdos3.NativeRankRelation.CommonData.proper_affine_graph_recovery`, `OAI.Erdos3.NativeRankRelation.CommonData.proper_integer_graph_affine_model`, `OAI.Erdos3.affine_petal_decomposition`, `OAI.Erdos3.exists_small_difference_graph_affine_coordinates`, `OAI.Erdos3.exists_small_difference_graph_coordinates`, `OAI.Erdos3.exists_small_difference_graph_proper_coordinates`, `OAI.Erdos3.markedEvaluationBoxRadius`, `OAI.Erdos3.markedLocalBoxConstant`, `OAI.Erdos3.markedLocalCoefficientValue_coordinate_dist_le`, `OAI.Erdos3.markedLocalCoefficientValue_norm_le`, `OAI.Erdos3.markedPhaseRemovalLinear`, `OAI.Erdos3.markedPhaseRemovalLinear_apply`, `OAI.Erdos3.markedPhaseRemovalLinear_coordinate_dist_le`, `OAI.Erdos3.markedPhaseRemovalLinear_coordinate_norm_le`, `OAI.Erdos3.markedRetractionBoxConstant`, `OAI.Erdos3.normalizedMarkedPhase_coordinate_norm_le`, `OAI.Erdos3.normalizedMarkedRetraction_coord`, `OAI.Erdos3.normalizedMarkedRetraction_coordinate_dist_le`, `OAI.Erdos3.normalizedMarkedRetraction_coordinate_norm_le`, `OAI.Erdos3.realMarkedParameterDirection_coordinate_norm_le`, `OAI.Erdos3.sharedFreePetalLiftBudget`, `OAI.Erdos3.sharedFreePetalLiftInput`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B065

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MarkedLocalObservableMetric
namespace OAI

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r d : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (t m : ℕ) (e : Basis (Fin d) ℚ (MarkedShiftQuotient F v w marked t))

theorem realMarkedParameterDirection_coordinate_norm_le {p : ℝ}
    (ht : (t : ℝ) ≤ p)
    (hdir : ∀ i j, rationalLogHeight
      (e.repr (markedQuotientDirection F v w marked t (RationalTorus.basis t i)) j) ≤ p)
    (a : Fin t → ℝ) :
    ‖(e.baseChange ℝ).equivFun (realMarkedParameterDirection F v w marked t a)‖ ≤
      Real.exp (2 * p) * ‖a‖ := by
  have hentries (i : Fin t) (j : Fin d) :
      |(e.repr (markedQuotientDirection F v w marked t (Pi.single i 1)) j : ℝ)| ≤ Real.exp p := by
    have hi : (RationalTorus.basis t i : Fin t → ℚ) = Pi.single i 1 := Pi.basisFun_apply ℚ (Fin t) i
    have h := hdir i j
    rw [hi] at h
    exact (rational_abs_real_le_numerator _).trans ((rationalLogHeight_le_iff _ _).mp h).1
  have hnorm : ‖(e.baseChange ℝ).equivFun (realMarkedParameterDirection F v w marked t a)‖ ≤
      (t : ℝ) * ‖a‖ * Real.exp p := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro j
    exact realMarkedParameterDirection_coordinate_le F v w marked t e a (norm_nonneg _)
      (fun i => by simpa only [Real.norm_eq_abs] using norm_le_pi_norm a i) hentries j
  apply hnorm.trans
  have ht' : (t : ℝ) ≤ Real.exp p := ht.trans (by linarith [Real.add_one_le_exp p])
  calc
    (t : ℝ) * ‖a‖ * Real.exp p ≤ Real.exp p * ‖a‖ * Real.exp p := by gcongr
    _ = Real.exp (2 * p) * ‖a‖ := by rw [show 2 * p = p + p by ring, Real.exp_add]; ring

theorem normalizedMarkedPhase_coordinate_norm_le {p : ℝ}
    (hd : (d : ℝ) ≤ p)
    (hphase : ∀ i j, rationalLogHeight (normalizedMarkedPhase F v w marked t m (e j) i) ≤ p)
    (x : ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t) :
    ‖torusPhaseLinear (normalizedMarkedPhase F v w marked t m) x‖ ≤
      Real.exp (2 * p) * ‖(e.baseChange ℝ).equivFun x‖ := by
  exact scalarExtension_coordinate_norm_le e (RationalTorus.basis t)
    (normalizedMarkedPhase F v w marked t m).toLinearMap
    (by simpa only [Fintype.card_fin] using hd)
    (fun i j => by
      change rationalLogHeight (normalizedMarkedPhase F v w marked t m (e j) i) ≤ p
      exact hphase i j) x

noncomputable def markedPhaseRemovalLinear :
    (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t) →ₗ[ℝ]
      (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t) :=
  (realMarkedParameterDirection F v w marked t).comp
    ((m : ℝ) • (-torusPhaseLinear (normalizedMarkedPhase F v w marked t m)))

theorem markedPhaseRemovalLinear_apply (x : ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t) :
    markedPhaseRemovalLinear F v w marked t m x =
      realMarkedParameterDirection F v w marked t
        ((m : ℝ) • -(torusPhaseLinear (normalizedMarkedPhase F v w marked t m) x)) := rfl

theorem markedPhaseRemovalLinear_coordinate_norm_le {p : ℝ}
    (hd : (d : ℝ) ≤ p) (ht : (t : ℝ) ≤ p) (hm : (m : ℝ) ≤ Real.exp p)
    (hdir : ∀ i j, rationalLogHeight
      (e.repr (markedQuotientDirection F v w marked t (RationalTorus.basis t i)) j) ≤ p)
    (hphase : ∀ i j, rationalLogHeight (normalizedMarkedPhase F v w marked t m (e j) i) ≤ p)
    (x : ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t) :
    ‖(e.baseChange ℝ).equivFun (markedPhaseRemovalLinear F v w marked t m x)‖ ≤
      Real.exp (5 * p) * ‖(e.baseChange ℝ).equivFun x‖ := by
  rw [markedPhaseRemovalLinear_apply]
  apply (realMarkedParameterDirection_coordinate_norm_le F v w marked t e ht hdir _).trans
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg m), norm_neg]
  calc
    Real.exp (2 * p) * ((m : ℝ) * ‖torusPhaseLinear (normalizedMarkedPhase F v w marked t m) x‖) ≤
        Real.exp (2 * p) * (Real.exp p * (Real.exp (2 * p) * ‖(e.baseChange ℝ).equivFun x‖)) := by
      gcongr
      exact normalizedMarkedPhase_coordinate_norm_le F v w marked t m e hd hphase x
    _ = _ := by
      rw [← mul_assoc, ← mul_assoc, ← Real.exp_add, ← Real.exp_add]
      congr 2
      ring

theorem markedPhaseRemovalLinear_coordinate_dist_le {p : ℝ}
    (hd : (d : ℝ) ≤ p) (ht : (t : ℝ) ≤ p) (hm : (m : ℝ) ≤ Real.exp p)
    (hdir : ∀ i j, rationalLogHeight
      (e.repr (markedQuotientDirection F v w marked t (RationalTorus.basis t i)) j) ≤ p)
    (hphase : ∀ i j, rationalLogHeight (normalizedMarkedPhase F v w marked t m (e j) i) ≤ p)
    (x y : ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t) :
    dist ((e.baseChange ℝ).equivFun (markedPhaseRemovalLinear F v w marked t m x))
      ((e.baseChange ℝ).equivFun (markedPhaseRemovalLinear F v w marked t m y)) ≤
      Real.exp (5 * p) * dist ((e.baseChange ℝ).equivFun x) ((e.baseChange ℝ).equivFun y) := by
  simpa only [map_sub, ← dist_eq_norm] using
    markedPhaseRemovalLinear_coordinate_norm_le F v w marked t m e hd ht hm hdir hphase (x - y)

variable (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1)
  (D : RationalFilteredNilmanifold (MarkedShiftQuotient F v w marked t) (s + 1) d)

theorem normalizedMarkedRetraction_coord (g : D.RealGroup) :
    (normalizedMarkedRetraction F v w marked hw hv t m D g).coord =
      lieBCH (s + 1) (markedPhaseRemovalLinear F v w marked t m g.coord) g.coord := rfl

theorem normalizedMarkedRetraction_coordinate_dist_le {p B : ℝ} {H : ℕ}
    (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) (ht : (t : ℝ) ≤ p) (hm : (m : ℝ) ≤ Real.exp p)
    (hdir : ∀ i j, rationalLogHeight
      (D.basis.repr (markedQuotientDirection F v w marked t (RationalTorus.basis t i)) j) ≤ p)
    (hphase : ∀ i j, rationalLogHeight (normalizedMarkedPhase F v w marked t m (D.basis j) i) ≤ p)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants D.basis i j k) H)
    (hB : 1 ≤ B) (g h : D.RealGroup)
    (hg : ‖(D.basis.baseChange ℝ).equivFun g.coord‖ ≤ B)
    (hh : ‖(D.basis.baseChange ℝ).equivFun h.coord‖ ≤ B) :
    dist ((D.basis.baseChange ℝ).equivFun (normalizedMarkedRetraction F v w marked hw hv t m D g).coord)
      ((D.basis.baseChange ℝ).equivFun (normalizedMarkedRetraction F v w marked hw hv t m D h).coord) ≤
      (bchBoxCoordinateBound (s + 1) d H (Real.exp (5 * p) * B) * Real.exp (5 * p)) *
        dist ((D.basis.baseChange ℝ).equivFun g.coord) ((D.basis.baseChange ℝ).equivFun h.coord) := by
  let A := Real.exp (5 * p)
  have hA : 1 ≤ A := Real.one_le_exp (by positivity)
  have hBA : B ≤ A * B := by nlinarith
  have hbox (x : D.RealGroup) (hx : ‖(D.basis.baseChange ℝ).equivFun x.coord‖ ≤ B) :
      ‖(D.basis.baseChange ℝ).equivFun (markedPhaseRemovalLinear F v w marked t m x.coord)‖ ≤ A * B :=
    (markedPhaseRemovalLinear_coordinate_norm_le F v w marked t m D.basis hd ht hm hdir hphase x.coord).trans
      (mul_le_mul_of_nonneg_left hx (Real.exp_nonneg _))
  rw [normalizedMarkedRetraction_coord, normalizedMarkedRetraction_coord, mul_assoc]
  have hbch := lieBCH_pair_coordinate_dist_le (s := s + 1)
    (D.basis.baseChange ℝ) (lieStructureConstants D.basis)
    (fun i j k => (realLieBasis_structure D.basis i j k).symm) hc
    _ _ _ _ (hB.trans hBA) (by positivity)
    (hbox g hg) (hg.trans hBA) (hbox h hh) (hh.trans hBA)
    (markedPhaseRemovalLinear_coordinate_dist_le F v w marked t m D.basis hd ht hm hdir hphase _ _)
    (le_mul_of_one_le_left dist_nonneg hA)
  simpa only [Fintype.card_fin] using hbch

theorem normalizedMarkedRetraction_coordinate_norm_le {p B : ℝ} {H : ℕ}
    (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) (ht : (t : ℝ) ≤ p) (hm : (m : ℝ) ≤ Real.exp p)
    (hdir : ∀ i j, rationalLogHeight
      (D.basis.repr (markedQuotientDirection F v w marked t (RationalTorus.basis t i)) j) ≤ p)
    (hphase : ∀ i j, rationalLogHeight (normalizedMarkedPhase F v w marked t m (D.basis j) i) ≤ p)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants D.basis i j k) H)
    (hB : 1 ≤ B) (g : D.RealGroup)
    (hg : ‖(D.basis.baseChange ℝ).equivFun g.coord‖ ≤ B) :
    ‖(D.basis.baseChange ℝ).equivFun (normalizedMarkedRetraction F v w marked hw hv t m D g).coord‖ ≤
      (bchBoxCoordinateBound (s + 1) d H (Real.exp (5 * p) * B) * Real.exp (5 * p)) * B := by
  have hzero : normalizedMarkedRetraction F v w marked hw hv t m D 1 = 1 := by
    apply NilpotentLieBCHGroup.ext
    rw [normalizedMarkedRetraction_coord, coord_one, map_zero,
      lieBCH_zero_left D.filtration.realification.lowerCentralSeries_eq_bot]
  have h := normalizedMarkedRetraction_coordinate_dist_le F v w marked t m hw hv D
    hp hd ht hm hdir hphase hc hB g 1 hg (by simpa using (show (0 : ℝ) ≤ B by linarith))
  rw [hzero, coord_one, map_zero, dist_zero_right, dist_zero_right] at h
  exact h.trans (mul_le_mul_of_nonneg_left hg (mul_nonneg
    (bchBoxCoordinateBound_nonneg _ _ _ (mul_nonneg (Real.exp_nonneg _) (by linarith))) (Real.exp_nonneg _)))

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

noncomputable def markedRetractionBoxConstant (s d H : ℕ) (p : ℝ) (B : ℝ≥0) : ℝ≥0 :=
  ⟨bchBoxCoordinateBound (s + 1) d H (Real.exp (5 * p) * B) * Real.exp (5 * p),
    mul_nonneg (bchBoxCoordinateBound_nonneg _ _ _ (mul_nonneg (Real.exp_nonneg _) B.coe_nonneg))
      (Real.exp_nonneg _)⟩

noncomputable def markedEvaluationBoxRadius (s d H : ℕ) (p : ℝ) (B : ℝ≥0) : ℝ≥0 :=
  ⟨Real.exp (2 * p), Real.exp_nonneg _⟩ * markedRetractionBoxConstant s d H p B * B + 1

noncomputable def markedLocalBoxConstant (s d H u e Ht : ℕ) (p : ℝ) (B ℓ : ℝ≥0) : ℝ≥0 :=
  ℓ * bchBoxMetricConstant u e Ht (markedEvaluationBoxRadius s d H p B) *
    ⟨Real.exp (2 * p), Real.exp_nonneg _⟩ * markedRetractionBoxConstant s d H p B

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r d e u : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1) (t m : ℕ) (hm : 0 < m)
  (D : RationalFilteredNilmanifold (MarkedShiftQuotient F v w marked t) (s + 1) d)
  (J : LieIdeal ℚ L) (hJ : markedLieSpan v w marked 0 2 0 ≤ J.toSubmodule)
  (E : RationalFilteredNilmanifold (L ⧸ J) u e)
  (hmap : ∀ z : D.RealGroup, z ∈ D.realLattice →
    (⟨(markedBaseEvaluation F v w marked t J hJ 0).baseChange ℝ z.coord⟩ : E.RealGroup) ∈ E.realLattice)

theorem markedLocalCoefficientValue_norm_le (V : E.Space → ℂ) (hV : ∀ x, ‖V x‖ ≤ 1) (g : D.RealGroup) :
    ‖markedLocalCoefficientValue F v w marked hw hv t m hm D J hJ E hmap V g‖ ≤ 1 := hV _

variable [TopologicalSpace (ℝ ⊗[ℚ] (L ⧸ J))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ J))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (L ⧸ J))] [T2Space (ℝ ⊗[ℚ] (L ⧸ J))]

theorem markedLocalCoefficientValue_coordinate_dist_le {p : ℝ} {H Ht : ℕ}
    (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) (ht : (t : ℝ) ≤ p) (hmp : (m : ℝ) ≤ Real.exp p)
    (hdir : ∀ i j, rationalLogHeight
      (D.basis.repr (markedQuotientDirection F v w marked t (RationalTorus.basis t i)) j) ≤ p)
    (hphase : ∀ i j, rationalLogHeight (normalizedMarkedPhase F v w marked t m (D.basis j) i) ≤ p)
    (heval : ∀ i j, rationalLogHeight (E.basis.repr
      (markedBaseEvaluation F v w marked t J hJ 0 (D.basis j)) i) ≤ p)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants D.basis i j k) H)
    (hct : ∀ i j k, RationalHeightLE (lieStructureConstants E.basis i j k) Ht)
    (B ℓ : ℝ≥0) (hB : 1 ≤ B) (V : E.Space → ℂ)
    (hV : letI := E.metricSpace; LipschitzWith ℓ V)
    (g h : D.RealGroup)
    (hg : ‖(D.basis.baseChange ℝ).equivFun g.coord‖ ≤ B)
    (hh : ‖(D.basis.baseChange ℝ).equivFun h.coord‖ ≤ B) :
    dist (markedLocalCoefficientValue F v w marked hw hv t m hm D J hJ E hmap V g)
      (markedLocalCoefficientValue F v w marked hw hv t m hm D J hJ E hmap V h) ≤
        markedLocalBoxConstant s d H u e Ht p B ℓ *
          dist ((D.basis.baseChange ℝ).equivFun g.coord) ((D.basis.baseChange ℝ).equivFun h.coord) := by
  let := rightMetricSpace (hnil := E.filtration.realification.lowerCentralSeries_eq_bot) (E.basis.baseChange ℝ)
  let := E.metricSpace
  let q := markedBaseEvaluation F v w marked t J hJ 0
  let a (x : D.RealGroup) : E.RealGroup :=
    ⟨q.baseChange ℝ (normalizedMarkedRetraction F v w marked hw hv t m D x).coord⟩
  let R := markedRetractionBoxConstant s d H p B
  let T := markedEvaluationBoxRadius s d H p B
  let Δ := dist ((D.basis.baseChange ℝ).equivFun g.coord) ((D.basis.baseChange ℝ).equivFun h.coord)
  have hT : 1 ≤ T := by
    dsimp only [T, markedEvaluationBoxRadius]
    exact le_add_of_nonneg_left (by positivity)
  have hB' : (1 : ℝ) ≤ B := hB
  have hnorm (x : D.RealGroup) (hx : ‖(D.basis.baseChange ℝ).equivFun x.coord‖ ≤ B) :
      ‖(E.basis.baseChange ℝ).equivFun (a x).coord‖ ≤ T := by
    have hr := normalizedMarkedRetraction_coordinate_norm_le F v w marked t m hw hv D
      hp hd ht hmp hdir hphase hc hB' x hx
    have he := scalarExtension_coordinate_norm_le D.basis E.basis q
      (by simpa only [Fintype.card_fin] using hd) heval
      (normalizedMarkedRetraction F v w marked hw hv t m D x).coord
    change ‖(E.basis.baseChange ℝ).equivFun (a x).coord‖ ≤
      Real.exp (2 * p) * (R : ℝ) * B + 1
    calc
      _ ≤ Real.exp (2 * p) * ‖(D.basis.baseChange ℝ).equivFun
          (normalizedMarkedRetraction F v w marked hw hv t m D x).coord‖ := he
      _ ≤ Real.exp (2 * p) * ((R : ℝ) * B) := mul_le_mul_of_nonneg_left hr (Real.exp_nonneg _)
      _ ≤ _ := by ring_nf; linarith
  have hevaldist : dist ((E.basis.baseChange ℝ).equivFun (a g).coord)
      ((E.basis.baseChange ℝ).equivFun (a h).coord) ≤ Real.exp (2 * p) * (R : ℝ) * Δ := by
    have hr := normalizedMarkedRetraction_coordinate_dist_le F v w marked t m hw hv D
      hp hd ht hmp hdir hphase hc hB' g h hg hh
    have he := scalarExtension_coordinate_dist_le D.basis E.basis q
      (by simpa only [Fintype.card_fin] using hd) heval
      (normalizedMarkedRetraction F v w marked hw hv t m D g).coord
      (normalizedMarkedRetraction F v w marked hw hv t m D h).coord
    exact he.trans ((mul_le_mul_of_nonneg_left hr (Real.exp_nonneg _)).trans_eq (mul_assoc _ _ _).symm)
  have hgroup : dist (a g) (a h) ≤ bchBoxMetricConstant u e Ht T * (Real.exp (2 * p) * (R : ℝ) * Δ) := by
    have hb := dist_le_bchBoxMetricConstant (E.basis.baseChange ℝ) (lieStructureConstants E.basis)
      (fun i j k => (realLieBasis_structure E.basis i j k).symm) hct T hT
      (show 0 ≤ Real.exp (2 * p) * (R : ℝ) * Δ by dsimp [Δ]; positivity) (a g) (a h)
      (fun i => by
        calc
          _ ≤ ‖(E.basis.baseChange ℝ).equivFun (a g).coord‖ := by
            simpa only [Real.norm_eq_abs, Basis.equivFun_apply] using
              norm_le_pi_norm ((E.basis.baseChange ℝ).equivFun (a g).coord) i
          _ ≤ T := hnorm g hg)
      (fun i => by
        calc
          _ ≤ ‖(E.basis.baseChange ℝ).equivFun (a h).coord‖ := by
            simpa only [Real.norm_eq_abs, Basis.equivFun_apply] using
              norm_le_pi_norm ((E.basis.baseChange ℝ).equivFun (a h).coord) i
          _ ≤ T := hnorm h hh)
      (fun i => by
        calc
          _ ≤ dist ((E.basis.baseChange ℝ).equivFun (a g).coord)
              ((E.basis.baseChange ℝ).equivFun (a h).coord) := by
            simpa only [Real.dist_eq, Basis.equivFun_apply] using
              dist_le_pi_dist ((E.basis.baseChange ℝ).equivFun (a g).coord)
                ((E.basis.baseChange ℝ).equivFun (a h).coord) i
          _ ≤ _ := hevaldist)
    simpa only [Fintype.card_fin] using hb
  have hproj := quotientMetricSpace_lipschitz_mk (E.basis.baseChange ℝ) E.realLattice E.realLattice_closed_discrete.1
  have hvalue := (hV.comp hproj).dist_le_mul (a g) (a h)
  simp only [Function.comp_apply, mul_one] at hvalue
  change dist (V (QuotientGroup.mk (a g))) (V (QuotientGroup.mk (a h))) ≤ _
  apply hvalue.trans
  apply (mul_le_mul_of_nonneg_left hgroup ℓ.coe_nonneg).trans_eq
  change (ℓ : ℝ) * ((bchBoxMetricConstant u e Ht T : ℝ) * (Real.exp (2 * p) * (R : ℝ) * Δ)) =
    (((ℓ : ℝ) * (bchBoxMetricConstant u e Ht T : ℝ) * Real.exp (2 * p)) * (R : ℝ)) * Δ
  ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativeProperAffineRecovery
namespace OAI

section

namespace Erdos3.FreimanModel

def residueBlock {q : ℕ} [NeZero q] (x : ZMod q) : Fin 16 := by
  refine ⟨x.val / (q / 16 + 1), ?_⟩
  apply (Nat.div_lt_iff_lt_mul (Nat.succ_pos _)).mpr
  exact x.val_lt.trans (Nat.lt_mul_div_succ q (by decide))

def residueLift {q : ℕ} (x : ZMod q) : ℤ := x.val

theorem residueBlock_bounds {q : ℕ} [NeZero q] {x : ZMod q} {c : Fin 16}
    (hc : residueBlock x = c) :
    c.val * (q / 16 + 1) ≤ x.val ∧
      x.val ≤ c.val * (q / 16 + 1) + q / 16 := by
  have hdiv : x.val / (q / 16 + 1) = c.val := congrArg Fin.val hc
  have hmod := Nat.mod_lt x.val (Nat.succ_pos (q / 16))
  have hrem : x.val % (q / 16 + 1) ≤ q / 16 := Nat.le_of_lt_succ hmod
  have hid := Nat.mod_add_div x.val (q / 16 + 1)
  rw [hdiv, Nat.mul_comm (q / 16 + 1)] at hid
  omega

theorem residueLift_sum_cast {q : ℕ} [NeZero q] (T : Multiset (ZMod q)) :
    (((T.map residueLift).sum : ℤ) : ZMod q) = T.sum := by
  induction T using Multiset.induction_on with
  | empty => simp
  | @cons x T ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons, Int.cast_add, ih]
      simp [residueLift]

theorem residueLift_sum_bounds {q : ℕ} [NeZero q] {c : Fin 16}
    (T : Multiset (ZMod q)) (hT : T.card = 8)
    (hc : ∀ x ∈ T, residueBlock x = c) :
    (8 : ℤ) * (c.val * (q / 16 + 1) : ℕ) ≤ (T.map residueLift).sum ∧
      (T.map residueLift).sum ≤
        (8 : ℤ) * ((c.val * (q / 16 + 1) : ℕ) + (q / 16 : ℕ)) := by
  have hlo := Multiset.card_nsmul_le_sum
    (s := T.map residueLift) (a := ((c.val * (q / 16 + 1) : ℕ) : ℤ)) (by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hy
      change ((c.val * (q / 16 + 1) : ℕ) : ℤ) ≤ (x.val : ℤ)
      exact_mod_cast (residueBlock_bounds (hc x hx)).1)
  have hhi := Multiset.sum_le_card_nsmul
    (s := T.map residueLift) (n := (((c.val * (q / 16 + 1) : ℕ) + (q / 16 : ℕ)) : ℤ)) (by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hy
      change (x.val : ℤ) ≤ (((c.val * (q / 16 + 1) : ℕ) + (q / 16 : ℕ)) : ℤ)
      exact_mod_cast (residueBlock_bounds (hc x hx)).2)
  simpa only [Multiset.card_map, hT, nsmul_eq_mul, Nat.cast_add, Nat.cast_ofNat]
    using And.intro hlo hhi

theorem residueLift_sum_sub_abs_lt {q : ℕ} [NeZero q] {c : Fin 16}
    (T U : Multiset (ZMod q)) (hT : T.card = 8) (hU : U.card = 8)
    (hcT : ∀ x ∈ T, residueBlock x = c) (hcU : ∀ x ∈ U, residueBlock x = c) :
    |(T.map residueLift).sum - (U.map residueLift).sum| < (q : ℤ) := by
  obtain ⟨hTlo, hThi⟩ := residueLift_sum_bounds T hT hcT
  obtain ⟨hUlo, hUhi⟩ := residueLift_sum_bounds U hU hcU
  have hdiv : (16 : ℤ) * (q / 16 : ℕ) ≤ q := by
    exact_mod_cast Nat.mul_div_le q 16
  have hq : (0 : ℤ) < q := by exact_mod_cast NeZero.pos q
  rw [abs_lt]
  constructor <;> omega

theorem residueLift_sum_eq_iff {q : ℕ} [NeZero q] {c : Fin 16}
    (T U : Multiset (ZMod q)) (hT : T.card = 8) (hU : U.card = 8)
    (hcT : ∀ x ∈ T, residueBlock x = c) (hcU : ∀ x ∈ U, residueBlock x = c) :
    (T.map residueLift).sum = (U.map residueLift).sum ↔ T.sum = U.sum := by
  constructor
  · intro h
    simpa only [residueLift_sum_cast] using congrArg (fun z : ℤ => (z : ZMod q)) h
  · intro h
    have hsmall := abs_lt.mp (residueLift_sum_sub_abs_lt T U hT hU hcT hcU)
    have hdiv : (q : ℤ) ∣ (T.map residueLift).sum - (U.map residueLift).sum := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp
      rw [Int.cast_sub, residueLift_sum_cast, residueLift_sum_cast, h, sub_self]
    apply sub_eq_zero.mp
    apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdiv
    simpa only [Int.natAbs_natCast] using
      int_natAbs_lt_of_neg_lt_and_lt hsmall.1 hsmall.2

end Erdos3.FreimanModel

end

section

namespace Erdos3.FreimanModel

variable {I : Type*} (q : I → ℕ) [∀ i, NeZero (q i)]

def cyclicProductLift (x : ∀ i, ZMod (q i)) : I → ℤ := fun i => residueLift (x i)

def cyclicProductBlock (x : ∀ i, ZMod (q i)) : I → Fin 16 := fun i => residueBlock (x i)

theorem cyclicProductLift_injective : Function.Injective (cyclicProductLift q) := by
  intro x y h
  funext i
  have hi := congrArg (fun z : ℤ => (z : ZMod (q i))) (congrFun h i)
  simpa [cyclicProductLift, residueLift] using hi

omit [∀ i, NeZero (q i)] in
theorem cyclicProductLift_sum_apply (T : Multiset (∀ i, ZMod (q i))) (i : I) :
    ((T.map (cyclicProductLift q)).sum) i = (T.map fun x => residueLift (x i)).sum := by
  induction T using Multiset.induction_on with
  | empty => simp
  | @cons x T ih => simp [ih, cyclicProductLift]

omit [∀ i, NeZero (q i)] in
theorem cyclicProduct_sum_apply (T : Multiset (∀ i, ZMod (q i))) (i : I) :
    T.sum i = (T.map fun x => x i).sum := by
  induction T using Multiset.induction_on with
  | empty => simp
  | @cons x T ih => simp [ih]

theorem cyclicProductLift_sum_eq_iff {c : I → Fin 16}
    (T U : Multiset (∀ i, ZMod (q i))) (hT : T.card = 8) (hU : U.card = 8)
    (hcT : ∀ x ∈ T, cyclicProductBlock q x = c)
    (hcU : ∀ x ∈ U, cyclicProductBlock q x = c) :
    (T.map (cyclicProductLift q)).sum = (U.map (cyclicProductLift q)).sum ↔ T.sum = U.sum := by
  have hi (i : I) :
      ((T.map (cyclicProductLift q)).sum) i = ((U.map (cyclicProductLift q)).sum) i ↔
        T.sum i = U.sum i := by
    rw [cyclicProductLift_sum_apply, cyclicProductLift_sum_apply,
      cyclicProduct_sum_apply, cyclicProduct_sum_apply]
    have ht : ∀ x ∈ T.map (fun x => x i), residueBlock x = c i := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
      exact congrFun (hcT y hy) i
    have hu : ∀ x ∈ U.map (fun x => x i), residueBlock x = c i := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
      exact congrFun (hcU y hy) i
    simpa only [Multiset.map_map, Function.comp_def] using
      residueLift_sum_eq_iff (T.map fun x => x i) (U.map fun x => x i)
        (by simpa only [Multiset.card_map] using hT)
        (by simpa only [Multiset.card_map] using hU) ht hu
  constructor
  · intro h
    funext i
    exact (hi i).mp (congrFun h i)
  · intro h
    funext i
    exact (hi i).mpr (congrFun h i)

theorem isAddFreimanIso_cyclicProductLift [Fintype I]
    (A : Finset (∀ i, ZMod (q i))) {c : I → Fin 16}
    (hc : ∀ x ∈ A, cyclicProductBlock q x = c) :
    IsAddFreimanIso 8 (A : Set _) (A.image (cyclicProductLift q) : Set (I → ℤ))
      (cyclicProductLift q) := by
  refine ⟨⟨?_, (cyclicProductLift_injective q).injOn, ?_⟩, ?_⟩
  · intro x hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  · intro x hx
    exact Finset.mem_image.mp hx
  · intro T U hTA hUA hT hU
    exact cyclicProductLift_sum_eq_iff q T U hT hU
      (fun x hx => hc x (hTA hx)) (fun x hx => hc x (hUA hx))

theorem exists_large_cyclicProduct_integer_lift [Fintype I]
    (A : Finset (∀ i, ZMod (q i))) (hA : A.Nonempty) :
    ∃ J : Finset (∀ i, ZMod (q i)), J.Nonempty ∧ J ⊆ A ∧
      A.card ≤ 16 ^ Fintype.card I * J.card ∧
      IsAddFreimanIso 8 (J : Set _) (J.image (cyclicProductLift q) : Set (I → ℤ))
        (cyclicProductLift q) := by
  classical
  obtain ⟨c, hJ, hsize⟩ := exists_nonempty_large_fiber A hA (cyclicProductBlock q)
  let J := A.filter fun x => cyclicProductBlock q x = c
  refine ⟨J, hJ, Finset.filter_subset _ _, ?_, ?_⟩
  · simpa only [Fintype.card_fun, Fintype.card_fin] using hsize
  · apply isAddFreimanIso_cyclicProductLift q J
    intro x hx
    exact (Finset.mem_filter.mp hx).2

end Erdos3.FreimanModel

end

section

namespace Erdos3.FreimanModel

open scoped Pointwise

theorem exists_dense_cyclic_model_of_integer_vectors {I : Type*} [Fintype I]
    (A : Finset (I → ℤ)) (hA : A.Nonempty) {K : ℝ} (hK : 0 < K)
    (hsmall : ((A - A).card : ℝ) ≤ K * A.card) (s : ℕ) (hs : 0 < s) :
    ∃ (N : ℕ) (J : Finset (I → ℤ)) (B : Finset (ZMod N)) (f : (I → ℤ) → ZMod N),
      0 < N ∧ J.Nonempty ∧ J ⊆ A ∧ A.card ≤ (2 * s) * J.card ∧
      B.Nonempty ∧ B = J.image f ∧ B.card = J.card ∧
      IsAddFreimanIso s (J : Set _) (B : Set _) f ∧
      (N : ℝ) ≤ 2 * K ^ (2 * s) * A.card ∧
      (4 * (s : ℝ) * K ^ (2 * s))⁻¹ ≤ (B.card : ℝ) / N := by
  classical
  obtain ⟨e, he⟩ := exists_integer_freiman_embedding A s
  let X := A.image e
  have hX : X.Nonempty := hA.image e
  have hXcard : X.card = A.card := Finset.card_image_of_injOn he.bijOn.injOn
  have hXsmall : ((X - X).card : ℝ) ≤ K * X.card := by
    have hdiff : X - X = (A - A).image e := by
      ext z
      simp only [X, Finset.mem_sub, Finset.mem_image]
      constructor
      · rintro ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
        exact ⟨x - y, ⟨x, hx, y, hy, rfl⟩, e.map_sub x y⟩
      · rintro ⟨_, ⟨x, hx, y, hy, rfl⟩, rfl⟩
        exact ⟨e x, ⟨x, hx, rfl⟩, e y, ⟨y, hy, rfl⟩, (e.map_sub x y).symm⟩
    rw [hdiff, hXcard]
    exact (show (((A - A).image e).card : ℝ) ≤ (A - A).card by
      exact_mod_cast Finset.card_image_le).trans hsmall
  obtain ⟨N, X', B, g, hN, hX'ne, hX'sub, hsize, hBne, hB, hBcard,
      hg, hNsize, hdensity⟩ := exists_dense_cyclic_model X hX hK hXsmall s hs
  let J := A.filter fun x => e x ∈ X'
  have hJA : J ⊆ A := Finset.filter_subset _ _
  have hJimage : J.image e = X' := by
    ext z
    constructor
    · rintro hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      exact (Finset.mem_filter.mp hx).2
    · intro hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (hX'sub hz)
      exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hz⟩, rfl⟩
  have heJ : IsAddFreimanIso s (J : Set _) (X' : Set ℤ) e := by
    apply he.subset hJA
    refine ⟨?_, he.bijOn.injOn.mono hJA, ?_⟩
    · intro x hx
      exact (Finset.mem_filter.mp hx).2
    · intro z hz
      rw [← hJimage] at hz
      exact Finset.mem_image.mp hz
  have hJcard : X'.card = J.card := by
    rw [← hJimage]
    exact Finset.card_image_of_injOn heJ.bijOn.injOn
  have hJne : J.Nonempty := by
    apply Finset.card_pos.mp
    rw [← hJcard]
    exact hX'ne.card_pos
  have hJsize : A.card ≤ (2 * s) * J.card := by
    simpa only [hXcard, hJcard] using hsize
  have hBimage : B = J.image (g ∘ e) := by
    rw [hB, ← hJimage, Finset.image_image]
  have hNsize' : (N : ℝ) ≤ 2 * K ^ (2 * s) * A.card := by
    simpa only [hXcard] using hNsize
  exact ⟨N, J, B, g ∘ e, hN, hJne, hJA, hJsize, hBne, hBimage,
    hBcard.trans hJcard, hg.comp heJ, hNsize', hdensity⟩

end Erdos3.FreimanModel

end

section

namespace Erdos3.FreimanModel

open scoped Pointwise

theorem exists_dense_cyclicProduct_integer_model {I : Type*} [Fintype I]
    (q : I → ℕ) [∀ i, NeZero (q i)] (A : Finset (∀ i, ZMod (q i)))
    (hA : A.Nonempty) {K : ℝ} (hK : 0 < K)
    (hsmall : ((A - A).card : ℝ) ≤ K * A.card) :
    ∃ (N : ℕ) (J : Finset (∀ i, ZMod (q i))) (B : Finset (ZMod N))
      (g : (I → ℤ) → ZMod N),
      0 < N ∧ J.Nonempty ∧ J ⊆ A ∧
      A.card ≤ 16 ^ (Fintype.card I + 1) * J.card ∧
      B.Nonempty ∧ B = (J.image (cyclicProductLift q)).image g ∧ B.card = J.card ∧
      IsAddFreimanIso 8 (J : Set _) (J.image (cyclicProductLift q) : Set (I → ℤ))
        (cyclicProductLift q) ∧
      IsAddFreimanIso 8 (J.image (cyclicProductLift q) : Set (I → ℤ)) (B : Set _) g ∧
      (N : ℝ) ≤ 2 * (K * 16 ^ Fintype.card I) ^ 16 * A.card ∧
      (32 * (K * 16 ^ Fintype.card I) ^ 16)⁻¹ ≤ (B.card : ℝ) / N := by
  classical
  obtain ⟨A₀, hA₀, hA₀A, hlarge, he⟩ := exists_large_cyclicProduct_integer_lift q A hA
  let e := cyclicProductLift q
  let X := A₀.image e
  let R : ℝ := K * 16 ^ Fintype.card I
  have hR : 0 < R := mul_pos hK (by positivity)
  have hX : X.Nonempty := hA₀.image e
  have hXcard : X.card = A₀.card := Finset.card_image_of_injOn he.bijOn.injOn
  have hdiff : (X - X).card = (A₀ - A₀).card :=
    card_difference_image_of_freiman A₀ e (he.mono (hmn := by decide))
  have hsub : A₀ - A₀ ⊆ A - A := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_sub.mp hx
    exact Finset.mem_sub.mpr ⟨a, hA₀A ha, b, hA₀A hb, rfl⟩
  have hlargeR : (A.card : ℝ) ≤ 16 ^ Fintype.card I * A₀.card := by
    exact_mod_cast hlarge
  have hXsmall : ((X - X).card : ℝ) ≤ R * X.card := by
    rw [hdiff, hXcard]
    calc
      ((A₀ - A₀).card : ℝ) ≤ (A - A).card := by exact_mod_cast Finset.card_le_card hsub
      _ ≤ K * A.card := hsmall
      _ ≤ K * (16 ^ Fintype.card I * A₀.card) := mul_le_mul_of_nonneg_left hlargeR hK.le
      _ = R * A₀.card := by simp only [R, mul_assoc]
  obtain ⟨N, X', B, g, hN, hX', hX'X, hsize, hB, hBimage, hBcard, hg, hNsize, hdensity⟩ :=
    exists_dense_cyclic_model_of_integer_vectors X hX hR hXsmall 8 (by decide)
  let J := A₀.filter fun x => e x ∈ X'
  have hJA₀ : J ⊆ A₀ := Finset.filter_subset _ _
  have hJimage : J.image e = X' := by
    ext z
    constructor
    · intro hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      exact (Finset.mem_filter.mp hx).2
    · intro hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (hX'X hz)
      exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hz⟩, rfl⟩
  have heJ : IsAddFreimanIso 8 (J : Set _) (X' : Set (I → ℤ)) e := by
    apply he.subset hJA₀
    refine ⟨?_, he.bijOn.injOn.mono hJA₀, ?_⟩
    · intro x hx
      exact (Finset.mem_filter.mp hx).2
    · intro z hz
      rw [← hJimage] at hz
      exact Finset.mem_image.mp hz
  have hJcard : X'.card = J.card := by
    rw [← hJimage]
    exact Finset.card_image_of_injOn heJ.bijOn.injOn
  have hJ : J.Nonempty := by
    apply Finset.card_pos.mp
    rw [← hJcard]
    exact hX'.card_pos
  have hsize₀ : A₀.card ≤ 16 * J.card := by
    simpa only [hXcard, hJcard, Nat.reduceMul] using hsize
  have hsize' : A.card ≤ 16 ^ (Fintype.card I + 1) * J.card := by
    calc
      A.card ≤ 16 ^ Fintype.card I * A₀.card := hlarge
      _ ≤ 16 ^ Fintype.card I * (16 * J.card) := Nat.mul_le_mul_left _ hsize₀
      _ = _ := by rw [pow_succ, mul_assoc]
  have hBimage' : B = (J.image e).image g := by
    rw [hJimage]
    exact hBimage
  have hNsize' : (N : ℝ) ≤ 2 * R ^ 16 * A.card := by
    have hcard : (X.card : ℝ) ≤ A.card := by rw [hXcard]; exact_mod_cast Finset.card_le_card hA₀A
    have hn : (N : ℝ) ≤ 2 * R ^ 16 * X.card := by
      simpa only [Nat.reduceMul] using hNsize
    exact hn.trans
      (mul_le_mul_of_nonneg_left hcard (by positivity))
  refine ⟨N, J, B, g, hN, hJ, hJA₀.trans hA₀A, hsize', hB, hBimage',
    hBcard.trans hJcard, ?_, ?_, hNsize', ?_⟩
  · change IsAddFreimanIso 8 (J : Set _) (J.image e : Set (I → ℤ)) e
    rw [hJimage]
    exact heJ
  · change IsAddFreimanIso 8 (J.image e : Set (I → ℤ)) (B : Set _) g
    rw [hJimage]
    exact hg
  · norm_num only [Nat.reduceMul, Nat.cast_ofNat, mul_one] at hdensity
    simpa only [R, show (4 : ℝ) * 8 = 32 by norm_num] using hdensity

end Erdos3.FreimanModel

end

section

namespace Erdos3.FreimanModel

open scoped Pointwise

variable {I : Type*}

def variableIntegerGraphLift (N : ℕ) (M : I → ℕ)
    (x : ZMod N × (∀ i, ZMod (M i))) : Option I → ℤ :=
  cyclicProductLift (variableRoundedGraphModuli N M)
    (variableRoundedGraphCoordinateEquiv N M x)

def variableIntegerGraphReduction (N : ℕ) (M : I → ℕ) :
    (Option I → ℤ) →+ (ZMod N × (∀ i, ZMod (M i))) where
  toFun z := ((z none : ZMod N), fun i => (z (some i) : ZMod (M i)))
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp

@[simp] theorem variableIntegerGraphReduction_lift (N : ℕ) (M : I → ℕ)
    [NeZero N] [∀ i, NeZero (M i)] (x : ZMod N × (∀ i, ZMod (M i))) :
    variableIntegerGraphReduction N M (variableIntegerGraphLift N M x) = x := by
  apply Prod.ext
  · change (((x.1.val : ℤ) : ZMod N)) = x.1
    simp only [Int.cast_natCast, ZMod.natCast_zmod_val]
  · funext i
    change ((((x.2 i).val : ℤ) : ZMod (M i))) = x.2 i
    simp only [Int.cast_natCast, ZMod.natCast_zmod_val]

@[simp] theorem variableIntegerGraphLift_none (N : ℕ) (M : I → ℕ)
    (x : ZMod N × (∀ i, ZMod (M i))) :
    variableIntegerGraphLift N M x none = (x.1.val : ℤ) := rfl

@[simp] theorem variableIntegerGraphLift_some (N : ℕ) (M : I → ℕ)
    (x : ZMod N × (∀ i, ZMod (M i))) (i : I) :
    variableIntegerGraphLift N M x (some i) = ((x.2 i).val : ℤ) := rfl

theorem exists_variableIntegerGraph_cyclic_model [Fintype I]
    (N : ℕ) (M : I → ℕ) [NeZero N] [∀ i, NeZero (M i)]
    (A : Finset (ZMod N × (∀ i, ZMod (M i)))) (hA : A.Nonempty)
    {K : ℝ} (hK : 0 < K) (hsmall : ((A - A).card : ℝ) ≤ K * A.card) :
    ∃ (Q : ℕ) (S : Finset (Option I → ℤ)) (B : Finset (ZMod Q))
      (g : (Option I → ℤ) → ZMod Q),
      0 < Q ∧ S.Nonempty ∧ S ⊆ A.image (variableIntegerGraphLift N M) ∧
      A.card ≤ 16 ^ (Fintype.card I + 2) * S.card ∧
      B.Nonempty ∧ B = S.image g ∧ B.card = S.card ∧
      IsAddFreimanIso 8 (S : Set _) (B : Set _) g ∧
      (Q : ℝ) ≤ 2 * (K * 16 ^ (Fintype.card I + 1)) ^ 16 * A.card ∧
      (32 * (K * 16 ^ (Fintype.card I + 1)) ^ 16)⁻¹ ≤ (B.card : ℝ) / Q := by
  classical
  let q : Option I → ℕ := variableRoundedGraphModuli N M
  let _ : ∀ i, NeZero (q i) := variableRoundedGraphModuli_neZero N M
  let e := variableRoundedGraphCoordinateEquiv (I := I) N M
  let X := A.image e
  have he : IsAddFreimanIso 8 (A : Set _) (X : Set _) e :=
    isAddFreimanIso_of_injOn_iterated_sums e.toAddMonoidHom A 8
      e.injective.injOn e.injective.injOn
  have hX : X.Nonempty := hA.image e
  have hXcard : X.card = A.card := Finset.card_image_of_injOn e.injective.injOn
  have hXsmall : ((X - X).card : ℝ) ≤ K * X.card := by
    rw [card_difference_image_of_freiman A e (he.mono (hmn := by decide)), hXcard]
    exact hsmall
  obtain ⟨Q, J, B, g, hQ, hJ, hJX, hsize, hB, hBimage, hBcard, hlift, hg,
      hQsize, hdensity⟩ := exists_dense_cyclicProduct_integer_model q X hX hK hXsmall
  let S := J.image (cyclicProductLift q)
  have hScard : S.card = J.card := Finset.card_image_of_injOn hlift.bijOn.injOn
  have hSA : S ⊆ A.image (variableIntegerGraphLift N M) := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp (hJX hx)
    exact Finset.mem_image.mpr ⟨y, hy, rfl⟩
  refine ⟨Q, S, B, g, hQ, hJ.image _, hSA, ?_, hB, hBimage,
    hBcard.trans hScard.symm, hg, ?_, ?_⟩
  · simpa only [hXcard, hScard, Fintype.card_option, Nat.add_assoc] using hsize
  · simpa only [hXcard, Fintype.card_option] using hQsize
  · simpa only [Fintype.card_option] using hdensity

end Erdos3.FreimanModel

end

section

namespace Erdos3.FreimanModel

open scoped Pointwise BigOperators
open CyclicCrootSisask

theorem exists_bounded_affine_box_of_cyclic_model {G : Type*} [AddCommGroup G] [DecidableEq G]
    {Q : ℕ} [NeZero Q] (A : Finset G) (hA : A.Nonempty) (B : Finset (ZMod Q))
    (hB : B.Nonempty) (f : G → ZMod Q) (hf : IsAddFreimanIso 8 (A : Set _) (B : Set _) f)
    {p : ℝ} (hp : 0 ≤ p) (hdensity : Real.exp (-p) * Q ≤ (B.card : ℝ)) :
    ∃ F ⊆ A, F.Nonempty ∧
      Real.exp (-(quarticBogolyubovProgressionConstant * (p + 1) ^ 8)) * A.card ≤ (F.card : ℝ) ∧
      ∃ (r : ℕ) (R : Fin r → ℕ) (Φ : (Fin r → ℤ) →+ G) (base : G),
        (r : ℝ) ≤ 2 + quarticBogolyubovConstant * (p + 1) ^ 4 ∧
        (∏ i, (2 * R i + 1)) ≤ Q ∧
        Set.InjOn Φ {x | ∀ i, |x i| ≤ (R i : ℤ)} ∧
        ∀ a ∈ F, ∃ x : Fin r → ℤ, (∀ i, |x i| ≤ (R i : ℤ)) ∧ a = base + Φ x := by
  classical
  obtain ⟨T, hrank, hT, hTsub, hTsize⟩ := exists_quartic_bogolyubov_progression B hp hdensity
  obtain ⟨L, hmap, hinj, hzero, hadd⟩ := exists_fourfold_lift_of_eight_iso A B hB f hf
  have hpair (x y z t : T.Param) (h : T.eval x + T.eval y = T.eval z + T.eval t) :
      L (T.eval x) + L (T.eval y) = L (T.eval z) + L (T.eval t) :=
    (hadd _ (hTsub (T.eval_mem_carrier x)) _ (hTsub (T.eval_mem_carrier y))
      _ (hTsub (T.eval_mem_carrier z)) _ (hTsub (T.eval_mem_carrier t))).mpr h
  let Φ := T.freimanHom L
  let S := T.coefficientBox.image Φ
  have hS : S ⊆ 2 • A - 2 • A := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨y, rfl⟩ := T.mem_coefficientBox.mp hx
    change T.freimanHom L (T.coeff y) ∈ _
    rw [T.freimanHom_coeff L hzero hpair]
    exact hmap (hTsub (T.eval_mem_carrier y))
  have hScard : S.card = T.carrier.card := by
    change (T.coefficientBox.image (T.freimanHom L)).card = T.carrier.card
    rw [T.image_freimanHom L hzero hpair]
    exact Finset.card_image_of_injOn (hinj.mono hTsub)
  have hbound : ((A - S).card : ℝ) ≤ (Q : ℝ) := by
    have h := card_sub_le_of_fourfold_subset A S f (hf.mono (hmn := by decide)) hS
    have h' : (A - S).card ≤ Q := by simpa only [ZMod.card] using h
    exact_mod_cast h'
  have hsize : Real.exp (-(quarticBogolyubovProgressionConstant * (p + 1) ^ 8)) * Q ≤
      (S.card : ℝ) := by rw [hScard]; exact hTsize
  obtain ⟨base, _hbase, F, hFA, hF, hFsize, hFsub⟩ := exists_dense_translate A S hA
    (Real.exp_pos _) (by exact_mod_cast NeZero.pos Q) hbound hsize
  refine ⟨F, hFA, hF, hFsize, T.rank, T.radius, Φ, base, hrank, ?_, ?_, ?_⟩
  · rw [← T.card_carrier_of_proper hT]
    simpa only [ZMod.card] using Finset.card_le_univ T.carrier
  · intro x hx y hy hxy
    exact T.freimanHom_injOn hT L (hinj.mono hTsub) hzero hpair
      (T.mem_coefficientBox_iff_abs_le.mpr hx) (T.mem_coefficientBox_iff_abs_le.mpr hy) hxy
  · intro a ha
    obtain ⟨x, hx, heq⟩ := Finset.mem_image.mp (hFsub a ha)
    refine ⟨x, T.mem_coefficientBox_iff_abs_le.mp hx, ?_⟩
    rw [heq]
    abel

end Erdos3.FreimanModel

end

section

namespace Erdos3.NativeRankRelation.CommonData

open scoped Pointwise BigOperators
open CyclicCrootSisask

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

theorem integer_graph_affine_model {I : Type*} [Fintype I]
    (a : ZMod N → I → ℝ) (c : I → ℝ) (M l : I → ℕ) [∀ i, NeZero (M i)] (ε : I → ℝ)
    (hsmall : ∀ i, (M i : ℝ) * l i * ε i ≤ 1)
    (hnear : ∀ t ∈ D.quadruples, ∃ q ∈ coordinateDenominatorGrid l,
      ∀ i, |c i + (a (rankQuadrupleParameters t 1) i + a (rankQuadrupleParameters t 2) i -
        a (rankQuadrupleParameters t 0) i - a (rankQuadrupleParameters t 3) i) - q i| ≤ ε i) :
    let K := Real.exp (P + 13 * Fintype.card I)
    let z := roundedModelLogBudget P (Fintype.card I)
    let δ := Real.exp (-(quarticBogolyubovProgressionConstant * (z + 1) ^ 8))
    let v := fun h => variableRoundedCoefficient M l (a h)
    ∃ J' ⊆ H, J'.Nonempty ∧
      δ * ((2 ^ 4 : ℝ)⁻¹ * K⁻¹ * H.card) ≤ 16 ^ (Fintype.card I + 2) * (J'.card : ℝ) ∧
      ∃ (r : ℕ) (R : Fin r → ℕ)
        (Φ : (Fin r → ℤ) →+ (Option I → ℤ))
        (base : Option I → ℤ),
        (r : ℝ) ≤ 2 + quarticBogolyubovConstant * (z + 1) ^ 4 ∧
        ((∏ i, (2 * R i + 1) : ℕ) : ℝ) ≤
          2 * ((2 ^ 14 : ℝ) * K ^ 6 * 16 ^ (Fintype.card I + 1)) ^ 16 * H.card ∧
        Set.InjOn Φ {x | ∀ i, |x i| ≤ (R i : ℤ)} ∧
        ∀ h ∈ J', ∃ x : Fin r → ℤ,
          (∀ i, |x i| ≤ (R i : ℤ)) ∧
            FreimanModel.variableIntegerGraphLift N M (h, v h) = base + Φ x := by
  intro K z δ v
  classical
  obtain ⟨J, hJH, hJ, hsize, hsmallJ⟩ :=
    D.variable_graph_small_difference a c M l ε hsmall hnear
  let A := additiveGraph J v
  have hA : A.Nonempty := hJ.image _
  have hAsmall : ((A - A).card : ℝ) ≤ (2 ^ 14 : ℝ) * K ^ 6 * A.card := by
    simpa only [A, additiveGraph_card] using hsmallJ
  obtain ⟨Q, S, B, f, hQ, hS, hSA, hASsize, hB, _hBimage, _hBcard, hf,
      hQsize, hdensity⟩ :=
    FreimanModel.exists_variableIntegerGraph_cyclic_model N M A hA
      (by dsimp [K]; positivity) hAsmall
  let _ : NeZero Q := ⟨hQ.ne'⟩
  have hdensity' : Real.exp (-z) * Q ≤ (B.card : ℝ) := by
    apply (le_div_iff₀ (by exact_mod_cast hQ : (0 : ℝ) < Q)).mp
    exact (exp_neg_roundedModelLogBudget_le_density P (Fintype.card I)).trans hdensity
  obtain ⟨F, hFS, hF, hFsize, r, R, Φ, base, hrank, hbox, hinj, hrepr⟩ :=
    FreimanModel.exists_bounded_affine_box_of_cyclic_model S hS B hB f hf
      (roundedModelLogBudget_nonneg P (Fintype.card I)) hdensity'
  have hboxSize : ((∏ i, (2 * R i + 1) : ℕ) : ℝ) ≤
      2 * ((2 ^ 14 : ℝ) * K ^ 6 * 16 ^ (Fintype.card I + 1)) ^ 16 * H.card := by
    have hcast : ((∏ i, (2 * R i + 1) : ℕ) : ℝ) ≤ Q := by exact_mod_cast hbox
    have hJcard : (A.card : ℝ) ≤ H.card := by
      rw [show A.card = J.card from additiveGraph_card J v]
      exact_mod_cast Finset.card_le_card hJH
    exact hcast.trans (hQsize.trans (mul_le_mul_of_nonneg_left hJcard (by positivity)))
  have hFA : F ⊆ A.image (FreimanModel.variableIntegerGraphLift N M) := hFS.trans hSA
  let π : (Option I → ℤ) → ZMod N := fun z => (z none : ZMod N)
  have hback (z : Option I → ℤ) (hz : z ∈ F) :
      π z ∈ J ∧ FreimanModel.variableIntegerGraphLift N M (π z, v (π z)) = z := by
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp (hFA hz)
    obtain ⟨hyJ, hyv⟩ := (mem_additiveGraph_iff J v y).mp hy
    have hπ : π (FreimanModel.variableIntegerGraphLift N M y) = y.1 := by
      simp [π]
    rw [hπ]
    exact ⟨hyJ, congrArg (FreimanModel.variableIntegerGraphLift N M) (Prod.ext rfl hyv.symm)⟩
  let J' := F.image π
  have hπinj : Set.InjOn π (F : Set _) := by
    intro x hx y hy hxy
    calc
      x = FreimanModel.variableIntegerGraphLift N M (π x, v (π x)) := (hback x hx).2.symm
      _ = FreimanModel.variableIntegerGraphLift N M (π y, v (π y)) := by rw [hxy]
      _ = y := (hback y hy).2
  have hFcard : F.card = J'.card := (Finset.card_image_of_injOn hπinj).symm
  have hJ' : J' ⊆ H := by
    intro h hh
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hh
    exact hJH (hback z hz).1
  have hJS : (J.card : ℝ) ≤ 16 ^ (Fintype.card I + 2) * (S.card : ℝ) := by
    have h : J.card ≤ 16 ^ (Fintype.card I + 2) * S.card := by
      simpa only [A, additiveGraph_card] using hASsize
    exact_mod_cast h
  have hretain : δ * (S.card : ℝ) ≤ (J'.card : ℝ) := by
    simpa only [hFcard] using hFsize
  refine ⟨J', hJ', hF.image _, ?_, r, R, Φ, base, hrank, hboxSize, hinj, ?_⟩
  · calc
      _ ≤ δ * (J.card : ℝ) := mul_le_mul_of_nonneg_left hsize (Real.exp_pos _).le
      _ ≤ δ * (16 ^ (Fintype.card I + 2) * (S.card : ℝ)) :=
        mul_le_mul_of_nonneg_left hJS (Real.exp_pos _).le
      _ = 16 ^ (Fintype.card I + 2) * (δ * S.card) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hretain (by positivity)
  · intro h hh
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hh
    rw [(hback z hz).2]
    exact hrepr z hz

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open scoped BigOperators Pointwise
open CyclicCrootSisask

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open scoped Pointwise BigOperators
open CyclicCrootSisask

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

theorem proper_integer_graph_affine_model {I : Type*} [Fintype I]
    (a : ZMod N → I → ℝ) (c : I → ℝ) (M l : I → ℕ) [∀ i, NeZero (M i)] (ε : I → ℝ)
    (hsmall : ∀ i, (M i : ℝ) * l i * ε i ≤ 1)
    (hnear : ∀ t ∈ D.quadruples, ∃ q ∈ coordinateDenominatorGrid l,
      ∀ i, |c i + (a (rankQuadrupleParameters t 1) i + a (rankQuadrupleParameters t 2) i -
        a (rankQuadrupleParameters t 0) i - a (rankQuadrupleParameters t 3) i) - q i| ≤ ε i) :
    let K := Real.exp (P + 13 * Fintype.card I)
    let z := roundedModelLogBudget P (Fintype.card I)
    let δ := Real.exp (-(quarticBogolyubovProgressionConstant * (z + 1) ^ 8))
    let v := fun h => variableRoundedCoefficient M l (a h)
    ∃ J₀ ⊆ H, J₀.Nonempty ∧
      δ * ((2 ^ 4 : ℝ)⁻¹ * K⁻¹ * H.card) ≤ 16 ^ (Fintype.card I + 2) * (J₀.card : ℝ) ∧
      ∃ (r : ℕ) (R : Fin r → ℕ) (Φ : (Fin r → ℤ) →+ (Option I → ℤ)),
        (r : ℝ) ≤ 2 + quarticBogolyubovConstant * (z + 1) ^ 4 ∧
        ((∏ i, (2 * R i + 1) : ℕ) : ℝ) ≤
          2 * ((2 ^ 14 : ℝ) * K ^ 6 * 16 ^ (Fintype.card I + 1)) ^ 16 * H.card ∧
        (let k := (2 ^ r * ∏ i, (2 * R i + 1)) / J₀.card + 1
         let reduce := FreimanModel.variableIntegerGraphReduction N M
         let η := (AddMonoidHom.fst (ZMod N) (∀ i, ZMod (M i))).comp (reduce.comp Φ)
         ∃ J ⊆ J₀, J.Nonempty ∧ J₀.card ≤ (4 * k) ^ r * J.card ∧
           ∃ base : Option I → ℤ,
             Set.InjOn η (centeredIntegerBox (fun i => R i / (2 * k)) : Set _) ∧
             ∀ h ∈ J, ∃ x : Fin r → ℤ,
               (∀ i, |x i| ≤ (R i / (2 * k) : ℕ)) ∧
               FreimanModel.variableIntegerGraphLift N M (h, v h) = base + Φ x) := by
  intro K z δ v
  classical
  obtain ⟨J₀, hJ₀H, hJ₀, hsize, r, R, Φ, base, hrank, hvolume, _hfull, hrepr⟩ :=
    D.integer_graph_affine_model a c M l ε hsmall hnear
  let reduce := FreimanModel.variableIntegerGraphReduction N M
  let η := (AddMonoidHom.fst (ZMod N) (∀ i, ZMod (M i))).comp (reduce.comp Φ)
  have hall (h : {h // h ∈ J₀}) : ∃ x : Fin r → ℤ,
      (∀ i, |x i| ≤ (R i : ℤ)) ∧
      FreimanModel.variableIntegerGraphLift N M (h.val, v h.val) = base + Φ x :=
    hrepr h.val h.property
  choose x hx hgraph using hall
  have hspace (h : {h // h ∈ J₀}) : h.val = (reduce base).1 + η (x h) := by
    change h.val = (reduce base).1 + (reduce (Φ (x h))).1
    have hh := congrArg (fun y => (reduce y).1) (hgraph h)
    simpa only [reduce, FreimanModel.variableIntegerGraphReduction_lift, map_add,
      Prod.fst_add] using hh
  obtain ⟨J, hJJ₀, hJ, hretain, t, hproper, hsmallBox⟩ :=
    exists_dense_proper_coordinate_restriction J₀ hJ₀ R η (reduce base).1 x hx hspace
  refine ⟨J₀, hJ₀H, hJ₀, hsize, r, R, Φ, hrank, hvolume, J, hJJ₀,
    hJ, hretain, base + Φ t, hproper, ?_⟩
  intro h hh
  let h₀ : {h // h ∈ J₀} := ⟨h, hJJ₀ hh⟩
  refine ⟨x h₀ - t, hsmallBox ⟨h, hh⟩, ?_⟩
  rw [hgraph h₀, map_sub]
  abel

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open scoped BigOperators Pointwise
open CyclicCrootSisask

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

theorem proper_affine_graph_recovery {I : Type*} [Fintype I] (hP : 0 ≤ P)
    (a : ZMod N → I → ℝ) (c : I → ℝ) (l : I → ℕ) (hl : ∀ i, 0 < l i)
    (ε : I → ℝ) (hε : ∀ i, 0 < ε i) (hsmall : ∀ i, 2 * (l i : ℝ) * ε i ≤ 1)
    (hnear : ∀ t ∈ D.quadruples, ∃ q ∈ coordinateDenominatorGrid l,
      ∀ i, |c i + (a (rankQuadrupleParameters t 1) i + a (rankQuadrupleParameters t 2) i -
        a (rankQuadrupleParameters t 0) i - a (rankQuadrupleParameters t 3) i) - q i| ≤ ε i) :
    let K := Real.exp (P + 13 * Fintype.card I)
    let z := roundedModelLogBudget P (Fintype.card I)
    let δ := Real.exp (-(quarticBogolyubovProgressionConstant * (z + 1) ^ 8))
    ∃ M : I → ℕ, (∀ i, 0 < M i) ∧
      (∀ i, (M i : ℝ) * l i * ε i ≤ 1) ∧
      (∀ i, 1 / ((M i : ℝ) * l i) ≤ 2 * ε i) ∧
      ∃ J₀ ⊆ H, J₀.Nonempty ∧
        δ * ((2 ^ 4 : ℝ)⁻¹ * K⁻¹ * H.card) ≤ 16 ^ (Fintype.card I + 2) * (J₀.card : ℝ) ∧
        ∃ (r : ℕ) (R : Fin r → ℕ) (Φ : (Fin r → ℤ) →+ (Option I → ℤ)),
          (r : ℝ) ≤ 2 + quarticBogolyubovConstant * (z + 1) ^ 4 ∧
          ((∏ i, (2 * R i + 1) : ℕ) : ℝ) ≤
            2 * ((2 ^ 14 : ℝ) * K ^ 6 * 16 ^ (Fintype.card I + 1)) ^ 16 * H.card ∧
          (let k := (2 ^ r * ∏ i, (2 * R i + 1)) / J₀.card + 1
           let reduce := FreimanModel.variableIntegerGraphReduction N M
           let η := (AddMonoidHom.fst (ZMod N) (∀ i, ZMod (M i))).comp (reduce.comp Φ)
           ∃ J ⊆ J₀, J.Nonempty ∧ J₀.card ≤ (4 * k) ^ r * J.card ∧
             Real.exp (-properAffineRecoveryLogLoss P (Fintype.card I)) * H.card ≤ (J.card : ℝ) ∧
             (k : ℝ) ≤ Real.exp (properAffineScaleLog P (Fintype.card I)) ∧
             ∃ base : Option I → ℤ,
               Set.InjOn η (centeredIntegerBox (fun i => R i / (2 * k)) : Set _) ∧
               (let ψ := (AddMonoidHom.snd (ZMod N) (∀ i, ZMod (M i))).comp (reduce.comp Φ)
                let α := variableCoefficientLift l (reduce base).2
                let β := fun j => variableCoefficientLift l (ψ (Pi.single j 1))
                (∀ i, α i ∈ Set.Ico (0 : ℝ) (1 / l i)) ∧
                (∀ j i, β j i ∈ Set.Ico (0 : ℝ) (1 / l i)) ∧
                ∀ h ∈ J, ∃ x : Fin r → ℤ,
                  (∀ i, |x i| ≤ (R i / (2 * k) : ℕ)) ∧
                  h = (reduce base).1 + η x ∧
                  FreimanModel.variableIntegerGraphLift N M
                    (h, variableRoundedCoefficient M l (a h)) = base + Φ x ∧
                  ∃ q ∈ coordinateDenominatorGrid l, ∀ i,
                    |a h i - (α + ∑ j, (x j : ℝ) • β j) i - q i| ≤ 2 * ε i)) := by
  intro K z δ
  obtain ⟨M, hM, hMsmall, hMerror⟩ := exists_coordinate_rounding_moduli l hl ε hε hsmall
  let _ : ∀ i, NeZero (M i) := fun i => ⟨(hM i).ne'⟩
  obtain ⟨J₀, hJ₀H, hJ₀, hsize, r, R, Φ, hrank, hvolume,
      J, hJJ₀, hJ, hretain, base, hproper, hrepr⟩ :=
    D.proper_integer_graph_affine_model a c M l ε hMsmall hnear
  have hcost := properAffineSelection_bounds hP (Fintype.card I) r
    (∏ i, (2 * R i + 1)) H.card J₀.card J.card hJ₀.card_pos hrank hvolume
    (exp_neg_affineRecoveryLogLoss_card_le P (Fintype.card I) H.card J₀.card hsize) hretain
  refine ⟨M, hM, hMsmall, hMerror, J₀, hJ₀H, hJ₀, hsize, r, R, Φ, hrank, hvolume,
    J, hJJ₀, hJ, hretain, hcost.2, hcost.1, base, hproper, ?_⟩
  dsimp only
  refine ⟨variableCoefficientLift_mem_Ico l hl _, ?_, ?_⟩
  · intro j
    exact variableCoefficientLift_mem_Ico l hl _
  · intro h hh
    obtain ⟨x, hx, heq⟩ := hrepr h hh
    let reduce := FreimanModel.variableIntegerGraphReduction N M
    have hred : (h, variableRoundedCoefficient M l (a h)) =
        reduce base + reduce (Φ x) := by
      have hr := congrArg reduce heq
      simpa only [reduce, FreimanModel.variableIntegerGraphReduction_lift, map_add] using hr
    refine ⟨x, hx, congrArg Prod.fst hred, heq, ?_⟩
    obtain ⟨q, hq, herr⟩ := exists_variable_unrounded_affine l hl (reduce base).2
      ((AddMonoidHom.snd (ZMod N) (∀ i, ZMod (M i))).comp (reduce.comp Φ)) x (a h)
      (congrArg Prod.snd hred)
    exact ⟨q, hq, fun i => (herr i).trans (hMerror i)⟩

end Erdos3.NativeRankRelation.CommonData

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SmallDifferenceGraphCoordinates
namespace OAI

section

namespace Erdos3

open scoped Pointwise BigOperators
open CyclicCrootSisask

theorem exists_small_difference_graph_coordinates {I : Type*} [Fintype I]
    (N : ℕ) (M : I → ℕ) [NeZero N] [∀ i, NeZero (M i)]
    (H : Finset (ZMod N)) (hH : H.Nonempty) (b : ZMod N → ∀ i, ZMod (M i))
    {p : ℝ} (hp : 0 ≤ p)
    (hsmall : ((additiveGraph H b - additiveGraph H b).card : ℝ) ≤ Real.exp p * H.card) :
    let K := (2 ^ 14 : ℝ) * (Real.exp (p + 13 * Fintype.card I)) ^ 6
    let z := roundedModelLogBudget p (Fintype.card I)
    let δ := Real.exp (-(quarticBogolyubovProgressionConstant * (z + 1) ^ 8))
    ∃ J ⊆ H, J.Nonempty ∧ δ * H.card ≤ 16 ^ (Fintype.card I + 2) * (J.card : ℝ) ∧
      ∃ (r : ℕ) (R : Fin r → ℕ) (Φ : (Fin r → ℤ) →+ (Option I → ℤ))
        (base : Option I → ℤ),
        (r : ℝ) ≤ 2 + quarticBogolyubovConstant * (z + 1) ^ 4 ∧
        ((∏ i, (2 * R i + 1) : ℕ) : ℝ) ≤
          2 * (K * 16 ^ (Fintype.card I + 1)) ^ 16 * H.card ∧
        Set.InjOn Φ {x | ∀ i, |x i| ≤ (R i : ℤ)} ∧
        ∀ h ∈ J, ∃ x : Fin r → ℤ, (∀ i, |x i| ≤ (R i : ℤ)) ∧
          FreimanModel.variableIntegerGraphLift N M (h, b h) = base + Φ x := by
  intro K z δ
  classical
  let A := additiveGraph H b
  have hK : Real.exp p ≤ K := by
    calc
      _ ≤ Real.exp (6 * (p + 13 * Fintype.card I)) := by
        apply Real.exp_le_exp.mpr
        nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card I)]
      _ = Real.exp (p + 13 * Fintype.card I) ^ 6 := by
        rw [← Real.exp_nat_mul]
        norm_num
      _ ≤ K := le_mul_of_one_le_left (by positivity) (by norm_num)
  have hAsmall : ((A - A).card : ℝ) ≤ K * A.card := by
    rw [show A.card = H.card from additiveGraph_card H b]
    exact hsmall.trans (mul_le_mul_of_nonneg_right hK (Nat.cast_nonneg _))
  obtain ⟨Q, S, B, f, hQ, hS, hSA, hASsize, hB, _, _, hf, hQsize, hdensity⟩ :=
    FreimanModel.exists_variableIntegerGraph_cyclic_model N M A (hH.image _) (by positivity) hAsmall
  let _ : NeZero Q := ⟨hQ.ne'⟩
  have hdensity' : Real.exp (-z) * Q ≤ (B.card : ℝ) := by
    apply (le_div_iff₀ (by exact_mod_cast hQ : (0 : ℝ) < Q)).mp
    exact (exp_neg_roundedModelLogBudget_le_density p (Fintype.card I)).trans hdensity
  obtain ⟨F, hFS, hF, hFsize, r, R, Φ, base, hrank, hbox, hinj, hrepr⟩ :=
    FreimanModel.exists_bounded_affine_box_of_cyclic_model S hS B hB f hf
      (roundedModelLogBudget_nonneg p (Fintype.card I)) hdensity'
  have hboxSize : ((∏ i, (2 * R i + 1) : ℕ) : ℝ) ≤
      2 * (K * 16 ^ (Fintype.card I + 1)) ^ 16 * H.card := by
    have hcast : ((∏ i, (2 * R i + 1) : ℕ) : ℝ) ≤ Q := by exact_mod_cast hbox
    exact hcast.trans (by simpa only [A, additiveGraph_card] using hQsize)
  have hFA : F ⊆ A.image (FreimanModel.variableIntegerGraphLift N M) := hFS.trans hSA
  let π : (Option I → ℤ) → ZMod N := fun v => (v none : ZMod N)
  have hback (v : Option I → ℤ) (hv : v ∈ F) :
      π v ∈ H ∧ FreimanModel.variableIntegerGraphLift N M (π v, b (π v)) = v := by
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp (hFA hv)
    obtain ⟨hyH, hyb⟩ := (mem_additiveGraph_iff H b y).mp hy
    have hπ : π (FreimanModel.variableIntegerGraphLift N M y) = y.1 := by simp [π]
    rw [hπ]
    exact ⟨hyH, congrArg (FreimanModel.variableIntegerGraphLift N M) (Prod.ext rfl hyb.symm)⟩
  let J := F.image π
  have hπinj : Set.InjOn π (F : Set _) := by
    intro x hx y hy hxy
    calc
      x = FreimanModel.variableIntegerGraphLift N M (π x, b (π x)) := (hback x hx).2.symm
      _ = FreimanModel.variableIntegerGraphLift N M (π y, b (π y)) := by rw [hxy]
      _ = y := (hback y hy).2
  have hFcard : F.card = J.card := (Finset.card_image_of_injOn hπinj).symm
  have hJ : J ⊆ H := by
    intro h hh
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hh
    exact (hback v hv).1
  have hHS : (H.card : ℝ) ≤ 16 ^ (Fintype.card I + 2) * (S.card : ℝ) := by
    exact_mod_cast (show H.card ≤ 16 ^ (Fintype.card I + 2) * S.card by
      simpa only [A, additiveGraph_card] using hASsize)
  have hretain : δ * (S.card : ℝ) ≤ (J.card : ℝ) := by
    simpa only [hFcard] using hFsize
  refine ⟨J, hJ, hF.image _, ?_, r, R, Φ, base, hrank, hboxSize, hinj, ?_⟩
  · calc
      δ * (H.card : ℝ) ≤ δ * (16 ^ (Fintype.card I + 2) * (S.card : ℝ)) :=
        mul_le_mul_of_nonneg_left hHS (Real.exp_nonneg _)
      _ = 16 ^ (Fintype.card I + 2) * (δ * S.card) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hretain (by positivity)
  · intro h hh
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hh
    rw [(hback v hv).2]
    exact hrepr v hv

theorem exists_small_difference_graph_proper_coordinates {I : Type*} [Fintype I]
    (N : ℕ) (M : I → ℕ) [NeZero N] [∀ i, NeZero (M i)]
    (H : Finset (ZMod N)) (hH : H.Nonempty) (b : ZMod N → ∀ i, ZMod (M i))
    {p : ℝ} (hp : 0 ≤ p)
    (hsmall : ((additiveGraph H b - additiveGraph H b).card : ℝ) ≤ Real.exp p * H.card) :
    let K := (2 ^ 14 : ℝ) * (Real.exp (p + 13 * Fintype.card I)) ^ 6
    let z := roundedModelLogBudget p (Fintype.card I)
    let δ := Real.exp (-(quarticBogolyubovProgressionConstant * (z + 1) ^ 8))
    ∃ J₀ ⊆ H, J₀.Nonempty ∧ δ * H.card ≤ 16 ^ (Fintype.card I + 2) * (J₀.card : ℝ) ∧
      ∃ (r : ℕ) (R : Fin r → ℕ) (Φ : (Fin r → ℤ) →+ (Option I → ℤ)),
        (r : ℝ) ≤ 2 + quarticBogolyubovConstant * (z + 1) ^ 4 ∧
        ((∏ i, (2 * R i + 1) : ℕ) : ℝ) ≤
          2 * (K * 16 ^ (Fintype.card I + 1)) ^ 16 * H.card ∧
        (let k := (2 ^ r * ∏ i, (2 * R i + 1)) / J₀.card + 1
         let reduce := FreimanModel.variableIntegerGraphReduction N M
         let η := (AddMonoidHom.fst (ZMod N) (∀ i, ZMod (M i))).comp (reduce.comp Φ)
         ∃ J ⊆ J₀, J.Nonempty ∧ J₀.card ≤ (4 * k) ^ r * J.card ∧
           ∃ base : Option I → ℤ,
             Set.InjOn η (centeredIntegerBox (fun i => R i / (2 * k)) : Set _) ∧
             ∀ h ∈ J, ∃ x : Fin r → ℤ, (∀ i, |x i| ≤ (R i / (2 * k) : ℕ)) ∧
               FreimanModel.variableIntegerGraphLift N M (h, b h) = base + Φ x) := by
  intro K z δ
  classical
  obtain ⟨J₀, hJ₀H, hJ₀, hsize, r, R, Φ, base, hrank, hvolume, _, hrepr⟩ :=
    exists_small_difference_graph_coordinates N M H hH b hp hsmall
  let reduce := FreimanModel.variableIntegerGraphReduction N M
  let η := (AddMonoidHom.fst (ZMod N) (∀ i, ZMod (M i))).comp (reduce.comp Φ)
  have hall (h : {h // h ∈ J₀}) : ∃ x : Fin r → ℤ, (∀ i, |x i| ≤ (R i : ℤ)) ∧
      FreimanModel.variableIntegerGraphLift N M (h.val, b h.val) = base + Φ x :=
    hrepr h.val h.property
  choose x hx hgraph using hall
  have hspace (h : {h // h ∈ J₀}) : h.val = (reduce base).1 + η (x h) := by
    change h.val = (reduce base).1 + (reduce (Φ (x h))).1
    have hh := congrArg (fun v => (reduce v).1) (hgraph h)
    simpa only [reduce, FreimanModel.variableIntegerGraphReduction_lift, map_add,
      Prod.fst_add] using hh
  obtain ⟨J, hJJ₀, hJ, hretain, t, hproper, hsmallBox⟩ :=
    exists_dense_proper_coordinate_restriction J₀ hJ₀ R η (reduce base).1 x hx hspace
  refine ⟨J₀, hJ₀H, hJ₀, hsize, r, R, Φ, hrank, hvolume, J, hJJ₀,
    hJ, hretain, base + Φ t, hproper, ?_⟩
  intro h hh
  let h₀ : {h // h ∈ J₀} := ⟨h, hJJ₀ hh⟩
  refine ⟨x h₀ - t, hsmallBox ⟨h, hh⟩, ?_⟩
  rw [hgraph h₀, map_sub]
  abel

theorem exists_small_difference_graph_affine_coordinates {I : Type*} [Fintype I]
    (N : ℕ) (M : I → ℕ) [NeZero N] [∀ i, NeZero (M i)]
    (H : Finset (ZMod N)) (hH : H.Nonempty) (b : ZMod N → ∀ i, ZMod (M i))
    {p : ℝ} (hp : 0 ≤ p)
    (hsmall : ((additiveGraph H b - additiveGraph H b).card : ℝ) ≤ Real.exp p * H.card) :
    ∃ J ⊆ H, J.Nonempty ∧
      Real.exp (-properAffineRecoveryLogLoss p (Fintype.card I)) * H.card ≤ (J.card : ℝ) ∧
      ∃ (r : ℕ) (R : Fin r → ℕ) (Φ : (Fin r → ℤ) →+ (Option I → ℤ))
        (base : Option I → ℤ),
        (r : ℝ) ≤ properAffineRankBound p (Fintype.card I) ∧
        (let reduce := FreimanModel.variableIntegerGraphReduction N M
         let η := (AddMonoidHom.fst (ZMod N) (∀ i, ZMod (M i))).comp (reduce.comp Φ)
         Set.InjOn η (centeredIntegerBox R : Set _)) ∧
        ∀ h ∈ J, ∃ x : Fin r → ℤ, (∀ i, |x i| ≤ (R i : ℤ)) ∧
          FreimanModel.variableIntegerGraphLift N M (h, b h) = base + Φ x := by
  classical
  obtain ⟨J₀, hJ₀H, hJ₀, hsize, r, R, Φ, hrank, hvolume,
      J, hJJ₀, hJ, hretain, base, hproper, hrepr⟩ :=
    exists_small_difference_graph_proper_coordinates N M H hH b hp hsmall
  have hfactor : ((2 : ℝ) ^ 4)⁻¹ * (Real.exp (p + 13 * Fintype.card I))⁻¹ ≤ 1 := by
    calc
      _ ≤ (Real.exp (p + 13 * Fintype.card I))⁻¹ :=
        mul_le_of_le_one_left (by positivity) (by norm_num)
      _ ≤ 1 := inv_le_one_of_one_le₀ (Real.one_le_exp_iff.mpr (by positivity))
  have hweaker : Real.exp (-(quarticBogolyubovProgressionConstant *
      (roundedModelLogBudget p (Fintype.card I) + 1) ^ 8)) *
      ((2 ^ 4 : ℝ)⁻¹ * (Real.exp (p + 13 * Fintype.card I))⁻¹ * H.card) ≤
      16 ^ (Fintype.card I + 2) * (J₀.card : ℝ) := by
    apply le_trans _ hsize
    apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
    exact mul_le_of_le_one_left (Nat.cast_nonneg _) hfactor
  have hdense₀ := exp_neg_affineRecoveryLogLoss_card_le p (Fintype.card I) H.card J₀.card hweaker
  have hcost := properAffineSelection_bounds hp (Fintype.card I) r
    (∏ i, (2 * R i + 1)) H.card J₀.card J.card hJ₀.card_pos hrank hvolume hdense₀ hretain
  exact ⟨J, hJJ₀.trans hJ₀H, hJ, hcost.2, r,
    (fun i => R i / (2 * ((2 ^ r * ∏ j, (2 * R j + 1)) / J₀.card + 1))),
    Φ, base, hrank, hproper, hrepr⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.DegreewiseProperAffineRecovery
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open scoped BigOperators Pointwise
open CyclicCrootSisask

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

theorem degreewise_proper_affine_recovery {B : Type*} [Fintype B] {I : B → Type*}
    [∀ d, Fintype (I d)] (hP : 0 ≤ P) (a : ZMod N → ∀ d, I d → ℝ) (c : ∀ d, I d → ℝ)
    (l : B → ℕ) (hl : ∀ d, 0 < l d) (ε : B → ℝ) (hε : ∀ d, 0 < ε d)
    (hsmall : ∀ d, 2 * (l d : ℝ) * ε d ≤ 1)
    (hnear : ∀ t ∈ D.quadruples, ∀ d, ∃ q ∈ realDenominatorGrid (l d),
      ‖c d + (a (rankQuadrupleParameters t 1) d + a (rankQuadrupleParameters t 2) d -
        a (rankQuadrupleParameters t 0) d - a (rankQuadrupleParameters t 3) d) - q‖ ≤ ε d) :
    let n := Fintype.card (Σ d, I d)
    ∃ J' ⊆ H, J'.Nonempty ∧
      Real.exp (-properAffineRecoveryLogLoss P n) * H.card ≤ (J'.card : ℝ) ∧
      ∃ (r : ℕ) (R : Fin r → ℕ) (ξ : (Fin r → ℤ) →+ ZMod N)
        (h₀ : ZMod N) (α : ∀ d, I d → ℝ) (β : Fin r → ∀ d, I d → ℝ),
        (r : ℝ) ≤ properAffineRankBound P n ∧
        Set.InjOn ξ {x | ∀ i, |x i| ≤ (R i : ℤ)} ∧
        (∀ d i, α d i ∈ Set.Ico (0 : ℝ) (1 / l d)) ∧
        (∀ j d i, β j d i ∈ Set.Ico (0 : ℝ) (1 / l d)) ∧
        ∀ h ∈ J', ∃ x : Fin r → ℤ,
          (∀ j, |x j| ≤ (R j : ℤ)) ∧ h = h₀ + ξ x ∧
          ∀ d, ∃ q ∈ realDenominatorGrid (l d),
            ‖a h d - (α d + ∑ j, (x j : ℝ) • β j d) - q‖ ≤ 2 * ε d := by
  intro n
  let a' : ZMod N → (Σ d, I d) → ℝ := fun h i => a h i.1 i.2
  let c' : (Σ d, I d) → ℝ := fun i => c i.1 i.2
  let l' : (Σ d, I d) → ℕ := fun i => l i.1
  let ε' : (Σ d, I d) → ℝ := fun i => ε i.1
  have hnear' : ∀ t ∈ D.quadruples, ∃ q ∈ coordinateDenominatorGrid l',
      ∀ i, |c' i + (a' (rankQuadrupleParameters t 1) i + a' (rankQuadrupleParameters t 2) i -
        a' (rankQuadrupleParameters t 0) i - a' (rankQuadrupleParameters t 3) i) - q i| ≤ ε' i := by
    intro t ht
    choose q hq he using hnear t ht
    have hq' : ∀ d, ∃ v : I d → ℤ, ∀ i, (v i : ℝ) = (l d : ℝ) * q d i := by
      intro d
      obtain ⟨v, hv⟩ := hq d
      exact ⟨v, fun i => congrFun hv i⟩
    choose v hv using hq'
    refine ⟨fun i => q i.1 i.2, ⟨fun i => v i.1 i.2, fun i => hv i.1 i.2⟩, ?_⟩
    intro i
    have hi := (norm_le_pi_norm (c i.1 +
      (a (rankQuadrupleParameters t 1) i.1 + a (rankQuadrupleParameters t 2) i.1 -
        a (rankQuadrupleParameters t 0) i.1 - a (rankQuadrupleParameters t 3) i.1) - q i.1)
      i.2).trans (he i.1)
    simpa only [a', c', ε', Pi.add_apply, Pi.sub_apply, Real.norm_eq_abs] using hi
  obtain ⟨M, _hM, _hMsmall, _hMerror, J₀, hJ₀H, _hJ₀, _hsize₀, r, R, Φ,
      hrank, _hvolume, J', hJ'J₀, hJ, _hretain, hsize, _hscale, base, hproper, hα, hβ, hrepr⟩ :=
    D.proper_affine_graph_recovery hP a' c' l' (fun i => hl i.1) ε' (fun i => hε i.1)
      (fun i => hsmall i.1) hnear'
  let k := (2 ^ r * ∏ i, (2 * R i + 1)) / J₀.card + 1
  let R' := fun i => R i / (2 * k)
  let reduce := FreimanModel.variableIntegerGraphReduction N M
  let ξ := (AddMonoidHom.fst (ZMod N) (∀ i, ZMod (M i))).comp (reduce.comp Φ)
  let ψ := (AddMonoidHom.snd (ZMod N) (∀ i, ZMod (M i))).comp (reduce.comp Φ)
  let α := variableCoefficientLift l' (reduce base).2
  let β := fun j => variableCoefficientLift l' (ψ (Pi.single j 1))
  have hinj : Set.InjOn ξ {x | ∀ i, |x i| ≤ (R' i : ℤ)} := by
    intro x hx y hy hxy
    exact hproper ((mem_centeredIntegerBox R' x).mpr hx)
      ((mem_centeredIntegerBox R' y).mpr hy) hxy
  refine ⟨J', hJ'J₀.trans hJ₀H, hJ, hsize, r, R', ξ, (reduce base).1,
    (fun d i => α ⟨d, i⟩), (fun j d i => β j ⟨d, i⟩), hrank, hinj,
    (fun d i => hα ⟨d, i⟩), (fun j d i => hβ j ⟨d, i⟩), ?_⟩
  intro h hh
  obtain ⟨x, hx, hspace, _hgraph, q, hq, he⟩ := hrepr h hh
  obtain ⟨v, hv⟩ := hq
  refine ⟨x, hx, hspace, ?_⟩
  intro d
  refine ⟨fun i => q ⟨d, i⟩, ⟨fun i => v ⟨d, i⟩, funext (fun i => hv ⟨d, i⟩)⟩, ?_⟩
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (by norm_num) (hε d).le)).mpr
  intro i
  simpa only [a', ε', Pi.sub_apply, Pi.add_apply, Finset.sum_apply, Pi.smul_apply,
    Real.norm_eq_abs] using he ⟨d, i⟩

end Erdos3.NativeRankRelation.CommonData

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SharedFreeAffineOrbitFamily
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct BigOperators

theorem affine_petal_decomposition
    {μ ι V : Type*} [Fintype μ] [Fintype ι] [AddCommGroup V] [Module ℚ V]
    (b : Basis μ ℚ V) (U : Submodule ℚ V) (K : Submodule ℚ (Fin 4 → V))
    (ℓ : (Fin 4 → V) →ₗ[ℚ] (ι → ℚ)) (hker : LinearMap.ker ℓ = K)
    (σ : (ι → ℝ) →ₗ[ℝ] (ℝ ⊗[ℚ] V))
    (hσU : ∀ y, σ y ∈ U.baseChange ℝ)
    (hσ : ∀ w ∈ U.baseChange ℝ,
      realifyCoordinateMap (ℓ.comp (LinearMap.single ℚ (fun _ : Fin 4 => V) 0))
          (σ (realifyCoordinateMap (ℓ.comp (LinearMap.single ℚ (fun _ : Fin 4 => V) 0)) w)) =
        realifyCoordinateMap (ℓ.comp (LinearMap.single ℚ (fun _ : Fin 4 => V) 0)) w)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ y, ‖(b.baseChange ℝ).equivFun (σ y)‖ ≤ C * ‖y‖)
    {l m : ℕ} (hgrid : ∀ y ∈ realDenominatorGrid l,
      (b.baseChange ℝ).equivFun (σ y) ∈ realDenominatorGrid m)
    {r : ℕ} (α : ι → ℝ) (β : Fin r → ι → ℝ) (x : Fin r → ℤ)
    (w : ℝ ⊗[ℚ] V) (hw : w ∈ U.baseChange ℝ) (q : ι → ℝ)
    (hq : q ∈ realDenominatorGrid l) {ε : ℝ}
    (he : ‖realifyCoordinateMap (ℓ.comp (LinearMap.single ℚ (fun _ : Fin 4 => V) 0)) w -
      (α + ∑ j, (x j : ℝ) • β j) - q‖ ≤ ε) :
    ∃ E Q P : ℝ ⊗[ℚ] V, E ∈ U.baseChange ℝ ∧ Q ∈ U.baseChange ℝ ∧
      P ∈ (fourPetalSpace U K).baseChange ℝ ∧
      w = (σ α + ∑ j, (x j : ℝ) • σ (β j)) + E + Q + P ∧
      ‖(b.baseChange ℝ).equivFun E‖ ≤ C * ε ∧
      (b.baseChange ℝ).equivFun Q ∈ realDenominatorGrid m := by
  let φ := ℓ.comp (LinearMap.single ℚ (fun _ : Fin 4 => V) 0)
  let a := realifyCoordinateMap φ w
  let e := a - (α + ∑ j, (x j : ℝ) • β j) - q
  let P := w - σ a
  have hPU : P ∈ U.baseChange ℝ := (U.baseChange ℝ).sub_mem hw (hσU a)
  have hzero : realifyCoordinateMap φ P = 0 := by
    change realifyCoordinateMap φ (w - σ a) = 0
    rw [map_sub, hσ w hw, sub_self]
  have hP : P ∈ (fourPetalSpace U K).baseChange ℝ := by
    apply (mem_real_petal_annihilator_iff U K ℓ hker P).mpr
    refine ⟨hPU, fun j => ?_⟩
    exact congrFun hzero j
  refine ⟨σ e, σ q, P, hσU e, hσU q, hP, ?_, ?_, hgrid q hq⟩
  · dsimp [P, e]
    simp only [map_sub, map_add, map_sum, map_smul]
    abel
  · exact (hbound e).trans (mul_le_mul_of_nonneg_left he hC)

end Erdos3

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module VectorPolynomial CyclicCrootSisask
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure r) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  (F : FreeCoordinateFrame E.basis Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s r) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

include F

theorem exists_shared_free_affine_recovery
    (hs : 2 ≤ s) (hp' : 0 ≤ p') (hP' : 0 ≤ P') (hQP' : Q ≤ P') (hpp' : p' ≤ P')
    (ξ : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (v : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hsplit : ∀ h, g h = ξ * v h)
    (hξ : ∀ d : Fin s, coefficients ξ.log (Finsupp.single () (d.val + 1)) ∈
      (D.commonFreeSpan d).baseChange ℝ)
    (hv : ∀ h (d : Fin s), coefficients (v h).log (Finsupp.single () (d.val + 1)) ∈
      (D.dependentFreeSpan d).baseChange ℝ)
    (hN : Real.exp ((P' + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s) ≤ (N : ℝ)) :
    let B := (P' + 2) ^ 3 + 2 * P'
    let Λ := (P' + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s
    ∃ D₁ : R'.CommonData B, D₁.quadruples ⊆ D'.quadruples ∧ D₁.spaces = D'.spaces ∧
      ∃ (n : Fin s → ℕ)
        (ℓ : ∀ d : Fin s, (Fin 4 → D.CoefficientFreeLieAlgebra) →ₗ[ℚ] (Fin (n d) → ℚ))
        (m : Fin s → ℕ),
        (∀ d, n d ≤ 4 * finrank ℚ D.CoefficientFreeLieAlgebra ∧
          Function.Surjective (ℓ d) ∧ LinearMap.ker (ℓ d) =
            fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
              (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩) ∧
          (∀ k i j, rationalLogHeight (ℓ d (LinearMap.single ℚ
            (fun _ : Fin 4 => D.CoefficientFreeLieAlgebra) k (E.basis i)) j) ≤
              fourRefinementAnnihilatorBudget (Q + coefficientFourHeightBudget P')) ∧
          0 < m d ∧ (m d : ℝ) ≤ Real.exp Λ) ∧
        let a := fun h (d : Fin s) => realifyCoordinateMap
          ((ℓ d).comp (LinearMap.single ℚ (fun _ : Fin 4 => D.CoefficientFreeLieAlgebra) 0))
          (coefficients (v h).log (Finsupp.single () (d.val + 1)))
        let n₀ := Fintype.card (Σ d : Fin s, Fin (n d))
        (n₀ : ℝ) ≤ 4 * (s : ℝ) * P' ∧
        ∃ J ⊆ H', J.Nonempty ∧
          Real.exp (-Λ) * H'.card ≤ (J.card : ℝ) ∧
          ∃ (r₀ : ℕ) (R₀ : Fin r₀ → ℕ) (η : (Fin r₀ → ℤ) →+ ZMod N)
            (h₀ : ZMod N) (α : ∀ d, Fin (n d) → ℝ) (β : Fin r₀ → ∀ d, Fin (n d) → ℝ),
            (r₀ : ℝ) ≤ Λ ∧ Set.InjOn η {x | ∀ j, |x j| ≤ (R₀ j : ℤ)} ∧
            (∀ d i, α d i ∈ Set.Ico (0 : ℝ) (1 / m d)) ∧
            (∀ j d i, β j d i ∈ Set.Ico (0 : ℝ) (1 / m d)) ∧
            ∀ h ∈ J, ∃ x : Fin r₀ → ℤ,
              (∀ j, |x j| ≤ (R₀ j : ℤ)) ∧ h = h₀ + η x ∧
              ∀ d, ∃ q ∈ realDenominatorGrid (m d),
                ‖a h d - (α d + ∑ j, (x j : ℝ) • β j d) - q‖ ≤
                  Real.exp Λ / (N : ℝ) ^ (d.val + 1) := by
  intro B Λ
  classical
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  let z₀ := 8 * sharedRefinementInputBudget s P' + 1
  let A := sharedFreeEquationInputBudget s Q P'
  have hQ : 0 ≤ Q := (Nat.cast_nonneg _).trans hT.1.1
  have hbudget₀ := (sharedFreeAffineConstant_spec s).2 Q P' hQ hQP' hP' 0
    (by simpa only [Nat.cast_zero] using
      mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (Nat.cast_nonneg s)) hP')
  have hcut := sharedFreeRecoveryThreshold_spec s hQ hP' N
    ((Real.exp_le_exp.mpr hbudget₀.1).trans hN)
  have hcoeff := sharedFreeRecoveryThreshold_coefficient_bounds s hQ hP'
  obtain ⟨D₁, hsub, hspaces, hblocks⟩ :=
    D.exists_controlled_shared_free_equations E T hbQ hT F V g hg D'
      hs hp' hP' hQP' hpp' ξ v hsplit hξ hv hcut.1
  choose n hn ℓ hsurj hker hheight m hm hmA hnear using hblocks
  have hdenom (d : Fin s) : (m d : ℝ) ≤ Real.exp Λ :=
    (hmA d).trans (Real.exp_le_exp.mpr (hcoeff.1.trans hbudget₀.1))
  have hnum : 2 * (Real.exp ((A + 2) ^ 3) *
      (Real.exp z₀ + Real.exp ((z₀ + 2) ^ 3 + (z₀ + 2) ^ 18 + z₀))) ≤ Real.exp Λ :=
    hcoeff.2.trans (Real.exp_le_exp.mpr hbudget₀.1)
  let a := fun h (d : Fin s) => realifyCoordinateMap
    ((ℓ d).comp (LinearMap.single ℚ (fun _ : Fin 4 => D.CoefficientFreeLieAlgebra) 0))
    (coefficients (v h).log (Finsupp.single () (d.val + 1)))
  let c := fun d : Fin s => realifyCoordinateMap ((ℓ d).comp (fourDiagonalMap (R := ℚ)))
    (coefficients ξ.log (Finsupp.single () (d.val + 1)))
  let ε := fun d : Fin s => Real.exp ((A + 2) ^ 3) *
    ((Real.exp z₀ + Real.exp ((z₀ + 2) ^ 3 + (z₀ + 2) ^ 18 + z₀)) / (N : ℝ) ^ (d.val + 1))
  have hNpos : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hε : ∀ d, 0 < ε d := by intro d; dsimp [ε]; positivity
  have hsmall : ∀ d, 2 * (m d : ℝ) * ε d ≤ 1 := by
    intro d
    exact hcut.2 (m d) (d.val + 1) (by omega) (hmA d)
  have hnear' : ∀ t ∈ D₁.quadruples, ∀ d, ∃ q ∈ realDenominatorGrid (m d),
      ‖c d + (a (rankQuadrupleParameters t 1) d + a (rankQuadrupleParameters t 2) d -
        a (rankQuadrupleParameters t 0) d - a (rankQuadrupleParameters t 3) d) - q‖ ≤ ε d := by
    intro t ht d
    simpa only [a, c, ε, monomialScale, Finsupp.prod_single_index, pow_zero] using hnear d t ht
  have hdim : (Fintype.card (Σ d : Fin s, Fin (n d)) : ℝ) ≤ 4 * (s : ℝ) * P' := by
    rw [Fintype.card_sigma, Nat.cast_sum]
    simp only [Fintype.card_fin]
    calc
      (∑ d : Fin s, (n d : ℝ)) ≤ ∑ _d : Fin s, 4 * P' := by
        apply Finset.sum_le_sum
        intro d _hd
        have hnR := (Nat.cast_le (α := ℝ)).mpr (hn d)
        simp only [Nat.cast_mul, Nat.cast_ofNat] at hnR
        exact hnR.trans (mul_le_mul_of_nonneg_left (hT.1.1.trans hQP') (by norm_num))
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
  refine ⟨D₁, hsub, hspaces, n, ℓ, m, ?_, hdim, ?_⟩
  · intro d
    exact ⟨hn d, hsurj d, hker d, hheight d, hm d, hdenom d⟩
  · obtain ⟨J, hJH, hJ, hsize, r₀, R₀, η, h₀, α, β, hrank, hproper, hα, hβ, hrepr⟩ :=
      D₁.degreewise_proper_affine_recovery hB a c m hm ε hε hsmall hnear'
    have hbudget := sharedFreeAffineConstant_proper_spec s hP' _ hdim
    refine ⟨J, hJH, hJ, ?_, r₀, R₀, η, h₀, α, β, hrank.trans hbudget.2.2, hproper, hα, hβ, ?_⟩
    · exact (mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr (neg_le_neg hbudget.1)) (Nat.cast_nonneg _)).trans hsize
    · intro h hh
      obtain ⟨x, hx, hspace, herr⟩ := hrepr h hh
      refine ⟨x, hx, hspace, ?_⟩
      intro d
      obtain ⟨q, hq, he⟩ := herr d
      refine ⟨q, hq, he.trans ?_⟩
      simpa only [ε, mul_div_assoc] using
        div_le_div_of_nonneg_right hnum (pow_nonneg (Nat.cast_nonneg N) (d.val + 1))

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3

noncomputable def sharedFreePetalLiftInput (s : ℕ) (q p : ℝ) : ℝ :=
  4 * p + fourRefinementAnnihilatorBudget (q + coefficientFourHeightBudget p) +
    (p + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s

noncomputable def sharedFreePetalLiftBudget (s : ℕ) (q p : ℝ) : ℝ :=
  let t := (sharedFreePetalLiftInput s q p + 2) ^ 4 + 1
  (t + 2) ^ 3 + (t + 2) ^ 36 + (p + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s

end Erdos3

namespace Erdos3.NativeRankRelation.CommonData

open Module VectorPolynomial CyclicCrootSisask
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure r) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  (F : FreeCoordinateFrame E.basis Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s r) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

include F

theorem exists_shared_free_affine_petal
    (hs : 2 ≤ s) (hp' : 0 ≤ p') (hP' : 0 ≤ P') (hQP' : Q ≤ P') (hpp' : p' ≤ P')
    (ξ : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (v : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hsplit : ∀ h, g h = ξ * v h)
    (hξ : ∀ d : Fin s, coefficients ξ.log (Finsupp.single () (d.val + 1)) ∈
      (D.commonFreeSpan d).baseChange ℝ)
    (hv : ∀ h (d : Fin s), coefficients (v h).log (Finsupp.single () (d.val + 1)) ∈
      (D.dependentFreeSpan d).baseChange ℝ)
    (hN : Real.exp ((P' + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s) ≤ (N : ℝ)) :
    let B := (P' + 2) ^ 3 + 2 * P'
    let Λ := (P' + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s
    let L := sharedFreePetalLiftBudget s Q P'
    ∃ D₁ : R'.CommonData B, D₁.quadruples ⊆ D'.quadruples ∧ D₁.spaces = D'.spaces ∧
      ∃ J ⊆ H', J.Nonempty ∧ Real.exp (-Λ) * H'.card ≤ (J.card : ℝ) ∧
        ∃ (r₀ : ℕ) (R₀ : Fin r₀ → ℕ) (η : (Fin r₀ → ℤ) →+ ZMod N) (h₀ : ZMod N)
          (m : Fin s → ℕ) (α : Fin s → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
          (β : Fin r₀ → Fin s → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra),
          (r₀ : ℝ) ≤ Λ ∧ Set.InjOn η {x | ∀ j, |x j| ≤ (R₀ j : ℤ)} ∧ (∀ d, 0 < m d ∧ (m d : ℝ) ≤ Real.exp L) ∧
          (∀ d, α d ∈ (D.dependentFreeSpan d).baseChange ℝ ∧
            ‖(E.basis.baseChange ℝ).equivFun (α d)‖ ≤ Real.exp L) ∧
          (∀ j d, β j d ∈ (D.dependentFreeSpan d).baseChange ℝ ∧
            ‖(E.basis.baseChange ℝ).equivFun (β j d)‖ ≤ Real.exp L) ∧
          ∀ h ∈ J, ∃ x : Fin r₀ → ℤ,
            (∀ j, |x j| ≤ (R₀ j : ℤ)) ∧ h = h₀ + η x ∧
            ∀ d, ∃ e q u : ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra,
              e ∈ (D.dependentFreeSpan d).baseChange ℝ ∧
              q ∈ (D.dependentFreeSpan d).baseChange ℝ ∧
              u ∈ (fourPetalSpace (D.dependentFreeSpan d)
                (fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
                  (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩))).baseChange ℝ ∧
              coefficients (v h).log (Finsupp.single () (d.val + 1)) =
                (α d + ∑ j, (x j : ℝ) • β j d) + e + q + u ∧
              ‖(E.basis.baseChange ℝ).equivFun e‖ ≤ Real.exp L / (N : ℝ) ^ (d.val + 1) ∧
              (E.basis.baseChange ℝ).equivFun q ∈ realDenominatorGrid (m d) := by
  intro B Λ L
  classical
  obtain ⟨D₁, hsub, hspaces, n, ℓ, l, hdata, _hdim, J, hJH, hJ, hcard,
      r₀, R₀, η, h₀, α, β, hrank, hproper, hα, hβ, hrepr⟩ :=
    D.exists_shared_free_affine_recovery E T hbQ hT F V g hg D'
      hs hp' hP' hQP' hpp' ξ v hsplit hξ hv hN
  let A := sharedFreePetalLiftInput s Q P'
  let t := (A + 2) ^ 4 + 1
  let C := (t + 2) ^ 3 + (t + 2) ^ 18
  have hQ : 0 ≤ Q := (Nat.cast_nonneg _).trans hT.1.1
  have hΛ : 0 ≤ Λ := by dsimp [Λ]; positivity
  have ha : 0 ≤ fourRefinementAnnihilatorBudget (Q + coefficientFourHeightBudget P') :=
    fourRefinementAnnihilatorBudget_nonneg (add_nonneg hQ (coefficientFourHeightBudget_nonneg hP'))
  have hA : 0 ≤ A := by dsimp [A, sharedFreePetalLiftInput]; positivity
  have h4A : 4 * P' ≤ A := by dsimp [A, sharedFreePetalLiftInput]; linarith
  have hPA : P' ≤ A := by linarith
  have hQA : Q ≤ A := hQP'.trans hPA
  have hΛA : Λ ≤ A := by dsimp [A, sharedFreePetalLiftInput]; linarith
  have haA : fourRefinementAnnihilatorBudget (Q + coefficientFourHeightBudget P') ≤ A := by
    dsimp [A, sharedFreePetalLiftInput]
    linarith
  have hsections (d : Fin s) :
      ∃ (σ : (Fin (n d) → ℝ) →ₗ[ℝ] (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)) (m : ℕ),
        0 < m ∧ (m : ℝ) ≤ Real.exp ((t + 2) ^ 3 + (t + 2) ^ 36) ∧
        (∀ y, σ y ∈ (D.dependentFreeSpan d).baseChange ℝ) ∧
        (∀ w ∈ (D.dependentFreeSpan d).baseChange ℝ,
          realifyCoordinateMap ((ℓ d).comp (LinearMap.single ℚ
            (fun _ : Fin 4 => D.CoefficientFreeLieAlgebra) 0))
              (σ (realifyCoordinateMap ((ℓ d).comp (LinearMap.single ℚ
                (fun _ : Fin 4 => D.CoefficientFreeLieAlgebra) 0)) w)) =
            realifyCoordinateMap ((ℓ d).comp (LinearMap.single ℚ
              (fun _ : Fin 4 => D.CoefficientFreeLieAlgebra) 0)) w) ∧
        (∀ y, ‖(E.basis.baseChange ℝ).equivFun (σ y)‖ ≤ Real.exp C * ‖y‖) ∧
        ∀ y ∈ realDenominatorGrid (l d),
          (E.basis.baseChange ℝ).equivFun (σ y) ∈ realDenominatorGrid m := by
    obtain ⟨c, hc⟩ := D.exists_dependentFreeSpan_basis E.basis F (by omega) d
    obtain ⟨hn, _hsurj, _hker, hheight, hl, hlΛ⟩ := hdata d
    have hcspan : Submodule.span ℚ (Set.range (fun j => (c j : D.CoefficientFreeLieAlgebra))) =
        D.dependentFreeSpan d := by
      change Submodule.span ℚ (Set.range ((D.dependentFreeSpan d).subtype ∘ c)) = _
      rw [Set.range_comp, ← Submodule.map_span, c.span_eq, Submodule.map_top, Submodule.range_subtype]
    apply exists_logHeight_subspace_image_section E.basis (D.dependentFreeSpan d)
      (fun j => (c j : D.CoefficientFreeLieAlgebra)) hcspan
      ((ℓ d).comp (LinearMap.single ℚ (fun _ : Fin 4 => D.CoefficientFreeLieAlgebra) 0))
      (l d) hl hA
    · simpa only [Fintype.card_fin] using (hT.1.1.trans hQP').trans hPA
    · have hnR := (Nat.cast_le (α := ℝ)).mpr hn
      simp only [Nat.cast_mul, Nat.cast_ofNat] at hnR
      have hdim := mul_le_mul_of_nonneg_left (hT.1.1.trans hQP') (by norm_num : (0 : ℝ) ≤ 4)
      simpa only [Fintype.card_fin] using hnR.trans (hdim.trans h4A)
    · have hcR : (finrank ℚ (D.dependentFreeSpan d) : ℝ) ≤
          finrank ℚ D.CoefficientFreeLieAlgebra := by
        exact_mod_cast Submodule.finrank_le (D.dependentFreeSpan d)
      simpa only [Fintype.card_fin] using hcR.trans ((hT.1.1.trans hQP').trans hPA)
    · intro j i
      exact (hc j i).trans hQA
    · intro i j
      exact (hheight 0 i j).trans haA
    · exact hlΛ.trans (Real.exp_le_exp.mpr hΛA)
  choose σ m hm hmb hσU hσfix hσnorm hσgrid using hsections
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have h18 : (t + 2) ^ 18 ≤ (t + 2) ^ 36 := pow_le_pow_right₀ (by linarith) (by decide)
  have hL : L = (t + 2) ^ 3 + (t + 2) ^ 36 + Λ := rfl
  have hCL : C + Λ ≤ L := by dsimp [C]; rw [hL]; linarith
  have hCL' : C ≤ L := (le_add_of_nonneg_right hΛ).trans hCL
  have hunit (d : Fin s) (y : Fin (n d) → ℝ)
      (hy : ∀ i, y i ∈ Set.Ico (0 : ℝ) (1 / l d)) : ‖y‖ ≤ 1 := by
    have hl : 0 < l d := (hdata d).2.2.2.2.1
    have hlR : (0 : ℝ) < l d := by exact_mod_cast hl
    have hl1 : (1 : ℝ) ≤ l d := by exact_mod_cast hl
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro i
    rw [Real.norm_eq_abs, abs_of_nonneg (hy i).1]
    exact (hy i).2.le.trans ((div_le_one hlR).mpr hl1)
  have hσunit (d : Fin s) (y : Fin (n d) → ℝ)
      (hy : ∀ i, y i ∈ Set.Ico (0 : ℝ) (1 / l d)) :
      ‖(E.basis.baseChange ℝ).equivFun (σ d y)‖ ≤ Real.exp L := by
    calc
      _ ≤ Real.exp C * ‖y‖ := hσnorm d y
      _ ≤ Real.exp C * 1 := mul_le_mul_of_nonneg_left (hunit d y hy) (Real.exp_pos _).le
      _ ≤ _ := by rw [mul_one]; exact Real.exp_le_exp.mpr hCL'
  refine ⟨D₁, hsub, hspaces, J, hJH, hJ, hcard, r₀, R₀, η, h₀, m,
    (fun d => σ d (α d)), (fun j d => σ d (β j d)), hrank, hproper, ?_, ?_, ?_, ?_⟩
  · intro d
    exact ⟨hm d, (hmb d).trans (Real.exp_le_exp.mpr (by rw [hL]; linarith))⟩
  · intro d
    exact ⟨hσU d _, hσunit d _ (hα d)⟩
  · intro j d
    exact ⟨hσU d _, hσunit d _ (hβ j d)⟩
  · intro h hh
    obtain ⟨x, hx, hspace, herr⟩ := hrepr h hh
    refine ⟨x, hx, hspace, ?_⟩
    intro d
    obtain ⟨q, hq, he⟩ := herr d
    obtain ⟨e, q', u, heU, hqU, hu, heq, hbound, hgrid⟩ :=
      affine_petal_decomposition E.basis (D.dependentFreeSpan d) _ (ℓ d) (hdata d).2.2.1
        (σ d) (hσU d) (hσfix d) (Real.exp_pos _).le (hσnorm d) (hσgrid d)
        (α d) (fun j => β j d) x (coefficients (v h).log (Finsupp.single () (d.val + 1)))
        (hv h d) q hq he
    refine ⟨e, q', u, heU, hqU, hu, heq, hbound.trans ?_, hgrid⟩
    calc
      Real.exp C * (Real.exp Λ / (N : ℝ) ^ (d.val + 1)) =
          Real.exp (C + Λ) / (N : ℝ) ^ (d.val + 1) := by rw [← mul_div_assoc, ← Real.exp_add]
      _ ≤ _ := div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hCL) (by positivity)

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module VectorPolynomial CyclicCrootSisask
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure r) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  (F : FreeCoordinateFrame E.basis Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s r) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

include F

theorem exists_shared_free_affine_orbit_family
    (hTfil : T.filtration = D.coefficientFreeFiltration)
    (hs : 2 ≤ s) (hp' : 0 ≤ p') (hP' : 0 ≤ P') (hQP' : Q ≤ P') (hpp' : p' ≤ P')
    (ξ : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (v : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hsplit : ∀ h, g h = ξ * v h)
    (hξ : ∀ d : Fin s, coefficients ξ.log (Finsupp.single () (d.val + 1)) ∈
      (D.commonFreeSpan d).baseChange ℝ)
    (hv : ∀ h (d : Fin s), coefficients (v h).log (Finsupp.single () (d.val + 1)) ∈
      (D.dependentFreeSpan d).baseChange ℝ)
    (hN : Real.exp ((P' + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s) ≤ (N : ℝ)) :
    let B := (P' + 2) ^ 3 + 2 * P'
    let Λ := (P' + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s
    let L := sharedFreePetalLiftBudget s Q P'
    ∃ D₁ : R'.CommonData B, D₁.quadruples ⊆ D'.quadruples ∧ D₁.spaces = D'.spaces ∧
      ∃ J ⊆ H', J.Nonempty ∧ Real.exp (-Λ) * H'.card ≤ (J.card : ℝ) ∧
        ∃ (r₀ : ℕ) (R₀ : Fin r₀ → ℕ) (η : (Fin r₀ → ℤ) →+ ZMod N) (h₀ : ZMod N)
          (m : ℕ) (α : Fin s → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
          (β : Fin r₀ → Fin s → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra),
          (r₀ : ℝ) ≤ Λ ∧ Set.InjOn η {x | ∀ j, |x j| ≤ (R₀ j : ℤ)} ∧ 0 < m ∧ (m : ℝ) ≤ Real.exp ((s : ℝ) * L) ∧
          (∀ d, α d ∈ (D.dependentFreeSpan d).baseChange ℝ ∧
            ‖(E.basis.baseChange ℝ).equivFun (α d)‖ ≤ Real.exp L) ∧
          (∀ j d, β j d ∈ (D.dependentFreeSpan d).baseChange ℝ ∧
            ‖(E.basis.baseChange ℝ).equivFun (β j d)‖ ≤ Real.exp L) ∧
          ∀ h ∈ J, ∃ x : Fin r₀ → ℤ,
            (∀ j, |x j| ≤ (R₀ j : ℤ)) ∧ h = h₀ + η x ∧
            ∃ A ε ρ U : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1),
              A.log = positiveUnivariate (fun d => α d + ∑ j, (x j : ℝ) • β j d) ∧
              E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 A = 1 ∧
              E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 ε = 1 ∧
              E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 ρ = 1 ∧
              E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 U = 1 ∧
              CoefficientBound (E.basis.baseChange ℝ) (fun _ : Unit => (N : ℝ)) (Real.exp L) ε.log ∧
              CoefficientGrid (E.basis.baseChange ℝ) m ρ.log ∧
              ∀ d : Fin s,
                coefficients U.log (Finsupp.single () (d.val + 1)) ∈
                  (fourPetalSpace (D.dependentFreeSpan d)
                    (fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
                      (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩))).baseChange ℝ ∧
                coefficients (v h).log (Finsupp.single () (d.val + 1)) =
                  coefficients A.log (Finsupp.single () (d.val + 1)) +
                  coefficients ε.log (Finsupp.single () (d.val + 1)) +
                  coefficients ρ.log (Finsupp.single () (d.val + 1)) +
                  coefficients U.log (Finsupp.single () (d.val + 1)) := by
  intro B Λ L
  classical
  obtain ⟨D₁, hsub, hspaces, J, hJH, hJ, hcard, r₀, R₀, η, h₀, l, α, β,
      hrank, hproper, hl, hα, hβ, hrepr⟩ :=
    D.exists_shared_free_affine_petal E T hbQ hT F V g hg D'
      hs hp' hP' hQP' hpp' ξ v hsplit hξ hv hN
  let m := ∏ d, l d
  have hm : 0 < m := Finset.prod_pos (fun d _ => (hl d).1)
  have hdiv (d : Fin s) : l d ∣ m := Finset.dvd_prod_of_mem l (Finset.mem_univ d)
  have hmb : (m : ℝ) ≤ Real.exp ((s : ℝ) * L) := by
    change ((∏ d, l d : ℕ) : ℝ) ≤ _
    rw [Nat.cast_prod]
    calc
      _ ≤ ∏ _d : Fin s, Real.exp L :=
        Finset.prod_le_prod (fun d _ => Nat.cast_nonneg (l d)) (fun d _ => (hl d).2)
      _ = _ := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Real.exp_nat_mul]
  refine ⟨D₁, hsub, hspaces, J, hJH, hJ, hcard, r₀, R₀, η, h₀, m, α, β,
    hrank, hproper, hm, hmb, hα, hβ, ?_⟩
  intro h hh
  obtain ⟨x, hx, hspace, hcoeff⟩ := hrepr h hh
  choose e q u he hq hu heq herr hgrid using hcoeff
  have hdep (d : Fin s) :=
    Submodule.baseChange_mono ℝ (D.dependentFreeSpan_le_coefficientFreeSpan d)
  have ha (d : Fin s) : α d + ∑ j, (x j : ℝ) • β j d ∈
      (D.coefficientFreeSpan d).baseChange ℝ := by
    apply hdep d
    exact Submodule.add_mem _ (hα d).1
      (Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (hβ j d).1))
  have huC (d : Fin s) : u d ∈ (D.coefficientFreeSpan d).baseChange ℝ :=
    hdep d (Submodule.baseChange_mono ℝ inf_le_left (hu d))
  obtain ⟨A, hA, hA0⟩ := D.exists_native_freeCoefficientPolynomialOrbit E T hTfil _ ha
  obtain ⟨ε, hε, hε0⟩ := D.exists_native_freeCoefficientPolynomialOrbit E T hTfil e
    (fun d => hdep d (he d))
  obtain ⟨ρ, hρ, hρ0⟩ := D.exists_native_freeCoefficientPolynomialOrbit E T hTfil q
    (fun d => hdep d (hq d))
  obtain ⟨U, hU, hU0⟩ := D.exists_native_freeCoefficientPolynomialOrbit E T hTfil u huC
  refine ⟨x, hx, hspace, A, ε, ρ, U, hA, hA0, hε0, hρ0, hU0, ?_, ?_, ?_⟩
  · rw [hε]
    apply positiveUnivariate_coefficientBound (E.basis.baseChange ℝ) e
      (fun _ : Unit => (N : ℝ)) (fun _ => by exact_mod_cast NeZero.pos N) (Real.exp_pos L).le
    intro d
    simpa only [monomialScale, Finsupp.prod_single_index, pow_zero] using herr d
  · rw [hρ]
    apply positiveUnivariate_coefficientGrid
    exact fun d => realDenominatorGrid_subset_of_dvd (hl d).1 (hdiv d) (hgrid d)
  · intro d
    rw [hA, hε, hρ, hU, positiveUnivariate_coefficient, positiveUnivariate_coefficient,
      positiveUnivariate_coefficient, positiveUnivariate_coefficient]
    exact ⟨hu d, heq d⟩

end Erdos3.NativeRankRelation.CommonData

end

end OAI

end


