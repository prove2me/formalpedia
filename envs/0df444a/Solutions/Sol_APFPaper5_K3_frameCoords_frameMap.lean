-- Prove2me | solution 1 for APFPaper5.K3.frameCoords_frameMap
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-14T08:03:13.336699+00:00
-- url     : https://prove2.me/submissions/4408142e-23e9-49ef-9f63-d77810b3148d

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-13; not gated, not reviewed)
name: APFPaper5_K3_carrier_representation
title: A space of held states that meets the checklist is the carrier of two held components, and generator completeness holds on it
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: as Def_APFPaper5_K3_CarrierFrame.
consumes_inputs: none. CONDITIONAL on the checklist IsTwoComponentCarrier. No model is supplied here: the
 statements hold for every space of held states that meets the checklist.
statement: (frame_gram) the four states a, its quarter turn, b and its quarter turn have unit cost and
 vanishing cross terms.
 (frameCoords_frameMap, frameMap_frameCoords) values and rates determine the held state and are determined
 by it.
 (frameMap_cross, frameMap_cost) the cross term of cost is the sum of products of values and rates, and the
 cost is the cost of the first component plus the cost of the second.
 (frameMap_commonTurn, frameMap_quarter, frameMap_add, frameMap_smul) the common turn, sums and scalings of
 held states are those of values and rates.
 (frameCoords_add, frameCoords_smul) reading values and rates is additive and homogeneous.
 (pullback_spec, pullback_additiveHomogeneous, pullback_preservesTotalCost, pullback_commutesWithQuarter) a
 map of held states that is additive, homogeneous, leaves cost unchanged and commutes with the quarter turn
 reads in values and rates as a map with the same properties.
 (carrier_generator_completeness) so it is built from turns and recombinations.
 (coordinate_space_is_carrier) four real coordinates, with the sum of products as cross term of cost, meet
 the checklist. So the checklist can be met.
not_claimed: that an interface meets the checklist; any K. Carries hroot in the last statement.
-/
import Definitions.Def_APFPaper5_K3_CarrierFrame
import Theorems.Thm_APFPaper5_K3_euler_core
import Theorems.Thm_APFPaper5_K3_expand_of_commutes
import Theorems.Thm_APFPaper5_K3_commuting_is_combination_of_built
import Theorems.Thm_APFPaper5_K3_generator_completeness
import Theorems.Thm_APFPaper5_K3_built_iff
import Theorems.Thm_APFPaper5_K3_admitted_is_built_or_flipped
import Theorems.Thm_APFPaper5_K3_admitted_iff
import Theorems.Thm_APFPaper5_K3_generator_completeness_of_halves
import Theorems.Thm_APFPaper5_K3_rateFlip_has_no_admitted_half
import Mathlib.Algebra.Module.Prod
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false
namespace APFPaper5.K3

open APFPaper5.K1

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem frame_gram (B : V → V → ℝ) (J : V → V) (a b : V) (hc : IsTwoComponentCarrier B J a b) :
    B a (J a) = 0 ∧ B (J a) a = 0 ∧ B (J a) (J a) = 1 ∧ B (J a) b = 0 ∧ B (J a) (J b) = 0 ∧
      B b a = 0 ∧ B b (J a) = 0 ∧ B b (J b) = 0 ∧ B (J b) a = 0 ∧ B (J b) (J a) = 0 ∧
      B (J b) b = 0 ∧ B (J b) (J b) = 1 := by
  obtain ⟨⟨_, h2, _, h4⟩, hsym, _, _, hJsq, hJB, haa, hbb, hab, haJb, _⟩ := hc
  have hneg : ∀ x y : V, B x (-y) = -(B x y) := by
    intro x y
    have e := h4 (-1) x y
    rw [neg_one_smul] at e
    linarith
  have hnegl : ∀ x y : V, B (-x) y = -(B x y) := by
    intro x y
    have e := h2 (-1) x y
    rw [neg_one_smul] at e
    linarith
  have skew : ∀ x : V, B x (J x) = 0 := by
    intro x
    have e := hJB x (J x)
    rw [hJsq, hneg] at e
    have s := hsym (J x) x
    linarith
  have g4 : B (J a) b = 0 := by
    have e := hJB (J a) b
    rw [hJsq, hnegl] at e
    linarith
  refine ⟨skew a, ?_, ?_, g4, ?_, ?_, ?_, skew b, ?_, ?_, ?_, ?_⟩
  · rw [hsym]; exact skew a
  · rw [hJB]; exact haa
  · rw [hJB]; exact hab
  · rw [hsym]; exact hab
  · rw [hsym]; exact g4
  · rw [hsym]; exact haJb
  · rw [hJB, hsym]; exact hab
  · rw [hsym]; exact skew b
  · rw [hJB]; exact hbb

theorem frameMap_cross (B : V → V → ℝ) (J : V → V) (a b : V) (hc : IsTwoComponentCarrier B J a b)
    (h k : Held2) :
    B (frameMap J a b h) (frameMap J a b k) =
      h.a1 * k.a1 + h.a2 * k.a2 + h.b1 * k.b1 + h.b2 * k.b2 := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12⟩ := frame_gram B J a b hc
  obtain ⟨⟨h1, h2, h3, h4⟩, _, _, _, _, _, haa, hbb, hab, haJb, _⟩ := hc
  dsimp only [frameMap]
  simp only [h1, h2, h3, h4, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, haa, hbb, hab, haJb]
  ring

theorem frameMap_cost (B : V → V → ℝ) (J : V → V) (a b : V) (hc : IsTwoComponentCarrier B J a b)
    (h : Held2) : B (frameMap J a b h) (frameMap J a b h) = totalCost h := by
  rw [frameMap_cross B J a b hc]
  dsimp only [totalCost, recA, recB]
  ring

theorem frameCoords_frameMap (B : V → V → ℝ) (J : V → V) (a b : V)
    (hc : IsTwoComponentCarrier B J a b) (h : Held2) :
    frameCoords B J a b (frameMap J a b h) = h := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12⟩ := frame_gram B J a b hc
  obtain ⟨⟨_, _, h3, h4⟩, _, _, _, _, _, haa, hbb, hab, haJb, _⟩ := hc
  apply Held2.ext <;> dsimp only [frameCoords, frameMap] <;>
    simp only [h3, h4, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, haa, hbb, hab, haJb] <;>
    ring

theorem frameMap_frameCoords (B : V → V → ℝ) (J : V → V) (a b : V)
    (hc : IsTwoComponentCarrier B J a b) (v : V) :
    frameMap J a b (frameCoords B J a b v) = v := by
  obtain ⟨x, y, z, w, hv⟩ := hc.2.2.2.2.2.2.2.2.2.2 v
  have e := frameCoords_frameMap B J a b hc ⟨x, y, z, w⟩
  rw [show frameMap J a b ⟨x, y, z, w⟩ = v from hv.symm] at e
  rw [e]
  exact hv.symm

theorem frameMap_injective (B : V → V → ℝ) (J : V → V) (a b : V)
    (hc : IsTwoComponentCarrier B J a b) (h k : Held2)
    (e : frameMap J a b h = frameMap J a b k) : h = k :=
  calc h = frameCoords B J a b (frameMap J a b h) := (frameCoords_frameMap B J a b hc h).symm
    _ = frameCoords B J a b (frameMap J a b k) := by rw [e]
    _ = k := frameCoords_frameMap B J a b hc k

theorem frameMap_commonTurn (B : V → V → ℝ) (J : V → V) (a b : V)
    (hc : IsTwoComponentCarrier B J a b) (c s : ℝ) (h : Held2) :
    frameMap J a b (commonTurn c s h) = c • frameMap J a b h + s • J (frameMap J a b h) := by
  obtain ⟨_, _, hJadd, hJsmul, hJsq, _⟩ := hc
  dsimp only [frameMap, commonTurn]
  simp only [hJadd, hJsmul, hJsq]
  module

theorem frameMap_quarter (B : V → V → ℝ) (J : V → V) (a b : V)
    (hc : IsTwoComponentCarrier B J a b) (h : Held2) :
    frameMap J a b (commonTurn 0 1 h) = J (frameMap J a b h) := by
  rw [frameMap_commonTurn B J a b hc]
  module

theorem frameMap_add (J : V → V) (a b : V) (h k : Held2) :
    frameMap J a b (add2 h k) = frameMap J a b h + frameMap J a b k := by
  dsimp only [frameMap, add2]
  module

theorem frameMap_smul (J : V → V) (a b : V) (r : ℝ) (h : Held2) :
    frameMap J a b (smul2 r h) = r • frameMap J a b h := by
  dsimp only [frameMap, smul2]
  module

theorem pullback_spec (B : V → V → ℝ) (J : V → V) (a b : V) (hc : IsTwoComponentCarrier B J a b)
    (T : V → V) (h : Held2) :
    frameMap J a b (pullback B J a b T h) = T (frameMap J a b h) :=
  frameMap_frameCoords B J a b hc (T (frameMap J a b h))

theorem frameCoords_add (B : V → V → ℝ) (J : V → V) (a b : V) (hB : IsBilinear B) (v w : V) :
    frameCoords B J a b (v + w) = add2 (frameCoords B J a b v) (frameCoords B J a b w) := by
  obtain ⟨_, _, h3, _⟩ := hB
  apply Held2.ext <;> dsimp only [frameCoords, add2] <;> rw [h3]

theorem frameCoords_smul (B : V → V → ℝ) (J : V → V) (a b : V) (hB : IsBilinear B) (r : ℝ)
    (v : V) : frameCoords B J a b (r • v) = smul2 r (frameCoords B J a b v) := by
  obtain ⟨_, _, _, h4⟩ := hB
  apply Held2.ext <;> dsimp only [frameCoords, smul2] <;> rw [h4]

theorem pullback_additiveHomogeneous (B : V → V → ℝ) (J : V → V) (a b : V)
    (hc : IsTwoComponentCarrier B J a b) (T : V → V) (hTadd : ∀ x y : V, T (x + y) = T x + T y)
    (hTsmul : ∀ (r : ℝ) (x : V), T (r • x) = r • T x) :
    AdditiveHomogeneous (pullback B J a b T) := by
  constructor
  · intro x y
    show frameCoords B J a b (T (frameMap J a b (add2 x y))) =
      add2 (frameCoords B J a b (T (frameMap J a b x))) (frameCoords B J a b (T (frameMap J a b y)))
    rw [frameMap_add, hTadd, frameCoords_add B J a b hc.1]
  · intro r x
    show frameCoords B J a b (T (frameMap J a b (smul2 r x))) =
      smul2 r (frameCoords B J a b (T (frameMap J a b x)))
    rw [frameMap_smul, hTsmul, frameCoords_smul B J a b hc.1]

theorem pullback_preservesTotalCost (B : V → V → ℝ) (J : V → V) (a b : V)
    (hc : IsTwoComponentCarrier B J a b) (T : V → V) (hT : ∀ v : V, B (T v) (T v) = B v v) :
    PreservesTotalCost (pullback B J a b T) := by
  intro h
  rw [← frameMap_cost B J a b hc (pullback B J a b T h), pullback_spec B J a b hc, hT,
    frameMap_cost B J a b hc]

theorem pullback_commutesWithQuarter (B : V → V → ℝ) (J : V → V) (a b : V)
    (hc : IsTwoComponentCarrier B J a b) (T : V → V) (hTJ : ∀ v : V, T (J v) = J (T v)) :
    CommutesWithQuarter (pullback B J a b T) := by
  intro h
  apply frameMap_injective B J a b hc
  rw [pullback_spec B J a b hc, frameMap_quarter B J a b hc, hTJ, frameMap_quarter B J a b hc,
    pullback_spec B J a b hc]

theorem carrier_generator_completeness (hroot : ∀ t : ℝ, 0 ≤ t → ∃ r : ℝ, 0 ≤ r ∧ r * r = t)
    (B : V → V → ℝ) (J : V → V) (a b : V) (hc : IsTwoComponentCarrier B J a b) (T : V → V)
    (hTadd : ∀ x y : V, T (x + y) = T x + T y) (hTsmul : ∀ (r : ℝ) (x : V), T (r • x) = r • T x)
    (hTcost : ∀ v : V, B (T v) (T v) = B v v) (hTJ : ∀ v : V, T (J v) = J (T v)) :
    ∃ U : Held2 → Held2, BuiltFromTurns U ∧ ∀ h : Held2, T (frameMap J a b h) = frameMap J a b (U h) :=
  ⟨pullback B J a b T,
    generator_completeness hroot _ (pullback_additiveHomogeneous B J a b hc T hTadd hTsmul)
      (pullback_preservesTotalCost B J a b hc T hTcost)
      (pullback_commutesWithQuarter B J a b hc T hTJ),
    fun h => (pullback_spec B J a b hc T h).symm⟩

theorem coordinate_space_is_carrier :
    IsTwoComponentCarrier coordCross coordQuarter (1, 0, 0, 0) (0, 0, 1, 0) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e e' p
    simp only [coordCross, Prod.fst_add, Prod.snd_add]
    ring
  · intro r e p
    simp only [coordCross, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  · intro e p p'
    simp only [coordCross, Prod.fst_add, Prod.snd_add]
    ring
  · intro r e p
    simp only [coordCross, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  · intro x y
    simp only [coordCross]
    ring
  · intro x y
    simp only [coordQuarter, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk, neg_add]
  · intro r x
    simp only [coordQuarter, Prod.smul_fst, Prod.smul_snd, Prod.smul_mk, smul_eq_mul, mul_neg]
  · intro x
    simp only [coordQuarter]
    rfl
  · intro x y
    simp only [coordCross, coordQuarter]
    ring
  · simp only [coordCross]; norm_num
  · simp only [coordCross]; norm_num
  · simp only [coordCross]; norm_num
  · simp only [coordCross, coordQuarter]; norm_num
  · intro v
    refine ⟨v.1, v.2.1, v.2.2.1, v.2.2.2, ?_⟩
    simp only [coordQuarter, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, mul_one, mul_zero, neg_zero,
      add_zero, zero_add]

end APFPaper5.K3


universe apfNative_u_1
theorem solution :
∀ {V : Type apfNative_u_1} [inst : AddCommGroup.{apfNative_u_1} V]
  [inst_1 :
    @_root_.Module.{0, apfNative_u_1} Real V Real.semiring (@AddCommGroup.toAddCommMonoid.{apfNative_u_1} V inst)]
  (B : V → V → Real) (J : V → V) (a b : V)
  (hc : @APFPaper5.K3.IsTwoComponentCarrier.{apfNative_u_1} V inst inst_1 B J a b) (h : APFPaper5.K3.Held2),
  @Eq.{1} APFPaper5.K3.Held2
    (@APFPaper5.K3.frameCoords.{apfNative_u_1} V B J a b (@APFPaper5.K3.frameMap.{apfNative_u_1} V inst inst_1 J a b h))
    h := by
  exact @APFPaper5.K3.frameCoords_frameMap
