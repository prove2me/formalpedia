-- Prove2me | solution 1 for AnosovPlugs.exists_riemannianMetric3
-- status  : ACCEPTED   (prove)
-- author  : @ebayuser
-- created : 2026-10-03T19:13:18.792895+00:00
-- url     : https://prove2.me/submissions/eb889694-680c-4873-9433-4bd4e21a0755

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing

open scoped Manifold ContDiff Topology
open Set Bundle AnosovPlugs

/-- A positive definite bilinear form on a finite-dimensional normed space is coercive. -/
theorem rm_exists_coercive {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (φ : F →L[ℝ] F →L[ℝ] ℝ) (h : ∀ v ≠ 0, 0 < φ v v) :
    ∃ m > 0, ∀ v, m * ‖v‖ ^ 2 ≤ φ v v := by
  rcases subsingleton_or_nontrivial F with hF | hF
  · refine ⟨1, one_pos, fun v => ?_⟩
    rw [Subsingleton.elim v 0]
    simp
  have hcont : Continuous fun v : F => φ v v := by fun_prop
  have hne : (Metric.sphere (0 : F) 1).Nonempty := NormedSpace.sphere_nonempty.mpr zero_le_one
  obtain ⟨v₀, hv₀, hmin⟩ :=
    (isCompact_sphere (0 : F) 1).exists_isMinOn hne hcont.continuousOn
  have hv₀n : ‖v₀‖ = 1 := by simpa using hv₀
  have hv₀0 : v₀ ≠ 0 := by
    intro h0
    simp [h0] at hv₀n
  refine ⟨φ v₀ v₀, h v₀ hv₀0, fun v => ?_⟩
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hu : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : F) 1 := by
    simp [norm_smul, hvn.ne']
  have := hmin hu
  have h2 : φ v₀ v₀ ≤ (‖v‖⁻¹ * ‖v‖⁻¹) * φ v v := by
    simpa [mul_assoc] using this
  have h3 : ‖v‖ ^ 2 * (‖v‖⁻¹ * ‖v‖⁻¹) = 1 := by
    field_simp
  have h4 : ‖v‖ ^ 2 * φ v₀ v₀ ≤ ‖v‖ ^ 2 * ((‖v‖⁻¹ * ‖v‖⁻¹) * φ v v) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  calc φ v₀ v₀ * ‖v‖ ^ 2 = ‖v‖ ^ 2 * φ v₀ v₀ := by ring
    _ ≤ ‖v‖ ^ 2 * ((‖v‖⁻¹ * ‖v‖⁻¹) * φ v v) := h4
    _ = (‖v‖ ^ 2 * (‖v‖⁻¹ * ‖v‖⁻¹)) * φ v v := by ring
    _ = φ v v := by rw [h3, one_mul]

/-- The sublevel set of a positive definite form is von Neumann bounded. -/
theorem rm_isVonNBounded {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (φ : F →L[ℝ] F →L[ℝ] ℝ) (h : ∀ v ≠ 0, 0 < φ v v) :
    Bornology.IsVonNBounded ℝ {v : F | φ v v < 1} := by
  obtain ⟨m, hm, hφ⟩ := rm_exists_coercive φ h
  rw [NormedSpace.isVonNBounded_iff']
  refine ⟨1 + 1 / m, fun v hv => ?_⟩
  have hv' : φ v v < 1 := hv
  have h1 := hφ v
  by_contra hcon'
  have hcon := not_le.mp hcon'
  have hpos : 0 < 1 / m := by positivity
  have hge1 : 1 ≤ ‖v‖ := by linarith
  have : m * ‖v‖ ≤ m * ‖v‖ ^ 2 :=
    mul_le_mul_of_nonneg_left (by nlinarith) hm.le
  have hmv : m * (1 + 1 / m) < m * ‖v‖ := by nlinarith
  have : m * (1 + 1 / m) = m + 1 := by field_simp
  nlinarith

/-- Positive definite symmetric bilinear forms form a convex set. -/
theorem rm_convex {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] :
    Convex ℝ {φ : E →L[ℝ] E →L[ℝ] ℝ | (∀ v w, φ v w = φ w v) ∧ ∀ v ≠ 0, 0 < φ v v} := by
  intro φ hφ ψ hψ a c ha hc hac
  refine ⟨fun v w => ?_, fun v hv => ?_⟩
  · simp [hφ.1 v w, hψ.1 v w]
  · have hp := hφ.2 v hv
    have hq := hψ.2 v hv
    show 0 < (a • φ + c • ψ) v v
    rw [show (a • φ + c • ψ) v v = a * φ v v + c * ψ v v from rfl]
    rcases ha.eq_or_lt with h | h
    · subst h
      have : c = 1 := by linarith
      subst this
      simpa using hq
    · have := mul_pos h hp
      have := mul_nonneg hc hq.le
      linarith

local notation "F3" => EuclideanSpace ℝ (Fin 3)

set_option synthInstance.maxHeartbeats 400000 in
/-- A bilinear form on a tangent space, read in the trivialization at `x₀`. -/
theorem rm_apply_eq {N : Type} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace 3) N]
    [IsManifold I3 ∞ N] (x₀ y : N)
    (hy : y ∈ (trivializationAt F3 (TangentSpace I3 : N → Type) x₀).baseSet)
    (φ : TangentSpace I3 y →L[ℝ] TangentSpace I3 y →L[ℝ] ℝ) (u u' : TangentSpace I3 y) :
    φ u u' = (trivializationAt (F3 →L[ℝ] F3 →L[ℝ] ℝ)
      (fun b : N => TangentSpace I3 b →L[ℝ] TangentSpace I3 b →L[ℝ] ℝ) x₀ ⟨y, φ⟩).2
        ((trivializationAt F3 (TangentSpace I3 : N → Type) x₀ ⟨y, u⟩).2)
        ((trivializationAt F3 (TangentSpace I3 : N → Type) x₀ ⟨y, u'⟩).2) := by
  rw [hom_trivializationAt_apply]
  dsimp only
  rw [inCoordinates_apply_eq₂ hy hy (mem_univ _)]
  rw [Trivialization.symm_apply_apply_mk _ hy, Trivialization.symm_apply_apply_mk _ hy]
  rw [Trivialization.coe_linearMapAt_of_mem _ (mem_univ _)]
  rfl

/-- The section of a vector bundle that is constant in a trivialization is smooth on the base
set of that trivialization. -/
theorem rm_const_section {B : Type*} [TopologicalSpace B] {EB : Type*} [NormedAddCommGroup EB]
    [NormedSpace ℝ EB] {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
    [ChartedSpace HB B] {n : WithTop ℕ∞} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (V : B → Type*) [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
    [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V]
    [VectorBundle ℝ F V] [ContMDiffVectorBundle n F V IB] (x₀ : B) (c : F) :
    ContMDiffOn IB (IB.prod 𝓘(ℝ, F)) n
        (fun x => TotalSpace.mk' F x ((trivializationAt F V x₀).symmL ℝ x c))
        (trivializationAt F V x₀).baseSet ∧
      ∀ y ∈ (trivializationAt F V x₀).baseSet,
        (trivializationAt F V x₀ ⟨y, (trivializationAt F V x₀).symmL ℝ y c⟩).2 = c := by
  have hval : ∀ y ∈ (trivializationAt F V x₀).baseSet,
      (trivializationAt F V x₀ ⟨y, (trivializationAt F V x₀).symmL ℝ y c⟩).2 = c := by
    intro y hy
    rw [← (trivializationAt F V x₀).continuousLinearMapAt_apply_of_mem ℝ hy,
      (trivializationAt F V x₀).continuousLinearMapAt_symmL hy]
  refine ⟨?_, hval⟩
  rw [(trivializationAt F V x₀).contMDiffOn_section_baseSet_iff]
  exact contMDiffOn_const.congr hval

set_option synthInstance.maxHeartbeats 400000 in
theorem solution
    {N : Type} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace 3) N] [IsManifold I3 ∞ N]
    [T2Space N] [SigmaCompactSpace N] :
    Nonempty (RiemannianMetric3 N) := by
  have key := exists_contMDiffSection_forall_mem_convex_of_local (n := ⊤) (M := N) I3
    (F_fiber := F3 →L[ℝ] F3 →L[ℝ] ℝ)
    (fun b : N => TangentSpace I3 b →L[ℝ] TangentSpace I3 b →L[ℝ] ℝ)
    (fun b => {φ | (∀ v w, φ v w = φ w v) ∧ ∀ v ≠ 0, 0 < φ v v})
  have h1 : ∀ b : N, Convex ℝ {φ : TangentSpace I3 b →L[ℝ] TangentSpace I3 b →L[ℝ] ℝ |
      (∀ v w, φ v w = φ w v) ∧ ∀ v ≠ 0, 0 < φ v v} := fun b => rm_convex
  have key2 := key h1
  obtain ⟨s, hs⟩ := key2 (fun x₀ => by
    obtain ⟨hsm, hval⟩ := rm_const_section (n := ∞) (IB := I3) (F := F3 →L[ℝ] F3 →L[ℝ] ℝ)
      (fun b : N => TangentSpace I3 b →L[ℝ] TangentSpace I3 b →L[ℝ] ℝ) x₀ (innerSL ℝ)
    refine ⟨_, ?_, _, hsm, fun y hy => ?_⟩
    · exact (trivializationAt _ _ x₀).open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt' x₀)
    have hy' : y ∈ (trivializationAt F3 (TangentSpace I3 : N → Type) x₀).baseSet := by
      have h : y ∈ (trivializationAt F3 (TangentSpace I3 : N → Type) x₀).baseSet ∩
        ((trivializationAt F3 (TangentSpace I3 : N → Type) x₀).baseSet ∩ univ) := hy
      exact h.1
    have main : ∀ φ : TangentSpace I3 y →L[ℝ] TangentSpace I3 y →L[ℝ] ℝ,
        (trivializationAt (F3 →L[ℝ] F3 →L[ℝ] ℝ)
          (fun b : N => TangentSpace I3 b →L[ℝ] TangentSpace I3 b →L[ℝ] ℝ) x₀ ⟨y, φ⟩).2 =
          (innerSL ℝ : F3 →L[ℝ] F3 →L[ℝ] ℝ) →
        (∀ v w, φ v w = φ w v) ∧ ∀ v ≠ 0, 0 < φ v v := by
      intro φ hφ
      have hk : ∀ u u' : TangentSpace I3 y, φ u u' =
          inner ℝ (trivializationAt F3 (TangentSpace I3 : N → Type) x₀ ⟨y, u⟩).2
            (trivializationAt F3 (TangentSpace I3 : N → Type) x₀ ⟨y, u'⟩).2 := by
        intro u u'
        rw [rm_apply_eq x₀ y hy' φ u u', hφ, innerSL_apply_apply]
      refine ⟨fun u u' => by rw [hk, hk, real_inner_comm], fun u hu => ?_⟩
      rw [hk]
      refine real_inner_self_pos.2 fun h0 => hu ?_
      exact ((trivializationAt F3 (TangentSpace I3 : N → Type) x₀).continuousLinearEquivAt ℝ y
        hy').map_eq_zero_iff.mp h0
    exact main _ (hval y hy))
  exact ⟨{ inner := fun b => s b
           symm := fun b => (hs b).1
           pos := fun b => (hs b).2
           isVonNBounded := fun b => rm_isVonNBounded (F := F3) (s b) (hs b).2
           continuous := s.contMDiff.continuous }⟩

