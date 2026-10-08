-- Prove2me | solution 1 for AnosovPlugs.flowMap_contMDiffOn_of_localSteps
-- status  : ACCEPTED   (prove)
-- author  : @ebayuser
-- created : 2026-10-04T20:36:36.40832+00:00
-- url     : https://prove2.me/submissions/60dd8268-302c-4516-8dea-babaf9c64ede

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing

open scoped Manifold ContDiff Topology
open Set AnosovPlugs

section ChHelpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {v : (x : M) → TangentSpace I x}

/-- Change the point `p` in the derivative `smulRight (v p)` to an equal point `q`. -/
theorem ch_congr_val {f : ℝ → M} {S : Set ℝ} {s : ℝ} {p q : M}
    (h : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I f S s ((1 : ℝ →L[ℝ] ℝ).smulRight (v p)))
    (hp : p = q) :
    HasMFDerivWithinAt 𝓘(ℝ, ℝ) I f S s ((1 : ℝ →L[ℝ] ℝ).smulRight (v q)) := by
  subst hp
  exact h

/-- Congruence: an integral curve on `A` stays an integral curve after a change off `A`. -/
theorem ch_congr {γ γ₁ : ℝ → M} {A : Set ℝ} (h : IsMIntegralCurveOn γ₁ v A)
    (heq : EqOn γ γ₁ A) : IsMIntegralCurveOn γ v A := by
  intro s hs
  exact ch_congr_val ((h s hs).congr_mono (fun x hx => heq hx) (heq hs) subset_rfl) (heq hs).symm

/-- Gluing of integral curves on two closed sets. -/
theorem ch_union {γ : ℝ → M} {A B : Set ℝ} (hA : IsMIntegralCurveOn γ v A)
    (hB : IsMIntegralCurveOn γ v B) (hAc : IsClosed A) (hBc : IsClosed B) :
    IsMIntegralCurveOn γ v (A ∪ B) := by
  intro s hs
  by_cases hsA : s ∈ A
  · by_cases hsB : s ∈ B
    · exact (hA s hsA).union (hB s hsB)
    · refine (hA s hsA).mono_of_mem_nhdsWithin
        (mem_nhdsWithin.2 ⟨Bᶜ, hBc.isOpen_compl, hsB, fun x hx => ?_⟩)
      rcases hx.2 with h | h
      · exact h
      · exact absurd h hx.1
  · have hsB : s ∈ B := hs.resolve_left hsA
    refine (hB s hsB).mono_of_mem_nhdsWithin
      (mem_nhdsWithin.2 ⟨Aᶜ, hAc.isOpen_compl, hsA, fun x hx => ?_⟩)
    rcases hx.2 with h | h
    · exact absurd h hx.1
    · exact h

/-- A curve on `uIcc 0 (b - a)`, shifted by `a`, is an integral curve on `uIcc a b`. -/
theorem ch_shift_from_zero {η : ℝ → M} {a b : ℝ} (h : IsMIntegralCurveOn η v (uIcc 0 (b - a))) :
    IsMIntegralCurveOn (fun s => η (s - a)) v (uIcc a b) := by
  have h1 := (isMIntegralCurveOn_comp_sub (dt := a)).2 h
  have e : {s : ℝ | s - a ∈ uIcc 0 (b - a)} = uIcc a b := by
    rw [show {s : ℝ | s - a ∈ uIcc 0 (b - a)} = (fun x => x - a) ⁻¹' uIcc 0 (b - a) from rfl,
      preimage_sub_const_uIcc, zero_add, sub_add_cancel]
  rw [e] at h1
  exact h1

/-- A curve on `uIcc a b`, shifted back by `a`, is an integral curve on `uIcc 0 (b - a)`. -/
theorem ch_shift_to_zero {γ : ℝ → M} {a b : ℝ} (hγ : IsMIntegralCurveOn γ v (uIcc a b)) :
    IsMIntegralCurveOn (fun τ => γ (τ + a)) v (uIcc 0 (b - a)) := by
  have h1 := hγ.comp_add a
  have e : {τ : ℝ | τ + a ∈ uIcc a b} = uIcc 0 (b - a) := by
    rw [show {τ : ℝ | τ + a ∈ uIcc a b} = (fun x => x + a) ⁻¹' uIcc a b from rfl,
      preimage_add_const_uIcc, sub_self]
  rw [e] at h1
  exact h1

end ChHelpers

theorem solution
    {N : Type} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace 3) N] [IsManifold I3 ∞ N]
    (Z : (w : N) → TangentSpace I3 w)
    (huniq : ∀ (γ γ' : ℝ → N) (t : ℝ), IsMIntegralCurveOn γ Z (uIcc 0 t) → IsMIntegralCurveOn γ' Z (uIcc 0 t) →
        γ' 0 = γ 0 → ∀ s ∈ uIcc 0 t, γ' s = γ s)
    (γ : ℝ → N) (t : ℝ) (hγ : IsMIntegralCurveOn γ Z (uIcc 0 t))
    (hloc : ∀ s ∈ uIcc 0 t,
      ∃ ε > (0 : ℝ), ∃ O : Set N, IsOpen O ∧ γ s ∈ O ∧ ∀ h : ℝ, |h| ≤ ε → ∃ f : N → N,
        ContMDiffOn I3 I3 1 f O ∧
        ∀ y ∈ O, ∃ η : ℝ → N, η 0 = y ∧ IsMIntegralCurveOn η Z (uIcc 0 h) ∧ η h = f y) :
    ∃ O : Set N, IsOpen O ∧ γ 0 ∈ O ∧
      (∀ y ∈ O, FlowDefined Z y t) ∧ ContMDiffOn I3 I3 1 (flowMap Z t) O := by
  classical
  -- the invariant of the induction
  let Q : ℝ → Prop := fun a => ∃ Ok : Set N, IsOpen Ok ∧ γ 0 ∈ Ok ∧ ∃ F : N → N,
    ContMDiffOn I3 I3 1 F Ok ∧ F (γ 0) = γ a ∧
    ∀ y ∈ Ok, ∃ η : ℝ → N, η 0 = y ∧ IsMIntegralCurveOn η Z (uIcc 0 a) ∧ η a = F y
  -- the base case
  have hQ0 : Q 0 := by
    obtain ⟨ε, hε, O, hO, hxO, hf⟩ := hloc 0 left_mem_uIcc
    obtain ⟨f, -, hfη⟩ := hf 0 (by rw [abs_zero]; exact hε.le)
    refine ⟨O, hO, hxO, id, contMDiffOn_id, rfl, fun y hy => ?_⟩
    obtain ⟨η, h0, hc, -⟩ := hfη y hy
    exact ⟨η, h0, hc, h0⟩
  -- the local step data along `γ`
  have hdata := fun s : uIcc 0 t => hloc s s.2
  choose ε hε O hO hγO hf using hdata
  have hV : ∀ σ : uIcc 0 t, ∃ V : Set ℝ, IsOpen V ∧ γ ⁻¹' O σ ∩ uIcc 0 t = V ∩ uIcc 0 t :=
    fun σ => continuousOn_iff'.1 hγ.continuousOn _ (hO σ)
  choose V hVo hVeq using hV
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric (isCompact_uIcc (a := (0:ℝ)) (b := t))
    (c := fun σ : uIcc 0 t => V σ ∩ Metric.ball (σ : ℝ) (ε σ / 2))
    (fun σ => (hVo σ).inter Metric.isOpen_ball) (by
      intro s hs
      refine mem_iUnion.2 ⟨⟨s, hs⟩, ?_, ?_⟩
      · have : s ∈ γ ⁻¹' O ⟨s, hs⟩ ∩ uIcc 0 t := ⟨hγO ⟨s, hs⟩, hs⟩
        rw [hVeq] at this
        exact this.1
      · exact Metric.mem_ball_self (half_pos (hε _)))
  -- the induction step
  have hstep : ∀ a b : ℝ, a ∈ uIcc 0 b → b ∈ uIcc 0 t → |b - a| < δ → Q a → Q b := by
    intro a b hab hbt hδab hQa
    by_cases hba : b ∈ uIcc 0 a
    · have : a = b := by
        rcases mem_uIcc.1 hab with ⟨_, _⟩ | ⟨_, _⟩ <;>
          rcases mem_uIcc.1 hba with ⟨_, _⟩ | ⟨_, _⟩ <;> linarith
      rw [← this]
      exact hQa
    obtain ⟨Ok, hOk, h0Ok, F, hFC, hFγ, hη⟩ := hQa
    have hat : a ∈ uIcc 0 t := uIcc_subset_uIcc left_mem_uIcc hbt hab
    obtain ⟨σ, hσ⟩ := hleb a hat
    have hP : uIcc a b ⊆ uIcc 0 t := uIcc_subset_uIcc hat hbt
    have hPball : uIcc a b ⊆ V σ ∩ Metric.ball (σ : ℝ) (ε σ / 2) := by
      intro s hs
      apply hσ
      rw [Metric.mem_ball, Real.dist_eq]
      exact (abs_sub_left_of_mem_uIcc hs).trans_lt hδab
    have hγaO : γ a ∈ O σ := by
      have : a ∈ V σ ∩ uIcc 0 t := ⟨(hPball left_mem_uIcc).1, hat⟩
      rw [← hVeq] at this
      exact this.1
    have hlen : |b - a| ≤ ε σ := by
      have h1 := (hPball left_mem_uIcc).2
      have h2 := (hPball right_mem_uIcc).2
      rw [Metric.mem_ball, Real.dist_eq] at h1 h2
      have h1' := abs_lt.1 h1
      have h2' := abs_lt.1 h2
      exact abs_le.2 ⟨by linarith, by linarith⟩
    obtain ⟨g, hgC, hgη⟩ := hf σ (b - a) hlen
    have key : g (γ a) = γ b := by
      obtain ⟨η0, h00, h0c, h0e⟩ := hgη (γ a) hγaO
      have := huniq (fun τ => γ (τ + a)) η0 (b - a) (ch_shift_to_zero (hγ.mono hP)) h0c
        (by simp [h00]) (b - a) right_mem_uIcc
      rw [← h0e, this]
      simp
    refine ⟨Ok ∩ F ⁻¹' O σ, hFC.continuousOn.isOpen_inter_preimage hOk (hO σ),
      ⟨h0Ok, by simp only [mem_preimage, hFγ]; exact hγaO⟩, g ∘ F,
      hgC.comp (hFC.mono inter_subset_left) (fun y hy => hy.2),
      by simp only [Function.comp_apply, hFγ, key], fun y hy => ?_⟩
    obtain ⟨η, h0, hc, he⟩ := hη y hy.1
    obtain ⟨η2, h20, h2c, h2e⟩ := hgη (F y) hy.2
    have hseam : ∀ s ∈ uIcc a b, s ∈ uIcc 0 a → s = a := by
      intro s hs1 hs2
      rcases mem_uIcc.1 hs1 with ⟨_, _⟩ | ⟨_, _⟩ <;>
        rcases mem_uIcc.1 hs2 with ⟨_, _⟩ | ⟨_, _⟩ <;>
        rcases mem_uIcc.1 hab with ⟨_, _⟩ | ⟨_, _⟩ <;> linarith
    let Γ : ℝ → N := fun s => if s ∈ uIcc 0 a then η s else η2 (s - a)
    have hc1 : IsMIntegralCurveOn Γ Z (uIcc 0 a) :=
      ch_congr hc (fun s hs => by simp only [Γ, if_pos hs])
    have hc2 : IsMIntegralCurveOn Γ Z (uIcc a b) := by
      refine ch_congr (ch_shift_from_zero h2c) (fun s hs => ?_)
      by_cases hs0 : s ∈ uIcc 0 a
      · have hsa := hseam s hs hs0
        simp only [Γ, if_pos hs0]
        rw [hsa, sub_self, h20, he]
      · simp only [Γ, if_neg hs0]
    refine ⟨Γ, by simp only [Γ, if_pos (left_mem_uIcc : (0:ℝ) ∈ uIcc 0 a), h0], ?_, ?_⟩
    · exact (ch_union hc1 hc2 isCompact_uIcc.isClosed isCompact_uIcc.isClosed).mono
        uIcc_subset_uIcc_union_uIcc
    · simp only [Γ, if_neg hba, Function.comp_apply, h2e]
  -- the subdivision
  obtain ⟨M, hM⟩ := exists_nat_gt (|t| / δ)
  have hMpos : (0:ℝ) < M := lt_of_le_of_lt (div_nonneg (abs_nonneg t) hδ.le) hM
  have hM0 : (M:ℝ) ≠ 0 := hMpos.ne'
  set h := t / M with hh_def
  have htM : (M:ℝ) * h = t := by
    rw [hh_def]
    field_simp
  have hhδ : |h| < δ := by
    rw [hh_def, abs_div, Nat.abs_cast, div_lt_iff₀ hMpos]
    rw [div_lt_iff₀ hδ] at hM
    linarith
  have hind : ∀ k : ℕ, k ≤ M → Q ((k:ℝ) * h) := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [Nat.cast_zero, zero_mul]
      exact hQ0
    | succ k ih =>
      intro hk
      have hk' : ((k:ℝ) + 1) ≤ M := by exact_mod_cast hk
      have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
      push_cast
      refine hstep _ _ ?_ ?_ ?_ (ih (by omega))
      · rw [mem_uIcc]
        rcases le_total 0 h with hh | hh
        · left
          constructor <;> nlinarith
        · right
          constructor <;> nlinarith
      · rw [mem_uIcc, ← htM]
        rcases le_total 0 h with hh | hh
        · left
          constructor <;> nlinarith
        · right
          constructor <;> nlinarith
      · rw [show ((k:ℝ) + 1) * h - k * h = h by ring]
        exact hhδ
  have hfin := hind M le_rfl
  rw [htM] at hfin
  obtain ⟨Ok, hOk, h0Ok, F, hFC, -, hη⟩ := hfin
  have hfd : ∀ y ∈ Ok, FlowDefined Z y t := by
    intro y hy
    obtain ⟨η, h0, hc, -⟩ := hη y hy
    exact ⟨η, h0, hc⟩
  refine ⟨Ok, hOk, h0Ok, hfd, hFC.congr fun y hy => ?_⟩
  obtain ⟨η, h0, hc, he⟩ := hη y hy
  have hd := hfd y hy
  unfold flowMap
  rw [dif_pos hd]
  obtain ⟨h0', hc'⟩ := hd.choose_spec
  rw [← he]
  exact huniq η hd.choose t hc hc' (by rw [h0', h0]) t right_mem_uIcc
