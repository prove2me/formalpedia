-- Prove2me | solution 1 for AnosovPlugs.exists_integralCurveOn_nhds_of_localFlow
-- status  : ACCEPTED   (prove)
-- author  : @ebayuser
-- created : 2026-10-03T19:13:19.401827+00:00
-- url     : https://prove2.me/submissions/413754f8-8be7-44ce-9da8-809d93ec4761

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing

open scoped Manifold ContDiff Topology
open Set
open AnosovPlugs

section GlHelpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {v : (x : M) → TangentSpace I x}

/-- Change the point `p` in the derivative `smulRight (v p)` to an equal point `q`. -/
theorem gl_congr_val {f : ℝ → M} {S : Set ℝ} {s : ℝ} {p q : M}
    (h : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I f S s ((1 : ℝ →L[ℝ] ℝ).smulRight (v p)))
    (hp : p = q) :
    HasMFDerivWithinAt 𝓘(ℝ, ℝ) I f S s ((1 : ℝ →L[ℝ] ℝ).smulRight (v q)) := by
  subst hp
  exact h

/-- Congruence: an integral curve on `A` stays an integral curve after a change off `A`. -/
theorem gl_congr {γ γ₁ : ℝ → M} {A : Set ℝ} (h : IsMIntegralCurveOn γ₁ v A)
    (heq : EqOn γ γ₁ A) : IsMIntegralCurveOn γ v A := by
  intro s hs
  exact gl_congr_val ((h s hs).congr_mono (fun x hx => heq hx) (heq hs) subset_rfl) (heq hs).symm

/-- Gluing of integral curves on two closed sets. -/
theorem gl_union {γ : ℝ → M} {A B : Set ℝ} (hA : IsMIntegralCurveOn γ v A)
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

/-- A curve on `Icc (-ε) ε`, shifted by `a`, is an integral curve on `uIcc a b`. -/
theorem gl_shift_to_piece {β : ℝ → M} {ε a b : ℝ} (hβ : IsMIntegralCurveOn β v (Icc (-ε) ε))
    (hab : |b - a| ≤ ε) : IsMIntegralCurveOn (fun s => β (s - a)) v (uIcc a b) := by
  have h1 := (isMIntegralCurveOn_comp_sub (dt := a)).2 hβ
  refine h1.mono fun s hs => ?_
  have := (abs_sub_left_of_mem_uIcc hs).trans hab
  exact abs_le.1 this

/-- A curve on `uIcc a b`, shifted back by `a`, is an integral curve on `uIcc 0 (b - a)`. -/
theorem gl_shift_to_zero {γ : ℝ → M} {a b : ℝ} (hγ : IsMIntegralCurveOn γ v (uIcc a b)) :
    IsMIntegralCurveOn (fun τ => γ (τ + a)) v (uIcc 0 (b - a)) := by
  have h1 := hγ.comp_add a
  have e : {τ : ℝ | τ + a ∈ uIcc a b} = uIcc 0 (b - a) := by
    rw [show {τ : ℝ | τ + a ∈ uIcc a b} = (fun x => x + a) ⁻¹' uIcc a b from rfl,
      preimage_add_const_uIcc, sub_self]
  rw [e] at h1
  exact h1

end GlHelpers

theorem solution
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold I3 ∞ M]
    (X : (x : M) → TangentSpace I3 x)
    (hflow : ∀ x₀ : M, I3.IsInteriorPoint x₀ →
      ∃ ε > (0 : ℝ), ∃ O : Set M, IsOpen O ∧ x₀ ∈ O ∧ ∃ α : M → ℝ → M,
        (∀ y ∈ O, α y 0 = y ∧ IsMIntegralCurveOn (α y) X (Icc (-ε) ε) ∧
          ∀ τ ∈ Icc (-ε) ε, I3.IsInteriorPoint (α y τ)) ∧
        (∀ τ ∈ Icc (-ε) ε, ContinuousOn (fun y => α y τ) O) ∧
        (∀ y ∈ O, ∀ h : ℝ, |h| ≤ ε → ∀ η : ℝ → M, η 0 = y →
          IsMIntegralCurveOn η X (uIcc 0 h) → (∀ τ ∈ uIcc 0 h, η τ ∈ O) →
          ∀ τ ∈ uIcc 0 h, η τ = α y τ))
    (γ : ℝ → M) (t : ℝ)
    (hγ : IsMIntegralCurveOn γ X (uIcc 0 t)) (hint : ∀ s ∈ uIcc 0 t, I3.IsInteriorPoint (γ s)) :
    ∀ᶠ y in 𝓝 (γ 0), ∃ γ' : ℝ → M, γ' 0 = y ∧ IsMIntegralCurveOn γ' X (uIcc 0 t) ∧
      ∀ s ∈ uIcc 0 t, I3.IsInteriorPoint (γ' s) := by
  classical
  -- the invariant of the induction
  let Q : ℝ → Prop := fun a => ∃ Γ : M → ℝ → M,
    (∀ᶠ y in 𝓝 (γ 0), Γ y 0 = y ∧ IsMIntegralCurveOn (Γ y) X (uIcc 0 a) ∧
      ∀ s ∈ uIcc 0 a, I3.IsInteriorPoint (Γ y s)) ∧
    Filter.Tendsto (fun y => Γ y a) (𝓝 (γ 0)) (𝓝 (γ a))
  -- the base case
  have hQ0 : Q 0 := by
    obtain ⟨ε, hε, O, hO, hxO, α, hα, -, -⟩ := hflow (γ 0) (hint 0 left_mem_uIcc)
    refine ⟨α, ?_, ?_⟩
    · filter_upwards [hO.mem_nhds hxO] with y hy
      obtain ⟨h0, hc, hi⟩ := hα y hy
      have hsub : uIcc (0:ℝ) 0 ⊆ Icc (-ε) ε := by
        rw [uIcc_self]
        intro s hs
        rw [mem_singleton_iff.1 hs]
        constructor <;> linarith
      exact ⟨h0, hc.mono hsub, fun s hs => hi s (hsub hs)⟩
    · refine Filter.tendsto_id.congr' ?_
      filter_upwards [hO.mem_nhds hxO] with y hy
      exact (hα y hy).1.symm
  -- the local flow data along `γ`
  have hdata := fun s : uIcc 0 t => hflow (γ s) (hint s s.2)
  choose ε hε O hO hγO α hα hcont huniq using hdata
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
    obtain ⟨Γ, hE, hT⟩ := hQa
    have hat : a ∈ uIcc 0 t := uIcc_subset_uIcc left_mem_uIcc hbt hab
    obtain ⟨σ, hσ⟩ := hleb a hat
    have hP : uIcc a b ⊆ uIcc 0 t := uIcc_subset_uIcc hat hbt
    have hPball : uIcc a b ⊆ V σ ∩ Metric.ball (σ : ℝ) (ε σ / 2) := by
      intro s hs
      apply hσ
      rw [Metric.mem_ball, Real.dist_eq]
      exact (abs_sub_left_of_mem_uIcc hs).trans_lt hδab
    have hPO : ∀ s ∈ uIcc a b, γ s ∈ O σ := by
      intro s hs
      have : s ∈ V σ ∩ uIcc 0 t := ⟨(hPball hs).1, hP hs⟩
      rw [← hVeq] at this
      exact this.1
    have hlen : |b - a| ≤ ε σ := by
      have h1 := (hPball left_mem_uIcc).2
      have h2 := (hPball right_mem_uIcc).2
      rw [Metric.mem_ball, Real.dist_eq] at h1 h2
      have h1' := abs_lt.1 h1
      have h2' := abs_lt.1 h2
      exact abs_le.2 ⟨by linarith, by linarith⟩
    have hγaO : γ a ∈ O σ := hPO a left_mem_uIcc
    have key : γ b = α σ (γ a) (b - a) := by
      have hmem : ∀ τ ∈ uIcc 0 (b - a), γ (τ + a) ∈ O σ := by
        intro τ hτ
        apply hPO
        have : τ + a ∈ (fun x => x + a) '' uIcc 0 (b - a) := ⟨τ, hτ, rfl⟩
        rwa [image_add_const_uIcc, zero_add, sub_add_cancel] at this
      have := huniq σ (γ a) hγaO (b - a) hlen (fun τ => γ (τ + a)) (by simp)
        (gl_shift_to_zero (hγ.mono hP)) hmem (b - a) right_mem_uIcc
      simpa using this
    let Γ' : M → ℝ → M := fun y s => if s ∈ uIcc 0 a then Γ y s else α σ (Γ y a) (s - a)
    refine ⟨Γ', ?_, ?_⟩
    · filter_upwards [hE, hT ((hO σ).mem_nhds hγaO)] with y hy hyO
      obtain ⟨h0, hc, hi⟩ := hy
      have hyO' : Γ y a ∈ O σ := hyO
      obtain ⟨hα0, hαc, hαi⟩ := hα σ (Γ y a) hyO'
      have hseam : ∀ s ∈ uIcc a b, s ∈ uIcc 0 a → s = a := by
        intro s hs1 hs2
        rcases mem_uIcc.1 hs1 with ⟨_, _⟩ | ⟨_, _⟩ <;>
          rcases mem_uIcc.1 hs2 with ⟨_, _⟩ | ⟨_, _⟩ <;>
          rcases mem_uIcc.1 hab with ⟨_, _⟩ | ⟨_, _⟩ <;> linarith
      have hc1 : IsMIntegralCurveOn (Γ' y) X (uIcc 0 a) :=
        gl_congr hc (fun s hs => by simp only [Γ', if_pos hs])
      have hc2 : IsMIntegralCurveOn (Γ' y) X (uIcc a b) := by
        refine gl_congr (gl_shift_to_piece hαc hlen) (fun s hs => ?_)
        by_cases hs0 : s ∈ uIcc 0 a
        · have hsa := hseam s hs hs0
          simp only [Γ', if_pos hs0]
          rw [hsa, sub_self, hα0]
        · simp only [Γ', if_neg hs0]
      refine ⟨by simp only [Γ', if_pos (left_mem_uIcc : (0:ℝ) ∈ uIcc 0 a), h0], ?_, ?_⟩
      · exact (gl_union hc1 hc2 isCompact_uIcc.isClosed isCompact_uIcc.isClosed).mono
          uIcc_subset_uIcc_union_uIcc
      · intro s hs
        by_cases hs0 : s ∈ uIcc 0 a
        · simp only [Γ', if_pos hs0]
          exact hi s hs0
        · simp only [Γ', if_neg hs0]
          have hs' : s ∈ uIcc a b := (uIcc_subset_uIcc_union_uIcc hs).resolve_left hs0
          exact hαi _ (abs_le.1 ((abs_sub_left_of_mem_uIcc hs').trans hlen))
    · have hcont' : ContinuousAt (fun y => α σ y (b - a)) (γ a) :=
        (hcont σ (b - a) (abs_le.1 hlen)).continuousAt ((hO σ).mem_nhds hγaO)
      have := hcont'.tendsto.comp hT
      rw [← key] at this
      refine this.congr fun y => ?_
      simp only [Function.comp_apply, Γ', if_neg hba]
  -- the subdivision
  obtain ⟨N, hN⟩ := exists_nat_gt (|t| / δ)
  have hNpos : (0:ℝ) < N := lt_of_le_of_lt (div_nonneg (abs_nonneg t) hδ.le) hN
  have hN0 : (N:ℝ) ≠ 0 := hNpos.ne'
  set h := t / N with hh_def
  have htN : (N:ℝ) * h = t := by
    rw [hh_def]
    field_simp
  have hhδ : |h| < δ := by
    rw [hh_def, abs_div, Nat.abs_cast, div_lt_iff₀ hNpos]
    rw [div_lt_iff₀ hδ] at hN
    linarith
  have hind : ∀ k : ℕ, k ≤ N → Q ((k:ℝ) * h) := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [Nat.cast_zero, zero_mul]
      exact hQ0
    | succ k ih =>
      intro hk
      have hk' : ((k:ℝ) + 1) ≤ N := by exact_mod_cast hk
      have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
      push_cast
      refine hstep _ _ ?_ ?_ ?_ (ih (by omega))
      · rw [mem_uIcc]
        rcases le_total 0 h with hh | hh
        · left
          constructor <;> nlinarith
        · right
          constructor <;> nlinarith
      · rw [mem_uIcc, ← htN]
        rcases le_total 0 h with hh | hh
        · left
          constructor <;> nlinarith
        · right
          constructor <;> nlinarith
      · rw [show ((k:ℝ) + 1) * h - k * h = h by ring]
        exact hhδ
  have hfin := hind N le_rfl
  rw [htN] at hfin
  obtain ⟨Γ, hE, -⟩ := hfin
  exact hE.mono fun y hy => ⟨Γ y, hy⟩
