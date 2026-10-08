-- Prove2me | solution 1 for AnosovPlugs.flowMap_flowProperty_of_regularity
-- status  : ACCEPTED   (prove)
-- author  : @ebayuser
-- created : 2026-10-04T23:58:53.451693+00:00
-- url     : https://prove2.me/submissions/7769da40-945a-4d06-a4da-448b94b6fccd

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing

open scoped Manifold ContDiff Topology
open Set AnosovPlugs

section FpHelpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {v : (x : M) → TangentSpace I x}

/-- Change the point `p` in the derivative `smulRight (v p)` to an equal point `q`. -/
theorem fp_congr_val {f : ℝ → M} {S : Set ℝ} {s : ℝ} {p q : M}
    (h : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I f S s ((1 : ℝ →L[ℝ] ℝ).smulRight (v p)))
    (hp : p = q) :
    HasMFDerivWithinAt 𝓘(ℝ, ℝ) I f S s ((1 : ℝ →L[ℝ] ℝ).smulRight (v q)) := by
  subst hp
  exact h

/-- The same change of point for `HasMFDerivAt`. -/
theorem fp_congr_val_at {f : ℝ → M} {s : ℝ} {p q : M}
    (h : HasMFDerivAt 𝓘(ℝ, ℝ) I f s ((1 : ℝ →L[ℝ] ℝ).smulRight (v p)))
    (hp : p = q) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I f s ((1 : ℝ →L[ℝ] ℝ).smulRight (v q)) := by
  subst hp
  exact h

/-- Congruence: an integral curve on `A` stays an integral curve after a change off `A`. -/
theorem fp_congr {γ γ₁ : ℝ → M} {A : Set ℝ} (h : IsMIntegralCurveOn γ₁ v A)
    (heq : EqOn γ γ₁ A) : IsMIntegralCurveOn γ v A := by
  intro s hs
  exact fp_congr_val ((h s hs).congr_mono (fun x hx => heq hx) (heq hs) subset_rfl) (heq hs).symm

/-- Gluing of integral curves on two closed sets. -/
theorem fp_union {γ : ℝ → M} {A B : Set ℝ} (hA : IsMIntegralCurveOn γ v A)
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
theorem fp_shift_from_zero {η : ℝ → M} {a b : ℝ} (h : IsMIntegralCurveOn η v (uIcc 0 (b - a))) :
    IsMIntegralCurveOn (fun s => η (s - a)) v (uIcc a b) := by
  have h1 := (isMIntegralCurveOn_comp_sub (dt := a)).2 h
  have e : {s : ℝ | s - a ∈ uIcc 0 (b - a)} = uIcc a b := by
    rw [show {s : ℝ | s - a ∈ uIcc 0 (b - a)} = (fun x => x - a) ⁻¹' uIcc 0 (b - a) from rfl,
      preimage_sub_const_uIcc, zero_add, sub_add_cancel]
  rw [e] at h1
  exact h1

/-- A curve on `uIcc a b`, shifted back by `a`, is an integral curve on `uIcc 0 (b - a)`. -/
theorem fp_shift_to_zero {γ : ℝ → M} {a b : ℝ} (hγ : IsMIntegralCurveOn γ v (uIcc a b)) :
    IsMIntegralCurveOn (fun τ => γ (τ + a)) v (uIcc 0 (b - a)) := by
  have h1 := hγ.comp_add a
  have e : {τ : ℝ | τ + a ∈ uIcc a b} = uIcc 0 (b - a) := by
    rw [show {τ : ℝ | τ + a ∈ uIcc a b} = (fun x => x + a) ⁻¹' uIcc a b from rfl,
      preimage_add_const_uIcc, sub_self]
  rw [e] at h1
  exact h1

end FpHelpers

/-- `flowMap` is the value of any integral curve from the start point. -/
theorem fp_flowMap_eq
    {N : Type} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace 3) N] [IsManifold I3 ∞ N]
    (Z : (w : N) → TangentSpace I3 w)
    (huniq : ∀ (γ γ' : ℝ → N) (t : ℝ), IsMIntegralCurveOn γ Z (uIcc 0 t) →
      IsMIntegralCurveOn γ' Z (uIcc 0 t) → γ' 0 = γ 0 → ∀ s ∈ uIcc 0 t, γ' s = γ s)
    {η : ℝ → N} {y : N} {t : ℝ} (h0 : η 0 = y) (hη : IsMIntegralCurveOn η Z (uIcc 0 t)) :
    flowMap Z t y = η t := by
  have hd : FlowDefined Z y t := ⟨η, h0, hη⟩
  unfold flowMap
  rw [dif_pos hd]
  obtain ⟨h0', hc'⟩ := hd.choose_spec
  exact huniq η hd.choose t hη hc' (by rw [h0', h0]) t right_mem_uIcc

/-- The time-zero map is the identity. -/
theorem fp_flowMap_zero
    {N : Type} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace 3) N] [IsManifold I3 ∞ N]
    (Z : (w : N) → TangentSpace I3 w) (y : N) : flowMap Z 0 y = y := by
  unfold flowMap
  by_cases hd : FlowDefined Z y 0
  · rw [dif_pos hd]
    exact hd.choose_spec.1
  · rw [dif_neg hd]

/-- Two consecutive integral curves glue to one integral curve. -/
theorem fp_glue
    {N : Type} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace 3) N] [IsManifold I3 ∞ N]
    (Z : (w : N) → TangentSpace I3 w)
    (huniq : ∀ (γ γ' : ℝ → N) (t : ℝ), IsMIntegralCurveOn γ Z (uIcc 0 t) →
      IsMIntegralCurveOn γ' Z (uIcc 0 t) → γ' 0 = γ 0 → ∀ s ∈ uIcc 0 t, γ' s = γ s)
    {η₁ η₂ : ℝ → N} {s t : ℝ} (h1 : IsMIntegralCurveOn η₁ Z (uIcc 0 s))
    (h2 : IsMIntegralCurveOn η₂ Z (uIcc 0 t)) (h20 : η₂ 0 = η₁ s) :
    ∃ Γ : ℝ → N, Γ 0 = η₁ 0 ∧ IsMIntegralCurveOn Γ Z (uIcc 0 (s + t)) ∧ Γ (s + t) = η₂ t := by
  classical
  have hov : ∀ τ ∈ uIcc s (s + t), τ ∈ uIcc 0 s → η₂ (τ - s) = η₁ τ := by
    intro τ hτ1 hτ2
    have hA : τ - s ∈ uIcc 0 t := by
      rcases mem_uIcc.1 hτ1 with ⟨a, b⟩ | ⟨a, b⟩
      · exact mem_uIcc.2 (Or.inl ⟨by linarith, by linarith⟩)
      · exact mem_uIcc.2 (Or.inr ⟨by linarith, by linarith⟩)
    have hB : τ - s ∈ uIcc 0 (0 - s) := by
      rcases mem_uIcc.1 hτ2 with ⟨a, b⟩ | ⟨a, b⟩
      · exact mem_uIcc.2 (Or.inr ⟨by linarith, by linarith⟩)
      · exact mem_uIcc.2 (Or.inl ⟨by linarith, by linarith⟩)
    have h1' : IsMIntegralCurveOn η₁ Z (uIcc s 0) := by rw [uIcc_comm]; exact h1
    have hsh := (fp_shift_to_zero h1').mono (uIcc_subset_uIcc left_mem_uIcc hB)
    have h2' := h2.mono (uIcc_subset_uIcc left_mem_uIcc hA)
    have := huniq (fun r => η₁ (r + s)) η₂ (τ - s) hsh h2' (by simp [h20]) (τ - s) right_mem_uIcc
    rw [this]
    simp
  let Γ : ℝ → N := fun τ => if τ ∈ uIcc 0 s then η₁ τ else η₂ (τ - s)
  have hc1 : IsMIntegralCurveOn Γ Z (uIcc 0 s) :=
    fp_congr h1 (fun τ hτ => by simp only [Γ, if_pos hτ])
  have h2s : IsMIntegralCurveOn η₂ Z (uIcc 0 (s + t - s)) := by
    rw [add_sub_cancel_left]; exact h2
  have hc2 : IsMIntegralCurveOn Γ Z (uIcc s (s + t)) := by
    refine fp_congr (fp_shift_from_zero h2s) (fun τ hτ => ?_)
    by_cases hτ0 : τ ∈ uIcc 0 s
    · simp only [Γ, if_pos hτ0]
      exact (hov τ hτ hτ0).symm
    · simp only [Γ, if_neg hτ0]
  refine ⟨Γ, by simp only [Γ, if_pos (left_mem_uIcc : (0:ℝ) ∈ uIcc 0 s)], ?_, ?_⟩
  · exact (fp_union hc1 hc2 isCompact_uIcc.isClosed isCompact_uIcc.isClosed).mono uIcc_subset_uIcc_union_uIcc
  · by_cases hst : s + t ∈ uIcc 0 s
    · simp only [Γ, if_pos hst]
      rw [← hov (s + t) right_mem_uIcc hst, add_sub_cancel_left]
    · simp only [Γ, if_neg hst, add_sub_cancel_left]

theorem solution
    {N : Type} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace 3) N] [IsManifold I3 ∞ N]
    (Z : (w : N) → TangentSpace I3 w)
    (huniq : ∀ (γ γ' : ℝ → N) (t : ℝ), IsMIntegralCurveOn γ Z (uIcc 0 t) → IsMIntegralCurveOn γ' Z (uIcc 0 t) →
        γ' 0 = γ 0 → ∀ s ∈ uIcc 0 t, γ' s = γ s)
    (hreg : ∀ w ∈ maxInvSet Z, I3.IsInteriorPoint w ∧ ∀ t : ℝ, ∃ O : Set N, IsOpen O ∧ w ∈ O ∧
        (∀ y ∈ O, FlowDefined Z y t) ∧ ContMDiffOn I3 I3 1 (flowMap Z t) O) :
    ∀ w ∈ maxInvSet Z,
      (∀ t : ℝ, flowMap Z t w ∈ maxInvSet Z) ∧
      (∀ s t : ℝ, flowMap Z t (flowMap Z s w) = flowMap Z (s + t) w) ∧
      (∀ v : TangentSpace I3 w, mfderiv I3 I3 (flowMap Z 0) w v = v) ∧
      (∀ (s t : ℝ) (v : TangentSpace I3 w), mfderiv I3 I3 (flowMap Z (s + t)) w v =
        mfderiv I3 I3 (flowMap Z t) (flowMap Z s w) (mfderiv I3 I3 (flowMap Z s) w v)) ∧
      (∀ t : ℝ, mfderiv I3 I3 (flowMap Z t) w (Z w) = Z (flowMap Z t w)) := by
  intro w hw
  -- the flow along a complete integral curve
  have hcomp : ∀ γ : ℝ → N, IsMIntegralCurve γ Z → ∀ r t : ℝ, flowMap Z t (γ r) = γ (r + t) := by
    intro γ hγ r t
    have := fp_flowMap_eq Z huniq (η := γ ∘ (· + r)) (y := γ r) (t := t)
      (by simp) ((hγ.comp_add r).isMIntegralCurveOn _)
    rw [this, Function.comp_apply, add_comm]
  -- invariance of the maximal invariant set
  have hinv : ∀ x ∈ maxInvSet Z, ∀ t : ℝ, flowMap Z t x ∈ maxInvSet Z := by
    rintro x ⟨γ, rfl, hγ⟩ t
    exact ⟨γ ∘ (· + t), by rw [hcomp γ hγ 0 t]; simp, hγ.comp_add t⟩
  -- differentiability at points of the maximal invariant set
  have hdiff : ∀ x ∈ maxInvSet Z, ∀ t : ℝ, MDifferentiableAt I3 I3 (flowMap Z t) x := by
    intro x hx t
    obtain ⟨O, hO, hxO, -, hC⟩ := (hreg x hx).2 t
    exact (hC.contMDiffAt (hO.mem_nhds hxO)).mdifferentiableAt one_ne_zero
  -- the local group law
  have hloc : ∀ x ∈ maxInvSet Z, ∀ s t : ℝ,
      flowMap Z (s + t) =ᶠ[𝓝 x] flowMap Z t ∘ flowMap Z s := by
    intro x hx s t
    obtain ⟨O, hO, hxO, hfd, hC⟩ := (hreg x hx).2 s
    obtain ⟨O', hO', hxO', hfd', -⟩ := (hreg _ (hinv x hx s)).2 t
    have hopen := hC.continuousOn.isOpen_inter_preimage hO hO'
    filter_upwards [hopen.mem_nhds ⟨hxO, hxO'⟩] with y hy
    obtain ⟨η₁, h10, h1⟩ := hfd y hy.1
    have e1 : flowMap Z s y = η₁ s := fp_flowMap_eq Z huniq h10 h1
    obtain ⟨η₂, h20, h2⟩ := hfd' _ hy.2
    have e2 : flowMap Z t (flowMap Z s y) = η₂ t := fp_flowMap_eq Z huniq h20 h2
    obtain ⟨Γ, hΓ0, hΓ, hΓe⟩ := fp_glue Z huniq h1 h2 (h20.trans e1)
    rw [Function.comp_apply, e2, fp_flowMap_eq Z huniq (hΓ0.trans h10) hΓ, hΓe]
  refine ⟨hinv w hw, ?_, ?_, ?_, ?_⟩
  · intro s t
    obtain ⟨γ, rfl, hγ⟩ := hw
    simp only [hcomp γ hγ, zero_add]
  · intro v
    have h0 : flowMap Z 0 = (id : N → N) := funext (fp_flowMap_zero Z)
    rw [h0, mfderiv_id]
    rfl
  · intro s t v
    rw [(hloc w hw s t).mfderiv_eq, mfderiv_comp (x := w) (hdiff _ (hinv w hw s) t) (hdiff w hw s)]
    rfl
  · intro t
    obtain ⟨γ, rfl, hγ⟩ := id hw
    have hfun : flowMap Z t ∘ γ = γ ∘ (· + t) := funext fun r => hcomp γ hγ r t
    have hA : HasMFDerivAt 𝓘(ℝ, ℝ) I3 (flowMap Z t ∘ γ) 0
        ((mfderiv I3 I3 (flowMap Z t) (γ 0)).comp ((1 : ℝ →L[ℝ] ℝ).smulRight (Z (γ 0)))) :=
      HasMFDerivAt.comp 0 (hdiff _ hw t).hasMFDerivAt (hγ 0)
    have hB : HasMFDerivAt 𝓘(ℝ, ℝ) I3 (flowMap Z t ∘ γ) 0
        ((1 : ℝ →L[ℝ] ℝ).smulRight (Z (γ t))) := by
      rw [hfun]
      exact fp_congr_val_at (hγ.comp_add t 0) (by simp)
    have hAB : mfderiv I3 I3 (flowMap Z t) (γ 0) ((1:ℝ) • Z (γ 0)) = (1:ℝ) • Z (γ t) :=
      DFunLike.congr_fun (hasMFDerivAt_unique hA hB) 1
    rw [one_smul, one_smul] at hAB
    have e : flowMap Z t (γ 0) = γ t := by rw [hcomp γ hγ 0 t, zero_add]
    rw [hAB, e]
