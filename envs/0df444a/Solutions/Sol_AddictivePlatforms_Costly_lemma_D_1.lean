-- Prove2me | solution 1 for AddictivePlatforms.Costly.lemma_D_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T09:16:26.913194+00:00
-- url     : https://prove2.me/submissions/c4174b7e-1a0b-476d-a536-8318bbb9ed80

import Mathlib
import Definitions.Def_AddictivePlatforms_Costly_Model

open Set Filter Topology
open scoped ENNReal

namespace AddictivePlatforms.Costly

/-- `v` is differentiable everywhere. -/
theorem d1aux_v_diff {v C γ g : ℝ → ℝ} {K : ℕ} (hS : Standing v C γ g K) (x : ℝ) :
    DifferentiableAt ℝ v x := by
  set d : ℝ := |x| + 1
  have hd : 0 < d := by positivity
  have ha : 0 < x + d := by have := neg_abs_le x; simp only [d]; linarith
  have hq : AddictivePlatforms.Compete.quadrant ∈ 𝓝 ((x + d, d) : ℝ × ℝ) := by
    unfold AddictivePlatforms.Compete.quadrant
    exact prod_mem_nhds (Ici_mem_nhds ha) (Ici_mem_nhds hd)
  have hdiff : DifferentiableAt ℝ (Function.uncurry (uOf v)) ((x + d, d) : ℝ × ℝ) :=
    (hS.assumption1.differentiableOn _ (mem_of_mem_nhds hq)).differentiableAt hq
  have h1 : DifferentiableAt ℝ (fun s : ℝ => ((s + d, d) : ℝ × ℝ)) x := by fun_prop
  have hcomp : DifferentiableAt ℝ (Function.uncurry (uOf v) ∘ (fun s : ℝ => ((s + d, d) : ℝ × ℝ))) x :=
    DifferentiableAt.comp (g := Function.uncurry (uOf v)) x hdiff h1
  have heq : (Function.uncurry (uOf v) ∘ (fun s : ℝ => ((s + d, d) : ℝ × ℝ))) = v := by
    funext s; simp [uOf]
  rwa [heq] at hcomp

/-- `v′` is strictly decreasing on `ℝ`. -/
theorem d1aux_v_deriv_anti {v C γ g : ℝ → ℝ} {K : ℕ} (hS : Standing v C γ g K) :
    StrictAnti (deriv v) := by
  intro s t hst
  set d : ℝ := |s| + 1
  have hsd : 0 < s + d := by have := neg_abs_le s; simp only [d]; linarith
  have hd : 0 ≤ d := by positivity
  have hconc := hS.strictConcaveOn_a d hd
  have hdiff : ∀ x ∈ Ici (0:ℝ), DifferentiableAt ℝ (fun a => uOf v a d) x := by
    intro x _
    have := d1aux_v_diff hS (x - d)
    simp only [uOf]
    exact this.comp x (by fun_prop)
  have h := hconc.strictAntiOn_deriv hdiff (show s + d ∈ Ici (0:ℝ) from hsd.le)
    (show t + d ∈ Ici (0:ℝ) from by show (0:ℝ) ≤ t + d; linarith) (by linarith)
  have hder : ∀ y, deriv (fun a => uOf v a d) y = deriv v (y - d) := by
    intro y
    simp only [uOf]
    exact deriv_comp_sub_const (f := v) d y
  rw [hder, hder] at h
  simpa using h

/-- Tangent-line inequality for `v`: `v y ≤ v x + v′(x) (y − x)`. -/
theorem d1aux_v_tangent {v C γ g : ℝ → ℝ} {K : ℕ} (hS : Standing v C γ g K) (x y : ℝ) :
    v y ≤ v x + deriv v x * (y - x) := by
  set d : ℝ := |x| + |y| + 1
  have hxd : 0 ≤ x + d := by have := neg_abs_le x; have := abs_nonneg y; simp only [d]; linarith
  have hyd : 0 ≤ y + d := by have := neg_abs_le y; have := abs_nonneg x; simp only [d]; linarith
  have hd : 0 ≤ d := by positivity
  have hconc := (hS.strictConcaveOn_a d hd).concaveOn
  set f : ℝ → ℝ := fun a => uOf v a d with hf
  have hdf : DifferentiableAt ℝ f (x + d) := by
    have := d1aux_v_diff hS (x + d - d)
    simp only [hf, uOf]
    exact this.comp (x + d) (by fun_prop)
  have hder : deriv f (x + d) = deriv v x := by
    simp only [hf, uOf]
    rw [deriv_comp_sub_const (f := v) d (x + d)]; simp
  have fx : f (x + d) = v x := by simp [hf, uOf]
  have fy : f (y + d) = v y := by simp [hf, uOf]
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · have h := hconc.slope_le_deriv (show x + d ∈ Ici (0:ℝ) from hxd)
      (show y + d ∈ Ici (0:ℝ) from hyd) (by linarith) hdf
    rw [slope_def_field, hder, fx, fy] at h
    have hpos : 0 < y + d - (x + d) := by linarith
    rw [div_le_iff₀ hpos] at h
    nlinarith
  · subst hxy; simp
  · have h := hconc.deriv_le_slope (show y + d ∈ Ici (0:ℝ) from hyd)
      (show x + d ∈ Ici (0:ℝ) from hxd) (by linarith) hdf
    rw [slope_def_field, hder, fx, fy] at h
    have hpos : 0 < x + d - (y + d) := by linarith
    rw [le_div_iff₀ hpos] at h
    nlinarith

/-- Tangent-line inequality for the convex `C` on `ℝ₊`. -/
theorem d1aux_C_tangent {v C γ g : ℝ → ℝ} {K : ℕ} (hS : Standing v C γ g K) (x y : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    C x + AddictivePlatforms.Compete.Cderiv C x * (y - x) ≤ C y := by
  have hconv := hS.assumption2.convexOn
  have hdiff := hS.assumption2.differentiableOn
  unfold AddictivePlatforms.Compete.Cderiv
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · have h := hconv.derivWithin_le_slope (show x ∈ Ici (0:ℝ) from hx) (show y ∈ Ici (0:ℝ) from hy)
      hxy (hdiff x hx)
    rw [slope_def_field] at h
    have hpos : 0 < y - x := by linarith
    rw [le_div_iff₀ hpos] at h
    linarith
  · subst hxy; simp
  · have h := hconv.slope_le_derivWithin (show y ∈ Ici (0:ℝ) from hy) (show x ∈ Ici (0:ℝ) from hx)
      hxy (hdiff x hx)
    rw [slope_def_field] at h
    have hpos : 0 < x - y := by linarith
    rw [div_le_iff₀ hpos] at h
    nlinarith

/-- `C′` is monotone on `ℝ₊`. -/
theorem d1aux_Cd_mono {v C γ g : ℝ → ℝ} {K : ℕ} (hS : Standing v C γ g K) :
    MonotoneOn (AddictivePlatforms.Compete.Cderiv C) (Ici 0) :=
  hS.assumption2.convexOn.monotoneOn_derivWithin hS.assumption2.differentiableOn

/-- `g ∘ C′` is antitone on `ℝ₊`. -/
theorem d1aux_gC_anti {v C γ g : ℝ → ℝ} {K : ℕ} (hS : Standing v C γ g K) :
    AntitoneOn (fun x => g (AddictivePlatforms.Compete.Cderiv C x)) (Ici 0) := by
  intro x hx y hy hxy
  by_contra hlt
  push Not at hlt
  have h1 := d1aux_v_deriv_anti hS hlt
  rw [hS.assumption3.g_rightInv x hx, hS.assumption3.g_rightInv y hy] at h1
  have := d1aux_Cd_mono hS hx hy hxy
  linarith

/-- `g ∘ C′` is continuous on `ℝ₊`. -/
theorem d1aux_gC_cont {v C γ g : ℝ → ℝ} {K : ℕ} (hS : Standing v C γ g K) :
    ContinuousOn (fun x => g (AddictivePlatforms.Compete.Cderiv C x)) (Ici 0) := by
  intro x hx
  have hg := (hS.assumption3.g_differentiableAt x hx).continuousAt
  have hc := (hS.assumption2.differentiableOn_deriv x hx).continuousWithinAt
  exact hg.comp_continuousWithinAt hc

/-- `v′(0) > C′(0)`, hence `g(C′(0)) > 0`. -/
theorem d1aux_gC0_pos {v C γ g : ℝ → ℝ} {K : ℕ} (hS : Standing v C γ g K) :
    0 < g (AddictivePlatforms.Compete.Cderiv C 0) := by
  have hev : ∀ᶠ a in 𝓝[>] (0:ℝ),
      0 < AddictivePlatforms.Compete.u1 (uOf v) a 0 - AddictivePlatforms.Compete.Cderiv C a := by
    rcases hS.assumption2.limit_pos with ⟨L, hL, hT⟩ | hT
    · exact hT.eventually (lt_mem_nhds hL)
    · exact hT.eventually (eventually_gt_atTop 0)
  have hev2 : ∀ᶠ a in 𝓝[>] (0:ℝ), 0 < a := self_mem_nhdsWithin
  obtain ⟨a, ha, ha0⟩ := (hev.and hev2).exists
  have hu1 : AddictivePlatforms.Compete.u1 (uOf v) a 0 = deriv v a := by
    unfold AddictivePlatforms.Compete.u1
    have : (fun x => uOf v x 0) = v := by funext x; simp [uOf]
    rw [this]
    exact derivWithin_of_mem_nhds (Ici_mem_nhds ha0)
  rw [hu1] at ha
  have h1 := d1aux_v_deriv_anti hS ha0
  have h2 := d1aux_Cd_mono hS (Set.mem_Ici.2 (le_refl (0:ℝ)))
    (show a ∈ Ici (0:ℝ) from ha0.le) ha0.le
  have hlt : AddictivePlatforms.Compete.Cderiv C 0 < deriv v 0 := by linarith
  by_contra hle
  push Not at hle
  have h3 := (d1aux_v_deriv_anti hS).antitone hle
  rw [hS.assumption3.g_rightInv 0 (le_refl (0:ℝ))] at h3
  linarith

/-- The left side minus the right side of `A − D = K g(C′(A))` is strictly increasing in `A ≥ 0`. -/
theorem d1aux_phi_strict {v C γ g : ℝ → ℝ} {K : ℕ} (hS : Standing v C γ g K) (D A A' : ℝ)
    (hA : 0 ≤ A) (hAA : A < A') :
    A - D - (K : ℝ) * g (AddictivePlatforms.Compete.Cderiv C A) <
      A' - D - (K : ℝ) * g (AddictivePlatforms.Compete.Cderiv C A') := by
  have h := d1aux_gC_anti hS (show A ∈ Ici (0:ℝ) from hA)
    (show A' ∈ Ici (0:ℝ) from by show (0:ℝ) ≤ A'; linarith) hAA.le
  have hK : (0:ℝ) ≤ K := Nat.cast_nonneg K
  simp only at h
  nlinarith

/-- Existence of a nonnegative solution of `A − D = K g(C′(A))`. -/
theorem d1aux_exists {v C γ g : ℝ → ℝ} {K : ℕ} (hS : Standing v C γ g K) (D : ℝ) (hD : 0 ≤ D) :
    ∃ A : ℝ, 0 ≤ A ∧ A - D = (K : ℝ) * g (AddictivePlatforms.Compete.Cderiv C A) := by
  set G0 := g (AddictivePlatforms.Compete.Cderiv C 0)
  have hG0 : 0 < G0 := d1aux_gC0_pos hS
  have hK : (0:ℝ) ≤ K := Nat.cast_nonneg K
  set B := D + (K : ℝ) * G0
  have hB : 0 ≤ B := by positivity
  set f : ℝ → ℝ := fun A => A - D - (K : ℝ) * g (AddictivePlatforms.Compete.Cderiv C A) with hf
  have hcont : ContinuousOn f (Icc 0 B) := by
    have h1 := (d1aux_gC_cont hS).mono (Icc_subset_Ici_self : Icc (0:ℝ) B ⊆ Ici 0)
    have : ContinuousOn (fun A : ℝ => A - D) (Icc 0 B) := by fun_prop
    exact this.sub (h1.const_smul (K : ℝ) |>.congr (fun x _ => by simp [smul_eq_mul]))
  have hf0 : f 0 ≤ 0 := by simp only [hf]; nlinarith
  have hfB : 0 ≤ f B := by
    simp only [hf]
    have := d1aux_gC_anti hS (Set.mem_Ici.2 (le_refl (0:ℝ))) (show B ∈ Ici (0:ℝ) from hB) hB
    simp only at this
    have : (K : ℝ) * g (AddictivePlatforms.Compete.Cderiv C B) ≤ (K : ℝ) * G0 :=
      mul_le_mul_of_nonneg_left this hK
    simp only [B] at this ⊢
    linarith
  obtain ⟨A, hAmem, hfA⟩ := intermediate_value_Icc hB hcont ⟨hf0, hfB⟩
  refine ⟨A, hAmem.1, ?_⟩
  simp only [hf] at hfA
  linarith

/-- `g ∘ C′` is concave on `ℝ₊` (from the monotonicity of `g′(C′(x)) C″(x)`). -/
theorem d1aux_gC_concave {v C γ g : ℝ → ℝ} {K : ℕ} (hS : Standing v C γ g K) :
    ConcaveOn ℝ (Ici 0) (fun x => g (AddictivePlatforms.Compete.Cderiv C x)) := by
  have hderiv : ∀ x : ℝ, 0 < x → HasDerivAt (fun x => g (AddictivePlatforms.Compete.Cderiv C x))
      (deriv g (AddictivePlatforms.Compete.Cderiv C x) * Cderiv2 C x) x := by
    intro x hx
    have hCd : DifferentiableAt ℝ (AddictivePlatforms.Compete.Cderiv C) x :=
      (hS.assumption2.differentiableOn_deriv x (le_of_lt hx)).differentiableAt (Ici_mem_nhds hx)
    have h2 : Cderiv2 C x = deriv (AddictivePlatforms.Compete.Cderiv C) x := by
      unfold Cderiv2
      exact derivWithin_of_mem_nhds (Ici_mem_nhds hx)
    rw [h2]
    exact (hS.assumption3.g_differentiableAt x hx.le).hasDerivAt.comp x hCd.hasDerivAt
  apply AntitoneOn.concaveOn_of_deriv (convex_Ici 0) (d1aux_gC_cont hS)
  · rw [interior_Ici]
    intro x hx
    exact (hderiv x hx).differentiableAt.differentiableWithinAt
  · rw [interior_Ici]
    intro x hx y hy hxy
    rw [(hderiv x hx).deriv, (hderiv y hy).deriv]
    exact hS.assumption3.antitoneOn (Set.mem_Ici.2 (le_of_lt (Set.mem_Ioi.1 hx)))
      (Set.mem_Ici.2 (le_of_lt (Set.mem_Ioi.1 hy))) hxy

/-- Uniqueness of the nonnegative solution. -/
theorem d1aux_unique {v C γ g : ℝ → ℝ} {K : ℕ} (hS : Standing v C γ g K) (D A A' : ℝ)
    (hA : 0 ≤ A) (hA' : 0 ≤ A')
    (h : A - D = (K : ℝ) * g (AddictivePlatforms.Compete.Cderiv C A))
    (h' : A' - D = (K : ℝ) * g (AddictivePlatforms.Compete.Cderiv C A')) : A = A' := by
  rcases lt_trichotomy A A' with hlt | heq | hgt
  · have := d1aux_phi_strict hS D A A' hA hlt; linarith
  · exact heq
  · have := d1aux_phi_strict hS D A' A hA' hgt; linarith

theorem d1aux_capMin_nonneg (Abar : ℝ≥0∞) (A : ℝ) : 0 ≤ capMin Abar A := ENNReal.toReal_nonneg

theorem d1aux_ofReal_capMin (Abar : ℝ≥0∞) (A : ℝ) : ENNReal.ofReal (capMin Abar A) ≤ Abar := by
  unfold capMin
  rw [ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (min_le_left _ _))]
  exact min_le_right _ _

end AddictivePlatforms.Costly

open AddictivePlatforms.Costly in
theorem solution (v C γ g : ℝ → ℝ) (K : ℕ) (hK : 0 < K) (hS : Standing v C γ g K)
    (Abar : ℝ≥0∞) :
    ∃ AD : ℝ → ℝ, IsAD C g K AD ∧
      (∀ D : ℝ, 0 ≤ D → ∀ A : ℝ, 0 ≤ A → A - D = (K : ℝ) * g (AddictivePlatforms.Compete.Cderiv C A) → A = AD D) ∧
      ConcaveOn ℝ (Ici 0) AD ∧
      ∀ d : Fin K → ℝ, (∀ k, 0 ≤ d k) → (∀ k, 0 ≤ allocA6 AD Abar d k) →
        ∀ a : Fin K → ℝ, IsAllocOpt (uOf v) C Abar d a ↔ a = allocA6 AD Abar d := by
  have hex : ∀ D : ℝ, ∃ A : ℝ, 0 ≤ D →
      (0 ≤ A ∧ A - D = (K : ℝ) * g (AddictivePlatforms.Compete.Cderiv C A)) := by
    intro D
    by_cases hD : 0 ≤ D
    · obtain ⟨A, hA⟩ := d1aux_exists hS D hD
      exact ⟨A, fun _ => hA⟩
    · exact ⟨0, fun h => absurd h hD⟩
  choose AD hAD using hex
  have hKpos : (0:ℝ) < K := by exact_mod_cast hK
  have hKne : (K : ℝ) ≠ 0 := hKpos.ne'
  set ψ : ℝ → ℝ := fun x => g (AddictivePlatforms.Compete.Cderiv C x) with hψ
  have hIsAD : IsAD C g K AD := fun D hD => hAD D hD
  have huniq : ∀ D : ℝ, 0 ≤ D → ∀ A : ℝ, 0 ≤ A →
      A - D = (K : ℝ) * g (AddictivePlatforms.Compete.Cderiv C A) → A = AD D :=
    fun D hD A hA h => d1aux_unique hS D A (AD D) hA (hAD D hD).1 h (hAD D hD).2
  refine ⟨AD, hIsAD, huniq, ?_, ?_⟩
  · -- concavity of `A(·)`
    refine ⟨convex_Ici 0, ?_⟩
    intro x hx y hy a b ha hb hab
    simp only [smul_eq_mul]
    have hx' : (0:ℝ) ≤ x := hx
    have hy' : (0:ℝ) ≤ y := hy
    have hAx := hAD x hx'
    have hAy := hAD y hy'
    set Dm := a * x + b * y with hDm
    have hDm0 : 0 ≤ Dm := by positivity
    have hAm := hAD Dm hDm0
    set M := a * AD x + b * AD y with hM
    have hM0 : 0 ≤ M := by have := hAx.1; have := hAy.1; positivity
    have hconc := (d1aux_gC_concave hS).2 (show AD x ∈ Ici (0:ℝ) from hAx.1)
      (show AD y ∈ Ici (0:ℝ) from hAy.1) ha hb hab
    simp only [smul_eq_mul] at hconc
    -- `M − K ψ(M) ≤ Dm`
    have h1 : M - (K : ℝ) * g (AddictivePlatforms.Compete.Cderiv C M) ≤ Dm := by
      have e1 := hAx.2
      have e2 := hAy.2
      have : (K : ℝ) * (a * g (AddictivePlatforms.Compete.Cderiv C (AD x)) +
          b * g (AddictivePlatforms.Compete.Cderiv C (AD y))) ≤
          (K : ℝ) * g (AddictivePlatforms.Compete.Cderiv C M) :=
        mul_le_mul_of_nonneg_left hconc hKpos.le
      have hb' : b = 1 - a := by linarith
      subst hb'
      simp only [hM, hDm] at this ⊢
      nlinarith
    by_contra hlt
    push Not at hlt
    have := d1aux_phi_strict hS Dm (AD Dm) M hAm.1 hlt
    linarith [hAm.2]
  · -- the optimal allocation
    intro d hd halloc a
    set D := ∑ j, d j with hD
    have hD0 : 0 ≤ D := Finset.sum_nonneg (fun j _ => hd j)
    set m := capMin Abar (AD D) with hm
    have hm0 : 0 ≤ m := d1aux_capMin_nonneg _ _
    set t := (1 / (K : ℝ)) * (m - D) with ht
    have hstar : ∀ k, allocA6 AD Abar d k = t + d k := fun k => rfl
    have hsum : ∑ k, allocA6 AD Abar d k = m := by
      simp only [hstar, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, ← hD]
      rw [ht]; field_simp; ring
    have hne : (Finset.univ : Finset (Fin K)) ≠ ∅ := by
      rw [← Finset.nonempty_iff_ne_empty]; exact ⟨⟨0, hK⟩, Finset.mem_univ _⟩
    have hpay : ∀ a' : Fin K → ℝ, AddictivePlatforms.Compete.payoff (uOf v) C d
        ((Finset.univ, a') : AddictivePlatforms.Compete.Choice K) =
        ∑ k, v (a' k - d k) - C (∑ k, a' k) := by
      intro a'
      simp [AddictivePlatforms.Compete.payoff, hne, uOf]
    have hfeas_star : AddictivePlatforms.Compete.Feasible Abar
        ((Finset.univ, allocA6 AD Abar d) : AddictivePlatforms.Compete.Choice K) := by
      refine ⟨fun k _ => halloc k, ?_⟩
      show ENNReal.ofReal (∑ k ∈ Finset.univ, allocA6 AD Abar d k) ≤ Abar
      rw [hsum]; exact d1aux_ofReal_capMin _ _
    -- the key sign condition
    have hkey : ∀ S' : ℝ, 0 ≤ S' → ENNReal.ofReal S' ≤ Abar →
        (deriv v t - AddictivePlatforms.Compete.Cderiv C m) * (S' - m) ≤ 0 := by
      intro S' hS'0 hS'
      have hAD0 := hAD D hD0
      by_cases hcap : ENNReal.ofReal (AD D) ≤ Abar
      · have hmeq : m = AD D := by
          rw [hm]; unfold capMin; rw [min_eq_left hcap, ENNReal.toReal_ofReal hAD0.1]
        have htg : t = g (AddictivePlatforms.Compete.Cderiv C m) := by
          rw [ht, hmeq, hAD0.2]; field_simp
        have : deriv v t = AddictivePlatforms.Compete.Cderiv C m := by
          rw [htg]; exact hS.assumption3.g_rightInv m hm0
        rw [this]; simp
      · push Not at hcap
        have hntop : Abar ≠ ⊤ := ne_top_of_lt hcap
        have hmeq : m = Abar.toReal := by
          rw [hm]; unfold capMin; rw [min_eq_right hcap.le]
        have hmlt : m < AD D := by
          rw [hmeq]; exact (ENNReal.lt_ofReal_iff_toReal_lt hntop).1 hcap
        have hS'm : S' ≤ m := by
          rw [hmeq]; exact (ENNReal.ofReal_le_iff_le_toReal hntop).1 hS'
        have hphi := d1aux_phi_strict hS D m (AD D) hm0 hmlt
        have htlt : t < g (AddictivePlatforms.Compete.Cderiv C m) := by
          rw [ht]
          have : m - D < (K : ℝ) * g (AddictivePlatforms.Compete.Cderiv C m) := by
            linarith [hAD0.2]
          rw [one_div, inv_mul_lt_iff₀ hKpos]; exact this
        have hv := d1aux_v_deriv_anti hS htlt
        rw [hS.assumption3.g_rightInv m hm0] at hv
        nlinarith
    -- optimality of (A.6)
    have hopt : ∀ a' : Fin K → ℝ, AddictivePlatforms.Compete.Feasible Abar
        ((Finset.univ, a') : AddictivePlatforms.Compete.Choice K) →
        AddictivePlatforms.Compete.payoff (uOf v) C d ((Finset.univ, a') : AddictivePlatforms.Compete.Choice K) ≤
          AddictivePlatforms.Compete.payoff (uOf v) C d
            ((Finset.univ, allocA6 AD Abar d) : AddictivePlatforms.Compete.Choice K) := by
      intro a' ha'
      rw [hpay, hpay, hsum]
      set S' := ∑ k, a' k with hS'
      have hS'0 : 0 ≤ S' := Finset.sum_nonneg (fun k _ => ha'.1 k (Finset.mem_univ k))
      have hS'cap : ENNReal.ofReal S' ≤ Abar := ha'.2
      have h1 : ∑ k, v (a' k - d k) ≤ ∑ k, (v t + deriv v t * (a' k - d k - t)) :=
        Finset.sum_le_sum (fun k _ => d1aux_v_tangent hS t (a' k - d k))
      have h1' : ∑ k, (v t + deriv v t * (a' k - d k - t)) =
          (K : ℝ) * v t + deriv v t * (S' - m) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Finset.sum_sub_distrib, ← hS', ← hD]
        rw [ht]; field_simp; ring
      have h2 : ∑ k, v (allocA6 AD Abar d k - d k) = (K : ℝ) * v t := by
        simp only [hstar, add_sub_cancel_right, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
      have h3 := d1aux_C_tangent hS m S' hm0 hS'0
      have h4 := hkey S' hS'0 hS'cap
      rw [h2]
      nlinarith
    constructor
    · intro ha
      by_contra hne'
      obtain ⟨k0, hk0⟩ : ∃ k, a k ≠ allocA6 AD Abar d k := by
        by_contra h; push Not at h; exact hne' (funext h)
      have hfa := ha.1
      have ha0 : ∀ k, 0 ≤ a k := fun k => hfa.1 k (Finset.mem_univ k)
      have hge := ha.2 _ hfeas_star
      set mid : Fin K → ℝ := fun k => (1/2 : ℝ) * a k + (1/2 : ℝ) * allocA6 AD Abar d k with hmid
      have hSa0 : 0 ≤ ∑ k, a k := Finset.sum_nonneg (fun k _ => ha0 k)
      have hsummid : ∑ k, mid k = (1/2 : ℝ) * ∑ k, a k + (1/2 : ℝ) * m := by
        simp only [hmid, Finset.sum_add_distrib, ← Finset.mul_sum, hsum]
      have hfeas_mid : AddictivePlatforms.Compete.Feasible Abar
          ((Finset.univ, mid) : AddictivePlatforms.Compete.Choice K) := by
        refine ⟨fun k _ => by have := ha0 k; have := halloc k; simp only [hmid]; positivity, ?_⟩
        show ENNReal.ofReal (∑ k ∈ Finset.univ, mid k) ≤ Abar
        rw [hsummid]
        have hcapa : ENNReal.ofReal (∑ k, a k) ≤ Abar := hfa.2
        have hcapm : ENNReal.ofReal m ≤ Abar := d1aux_ofReal_capMin _ _
        rcases le_total (∑ k, a k) m with hle | hle
        · exact le_trans (ENNReal.ofReal_le_ofReal (by linarith)) hcapm
        · exact le_trans (ENNReal.ofReal_le_ofReal (by linarith)) hcapa
      have hlt_mid := hopt mid hfeas_mid
      rw [hpay, hpay] at hlt_mid hge
      -- strict concavity of the sum
      have hvsum : ∑ k, ((1/2 : ℝ) * v (a k - d k) + (1/2 : ℝ) * v (allocA6 AD Abar d k - d k)) <
          ∑ k, v (mid k - d k) := by
        apply Finset.sum_lt_sum
        · intro k _
          have hc := (hS.strictConcaveOn_a (d k) (hd k)).concaveOn.2
            (show a k ∈ Ici (0:ℝ) from ha0 k) (show allocA6 AD Abar d k ∈ Ici (0:ℝ) from halloc k)
            (show (0:ℝ) ≤ 1/2 by norm_num) (show (0:ℝ) ≤ 1/2 by norm_num) (by norm_num)
          simpa [smul_eq_mul, uOf, hmid] using hc
        · refine ⟨k0, Finset.mem_univ _, ?_⟩
          have hc := (hS.strictConcaveOn_a (d k0) (hd k0)).2
            (show a k0 ∈ Ici (0:ℝ) from ha0 k0) (show allocA6 AD Abar d k0 ∈ Ici (0:ℝ) from halloc k0)
            hk0 (show (0:ℝ) < 1/2 by norm_num) (show (0:ℝ) < 1/2 by norm_num) (by norm_num)
          simpa [smul_eq_mul, uOf, hmid] using hc
      have hCc := hS.assumption2.convexOn.2 (show ∑ k, a k ∈ Ici (0:ℝ) from hSa0)
        (show m ∈ Ici (0:ℝ) from hm0) (show (0:ℝ) ≤ 1/2 by norm_num)
        (show (0:ℝ) ≤ 1/2 by norm_num) (by norm_num)
      simp only [smul_eq_mul] at hCc
      rw [hsum] at hlt_mid hge
      rw [hsummid] at hlt_mid
      have hsplit : ∑ k, ((1/2 : ℝ) * v (a k - d k) + (1/2 : ℝ) * v (allocA6 AD Abar d k - d k)) =
          (1/2 : ℝ) * ∑ k, v (a k - d k) + (1/2 : ℝ) * ∑ k, v (allocA6 AD Abar d k - d k) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      linarith
    · intro ha
      rw [ha]
      exact ⟨hfeas_star, hopt⟩
