-- Prove2me | solution 1 for AddictivePlatforms.Costly.proposition_5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T09:08:25.87156+00:00
-- url     : https://prove2.me/submissions/f80185ef-5445-4b57-8fe8-681d417722ef
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AddictivePlatforms_Costly_Model
import Theorems.Thm_AddictivePlatforms_Costly_lemma_D_1
import Theorems.Thm_AddictivePlatforms_Costly_lemma_D_2
import Theorems.Thm_AddictivePlatforms_Costly_lemma_D_3
import Theorems.Thm_AddictivePlatforms_Costly_lemma_D_4
import Theorems.Thm_AddictivePlatforms_Compete_proposition_2_step_1

open Set Filter Topology
open scoped ENNReal

namespace AddictivePlatforms.Costly

/-- `γ` is strictly increasing on `ℝ₊`: it is monotone and strictly convex. -/
theorem p5red_gamma_lt {γ : ℝ → ℝ} (hm : MonotoneOn γ (Ici 0)) (hc : StrictConvexOn ℝ (Ici 0) γ)
    {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) : γ x < γ y := by
  have hy : (0:ℝ) ≤ y := le_trans hx hxy.le
  have hmid := hc.2 (show x ∈ Ici (0:ℝ) from hx) (show y ∈ Ici (0:ℝ) from hy) hxy.ne
    (show (0:ℝ) < 1/2 by norm_num) (show (0:ℝ) < 1/2 by norm_num) (by norm_num)
  have hle : γ x ≤ γ ((1/2:ℝ) • x + (1/2:ℝ) • y) := by
    apply hm (show x ∈ Ici (0:ℝ) from hx)
    · show (0:ℝ) ≤ (1/2:ℝ) • x + (1/2:ℝ) • y
      simp only [smul_eq_mul]; linarith
    · simp only [smul_eq_mul]; linarith
  simp only [smul_eq_mul] at hmid hle
  linarith

/-- Payoff of joining all platforms is (weakly) decreasing in a common profile. -/
theorem p5red_payoff_anti {v C : ℝ → ℝ} {K : ℕ} (hK : 0 < K)
    (hA : ∀ a : ℝ, 0 ≤ a → StrictAntiOn (fun d => uOf v a d) (Ici 0))
    (d d' : Fin K → ℝ) (hd : ∀ k, 0 ≤ d k) (hdd : ∀ k, d k ≤ d' k) (a : Fin K → ℝ)
    (ha : ∀ k, 0 ≤ a k) :
    AddictivePlatforms.Compete.payoff (uOf v) C d' ((Finset.univ, a) : AddictivePlatforms.Compete.Choice K) ≤
      AddictivePlatforms.Compete.payoff (uOf v) C d ((Finset.univ, a) : AddictivePlatforms.Compete.Choice K) := by
  have hne : (Finset.univ : Finset (Fin K)) ≠ ∅ := by
    rw [← Finset.nonempty_iff_ne_empty]; exact ⟨⟨0, hK⟩, Finset.mem_univ _⟩
  simp only [AddictivePlatforms.Compete.payoff, hne, if_false]
  have : ∑ k, uOf v (a k) (d' k) ≤ ∑ k, uOf v (a k) (d k) := by
    apply Finset.sum_le_sum
    intro k _
    exact (hA (a k) (ha k)).antitoneOn (show d k ∈ Ici (0:ℝ) from hd k)
      (show d' k ∈ Ici (0:ℝ) from le_trans (hd k) (hdd k)) (hdd k)
  linarith

/-- Strict version for a common strictly higher profile. -/
theorem p5red_payoff_strict {v C : ℝ → ℝ} {K : ℕ} (hK : 0 < K)
    (hA : ∀ a : ℝ, 0 ≤ a → StrictAntiOn (fun d => uOf v a d) (Ici 0))
    (d d' : Fin K → ℝ) (hd : ∀ k, 0 ≤ d k) (hdd : ∀ k, d k < d' k) (a : Fin K → ℝ)
    (ha : ∀ k, 0 ≤ a k) :
    AddictivePlatforms.Compete.payoff (uOf v) C d' ((Finset.univ, a) : AddictivePlatforms.Compete.Choice K) <
      AddictivePlatforms.Compete.payoff (uOf v) C d ((Finset.univ, a) : AddictivePlatforms.Compete.Choice K) := by
  have hne : (Finset.univ : Finset (Fin K)) ≠ ∅ := by
    rw [← Finset.nonempty_iff_ne_empty]; exact ⟨⟨0, hK⟩, Finset.mem_univ _⟩
  simp only [AddictivePlatforms.Compete.payoff, hne, if_false]
  have : ∑ k, uOf v (a k) (d' k) < ∑ k, uOf v (a k) (d k) := by
    apply Finset.sum_lt_sum_of_nonempty ⟨⟨0, hK⟩, Finset.mem_univ _⟩
    intro k _
    exact (hA (a k) (ha k)) (show d k ∈ Ici (0:ℝ) from hd k)
      (show d' k ∈ Ici (0:ℝ) from le_trans (hd k) (hdd k).le) (hdd k)
  linarith

/-- In an equilibrium with a common positive addictiveness, the consumer joins every platform. -/
theorem p5red_spe_joins_all {v C γ : ℝ → ℝ} {K : ℕ} {κ : ℝ} {Abar : ℝ≥0∞} (hκ : 0 < κ)
    (hγ0 : ∀ x : ℝ, 0 < x → γ 0 < γ x) (dE : Fin K → ℝ)
    (σE : AddictivePlatforms.Compete.ConsumerStrategy K) (hE : IsSPE (uOf v) C γ κ Abar dE σE)
    (e : ℝ) (he : 0 < e) (hdE : ∀ k, dE k = e) : (σE dE).1 = Finset.univ := by
  by_contra hne
  obtain ⟨k, hk⟩ : ∃ k, k ∉ (σE dE).1 := by
    by_contra h
    push Not at h
    exact hne (Finset.eq_univ_iff_forall.2 h)
  have hdev := hE.2.2 k 0 le_rfl
  have hnn : ∀ j, 0 ≤ Function.update dE k 0 j := by
    intro j
    by_cases hj : j = k
    · subst hj; simp
    · rw [Function.update_of_ne hj]; exact (hE.1 j)
  have hopt := hE.2.1 _ hnn
  have hfeas := hopt.1.1
  have hL : -(κ * γ 0) ≤ platformPayoff γ κ (Function.update dE k 0) k (σE (Function.update dE k 0)) := by
    unfold platformPayoff
    rw [Function.update_self]
    split_ifs with h
    · linarith [hfeas k h]
    · linarith
  have hR : platformPayoff γ κ dE k (σE dE) = -(κ * γ e) := by
    unfold platformPayoff
    rw [if_neg hk, hdE k]; ring
  have := hγ0 e he
  have : κ * γ 0 < κ * γ e := mul_lt_mul_of_pos_left this hκ
  linarith

/-- Concavity of `min{·, Ā}` as used in (A.11). -/
theorem p5red_capMin_eq (Abar : ℝ≥0∞) (A : ℝ) (hA : 0 ≤ A) :
    capMin Abar A = if Abar = ⊤ then A else min A Abar.toReal := by
  unfold capMin
  split_ifs with h
  · subst h; simp [ENNReal.toReal_ofReal hA]
  · have : Abar = ENNReal.ofReal Abar.toReal := (ENNReal.ofReal_toReal h).symm
    conv_lhs => rw [this]
    rw [← ENNReal.ofReal_min, ENNReal.toReal_ofReal (le_min hA ENNReal.toReal_nonneg)]

theorem p5red_capMin_conc (Abar : ℝ≥0∞) (A A1 A2 θ : ℝ) (h1 : 0 ≤ A1) (h2 : 0 ≤ A2)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hA : θ * A1 + (1 - θ) * A2 ≤ A) :
    θ * capMin Abar A1 + (1 - θ) * capMin Abar A2 ≤ capMin Abar A := by
  have hA0 : 0 ≤ A := le_trans (by nlinarith) hA
  rw [p5red_capMin_eq Abar A hA0, p5red_capMin_eq Abar A1 h1, p5red_capMin_eq Abar A2 h2]
  split_ifs with h
  · exact hA
  · have hb := (ENNReal.toReal_nonneg : 0 ≤ Abar.toReal)
    have m1 := min_le_left A1 Abar.toReal
    have m2 := min_le_left A2 Abar.toReal
    have m1' := min_le_right A1 Abar.toReal
    have m2' := min_le_right A2 Abar.toReal
    apply le_min
    · nlinarith
    · nlinarith

/-- Right-closedness of `{κ : d¹_J(κ) ≤ c}`. -/
theorem p5red_closed {γ : ℝ → ℝ} {Abar : ℝ≥0∞} {K : ℕ} (hK : 0 < K) {AD : ℝ → ℝ}
    (hADc : ConcaveOn ℝ (Ici 0) AD) (hADnn : ∀ D, 0 ≤ D → 0 ≤ AD D)
    (hγc : ConvexOn ℝ (Ici 0) γ) (hγnn : ∀ d, 0 ≤ d → 0 ≤ γ d)
    (J1 : ℝ → ℝ) (hJ : ∀ κ, 0 < κ → IsD1J AD γ κ Abar K (J1 κ))
    (hJu : ∀ κ, 0 < κ → ∀ x, IsD1J AD γ κ Abar K x → x = J1 κ)
    (κ0 : ℝ) (hκ0 : 0 < κ0) (c : ℝ) (hc : ∀ κ, κ0 < κ → J1 κ ≤ c) : J1 κ0 ≤ c := by
  by_contra hlt
  push Not at hlt
  set x0 := J1 κ0 with hx0
  have hc0 : 0 ≤ c := le_trans (hJ (κ0 + 1) (by linarith)).1 (hc (κ0 + 1) (by linarith))
  set F : ℝ → ℝ → ℝ := fun κ y => capMin Abar (AD ((K : ℝ) * y)) - (K : ℝ) * κ * γ y with hF
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  -- F κ0 c < F κ0 x0 by uniqueness
  have hopt0 := (hJ κ0 hκ0).2
  have hlt0 : F κ0 c < F κ0 x0 := by
    by_contra hge
    push Not at hge
    have : IsD1J AD γ κ0 Abar K c := ⟨hc0, fun d hd => le_trans (hopt0 d hd) hge⟩
    have := hJu κ0 hκ0 c this
    linarith
  set δ := F κ0 x0 - F κ0 c with hδ
  have hδpos : 0 < δ := by linarith
  have hγx0 : 0 ≤ γ x0 := hγnn x0 (by linarith)
  set κ := κ0 + δ / (2 * ((K : ℝ) * γ x0 + 1)) with hκ
  have hden : 0 < 2 * ((K : ℝ) * γ x0 + 1) := by positivity
  have hκgt : κ0 < κ := by
    have : 0 < δ / (2 * ((K : ℝ) * γ x0 + 1)) := div_pos hδpos hden
    linarith
  have hκpos : 0 < κ := by linarith
  set xk := J1 κ
  have hxk0 : 0 ≤ xk := (hJ κ hκpos).1
  have hxkc : xk ≤ c := hc κ hκgt
  -- concavity: F κ0 xk ≤ F κ0 c
  have hconc : F κ0 xk ≤ F κ0 c := by
    have hxlt : xk < x0 := lt_of_le_of_lt hxkc hlt
    set θ := (x0 - c) / (x0 - xk) with hθ
    have hpos : 0 < x0 - xk := by linarith
    have hθ0 : 0 ≤ θ := div_nonneg (by linarith) hpos.le
    have hθ1 : θ ≤ 1 := by rw [div_le_one hpos]; linarith
    have hcomb : θ * xk + (1 - θ) * x0 = c := by
      rw [hθ]; field_simp; ring
    -- AD concavity
    have hx0nn : (0:ℝ) ≤ x0 := by linarith
    have hm1 : (K : ℝ) * xk ∈ Ici (0:ℝ) := Set.mem_Ici.2 (by positivity)
    have hm2 : (K : ℝ) * x0 ∈ Ici (0:ℝ) := Set.mem_Ici.2 (by positivity)
    have hAD := hADc.2 hm1 hm2 hθ0 (show (0:ℝ) ≤ 1 - θ by linarith) (show θ + (1 - θ) = 1 by ring)
    simp only [smul_eq_mul] at hAD
    have hargeq : θ * ((K : ℝ) * xk) + (1 - θ) * ((K : ℝ) * x0) = (K : ℝ) * c := by
      rw [← hcomb]; ring
    rw [hargeq] at hAD
    have hcap := p5red_capMin_conc Abar (AD ((K : ℝ) * c)) (AD ((K : ℝ) * xk)) (AD ((K : ℝ) * x0)) θ
      (hADnn _ hm1) (hADnn _ hm2) hθ0 hθ1 hAD
    have hγ := hγc.2 (show xk ∈ Ici (0:ℝ) from hxk0) (show x0 ∈ Ici (0:ℝ) from hx0nn) hθ0 (show (0:ℝ) ≤ 1 - θ by linarith) (show θ + (1 - θ) = 1 by ring)
    simp only [smul_eq_mul] at hγ
    rw [hcomb] at hγ
    have hmax : F κ0 xk ≤ F κ0 x0 := hopt0 xk hxk0
    have hKκ : 0 ≤ (K : ℝ) * κ0 := by positivity
    simp only [hF] at hmax ⊢
    have h3 : (K : ℝ) * κ0 * γ c ≤ (K : ℝ) * κ0 * (θ * γ xk + (1 - θ) * γ x0) :=
      mul_le_mul_of_nonneg_left hγ hKκ
    nlinarith
  -- optimality of xk at κ is contradicted by x0
  have hoptk := (hJ κ hκpos).2 x0 (by linarith)
  have hFk : ∀ y, F κ y = F κ0 y - (K : ℝ) * (κ - κ0) * γ y := by
    intro y; simp only [hF]; ring
  have e1 : F κ xk ≤ F κ0 c := by
    rw [hFk]
    have : 0 ≤ (K : ℝ) * (κ - κ0) * γ xk := by
      have := hγnn xk hxk0
      have : 0 ≤ κ - κ0 := by linarith
      positivity
    linarith
  have e2 : F κ0 c < F κ x0 := by
    rw [hFk]
    have hkk : κ - κ0 = δ / (2 * ((K : ℝ) * γ x0 + 1)) := by rw [hκ]; ring
    have : (K : ℝ) * (κ - κ0) * γ x0 < δ := by
      rw [hkk]
      have : (K : ℝ) * (δ / (2 * ((K : ℝ) * γ x0 + 1))) * γ x0
          = δ * ((K : ℝ) * γ x0) / (2 * ((K : ℝ) * γ x0 + 1)) := by ring
      rw [this, div_lt_iff₀ hden]
      have : 0 ≤ (K : ℝ) * γ x0 := by positivity
      nlinarith
    linarith
  have : F κ x0 ≤ F κ xk := hoptk
  linarith

end AddictivePlatforms.Costly

open AddictivePlatforms.Costly

/-- Proposition 5, reduced to Lemmas D.1–D.4 and Proposition 2, Step 1. -/
theorem solution (v C γ g : ℝ → ℝ) (K : ℕ) (hK : 2 ≤ K) (hS : Standing v C γ g K) :
    (∀ κ : ℝ, 0 < κ → ∀ Abar : ℝ≥0∞, 0 < Abar →
      ∃ x : ℝ, 0 < x ∧
        (∃ σ : AddictivePlatforms.Compete.ConsumerStrategy K, IsSPE (uOf v) C γ κ Abar (fun _ : Fin K => x) σ) ∧
        ∀ (d : Fin K → ℝ) (σ : AddictivePlatforms.Compete.ConsumerStrategy K), IsSPE (uOf v) C γ κ Abar d σ →
          ∀ k, d k = x) ∧
    (∀ κ : ℝ, 0 < κ → ∀ Abar : ℝ≥0∞, 0 < Abar →
      ∃ (d : Fin K → ℝ) (σ : AddictivePlatforms.Compete.ConsumerStrategy K), IsJPM (uOf v) C γ κ Abar d σ) ∧
    ∀ Abar : ℝ≥0∞, 0 < Abar → ∃ κstar : ℝ, 0 ≤ κstar ∧ ∀ κ : ℝ, 0 < κ →
      ((∀ (dJ : Fin K → ℝ) (σJ : AddictivePlatforms.Compete.ConsumerStrategy K), IsJPM (uOf v) C γ κ Abar dJ σJ →
          ∀ (dE : Fin K → ℝ) (σE : AddictivePlatforms.Compete.ConsumerStrategy K), IsSPE (uOf v) C γ κ Abar dE σE →
            (∀ k, dJ k ≤ dE k) ∧
              AddictivePlatforms.Compete.consumerSurplus (uOf v) C dE σE ≤ AddictivePlatforms.Compete.consumerSurplus (uOf v) C dJ σJ) ↔
        κstar ≤ κ) := by
  have hK0 : 0 < K := by omega
  have hSC : AddictivePlatforms.Compete.Standing (uOf v) C :=
    ⟨hS.assumption1, hS.assumption2, hS.strictConcaveOn_a, hS.C_zero⟩
  have hγ0 : ∀ x : ℝ, 0 < x → γ 0 < γ x := fun x hx =>
    p5red_gamma_lt hS.assumption3.γ_monotoneOn hS.assumption3.γ_strictConvexOn le_rfl hx
  have hAnti := hS.assumption1.strictAntiOn_d
  -- common data for a cap `Abar`
  have setup : ∀ Abar : ℝ≥0∞, 0 < Abar → ∃ AD : ℝ → ℝ, IsAD C g K AD ∧ ConcaveOn ℝ (Ici 0) AD ∧
      ∃ d2 : ℝ, 0 < d2 ∧ AddictivePlatforms.Compete.Eq3 (uOf v) C Abar K d2 := by
    intro Abar hAbar
    obtain ⟨AD, hAD, -, hconc, -⟩ := lemma_D_1 v C γ g K hK0 hS Abar
    obtain ⟨d2, hd2, -⟩ := AddictivePlatforms.Compete.proposition_2_step_1 (uOf v) C hSC K hK
      hS.uncOptExists Abar hAbar
    exact ⟨AD, hAD, hconc, d2, hd2⟩
  refine ⟨?_, ?_, ?_⟩
  · intro κ hκ Abar hAbar
    obtain ⟨AD, hAD, -, d2, hd2⟩ := setup Abar hAbar
    obtain ⟨d1, -, -, -, -, hEq, -⟩ := lemma_D_2 v C γ g K hK hS Abar hAbar AD hAD d2 hd2
    exact ⟨min (d1 κ) d2, (hEq κ hκ).1, (hEq κ hκ).2.1, (hEq κ hκ).2.2⟩
  · intro κ hκ Abar hAbar
    obtain ⟨AD, hAD, -, -⟩ := setup Abar hAbar
    obtain ⟨d1J, d2J, -, -, -, -, ⟨σ, hσ⟩, -⟩ := lemma_D_3 v C γ g K hK hS Abar hAbar κ hκ AD hAD
    exact ⟨_, σ, hσ⟩
  · intro Abar hAbar
    obtain ⟨AD, hAD, hADc, d2, hd2⟩ := setup Abar hAbar
    obtain ⟨d1, hd1, -, -, -, hEq, κE, hκE⟩ := lemma_D_2 v C γ g K hK hS Abar hAbar AD hAD d2 hd2
    have hD3 : ∀ κ : ℝ, ∃ p : ℝ × ℝ, 0 < κ →
        (IsD1J AD γ κ Abar K p.1 ∧ (∀ x : ℝ, IsD1J AD γ κ Abar K x → x = p.1) ∧
        IsD2J (uOf v) C Abar K p.2 ∧ (∀ x : ℝ, IsD2J (uOf v) C Abar K x → x = p.2) ∧
        (∃ σ : AddictivePlatforms.Compete.ConsumerStrategy K,
          IsJPM (uOf v) C γ κ Abar (fun _ : Fin K => min p.1 p.2) σ) ∧
        ∀ (d : Fin K → ℝ) (σ : AddictivePlatforms.Compete.ConsumerStrategy K),
          IsJPM (uOf v) C γ κ Abar d σ → ∀ k, d k = min p.1 p.2) := by
      intro κ
      by_cases hκ : 0 < κ
      · obtain ⟨a, b, h⟩ := lemma_D_3 v C γ g K hK hS Abar hAbar κ hκ AD hAD
        exact ⟨(a, b), fun _ => h⟩
      · exact ⟨(0, 0), fun h => absurd h hκ⟩
    choose P hP using hD3
    set J1 : ℝ → ℝ := fun κ => (P κ).1 with hJ1
    set J2 : ℝ → ℝ := fun κ => (P κ).2 with hJ2
    set e : ℝ → ℝ := fun κ => min (d1 κ) d2 with he
    set j : ℝ → ℝ := fun κ => min (J1 κ) (J2 κ) with hj
    have k0 : Fin K := ⟨0, hK0⟩
    -- J2 is constant
    have hJ2c : ∀ κ κ', 0 < κ → 0 < κ' → J2 κ = J2 κ' := by
      intro κ κ' hκ hκ'
      exact ((hP κ' hκ').2.2.2.1 (J2 κ) (hP κ hκ).2.2.1)
    -- J1 antitone
    have hJ1anti : ∀ κ1 κ2, 0 < κ1 → κ1 ≤ κ2 → J1 κ2 ≤ J1 κ1 := by
      intro κ1 κ2 h1 h12
      have h2 : 0 < κ2 := by linarith
      by_contra hlt
      push Not at hlt
      have hx1 := (hP κ1 h1).1
      have hx2 := (hP κ2 h2).1
      have a1 := hx1.2 (J1 κ2) hx2.1
      have a2 := hx2.2 (J1 κ1) hx1.1
      have hg := hγ0 -- not needed directly
      have hglt : γ (J1 κ1) < γ (J1 κ2) :=
        p5red_gamma_lt hS.assumption3.γ_monotoneOn hS.assumption3.γ_strictConvexOn hx1.1 hlt
      have hKpos : (0 : ℝ) < K := by exact_mod_cast hK0
      simp only [hJ1] at a1 a2 hglt
      have hk12 : κ1 < κ2 ∨ κ1 = κ2 := lt_or_eq_of_le h12
      rcases hk12 with hk | hk
      · nlinarith [mul_pos hKpos (sub_pos.2 hk), mul_pos (mul_pos hKpos (sub_pos.2 hk)) (sub_pos.2 hglt)]
      · subst hk; simp only [hJ1] at hlt; exact lt_irrefl _ hlt
    have hjanti : ∀ κ1 κ2, 0 < κ1 → κ1 ≤ κ2 → j κ2 ≤ j κ1 := by
      intro κ1 κ2 h1 h12
      simp only [hj]
      rw [hJ2c κ2 κ1 (by linarith) h1]
      exact min_le_min_right _ (hJ1anti κ1 κ2 h1 h12)
    -- existence of outcomes at each κ
    have hSPE : ∀ κ, 0 < κ → ∃ σ, IsSPE (uOf v) C γ κ Abar (fun _ : Fin K => e κ) σ :=
      fun κ hκ => (hEq κ hκ).2.1
    have hJPM : ∀ κ, 0 < κ → ∃ σ, IsJPM (uOf v) C γ κ Abar (fun _ : Fin K => j κ) σ :=
      fun κ hκ => (hP κ hκ).2.2.2.2.1
    have hepos : ∀ κ, 0 < κ → 0 < e κ := fun κ hκ => (hEq κ hκ).1
    -- characterization: the condition holds iff j ≤ e
    have hchar : ∀ κ, 0 < κ →
        ((∀ (dJ : Fin K → ℝ) (σJ : AddictivePlatforms.Compete.ConsumerStrategy K), IsJPM (uOf v) C γ κ Abar dJ σJ →
          ∀ (dE : Fin K → ℝ) (σE : AddictivePlatforms.Compete.ConsumerStrategy K), IsSPE (uOf v) C γ κ Abar dE σE →
            (∀ k, dJ k ≤ dE k) ∧
              AddictivePlatforms.Compete.consumerSurplus (uOf v) C dE σE ≤ AddictivePlatforms.Compete.consumerSurplus (uOf v) C dJ σJ) ↔
          j κ ≤ e κ) := by
      intro κ hκ
      constructor
      · intro H
        obtain ⟨σJ, hσJ⟩ := hJPM κ hκ
        obtain ⟨σE, hσE⟩ := hSPE κ hκ
        exact (H _ σJ hσJ _ σE hσE).1 k0
      · intro hje dJ σJ hJ dE σE hE
        have hdJ : ∀ k, dJ k = j κ := (hP κ hκ).2.2.2.2.2 dJ σJ hJ
        have hdE : ∀ k, dE k = e κ := (hEq κ hκ).2.2 dE σE hE
        refine ⟨fun k => by rw [hdJ k, hdE k]; exact hje, ?_⟩
        have hall := p5red_spe_joins_all hκ hγ0 dE σE hE (e κ) (hepos κ hκ) hdE
        have hoptE := hE.2.1 dE hE.1
        set aE := (σE dE).2
        have hσE : σE dE = ((Finset.univ, aE) : AddictivePlatforms.Compete.Choice K) := by
          rw [← hall]
        have hfeasE : AddictivePlatforms.Compete.Feasible Abar
            ((Finset.univ, aE) : AddictivePlatforms.Compete.Choice K) := by
          rw [← hσE]; exact hoptE.1
        have haE : ∀ k, 0 ≤ aE k := fun k => hfeasE.1 k (Finset.mem_univ k)
        unfold AddictivePlatforms.Compete.consumerSurplus
        rw [hσE]
        have hdJnn : ∀ k, 0 ≤ dJ k := hJ.1
        have h1 := p5red_payoff_anti (C := C) hK0 hAnti dJ dE hdJnn
          (fun k => by rw [hdJ k, hdE k]; exact hje) aE haE
        have h2 := (hJ.2.1 dJ hdJnn).2 _ ⟨hfeasE, Or.inr rfl⟩
        exact le_trans h1 h2
    -- above κE the condition holds (Lemma D.4)
    have hhigh : ∀ κ, 0 < κ → κE < κ → j κ ≤ e κ := by
      intro κ hκ hκE'
      have hne : min (d1 κ) d2 ≠ d2 := by
        intro h; exact absurd ((hκE κ hκ).1 h) (not_le.2 hκE')
      have hed1 : e κ = d1 κ := by
        simp only [he]
        rcases min_choice (d1 κ) d2 with h | h
        · exact h
        · exact absurd h hne
      obtain ⟨σJ, hσJ⟩ := hJPM κ hκ
      obtain ⟨σE, hσE⟩ := hSPE κ hκ
      have hCS := lemma_D_4 v C γ g K hK hS Abar hAbar κ hκ AD hAD (d1 κ) (hd1 κ hκ).1
        (fun _ => e κ) σE hσE (fun _ => hed1) (fun _ => j κ) σJ hσJ
      by_contra hlt
      push Not at hlt
      set dEp : Fin K → ℝ := fun _ => e κ
      set dJp : Fin K → ℝ := fun _ => j κ
      have hall := p5red_spe_joins_all hκ hγ0 dEp σE hσE (e κ) (hepos κ hκ) (fun _ => rfl)
      have hoptE := hσE.2.1 dEp hσE.1
      have hRJ := hσJ.2.1 dJp hσJ.1
      rcases hRJ.1.2 with h0 | huniv
      · -- the consumer joins none: joint profit is beaten by the zero profile
        have hjp : jointProfit γ κ dJp (σJ dJp) = ∑ _k : Fin K, (-(κ * γ (j κ))) := by
          unfold jointProfit platformPayoff
          apply Finset.sum_congr rfl
          intro k _
          rw [h0]; simp [dJp]
        have hz : ∀ k, (0 : ℝ) ≤ (fun _ : Fin K => (0:ℝ)) k := fun _ => le_rfl
        have hjp0 : ∑ _k : Fin K, (-(κ * γ 0)) ≤ jointProfit γ κ (fun _ => 0) (σJ (fun _ => 0)) := by
          unfold jointProfit
          apply Finset.sum_le_sum
          intro k _
          unfold platformPayoff
          have hf := (hσJ.2.1 _ hz).1.1.1
          split_ifs with hk
          · have := hf k hk; simp; linarith
          · simp
        have hmax := hσJ.2.2.1 _ hz
        have hjpos : 0 < j κ := lt_trans (hepos κ hκ) hlt
        have hg := hγ0 _ hjpos
        have : κ * γ 0 < κ * γ (j κ) := mul_lt_mul_of_pos_left hg hκ
        have hsum : ∑ _k : Fin K, (-(κ * γ (j κ))) < ∑ _k : Fin K, (-(κ * γ 0)) := by
          apply Finset.sum_lt_sum_of_nonempty ⟨k0, Finset.mem_univ _⟩
          intro k _; linarith
        linarith
      · -- the consumer joins all: strictly worse than in the equilibrium
        set aJ := (σJ dJp).2
        have hσJ' : σJ dJp = ((Finset.univ, aJ) : AddictivePlatforms.Compete.Choice K) := by
          rw [← huniv]
        have hfeasJ : AddictivePlatforms.Compete.Feasible Abar
            ((Finset.univ, aJ) : AddictivePlatforms.Compete.Choice K) := by
          rw [← hσJ']; exact hRJ.1.1
        have haJ : ∀ k, 0 ≤ aJ k := fun k => hfeasJ.1 k (Finset.mem_univ k)
        have hs := p5red_payoff_strict (C := C) hK0 hAnti dEp dJp (fun _ => (hepos κ hκ).le)
          (fun _ => hlt) aJ haJ
        have hb := hoptE.2 _ hfeasJ
        unfold AddictivePlatforms.Compete.consumerSurplus at hCS
        rw [hσJ'] at hCS
        linarith
    -- the set of κ where the comparison holds
    set S : Set ℝ := {κ | 0 < κ ∧ j κ ≤ e κ} with hSdef
    have hup : ∀ s ∈ S, ∀ κ, s ≤ κ → κ ∈ S := by
      rintro s ⟨hs, hjs⟩ κ hsκ
      have hκ : 0 < κ := by linarith
      refine ⟨hκ, ?_⟩
      by_cases hκE' : κE < κ
      · exact hhigh κ hκ hκE'
      · push Not at hκE'
        have h1 : e κ = d2 := (hκE κ hκ).2 hκE'
        have h2 : e s = d2 := (hκE s hs).2 (le_trans hsκ hκE')
        calc j κ ≤ j s := hjanti s κ hs hsκ
          _ ≤ e s := hjs
          _ = e κ := by rw [h1, h2]
    have hcl : ∀ κ0, 0 < κ0 → (∀ κ, κ0 < κ → κ ∈ S) → κ0 ∈ S := by
      intro κ0 hκ0 hall
      refine ⟨hκ0, ?_⟩
      by_cases hκE' : κE < κ0
      · exact hhigh κ0 hκ0 hκE'
      · push Not at hκE'
        have h1 : e κ0 = d2 := (hκE κ0 hκ0).2 hκE'
        rw [h1]
        have hjle : ∀ κ, κ0 < κ → j κ ≤ d2 := by
          intro κ hκ
          have := (hall κ hκ).2
          exact le_trans this (min_le_right _ _)
        by_cases h2 : J2 κ0 ≤ d2
        · exact le_trans (min_le_right _ _) h2
        · push Not at h2
          have hJ1le : ∀ κ, κ0 < κ → J1 κ ≤ d2 := by
            intro κ hκ
            have := hjle κ hκ
            simp only [hj] at this
            rw [hJ2c κ κ0 (by linarith) hκ0] at this
            rcases min_choice (J1 κ) (J2 κ0) with h | h
            · rw [h] at this; exact this
            · rw [h] at this; linarith
          have := p5red_closed hK0 hADc (fun D hD => (hAD D hD).1)
            hS.assumption3.γ_strictConvexOn.convexOn hS.assumption3.γ_nonneg J1
            (fun κ hκ => (hP κ hκ).1) (fun κ hκ => (hP κ hκ).2.1) κ0 hκ0 d2 hJ1le
          exact le_trans (min_le_left _ _) this
    have hSne : (max κE 0 + 1) ∈ S := by
      have hpos : 0 < max κE 0 + 1 := by have := le_max_right κE 0; linarith
      exact ⟨hpos, hhigh _ hpos (by have := le_max_left κE 0; linarith)⟩
    have hSbdd : BddBelow S := ⟨0, fun s hs => hs.1.le⟩
    refine ⟨sInf S, le_csInf ⟨_, hSne⟩ (fun s hs => hs.1.le), ?_⟩
    intro κ hκ
    rw [hchar κ hκ]
    constructor
    · intro hje
      exact csInf_le hSbdd ⟨hκ, hje⟩
    · intro hle
      have hmem : κ ∈ S := by
        rcases lt_or_eq_of_le hle with hlt | heq
        · obtain ⟨s, hs, hsκ⟩ := exists_lt_of_csInf_lt ⟨_, hSne⟩ hlt
          exact hup s hs κ hsκ.le
        · apply hcl κ hκ
          intro κ' hκ'
          rw [← heq] at hκ'
          obtain ⟨s, hs, hsκ⟩ := exists_lt_of_csInf_lt ⟨_, hSne⟩ hκ'
          exact hup s hs κ' hsκ.le
      exact hmem.2
