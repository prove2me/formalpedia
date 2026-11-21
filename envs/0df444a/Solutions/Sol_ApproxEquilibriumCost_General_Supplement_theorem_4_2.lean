-- Prove2me | solution 1 for ApproxEquilibriumCost.General.Supplement.theorem_4_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T10:11:34.092075+00:00
-- url     : https://prove2.me/submissions/328a4412-3207-4422-a5b2-44b69bd9dbe5

import Mathlib
import Definitions.Def_ApproxEquilibriumCost_General_FlowCosts
import Definitions.Def_ApproxEquilibriumCost_General_PolynomialLatencies
import Definitions.Def_ApproxEquilibriumCost_General_Supplement_UpperParameters
import Theorems.Thm_ApproxEquilibriumCost_General_lemma_2_2
import Theorems.Thm_ApproxEquilibriumCost_General_Supplement_lemma_A_1

section
set_option autoImplicit false

namespace ApproxEquilibriumCost.Dev.T42

open ApproxEquilibriumCost.General ApproxEquilibriumCost.General.Supplement

lemma p_ineq (d : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    0 ≤ (d:ℝ) * u^(d+1) - ((d:ℝ)+1) * u^d + 1 := by
  induction d with
  | zero => simp
  | succ n ih =>
    have h1 : 0 ≤ (u - 1) * (u^(n+1) - 1) := by
      rcases le_total u 1 with h | h
      · have := pow_le_one₀ hu h (n := n+1)
        exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
      · have := one_le_pow₀ h (n := n+1)
        exact mul_nonneg (by linarith) (by linarith)
    have e : ((n+1:ℕ):ℝ) * u^(n+1+1) - (((n+1:ℕ):ℝ)+1) * u^(n+1) + 1
        = u * ((n:ℝ) * u^(n+1) - ((n:ℝ)+1) * u^n + 1) + (u-1)*(u^(n+1)-1) := by
      push_cast; ring
    rw [e]
    have := mul_nonneg hu ih
    linarith

lemma p2_ineq (d : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    0 ≤ u^(d+1) - ((d:ℝ)+1) * u + d := by
  have h := one_add_mul_le_pow (a := u - 1) (by linarith) (d+1)
  have e : 1 + (u - 1) = u := by ring
  rw [e] at h
  push_cast at h
  nlinarith

lemma endpoints (d : ℕ) (B K q : ℝ) (hq : 0 ≤ q) (h0 : 0 ≤ B*q + (-1) + K)
    (hd : 0 ≤ B*q^(d+1) - q^d + K) :
    ∀ i ≤ d, 0 ≤ B*q^(i+1) - q^i + K := by
  intro i hi
  have step : ∀ j : ℕ, B*q^(j+1+1) - q^(j+1) + K
      = (B*q^(j+1) - q^j + K) + q^j*((q-1)*(B*q-1)) := by intro j; ring
  rcases le_total 0 ((q-1)*(B*q-1)) with hs | hs
  · have : ∀ j : ℕ, 0 ≤ B*q^(j+1) - q^j + K := by
      intro j
      induction j with
      | zero => simp only [zero_add, pow_one, pow_zero]; linarith
      | succ j ih =>
        rw [step]
        have := mul_nonneg (pow_nonneg hq j) hs
        linarith
    exact this i
  · have : ∀ n : ℕ, ∀ i : ℕ, i + n = d → 0 ≤ B*q^(i+1) - q^i + K := by
      intro n
      induction n with
      | zero => intro i h; simp at h; subst h; exact hd
      | succ n ih =>
        intro i h
        have := ih (i+1) (by omega)
        rw [step] at this
        have h2 := mul_nonneg (pow_nonneg hq i) (neg_nonneg.2 hs)
        nlinarith
    exact this (d - i) i (by omega)

lemma feas_poly (d : ℕ) (A B s : ℝ) (hA : 0 ≤ A) (hAB : A ≤ B) (hs : 1 ≤ s)
    (hd : ∀ q, 0 ≤ q → 0 ≤ B*q^(d+1) - q^d - A*q + s) :
    ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → ∀ i ≤ d,
      0 ≤ B*y^(i+1) - x*y^i - A*y*x^i + s*x^(i+1) := by
  intro x y hx hy i hi
  rcases hx.eq_or_lt with h0 | hpos
  · subst h0
    cases i with
    | zero => simp; nlinarith
    | succ i =>
      simp
      have : 0 ≤ B := le_trans hA hAB
      positivity
  · obtain ⟨q, hq, rfl⟩ : ∃ q, 0 ≤ q ∧ y = q*x := ⟨y/x, by positivity, by field_simp⟩
    have h0 : 0 ≤ B*q + (-1) + (-A*q + s) := by nlinarith [mul_nonneg (sub_nonneg.2 hAB) hq]
    have hd' : 0 ≤ B*q^(d+1) - q^d + (-A*q + s) := by linarith [hd q hq]
    have := endpoints d B (-A*q + s) q hq h0 hd' i hi
    have e : B*(q*x)^(i+1) - x*(q*x)^i - A*(q*x)*x^i + s*x^(i+1)
        = x^(i+1) * (B*q^(i+1) - q^i + (-A*q + s)) := by ring
    rw [e]
    exact mul_nonneg (pow_nonneg hx _) this

lemma scaled_ineq (d : ℕ) (κ q : ℝ) (hκ : 0 < κ) (hq : 0 ≤ q) :
    0 ≤ ((d:ℝ)/(((d:ℝ)+1)*κ)) * q^(d+1) - q^d - 0*q + κ^d/((d:ℝ)+1) := by
  obtain ⟨u, hu, rfl⟩ : ∃ u, 0 ≤ u ∧ q = κ*u := ⟨q/κ, by positivity, by field_simp⟩
  have := p_ineq d u hu
  have e : ((d:ℝ)/(((d:ℝ)+1)*κ)) * (κ*u)^(d+1) - (κ*u)^d - 0*(κ*u) + κ^d/((d:ℝ)+1)
      = κ^d/((d:ℝ)+1) * ((d:ℝ)*u^(d+1) - ((d:ℝ)+1)*u^d + 1) := by
    rw [mul_pow, mul_pow, pow_succ κ d]
    field_simp
    ring
  rw [e]
  exact mul_nonneg (by positivity) this

lemma reg1_ineq (d : ℕ) (hd : 1 ≤ d) (β a q : ℝ) (hβ : 0 < β) (ha : a = β^d) (hq : 0 ≤ q) :
    0 ≤ (((d:ℝ)-1)*a+1)/((d:ℝ)*β*a) * q^(d+1) - q^d - ((d:ℝ)+1-a)/((d:ℝ)*β) * q + 1 := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  obtain ⟨u, hu, rfl⟩ : ∃ u, 0 ≤ u ∧ q = β*u := ⟨q/β, by positivity, by field_simp⟩
  subst ha
  have h1 := p_ineq e u hu
  have h2 := p2_ineq (e+1) u hu
  have hpos : 0 < β^(e+1) := by positivity
  have ex : (((((e+1:ℕ):ℝ))-1)*β^(e+1)+1)/((((e+1:ℕ):ℝ))*β*β^(e+1)) * (β*u)^(e+1+1)
      - (β*u)^(e+1) - (((e+1:ℕ):ℝ)+1-β^(e+1))/(((e+1:ℕ):ℝ)*β) * (β*u) + 1
      = (β^(e+1) * u * ((e:ℝ) * u^(e+1) - ((e:ℝ)+1) * u^e + 1)
          + (u^(e+1+1) - (((e+1:ℕ):ℝ)+1) * u + ((e+1:ℕ):ℝ))) / ((e:ℝ)+1) := by
    rw [mul_pow, mul_pow]
    push_cast
    field_simp
    ring
  rw [ex]
  have : 0 ≤ β^(e+1) * u * ((e:ℝ) * u^(e+1) - ((e:ℝ)+1) * u^e + 1) :=
    mul_nonneg (mul_nonneg hpos.le hu) h1
  apply div_nonneg _ (by positivity)
  linarith

lemma lam_eq (d : ℕ) (x : ℝ) :
    lambda d x = x / (1 + x) * (1 - (1 + x) ^ (-(1 / (d : ℝ)))) := by
  unfold lambda
  rw [neg_div]
  rfl

lemma reg1_real (d : ℕ) (hd : 1 ≤ d) (α z : ℝ) (hα1 : 1 < α) (hαd : α ≤ d+1) :
    ∃ A B : ℝ, 0 ≤ A ∧ A ≤ B ∧ (∀ q, 0 ≤ q → 0 ≤ B*q^(d+1) - q^d - A*q + 1) ∧
      (α*(z - B) ≤ 1 - A → lambda d (α-1) ≤ 1 - z) := by
  have hdpos : (0:ℝ) < d := by exact_mod_cast hd
  have hα0 : 0 < α := by linarith
  set β : ℝ := α ^ ((d:ℝ)⁻¹) with hβdef
  have hβ : 0 < β := Real.rpow_pos_of_pos hα0 _
  have hβd : β ^ d = α := Real.rpow_inv_natCast_pow hα0.le (by omega)
  refine ⟨((d:ℝ)+1-α)/((d:ℝ)*β), (((d:ℝ)-1)*α+1)/((d:ℝ)*β*α), ?_, ?_, ?_, ?_⟩
  · apply div_nonneg (by linarith) (by positivity)
  · have e : (((d:ℝ)-1)*α+1)/((d:ℝ)*β*α) - ((d:ℝ)+1-α)/((d:ℝ)*β)
        = (α-1)^2/((d:ℝ)*β*α) := by field_simp; ring
    have : 0 ≤ (α-1)^2/((d:ℝ)*β*α) := by positivity
    linarith
  · intro q hq
    have := reg1_ineq d hd β α q hβ hβd.symm hq
    exact this
  · intro h
    have e1 : α * ((((d:ℝ)-1)*α+1)/((d:ℝ)*β*α)) - ((d:ℝ)+1-α)/((d:ℝ)*β) = (α-1)/β := by
      field_simp; ring
    have key : α*z ≤ 1 + (α-1)/β := by nlinarith
    have hl : lambda d (α-1) = (α-1)/α * (1 - β⁻¹) := by
      rw [lam_eq]
      have : 1 + (α - 1) = α := by ring
      rw [this, show -(1 / (d:ℝ)) = -((d:ℝ)⁻¹) by rw [one_div], Real.rpow_neg hα0.le]
    rw [hl]
    have e2 : (α-1)/α * (1 - β⁻¹) = 1 - (1 + (α-1)/β)/α := by field_simp; ring
    rw [e2]
    have : z ≤ (1 + (α-1)/β)/α := by rw [le_div_iff₀ hα0]; linarith
    linarith

lemma omega_spec (d : ℕ) (hd : 1 ≤ d) (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y < 1) :
    0 ≤ omega d y ∧ ∀ x, 0 ≤ x → lambda d x ≤ y → x ≤ omega d y := by
  obtain ⟨_, hmono, himg⟩ := lemma_A_1 d hd
  have hy : y ∈ (lambda d) '' Set.Ici 0 := by rw [himg]; exact ⟨hy0, hy1⟩
  obtain ⟨x0, hx0, hlx0⟩ := hy
  have hx0' : 0 ≤ x0 := hx0
  have hleast : IsLeast {x : ℝ | 0 ≤ x ∧ y ≤ lambda d x} x0 := by
    refine ⟨⟨hx0', hlx0.ge⟩, ?_⟩
    rintro x ⟨hx, hxy⟩
    by_contra hlt
    push Not at hlt
    have := hmono hx hx0 hlt
    linarith
  have hom : omega d y = x0 := by
    unfold omega
    rw [if_pos ⟨hd, hy0, hy1⟩]
    exact hleast.csInf_eq
  rw [hom]
  refine ⟨hx0', fun x hx hxy => ?_⟩
  exact (hmono.le_iff_le hx hx0).1 (by rw [hlx0]; exact hxy)

lemma load_nonneg {n k : ℕ} (G : Game n k) (f : Flow G) (hf : IsFeasible G f) (e : Fin n) :
    0 ≤ load G f e := by
  unfold load KellyStochasticNetworks.linkFlow
  apply Finset.sum_nonneg
  intro r _
  apply mul_nonneg
  · unfold incidence; split_ifs <;> norm_num
  · exact hf.1 r

lemma cross_ineq {n k : ℕ} (G : Game n k) (d : ℕ) (hpoly : HasPolynomialLatencies G d)
    (f f' : Flow G) (hf : IsFeasible G f) (hf' : IsFeasible G f') (A B s : ℝ)
    (hP : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → ∀ i ≤ d,
      0 ≤ B*y^(i+1) - x*y^i - A*y*x^i + s*x^(i+1)) :
    0 ≤ B * cost G f' - crossCost G f' f - A * crossCost G f f' + s * cost G f := by
  obtain ⟨a, ha0, hl⟩ := hpoly
  have e : B * cost G f' - crossCost G f' f - A * crossCost G f f' + s * cost G f
      = ∑ e, (B * (load G f' e * G.latency e (load G f' e))
          - load G f e * G.latency e (load G f' e)
          - A * (load G f' e * G.latency e (load G f e))
          + s * (load G f e * G.latency e (load G f e))) := by
    simp only [cost, crossCost, Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [e]
  apply Finset.sum_nonneg
  intro e _
  have hx := load_nonneg G f hf e
  have hy := load_nonneg G f' hf' e
  rw [hl e _ hx, hl e _ hy]
  have : ∀ x y : ℝ, B * (y * ∑ j : Fin (d+1), a e j * y ^ (j:ℕ))
      - x * ∑ j : Fin (d+1), a e j * y ^ (j:ℕ)
      - A * (y * ∑ j : Fin (d+1), a e j * x ^ (j:ℕ))
      + s * (x * ∑ j : Fin (d+1), a e j * x ^ (j:ℕ))
      = ∑ j : Fin (d+1), a e j * (B*y^((j:ℕ)+1) - x*y^(j:ℕ) - A*y*x^(j:ℕ) + s*x^((j:ℕ)+1)) := by
    intro x y
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [this]
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (ha0 e j) (hP _ _ hx hy j (Nat.lt_succ_iff.1 j.2))

lemma key {n k : ℕ} (G : Game n k) (d : ℕ) (hpoly : HasPolynomialLatencies G d)
    (f : Flow G) (hf : IsNash G f) (hcost : 0 < cost G f) (ε : ℝ) (hε : 0 ≤ ε)
    (f' : Flow G) (hf' : IsApproxNash G ε f') (A B s : ℝ) (hA : 0 ≤ A)
    (hP : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → ∀ i ≤ d,
      0 ≤ B*y^(i+1) - x*y^i - A*y*x^i + s*x^(i+1)) :
    (cost G f' / cost G f) * (1/(1+ε) - B) ≤ s - A := by
  have hfe : IsFeasible G f := hf.1
  have hfe' : IsFeasible G f' := hf'.1
  obtain ⟨h1, h2, _⟩ := lemma_2_2 G f f' hfe hfe' ε hε
  have hN := h1 hf
  have hAp := h2 hf'
  have hc := cross_ineq G d hpoly f f' hfe hfe' A B s hP
  have h1ε : 0 < 1 + ε := by linarith
  have hX : cost G f' / (1+ε) ≤ crossCost G f' f := by
    rw [div_le_iff₀ h1ε]; linarith
  have hA' := mul_nonneg hA hN
  have : cost G f' * (1/(1+ε) - B) ≤ (s - A) * cost G f := by
    have e : cost G f' * (1/(1+ε)) = cost G f' / (1+ε) := by ring
    nlinarith
  have e2 : (cost G f' / cost G f) * (1/(1+ε) - B) = cost G f' * (1/(1+ε) - B) / cost G f := by
    ring
  rw [e2, div_le_iff₀ hcost]
  exact this

lemma rpow_facts (d : ℕ) (hd : 1 ≤ d) :
    ∃ m : ℝ, 1 ≤ m ∧ m ^ d = (d:ℝ)+1 ∧ epsilon2 d = m - 1 ∧ c d = (d:ℝ)/(((d:ℝ)+1)*m) ∧
      lambda d (d:ℝ) = (d:ℝ)/((d:ℝ)+1) * (1 - m⁻¹) := by
  have hdpos : (0:ℝ) < d := by exact_mod_cast hd
  have hd1 : (0:ℝ) < (d:ℝ)+1 := by linarith
  refine ⟨Real.rpow ((d:ℝ)+1) ((1:ℝ)/(d:ℝ)), ?_, ?_, ?_, ?_, ?_⟩
  · show 1 ≤ ((d:ℝ)+1) ^ ((1:ℝ)/(d:ℝ))
    apply Real.one_le_rpow (by linarith) (by positivity)
  · show (((d:ℝ)+1) ^ ((1:ℝ)/(d:ℝ))) ^ d = (d:ℝ)+1
    rw [← Real.rpow_natCast, ← Real.rpow_mul hd1.le, one_div_mul_cancel hdpos.ne', Real.rpow_one]
  · rfl
  · unfold c
    have : ((d:ℝ)+1)/(d:ℝ) = 1 + (1:ℝ)/(d:ℝ) := by field_simp
    simp only [Real.rpow_eq_pow]
    rw [this, Real.rpow_add hd1, Real.rpow_one]
  · unfold lambda
    have : (1 + (d:ℝ)) = (d:ℝ)+1 := by ring
    simp only [Real.rpow_eq_pow]
    rw [this, show -(1:ℝ)/(d:ℝ) = -((1:ℝ)/(d:ℝ)) by ring, Real.rpow_neg hd1.le]

end ApproxEquilibriumCost.Dev.T42

namespace ApproxEquilibriumCost.General.Supplement

theorem chk_theorem_4_2 {n k : ℕ} (G : Game n k) (d : ℕ) (hd : 1 ≤ d)
    (hpoly : HasPolynomialLatencies G d) (f : Flow G) (hf : IsNash G f)
    (hcost : 0 < cost G f) (ε : ℝ) (hε : 0 ≤ ε)
    (f' : Flow G) (hf' : IsApproxNash G ε f') :
    (ε ≤ epsilon1 d → cost G f' / cost G f ≤ 1 + omega d (ε / (1 + ε))) ∧
    (epsilon1 d ≤ ε ∧ ε ≤ epsilon2 d →
      cost G f' / cost G f ≤ (1 / (1 + ε) - c d)⁻¹) ∧
    (epsilon2 d ≤ ε → cost G f' / cost G f ≤ (1 + ε) ^ (d + 1)) := by
  obtain ⟨m, hm1, hmd, he2, hc, hlam⟩ := ApproxEquilibriumCost.Dev.T42.rpow_facts d hd
  have hdpos : (0:ℝ) < d := by exact_mod_cast hd
  have hd1 : (0:ℝ) < (d:ℝ)+1 := by linarith
  have hm0 : 0 < m := by linarith
  have h1ε : 0 < 1 + ε := by linarith
  set α := cost G f' / cost G f with hα
  have hmain : ∀ A B s : ℝ, 0 ≤ A → A ≤ B → 1 ≤ s →
      (∀ q, 0 ≤ q → 0 ≤ B*q^(d+1) - q^d - A*q + s) → α * (1/(1+ε) - B) ≤ s - A := by
    intro A B s hA hAB hs hd'
    exact ApproxEquilibriumCost.Dev.T42.key G d hpoly f hf hcost ε hε f' hf' A B s hA
      (ApproxEquilibriumCost.Dev.T42.feas_poly d A B s hA hAB hs hd')
  have hgen : ∀ κ : ℝ, 0 < κ → 1 ≤ κ^d/((d:ℝ)+1) →
      α * (1/(1+ε) - (d:ℝ)/(((d:ℝ)+1)*κ)) ≤ κ^d/((d:ℝ)+1) := by
    intro κ hκ h1
    have := hmain 0 ((d:ℝ)/(((d:ℝ)+1)*κ)) (κ^d/((d:ℝ)+1)) le_rfl (by positivity) h1
      (fun q hq => ApproxEquilibriumCost.Dev.T42.scaled_ineq d κ q hκ hq)
    simpa using this
  have H2 : α * (1/(1+ε) - c d) ≤ 1 := by
    have h := hgen m hm0 (by rw [hmd, div_self hd1.ne'])
    rw [hmd, div_self hd1.ne'] at h
    rw [hc]; exact h
  refine ⟨?_, ?_, ?_⟩
  · intro hε1
    have hy0 : 0 ≤ ε / (1 + ε) := by positivity
    have hy1 : ε / (1 + ε) < 1 := by rw [div_lt_one h1ε]; linarith
    obtain ⟨hom0, homle⟩ := ApproxEquilibriumCost.Dev.T42.omega_spec d hd _ hy0 hy1
    rcases le_or_gt α 1 with hα1 | hα1
    · linarith
    · have hL : 1 - lambda d (d:ℝ) = 1/((d:ℝ)+1) + c d := by
        rw [hlam, hc]; field_simp; ring
      have hLpos : 0 < 1 - lambda d (d:ℝ) := by
        rw [hL, hc]; positivity
      have hε1' : 1/(1+epsilon1 d) = 1 - lambda d (d:ℝ) := by
        unfold epsilon1
        have : 1 + lambda d (d:ℝ) / (1 - lambda d (d:ℝ)) = 1/(1 - lambda d (d:ℝ)) := by
          field_simp; ring
        rw [this, one_div_one_div]
      have hz : 1 - lambda d (d:ℝ) ≤ 1/(1+ε) := by
        rw [← hε1']
        exact one_div_le_one_div_of_le h1ε (by linarith)
      have hzc : 1/((d:ℝ)+1) ≤ 1/(1+ε) - c d := by linarith
      have h3 : α * (1/((d:ℝ)+1)) ≤ 1 :=
        le_trans (mul_le_mul_of_nonneg_left hzc (by linarith)) H2
      have hαd : α ≤ (d:ℝ)+1 := by
        rw [mul_one_div, div_le_iff₀ hd1] at h3
        linarith
      obtain ⟨A, B, hA, hAB, hfe, hlm⟩ :=
        ApproxEquilibriumCost.Dev.T42.reg1_real d hd α (1/(1+ε)) hα1 hαd
      have := hmain A B 1 hA hAB le_rfl hfe
      have h4 := hlm this
      have e : 1 - 1/(1+ε) = ε/(1+ε) := by field_simp; ring
      rw [e] at h4
      have := homle (α - 1) (by linarith) h4
      linarith
  · rintro ⟨_, hε2⟩
    rw [he2] at hε2
    have hε2' : 1 + ε ≤ m := by linarith
    have hz : 1/m ≤ 1/(1+ε) := one_div_le_one_div_of_le h1ε hε2'
    have hpos : 0 < 1/(1+ε) - c d := by
      have e : 1/m - (d:ℝ)/(((d:ℝ)+1)*m) = 1/(((d:ℝ)+1)*m) := by field_simp; ring
      have : 0 < 1/(((d:ℝ)+1)*m) := by positivity
      rw [hc]; linarith
    rw [← one_div, le_div_iff₀ hpos]
    exact H2
  · intro hε2
    rw [he2] at hε2
    have hε2' : m ≤ 1 + ε := by linarith
    have h1 : 1 ≤ (1+ε)^d/((d:ℝ)+1) := by
      rw [le_div_iff₀ hd1, one_mul, ← hmd]
      exact pow_le_pow_left₀ hm0.le hε2' d
    have h := hgen (1+ε) h1ε h1
    have e : 1/(1+ε) - (d:ℝ)/(((d:ℝ)+1)*(1+ε)) = 1/(((d:ℝ)+1)*(1+ε)) := by
      field_simp; ring
    rw [e, mul_one_div, div_le_iff₀ (by positivity)] at h
    calc α ≤ (1+ε)^d/((d:ℝ)+1) * (((d:ℝ)+1)*(1+ε)) := h
      _ = (1+ε)^(d+1) := by field_simp; ring

end ApproxEquilibriumCost.General.Supplement
end

theorem solution : type_of% @ApproxEquilibriumCost.General.Supplement.chk_theorem_4_2 := @ApproxEquilibriumCost.General.Supplement.chk_theorem_4_2
