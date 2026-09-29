-- Prove2me | solution 1 for AutomorphicForm.WindingDatum.exists_forall_coeff_eq_sum_tsum_ite_of_contDiff_of_periodic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/61fe16d8-336b-5292-927f-7989d51e2e62

import Mathlib
import Definitions.Def_AutomorphicForm_WindingDatum
import Theorems.Thm_MeasureTheory_exists_summable_forall_norm_setIntegral_mul_cexp_le_prod_of_contDiff_of_periodic
import Theorems.Thm_MeasureTheory_hasSum_fourierCoeff_pi_mul_cexp_of_continuous_of_periodic_of_summable
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_WindingDatum_exists_forall_coeff_eq_sum_tsum_ite_of_contDiff_of_periodic

set_option autoImplicit false

open MeasureTheory

noncomputable section

namespace ANR25

open AutomorphicForm

def E {c : ℕ} (m : Fin c → ℤ) (θ : Fin c → ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ))

def mode {r c : ℕ} (W : (Fin r → ℝ) × (Fin c → ℝ) → ℂ) (m : Fin c → ℤ) (x : Fin r → ℝ) : ℂ :=
  ∫ θ in Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1),
    W (x, θ) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ)))

theorem norm_E {c : ℕ} (m : Fin c → ℤ) (θ : Fin c → ℝ) : ‖E m θ‖ = 1 := by
  unfold E
  have h : (2 * (Real.pi : ℂ) * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ)) =
      ((2 * Real.pi * (∑ j, (m j : ℝ) * θ j) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

theorem prod_fourier_coe {c : ℕ} (m : Fin c → ℤ) (t : Fin c → ℝ) :
    ∏ j, fourier (m j) ((t j : ℝ) : AddCircle (1 : ℝ)) = E m t := by
  unfold E
  simp_rw [fourier_coe_apply]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem prod_inv_one_add_abs_sq_le_one {r : ℕ} (x : Fin r → ℝ) :
    ∏ k, (1 + |x k|)⁻¹ ^ 2 ≤ (1 : ℝ) :=
  Finset.prod_le_one (fun k _ => by positivity) fun k _ =>
    pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (by linarith [abs_nonneg (x k)]))

theorem summable_prod_fin {N : ℕ} {β α : Type*} [AddCommMonoid α] [TopologicalSpace α]
    [ContinuousAdd α] (f : Fin N × β → α) (h : ∀ i, Summable fun m => f (i, m)) : Summable f := by
  have hf : f = fun b => ∑ i : Fin N, if b.1 = i then f (i, b.2) else 0 := by
    funext b
    rw [Finset.sum_ite_eq]
    simp
  rw [hf]
  refine summable_sum fun i _ => ?_
  have hj : Function.Injective (fun m : β => ((i, m) : Fin N × β)) := fun m m' hmm => by
    simpa using hmm
  have h0 : ∀ b ∉ Set.range (fun m : β => ((i, m) : Fin N × β)),
      (fun b : Fin N × β => if b.1 = i then f (i, b.2) else 0) b = 0 := by
    intro b hb
    simp only
    split_ifs with hbi
    · exact absurd ⟨b.2, by ext <;> simp [hbi]⟩ hb
    · rfl
  refine (hj.summable_iff h0).mp ?_
  have hc : ((fun b : Fin N × β => if b.1 = i then f (i, b.2) else 0) ∘ fun m : β => ((i, m) : Fin N × β)) =
      fun m => f (i, m) := by
    funext m; simp
  rw [hc]
  exact h i

theorem finite_fibre {r d : ℕ} (Λ : AddSubgroup ((Fin r → ℝ) × (Fin d → ℤ))) (hΛ : DiscreteTopology Λ)
    (S : AddSubgroup ((Fin r → ℝ) × (Fin d → ℤ))) (hS : S ≤ Λ)
    (k₀ n : Fin d → ℤ) (x₀ : Fin r → ℝ) (R : ℝ) :
    Set.Finite {γ : S | (γ : (Fin r → ℝ) × (Fin d → ℤ)).2 + k₀ = n ∧
      ∀ j, |x₀ j + (γ : (Fin r → ℝ) × (Fin d → ℤ)).1 j| ≤ R} := by
  set B : Set ((Fin r → ℝ) × (Fin d → ℤ)) :=
    (Set.pi Set.univ fun j => Set.Icc (-R - x₀ j) (R - x₀ j)) ×ˢ {n - k₀} with hB
  have hBc : IsCompact B := (isCompact_univ_pi fun j => isCompact_Icc).prod isCompact_singleton
  haveI := hΛ
  have hΛc : IsClosed (Λ : Set ((Fin r → ℝ) × (Fin d → ℤ))) := AddSubgroup.isClosed_of_discrete
  have hK : IsCompact ((Λ : Set ((Fin r → ℝ) × (Fin d → ℤ))) ∩ B) := hBc.inter_left hΛc
  have hdisc : IsDiscrete ((Λ : Set ((Fin r → ℝ) × (Fin d → ℤ))) ∩ B) :=
    (SetLike.isDiscrete_iff_discreteTopology.mpr hΛ).mono Set.inter_subset_left
  have hfin : ((Λ : Set ((Fin r → ℝ) × (Fin d → ℤ))) ∩ B).Finite := hK.finite hdisc
  have hpre : (Subtype.val ⁻¹' ((Λ : Set ((Fin r → ℝ) × (Fin d → ℤ))) ∩ B) : Set S).Finite :=
    hfin.preimage Subtype.val_injective.injOn
  refine hpre.subset ?_
  intro γ hγ
  obtain ⟨hk, hx⟩ := hγ
  refine ⟨hS γ.2, ?_, ?_⟩
  · rw [Set.mem_univ_pi]
    intro j
    have h := (abs_le.mp (hx j))
    constructor <;> linarith [h.1, h.2]
  · rw [Set.mem_singleton_iff]
    exact eq_sub_of_add_eq hk

section Inner

variable {r d c : ℕ}

theorem inner
    (S : AddSubgroup ((Fin r → ℝ) × (Fin d → ℤ)))
    (W : (Fin r → ℝ) × (Fin c → ℝ) → ℂ) (hW : ContDiff ℝ (⊤ : ℕ∞) W)
    (R : ℝ) (hWsupp : ∀ p : (Fin r → ℝ) × (Fin c → ℝ), (∃ k, R < |p.1 k|) → W p = 0)
    (hWper : ∀ (p : (Fin r → ℝ) × (Fin c → ℝ)) (j : Fin c), W (p.1, p.2 + Pi.single j 1) = W p)
    (C : (Fin c → ℤ) → ℝ) (hC : Summable C) (hC0 : ∀ m, 0 ≤ C m)
    (hmode0 : ∀ (m : Fin c → ℤ) (x : Fin r → ℝ), (∃ k, R < |x k|) → mode W m x = 0)
    (hmoded : ∀ (m : Fin c → ℤ) (x : Fin r → ℝ), ‖mode W m x‖ ≤ C m * ∏ k, (1 + |x k|)⁻¹ ^ 2)
    (x₀ : Fin r → ℝ) (k₀ : Fin d → ℤ) (θf : (Fin r → ℝ) × (Fin d → ℤ) → (Fin c → ℝ))
    (n : Fin d → ℤ)
    (hfin : Set.Finite {γ : S | (γ : (Fin r → ℝ) × (Fin d → ℤ)).2 + k₀ = n ∧
      ∀ j, |x₀ j + (γ : (Fin r → ℝ) × (Fin d → ℤ)).1 j| ≤ R}) :
    (Summable fun m : Fin c → ℤ => ∑' γ : S,
      (if (γ : (Fin r → ℝ) × (Fin d → ℤ)).2 + k₀ = n then
        mode W m (x₀ + (γ : (Fin r → ℝ) × (Fin d → ℤ)).1) * E m (θf γ) else 0)) ∧
    ∑' m : Fin c → ℤ, ∑' γ : S,
      (if (γ : (Fin r → ℝ) × (Fin d → ℤ)).2 + k₀ = n then
        mode W m (x₀ + (γ : (Fin r → ℝ) × (Fin d → ℤ)).1) * E m (θf γ) else 0) =
    ∑' γ : S, (if (γ : (Fin r → ℝ) × (Fin d → ℤ)).2 + k₀ = n then
        W (x₀ + (γ : (Fin r → ℝ) × (Fin d → ℤ)).1, θf γ) else 0) := by

  set F : Finset S := hfin.toFinset with hF
  have hmemF : ∀ γ : S, γ ∉ F → (γ : (Fin r → ℝ) × (Fin d → ℤ)).2 + k₀ = n →
      ∃ k, R < |(x₀ + (γ : (Fin r → ℝ) × (Fin d → ℤ)).1) k| := by
    intro γ hγ hk
    by_contra hne
    push Not at hne
    apply hγ
    rw [hF, Set.Finite.mem_toFinset]
    exact ⟨hk, fun j => by simpa using hne j⟩

  set T : (Fin c → ℤ) → S → ℂ := fun m γ =>
    if (γ : (Fin r → ℝ) × (Fin d → ℤ)).2 + k₀ = n then
      mode W m (x₀ + (γ : (Fin r → ℝ) × (Fin d → ℤ)).1) * E m (θf γ) else 0 with hT
  have hT0 : ∀ (m : Fin c → ℤ) (γ : S), γ ∉ F → T m γ = 0 := by
    intro m γ hγ
    simp only [hT]
    split_ifs with hk
    · rw [hmode0 m _ (hmemF γ hγ hk), zero_mul]
    · rfl

  have hTm : ∀ γ : S, Summable fun m => T m γ := by
    intro γ
    refine Summable.of_norm_bounded hC fun m => ?_
    simp only [hT]
    split_ifs with hk
    · rw [norm_mul, norm_E, mul_one]
      exact (hmoded m _).trans (mul_le_of_le_one_right (hC0 m) (prod_inv_one_add_abs_sq_le_one _))
    · rw [norm_zero]; exact hC0 m
  have h1 : ∀ m, ∑' γ : S, T m γ = ∑ γ ∈ F, T m γ := fun m => tsum_eq_sum (hT0 m)

  have hrec : ∀ γ : S, ∑' m, T m γ =
      (if (γ : (Fin r → ℝ) × (Fin d → ℤ)).2 + k₀ = n then
        W (x₀ + (γ : (Fin r → ℝ) × (Fin d → ℤ)).1, θf γ) else 0) := by
    intro γ
    simp only [hT]
    split_ifs with hk
    · have hcont : Continuous fun θ : Fin c → ℝ => W (x₀ + (γ : (Fin r → ℝ) × (Fin d → ℤ)).1, θ) :=
        hW.continuous.comp (continuous_const.prodMk continuous_id)
      have hper' : ∀ (θ : Fin c → ℝ) (j : Fin c),
          W (x₀ + (γ : (Fin r → ℝ) × (Fin d → ℤ)).1, θ + Pi.single j 1) =
            W (x₀ + (γ : (Fin r → ℝ) × (Fin d → ℤ)).1, θ) :=
        fun θ j => hWper (x₀ + (γ : (Fin r → ℝ) × (Fin d → ℤ)).1, θ) j
      have hsum' : Summable fun m : Fin c → ℤ =>
          ‖∫ θ in Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1),
              W (x₀ + (γ : (Fin r → ℝ) × (Fin d → ℤ)).1, θ) *
                Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ)))‖ :=
        Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
          (fun m => (hmoded m _).trans
            (mul_le_of_le_one_right (hC0 m) (prod_inv_one_add_abs_sq_le_one _))) hC
      exact (MeasureTheory.hasSum_fourierCoeff_pi_mul_cexp_of_continuous_of_periodic_of_summable
        _ hcont hper' hsum' (θf γ)).tsum_eq
    · exact tsum_zero
  refine ⟨?_, ?_⟩
  · have : (fun m : Fin c → ℤ => ∑' γ : S, T m γ) = fun m => ∑ γ ∈ F, T m γ := funext h1
    rw [this]
    exact summable_sum fun γ _ => hTm γ
  · calc ∑' m, ∑' γ : S, T m γ = ∑' m, ∑ γ ∈ F, T m γ := tsum_congr h1
      _ = ∑ γ ∈ F, ∑' m, T m γ := Summable.tsum_finsetSum fun γ _ => hTm γ
      _ = ∑ γ ∈ F, (if (γ : (Fin r → ℝ) × (Fin d → ℤ)).2 + k₀ = n then
            W (x₀ + (γ : (Fin r → ℝ) × (Fin d → ℤ)).1, θf γ) else 0) := Finset.sum_congr rfl fun γ _ => hrec γ
      _ = ∑' γ : S, (if (γ : (Fin r → ℝ) × (Fin d → ℤ)).2 + k₀ = n then
            W (x₀ + (γ : (Fin r → ℝ) × (Fin d → ℤ)).1, θf γ) else 0) := by
          refine (tsum_eq_sum fun γ hγ => ?_).symm
          split_ifs with hk
          · exact hWsupp _ (hmemF γ hγ hk)
          · rfl

end Inner

section Main

variable {r d c N : ℕ}

theorem main
    (Λ : AddSubgroup ((Fin r → ℝ) × (Fin d → ℤ))) (hΛ : DiscreteTopology Λ)
    (s : (Fin r → ℝ) →ₗ[ℝ] ℝ) (ω : Fin d → ℝ) (hω : ω ≠ 0)
    (hpf : ∀ γ ∈ Λ, s γ.1 = ∑ i, ω i * (γ.2 i : ℝ))
    (χ : Λ →+ (Fin c → AddCircle (1 : ℝ)))
    (lift : (Fin r → ℝ) × (Fin d → ℤ) → (Fin c → ℝ))
    (hlift : ∀ (γ : (Fin r → ℝ) × (Fin d → ℤ)) (hγ : γ ∈ Λ) (j : Fin c),
      ((lift γ j : ℝ) : AddCircle (1 : ℝ)) = χ ⟨γ, hγ⟩ j)
    (sub : Fin N → AddSubgroup ((Fin r → ℝ) × (Fin d → ℤ))) (hsub : ∀ i, sub i ≤ Λ)
    (G : Fin N → (Fin r → ℝ) × (Fin c → ℝ) → ℂ) (hG : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (G i))
    (R : ℝ) (hR : 0 ≤ R) (hGsupp : ∀ i (p : (Fin r → ℝ) × (Fin c → ℝ)), (∃ k, R < |p.1 k|) → G i p = 0)
    (hGper : ∀ i (p : (Fin r → ℝ) × (Fin c → ℝ)) (j : Fin c), G i (p.1, p.2 + Pi.single j 1) = G i p)
    (x₀ : Fin N → Fin r → ℝ) (n₀ : Fin N → Fin d → ℤ) (θ₀ : Fin N → Fin c → ℝ) (hN : 0 < N) :
    ∃ 𝒜 : AutomorphicForm.WindingDatum r d c, ∀ n : Fin d → ℤ,
      𝒜.coeff n = ∑ i : Fin N, ∑' γ : sub i,
        if (γ : (Fin r → ℝ) × (Fin d → ℤ)).2 + n₀ i = n then
          G i (x₀ i + (γ : (Fin r → ℝ) × (Fin d → ℤ)).1, θ₀ i + lift (γ : (Fin r → ℝ) × (Fin d → ℤ)))
        else 0 := by

  have hW2 := fun i => MeasureTheory.exists_summable_forall_norm_setIntegral_mul_cexp_le_prod_of_contDiff_of_periodic
    (G i) (hG i) R hR (hGsupp i) (hGper i)
  choose Cf hCs hC0 hCd hChat using fun i => (hW2 i).2
  have hsm : ∀ i (m : Fin c → ℤ), ContDiff ℝ (⊤ : ℕ∞) (mode (G i) m) ∧
      ∀ x : Fin r → ℝ, (∃ k, R < |x k|) → mode (G i) m x = 0 := fun i m => (hW2 i).1 m
  have hCd' : ∀ i (m : Fin c → ℤ) (x : Fin r → ℝ), ‖mode (G i) m x‖ ≤ Cf i m * ∏ k, (1 + |x k|)⁻¹ ^ 2 :=
    fun i m x => hCd i m x

  haveI : Nonempty (Fin N × (Fin c → ℤ)) := ⟨(⟨0, hN⟩, 0)⟩
  obtain ⟨e, he⟩ := Countable.exists_injective_nat (Fin N × (Fin c → ℤ))
  set a : ℕ → Fin N × (Fin c → ℤ) := Function.invFun e with ha_def
  have ha : ∀ b, a (e b) = b := Function.leftInverse_invFun he
  set lam : ℕ → ℂ := (Set.range e).indicator fun _ => 1 with hlam
  have hlam1 : ∀ b, lam (e b) = 1 := fun b => by
    rw [hlam, Set.indicator_of_mem (Set.mem_range_self b)]
  have hlam0 : ∀ ι, ι ∉ Set.range e → lam ι = 0 := fun ι hι => by
    rw [hlam, Set.indicator_of_notMem hι]

  have hint : ∀ i (m : Fin c → ℤ), Integrable (mode (G i) m) := by
    intro i m
    refine (hsm i m).1.continuous.integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.of_support_subset_isCompact
      (isCompact_univ_pi fun _ : Fin r => isCompact_Icc (a := -R) (b := R)) ?_
    intro x hx
    rw [Set.mem_univ_pi]
    intro k
    by_contra hk
    apply hx
    apply (hsm i m).2 x
    refine ⟨k, ?_⟩
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hk
    rcases hk with hk | hk
    · rw [lt_abs]; right; linarith
    · rw [lt_abs]; left; exact hk

  have hsumC : Summable fun b : Fin N × (Fin c → ℤ) => Cf b.1 b.2 :=
    summable_prod_fin (fun b : Fin N × (Fin c → ℤ) => Cf b.1 b.2) fun i => hCs i
  have hsumw : Summable fun ι : ℕ => ‖lam ι‖ * Cf (a ι).1 (a ι).2 := by
    have h0 : ∀ ι ∉ Set.range e, (fun ι : ℕ => ‖lam ι‖ * Cf (a ι).1 (a ι).2) ι = 0 := by
      intro ι hι; simp only [hlam0 ι hι, norm_zero, zero_mul]
    refine (he.summable_iff h0).mp ?_
    have : ((fun ι : ℕ => ‖lam ι‖ * Cf (a ι).1 (a ι).2) ∘ e) = fun b => Cf b.1 b.2 := by
      funext b; simp only [Function.comp_apply, hlam1, ha, norm_one, one_mul]
    rw [this]
    exact hsumC

  refine ⟨
    { Λ := Λ, hΛ := hΛ, s := s, ω := ω, hω := hω, hpf := hpf, χ := χ
      sub := fun ι => sub (a ι).1
      hsub := fun ι => hsub (a ι).1
      Ψ := fun ι => mode (G (a ι).1) (a ι).2
      hΨc := fun ι => (hsm (a ι).1 (a ι).2).1.continuous
      hΨi := fun ι => hint (a ι).1 (a ι).2
      C := fun ι => Cf (a ι).1 (a ι).2
      hΨd := fun ι x => hCd (a ι).1 (a ι).2 x
      hΨhatd := fun ι ξ => hChat (a ι).1 (a ι).2 ξ
      m := fun ι => (a ι).2
      θ₀ := fun ι j => ((θ₀ (a ι).1 j : ℝ) : AddCircle (1 : ℝ))
      x₀ := fun ι => x₀ (a ι).1
      n₀ := fun ι => n₀ (a ι).1
      lam := lam
      hsum := hsumw }, fun n => ?_⟩

  set T : ∀ i : Fin N, (Fin c → ℤ) → sub i → ℂ := fun i m γ =>
    if (γ : (Fin r → ℝ) × (Fin d → ℤ)).2 + n₀ i = n then
      mode (G i) m (x₀ i + (γ : (Fin r → ℝ) × (Fin d → ℤ)).1) *
        E m (θ₀ i + lift (γ : (Fin r → ℝ) × (Fin d → ℤ))) else 0 with hT
  have hphase : ∀ (i : Fin N) (m : Fin c → ℤ) (γ : sub i),
      ∏ j, fourier (m j) (((θ₀ i j : ℝ) : AddCircle (1 : ℝ)) +
        χ ⟨(γ : (Fin r → ℝ) × (Fin d → ℤ)), hsub i γ.2⟩ j) =
      E m (θ₀ i + lift (γ : (Fin r → ℝ) × (Fin d → ℤ))) := by
    intro i m γ
    rw [← prod_fourier_coe]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← hlift _ (hsub i γ.2) j, Pi.add_apply, AddCircle.coe_add]
  have hstep0 : (WindingDatum.coeff ⟨Λ, hΛ, s, ω, hω, hpf, χ, fun ι => sub (a ι).1, fun ι => hsub (a ι).1,
        fun ι => mode (G (a ι).1) (a ι).2, fun ι => (hsm (a ι).1 (a ι).2).1.continuous,
        fun ι => hint (a ι).1 (a ι).2, fun ι => Cf (a ι).1 (a ι).2, fun ι x => hCd (a ι).1 (a ι).2 x,
        fun ι ξ => hChat (a ι).1 (a ι).2 ξ, fun ι => (a ι).2,
        fun ι j => ((θ₀ (a ι).1 j : ℝ) : AddCircle (1 : ℝ)), fun ι => x₀ (a ι).1, fun ι => n₀ (a ι).1,
        lam, hsumw⟩ n) = ∑' ι : ℕ, lam ι * ∑' γ : sub (a ι).1, T (a ι).1 (a ι).2 γ := by
    simp only [WindingDatum.coeff, WindingDatum.fibreCoeff, WindingDatum.fibreTerm, hT, hphase]
  rw [hstep0]

  set Φ : Fin N × (Fin c → ℤ) → ℂ := fun b => ∑' γ : sub b.1, T b.1 b.2 γ with hΦ
  have hsupp : Function.support (fun ι : ℕ => lam ι * Φ (a ι)) ⊆ Set.range e := by
    intro ι hι
    by_contra h
    exact hι (by simp only [hlam0 ι h, zero_mul])
  have hb : ∀ b : Fin N × (Fin c → ℤ), lam (e b) * Φ (a (e b)) = Φ b := fun b => by
    rw [hlam1, one_mul, ha]
  have hfin : ∀ (i : Fin N), Set.Finite {γ : sub i | (γ : (Fin r → ℝ) × (Fin d → ℤ)).2 + n₀ i = n ∧
      ∀ j, |x₀ i j + (γ : (Fin r → ℝ) × (Fin d → ℤ)).1 j| ≤ R} :=
    fun i => finite_fibre Λ hΛ (sub i) (hsub i) (n₀ i) n (x₀ i) R
  have hinner := fun i : Fin N => inner (sub i) (G i) (hG i) R (hGsupp i) (hGper i) (Cf i) (hCs i) (hC0 i)
    (fun m x hx => (hsm i m).2 x hx) (hCd' i) (x₀ i) (n₀ i)
    (fun γ => θ₀ i + lift γ) n (hfin i)
  have hS : Summable Φ := summable_prod_fin Φ fun i => (hinner i).1
  calc ∑' ι : ℕ, lam ι * Φ (a ι) = ∑' b : Fin N × (Fin c → ℤ), lam (e b) * Φ (a (e b)) :=
        (he.tsum_eq hsupp).symm
    _ = ∑' b : Fin N × (Fin c → ℤ), Φ b := tsum_congr hb
    _ = ∑ i : Fin N, ∑' m : Fin c → ℤ, Φ (i, m) := by
        rw [Summable.tsum_prod' hS fun i => (hinner i).1, tsum_fintype]
    _ = _ := Finset.sum_congr rfl fun i _ => (hinner i).2

end Main

theorem main_zero {r d c : ℕ}
    (Λ : AddSubgroup ((Fin r → ℝ) × (Fin d → ℤ))) (hΛ : DiscreteTopology Λ)
    (s : (Fin r → ℝ) →ₗ[ℝ] ℝ) (ω : Fin d → ℝ) (hω : ω ≠ 0)
    (hpf : ∀ γ ∈ Λ, s γ.1 = ∑ i, ω i * (γ.2 i : ℝ))
    (χ : Λ →+ (Fin c → AddCircle (1 : ℝ))) :
    ∃ 𝒜 : AutomorphicForm.WindingDatum r d c, ∀ n : Fin d → ℤ, 𝒜.coeff n = 0 := by
  refine ⟨
    { Λ := Λ, hΛ := hΛ, s := s, ω := ω, hω := hω, hpf := hpf, χ := χ
      sub := fun _ => Λ
      hsub := fun _ => le_rfl
      Ψ := fun _ _ => 0
      hΨc := fun _ => continuous_const
      hΨi := fun _ => integrable_zero _ _ _
      C := fun _ => 0
      hΨd := fun _ x => by simp
      hΨhatd := fun _ ξ => by simp
      m := fun _ _ => 0
      θ₀ := fun _ _ => 0
      x₀ := fun _ _ => 0
      n₀ := fun _ _ => 0
      lam := fun _ => 0
      hsum := by simpa using summable_zero }, fun n => ?_⟩
  exact WindingDatum.coeff_eq_zero_of_lam_eq_zero _ (fun _ => rfl) n

end ANR25

end

theorem solution
    {r d c N : ℕ}
    (Λ : AddSubgroup ((Fin r → ℝ) × (Fin d → ℤ))) (hΛ : DiscreteTopology Λ)
    (s : (Fin r → ℝ) →ₗ[ℝ] ℝ) (ω : Fin d → ℝ) (hω : ω ≠ 0)
    (hpf : ∀ γ ∈ Λ, s γ.1 = ∑ i, ω i * (γ.2 i : ℝ))
    (χ : Λ →+ (Fin c → AddCircle (1 : ℝ)))
    (lift : (Fin r → ℝ) × (Fin d → ℤ) → (Fin c → ℝ))
    (hlift : ∀ (γ : (Fin r → ℝ) × (Fin d → ℤ)) (hγ : γ ∈ Λ) (j : Fin c),
      ((lift γ j : ℝ) : AddCircle (1 : ℝ)) = χ ⟨γ, hγ⟩ j)
    (sub : Fin N → AddSubgroup ((Fin r → ℝ) × (Fin d → ℤ))) (hsub : ∀ i, sub i ≤ Λ)
    (G : Fin N → (Fin r → ℝ) × (Fin c → ℝ) → ℂ) (hG : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (G i))
    (R : ℝ) (hR : 0 ≤ R) (hGsupp : ∀ i (p : (Fin r → ℝ) × (Fin c → ℝ)), (∃ k, R < |p.1 k|) → G i p = 0)
    (hGper : ∀ i (p : (Fin r → ℝ) × (Fin c → ℝ)) (j : Fin c), G i (p.1, p.2 + Pi.single j 1) = G i p)
    (x₀ : Fin N → Fin r → ℝ) (n₀ : Fin N → Fin d → ℤ) (θ₀ : Fin N → Fin c → ℝ) :
    ∃ 𝒜 : AutomorphicForm.WindingDatum r d c, ∀ n : Fin d → ℤ,
      𝒜.coeff n = ∑ i : Fin N, ∑' γ : sub i,
        if (γ : (Fin r → ℝ) × (Fin d → ℤ)).2 + n₀ i = n then
          G i (x₀ i + (γ : (Fin r → ℝ) × (Fin d → ℤ)).1, θ₀ i + lift (γ : (Fin r → ℝ) × (Fin d → ℤ)))
        else 0 := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    obtain ⟨𝒜, h𝒜⟩ := ANR25.main_zero Λ hΛ s ω hω hpf χ
    exact ⟨𝒜, fun n => by rw [h𝒜 n]; simp⟩
  · exact ANR25.main Λ hΛ s ω hω hpf χ lift hlift sub hsub G hG R hR hGsupp hGper x₀ n₀ θ₀ hN

#print axioms solution

end S_AutomorphicForm_WindingDatum_exists_forall_coeff_eq_sum_tsum_ite_of_contDiff_of_periodic
end P2MW
export P2MW.S_AutomorphicForm_WindingDatum_exists_forall_coeff_eq_sum_tsum_ite_of_contDiff_of_periodic (solution)
