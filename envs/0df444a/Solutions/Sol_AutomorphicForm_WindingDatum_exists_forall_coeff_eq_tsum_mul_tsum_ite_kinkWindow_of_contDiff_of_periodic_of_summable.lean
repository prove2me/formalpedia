-- Prove2me | solution 1 for AutomorphicForm.WindingDatum.exists_forall_coeff_eq_tsum_mul_tsum_ite_kinkWindow_of_contDiff_of_periodic_of_summable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/6cda58af-8538-5903-b9c4-86a072881c0b

import Mathlib
import Definitions.Def_AutomorphicForm_WindingDatum
import Theorems.Thm_MeasureTheory_exists_summable_forall_fourierMode_kinkWindow_productPoisson
import Theorems.Thm_AutomorphicForm_WindingDatum_exists_forall_summable_norm_fibreTerm_and_norm_fibreCoeff_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_WindingDatum_exists_forall_coeff_eq_tsum_mul_tsum_ite_kinkWindow_of_contDiff_of_periodic_of_summable

set_option autoImplicit false

open MeasureTheory

noncomputable section

namespace ANRD

open AutomorphicForm

def E {c : ℕ} (m : Fin c → ℤ) (θ : Fin c → ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ))

def mode {r c : ℕ} (W : (Fin r → ℝ) × (Fin c → ℝ) → ℂ) (m : Fin c → ℤ) (x : Fin r → ℝ) : ℂ :=
  ∫ θ in Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1),
    W (x, θ) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ)))

def GD {r c q : ℕ} (kC : Fin c → Fin r) (kR : Fin q → Fin r)
    (B : (Fin r → ℝ) × (Fin c → ℝ) → ℂ) (C : Fin q → (Fin r → ℝ) × (Fin c → ℝ) → ℂ)
    (E' : Fin c → (Fin r → ℝ) × (Fin c → ℝ) → ℂ) : (Fin r → ℝ) × (Fin c → ℝ) → ℂ := fun p =>
  B p + ∑ i, ((|1 - Real.exp (p.1 (kR i))| : ℝ) : ℂ) * C i p +
    ∑ j, ((‖(1 : ℂ) - Complex.exp ((p.1 (kC j) / 2 : ℝ) + 2 * Real.pi * Complex.I * (p.2 j : ℝ))‖ ^ 2 *
          Real.log ‖(1 : ℂ) - Complex.exp ((p.1 (kC j) / 2 : ℝ) + 2 * Real.pi * Complex.I * (p.2 j : ℝ))‖ : ℝ) : ℂ) *
        E' j p

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

theorem finite_fibre {r d : ℕ} (Λ : AddSubgroup ((Fin r → ℝ) × (Fin d → ℤ))) (hΛ : DiscreteTopology Λ)
    (Sg : AddSubgroup ((Fin r → ℝ) × (Fin d → ℤ))) (hSg : Sg ≤ Λ)
    (k₀ n : Fin d → ℤ) (x₀ : Fin r → ℝ) (S : Set (Fin r → ℝ)) (hS : IsCompact S) :
    Set.Finite {γ : Sg | (γ : (Fin r → ℝ) × (Fin d → ℤ)).2 + k₀ = n ∧
      x₀ + (γ : (Fin r → ℝ) × (Fin d → ℤ)).1 ∈ S} := by
  set Bx : Set ((Fin r → ℝ) × (Fin d → ℤ)) := ((fun x : Fin r → ℝ => x₀ + x) ⁻¹' S) ×ˢ {n - k₀} with hB
  have hBc : IsCompact Bx := by
    refine IsCompact.prod ?_ isCompact_singleton
    exact (Homeomorph.addLeft x₀).isCompact_preimage.mpr hS
  haveI := hΛ
  have hΛc : IsClosed (Λ : Set ((Fin r → ℝ) × (Fin d → ℤ))) := AddSubgroup.isClosed_of_discrete
  have hK : IsCompact ((Λ : Set ((Fin r → ℝ) × (Fin d → ℤ))) ∩ Bx) := hBc.inter_left hΛc
  have hdisc : IsDiscrete ((Λ : Set ((Fin r → ℝ) × (Fin d → ℤ))) ∩ Bx) :=
    (SetLike.isDiscrete_iff_discreteTopology.mpr hΛ).mono Set.inter_subset_left
  have hfin : ((Λ : Set ((Fin r → ℝ) × (Fin d → ℤ))) ∩ Bx).Finite := hK.finite hdisc
  have hpre : (Subtype.val ⁻¹' ((Λ : Set ((Fin r → ℝ) × (Fin d → ℤ))) ∩ Bx) : Set Sg).Finite :=
    hfin.preimage Subtype.val_injective.injOn
  refine hpre.subset ?_
  intro γ hγ
  obtain ⟨hk, hx⟩ := hγ
  refine ⟨hSg γ.2, ?_, ?_⟩
  · exact hx
  · rw [Set.mem_singleton_iff]
    exact eq_sub_of_add_eq hk

section Inner

variable {r d c : ℕ}

theorem inner
    (Sg : AddSubgroup ((Fin r → ℝ) × (Fin d → ℤ)))
    (W : (Fin r → ℝ) × (Fin c → ℝ) → ℂ) (S : Set (Fin r → ℝ))
    (hWsupp : ∀ p : (Fin r → ℝ) × (Fin c → ℝ), p.1 ∉ S → W p = 0)
    (Cm : (Fin c → ℤ) → ℝ) (hC : Summable Cm) (hC0 : ∀ m, 0 ≤ Cm m)
    (hmode0 : ∀ (m : Fin c → ℤ) (x : Fin r → ℝ), x ∉ S → mode W m x = 0)
    (hmoded : ∀ (m : Fin c → ℤ) (x : Fin r → ℝ), ‖mode W m x‖ ≤ Cm m * ∏ k, (1 + |x k|)⁻¹ ^ 2)
    (hrecW : ∀ p : (Fin r → ℝ) × (Fin c → ℝ), HasSum (fun m : Fin c → ℤ => mode W m p.1 * E m p.2) (W p))
    (x₀ : Fin r → ℝ) (k₀ : Fin d → ℤ) (θf : (Fin r → ℝ) × (Fin d → ℤ) → (Fin c → ℝ))
    (n : Fin d → ℤ)
    (hfin : Set.Finite {γ : Sg | (γ : (Fin r → ℝ) × (Fin d → ℤ)).2 + k₀ = n ∧
      x₀ + (γ : (Fin r → ℝ) × (Fin d → ℤ)).1 ∈ S}) :
    (Summable fun m : Fin c → ℤ => ∑' γ : Sg,
      (if (γ : (Fin r → ℝ) × (Fin d → ℤ)).2 + k₀ = n then
        mode W m (x₀ + (γ : (Fin r → ℝ) × (Fin d → ℤ)).1) * E m (θf γ) else 0)) ∧
    ∑' m : Fin c → ℤ, ∑' γ : Sg,
      (if (γ : (Fin r → ℝ) × (Fin d → ℤ)).2 + k₀ = n then
        mode W m (x₀ + (γ : (Fin r → ℝ) × (Fin d → ℤ)).1) * E m (θf γ) else 0) =
    ∑' γ : Sg, (if (γ : (Fin r → ℝ) × (Fin d → ℤ)).2 + k₀ = n then
        W (x₀ + (γ : (Fin r → ℝ) × (Fin d → ℤ)).1, θf γ) else 0) := by
  set F : Finset Sg := hfin.toFinset with hF
  have hmemF : ∀ γ : Sg, γ ∉ F → (γ : (Fin r → ℝ) × (Fin d → ℤ)).2 + k₀ = n →
      x₀ + (γ : (Fin r → ℝ) × (Fin d → ℤ)).1 ∉ S := by
    intro γ hγ hk hx
    apply hγ
    rw [hF, Set.Finite.mem_toFinset]
    exact ⟨hk, hx⟩
  set T : (Fin c → ℤ) → Sg → ℂ := fun m γ =>
    if (γ : (Fin r → ℝ) × (Fin d → ℤ)).2 + k₀ = n then
      mode W m (x₀ + (γ : (Fin r → ℝ) × (Fin d → ℤ)).1) * E m (θf γ) else 0 with hT
  have hT0 : ∀ (m : Fin c → ℤ) (γ : Sg), γ ∉ F → T m γ = 0 := by
    intro m γ hγ
    simp only [hT]
    split_ifs with hk
    · rw [hmode0 m _ (hmemF γ hγ hk), zero_mul]
    · rfl
  have hTm : ∀ γ : Sg, Summable fun m => T m γ := by
    intro γ
    refine Summable.of_norm_bounded hC fun m => ?_
    simp only [hT]
    split_ifs with hk
    · rw [norm_mul, norm_E, mul_one]
      exact (hmoded m _).trans (mul_le_of_le_one_right (hC0 m) (prod_inv_one_add_abs_sq_le_one _))
    · rw [norm_zero]; exact hC0 m
  have h1 : ∀ m, ∑' γ : Sg, T m γ = ∑ γ ∈ F, T m γ := fun m => tsum_eq_sum (hT0 m)
  have hrec : ∀ γ : Sg, ∑' m, T m γ =
      (if (γ : (Fin r → ℝ) × (Fin d → ℤ)).2 + k₀ = n then
        W (x₀ + (γ : (Fin r → ℝ) × (Fin d → ℤ)).1, θf γ) else 0) := by
    intro γ
    simp only [hT]
    split_ifs with hk
    · exact (hrecW (x₀ + (γ : (Fin r → ℝ) × (Fin d → ℤ)).1, θf γ)).tsum_eq
    · exact tsum_zero
  refine ⟨?_, ?_⟩
  · have : (fun m : Fin c → ℤ => ∑' γ : Sg, T m γ) = fun m => ∑ γ ∈ F, T m γ := funext h1
    rw [this]
    exact summable_sum fun γ _ => hTm γ
  · calc ∑' m, ∑' γ : Sg, T m γ = ∑' m, ∑ γ ∈ F, T m γ := tsum_congr h1
      _ = ∑ γ ∈ F, ∑' m, T m γ := Summable.tsum_finsetSum fun γ _ => hTm γ
      _ = ∑ γ ∈ F, (if (γ : (Fin r → ℝ) × (Fin d → ℤ)).2 + k₀ = n then
            W (x₀ + (γ : (Fin r → ℝ) × (Fin d → ℤ)).1, θf γ) else 0) := Finset.sum_congr rfl fun γ _ => hrec γ
      _ = ∑' γ : Sg, (if (γ : (Fin r → ℝ) × (Fin d → ℤ)).2 + k₀ = n then
            W (x₀ + (γ : (Fin r → ℝ) × (Fin d → ℤ)).1, θf γ) else 0) := by
          refine (tsum_eq_sum fun γ hγ => ?_).symm
          split_ifs with hk
          · exact hWsupp _ (hmemF γ hγ hk)
          · rfl

end Inner

theorem summable_weights {A c : ℕ} (Cm : Fin A → (Fin c → ℤ) → ℝ) (hCm0 : ∀ a m, 0 ≤ Cm a m)
    (hCms : ∀ a, Summable (Cm a)) (lam : ℕ → ℂ) (hlam : Summable fun i => ‖lam i‖) (shape : ℕ → Fin A) :
    Summable fun b : ℕ × (Fin c → ℤ) => ‖lam b.1‖ * Cm (shape b.1) b.2 := by
  obtain ⟨D, hDdef⟩ : ∃ D : (Fin c → ℤ) → ℝ, ∀ m, D m = ∑ a : Fin A, Cm a m := ⟨_, fun _ => rfl⟩
  obtain ⟨nl, hnl⟩ : ∃ nl : ℕ → ℝ, ∀ i, nl i = ‖lam i‖ := ⟨_, fun _ => rfl⟩
  have hD : Summable D := by
    have := summable_sum (s := (Finset.univ : Finset (Fin A))) fun a _ => hCms a
    exact this.congr fun m => (hDdef m).symm
  have hnlS : Summable nl := hlam.congr fun i => (hnl i).symm
  have h1 : 0 ≤ nl := fun i => by rw [hnl]; exact norm_nonneg _
  have h2 : 0 ≤ D := fun m => by rw [hDdef]; exact Finset.sum_nonneg fun a _ => hCm0 a m
  have hprod : Summable fun b : ℕ × (Fin c → ℤ) => nl b.1 * D b.2 := Summable.mul_of_nonneg hnlS hD h1 h2
  refine Summable.of_nonneg_of_le (fun b => mul_nonneg (norm_nonneg _) (hCm0 _ _)) (fun b => ?_) hprod
  have hle : Cm (shape b.1) b.2 ≤ D b.2 := by
    rw [hDdef]
    exact Finset.single_le_sum (f := fun a => Cm a b.2) (fun a _ => hCm0 a b.2) (Finset.mem_univ (shape b.1))
  rw [hnl]
  exact mul_le_mul_of_nonneg_left hle (norm_nonneg _)

end ANRD

end

theorem solution
    {r d c A q : ℕ}
    (Λ : AddSubgroup ((Fin r → ℝ) × (Fin d → ℤ))) (hΛ : DiscreteTopology Λ)
    (s : (Fin r → ℝ) →ₗ[ℝ] ℝ) (ω : Fin d → ℝ) (hω : ω ≠ 0)
    (hpf : ∀ γ ∈ Λ, s γ.1 = ∑ i, ω i * (γ.2 i : ℝ))
    (χ : Λ →+ (Fin c → AddCircle (1 : ℝ)))
    (lift : (Fin r → ℝ) × (Fin d → ℤ) → (Fin c → ℝ))
    (hlift : ∀ (γ : (Fin r → ℝ) × (Fin d → ℤ)) (hγ : γ ∈ Λ) (j : Fin c),
      ((lift γ j : ℝ) : AddCircle (1 : ℝ)) = χ ⟨γ, hγ⟩ j)

    (kC : Fin c → Fin r) (kR : Fin q → Fin r)

    (B : Fin A → (Fin r → ℝ) × (Fin c → ℝ) → ℂ) (C : Fin A → Fin q → (Fin r → ℝ) × (Fin c → ℝ) → ℂ)
    (E : Fin A → Fin c → (Fin r → ℝ) × (Fin c → ℝ) → ℂ)
    (hB : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (B a)) (hC : ∀ a k, ContDiff ℝ (⊤ : ℕ∞) (C a k))
    (hE : ∀ a j, ContDiff ℝ (⊤ : ℕ∞) (E a j))
    (hper : ∀ (a : Fin A) (p : (Fin r → ℝ) × (Fin c → ℝ)) (j : Fin c),
      B a (p.1, p.2 + Pi.single j 1) = B a p ∧ (∀ k, C a k (p.1, p.2 + Pi.single j 1) = C a k p) ∧
        ∀ j', E a j' (p.1, p.2 + Pi.single j 1) = E a j' p)
    (S : Set (Fin r → ℝ)) (hS : IsCompact S)
    (hsupp : ∀ (a : Fin A) (p : (Fin r → ℝ) × (Fin c → ℝ)), p.1 ∉ S →
      B a p = 0 ∧ (∀ k, C a k p = 0) ∧ ∀ j, E a j p = 0)

    (sub : ℕ → AddSubgroup ((Fin r → ℝ) × (Fin d → ℤ))) (hsub : ∀ i, sub i ≤ Λ)
    (shape : ℕ → Fin A) (lam : ℕ → ℂ) (hlam : Summable fun i => ‖lam i‖)
    (x₀ : ℕ → Fin r → ℝ) (n₀ : ℕ → Fin d → ℤ) (θ₀ : ℕ → Fin c → ℝ) :
    ∃ 𝒜 : AutomorphicForm.WindingDatum r d c, ∀ n : Fin d → ℤ,
      𝒜.coeff n = ∑' i : ℕ, lam i * ∑' γ : sub i,
        if (γ : (Fin r → ℝ) × (Fin d → ℤ)).2 + n₀ i = n then
          B (shape i) (x₀ i + (γ : (Fin r → ℝ) × (Fin d → ℤ)).1, θ₀ i + lift (γ : (Fin r → ℝ) × (Fin d → ℤ))) +
            ∑ k : Fin q, ((|1 - Real.exp ((x₀ i + (γ : (Fin r → ℝ) × (Fin d → ℤ)).1) (kR k))| : ℝ) : ℂ) * C (shape i) k (x₀ i + (γ : (Fin r → ℝ) × (Fin d → ℤ)).1, θ₀ i + lift (γ : (Fin r → ℝ) × (Fin d → ℤ))) +
            ∑ j : Fin c, ((‖(1 : ℂ) - Complex.exp ((((x₀ i + (γ : (Fin r → ℝ) × (Fin d → ℤ)).1) (kC j) / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * (((θ₀ i + lift (γ : (Fin r → ℝ) × (Fin d → ℤ))) j : ℝ) : ℂ))‖ ^ 2 *
                  Real.log ‖(1 : ℂ) - Complex.exp ((((x₀ i + (γ : (Fin r → ℝ) × (Fin d → ℤ)).1) (kC j) / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * (((θ₀ i + lift (γ : (Fin r → ℝ) × (Fin d → ℤ))) j : ℝ) : ℂ))‖ : ℝ) : ℂ) *
              E (shape i) j (x₀ i + (γ : (Fin r → ℝ) × (Fin d → ℤ)).1, θ₀ i + lift (γ : (Fin r → ℝ) × (Fin d → ℤ)))
        else 0 := by
  classical

  have hPK : ∀ a : Fin A, ∃ Cm : (Fin c → ℤ) → ℝ, (∀ m, 0 ≤ Cm m) ∧ Summable Cm ∧
      (∀ m, Continuous (ANRD.mode (ANRD.GD kC kR (B a) (C a) (E a)) m) ∧
        Integrable (ANRD.mode (ANRD.GD kC kR (B a) (C a) (E a)) m) ∧
        (∀ x : Fin r → ℝ, ‖ANRD.mode (ANRD.GD kC kR (B a) (C a) (E a)) m x‖ ≤ Cm m * ∏ k, (1 + |x k|)⁻¹ ^ 2) ∧
        (∀ ξ : Fin r → ℝ,
          ‖∫ x : Fin r → ℝ, Complex.exp (-(2 * Real.pi * Complex.I * ((∑ k, ξ k * x k : ℝ) : ℂ))) *
              ANRD.mode (ANRD.GD kC kR (B a) (C a) (E a)) m x‖ ≤ Cm m * ∏ k, (1 + |ξ k|)⁻¹ ^ 2)) ∧
      ∀ p : (Fin r → ℝ) × (Fin c → ℝ),
        HasSum (fun m : Fin c → ℤ => ANRD.mode (ANRD.GD kC kR (B a) (C a) (E a)) m p.1 * ANRD.E m p.2)
          (ANRD.GD kC kR (B a) (C a) (E a) p) :=
    fun a => MeasureTheory.exists_summable_forall_fourierMode_kinkWindow_productPoisson kC kR (B a) (C a) (E a)
      (hB a) (hC a) (hE a) (hper a) S hS (hsupp a)
  choose Cm hCm0 hCms hCmp hrec using hPK

  have hGD0 : ∀ (a : Fin A) (p : (Fin r → ℝ) × (Fin c → ℝ)), p.1 ∉ S → ANRD.GD kC kR (B a) (C a) (E a) p = 0 := by
    intro a p hp
    obtain ⟨h1, h2, h3⟩ := hsupp a p hp
    simp [ANRD.GD, h1, h2, h3]
  have hmode0 : ∀ (a : Fin A) (m : Fin c → ℤ) (x : Fin r → ℝ), x ∉ S →
      ANRD.mode (ANRD.GD kC kR (B a) (C a) (E a)) m x = 0 := by
    intro a m x hx
    unfold ANRD.mode
    have : ∀ θ : Fin c → ℝ, ANRD.GD kC kR (B a) (C a) (E a) (x, θ) *
        Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ))) = 0 := fun θ => by
      rw [hGD0 a (x, θ) hx, zero_mul]
    simp_rw [this]
    exact integral_zero _ _

  haveI : Nonempty (ℕ × (Fin c → ℤ)) := ⟨(0, 0)⟩
  obtain ⟨e, he⟩ := Countable.exists_injective_nat (ℕ × (Fin c → ℤ))
  set aa : ℕ → ℕ × (Fin c → ℤ) := Function.invFun e with haa_def
  have haa : ∀ b, aa (e b) = b := Function.leftInverse_invFun he
  set lamW : ℕ → ℂ := (Set.range e).indicator fun ι => lam (aa ι).1 with hlamW
  have hlam1 : ∀ b, lamW (e b) = lam b.1 := fun b => by
    rw [hlamW, Set.indicator_of_mem (Set.mem_range_self b)]; simp only [haa]
  have hlam0 : ∀ ι, ι ∉ Set.range e → lamW ι = 0 := fun ι hι => by
    rw [hlamW, Set.indicator_of_notMem hι]

  have hsumP : Summable fun b : ℕ × (Fin c → ℤ) => ‖lam b.1‖ * Cm (shape b.1) b.2 :=
    ANRD.summable_weights Cm hCm0 hCms lam hlam shape
  have hsumw : Summable fun ι : ℕ => ‖lamW ι‖ * Cm (shape (aa ι).1) (aa ι).2 := by
    have h0 : ∀ ι ∉ Set.range e, (fun ι : ℕ => ‖lamW ι‖ * Cm (shape (aa ι).1) (aa ι).2) ι = 0 := by
      intro ι hι; simp only [hlam0 ι hι, norm_zero, zero_mul]
    refine (he.summable_iff h0).mp ?_
    have : ((fun ι : ℕ => ‖lamW ι‖ * Cm (shape (aa ι).1) (aa ι).2) ∘ e) = fun b => ‖lam b.1‖ * Cm (shape b.1) b.2 := by
      funext b; simp only [Function.comp_apply, hlam1, haa]
    rw [this]
    exact hsumP

  refine ⟨
    ({ Λ := Λ, hΛ := hΛ, s := s, ω := ω, hω := hω, hpf := hpf, χ := χ,
        sub := fun ι => sub (aa ι).1,
        hsub := fun ι => hsub (aa ι).1,
        Ψ := fun ι => ANRD.mode (ANRD.GD kC kR (B (shape (aa ι).1)) (C (shape (aa ι).1)) (E (shape (aa ι).1))) (aa ι).2,
        hΨc := fun ι => (hCmp (shape (aa ι).1) (aa ι).2).1,
        hΨi := fun ι => (hCmp (shape (aa ι).1) (aa ι).2).2.1,
        C := fun ι => Cm (shape (aa ι).1) (aa ι).2,
        hΨd := fun ι x => (hCmp (shape (aa ι).1) (aa ι).2).2.2.1 x,
        hΨhatd := fun ι ξ => (hCmp (shape (aa ι).1) (aa ι).2).2.2.2 ξ,
        m := fun ι => (aa ι).2,
        θ₀ := fun ι j => ((θ₀ (aa ι).1 j : ℝ) : AddCircle (1 : ℝ)),
        x₀ := fun ι => x₀ (aa ι).1,
        n₀ := fun ι => n₀ (aa ι).1,
        lam := lamW,
        hsum := hsumw } : AutomorphicForm.WindingDatum r d c), fun n => ?_⟩

  set T : ∀ i : ℕ, (Fin c → ℤ) → sub i → ℂ := fun i m γ =>
    if (γ : (Fin r → ℝ) × (Fin d → ℤ)).2 + n₀ i = n then
      ANRD.mode (ANRD.GD kC kR (B (shape i)) (C (shape i)) (E (shape i))) m (x₀ i + (γ : (Fin r → ℝ) × (Fin d → ℤ)).1) *
        ANRD.E m (θ₀ i + lift (γ : (Fin r → ℝ) × (Fin d → ℤ))) else 0 with hT
  have hphase : ∀ (i : ℕ) (m : Fin c → ℤ) (γ : sub i),
      ∏ j, fourier (m j) (((θ₀ i j : ℝ) : AddCircle (1 : ℝ)) +
        χ ⟨(γ : (Fin r → ℝ) × (Fin d → ℤ)), hsub i γ.2⟩ j) =
      ANRD.E m (θ₀ i + lift (γ : (Fin r → ℝ) × (Fin d → ℤ))) := by
    intro i m γ
    rw [← ANRD.prod_fourier_coe]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← hlift _ (hsub i γ.2) j, ← AddCircle.coe_add]
    rfl
  have hstep0 : AutomorphicForm.WindingDatum.coeff
    ({ Λ := Λ, hΛ := hΛ, s := s, ω := ω, hω := hω, hpf := hpf, χ := χ,
        sub := fun ι => sub (aa ι).1,
        hsub := fun ι => hsub (aa ι).1,
        Ψ := fun ι => ANRD.mode (ANRD.GD kC kR (B (shape (aa ι).1)) (C (shape (aa ι).1)) (E (shape (aa ι).1))) (aa ι).2,
        hΨc := fun ι => (hCmp (shape (aa ι).1) (aa ι).2).1,
        hΨi := fun ι => (hCmp (shape (aa ι).1) (aa ι).2).2.1,
        C := fun ι => Cm (shape (aa ι).1) (aa ι).2,
        hΨd := fun ι x => (hCmp (shape (aa ι).1) (aa ι).2).2.2.1 x,
        hΨhatd := fun ι ξ => (hCmp (shape (aa ι).1) (aa ι).2).2.2.2 ξ,
        m := fun ι => (aa ι).2,
        θ₀ := fun ι j => ((θ₀ (aa ι).1 j : ℝ) : AddCircle (1 : ℝ)),
        x₀ := fun ι => x₀ (aa ι).1,
        n₀ := fun ι => n₀ (aa ι).1,
        lam := lamW,
        hsum := hsumw } : AutomorphicForm.WindingDatum r d c) n =
      ∑' ι : ℕ, lamW ι * ∑' γ : sub (aa ι).1, T (aa ι).1 (aa ι).2 γ := by
    simp only [AutomorphicForm.WindingDatum.coeff, AutomorphicForm.WindingDatum.fibreCoeff,
      AutomorphicForm.WindingDatum.fibreTerm, hT, hphase]

  have hK := AutomorphicForm.WindingDatum.exists_forall_summable_norm_fibreTerm_and_norm_fibreCoeff_le

    ({ Λ := Λ, hΛ := hΛ, s := s, ω := ω, hω := hω, hpf := hpf, χ := χ,
        sub := fun ι => sub (aa ι).1,
        hsub := fun ι => hsub (aa ι).1,
        Ψ := fun ι => ANRD.mode (ANRD.GD kC kR (B (shape (aa ι).1)) (C (shape (aa ι).1)) (E (shape (aa ι).1))) (aa ι).2,
        hΨc := fun ι => (hCmp (shape (aa ι).1) (aa ι).2).1,
        hΨi := fun ι => (hCmp (shape (aa ι).1) (aa ι).2).2.1,
        C := fun ι => Cm (shape (aa ι).1) (aa ι).2,
        hΨd := fun ι x => (hCmp (shape (aa ι).1) (aa ι).2).2.2.1 x,
        hΨhatd := fun ι ξ => (hCmp (shape (aa ι).1) (aa ι).2).2.2.2 ξ,
        m := fun ι => (aa ι).2,
        θ₀ := fun ι j => ((θ₀ (aa ι).1 j : ℝ) : AddCircle (1 : ℝ)),
        x₀ := fun ι => x₀ (aa ι).1,
        n₀ := fun ι => n₀ (aa ι).1,
        lam := lamW,
        hsum := hsumw } : AutomorphicForm.WindingDatum r d c)
  obtain ⟨Kc, hKc0, hKc1, hKc2⟩ := hK
  have hsumN : Summable fun ι : ℕ => lamW ι * ∑' γ : sub (aa ι).1, T (aa ι).1 (aa ι).2 γ := by
    have := hKc2 n
    refine Summable.of_norm ?_
    refine this.congr fun ι => ?_
    simp only [AutomorphicForm.WindingDatum.fibreCoeff, AutomorphicForm.WindingDatum.fibreTerm, hT, hphase]
  rw [hstep0]
  set Φ : ℕ × (Fin c → ℤ) → ℂ := fun b => ∑' γ : sub b.1, T b.1 b.2 γ with hΦ
  have hsuppe : Function.support (fun ι : ℕ => lamW ι * Φ (aa ι)) ⊆ Set.range e := by
    intro ι hι
    by_contra h
    exact hι (by simp only [hlam0 ι h, zero_mul])
  have hb : ∀ b : ℕ × (Fin c → ℤ), lamW (e b) * Φ (aa (e b)) = lam b.1 * Φ b := fun b => by
    rw [hlam1, haa]
  have hfin : ∀ i : ℕ, Set.Finite {γ : sub i | (γ : (Fin r → ℝ) × (Fin d → ℤ)).2 + n₀ i = n ∧
      x₀ i + (γ : (Fin r → ℝ) × (Fin d → ℤ)).1 ∈ S} :=
    fun i => ANRD.finite_fibre Λ hΛ (sub i) (hsub i) (n₀ i) n (x₀ i) S hS
  have hinner := fun i : ℕ => ANRD.inner (sub i) (ANRD.GD kC kR (B (shape i)) (C (shape i)) (E (shape i))) S
    (hGD0 (shape i)) (Cm (shape i)) (hCms (shape i)) (hCm0 (shape i)) (hmode0 (shape i))
    (fun m x => (hCmp (shape i) m).2.2.1 x) (hrec (shape i)) (x₀ i) (n₀ i)
    (fun γ => θ₀ i + lift γ) n (hfin i)

  have hSb : Summable fun b : ℕ × (Fin c → ℤ) => lam b.1 * Φ b := by
    have h0 : ∀ ι ∉ Set.range e, (fun ι : ℕ => lamW ι * Φ (aa ι)) ι = 0 := by
      intro ι hι; simp only [hlam0 ι hι, zero_mul]
    have := (he.summable_iff h0).mpr hsumN
    refine this.congr fun b => ?_
    simp only [Function.comp_apply, hb]
  calc ∑' ι : ℕ, lamW ι * Φ (aa ι) = ∑' b : ℕ × (Fin c → ℤ), lamW (e b) * Φ (aa (e b)) :=
        (he.tsum_eq hsuppe).symm
    _ = ∑' b : ℕ × (Fin c → ℤ), lam b.1 * Φ b := tsum_congr hb
    _ = ∑' i : ℕ, ∑' m : Fin c → ℤ, lam i * Φ (i, m) :=
        Summable.tsum_prod' hSb fun i => ((hinner i).1.mul_left (lam i))
    _ = ∑' i : ℕ, lam i * ∑' m : Fin c → ℤ, Φ (i, m) := by simp_rw [tsum_mul_left]
    _ = _ := tsum_congr fun i => by rw [(hinner i).2]; rfl

end S_AutomorphicForm_WindingDatum_exists_forall_coeff_eq_tsum_mul_tsum_ite_kinkWindow_of_contDiff_of_periodic_of_summable
end P2MW
export P2MW.S_AutomorphicForm_WindingDatum_exists_forall_coeff_eq_tsum_mul_tsum_ite_kinkWindow_of_contDiff_of_periodic_of_summable (solution)
