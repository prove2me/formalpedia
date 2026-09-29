-- Prove2me | solution 1 for AutomorphicForm.integral_twistedConj_mul_eq_integral_conj_fibreIntegral_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/a59b0555-5467-5d39-9975-8ec26ad23087

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Prod
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_integral_twistedConj_mul_eq_integral_conj_fibreIntegral_mul

set_option autoImplicit false

open MeasureTheory

namespace TwistedShift

variable {G : Type} [Group G]

private def twc {n : ℕ} (δ x : Fin (n + 1) → G) : Fin (n + 1) → G := fun j => (x j)⁻¹ * δ j * x (j + 1)

private def cc {n : ℕ} (δ x : Fin (n + 1) → G) : Fin n → G := fun i => (x i.castSucc)⁻¹ * δ i.castSucc * x i.succ

private def nrm {n : ℕ} (δ : Fin (n + 1) → G) : G := (List.ofFn δ).prod

private def twCent {n : ℕ} (δ : Fin (n + 1) → G) : Subgroup (Fin (n + 1) → G) where
  carrier := {t | ∀ j, (t j)⁻¹ * δ j * t (j + 1) = δ j}
  mul_mem' := by
    intro s t hs ht j
    have hs' := hs j; have ht' := ht j
    simp only [Pi.mul_apply, mul_inv_rev]
    calc _ = (t j)⁻¹ * ((s j)⁻¹ * δ j * s (j + 1)) * t (j + 1) := by simp only [mul_assoc]
      _ = δ j := by rw [hs', ht']
  one_mem' := by intro j; simp
  inv_mem' := by
    intro t ht j
    have h := ht j
    simp only [Pi.inv_apply, inv_inv]
    calc _ = t j * ((t j)⁻¹ * δ j * t (j + 1)) * (t (j + 1))⁻¹ := by rw [h]
      _ = δ j := by simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]

private theorem twc_castSucc {n : ℕ} (δ x : Fin (n + 1) → G) (i : Fin n) :
    twc δ x i.castSucc = cc δ x i := by
  simp only [twc, cc, Fin.coeSucc_eq_succ]

private theorem twc_last {n : ℕ} (δ x : Fin (n + 1) → G) :
    twc δ x (Fin.last n) = (x (Fin.last n))⁻¹ * δ (Fin.last n) * x 0 := by
  simp only [twc, Fin.last_add_one]

private theorem prod_ofFn_cc {n : ℕ} (δ x : Fin (n + 1) → G) :
    (List.ofFn (cc δ x)).prod =
      (x 0)⁻¹ * (List.ofFn fun i : Fin n => δ i.castSucc).prod * x (Fin.last n) := by
  induction n with
  | zero => simp [List.ofFn_zero]
  | succ n ih =>
    rw [List.ofFn_succ, List.prod_cons]
    have htail : (List.ofFn fun i : Fin n => cc δ x i.succ) =
        List.ofFn (cc (fun j => δ j.succ) (fun j => x j.succ)) := rfl
    rw [htail, ih, List.ofFn_succ (f := fun i : Fin (n + 1) => δ i.castSucc), List.prod_cons]
    simp only [cc, Fin.castSucc_zero, Fin.succ_last, Fin.succ_castSucc, mul_assoc,
      mul_inv_cancel_left]

private theorem prod_twc {n : ℕ} (δ x : Fin (n + 1) → G) :
    (List.ofFn (twc δ x)).prod = (x 0)⁻¹ * nrm δ * x 0 := by
  rw [List.ofFn_succ', List.prod_concat]
  simp only [twc_castSucc, twc_last, prod_ofFn_cc, nrm, List.ofFn_succ' δ, List.prod_concat,
    mul_assoc, mul_inv_cancel_left]

private theorem twCent_zero_mem_centralizer {n : ℕ} (δ : Fin (n + 1) → G) (t : Fin (n + 1) → G)
    (ht : t ∈ twCent δ) : t 0 ∈ Subgroup.centralizer ({nrm δ} : Set G) := by
  have htwc : twc δ t = δ := funext fun j => ht j
  have hp := prod_twc δ t
  rw [htwc] at hp
  change nrm δ = (t 0)⁻¹ * nrm δ * t 0 at hp
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc t 0 * nrm δ = t 0 * ((t 0)⁻¹ * nrm δ * t 0) := by rw [← hp]
    _ = nrm δ * t 0 := by rw [mul_assoc, mul_inv_cancel_left]

private theorem cc_mul_of_mem_twCent {n : ℕ} (δ : Fin (n + 1) → G) (t : Fin (n + 1) → G) (ht : t ∈ twCent δ)
    (x : Fin (n + 1) → G) : cc δ (t * x) = cc δ x := by
  funext i
  have h := ht i.castSucc
  rw [Fin.coeSucc_eq_succ] at h
  simp only [cc, Pi.mul_apply, mul_inv_rev]
  calc _ = (x i.castSucc)⁻¹ * ((t i.castSucc)⁻¹ * δ i.castSucc * t i.succ) * x i.succ := by
          simp only [mul_assoc]
    _ = (x i.castSucc)⁻¹ * δ i.castSucc * x i.succ := by rw [h]

private theorem twc_mul_of_mem_twCent {n : ℕ} (δ t : Fin (n + 1) → G) (ht : t ∈ twCent δ)
    (x : Fin (n + 1) → G) : twc δ (t * x) = twc δ x := by
  funext j
  have h := ht j
  simp only [twc, Pi.mul_apply, mul_inv_rev]
  calc _ = (x j)⁻¹ * ((t j)⁻¹ * δ j * t (j + 1)) * x (j + 1) := by simp only [mul_assoc]
    _ = (x j)⁻¹ * δ j * x (j + 1) := by rw [h]

section Measure

variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
  (μ : Measure G) [SigmaFinite μ] [μ.IsMulLeftInvariant]

private noncomputable def fib {n : ℕ} (Φ : (Fin (n + 1) → G) → ℂ) (h : G) : ℂ :=
  ∫ c : Fin n → G, Φ (Fin.snoc c (((List.ofFn c).prod)⁻¹ * h)) ∂(Measure.pi fun _ => μ)

omit [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G] in

private theorem twc_eq_snoc {n : ℕ} (δ x : Fin (n + 1) → G) :
    twc δ x = Fin.snoc (cc δ x) (((List.ofFn (cc δ x)).prod)⁻¹ * ((x 0)⁻¹ * nrm δ * x 0)) := by
  funext j
  induction j using Fin.lastCases with
  | last =>
    rw [Fin.snoc_last, twc_last, prod_ofFn_cc, nrm, List.ofFn_succ' δ, List.prod_concat]
    simp only [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left]
  | cast i => rw [Fin.snoc_castSucc, twc_castSucc]

omit [Group G] [MeasurableMul₂ G] [MeasurableInv G] in
private theorem measurable_cons {m : ℕ} :
    Measurable fun p : G × (Fin m → G) => (Fin.cons p.1 p.2 : Fin (m + 1) → G) := by
  refine measurable_pi_iff.2 fun j => ?_
  induction j using Fin.cases with
  | zero => simpa using measurable_fst
  | succ k => (simp; exact (measurable_pi_apply k).comp measurable_snd)

private theorem measurable_cc_cons {m : ℕ} (δ : Fin (m + 1) → G) :
    Measurable fun p : G × (Fin m → G) => cc δ (Fin.cons p.1 p.2) := by
  refine measurable_pi_iff.2 fun i => ?_
  simp only [cc]
  exact (((measurable_pi_apply _).comp measurable_cons).inv.mul_const _).mul
    ((measurable_pi_apply _).comp measurable_cons)

omit [MeasurableInv G] in
private theorem measurable_ofFn_prod : ∀ m : ℕ, Measurable fun c : Fin m → G => (List.ofFn c).prod
  | 0 => by simp only [List.ofFn_zero, List.prod_nil]; exact measurable_const
  | m + 1 => by
    have htail : Measurable fun c : Fin (m + 1) → G => Fin.tail c :=
      measurable_pi_iff.2 fun i => measurable_pi_apply i.succ
    simp only [List.ofFn_succ, List.prod_cons]
    exact (measurable_pi_apply 0).mul ((measurable_ofFn_prod m).comp htail)

private theorem measurable_twc {m : ℕ} (δ : Fin (m + 1) → G) : Measurable (twc δ) := by
  refine measurable_pi_iff.2 fun j => ?_
  show Measurable fun x : Fin (m + 1) → G => (x j)⁻¹ * δ j * x (j + 1)
  exact ((measurable_pi_apply j).inv.mul_const _).mul (measurable_pi_apply (j + 1))

private theorem measurable_cc {m : ℕ} (δ : Fin (m + 1) → G) : Measurable (cc δ) := by
  refine measurable_pi_iff.2 fun i => ?_
  show Measurable fun x : Fin (m + 1) → G => (x i.castSucc)⁻¹ * δ i.castSucc * x i.succ
  exact ((measurable_pi_apply i.castSucc).inv.mul_const _).mul (measurable_pi_apply i.succ)

private theorem measurePreserving_cc_cons (n : ℕ) :
    ∀ (δ : Fin (n + 1) → G) (g : G),
      MeasurePreserving (fun y : Fin n → G => cc δ (Fin.cons g y)) (Measure.pi fun _ => μ)
        (Measure.pi fun _ => μ) := by
  induction n with
  | zero =>
    intro δ g
    have h : (fun y : Fin 0 → G => cc δ (Fin.cons g y)) = id :=
      funext fun _ => Subsingleton.elim _ _
    rw [h]
    exact MeasurePreserving.id _
  | succ n ih =>
    intro δ g
    have he : MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => G) 0)
        (Measure.pi fun _ => μ) (μ.prod (Measure.pi fun _ => μ)) :=
      measurePreserving_piFinSuccAbove (fun _ => μ) 0
    have hskew : MeasurePreserving
        (fun p : G × (Fin n → G) => (g⁻¹ * δ 0 * p.1, cc (Fin.tail δ) (Fin.cons p.1 p.2)))
        (μ.prod (Measure.pi fun _ => μ)) (μ.prod (Measure.pi fun _ => μ)) :=
      (measurePreserving_mul_left μ (g⁻¹ * δ 0)).skew_product (measurable_cc_cons (Fin.tail δ))
        (Filter.Eventually.of_forall fun a => (ih (Fin.tail δ) a).map_eq)
    have hkey : ∀ y : Fin (n + 1) → G,
        MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => G) 0 (cc δ (Fin.cons g y)) =
          (g⁻¹ * δ 0 * y 0, cc (Fin.tail δ) (Fin.cons (y 0) (Fin.tail y))) := by
      intro y
      rw [Fin.cons_self_tail]
      simp only [MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv_symm_apply,
        Fin.removeNth_zero]
      refine Prod.ext ?_ ?_
      · simp only [cc, Fin.castSucc_zero, Fin.cons_zero, Fin.succ_zero_eq_one, Fin.cons_one]
      · funext i
        simp only [Fin.tail, cc, ← Fin.succ_castSucc, Fin.cons_succ]
    have hfun : (fun y : Fin (n + 1) → G => cc δ (Fin.cons g y)) =
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => G) 0).symm ∘
          (fun p : G × (Fin n → G) => (g⁻¹ * δ 0 * p.1, cc (Fin.tail δ) (Fin.cons p.1 p.2))) ∘
            MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => G) 0 := by
      funext y
      simp only [Function.comp_apply]
      rw [← (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => G) 0).symm_apply_apply
        (cc δ (Fin.cons g y)), hkey y]
      simp only [MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv_symm_apply,
        Fin.removeNth_zero]
    rw [hfun]
    exact (MeasurePreserving.symm _ he).comp (hskew.comp he)

private theorem integral_twc_mul_eq_integral_fib {n : ℕ} (δ : Fin (n + 1) → G) (Φ : (Fin (n + 1) → G) → ℂ)
    (hΦm : Measurable Φ) (hΦb : ∃ C, ∀ x, ‖Φ x‖ ≤ C)
    (w₁ : G → ℝ) (hw₁m : Measurable w₁) (hw₁i : Integrable w₁ μ)
    (β : (Fin n → G) → ℝ) (hβm : Measurable β) (hβi : Integrable β (Measure.pi fun _ => μ))
    (hβ1 : ∀ c h, Φ (Fin.snoc c h) ≠ 0 → β c = 1) :
    ∫ x : Fin (n + 1) → G, Φ (twc δ x) * ((w₁ (x 0) * β (cc δ x) : ℝ) : ℂ) ∂(Measure.pi fun _ => μ) =
      ∫ g : G, fib μ Φ (g⁻¹ * nrm δ * g) * (w₁ g : ℂ) ∂μ := by

  set F : G × (Fin n → G) → ℂ := fun p =>
    Φ (Fin.snoc p.2 (((List.ofFn p.2).prod)⁻¹ * (p.1⁻¹ * nrm δ * p.1))) * ((w₁ p.1 * β p.2 : ℝ) : ℂ)
    with hF
  have hFm : Measurable F := by
    have hk : Measurable fun p : G × (Fin n → G) =>
        (Fin.snoc p.2 (((List.ofFn p.2).prod)⁻¹ * (p.1⁻¹ * nrm δ * p.1)) : Fin (n + 1) → G) := by
      refine measurable_pi_iff.2 fun j => ?_
      induction j using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last]
        exact ((measurable_ofFn_prod n).comp measurable_snd).inv.mul
          ((measurable_fst.inv.mul_const _).mul measurable_fst)
      | cast i =>
        simp only [Fin.snoc_castSucc]
        exact (measurable_pi_apply i).comp measurable_snd
    exact (hΦm.comp hk).mul
      (Complex.measurable_ofReal.comp ((hw₁m.comp measurable_fst).mul (hβm.comp measurable_snd)))

  have hΘ : MeasurePreserving (fun x : Fin (n + 1) → G => (x 0, cc δ x)) (Measure.pi fun _ => μ)
      (μ.prod (Measure.pi fun _ => μ)) := by
    have he : MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => G) 0)
        (Measure.pi fun _ => μ) (μ.prod (Measure.pi fun _ => μ)) :=
      measurePreserving_piFinSuccAbove (fun _ => μ) 0
    have hS : MeasurePreserving (fun p : G × (Fin n → G) => (p.1, cc δ (Fin.cons p.1 p.2)))
        (μ.prod (Measure.pi fun _ => μ)) (μ.prod (Measure.pi fun _ => μ)) :=
      (MeasurePreserving.id μ).skew_product (measurable_cc_cons δ)
        (Filter.Eventually.of_forall fun a => (measurePreserving_cc_cons μ n δ a).map_eq)
    have hfun : (fun x : Fin (n + 1) → G => (x 0, cc δ x)) =
        (fun p : G × (Fin n → G) => (p.1, cc δ (Fin.cons p.1 p.2))) ∘
          MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => G) 0 := by
      funext x
      simp only [Function.comp_apply, MeasurableEquiv.piFinSuccAbove_apply,
        Fin.insertNthEquiv_symm_apply, Fin.removeNth_zero, Fin.cons_self_tail]
    rw [hfun]
    exact hS.comp he

  have hFi : Integrable F (μ.prod (Measure.pi fun _ => μ)) := by
    refine Integrable.mono' ((hw₁i.mul_prod hβi).norm.const_mul hΦb.choose)
      hFm.aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
    simp only [hF, norm_mul, Complex.norm_real]
    exact mul_le_mul_of_nonneg_right (hΦb.choose_spec _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))

  have hinner : ∀ (g : G) (c : Fin n → G),
      F (g, c) = Φ (Fin.snoc c (((List.ofFn c).prod)⁻¹ * (g⁻¹ * nrm δ * g))) * (w₁ g : ℂ) := by
    intro g c
    simp only [hF]
    by_cases hc : Φ (Fin.snoc c (((List.ofFn c).prod)⁻¹ * (g⁻¹ * nrm δ * g))) = 0
    · rw [hc, zero_mul, zero_mul]
    · rw [hβ1 _ _ hc, mul_one]

  have hLHS : (fun x : Fin (n + 1) → G => Φ (twc δ x) * ((w₁ (x 0) * β (cc δ x) : ℝ) : ℂ)) =
      fun x => F (x 0, cc δ x) := by
    funext x
    simp only [hF, twc_eq_snoc]
  calc ∫ x : Fin (n + 1) → G, Φ (twc δ x) * ((w₁ (x 0) * β (cc δ x) : ℝ) : ℂ)
          ∂(Measure.pi fun _ => μ)
      = ∫ x : Fin (n + 1) → G, F (x 0, cc δ x) ∂(Measure.pi fun _ => μ) := by rw [hLHS]
    _ = ∫ p, F p ∂(μ.prod (Measure.pi fun _ => μ)) := by
        rw [← hΘ.map_eq, integral_map hΘ.measurable.aemeasurable hFm.aestronglyMeasurable]
    _ = ∫ g : G, ∫ c : Fin n → G, F (g, c) ∂(Measure.pi fun _ => μ) ∂μ := integral_prod F hFi
    _ = ∫ g : G, fib μ Φ (g⁻¹ * nrm δ * g) * (w₁ g : ℂ) ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        simp only [hinner]
        exact integral_mul_const (w₁ g : ℂ) fun c : Fin n → G =>
          Φ (Fin.snoc c (((List.ofFn c).prod)⁻¹ * (g⁻¹ * nrm δ * g)))

omit [MeasurableInv G] [SigmaFinite μ] [μ.IsMulLeftInvariant] in

private theorem integral_twCent_eq_one {n : ℕ} (δ : Fin (n + 1) → G) (Φ : (Fin (n + 1) → G) → ℂ)
    (y₀ γ : G) (hγ : γ = y₀⁻¹ * nrm δ * y₀)
    [MeasurableSpace (twCent δ)] (τ' : Measure (twCent δ))
    (hmeas : Measurable fun t : twCent δ => y₀⁻¹ * (t : Fin (n + 1) → G) 0 * y₀)
    [MeasurableSpace (Subgroup.centralizer ({γ} : Set G))]
    (τ : Measure (Subgroup.centralizer ({γ} : Set G)))
    (hval : Measurable fun s : Subgroup.centralizer ({γ} : Set G) => (s : G))
    (hτ : Measure.map (fun t : twCent δ => y₀⁻¹ * (t : Fin (n + 1) → G) 0 * y₀) τ' =
      Measure.map (fun s : Subgroup.centralizer ({γ} : Set G) => (s : G)) τ)
    (w₁ : G → ℝ) (hw₁m : Measurable w₁)
    (hsec : ∀ h, fib μ (fun y => (‖Φ y‖ : ℂ)) (h⁻¹ * γ * h) ≠ 0 →
      ∫ s : Subgroup.centralizer ({γ} : Set G), w₁ ((s : G) * h) ∂τ = 1)
    (β : (Fin n → G) → ℝ) (hβ1 : ∀ c h, Φ (Fin.snoc c h) ≠ 0 → β c = 1)
    (x : Fin (n + 1) → G) (hx : Φ (twc δ x) ≠ 0)
    (hx₁ : fib μ (fun y => (‖Φ y‖ : ℂ)) ((x 0)⁻¹ * nrm δ * x 0) ≠ 0) :
    ∫ t : twCent δ, (w₁ (y₀⁻¹ * ((t : Fin (n + 1) → G) * x) 0) *
      β (cc δ ((t : Fin (n + 1) → G) * x)) : ℝ) ∂τ' = 1 := by
  have hβx : β (cc δ x) = 1 := by
    apply hβ1 (cc δ x) (((List.ofFn (cc δ x)).prod)⁻¹ * ((x 0)⁻¹ * nrm δ * x 0))
    rw [← twc_eq_snoc]
    exact hx
  have hint : ∀ t : twCent δ,
      (w₁ (y₀⁻¹ * ((t : Fin (n + 1) → G) * x) 0) * β (cc δ ((t : Fin (n + 1) → G) * x)) : ℝ) =
        w₁ ((y₀⁻¹ * (t : Fin (n + 1) → G) 0 * y₀) * (y₀⁻¹ * x 0)) := by
    intro t
    rw [cc_mul_of_mem_twCent δ (t : Fin (n + 1) → G) t.2 x, hβx, mul_one, Pi.mul_apply]
    simp only [mul_assoc, mul_inv_cancel_left]
  have hF : StronglyMeasurable fun u : G => w₁ (u * (y₀⁻¹ * x 0)) :=
    (hw₁m.comp (measurable_mul_const _)).stronglyMeasurable
  have hconj : (y₀⁻¹ * x 0)⁻¹ * γ * (y₀⁻¹ * x 0) = (x 0)⁻¹ * nrm δ * x 0 := by
    subst hγ
    simp only [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left]
  have h1 := hsec (y₀⁻¹ * x 0) (by rw [hconj]; exact hx₁)
  simp only [hint]
  rw [← integral_map_of_stronglyMeasurable hmeas hF, hτ, integral_map_of_stronglyMeasurable hval hF]
  exact h1

omit [MeasurableMul₂ G] [MeasurableInv G] [SigmaFinite μ] [μ.IsMulLeftInvariant] in

private theorem fib_norm_ne_zero_of_ne_zero {n : ℕ} (Φ : (Fin (n + 1) → G) → ℂ) (h : G)
    (hf : fib μ Φ h ≠ 0) : fib μ (fun y => (‖Φ y‖ : ℂ)) h ≠ 0 := by
  intro h0
  apply hf
  simp only [fib] at h0 ⊢
  rw [integral_complex_ofReal, Complex.ofReal_eq_zero] at h0
  exact norm_eq_zero.mp
    (le_antisymm ((norm_integral_le_integral_norm _).trans h0.le) (norm_nonneg _))

omit [μ.IsMulLeftInvariant] in
private theorem measurable_fib {n : ℕ} (Φ : (Fin (n + 1) → G) → ℂ) (hΦm : Measurable Φ) :
    Measurable (fib μ Φ) := by
  have hk : Measurable fun p : G × (Fin n → G) =>
      (Fin.snoc p.2 (((List.ofFn p.2).prod)⁻¹ * p.1) : Fin (n + 1) → G) := by
    refine measurable_pi_iff.2 fun j => ?_
    induction j using Fin.lastCases with
    | last =>
      simp only [Fin.snoc_last]
      exact ((measurable_ofFn_prod n).comp measurable_snd).inv.mul measurable_fst
    | cast i =>
      simp only [Fin.snoc_castSucc]
      exact (measurable_pi_apply i).comp measurable_snd
  exact ((hΦm.comp hk).stronglyMeasurable.integral_prod_right'
    (ν := Measure.pi fun _ : Fin n => μ)).measurable

private theorem ae_fib_norm_ne_zero_of_ne_zero {n : ℕ} (δ : Fin (n + 1) → G) (Φ : (Fin (n + 1) → G) → ℂ)
    (hΦm : Measurable Φ) (hΦb : ∃ C, ∀ x, ‖Φ x‖ ≤ C)
    (β : (Fin n → G) → ℝ) (hβi : Integrable β (Measure.pi fun _ => μ))
    (hβ1 : ∀ c h, Φ (Fin.snoc c h) ≠ 0 → β c = 1) :
    ∀ᵐ x ∂(Measure.pi fun _ : Fin (n + 1) => μ),
      Φ (twc δ x) ≠ 0 → fib μ (fun y => (‖Φ y‖ : ℂ)) ((x 0)⁻¹ * nrm δ * x 0) ≠ 0 := by
  obtain ⟨C, hC⟩ := hΦb
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 1)

  set k : G → (Fin n → G) → ℂ :=
    fun g c => Φ (Fin.snoc c (((List.ofFn c).prod)⁻¹ * (g⁻¹ * nrm δ * g))) with hk_def
  have hkm : ∀ g, Measurable (k g) := by
    intro g
    refine hΦm.comp (measurable_pi_iff.2 fun j => ?_)
    induction j using Fin.lastCases with
    | last =>
      simp only [Fin.snoc_last]
      exact (measurable_ofFn_prod n).inv.mul_const _
    | cast i =>
      simp only [Fin.snoc_castSucc]
      exact measurable_pi_apply i
  have hki : ∀ g, Integrable (fun c => ‖k g c‖) (Measure.pi fun _ => μ) := by
    intro g
    refine Integrable.mono' (hβi.norm.const_mul C) (hkm g).norm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun c => ?_)
    rw [norm_norm]
    by_cases hc : k g c = 0
    · rw [hc, norm_zero]
      exact mul_nonneg hC0 (norm_nonneg _)
    · rw [hβ1 _ _ hc, norm_one, mul_one]
      exact hC _

  have hnull : ∀ g, fib μ (fun y => (‖Φ y‖ : ℂ)) (g⁻¹ * nrm δ * g) = 0 →
      (Measure.pi fun _ : Fin n => μ) {c | k g c ≠ 0} = 0 := by
    intro g hg
    have h0 : ∫ c, ‖k g c‖ ∂(Measure.pi fun _ : Fin n => μ) = 0 := by
      simp only [fib] at hg
      rw [integral_complex_ofReal, Complex.ofReal_eq_zero] at hg
      exact hg
    have hae := (integral_eq_zero_iff_of_nonneg (fun c => norm_nonneg (k g c)) (hki g)).mp h0
    have h' : ∀ᵐ c ∂(Measure.pi fun _ : Fin n => μ), k g c = 0 :=
      hae.mono fun c hc => norm_eq_zero.mp hc
    exact ae_iff.mp h'

  have hS : MeasurableSet {x : Fin (n + 1) → G |
      Φ (twc δ x) ≠ 0 ∧ fib μ (fun y => (‖Φ y‖ : ℂ)) ((x 0)⁻¹ * nrm δ * x 0) = 0} := by
    refine ((hΦm.comp (measurable_twc δ)) (measurableSet_singleton 0)).compl.inter ?_
    exact ((measurable_fib μ _ (hΦm.norm.complex_ofReal)).comp
      (((measurable_pi_apply 0).inv.mul_const _).mul (measurable_pi_apply 0)))
      (measurableSet_singleton 0)
  rw [ae_iff]
  simp only [Classical.not_imp, not_not]
  have he : MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => G) 0)
      (Measure.pi fun _ => μ) (μ.prod (Measure.pi fun _ => μ)) :=
    measurePreserving_piFinSuccAbove (fun _ => μ) 0
  set A : Set (G × (Fin n → G)) := (fun p : G × (Fin n → G) => (Fin.cons p.1 p.2 : Fin (n + 1) → G)) ⁻¹'
    {x : Fin (n + 1) → G |
      Φ (twc δ x) ≠ 0 ∧ fib μ (fun y => (‖Φ y‖ : ℂ)) ((x 0)⁻¹ * nrm δ * x 0) = 0} with hA_def
  have hAm : MeasurableSet A := measurable_cons hS
  have hpre : (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => G) 0) ⁻¹' A =
      {x : Fin (n + 1) → G |
        Φ (twc δ x) ≠ 0 ∧ fib μ (fun y => (‖Φ y‖ : ℂ)) ((x 0)⁻¹ * nrm δ * x 0) = 0} := by
    ext x
    simp only [hA_def, Set.mem_preimage, MeasurableEquiv.piFinSuccAbove_apply,
      Fin.insertNthEquiv_symm_apply, Fin.removeNth_zero, Fin.cons_self_tail]
  rw [← hpre, he.measure_preimage hAm.nullMeasurableSet, Measure.prod_apply hAm]
  have hsec : ∀ g : G, (Measure.pi fun _ : Fin n => μ) (Prod.mk g ⁻¹' A) = 0 := by
    intro g
    by_cases hg : fib μ (fun y => (‖Φ y‖ : ℂ)) (g⁻¹ * nrm δ * g) = 0
    · refine measure_mono_null (fun y hy => ?_)
        ((measurePreserving_cc_cons μ n δ g).measure_preimage
          ((hkm g) (measurableSet_singleton 0)).compl.nullMeasurableSet |>.trans (hnull g hg))
      simp only [hA_def, Set.mem_preimage, Set.mem_setOf_eq, Fin.cons_zero] at hy
      simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff]
      have hy' := hy.1
      rw [twc_eq_snoc] at hy'
      simpa only [Fin.cons_zero, hk_def] using hy'
    · have : Prod.mk g ⁻¹' A = ∅ := by
        ext y
        simp only [hA_def, Set.mem_preimage, Set.mem_setOf_eq, Fin.cons_zero, Set.mem_empty_iff_false,
          iff_false, not_and]
        exact fun _ => hg
      rw [this, measure_empty]
  simp only [hsec, lintegral_zero]

end Measure

section Uniq

variable {H : Type} [Group H] [MeasurableSpace H]

private def UniqAt (ν : Measure H) (T : Subgroup H) [MeasurableSpace T] (τ : Measure T) : Prop :=
  ∀ F : H → ℂ, Measurable F → (∀ (t : T) (x : H), F ((t : H) * x) = F x) →
    ∀ w w' : H → ℝ, (∀ x, 0 ≤ w x) → (∀ x, 0 ≤ w' x) → Measurable w → Measurable w' →
      (∀ x, F x ≠ 0 → ∫ t : T, w ((t : H) * x) ∂τ = 1) →
      (∀ x, F x ≠ 0 → ∫ t : T, w' ((t : H) * x) ∂τ = 1) →
      ∫ x, F x * (w x : ℂ) ∂ν = ∫ x, F x * (w' x : ℂ) ∂ν

end Uniq

section Assembly

variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
  (μ : Measure G) [SigmaFinite μ] [μ.IsMulLeftInvariant]

private theorem integral_twc_mul_eq_integral_fib_mul_of_uniqAt {n : ℕ} (δ : Fin (n + 1) → G)
    (Φ : (Fin (n + 1) → G) → ℂ) (hΦm : Measurable Φ) (hΦb : ∃ C, ∀ x, ‖Φ x‖ ≤ C)
    (y₀ γ : G) (hγ : γ = y₀⁻¹ * nrm δ * y₀)
    [MeasurableSpace (twCent δ)] (τ' : Measure (twCent δ))
    (hmeas : Measurable fun t : twCent δ => y₀⁻¹ * (t : Fin (n + 1) → G) 0 * y₀)
    [MeasurableSpace (Subgroup.centralizer ({γ} : Set G))]
    (τ : Measure (Subgroup.centralizer ({γ} : Set G)))
    (hval : Measurable fun s : Subgroup.centralizer ({γ} : Set G) => (s : G))
    (hτ : Measure.map (fun t : twCent δ => y₀⁻¹ * (t : Fin (n + 1) → G) 0 * y₀) τ' =
      Measure.map (fun s : Subgroup.centralizer ({γ} : Set G) => (s : G)) τ)
    (huniqT : UniqAt (Measure.pi fun _ : Fin (n + 1) => μ) (twCent δ) τ')
    (huniqG : UniqAt μ (Subgroup.centralizer ({γ} : Set G)) τ)
    (W₀ : (Fin (n + 1) → G) → ℝ) (hW₀ : ∀ x, 0 ≤ W₀ x) (hW₀m : Measurable W₀)
    (hW₀1 : ∀ x, Φ (twc δ x) ≠ 0 → ∫ t : twCent δ, W₀ ((t : Fin (n + 1) → G) * x) ∂τ' = 1)
    (w₀ : G → ℝ) (hw₀ : ∀ h, 0 ≤ w₀ h) (hw₀m : Measurable w₀)
    (hw₀1 : ∀ h, fib μ Φ (h⁻¹ * γ * h) ≠ 0 →
      ∫ s : Subgroup.centralizer ({γ} : Set G), w₀ ((s : G) * h) ∂τ = 1)
    (w₁ : G → ℝ) (hw₁ : ∀ h, 0 ≤ w₁ h) (hw₁m : Measurable w₁) (hw₁i : Integrable w₁ μ)
    (hw₁sec : ∀ h, fib μ (fun y => (‖Φ y‖ : ℂ)) (h⁻¹ * γ * h) ≠ 0 →
      ∫ s : Subgroup.centralizer ({γ} : Set G), w₁ ((s : G) * h) ∂τ = 1)
    (β : (Fin n → G) → ℝ) (hβ : ∀ c, 0 ≤ β c) (hβm : Measurable β)
    (hβi : Integrable β (Measure.pi fun _ => μ)) (hβ1 : ∀ c h, Φ (Fin.snoc c h) ≠ 0 → β c = 1) :
    ∫ x : Fin (n + 1) → G, Φ (twc δ x) * (W₀ x : ℂ) ∂(Measure.pi fun _ => μ) =
      ∫ h : G, fib μ Φ (h⁻¹ * γ * h) * (w₀ h : ℂ) ∂μ := by

  set P : Set (Fin (n + 1) → G) :=
    {x | fib μ (fun y => (‖Φ y‖ : ℂ)) ((x 0)⁻¹ * nrm δ * x 0) ≠ 0} with hP_def
  have hPm : MeasurableSet P :=
    (((measurable_fib μ _ hΦm.norm.complex_ofReal).comp
      (((measurable_pi_apply 0).inv.mul_const _).mul (measurable_pi_apply 0)))
      (measurableSet_singleton 0)).compl
  have hPT : ∀ (t : twCent δ) (x : Fin (n + 1) → G), ((t : Fin (n + 1) → G) * x) ∈ P ↔ x ∈ P := by
    intro t x
    have ht : (t : Fin (n + 1) → G) 0 * nrm δ = nrm δ * (t : Fin (n + 1) → G) 0 :=
      Subgroup.mem_centralizer_singleton_iff.mp (twCent_zero_mem_centralizer δ t t.2)
    simp only [hP_def, Set.mem_setOf_eq, Pi.mul_apply, mul_inv_rev, mul_assoc]
    rw [← mul_assoc (nrm δ), ← ht, mul_assoc, inv_mul_cancel_left]
  set F' : (Fin (n + 1) → G) → ℂ := P.indicator fun x => Φ (twc δ x) with hF'_def
  have hF'm : Measurable F' := (hΦm.comp (measurable_twc δ)).indicator hPm
  have hF'T : ∀ (t : twCent δ) (x : Fin (n + 1) → G), F' ((t : Fin (n + 1) → G) * x) = F' x := by
    intro t x
    by_cases hxP : x ∈ P
    · rw [hF'_def, Set.indicator_of_mem ((hPT t x).2 hxP), Set.indicator_of_mem hxP,
        twc_mul_of_mem_twCent δ _ t.2 x]
    · rw [hF'_def, Set.indicator_of_notMem (fun h => hxP ((hPT t x).1 h)),
        Set.indicator_of_notMem hxP]
  have hF'ne : ∀ x, F' x ≠ 0 → Φ (twc δ x) ≠ 0 ∧ x ∈ P := by
    intro x hx
    by_cases hxP : x ∈ P
    · exact ⟨by simpa only [hF'_def, Set.indicator_of_mem hxP] using hx, hxP⟩
    · exact absurd (Set.indicator_of_notMem hxP _) hx
  have hae : ∀ w : (Fin (n + 1) → G) → ℝ,
      ∫ x, Φ (twc δ x) * (w x : ℂ) ∂(Measure.pi fun _ => μ) =
        ∫ x, F' x * (w x : ℂ) ∂(Measure.pi fun _ => μ) := by
    intro w
    refine integral_congr_ae ((ae_fib_norm_ne_zero_of_ne_zero μ δ Φ hΦm hΦb β hβi hβ1).mono
      fun x hx => ?_)
    by_cases hxP : x ∈ P
    · simp only [hF'_def, Set.indicator_of_mem hxP]
    · have hΦx : Φ (twc δ x) = 0 := by
        by_contra hne
        exact hxP (hx hne)
      simp only [hF'_def, Set.indicator_of_notMem hxP, hΦx, zero_mul]

  have h1 : ∫ x, F' x * (W₀ x : ℂ) ∂(Measure.pi fun _ => μ) =
      ∫ x, F' x * ((w₁ (y₀⁻¹ * x 0) * β (cc δ x) : ℝ) : ℂ) ∂(Measure.pi fun _ => μ) :=
    huniqT F' hF'm hF'T W₀ (fun x => w₁ (y₀⁻¹ * x 0) * β (cc δ x)) hW₀
      (fun x => mul_nonneg (hw₁ _) (hβ _)) hW₀m
      ((hw₁m.comp (measurable_const_mul _ |>.comp (measurable_pi_apply 0))).mul
        (hβm.comp (measurable_cc δ)))
      (fun x hx => hW₀1 x (hF'ne x hx).1)
      (fun x hx => integral_twCent_eq_one μ δ Φ y₀ γ hγ τ' hmeas τ hval hτ w₁ hw₁m hw₁sec β hβ1 x
        (hF'ne x hx).1 (hF'ne x hx).2)

  have h2 := integral_twc_mul_eq_integral_fib μ δ Φ hΦm hΦb (fun g => w₁ (y₀⁻¹ * g))
    (hw₁m.comp (measurable_const_mul _)) (hw₁i.comp_mul_left y₀⁻¹) β hβm hβi hβ1

  have h3 : ∫ g : G, fib μ Φ (g⁻¹ * nrm δ * g) * ((w₁ (y₀⁻¹ * g) : ℝ) : ℂ) ∂μ =
      ∫ h : G, fib μ Φ (h⁻¹ * γ * h) * (w₁ h : ℂ) ∂μ := by
    rw [← integral_mul_left_eq_self (fun g => fib μ Φ (g⁻¹ * nrm δ * g) * ((w₁ (y₀⁻¹ * g) : ℝ) : ℂ))
      y₀]
    refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
    subst hγ
    simp only [mul_inv_rev, mul_assoc, inv_mul_cancel_left]

  have hconj : ∀ (s : Subgroup.centralizer ({γ} : Set G)) (h : G),
      ((s : G) * h)⁻¹ * γ * ((s : G) * h) = h⁻¹ * γ * h := by
    intro s h
    have hs : (s : G) * γ = γ * (s : G) := Subgroup.mem_centralizer_singleton_iff.mp s.2
    simp only [mul_inv_rev, mul_assoc]
    rw [← mul_assoc γ, ← hs, mul_assoc, inv_mul_cancel_left]
  have h4 : ∫ h : G, fib μ Φ (h⁻¹ * γ * h) * (w₁ h : ℂ) ∂μ =
      ∫ h : G, fib μ Φ (h⁻¹ * γ * h) * (w₀ h : ℂ) ∂μ :=
    huniqG (fun h => fib μ Φ (h⁻¹ * γ * h))
      ((measurable_fib μ Φ hΦm).comp ((measurable_id.inv.mul_const _).mul measurable_id))
      (fun s h => congrArg (fib μ Φ) (hconj s h)) w₁ w₀ hw₁ hw₀ hw₁m hw₀m
      (fun h hh => hw₁sec h (fib_norm_ne_zero_of_ne_zero μ Φ _ hh)) hw₀1
  calc ∫ x, Φ (twc δ x) * (W₀ x : ℂ) ∂(Measure.pi fun _ => μ)
      = ∫ x, F' x * (W₀ x : ℂ) ∂(Measure.pi fun _ => μ) := hae W₀
    _ = ∫ x, F' x * ((w₁ (y₀⁻¹ * x 0) * β (cc δ x) : ℝ) : ℂ) ∂(Measure.pi fun _ => μ) := h1
    _ = ∫ x, Φ (twc δ x) * ((w₁ (y₀⁻¹ * x 0) * β (cc δ x) : ℝ) : ℂ) ∂(Measure.pi fun _ => μ) :=
        (hae _).symm
    _ = ∫ g : G, fib μ Φ (g⁻¹ * nrm δ * g) * ((w₁ (y₀⁻¹ * g) : ℝ) : ℂ) ∂μ := h2
    _ = ∫ h : G, fib μ Φ (h⁻¹ * γ * h) * (w₁ h : ℂ) ∂μ := h3
    _ = ∫ h : G, fib μ Φ (h⁻¹ * γ * h) * (w₀ h : ℂ) ∂μ := h4

end Assembly

end TwistedShift

theorem solution
    {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [SigmaFinite μ] [μ.IsMulLeftInvariant] {n : ℕ} (δ : Fin (n + 1) → G)
    (twc : (Fin (n + 1) → G) → Fin (n + 1) → G)
    (htwc : ∀ x j, twc x j = (x j)⁻¹ * δ j * x (j + 1))
    (T : Subgroup (Fin (n + 1) → G)) (hT : ∀ t, t ∈ T ↔ ∀ j, (t j)⁻¹ * δ j * t (j + 1) = δ j)
    (y₀ γ : G) (hγ : γ = y₀⁻¹ * (List.ofFn δ).prod * y₀)
    (Φ : (Fin (n + 1) → G) → ℂ) (hΦm : Measurable Φ) (hΦb : ∃ C, ∀ x, ‖Φ x‖ ≤ C)
    (f f₁ : G → ℂ)
    (hf : ∀ h, f h =
      ∫ c : Fin n → G, Φ (Fin.snoc c (((List.ofFn c).prod)⁻¹ * h)) ∂(Measure.pi fun _ => μ))
    (hf₁ : ∀ h, f₁ h =
      ∫ c : Fin n → G, (‖Φ (Fin.snoc c (((List.ofFn c).prod)⁻¹ * h))‖ : ℂ) ∂(Measure.pi fun _ => μ))
    [MeasurableSpace T] (τ' : Measure T)
    (hmeas : Measurable fun t : T => y₀⁻¹ * (t : Fin (n + 1) → G) 0 * y₀)
    [MeasurableSpace (Subgroup.centralizer ({γ} : Set G))]
    (τ : Measure (Subgroup.centralizer ({γ} : Set G)))
    (hval : Measurable fun s : Subgroup.centralizer ({γ} : Set G) => (s : G))
    (hτ : Measure.map (fun t : T => y₀⁻¹ * (t : Fin (n + 1) → G) 0 * y₀) τ' =
      Measure.map (fun s : Subgroup.centralizer ({γ} : Set G) => (s : G)) τ)
    (huniqT : ∀ F : (Fin (n + 1) → G) → ℂ, Measurable F →
      (∀ (t : T) (x : Fin (n + 1) → G), F ((t : Fin (n + 1) → G) * x) = F x) →
      ∀ w w' : (Fin (n + 1) → G) → ℝ, (∀ x, 0 ≤ w x) → (∀ x, 0 ≤ w' x) →
        Measurable w → Measurable w' →
        (∀ x, F x ≠ 0 → ∫ t : T, w ((t : Fin (n + 1) → G) * x) ∂τ' = 1) →
        (∀ x, F x ≠ 0 → ∫ t : T, w' ((t : Fin (n + 1) → G) * x) ∂τ' = 1) →
        ∫ x, F x * (w x : ℂ) ∂(Measure.pi fun _ : Fin (n + 1) => μ) =
          ∫ x, F x * (w' x : ℂ) ∂(Measure.pi fun _ : Fin (n + 1) => μ))
    (huniqG : ∀ F : G → ℂ, Measurable F →
      (∀ (s : Subgroup.centralizer ({γ} : Set G)) (h : G), F ((s : G) * h) = F h) →
      ∀ w w' : G → ℝ, (∀ h, 0 ≤ w h) → (∀ h, 0 ≤ w' h) → Measurable w → Measurable w' →
        (∀ h, F h ≠ 0 → ∫ s : Subgroup.centralizer ({γ} : Set G), w ((s : G) * h) ∂τ = 1) →
        (∀ h, F h ≠ 0 → ∫ s : Subgroup.centralizer ({γ} : Set G), w' ((s : G) * h) ∂τ = 1) →
        ∫ h, F h * (w h : ℂ) ∂μ = ∫ h, F h * (w' h : ℂ) ∂μ)
    (W₀ : (Fin (n + 1) → G) → ℝ) (hW₀ : ∀ x, 0 ≤ W₀ x) (hW₀m : Measurable W₀)
    (hW₀1 : ∀ x, Φ (twc x) ≠ 0 → ∫ t : T, W₀ ((t : Fin (n + 1) → G) * x) ∂τ' = 1)
    (w₀ : G → ℝ) (hw₀ : ∀ h, 0 ≤ w₀ h) (hw₀m : Measurable w₀)
    (hw₀1 : ∀ h, f (h⁻¹ * γ * h) ≠ 0 →
      ∫ s : Subgroup.centralizer ({γ} : Set G), w₀ ((s : G) * h) ∂τ = 1)
    (hw₁ : ∃ w₁ : G → ℝ, (∀ h, 0 ≤ w₁ h) ∧ Measurable w₁ ∧ Integrable w₁ μ ∧
      ∀ h, f₁ (h⁻¹ * γ * h) ≠ 0 →
        ∫ s : Subgroup.centralizer ({γ} : Set G), w₁ ((s : G) * h) ∂τ = 1)
    (hβ : ∃ β : (Fin n → G) → ℝ, (∀ c, 0 ≤ β c) ∧ Measurable β ∧
      Integrable β (Measure.pi fun _ => μ) ∧ ∀ c h, Φ (Fin.snoc c h) ≠ 0 → β c = 1) :
    ∫ x, Φ (twc x) * (W₀ x : ℂ) ∂(Measure.pi fun _ : Fin (n + 1) => μ) =
      ∫ h, f (h⁻¹ * γ * h) * (w₀ h : ℂ) ∂μ := by
  obtain rfl : twc = TwistedShift.twc δ := funext fun x => funext fun j => htwc x j
  obtain rfl : T = TwistedShift.twCent δ := Subgroup.ext fun t => hT t
  obtain rfl : f = TwistedShift.fib μ Φ := funext fun h => hf h
  obtain rfl : f₁ = TwistedShift.fib μ (fun y => (‖Φ y‖ : ℂ)) := funext fun h => hf₁ h
  obtain ⟨w₁, hw₁, hw₁m, hw₁i, hw₁sec⟩ := hw₁
  obtain ⟨β, hβ, hβm, hβi, hβ1⟩ := hβ
  exact TwistedShift.integral_twc_mul_eq_integral_fib_mul_of_uniqAt μ δ Φ hΦm hΦb y₀ γ hγ τ' hmeas τ
    hval hτ huniqT huniqG W₀ hW₀ hW₀m hW₀1 w₀ hw₀ hw₀m hw₀1 w₁ hw₁ hw₁m hw₁i hw₁sec β hβ hβm hβi
    hβ1

end S_AutomorphicForm_integral_twistedConj_mul_eq_integral_conj_fibreIntegral_mul
end P2MW
export P2MW.S_AutomorphicForm_integral_twistedConj_mul_eq_integral_conj_fibreIntegral_mul (solution)
