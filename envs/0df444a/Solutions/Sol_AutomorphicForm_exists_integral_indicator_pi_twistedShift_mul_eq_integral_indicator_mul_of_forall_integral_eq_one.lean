-- Prove2me | solution 1 for AutomorphicForm.exists_integral_indicator_pi_twistedShift_mul_eq_integral_indicator_mul_of_forall_integral_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/927a36b0-74df-501f-b969-0a28844ce7ff

import Mathlib
import Definitions.Def_AutomorphicForm_SigmaCentralizer
import Theorems.Thm_AutomorphicForm_exists_continuousMulEquiv_sigmaCentralizer_homeomorph_measurePreserving_twistedShift
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_integral_indicator_pi_twistedShift_mul_eq_integral_indicator_mul_of_forall_integral_eq_one

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory MeasureTheory.Measure TopologicalSpace Function
open scoped ENNReal

noncomputable section

namespace P2mTwistedShiftUnit

open AutomorphicForm

section Algebra

variable {G : Type} [Group G]

def rho (θ : G →* G) (m : ℕ) : (Fin (m + 1) → G) →* (Fin (m + 1) → G) :=
  MonoidHom.pi fun j : Fin (m + 1) =>
    Fin.lastCases (motive := fun _ => (Fin (m + 1) → G) →* G)
      (θ.comp (Pi.evalMonoidHom (fun _ : Fin (m + 1) => G) 0))
      (fun k : Fin m => Pi.evalMonoidHom (fun _ : Fin (m + 1) => G) k.succ) j

def listProd {n : ℕ} (g : Fin n → G) : G := (List.ofFn g).prod

def string {n : ℕ} (g : Fin n → G) (h : G) : Fin (n + 1) → G :=
  Fin.snoc g ((listProd g)⁻¹ * h)

@[scoped simp] theorem string_castSucc {n : ℕ} (g : Fin n → G) (h : G) (k : Fin n) :
    string g h (Fin.castSucc k) = g k := by
  simp [string]

@[scoped simp] theorem string_last {n : ℕ} (g : Fin n → G) (h : G) :
    string g h (Fin.last n) = (listProd g)⁻¹ * h := by
  simp [string]

theorem listProd_zero (g : Fin 0 → G) : listProd g = 1 := by
  simp [listProd]

theorem listProd_succ {n : ℕ} (g : Fin (n + 1) → G) :
    listProd g = listProd (fun k : Fin n => g (Fin.castSucc k)) * g (Fin.last n) := by
  unfold listProd
  rw [List.ofFn_succ', List.prod_concat]

theorem listProd_mem (U : Subgroup G) : ∀ {n : ℕ} (g : Fin n → G), (∀ k, g k ∈ U) → listProd g ∈ U
  | 0, g, _ => by rw [listProd_zero]; exact U.one_mem
  | n + 1, g, hg => by
      rw [listProd_succ]
      exact U.mul_mem (listProd_mem U _ fun k => hg _) (hg _)

theorem string_mem_pi_iff (U : Subgroup G) {n : ℕ} (g : Fin n → G) (h : G) :
    string g h ∈ Set.univ.pi (fun _ : Fin (n + 1) => (U : Set G)) ↔
      g ∈ Set.univ.pi (fun _ : Fin n => (U : Set G)) ∧ h ∈ U := by
  simp only [Set.mem_univ_pi, SetLike.mem_coe]
  rw [Fin.forall_fin_succ']
  simp only [string_castSucc, string_last]
  constructor
  · rintro ⟨hg, hl⟩
    refine ⟨hg, ?_⟩
    have hp : listProd g ∈ U := listProd_mem U g hg
    have := U.mul_mem hp hl
    rwa [mul_inv_cancel_left] at this
  · rintro ⟨hg, hh⟩
    exact ⟨hg, U.mul_mem (U.inv_mem (listProd_mem U g hg)) hh⟩

theorem continuous_listProd [TopologicalSpace G] [IsTopologicalGroup G] :
    ∀ {n : ℕ}, Continuous (listProd : (Fin n → G) → G)
  | 0 => by
      have h : (listProd : (Fin 0 → G) → G) = fun _ => 1 := funext listProd_zero
      rw [h]; exact continuous_const
  | n + 1 => by
      have h : (listProd : (Fin (n + 1) → G) → G) =
          fun g => listProd (fun k : Fin n => g (Fin.castSucc k)) * g (Fin.last n) := funext listProd_succ
      rw [h]
      exact (continuous_listProd.comp (continuous_pi fun k => continuous_apply _)).mul (continuous_apply _)

theorem continuous_string₂ [TopologicalSpace G] [IsTopologicalGroup G] {n : ℕ} :
    Continuous fun p : (Fin n → G) × G => string p.1 p.2 := by
  refine continuous_pi fun j => ?_
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp only [string_last]
    exact (continuous_listProd.comp continuous_fst).inv.mul continuous_snd
  · simp only [string_castSucc]
    exact (continuous_apply k).comp continuous_fst

theorem inv_mul_mul_apply_of_mem {θ : G →* G} {ν t : G} (ht : t ∈ sigmaCentralizer θ ν) (x₀ : G) :
    (t * x₀)⁻¹ * ν * θ (t * x₀) = x₀⁻¹ * ν * θ x₀ := by
  rw [mem_sigmaCentralizer_iff_inv] at ht
  rw [mul_inv_rev, map_mul]
  calc x₀⁻¹ * t⁻¹ * ν * (θ t * θ x₀) = x₀⁻¹ * (t⁻¹ * ν * θ t) * θ x₀ := by group
    _ = x₀⁻¹ * ν * θ x₀ := by rw [ht]

end Algebra

section Straighten

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem straighten (θ : G →* G) {m : ℕ} (δ : Fin (m + 1) → G)
    (μ : Measure G) [SigmaFinite μ] [μ.IsMulLeftInvariant] :
    ∃ (e : sigmaCentralizer (rho θ m) δ ≃ₜ* sigmaCentralizer θ (listProd δ))
      (X : G × (Fin m → G) ≃ₜ (Fin (m + 1) → G)),
      (∀ t, ((e t : sigmaCentralizer θ (listProd δ)) : G) = (t : Fin (m + 1) → G) 0) ∧
      MeasurePreserving X (μ.prod (Measure.pi fun _ => μ)) (Measure.pi fun _ => μ) ∧
      (∀ p : G × (Fin m → G), X p 0 = p.1) ∧
      (∀ p : G × (Fin m → G),
        (X p)⁻¹ * δ * rho θ m (X p) = string p.2 (p.1⁻¹ * listProd δ * θ p.1)) ∧
      (∀ (t : sigmaCentralizer (rho θ m) δ) (p : G × (Fin m → G)),
        (t : Fin (m + 1) → G) * X p = X (((e t : sigmaCentralizer θ (listProd δ)) : G) * p.1, p.2)) :=
  AutomorphicForm.exists_continuousMulEquiv_sigmaCentralizer_homeomorph_measurePreserving_twistedShift θ δ μ

end Straighten

section Descent

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (θ : G →* G) (hθ : Continuous θ) {m : ℕ} (δ : Fin (m + 1) → G)
  (μ : Measure G) [μ.IsHaarMeasure]
  (U : Subgroup G) (hU : IsOpen (U : Set G)) (hμU : μ U = 1)

theorem lintegral_eq_one_of_integral_eq_one {α : Type*} [MeasurableSpace α] {κ : Measure α}
    {f : α → ℝ} (hf0 : ∀ a, 0 ≤ f a) (hf : ∫ a, f a ∂κ = 1) :
    ∫⁻ a, ENNReal.ofReal (f a) ∂κ = 1 := by
  have hint : Integrable f κ := by
    by_contra h
    rw [integral_undef h] at hf
    exact zero_ne_one hf
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hf0), hf, ENNReal.ofReal_one]

theorem indicator_pi_nonneg {n : ℕ} (y : Fin n → G) :
    0 ≤ (Set.univ.pi fun _ : Fin n => (U : Set G)).indicator (fun _ => (1 : ℝ)) y :=
  Set.indicator_nonneg (fun _ _ => zero_le_one) y

theorem indicator_pi_le_one {n : ℕ} (y : Fin n → G) :
    (Set.univ.pi fun _ : Fin n => (U : Set G)).indicator (fun _ => (1 : ℝ)) y ≤ 1 :=
  Set.indicator_le_self' (fun _ _ => zero_le_one) y

include hU in
theorem measurableSet_pi {n : ℕ} : MeasurableSet (Set.univ.pi fun _ : Fin n => (U : Set G)) :=
  (isOpen_set_pi Set.finite_univ fun _ _ => hU).measurableSet

include hθ hU hμU in

theorem descent
    (τ : Measure (sigmaCentralizer (rho θ m) δ)) (hτ : SFinite τ)
    (w : (Fin (m + 1) → G) → ℝ) (hw0 : ∀ x, 0 ≤ w x) (hwm : Measurable w) (hwc : HasCompactSupport w)
    (hsec : ∀ x : Fin (m + 1) → G,
      x⁻¹ * δ * rho θ m x ∈ Set.univ.pi (fun _ : Fin (m + 1) => (U : Set G)) →
        ∫ t : sigmaCentralizer (rho θ m) δ, w ((t : Fin (m + 1) → G) * x) ∂τ = 1) :
    ∃ (e : sigmaCentralizer (rho θ m) δ ≃ₜ* sigmaCentralizer θ (listProd δ)) (s : G → ℝ),
      (∀ t, ((e t : sigmaCentralizer θ (listProd δ)) : G) = (t : Fin (m + 1) → G) 0) ∧
      (∀ x, 0 ≤ s x) ∧ Measurable s ∧ HasCompactSupport s ∧
      (∀ x₀ : G, x₀⁻¹ * listProd δ * θ x₀ ∈ U →
        ∫ t : sigmaCentralizer θ (listProd δ), s ((t : G) * x₀) ∂(Measure.map e τ) = 1) ∧
      (Integrable (fun x : Fin (m + 1) → G =>
          (Set.univ.pi fun _ : Fin (m + 1) => (U : Set G)).indicator (fun _ => (1 : ℂ))
            (x⁻¹ * δ * rho θ m x) * (w x : ℂ)) (Measure.pi fun _ => μ) →
        ∫ x : Fin (m + 1) → G,
            (Set.univ.pi fun _ : Fin (m + 1) => (U : Set G)).indicator (fun _ => (1 : ℂ))
              (x⁻¹ * δ * rho θ m x) * (w x : ℂ) ∂(Measure.pi fun _ => μ) =
          ∫ x₀ : G, (U : Set G).indicator (fun _ => (1 : ℂ)) (x₀⁻¹ * listProd δ * θ x₀) * (s x₀ : ℂ) ∂μ) := by
  haveI := hτ
  obtain ⟨e, X, he, hXmp, hX0, hXconj, hXact⟩ := straighten θ δ μ

  set S : Set (Fin (m + 1) → G) := Set.univ.pi fun _ : Fin (m + 1) => (U : Set G) with hS
  set Sm : Set (Fin m → G) := Set.univ.pi fun _ : Fin m => (U : Set G) with hSm
  have hSmeas : MeasurableSet S := measurableSet_pi U hU
  have hSmmeas : MeasurableSet Sm := measurableSet_pi U hU
  set F : (Fin (m + 1) → G) → ℝ := S.indicator fun _ => (1 : ℝ) with hF
  have hF0 : ∀ y, 0 ≤ F y := indicator_pi_nonneg U
  have hF1 : ∀ y, F y ≤ 1 := indicator_pi_le_one U
  have hFm : Measurable F := measurable_const.indicator hSmeas
  have hFℂ : ∀ y, S.indicator (fun _ => (1 : ℂ)) y = (F y : ℂ) := fun y => by
    by_cases hy : y ∈ S
    · rw [Set.indicator_of_mem hy, hF, Set.indicator_of_mem hy]; simp
    · rw [Set.indicator_of_notMem hy, hF, Set.indicator_of_notMem hy]; simp
  set h : G → G := fun x₀ => x₀⁻¹ * listProd δ * θ x₀ with hh
  have hhc : Continuous h := (continuous_id.inv.mul continuous_const).mul hθ

  set W : G × (Fin m → G) → ℝ := fun p => w (X p) with hW
  have hW0 : ∀ p, 0 ≤ W p := fun p => hw0 _
  have hWm : Measurable W := hwm.comp X.measurable
  have hWc : HasCompactSupport W := hwc.comp_homeomorph X
  set g : G × (Fin m → G) → ℝ := fun p => F (string p.2 (h p.1)) * W p with hg
  have hg0 : ∀ p, 0 ≤ g p := fun p => mul_nonneg (hF0 _) (hW0 _)
  have hstrm : Measurable fun p : G × (Fin m → G) => string p.2 (h p.1) :=
    (continuous_string₂.comp (continuous_snd.prodMk (hhc.comp continuous_fst))).measurable
  have hgm : Measurable g := (hFm.comp hstrm).mul hWm
  have hgem : Measurable fun p => ENNReal.ofReal (g p) := ENNReal.measurable_ofReal.comp hgm

  set Λ : G → ℝ≥0∞ := fun x₀ => ∫⁻ u, ENNReal.ofReal (g (x₀, u)) ∂(Measure.pi fun _ => μ) with hΛ
  have hΛm : Measurable Λ := hgem.lintegral_prod_right'
  set s : G → ℝ := fun x₀ => (Λ x₀).toReal with hs
  have hs0 : ∀ x, 0 ≤ s x := fun x => ENNReal.toReal_nonneg
  have hsm : Measurable s := ENNReal.measurable_toReal.comp hΛm

  have hg_zero_of_not_mem : ∀ x₀, h x₀ ∉ U → ∀ u, g (x₀, u) = 0 := by
    intro x₀ hx₀ u
    have : F (string u (h x₀)) = 0 := by
      rw [hF, Set.indicator_of_notMem]
      rw [hS, string_mem_pi_iff]
      exact fun hmem => hx₀ hmem.2
    simp only [hg, this, zero_mul]
  have hΛ_zero_of_not_mem : ∀ x₀, h x₀ ∉ U → Λ x₀ = 0 := by
    intro x₀ hx₀
    simp only [hΛ, hg_zero_of_not_mem x₀ hx₀, ENNReal.ofReal_zero, lintegral_zero]
  have hsc : HasCompactSupport s := by
    have hK : IsCompact (Prod.fst '' tsupport W) := hWc.image continuous_fst
    refine HasCompactSupport.intro hK fun x₀ hx₀ => ?_
    have hWz : ∀ u, W (x₀, u) = 0 := by
      intro u
      by_contra hne
      exact hx₀ ⟨(x₀, u), subset_tsupport _ (Function.mem_support.2 hne), rfl⟩
    have : Λ x₀ = 0 := by
      simp only [hΛ, hg, hWz, mul_zero, ENNReal.ofReal_zero, lintegral_zero]
    simp only [hs, this, ENNReal.toReal_zero]

  have hinner : ∀ (x₀ : G) (u : Fin m → G),
      ∫⁻ t : sigmaCentralizer θ (listProd δ), ENNReal.ofReal (W ((t : G) * x₀, u)) ∂(Measure.map e τ) =
        ∫⁻ t : sigmaCentralizer (rho θ m) δ, ENNReal.ofReal (w ((t : Fin (m + 1) → G) * X (x₀, u))) ∂τ := by
    intro x₀ u
    have h1 : ∫⁻ t : sigmaCentralizer θ (listProd δ), ENNReal.ofReal (W ((t : G) * x₀, u)) ∂(Measure.map e τ) =
        ∫⁻ t : sigmaCentralizer (rho θ m) δ,
          ENNReal.ofReal (W (((e t : sigmaCentralizer θ (listProd δ)) : G) * x₀, u)) ∂τ := by
      have := lintegral_map_equiv (μ := τ) (fun t : sigmaCentralizer θ (listProd δ) => ENNReal.ofReal (W ((t : G) * x₀, u)))
        e.toHomeomorph.toMeasurableEquiv
      rw [Homeomorph.toMeasurableEquiv_coe] at this
      exact this
    rw [h1]
    congr 1
    funext t
    have hx := hXact t (x₀, u)
    dsimp only at hx
    simp only [hW]
    rw [← hx]

  have hfibre : ∀ h₀ : G, h₀ ∈ U →
      ∫⁻ u, ENNReal.ofReal (F (string u h₀)) ∂(Measure.pi fun _ : Fin m => μ) = 1 := by
    intro h₀ hh₀
    have hset : (fun u : Fin m → G => ENNReal.ofReal (F (string u h₀))) = Sm.indicator 1 := by
      funext u
      by_cases hu : u ∈ Sm
      · rw [Set.indicator_of_mem hu, hF, Set.indicator_of_mem ((string_mem_pi_iff U u h₀).2 ⟨hu, hh₀⟩)]
        simp
      · rw [Set.indicator_of_notMem hu, hF, Set.indicator_of_notMem]
        · simp
        · rw [hS, string_mem_pi_iff]; exact fun hmem => hu hmem.1
    rw [hset, lintegral_indicator_one hSmmeas, hSm, Measure.pi_pi]
    simp [hμU]

  have hsection : ∀ x₀ : G, h x₀ ∈ U →
      ∫ t : sigmaCentralizer θ (listProd δ), s ((t : G) * x₀) ∂(Measure.map e τ) = 1 := by
    intro x₀ hx₀

    have hΛt : ∀ t : sigmaCentralizer θ (listProd δ),
        Λ ((t : G) * x₀) = ∫⁻ u, ENNReal.ofReal (F (string u (h x₀))) * ENNReal.ofReal (W ((t : G) * x₀, u))
          ∂(Measure.pi fun _ => μ) := by
      intro t
      simp only [hΛ, hg]
      congr 1
      funext u
      rw [ENNReal.ofReal_mul (hF0 _), hh]
      simp only []
      rw [inv_mul_mul_apply_of_mem t.2 x₀]

    have hswap : ∫⁻ t : sigmaCentralizer θ (listProd δ), Λ ((t : G) * x₀) ∂(Measure.map e τ) =
        ∫⁻ u, ENNReal.ofReal (F (string u (h x₀))) *
          ∫⁻ t : sigmaCentralizer θ (listProd δ), ENNReal.ofReal (W ((t : G) * x₀, u)) ∂(Measure.map e τ)
            ∂(Measure.pi fun _ => μ) := by
      simp_rw [hΛt]
      rw [lintegral_lintegral_swap]
      · congr 1
        funext u
        rw [lintegral_const_mul]
        exact ENNReal.measurable_ofReal.comp
          (hWm.comp ((continuous_subtype_val.mul continuous_const).prodMk continuous_const).measurable)
      · apply Measurable.aemeasurable
        refine Measurable.fun_mul ?_ ?_
        · exact ENNReal.measurable_ofReal.comp
            ((hFm.comp hstrm).comp (measurable_const.prodMk measurable_snd))
        · exact ENNReal.measurable_ofReal.comp
            (hWm.comp (((continuous_subtype_val.comp continuous_fst).mul continuous_const).prodMk
              continuous_snd).measurable)

    have hprod : ∀ u : Fin m → G,
        ENNReal.ofReal (F (string u (h x₀))) *
            ∫⁻ t : sigmaCentralizer θ (listProd δ), ENNReal.ofReal (W ((t : G) * x₀, u)) ∂(Measure.map e τ) =
          ENNReal.ofReal (F (string u (h x₀))) := by
      intro u
      by_cases hu : string u (h x₀) ∈ S
      · rw [hinner]
        have hx : (X (x₀, u))⁻¹ * δ * rho θ m (X (x₀, u)) ∈ S := by
          rw [hXconj (x₀, u)]; exact hu
        rw [lintegral_eq_one_of_integral_eq_one (fun t => hw0 _) (hsec _ hx), mul_one]
      · have : F (string u (h x₀)) = 0 := by rw [hF, Set.indicator_of_notMem hu]
        rw [this, ENNReal.ofReal_zero, zero_mul]
    have htotal : ∫⁻ t : sigmaCentralizer θ (listProd δ), Λ ((t : G) * x₀) ∂(Measure.map e τ) = 1 := by
      rw [hswap]
      simp_rw [hprod]
      exact hfibre (h x₀) hx₀

    have hΛtm : Measurable fun t : sigmaCentralizer θ (listProd δ) => Λ ((t : G) * x₀) :=
      hΛm.comp (continuous_subtype_val.mul continuous_const).measurable
    have hae : ∀ᵐ t : sigmaCentralizer θ (listProd δ) ∂(Measure.map e τ), Λ ((t : G) * x₀) < ∞ :=
      ae_lt_top hΛtm (by rw [htotal]; exact ENNReal.one_ne_top)
    calc ∫ t : sigmaCentralizer θ (listProd δ), s ((t : G) * x₀) ∂(Measure.map e τ)
        = (∫⁻ t : sigmaCentralizer θ (listProd δ), Λ ((t : G) * x₀) ∂(Measure.map e τ)).toReal :=
          integral_toReal hΛtm.aemeasurable hae
      _ = 1 := by rw [htotal, ENNReal.toReal_one]
  refine ⟨e, s, he, hs0, hsm, hsc, hsection, fun hint => ?_⟩

  set Fw : (Fin (m + 1) → G) → ℝ := fun x => F (x⁻¹ * δ * rho θ m x) * w x with hFw
  have hFw0 : ∀ x, 0 ≤ Fw x := fun x => mul_nonneg (hF0 _) (hw0 _)
  have hconjm : Measurable fun x : Fin (m + 1) → G => x⁻¹ * δ * rho θ m x := by
    refine (continuous_pi fun j => ?_).measurable
    refine Fin.lastCases ?_ (fun k => ?_) j
    · simp only [Pi.mul_apply, Pi.inv_apply, rho, MonoidHom.pi_apply, Fin.lastCases_last, MonoidHom.coe_comp,
        Function.comp_apply, Pi.evalMonoidHom_apply]
      exact (((continuous_apply _).inv).mul continuous_const).mul (hθ.comp (continuous_apply 0))
    · simp only [Pi.mul_apply, Pi.inv_apply, rho, MonoidHom.pi_apply, Fin.lastCases_castSucc,
        Pi.evalMonoidHom_apply]
      exact (((continuous_apply _).inv).mul continuous_const).mul (continuous_apply _)
  have hFwm : Measurable Fw := (hFm.comp hconjm).mul hwm
  have hℂ : (fun x : Fin (m + 1) → G => S.indicator (fun _ => (1 : ℂ)) (x⁻¹ * δ * rho θ m x) * (w x : ℂ)) =
      fun x => ((Fw x : ℝ) : ℂ) := by
    funext x
    rw [hFℂ, hFw]
    push_cast
    ring
  have hint' : Integrable Fw (Measure.pi fun _ => μ) := by
    have h0 : Integrable (fun x => ((Fw x : ℝ) : ℂ)) (Measure.pi fun _ => μ) := by rw [← hℂ]; exact hint
    refine h0.norm.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hFw0 x)]

  have hT1 : ∫⁻ x, ENNReal.ofReal (Fw x) ∂(Measure.pi fun _ => μ) = ∫⁻ x₀, Λ x₀ ∂μ := by
    have h1 : ∫⁻ x, ENNReal.ofReal (Fw x) ∂(Measure.pi fun _ => μ) =
        ∫⁻ p, ENNReal.ofReal (Fw (X p)) ∂(μ.prod (Measure.pi fun _ => μ)) := by
      rw [← hXmp.lintegral_comp_emb X.toMeasurableEquiv.measurableEmbedding]
    have h2 : (fun p => ENNReal.ofReal (Fw (X p))) = fun p => ENNReal.ofReal (g p) := by
      funext p
      simp only [hFw, hg, hW, hXconj p, hh]
    rw [h1, h2, lintegral_prod _ hgem.aemeasurable]
  have hfin : ∫⁻ x₀, Λ x₀ ∂μ ≠ ∞ := by
    rw [← hT1]
    exact (hint'.lintegral_lt_top).ne
  have hae : ∀ᵐ x₀ ∂μ, Λ x₀ < ∞ := ae_lt_top hΛm hfin

  have hL : ∫ x, S.indicator (fun _ => (1 : ℂ)) (x⁻¹ * δ * rho θ m x) * (w x : ℂ) ∂(Measure.pi fun _ => μ) =
      (((∫⁻ x₀, Λ x₀ ∂μ).toReal : ℝ) : ℂ) := by
    rw [hℂ, integral_complex_ofReal, ← hT1,
      integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hFw0) hFwm.aestronglyMeasurable]

  have hRfun : (fun x₀ : G => (U : Set G).indicator (fun _ => (1 : ℂ)) (x₀⁻¹ * listProd δ * θ x₀) * (s x₀ : ℂ)) =
      fun x₀ => ((s x₀ : ℝ) : ℂ) := by
    funext x₀
    by_cases hx₀ : h x₀ ∈ U
    · have : x₀⁻¹ * listProd δ * θ x₀ ∈ (U : Set G) := hx₀
      rw [Set.indicator_of_mem this, one_mul]
    · have hz : s x₀ = 0 := by simp only [hs, hΛ_zero_of_not_mem x₀ hx₀, ENNReal.toReal_zero]
      rw [hz]; simp
  have hR : ∫ x₀, (U : Set G).indicator (fun _ => (1 : ℂ)) (x₀⁻¹ * listProd δ * θ x₀) * (s x₀ : ℂ) ∂μ =
      (((∫⁻ x₀, Λ x₀ ∂μ).toReal : ℝ) : ℂ) := by
    rw [hRfun, integral_complex_ofReal]
    congr 1
    exact integral_toReal hΛm.aemeasurable hae
  rw [hL, hR]

end Descent

end P2mTwistedShiftUnit
p2m_reactivate "P2MW.S_AutomorphicForm_exists_integral_indicator_pi_twistedShift_mul_eq_integral_indicator_mul_of_forall_integral_eq_one.P2mTwistedShiftUnit"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_integral_indicator_pi_twistedShift_mul_eq_integral_indicator_mul_of_forall_integral_eq_one.P2mTwistedShiftUnit"

open MeasureTheory in
theorem solution
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (θ : G →* G) (hθ : Continuous θ) {m : ℕ} (δ : Fin (m + 1) → G)
    (μ : Measure G) [μ.IsHaarMeasure]
    (U : Subgroup G) (hU : IsOpen (U : Set G)) (hμU : μ U = 1)
    (τ : Measure (AutomorphicForm.sigmaCentralizer
        (MonoidHom.pi fun j : Fin (m + 1) =>
          Fin.lastCases (motive := fun _ => (Fin (m + 1) → G) →* G)
            (θ.comp (Pi.evalMonoidHom (fun _ : Fin (m + 1) => G) 0))
            (fun k : Fin m => Pi.evalMonoidHom (fun _ : Fin (m + 1) => G) k.succ) j) δ)) [SFinite τ]
    (w : (Fin (m + 1) → G) → ℝ) (hw0 : ∀ x, 0 ≤ w x) (hwm : Measurable w) (hwc : HasCompactSupport w)
    (hsec : ∀ x : Fin (m + 1) → G,
      x⁻¹ * δ *
          (MonoidHom.pi fun j : Fin (m + 1) =>
            Fin.lastCases (motive := fun _ => (Fin (m + 1) → G) →* G)
              (θ.comp (Pi.evalMonoidHom (fun _ : Fin (m + 1) => G) 0))
              (fun k : Fin m => Pi.evalMonoidHom (fun _ : Fin (m + 1) => G) k.succ) j) x ∈
        Set.univ.pi (fun _ : Fin (m + 1) => (U : Set G)) →
      ∫ t : AutomorphicForm.sigmaCentralizer
          (MonoidHom.pi fun j : Fin (m + 1) =>
            Fin.lastCases (motive := fun _ => (Fin (m + 1) → G) →* G)
              (θ.comp (Pi.evalMonoidHom (fun _ : Fin (m + 1) => G) 0))
              (fun k : Fin m => Pi.evalMonoidHom (fun _ : Fin (m + 1) => G) k.succ) j) δ,
        w ((t : Fin (m + 1) → G) * x) ∂τ = 1) :
    ∃ (e : AutomorphicForm.sigmaCentralizer
            (MonoidHom.pi fun j : Fin (m + 1) =>
              Fin.lastCases (motive := fun _ => (Fin (m + 1) → G) →* G)
                (θ.comp (Pi.evalMonoidHom (fun _ : Fin (m + 1) => G) 0))
                (fun k : Fin m => Pi.evalMonoidHom (fun _ : Fin (m + 1) => G) k.succ) j) δ ≃ₜ*
          AutomorphicForm.sigmaCentralizer θ (List.ofFn δ).prod)
      (s : G → ℝ),
      (∀ t, ((e t : AutomorphicForm.sigmaCentralizer θ (List.ofFn δ).prod) : G) = (t : Fin (m + 1) → G) 0) ∧
      (∀ x, 0 ≤ s x) ∧ Measurable s ∧ HasCompactSupport s ∧
      (∀ x₀ : G, x₀⁻¹ * (List.ofFn δ).prod * θ x₀ ∈ U →
        ∫ t : AutomorphicForm.sigmaCentralizer θ (List.ofFn δ).prod, s ((t : G) * x₀) ∂(Measure.map e τ) = 1) ∧
      (Integrable (fun x : Fin (m + 1) → G =>
          (Set.univ.pi fun _ : Fin (m + 1) => (U : Set G)).indicator (fun _ => (1 : ℂ))
            (x⁻¹ * δ *
              (MonoidHom.pi fun j : Fin (m + 1) =>
                Fin.lastCases (motive := fun _ => (Fin (m + 1) → G) →* G)
                  (θ.comp (Pi.evalMonoidHom (fun _ : Fin (m + 1) => G) 0))
                  (fun k : Fin m => Pi.evalMonoidHom (fun _ : Fin (m + 1) => G) k.succ) j) x) *
            (w x : ℂ)) (Measure.pi fun _ => μ) →
        ∫ x : Fin (m + 1) → G,
            (Set.univ.pi fun _ : Fin (m + 1) => (U : Set G)).indicator (fun _ => (1 : ℂ))
              (x⁻¹ * δ *
                (MonoidHom.pi fun j : Fin (m + 1) =>
                  Fin.lastCases (motive := fun _ => (Fin (m + 1) → G) →* G)
                    (θ.comp (Pi.evalMonoidHom (fun _ : Fin (m + 1) => G) 0))
                    (fun k : Fin m => Pi.evalMonoidHom (fun _ : Fin (m + 1) => G) k.succ) j) x) *
              (w x : ℂ) ∂(Measure.pi fun _ => μ) =
          ∫ x₀ : G, (U : Set G).indicator (fun _ => (1 : ℂ)) (x₀⁻¹ * (List.ofFn δ).prod * θ x₀) * (s x₀ : ℂ) ∂μ) := by
  have h := P2mTwistedShiftUnit.descent θ hθ δ μ U hU hμU τ ‹_› w hw0 hwm hwc hsec
  dsimp only [P2mTwistedShiftUnit.rho, P2mTwistedShiftUnit.listProd, P2mTwistedShiftUnit.string] at h
  exact h

end S_AutomorphicForm_exists_integral_indicator_pi_twistedShift_mul_eq_integral_indicator_mul_of_forall_integral_eq_one
end P2MW
export P2MW.S_AutomorphicForm_exists_integral_indicator_pi_twistedShift_mul_eq_integral_indicator_mul_of_forall_integral_eq_one (solution)
