-- Prove2me | solution 1 for AutomorphicForm.exists_isLocalTestFn_areMatchingLocal_of_algHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/ebd77cd4-b9d5-5328-81c6-001408a292fe

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Theorems.Thm_AutomorphicForm_exists_isSectionFn_and_isLocallyConstant_of_isRegularSemisimple_of_isLocalTestFn
import Theorems.Thm_AutomorphicForm_integral_twistedConj_mul_eq_integral_conj_fibreIntegral_mul
import Theorems.Thm_AutomorphicForm_integral_mul_eq_integral_mul_of_forall_integral_subgroup_mul_eq_one
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isLocalTestFn_areMatchingLocal_of_algHom

set_option autoImplicit false
set_option maxHeartbeats 1600000

open NumberField IsDedekindDomain MeasureTheory TopologicalSpace
open scoped TensorProduct TensorProduct.RightActions

section ShiftBlock
open MeasureTheory

namespace TwistedShift

variable {G : Type} [Group G]

private def twc {n : ℕ} (δ x : Fin (n + 1) → G) : Fin (n + 1) → G := fun j => (x j)⁻¹ * δ j * x (j + 1)

private def nrm {n : ℕ} (δ : Fin (n + 1) → G) : G := (List.ofFn δ).prod

section Measure

variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
  (μ : Measure G) [SigmaFinite μ] [μ.IsMulLeftInvariant]

private noncomputable def fib {n : ℕ} (Φ : (Fin (n + 1) → G) → ℂ) (h : G) : ℂ :=
  ∫ c : Fin n → G, Φ (Fin.snoc c (((List.ofFn c).prod)⁻¹ * h)) ∂(Measure.pi fun _ => μ)

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

end Measure

section Uniq

variable {H : Type} [Group H] [MeasurableSpace H]

end Uniq

section Assembly

variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
  (μ : Measure G) [SigmaFinite μ] [μ.IsMulLeftInvariant]

end Assembly

set_option linter.unusedVariables false in
private def SectionIndependenceStatement : Prop :=
  ∀ {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
    (μ : Measure G) [SFinite μ] [μ.IsMulLeftInvariant]
    (T : Subgroup G) [MeasurableSpace T] [MeasurableInv T]
    (hT : Measurable (Subtype.val : T → G))
    (τ : Measure T) [SFinite τ] [τ.IsInvInvariant]
    (F : G → ℂ) (hF : Measurable F) (hFT : ∀ (t : T) (x : G), F ((t : G) * x) = F x)
    (w w' : G → ℝ) (hw : ∀ x, 0 ≤ w x) (hw' : ∀ x, 0 ≤ w' x)
    (hwm : Measurable w) (hw'm : Measurable w')
    (h1 : ∀ x, F x ≠ 0 → ∫ t : T, w ((t : G) * x) ∂τ = 1)
    (h1' : ∀ x, F x ≠ 0 → ∫ t : T, w' ((t : G) * x) ∂τ = 1),
    ∫ x, F x * (w x : ℂ) ∂μ = ∫ x, F x * (w' x : ℂ) ∂μ

set_option linter.unusedVariables false in
private def ShiftIdentityStatement : Prop :=
  ∀ {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
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
      Integrable β (Measure.pi fun _ => μ) ∧ ∀ c h, Φ (Fin.snoc c h) ≠ 0 → β c = 1),
    ∫ x, Φ (twc x) * (W₀ x : ℂ) ∂(Measure.pi fun _ : Fin (n + 1) => μ) =
      ∫ h, f (h⁻¹ * γ * h) * (w₀ h : ℂ) ∂μ

section Cutoff

variable {G : Type} [TopologicalSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G]
  [OpensMeasurableSpace G] (μ : Measure G)

private theorem exists_cutoff {n : ℕ} (Φ : (Fin (n + 1) → G) → ℂ) (hc : HasCompactSupport Φ)
    [IsFiniteMeasureOnCompacts (Measure.pi fun _ : Fin n => μ)] :
    ∃ β : (Fin n → G) → ℝ, (∀ c, 0 ≤ β c) ∧ Measurable β ∧
      Integrable β (Measure.pi fun _ => μ) ∧ ∀ c h, Φ (Fin.snoc c h) ≠ 0 → β c = 1 := by
  set S : Set (Fin n → G) := (fun x : Fin (n + 1) → G => (Fin.init x : Fin n → G)) '' tsupport Φ
    with hS_def
  have hScompact : IsCompact S := hc.image (continuous_pi fun i => continuous_apply _)
  have hSm : MeasurableSet S := hScompact.isClosed.measurableSet
  refine ⟨S.indicator fun _ => (1 : ℝ), fun c => Set.indicator_nonneg (fun _ _ => zero_le_one) c,
    measurable_const.indicator hSm, ?_, fun c h hne => ?_⟩
  · rw [integrable_indicator_iff hSm]
    exact integrableOn_const hScompact.measure_lt_top.ne
  · have hcS : c ∈ S := ⟨Fin.snoc c h, subset_tsupport Φ hne, Fin.init_snoc _ _⟩
    exact Set.indicator_of_mem hcS _

end Cutoff

section MatchingAbstract

variable {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
  (μ : Measure G) [SigmaFinite μ] [μ.IsMulLeftInvariant]

omit [MeasurableMul₂ G] [MeasurableInv G] in
private theorem measurableInv_subgroup {H : Type} [Group H] [MeasurableSpace H] [MeasurableInv H]
    (S : Subgroup H) : MeasurableInv S :=
  ⟨measurable_subtype_coe.inv.subtype_mk⟩

private theorem integral_twconj_mul_eq_integral_fib_mul
    (hUniq : SectionIndependenceStatement) (hShift : ShiftIdentityStatement)
    {n : ℕ} (δ : Fin (n + 1) → G)
    {Γ : Type} [Group Γ] [MeasurableSpace Γ] (Θ : Γ ≃* (Fin (n + 1) → G))
    (hΘm : Measurable Θ) (hΘsm : Measurable Θ.symm)
    (μΓ : Measure Γ) (c : NNReal) (hc : c ≠ 0)
    (hμΓ : Measure.map Θ μΓ = c • Measure.pi (fun _ : Fin (n + 1) => μ))
    (twconj : Γ → Γ) (htwc : ∀ x, Θ (twconj x) = twc δ (Θ x))
    (Tw : Subgroup Γ) [MeasurableSpace Tw] [MeasurableInv Tw]
    (hTwval : Measurable fun t : Tw => (t : Γ))
    (hTw : ∀ s : Γ, s ∈ Tw ↔ ∀ j, (Θ s j)⁻¹ * δ j * Θ s (j + 1) = δ j)
    (τ' : Measure Tw) [SFinite τ'] [τ'.IsInvInvariant]
    (y₀ γ : G) (hγ : γ = y₀⁻¹ * nrm δ * y₀)
    [MeasurableSpace (Subgroup.centralizer ({γ} : Set G))]
    [MeasurableInv (Subgroup.centralizer ({γ} : Set G))]
    (hval : Measurable fun s : Subgroup.centralizer ({γ} : Set G) => (s : G))
    (τ : Measure (Subgroup.centralizer ({γ} : Set G))) [SFinite τ] [τ.IsInvInvariant]
    (hcoup : Measure.map (fun t : Tw => y₀⁻¹ * Θ (t : Γ) 0 * y₀) τ' =
      Measure.map (fun s : Subgroup.centralizer ({γ} : Set G) => (s : G)) τ)
    (φ : Γ → ℂ) (hφm : Measurable φ) (hφb : ∃ C, ∀ x, ‖φ x‖ ≤ C)
    (W : Γ → ℝ) (hW : ∀ x, 0 ≤ W x) (hWm : Measurable W)
    (hW1 : ∀ x, φ (twconj x) ≠ 0 → ∫ t : Tw, W ((t : Γ) * x) ∂τ' = 1)
    (w₀ : G → ℝ) (hw₀ : ∀ h, 0 ≤ w₀ h) (hw₀m : Measurable w₀)
    (hw₀1 : ∀ h, ((c : ℝ) : ℂ) * fib μ (φ ∘ Θ.symm) (h⁻¹ * γ * h) ≠ 0 →
      ∫ s : Subgroup.centralizer ({γ} : Set G), w₀ ((s : G) * h) ∂τ = 1)
    (hw₁ : ∃ w₁ : G → ℝ, (∀ h, 0 ≤ w₁ h) ∧ Measurable w₁ ∧ Integrable w₁ μ ∧
      ∀ h, fib μ (fun y => (‖(φ ∘ Θ.symm) y‖ : ℂ)) (h⁻¹ * γ * h) ≠ 0 →
        ∫ s : Subgroup.centralizer ({γ} : Set G), w₁ ((s : G) * h) ∂τ = 1)
    (hβ : ∃ β : (Fin n → G) → ℝ, (∀ c, 0 ≤ β c) ∧ Measurable β ∧
      Integrable β (Measure.pi fun _ => μ) ∧ ∀ c h, (φ ∘ Θ.symm) (Fin.snoc c h) ≠ 0 → β c = 1) :
    ∫ x, φ (twconj x) * (W x : ℂ) ∂μΓ =
      ∫ h, (((c : ℝ) : ℂ) * fib μ (φ ∘ Θ.symm) (h⁻¹ * γ * h)) * (w₀ h : ℂ) ∂μ := by
  set Φ : (Fin (n + 1) → G) → ℂ := φ ∘ Θ.symm with hΦ_def
  have hΦm : Measurable Φ := hφm.comp hΘsm
  have hΦb : ∃ C, ∀ z, ‖Φ z‖ ≤ C := hφb.imp fun C hC z => hC _
  have hΦtwc : ∀ z, Φ (twc δ z) = φ (twconj (Θ.symm z)) := by
    intro z
    simp only [hΦ_def, Function.comp_apply]
    congr 1
    rw [MulEquiv.symm_apply_eq, htwc, MulEquiv.apply_symm_apply]

  set T : Subgroup (Fin (n + 1) → G) := Tw.map (Θ : Γ →* (Fin (n + 1) → G)) with hT_def
  have hTmem : ∀ t, t ∈ T ↔ ∀ j, (t j)⁻¹ * δ j * t (j + 1) = δ j := by
    intro t
    rw [hT_def, Subgroup.mem_map]
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact (hTw s).1 hs
    · intro ht
      refine ⟨Θ.symm t, (hTw _).2 ?_, by simp⟩
      simpa only [MulEquiv.apply_symm_apply] using ht
  let e : Tw → T := fun t => ⟨Θ (t : Γ), Subgroup.mem_map.2 ⟨(t : Γ), t.2, rfl⟩⟩
  have he_val : ∀ t : Tw, ((e t : T) : Fin (n + 1) → G) = Θ (t : Γ) := fun _ => rfl
  have hem : Measurable e := (hΘm.comp hTwval).subtype_mk
  haveI : MeasurableInv T := measurableInv_subgroup T
  set τT : Measure T := Measure.map e τ' with hτT_def
  haveI : τT.IsInvInvariant := by
    refine ⟨?_⟩
    show Measure.map Inv.inv (Measure.map e τ') = Measure.map e τ'
    rw [Measure.map_map measurable_inv hem]
    have hcomm : (Inv.inv ∘ e) = e ∘ (Inv.inv : Tw → Tw) := by
      funext t
      apply Subtype.ext
      simp only [Function.comp_apply, he_val, Subgroup.coe_inv, map_inv]
    rw [hcomm, ← Measure.map_map hem measurable_inv, Measure.map_inv_eq_self]

  have huniqT := hUniq (Measure.pi fun _ : Fin (n + 1) => μ) T measurable_subtype_coe τT
  have huniqG := hUniq μ (Subgroup.centralizer ({γ} : Set G)) hval τ

  have hmeasT : Measurable fun t : T => y₀⁻¹ * (t : Fin (n + 1) → G) 0 * y₀ :=
    (measurable_const.mul ((measurable_pi_apply 0).comp measurable_subtype_coe)).mul_const _
  have hτ : Measure.map (fun t : T => y₀⁻¹ * (t : Fin (n + 1) → G) 0 * y₀) τT =
      Measure.map (fun s : Subgroup.centralizer ({γ} : Set G) => (s : G)) τ := by
    rw [hτT_def, Measure.map_map hmeasT hem, ← hcoup]
    rfl

  have hW₀1 : ∀ z, Φ (twc δ z) ≠ 0 →
      ∫ t : T, (W ∘ Θ.symm) ((t : Fin (n + 1) → G) * z) ∂τT = 1 := by
    intro z hz
    have hsm : StronglyMeasurable fun t : T => (W ∘ Θ.symm) ((t : Fin (n + 1) → G) * z) :=
      ((hWm.comp hΘsm).comp (measurable_subtype_coe.mul_const z)).stronglyMeasurable
    rw [hτT_def, integral_map_of_stronglyMeasurable hem hsm]
    have : ∀ t : Tw, (W ∘ Θ.symm) (((e t : T) : Fin (n + 1) → G) * z) = W ((t : Γ) * Θ.symm z) := by
      intro t
      simp only [Function.comp_apply, he_val, map_mul, MulEquiv.symm_apply_apply]
    simp only [this]
    rw [hΦtwc] at hz
    exact hW1 _ hz
  have hcℂ : ((c : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (NNReal.coe_ne_zero.2 hc)

  have hmain := hShift μ δ (twc δ) (fun _ _ => rfl) T hTmem y₀ γ hγ Φ hΦm hΦb (fib μ Φ)
    (fib μ fun y => (‖Φ y‖ : ℂ)) (fun _ => rfl) (fun _ => rfl) τT hmeasT τ hval hτ huniqT huniqG
    (W ∘ Θ.symm) (fun z => hW _) (hWm.comp hΘsm) hW₀1 w₀ hw₀ hw₀m
    (fun h hh => hw₀1 h (mul_ne_zero hcℂ hh)) hw₁ hβ

  have hleft : ∫ x, φ (twconj x) * (W x : ℂ) ∂μΓ =
      ∫ z, Φ (twc δ z) * ((W ∘ Θ.symm) z : ℂ) ∂(c • Measure.pi fun _ : Fin (n + 1) => μ) := by
    have hsm : StronglyMeasurable fun z : Fin (n + 1) → G => Φ (twc δ z) * ((W ∘ Θ.symm) z : ℂ) :=
      ((hΦm.comp (measurable_twc δ)).mul
        (Complex.measurable_ofReal.comp (hWm.comp hΘsm))).stronglyMeasurable
    rw [← hμΓ, integral_map_of_stronglyMeasurable hΘm hsm]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hΦtwc, Function.comp_apply, MulEquiv.symm_apply_apply]
  rw [hleft, integral_smul_nnreal_measure, hmain, NNReal.smul_def, ← integral_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
  simp only [mul_assoc]
  exact Complex.real_smul

end MatchingAbstract

end TwistedShift

end ShiftBlock

namespace RotatedString

variable {G : Type} [Monoid G]

private theorem prod_ofFn_eq_of_forall_ne_eq_one : ∀ {m : ℕ} (f : Fin m → G) (i : Fin m),
    (∀ k, k ≠ i → f k = 1) → (List.ofFn f).prod = f i
  | 0, _, i, _ => i.elim0
  | m + 1, f, i, h => by
    rw [List.ofFn_succ, List.prod_cons]
    by_cases hi : i = 0
    · subst hi
      rw [List.prod_eq_one, mul_one]
      intro x hx
      obtain ⟨k, rfl⟩ := Set.mem_range.1 ((List.mem_ofFn' _ _).1 hx)
      exact h _ (Fin.succ_ne_zero k)
    · obtain ⟨i', rfl⟩ := Fin.exists_succ_eq.2 hi
      rw [h 0 (Ne.symm (Fin.succ_ne_zero i')), one_mul]
      exact prod_ofFn_eq_of_forall_ne_eq_one (fun k => f k.succ) i' fun k hk =>
        h _ (fun e => hk (Fin.succ_injective _ e))

private theorem prod_ofFn_mulSingle_add {n : ℕ} (γ : G) (j : Fin (n + 1)) :
    (List.ofFn fun k : Fin (n + 1) => (Pi.mulSingle 0 γ : Fin (n + 1) → G) (j + k)).prod = γ := by
  obtain ⟨i, hi⟩ : ∃ i : Fin (n + 1), j + i = 0 := ⟨-j, add_neg_cancel j⟩
  rw [prod_ofFn_eq_of_forall_ne_eq_one _ i]
  · rw [hi, Pi.mulSingle_eq_same]
  · intro k hk
    apply Pi.mulSingle_eq_of_ne
    intro hjk
    exact hk (add_left_cancel (hjk.trans hi.symm))

end RotatedString

section ModelBlock
p2m_open "AutomorphicForm Module TensorProduct.RightActions.Module"
p2m_open_scoped "TensorProduct TensorProduct.RightActions.Module.TensorProduct TensorProduct.RightActions"

namespace SplitModel

section Furniture

private def unitsCME {R S : Type} [Monoid R] [Monoid S] [TopologicalSpace R] [TopologicalSpace S]
    (e : R ≃* S) (he : Continuous e) (he' : Continuous e.symm) : Rˣ ≃ₜ* Sˣ where
  __ := Units.mapEquiv e
  continuous_toFun := he.units_map e.toMonoidHom
  continuous_invFun := he'.units_map e.symm.toMonoidHom

variable (F : Type) [Semiring F] (m : ℕ)

private def piMat : Matrix (Fin 2) (Fin 2) (Fin m → F) ≃+* (Fin m → Matrix (Fin 2) (Fin 2) F) :=
  Matrix.piRingEquiv

variable [TopologicalSpace F]

private theorem continuous_piMat : Continuous (piMat F m) :=
  continuous_pi fun i => continuous_id.matrix_map (continuous_apply i)

private theorem continuous_piMat_symm : Continuous (piMat F m).symm :=
  continuous_matrix fun a b => continuous_pi fun i => (continuous_apply i).matrix_elem a b

private theorem iterate_add_one_val {n : ℕ} (m : ℕ) (j : Fin (n + 1)) :
    (((fun x : Fin (n + 1) => x + 1)^[m] j) : ℕ) = (j + m) % (n + 1) := by
  induction m with
  | zero => simp [Nat.mod_eq_of_lt j.isLt]
  | succ m ih =>
    rw [Function.iterate_succ_apply', Fin.val_add, ih, Fin.val_one', Nat.add_mod_mod,
      Nat.mod_add_mod, ← Nat.add_assoc]

private theorem iterate_add_one_eq_add {n : ℕ} (j k : Fin (n + 1)) :
    (fun x : Fin (n + 1) => x + 1)^[(k : ℕ)] j = j + k := by
  apply Fin.ext
  rw [iterate_add_one_val, Fin.val_add]

private theorem apply_iterate_of_apply_eq {X Y : Type} {n : ℕ} (f : X → X) (θ : X → Fin (n + 1) → Y)
    (hθ : ∀ g i, θ (f g) i = θ g (i + 1)) (k : ℕ) (g : X) (i : Fin (n + 1)) :
    θ (f^[k] g) i = θ g ((fun x : Fin (n + 1) => x + 1)^[k] i) := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', hθ, ih, Function.iterate_succ_apply]

private theorem apply_iterate_val_of_apply_eq {X Y : Type} {n : ℕ} (f : X → X) (θ : X → Fin (n + 1) → Y)
    (hθ : ∀ g i, θ (f g) i = θ g (i + 1)) (g : X) (j k : Fin (n + 1)) :
    θ (f^[(k : ℕ)] g) j = θ g (j + k) := by
  rw [apply_iterate_of_apply_eq f θ hθ, iterate_add_one_eq_add]

end Furniture

section Defs

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  (F : Type) [CommRing F] [Algebra K F] (ι : L →ₐ[K] F) (σ : L ≃ₐ[K] L) (n : ℕ)

private def chiAlg (i : Fin (n + 1)) : L →ₐ[K] F :=
  ι.comp (σ ^ (i : ℕ)).toAlgHom

private theorem chiAlg_apply (i : Fin (n + 1)) (x : L) : chiAlg K L F ι σ n i x = ι ((σ ^ (i : ℕ)) x) :=
  rfl

private def chi (i : Fin (n + 1)) : L →* F :=
  MonoidHomClass.toMonoidHom (chiAlg K L F ι σ n i)

private theorem chi_apply (i : Fin (n + 1)) (x : L) : chi K L F ι σ n i x = ι ((σ ^ (i : ℕ)) x) :=
  rfl

private noncomputable def psiL : F ⊗[K] L →ₐ[F] (Fin (n + 1) → F) :=
  Algebra.TensorProduct.lift (Algebra.ofId F (Fin (n + 1) → F))
    (Pi.algHom K (A := fun _ : Fin (n + 1) => F) (chiAlg K L F ι σ n)) fun _ _ => Commute.all _ _

private theorem psiL_tmul (a : F) (x : L) :
    psiL K L F ι σ n (a ⊗ₜ x) = fun i : Fin (n + 1) => a * ι ((σ ^ (i : ℕ)) x) := by
  funext i
  simp [psiL, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, chiAlg_apply]

private theorem psiL_tmul_apply (a : F) (x : L) (i : Fin (n + 1)) :
    psiL K L F ι σ n (a ⊗ₜ x) i = a * ι ((σ ^ (i : ℕ)) x) := by
  rw [psiL_tmul]

variable {σ n}

private theorem orderOf_eq (hσ1 : σ ^ (n + 1) = 1) (hprime : (n + 1).Prime) (hσ : σ ≠ 1) :
    orderOf σ = n + 1 := by
  haveI := Fact.mk hprime
  exact orderOf_eq_prime hσ1 hσ

private theorem chi_injective [Nontrivial F] (hσ1 : σ ^ (n + 1) = 1) (hprime : (n + 1).Prime) (hσ : σ ≠ 1) :
    Function.Injective (chi K L F ι σ n) := by
  intro i j hij
  have hx : ∀ x : L, (σ ^ (i : ℕ)) x = (σ ^ (j : ℕ)) x := fun x =>
    ι.toRingHom.injective (by simpa [chi_apply] using congrArg (fun f : L →* F => f x) hij)
  have hmod := pow_eq_pow_iff_modEq.mp (AlgEquiv.ext hx)
  rw [Nat.ModEq, orderOf_eq K L hσ1 hprime hσ, Nat.mod_eq_of_lt i.isLt,
    Nat.mod_eq_of_lt j.isLt] at hmod
  exact Fin.ext hmod

end Defs

section FieldCase

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  (F : Type) [Field F] [Algebra K F] (ι : L →ₐ[K] F) {σ : L ≃ₐ[K] L} {n : ℕ}

private theorem psiL_surjective (hσ1 : σ ^ (n + 1) = 1) (hprime : (n + 1).Prime) (hσ : σ ≠ 1) :
    Function.Surjective (psiL K L F ι σ n) := by
  rw [← AlgHom.coe_toLinearMap, ← LinearMap.range_eq_top]
  by_contra hne
  obtain ⟨f, hf0, hf⟩ :=
    Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.mpr hne) inferInstance
  have hker : ∀ z, f ((psiL K L F ι σ n).toLinearMap z) = 0 := by
    intro z
    have hz := Submodule.mem_map_of_mem (f := f)
      (LinearMap.mem_range_self (psiL K L F ι σ n).toLinearMap z)
    rw [hf] at hz
    exact (Submodule.mem_bot F).mp hz
  have hli : LinearIndependent F fun i : Fin (n + 1) => ⇑(chi K L F ι σ n i) :=
    (linearIndependent_monoidHom L F).comp _ (chi_injective K L F ι hσ1 hprime hσ)
  have hc0 : ∀ i : Fin (n + 1), f (fun j => if i = j then (1 : F) else 0) = 0 := by
    refine Fintype.linearIndependent_iff.mp hli (fun i => f fun j => if i = j then 1 else 0) ?_
    funext x
    have h := hker (1 ⊗ₜ x)
    rw [AlgHom.toLinearMap_apply, psiL_tmul, LinearMap.pi_apply_eq_sum_univ] at h
    simp only [one_mul, smul_eq_mul] at h
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, chi_apply, Pi.zero_apply]
    simpa only [mul_comm] using h
  refine hf0 (LinearMap.ext fun v => ?_)
  rw [LinearMap.zero_apply, LinearMap.pi_apply_eq_sum_univ f v]
  simp only [hc0, smul_zero, Finset.sum_const_zero]

variable [FiniteDimensional K L]

private theorem psiL_bijective (hn : finrank K L = n + 1) (hσ1 : σ ^ (n + 1) = 1) (hprime : (n + 1).Prime)
    (hσ : σ ≠ 1) : Function.Bijective (psiL K L F ι σ n) := by
  have hsurj := psiL_surjective K L F ι hσ1 hprime hσ
  have hsurj' : Function.Surjective (psiL K L F ι σ n).toLinearMap := hsurj
  refine ⟨?_, hsurj⟩
  have hinj : Function.Injective (psiL K L F ι σ n).toLinearMap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mpr hsurj'
  · exact hinj
  · rw [Module.finrank_baseChange, Module.finrank_fin_fun, hn]

end FieldCase

section PiCase

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  {J : Type} [Fintype J] [DecidableEq J] (E : J → Type) [∀ j, Field (E j)] [∀ j, Algebra K (E j)]

private noncomputable def piDistrib : (Π j, E j) ⊗[K] L ≃ₐ[K] Π j, E j ⊗[K] L :=
  (Algebra.TensorProduct.comm K (Π j, E j) L).trans
    ((Algebra.TensorProduct.piRight K K L E).trans
      (AlgEquiv.piCongrRight fun j => Algebra.TensorProduct.comm K L (E j)))

private theorem piDistrib_tmul (a : Π j, E j) (x : L) :
    piDistrib K L E (a ⊗ₜ x) = fun j => a j ⊗ₜ x := by
  funext j
  simp [piDistrib]

variable (ι : L →ₐ[K] Π j, E j) {σ : L ≃ₐ[K] L} {n : ℕ}

private theorem psiL_pi_apply (z : (Π j, E j) ⊗[K] L) (i : Fin (n + 1)) (j : J) :
    psiL K L (Π j, E j) ι σ n z i j =
      psiL K L (E j) ((Pi.evalAlgHom K E j).comp ι) σ n (piDistrib K L E z j) i := by
  induction z with
  | zero => simp
  | tmul a x => simp [psiL_tmul_apply, piDistrib_tmul]
  | add y w hy hw => simp only [map_add, Pi.add_apply, hy, hw]

variable [FiniteDimensional K L]

private theorem psiL_bijective_pi (hn : finrank K L = n + 1) (hσ1 : σ ^ (n + 1) = 1)
    (hprime : (n + 1).Prime) (hσ : σ ≠ 1) : Function.Bijective (psiL K L (Π j, E j) ι σ n) := by
  have hcomp : ∀ j, Function.Bijective (psiL K L (E j) ((Pi.evalAlgHom K E j).comp ι) σ n) :=
    fun j => psiL_bijective K L (E j) _ hn hσ1 hprime hσ
  constructor
  · intro z₁ z₂ h
    apply (piDistrib K L E).injective
    funext j
    apply (hcomp j).1
    funext i
    rw [← psiL_pi_apply K L E ι, ← psiL_pi_apply K L E ι, h]
  · intro w
    choose y hy using fun j => (hcomp j).2 fun i => w i j
    refine ⟨(piDistrib K L E).symm y, ?_⟩
    funext i j
    rw [psiL_pi_apply K L E ι, AlgEquiv.apply_symm_apply, hy]

end PiCase

section Bridge

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  (F : Type) [CommRing F] [Algebra K F] (ι : L →ₐ[K] F) (σ : L ≃ₐ[K] L) (n : ℕ)

private noncomputable def psiR : L ⊗[K] F →ₐ[F] (Fin (n + 1) → F) :=
  (psiL K L F ι σ n).comp
    (TensorProduct.RightActions.Algebra.TensorProduct.comm K F L).symm.toAlgHom

private theorem psiR_apply (z : L ⊗[K] F) :
    psiR K L F ι σ n z =
      psiL K L F ι σ n ((TensorProduct.RightActions.Algebra.TensorProduct.comm K F L).symm z) :=
  rfl

private theorem psiR_tmul (x : L) (a : F) :
    psiR K L F ι σ n (x ⊗ₜ a) = fun i : Fin (n + 1) => a * ι ((σ ^ (i : ℕ)) x) := by
  rw [psiR_apply, TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul, psiL_tmul]

private theorem psiR_tmul_apply (x : L) (a : F) (i : Fin (n + 1)) :
    psiR K L F ι σ n (x ⊗ₜ a) i = a * ι ((σ ^ (i : ℕ)) x) := by
  rw [psiR_tmul]

private noncomputable def psi : L ⊗[K] F →ₗ[F] (Fin (n + 1) → F) :=
  (psiR K L F ι σ n).toLinearMap

private theorem coe_psi : ⇑(psi K L F ι σ n) = ⇑(psiR K L F ι σ n) :=
  rfl

private theorem sigmaTensor_tmul (x : L) (a : F) : sigmaTensor K L F σ (x ⊗ₜ a) = σ x ⊗ₜ a := by
  simp [sigmaTensor]

variable {σ n}

private theorem psiR_bijective (hbij : Function.Bijective (psiL K L F ι σ n)) :
    Function.Bijective (psiR K L F ι σ n) := by
  have h : ⇑(psiR K L F ι σ n) = ⇑(psiL K L F ι σ n) ∘
      ⇑(TensorProduct.RightActions.Algebra.TensorProduct.comm K F L).symm := rfl
  rw [h]
  exact hbij.comp (TensorProduct.RightActions.Algebra.TensorProduct.comm K F L).symm.bijective

private theorem pow_val_add_one (hσ1 : σ ^ (n + 1) = 1) (i : Fin (n + 1)) :
    σ ^ (((i + 1 : Fin (n + 1)) : ℕ)) = σ ^ ((i : ℕ) + 1) := by
  rw [Fin.val_add_one]
  split_ifs with h <;> simp [h, hσ1]

private theorem psiR_sigmaTensor (hσ1 : σ ^ (n + 1) = 1) (z : L ⊗[K] F) :
    psiR K L F ι σ n (sigmaTensor K L F σ z) =
      fun i : Fin (n + 1) => psiR K L F ι σ n z (i + 1) := by
  induction z with
  | zero => funext i; simp
  | tmul x a =>
    funext i
    rw [sigmaTensor_tmul, psiR_tmul_apply, psiR_tmul_apply, pow_val_add_one K L hσ1 i, pow_succ,
      AlgEquiv.mul_apply]
  | add y w hy hw => funext i; simp only [map_add, Pi.add_apply, hy, hw]

variable (hbij : Function.Bijective (psiL K L F ι σ n))
include hbij

private noncomputable def Psi : L ⊗[K] F ≃ₐ[F] (Fin (n + 1) → F) :=
  AlgEquiv.ofBijective (psiR K L F ι σ n) (psiR_bijective K L F ι hbij)

private theorem coe_Psi : ⇑(Psi K L F ι hbij) = ⇑(psiR K L F ι σ n) :=
  rfl

private noncomputable def PsiLin : L ⊗[K] F ≃ₗ[F] (Fin (n + 1) → F) :=
  { psi K L F ι σ n with
    invFun := ⇑(Psi K L F ι hbij).symm
    left_inv := (Psi K L F ι hbij).symm_apply_apply
    right_inv := (Psi K L F ι hbij).apply_symm_apply }

private theorem coe_PsiLin_symm : ⇑(PsiLin K L F ι hbij).symm = ⇑(Psi K L F ι hbij).symm :=
  rfl

section Topology

variable [FiniteDimensional K L] [TopologicalSpace F] [IsTopologicalRing F]

private theorem continuous_Psi : Continuous (Psi K L F ι hbij) := by
  rw [coe_Psi, ← coe_psi]
  exact IsModuleTopology.continuous_of_linearMap _

private theorem continuous_Psi_symm : Continuous (Psi K L F ι hbij).symm := by
  rw [← coe_PsiLin_symm K L F ι hbij]
  exact IsModuleTopology.continuous_of_linearMap (PsiLin K L F ι hbij).symm.toLinearMap

private noncomputable def matPsi :
    Matrix (Fin 2) (Fin 2) (L ⊗[K] F) ≃+* Matrix (Fin 2) (Fin 2) (Fin (n + 1) → F) :=
  RingEquiv.mapMatrix (Psi K L F ι hbij).toRingEquiv

private theorem continuous_matPsi : Continuous (matPsi K L F ι hbij) := by
  show Continuous fun M : Matrix (Fin 2) (Fin 2) (L ⊗[K] F) => M.map (Psi K L F ι hbij)
  exact continuous_id.matrix_map (continuous_Psi K L F ι hbij)

private theorem continuous_matPsi_symm : Continuous (matPsi K L F ι hbij).symm := by
  show Continuous fun M : Matrix (Fin 2) (Fin 2) (Fin (n + 1) → F) => M.map (Psi K L F ι hbij).symm
  exact continuous_id.matrix_map (continuous_Psi_symm K L F ι hbij)

private noncomputable def Theta : GL (Fin 2) (L ⊗[K] F) ≃ₜ* (Fin (n + 1) → GL (Fin 2) F) :=
  ((unitsCME (matPsi K L F ι hbij).toMulEquiv (continuous_matPsi K L F ι hbij)
        (continuous_matPsi_symm K L F ι hbij)).trans
      (unitsCME (piMat F (n + 1)).toMulEquiv (continuous_piMat F (n + 1))
        (continuous_piMat_symm F (n + 1)))).trans
    ContinuousMulEquiv.piUnits

private theorem Theta_apply (g : GL (Fin 2) (L ⊗[K] F)) (i : Fin (n + 1)) (a b : Fin 2) :
    Theta K L F ι hbij g i a b = psiR K L F ι σ n (g a b) i :=
  rfl

private theorem Theta_symm_apply (h : Fin (n + 1) → GL (Fin 2) F) (a b : Fin 2) :
    (Theta K L F ι hbij).symm h a b = (Psi K L F ι hbij).symm fun i => h i a b :=
  rfl

private theorem Theta_toTensorGL (γ : GL (Fin 2) F) :
    Theta K L F ι hbij (toTensorGL K L F γ) = fun _ => γ := by
  funext i
  refine Units.ext (Matrix.ext fun a b => ?_)
  rw [Theta_apply, toTensorGL, Matrix.GeneralLinearGroup.map_apply]
  simp [psiR_tmul_apply]

private theorem Theta_sigmaGL_apply (hσ1 : σ ^ (n + 1) = 1) (g : GL (Fin 2) (L ⊗[K] F)) (i : Fin (n + 1)) :
    Theta K L F ι hbij (sigmaGL K L F σ g) i = Theta K L F ι hbij g (i + 1) := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  rw [Theta_apply, Theta_apply, sigmaGL, Matrix.GeneralLinearGroup.map_apply,
    psiR_sigmaTensor K L F ι hσ1]

private theorem Theta_sigmaConj (hσ1 : σ ^ (n + 1) = 1) (x δ : GL (Fin 2) (L ⊗[K] F)) :
    Theta K L F ι hbij (x⁻¹ * δ * sigmaGL K L F σ x) = fun j : Fin (n + 1) =>
      (Theta K L F ι hbij x j)⁻¹ * Theta K L F ι hbij δ j * Theta K L F ι hbij x (j + 1) := by
  funext j
  simp only [map_mul, map_inv, Pi.mul_apply, Pi.inv_apply, Theta_sigmaGL_apply K L F ι hbij hσ1]

private theorem Theta_sigmaGL_iterate_apply (hσ1 : σ ^ (n + 1) = 1) (δ : GL (Fin 2) (L ⊗[K] F))
    (j k : Fin (n + 1)) :
    Theta K L F ι hbij ((⇑(sigmaGL K L F σ))^[(k : ℕ)] δ) j = Theta K L F ι hbij δ (j + k) :=
  apply_iterate_val_of_apply_eq (⇑(sigmaGL K L F σ)) (fun g => Theta K L F ι hbij g)
    (fun g i => Theta_sigmaGL_apply K L F ι hbij hσ1 g i) δ j k

private theorem Theta_normString_apply (hn : finrank K L = n + 1) (hσ1 : σ ^ (n + 1) = 1)
    (δ : GL (Fin 2) (L ⊗[K] F)) (j : Fin (n + 1)) :
    Theta K L F ι hbij (normString K L F σ δ) j =
      (List.ofFn fun k : Fin (n + 1) => Theta K L F ι hbij δ (j + k)).prod := by
  rw [normString, hn, map_list_prod, Pi.list_prod_apply, List.map_map, List.map_map,
    List.ofFn_eq_map, ← List.map_coe_finRange_eq_range, List.map_map]
  congr 1
  refine List.map_congr_left fun k _ => ?_
  simp only [Function.comp_apply]
  exact Theta_sigmaGL_iterate_apply K L F ι hbij hσ1 δ j k

private theorem Theta_normString_zero (hn : finrank K L = n + 1) (hσ1 : σ ^ (n + 1) = 1)
    (δ : GL (Fin 2) (L ⊗[K] F)) :
    Theta K L F ι hbij (normString K L F σ δ) 0 = (List.ofFn (Theta K L F ι hbij δ)).prod := by
  rw [Theta_normString_apply K L F ι hbij hn hσ1]
  simp only [zero_add]

end Topology

end Bridge

end SplitModel

end ModelBlock

section

open Filter Topology

namespace RegularCentralizer

private theorem exists_mem_nhds_one_forall_mul_eq {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {f : G → ℂ} (hf : IsLocallyConstant f) (hc : HasCompactSupport f) :
    ∃ W ∈ 𝓝 (1 : G), ∀ x ∈ W, ∀ y, f (x * y) = f y ∧ f (y * x) = f y := by
  have hL : IsOpen {z : G × G | f (z.1 * z.2) = f z.2} := by
    have h1 : IsLocallyConstant fun z : G × G => f (z.1 * z.2) := hf.comp_continuous continuous_mul
    have h2 : IsLocallyConstant fun z : G × G => f z.2 := hf.comp_continuous continuous_snd
    exact (h1.prodMk h2) {p : ℂ × ℂ | p.1 = p.2}
  have hR : IsOpen {z : G × G | f (z.2 * z.1) = f z.2} := by
    have h1 : IsLocallyConstant fun z : G × G => f (z.2 * z.1) :=
      hf.comp_continuous (continuous_snd.mul continuous_fst)
    have h2 : IsLocallyConstant fun z : G × G => f z.2 := hf.comp_continuous continuous_snd
    exact (h1.prodMk h2) {p : ℂ × ℂ | p.1 = p.2}
  have hLe : ∀ᶠ x in 𝓝 (1 : G), ∀ y ∈ tsupport f, f (x * y) = f y :=
    IsCompact.eventually_forall_of_forall_eventually (x₀ := (1 : G))
      (P := fun x y => f (x * y) = f y) (hc : IsCompact (tsupport f))
      fun y _ => hL.mem_nhds (by simp)
  have hRe : ∀ᶠ x in 𝓝 (1 : G), ∀ y ∈ tsupport f, f (y * x) = f y :=
    IsCompact.eventually_forall_of_forall_eventually (x₀ := (1 : G))
      (P := fun x y => f (y * x) = f y) (hc : IsCompact (tsupport f))
      fun y _ => hR.mem_nhds (by simp)
  have hinv : Tendsto (fun x : G => x⁻¹) (𝓝 (1 : G)) (𝓝 (1 : G)) := by
    simpa only [inv_one] using continuous_inv.tendsto (1 : G)
  have hLi : ∀ᶠ x in 𝓝 (1 : G), ∀ y ∈ tsupport f, f (x⁻¹ * y) = f y := hinv.eventually hLe
  have hRi : ∀ᶠ x in 𝓝 (1 : G), ∀ y ∈ tsupport f, f (y * x⁻¹) = f y := hinv.eventually hRe
  obtain ⟨W, hW, hWall⟩ := (hLe.and (hRe.and (hLi.and hRi))).exists_mem
  refine ⟨W, hW, fun x hx y => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hWall x hx
  constructor
  · by_cases hy : y ∈ tsupport f
    · exact h1 y hy
    · by_cases hxy : x * y ∈ tsupport f
      · have h := h3 (x * y) hxy
        rw [inv_mul_cancel_left] at h
        exact h.symm
      · rw [image_eq_zero_of_notMem_tsupport hy, image_eq_zero_of_notMem_tsupport hxy]
  · by_cases hy : y ∈ tsupport f
    · exact h2 y hy
    · by_cases hxy : y * x ∈ tsupport f
      · have h := h4 (y * x) hxy
        rw [mul_inv_cancel_right] at h
        exact h.symm
      · rw [image_eq_zero_of_notMem_tsupport hy, image_eq_zero_of_notMem_tsupport hxy]

end RegularCentralizer

end

section

open AutomorphicForm

namespace RegularCentralizer

section Ring

variable {A : Type*} [CommRing A]

private theorem exists_eq_smul_one_add_smul_of_mul_eq_mul {G X : Matrix (Fin 2) (Fin 2) A}
    (hd : IsUnit (Matrix.trace G ^ 2 - 4 * Matrix.det G)) (hX : X * G = G * X) :
    ∃ l m : A, X = l • (1 : Matrix (Fin 2) (Fin 2) A) + m • G := by
  rw [Matrix.trace_fin_two, Matrix.det_fin_two] at hd
  obtain ⟨u, hu⟩ := hd
  have hu1 : (↑u⁻¹ : A) * ↑u = 1 := u.inv_mul
  have h00 : (X * G) 0 0 = (G * X) 0 0 := by rw [hX]
  have h01 : (X * G) 0 1 = (G * X) 0 1 := by rw [hX]
  have h10 : (X * G) 1 0 = (G * X) 1 0 := by rw [hX]
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10
  obtain ⟨Z, hZ⟩ : ∃ Z : A,
      Z = (G 0 0 - G 1 1) * (X 0 0 - X 1 1) + 2 * (G 1 0 * X 0 1 + G 0 1 * X 1 0) := ⟨_, rfl⟩
  refine ⟨X 0 0 - (↑u⁻¹ : A) * Z * G 0 0, (↑u⁻¹ : A) * Z, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j
  · simp
  · simp
    linear_combination (-(X 0 1)) * hu1 + (X 0 1 * (↑u⁻¹ : A)) * hu -
      ((↑u⁻¹ : A) * (G 0 0 - G 1 1)) * h01 + (2 * (↑u⁻¹ : A) * G 0 1) * h00 -
      ((↑u⁻¹ : A) * G 0 1) * hZ
  · simp
    linear_combination (-(X 1 0)) * hu1 + (X 1 0 * (↑u⁻¹ : A)) * hu +
      ((↑u⁻¹ : A) * (G 0 0 - G 1 1)) * h10 - (2 * (↑u⁻¹ : A) * G 1 0) * h00 -
      ((↑u⁻¹ : A) * G 1 0) * hZ
  · simp
    linear_combination (X 0 0 - X 1 1) * hu1 - ((X 0 0 - X 1 1) * (↑u⁻¹ : A)) * hu -
      (2 * (↑u⁻¹ : A) * G 1 0) * h01 + (2 * (↑u⁻¹ : A) * G 0 1) * h10 +
      ((↑u⁻¹ : A) * (G 0 0 - G 1 1)) * hZ

private theorem commute_of_mul_eq_mul_of_mul_eq_mul {G X Y : Matrix (Fin 2) (Fin 2) A}
    (hd : IsUnit (Matrix.trace G ^ 2 - 4 * Matrix.det G)) (hX : X * G = G * X)
    (hY : Y * G = G * Y) :
    Commute X Y := by
  obtain ⟨l, m, rfl⟩ := exists_eq_smul_one_add_smul_of_mul_eq_mul hd hX
  obtain ⟨l', m', rfl⟩ := exists_eq_smul_one_add_smul_of_mul_eq_mul hd hY
  have c1 : Commute (1 : Matrix (Fin 2) (Fin 2) A) (l' • (1 : Matrix (Fin 2) (Fin 2) A) + m' • G) :=
    ((Commute.one_left _).smul_right l').add_right ((Commute.one_left G).smul_right m')
  have c2 : Commute G (l' • (1 : Matrix (Fin 2) (Fin 2) A) + m' • G) :=
    ((Commute.one_right G).smul_right l').add_right ((Commute.refl G).smul_right m')
  exact (c1.smul_left l).add_left (c2.smul_left m)

private theorem commute_of_mem_centralizer_of_isRegularSemisimple {g : GL (Fin 2) A}
    (hg : IsRegularSemisimple g) {x y : GL (Fin 2) A}
    (hx : x ∈ Subgroup.centralizer ({g} : Set (GL (Fin 2) A)))
    (hy : y ∈ Subgroup.centralizer ({g} : Set (GL (Fin 2) A))) : Commute x y := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hx hy
  have hx' : (x : Matrix (Fin 2) (Fin 2) A) * g = g * x := congrArg Units.val hx
  have hy' : (y : Matrix (Fin 2) (Fin 2) A) * g = g * y := congrArg Units.val hy
  exact Units.ext (commute_of_mul_eq_mul_of_mul_eq_mul hg hx' hy').eq

private theorem isMulCommutative_centralizer_of_isRegularSemisimple {g : GL (Fin 2) A}
    (hg : IsRegularSemisimple g) :
    IsMulCommutative (Subgroup.centralizer ({g} : Set (GL (Fin 2) A))) :=
  ⟨⟨fun x y => Subtype.ext (commute_of_mem_centralizer_of_isRegularSemisimple hg x.2 y.2).eq⟩⟩

end Ring

private theorem isMulCommutative_localCentralizer (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {γ : GL (Fin 2) (v.adicCompletion K)} (hγ : IsRegularSemisimple γ) :
    IsMulCommutative (localCentralizer K v γ) :=
  isMulCommutative_centralizer_of_isRegularSemisimple hγ

end RegularCentralizer

end

section

open AutomorphicForm
open scoped TensorProduct

namespace RegularCentralizer

section Generic

variable {G : Type*} [Group G]

private theorem mul_prod_range_iterate (f : G →* G) {t δ : G} (h : t * δ = δ * f t) (n : ℕ) :
    t * ((List.range n).map fun i => (⇑f)^[i] δ).prod =
      ((List.range n).map fun i => (⇑f)^[i] δ).prod * (⇑f)^[n] t := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.map_singleton, List.prod_append, List.prod_cons,
      List.prod_nil, mul_one, ← mul_assoc, ih, mul_assoc, mul_assoc, Function.iterate_succ_apply]
    congr 1
    have h' := congrArg ((⇑f)^[n]) h
    rwa [iterate_map_mul, iterate_map_mul] at h'

end Generic

section Twisted

variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]

private theorem twistedCentralizer_le_centralizer_normString_of_iterate (σ : L ≃ₐ[K] L)
    (hσ : ∀ t : GL (Fin 2) (L ⊗[K] A), (⇑(sigmaGL K L A σ))^[Module.finrank K L] t = t)
    (δ : GL (Fin 2) (L ⊗[K] A)) :
    twistedCentralizer K L A σ δ ≤
      Subgroup.centralizer ({normString K L A σ δ} : Set (GL (Fin 2) (L ⊗[K] A))) := by
  intro t ht
  rw [Subgroup.mem_centralizer_singleton_iff]
  have ht' : t * δ * (sigmaGL K L A σ t)⁻¹ = δ := ht
  have key := mul_prod_range_iterate (sigmaGL K L A σ) (mul_inv_eq_iff_eq_mul.mp ht')
    (Module.finrank K L)
  rw [hσ t] at key
  exact key

private theorem sigmaTensor_mul_apply (σ σ' : L ≃ₐ[K] L) (z : L ⊗[K] A) :
    sigmaTensor K L A (σ * σ') z = sigmaTensor K L A σ (sigmaTensor K L A σ' z) := by
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro l a
    simp [sigmaTensor, Algebra.TensorProduct.map_tmul, AlgEquiv.mul_apply]
  · intro x y hx hy
    simp only [map_add, hx, hy]

private theorem sigmaTensor_one_apply (z : L ⊗[K] A) : sigmaTensor K L A 1 z = z := by
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro l a
    simp [sigmaTensor, Algebra.TensorProduct.map_tmul, AlgEquiv.one_apply]
  · intro x y hx hy
    simp only [map_add, hx, hy]

private theorem sigmaGL_mul_apply (σ σ' : L ≃ₐ[K] L) (g : GL (Fin 2) (L ⊗[K] A)) :
    sigmaGL K L A (σ * σ') g = sigmaGL K L A σ (sigmaGL K L A σ' g) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  show Matrix.GeneralLinearGroup.map (sigmaTensor K L A (σ * σ')) g i j =
    Matrix.GeneralLinearGroup.map (sigmaTensor K L A σ)
      (Matrix.GeneralLinearGroup.map (sigmaTensor K L A σ') g) i j
  simp only [Matrix.GeneralLinearGroup.map_apply, sigmaTensor_mul_apply]

private theorem sigmaGL_one_apply (g : GL (Fin 2) (L ⊗[K] A)) : sigmaGL K L A 1 g = g := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  show Matrix.GeneralLinearGroup.map (sigmaTensor K L A 1) g i j = g i j
  simp only [Matrix.GeneralLinearGroup.map_apply, sigmaTensor_one_apply]

private theorem sigmaGL_iterate (σ : L ≃ₐ[K] L) (n : ℕ) (g : GL (Fin 2) (L ⊗[K] A)) :
    (⇑(sigmaGL K L A σ))^[n] g = sigmaGL K L A (σ ^ n) g := by
  induction n with
  | zero => simp [sigmaGL_one_apply]
  | succ n ih => rw [Function.iterate_succ_apply', ih, pow_succ', sigmaGL_mul_apply]

private theorem pow_finrank_eq_one [FiniteDimensional K L] (σ : L ≃ₐ[K] L) : σ ^ Module.finrank K L = 1 := by
  rw [← orderOf_dvd_iff_pow_eq_one, ← Nat.card_zpowers, ← IntermediateField.finrank_fixedField_eq_card]
  exact Dvd.intro_left _
    (Module.finrank_mul_finrank K (IntermediateField.fixedField (Subgroup.zpowers σ)) L)

private theorem sigmaGL_iterate_finrank [FiniteDimensional K L] (σ : L ≃ₐ[K] L)
    (g : GL (Fin 2) (L ⊗[K] A)) : (⇑(sigmaGL K L A σ))^[Module.finrank K L] g = g := by
  rw [sigmaGL_iterate, pow_finrank_eq_one, sigmaGL_one_apply]

private theorem twistedCentralizer_le_centralizer_normString [FiniteDimensional K L] (σ : L ≃ₐ[K] L)
    (δ : GL (Fin 2) (L ⊗[K] A)) :
    twistedCentralizer K L A σ δ ≤
      Subgroup.centralizer ({normString K L A σ δ} : Set (GL (Fin 2) (L ⊗[K] A))) :=
  twistedCentralizer_le_centralizer_normString_of_iterate K L A σ
    (sigmaGL_iterate_finrank K L A σ) δ

end Twisted

end RegularCentralizer

end

section

open NumberField IsDedekindDomain MeasureTheory TopologicalSpace TensorProduct Topology
open scoped TensorProduct.RightActions
open AutomorphicForm

namespace OrbitalCarriers

section GLCarrier

variable (A : Type) [CommRing A] [TopologicalSpace A]

private theorem secondCountableTopology_gl [SecondCountableTopology A] :
    SecondCountableTopology (GL (Fin 2) A) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) A) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → A))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) A)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
  exact Units.isInducing_embedProduct.secondCountableTopology

private theorem locallyCompactSpace_gl [IsTopologicalRing A] [T2Space A] [LocallyCompactSpace A] :
    LocallyCompactSpace (GL (Fin 2) A) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) A) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → A))
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) A) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → A))
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

private theorem sigmaCompactSpace_gl [IsTopologicalRing A] [T2Space A] [LocallyCompactSpace A]
    [SecondCountableTopology A] : SigmaCompactSpace (GL (Fin 2) A) := by
  haveI := locallyCompactSpace_gl A
  haveI := secondCountableTopology_gl A
  exact sigmaCompactSpace_of_locallyCompact_secondCountable

private theorem isClosed_centralizer [IsTopologicalRing A] [T2Space A] (γ : GL (Fin 2) A) :
    IsClosed ((Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) : Subgroup (GL (Fin 2) A)) :
      Set (GL (Fin 2) A)) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) A) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → A))
  haveI : T2Space (GL (Fin 2) A) := Units.isEmbedding_embedProduct.t2Space
  have h : ((Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) : Subgroup (GL (Fin 2) A)) :
      Set (GL (Fin 2) A)) = {x | x * γ = γ * x} := by
    ext x
    exact Subgroup.mem_centralizer_singleton_iff
  rw [h]
  exact isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)

end GLCarrier

section TwistedClosed

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
  (σ : L ≃ₐ[K] L)

private theorem isClosed_twistedCentralizer (hσc : Continuous (sigmaGL K L A σ))
    (δ : GL (Fin 2) (L ⊗[K] A)) :
    IsClosed ((twistedCentralizer K L A σ δ : Subgroup (GL (Fin 2) (L ⊗[K] A))) :
      Set (GL (Fin 2) (L ⊗[K] A))) := by
  haveI := isTopologicalRing_tensor K L A
  haveI := t2Space_tensorGL K L A
  have h : ((twistedCentralizer K L A σ δ : Subgroup (GL (Fin 2) (L ⊗[K] A))) :
      Set (GL (Fin 2) (L ⊗[K] A))) = {t | t * δ * (sigmaGL K L A σ t)⁻¹ = δ} := by
    ext t
    exact mem_sigmaCentralizer_iff
  rw [h]
  exact isClosed_eq ((continuous_id.mul continuous_const).mul hσc.inv) continuous_const

end TwistedClosed

section Torus

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G]

private theorem regular_of_isHaarMeasure_of_isClosed (T : Subgroup G) (hT : IsClosed (T : Set G))
    (τ : @Measure T (borel T)) (hτ : @Measure.IsHaarMeasure T _ _ (borel T) τ) :
    @Measure.Regular T (borel T) _ τ := by
  letI : MeasurableSpace T := borel T
  haveI : BorelSpace T := ⟨rfl⟩
  haveI : LocallyCompactSpace T := hT.locallyCompactSpace
  haveI : SecondCountableTopology T := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  haveI : SigmaCompactSpace T := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI := hτ
  obtain ⟨C, hC, hC1⟩ := exists_compact_mem_nhds (1 : T)
  exact Measure.regular_of_isMulLeftInvariant hC ⟨1, mem_interior_iff_mem_nhds.2 hC1⟩
    hC.measure_lt_top.ne

open scoped IsMulCommutative in
private theorem isInvInvariant_of_isHaarMeasure_of_isClosed (T : Subgroup G) (hT : IsClosed (T : Set G))
    (hcomm : IsMulCommutative T) (τ : @Measure T (borel T))
    (hτ : @Measure.IsHaarMeasure T _ _ (borel T) τ) : @Measure.IsInvInvariant T (borel T) _ τ := by
  letI : MeasurableSpace T := borel T
  haveI : BorelSpace T := ⟨rfl⟩
  haveI : LocallyCompactSpace T := hT.locallyCompactSpace
  haveI : SecondCountableTopology T := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  haveI := hτ
  haveI := hcomm
  haveI := regular_of_isHaarMeasure_of_isClosed T hT τ hτ
  exact Measure.IsHaarMeasure.isInvInvariant_of_regular τ

omit [IsTopologicalGroup G] in
private theorem sfinite_of_isHaarMeasure_of_isClosed (T : Subgroup G) (hT : IsClosed (T : Set G))
    (τ : @Measure T (borel T)) (hτ : @Measure.IsHaarMeasure T _ _ (borel T) τ) :
    @SFinite T (borel T) τ := by
  letI : MeasurableSpace T := borel T
  haveI : BorelSpace T := ⟨rfl⟩
  haveI : LocallyCompactSpace T := hT.locallyCompactSpace
  haveI : SecondCountableTopology T := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  haveI : SigmaCompactSpace T := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI := hτ
  infer_instance

end Torus

section Consumers

variable (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
  [LocallyCompactSpace A] [SecondCountableTopology A]

private theorem isOrbitalIntegralOn_unique (μ : @Measure (GL (Fin 2) A) (glBorelOf A))
    (hμ : @Measure.IsHaarMeasure _ _ _ (glBorelOf A) μ) (γ : GL (Fin 2) A)
    (hcomm : IsMulCommutative (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))))
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (centralizerBorel A γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel A γ) τ) (f : GL (Fin 2) A → ℂ)
    (hf : @Measurable _ _ (glBorelOf A) _ f) {I I' : ℂ} (hI : IsOrbitalIntegralOn A μ γ τ f I)
    (hI' : IsOrbitalIntegralOn A μ γ τ f I') : I = I' := by
  letI : MeasurableSpace (GL (Fin 2) A) := glBorelOf A
  haveI : BorelSpace (GL (Fin 2) A) := borelSpace_glBorelOf A
  haveI := locallyCompactSpace_gl A
  haveI := secondCountableTopology_gl A
  haveI := sigmaCompactSpace_gl A
  haveI := hμ
  set T : Subgroup (GL (Fin 2) A) := Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))
  have hTc : IsClosed (T : Set (GL (Fin 2) A)) := isClosed_centralizer A γ
  letI : MeasurableSpace T := centralizerBorel A γ
  haveI : BorelSpace T := ⟨rfl⟩
  haveI : @SFinite T (borel T) τ := sfinite_of_isHaarMeasure_of_isClosed T hTc τ hτ
  haveI : @Measure.IsInvInvariant T (borel T) _ τ :=
    isInvInvariant_of_isHaarMeasure_of_isClosed T hTc hcomm τ hτ
  obtain ⟨w, ⟨hw0, hwm, -, hw1⟩, rfl⟩ := hI
  obtain ⟨w', ⟨hw0', hwm', -, hw1'⟩, rfl⟩ := hI'
  have hcont : Continuous fun x : GL (Fin 2) A => x⁻¹ * γ * x :=
    (continuous_inv.mul continuous_const).mul continuous_id
  have hFT : ∀ (t : T) (x : GL (Fin 2) A),
      f (((t : GL (Fin 2) A) * x)⁻¹ * γ * ((t : GL (Fin 2) A) * x)) = f (x⁻¹ * γ * x) := by
    intro t x
    have ht : (t : GL (Fin 2) A) * γ = γ * t := Subgroup.mem_centralizer_singleton_iff.1 t.2
    have hconj : ((t : GL (Fin 2) A))⁻¹ * γ * t = γ := by
      rw [mul_assoc, ← ht, inv_mul_cancel_left]
    congr 1
    calc ((t : GL (Fin 2) A) * x)⁻¹ * γ * ((t : GL (Fin 2) A) * x)
        = x⁻¹ * (((t : GL (Fin 2) A))⁻¹ * γ * t) * x := by simp only [mul_inv_rev, mul_assoc]
      _ = x⁻¹ * γ * x := by rw [hconj]
  exact integral_mul_eq_integral_mul_of_forall_integral_subgroup_mul_eq_one μ T
    continuous_subtype_val.measurable τ (fun x => f (x⁻¹ * γ * x)) (hf.comp hcont.measurable) hFT
    w w' hw0 hw0' hwm hwm' hw1 hw1'

end Consumers

section TwistedConsumer

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
  [LocallyCompactSpace A] (σ : L ≃ₐ[K] L)

private theorem isTwistedOrbitalIntegralOn_unique (hsc : SecondCountableTopology (L ⊗[K] A))
    (μ : @Measure (GL (Fin 2) (L ⊗[K] A)) (glBorelOf (L ⊗[K] A)))
    (hμ : @Measure.IsHaarMeasure _ _ _ (glBorelOf (L ⊗[K] A)) μ) (δ : GL (Fin 2) (L ⊗[K] A))
    (hσc : Continuous (sigmaGL K L A σ))
    (hcomm : IsMulCommutative (twistedCentralizer K L A σ δ))
    (τ' : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L A σ δ) τ')
    (φ : GL (Fin 2) (L ⊗[K] A) → ℂ) (hφ : @Measurable _ _ (glBorelOf (L ⊗[K] A)) _ φ) {I I' : ℂ}
    (hI : IsTwistedOrbitalIntegralOn K L A σ μ δ τ' φ I)
    (hI' : IsTwistedOrbitalIntegralOn K L A σ μ δ τ' φ I') : I = I' := by
  haveI := isTopologicalRing_tensor K L A
  haveI := t2Space_tensor K L A
  haveI := locallyCompactSpace_tensor K L A
  haveI := hsc
  letI : MeasurableSpace (GL (Fin 2) (L ⊗[K] A)) := glBorelOf (L ⊗[K] A)
  haveI : BorelSpace (GL (Fin 2) (L ⊗[K] A)) := borelSpace_glBorelOf (L ⊗[K] A)
  haveI := locallyCompactSpace_gl (L ⊗[K] A)
  haveI := secondCountableTopology_gl (L ⊗[K] A)
  haveI := sigmaCompactSpace_gl (L ⊗[K] A)
  haveI := hμ
  have hclosed := isClosed_twistedCentralizer K L A σ hσc δ
  set T : Subgroup (GL (Fin 2) (L ⊗[K] A)) := twistedCentralizer K L A σ δ
  letI : MeasurableSpace T := twistedCentralizerBorel K L A σ δ
  haveI : BorelSpace T := ⟨rfl⟩
  haveI : @SFinite T (borel T) τ' := sfinite_of_isHaarMeasure_of_isClosed T hclosed τ' hτ'
  haveI : @Measure.IsInvInvariant T (borel T) _ τ' :=
    isInvInvariant_of_isHaarMeasure_of_isClosed T hclosed hcomm τ' hτ'
  obtain ⟨w, ⟨hw0, hwm, -, hw1⟩, rfl⟩ := hI
  obtain ⟨w', ⟨hw0', hwm', -, hw1'⟩, rfl⟩ := hI'
  have hcont : Continuous fun x : GL (Fin 2) (L ⊗[K] A) => x⁻¹ * δ * sigmaGL K L A σ x :=
    (continuous_inv.mul continuous_const).mul hσc
  have hFT : ∀ (t : T) (x : GL (Fin 2) (L ⊗[K] A)),
      φ (((t : GL (Fin 2) (L ⊗[K] A)) * x)⁻¹ * δ * sigmaGL K L A σ ((t : GL (Fin 2) (L ⊗[K] A)) * x))
        = φ (x⁻¹ * δ * sigmaGL K L A σ x) := by
    intro t x
    have ht : ((t : GL (Fin 2) (L ⊗[K] A)))⁻¹ * δ * sigmaGL K L A σ t = δ :=
      mem_sigmaCentralizer_iff_inv.1 t.2
    congr 1
    calc ((t : GL (Fin 2) (L ⊗[K] A)) * x)⁻¹ * δ * sigmaGL K L A σ ((t : GL (Fin 2) (L ⊗[K] A)) * x)
        = x⁻¹ * (((t : GL (Fin 2) (L ⊗[K] A)))⁻¹ * δ * sigmaGL K L A σ t) * sigmaGL K L A σ x := by
          simp only [map_mul, mul_inv_rev, mul_assoc]
      _ = x⁻¹ * δ * sigmaGL K L A σ x := by rw [ht]
  exact integral_mul_eq_integral_mul_of_forall_integral_subgroup_mul_eq_one μ T
    continuous_subtype_val.measurable τ' (fun x => φ (x⁻¹ * δ * sigmaGL K L A σ x))
    (hφ.comp hcont.measurable) hFT w w' hw0 hw0' hwm hwm' hw1 hw1'

end TwistedConsumer

section ProductReceipt

variable (A : Type) [CommRing A] [TopologicalSpace A] [SecondCountableTopology A]

private theorem borelSpace_pi_gl (m : ℕ) :
    @BorelSpace (Fin m → GL (Fin 2) A) _ (@MeasurableSpace.pi _ _ fun _ => glBorelOf A) := by
  letI : MeasurableSpace (GL (Fin 2) A) := glBorelOf A
  haveI := borelSpace_glBorelOf A
  haveI := secondCountableTopology_gl A
  infer_instance

end ProductReceipt

section FiniteCarriers

open NumberField IsDedekindDomain

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (σ : L ≃ₐ[K] L)

private theorem isOrbitalIntegralOn_localHaar_unique (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : IsRegularSemisimple γ) (τ : @Measure (localCentralizer K v γ) (localCentralizerBorel K v γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (localCentralizerBorel K v γ) τ)
    (fv : GL (Fin 2) (v.adicCompletion K) → ℂ) (hf : @Measurable _ _ (localGLBorel K v) _ fv) {I I' : ℂ}
    (hI : IsOrbitalIntegralOn (v.adicCompletion K) (localHaar K v) γ τ fv I)
    (hI' : IsOrbitalIntegralOn (v.adicCompletion K) (localHaar K v) γ τ fv I') : I = I' :=
  isOrbitalIntegralOn_unique (v.adicCompletion K) (localHaar K v) (isHaarMeasure_localHaar K v) γ
    (RegularCentralizer.isMulCommutative_localCentralizer K v hγ) τ hτ fv hf hI hI'

private theorem secondCountableTopology_semiLocal : SecondCountableTopology (L ⊗[K] v.adicCompletion K) := by
  haveI := HeightOneSpectrum.Extension.finite (𝓞 K) K L (𝓞 L) v
  exact (semiLocalHomeomorph K L v).isEmbedding.secondCountableTopology

private theorem isTwistedOrbitalIntegralOn_semiLocalHaar_unique
    (hσc : Continuous (sigmaGL K L (v.adicCompletion K) σ)) (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hcomm : IsMulCommutative (twistedCentralizer K L (v.adicCompletion K) σ δ))
    (τ' : @Measure (twistedCentralizer K L (v.adicCompletion K) σ δ)
      (twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ')
    (φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (hφ : @Measurable _ _ (glBorelOf (L ⊗[K] v.adicCompletion K)) _ φv) {I I' : ℂ}
    (hI : IsTwistedOrbitalIntegralOn K L (v.adicCompletion K) σ (semiLocalHaar K L v) δ τ' φv I)
    (hI' : IsTwistedOrbitalIntegralOn K L (v.adicCompletion K) σ (semiLocalHaar K L v) δ τ' φv I') : I = I' :=
  isTwistedOrbitalIntegralOn_unique K L (v.adicCompletion K) σ (secondCountableTopology_semiLocal K L v)
    (semiLocalHaar K L v) (isHaarMeasure_semiLocalHaar K L v) δ hσc hcomm τ' hτ' φv hφ hI hI'

end FiniteCarriers

section ArchCarriers

open NumberField

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]

private theorem secondCountableTopology_infiniteAdeleRing : SecondCountableTopology (InfiniteAdeleRing K) := by
  haveI : ∀ w : InfinitePlace K, SecondCountableTopology w.Completion := fun w =>
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  exact inferInstanceAs (SecondCountableTopology ((w : InfinitePlace K) → w.Completion))

private theorem secondCountableTopology_archGL : SecondCountableTopology (GL (Fin 2) (InfiniteAdeleRing K)) := by
  haveI := secondCountableTopology_infiniteAdeleRing K
  exact secondCountableTopology_gl (InfiniteAdeleRing K)

private theorem isHaarMeasure_archHaarK :
    @Measure.IsHaarMeasure _ _ _ (glBorelOf (InfiniteAdeleRing K)) (archHaarK K) := by
  letI := glBorelOf (InfiniteAdeleRing K)
  haveI := borelSpace_glBorelOf (InfiniteAdeleRing K)
  haveI := locallyCompactSpace_gl (InfiniteAdeleRing K)
  unfold archHaarK
  infer_instance

private theorem isHaarMeasure_archHaarL :
    @Measure.IsHaarMeasure _ _ _ (glBorelOf (L ⊗[K] InfiniteAdeleRing K)) (archHaarL K L) := by
  letI := glBorelOf (L ⊗[K] InfiniteAdeleRing K)
  haveI := borelSpace_glBorelOf (L ⊗[K] InfiniteAdeleRing K)
  haveI := isTopologicalGroup_tensorGL K L (InfiniteAdeleRing K)
  haveI := locallyCompactSpace_tensorGL K L (InfiniteAdeleRing K)
  unfold archHaarL
  infer_instance

end ArchCarriers

end OrbitalCarriers

end

section

open MeasureTheory

namespace HaarScalar

section Generic

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
variable {ι : Type*} [Fintype ι] {H : ι → Type*} [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)]
  [∀ i, IsTopologicalGroup (H i)] [∀ i, MeasurableSpace (H i)] [∀ i, BorelSpace (H i)]
  [∀ i, LocallyCompactSpace (H i)] [∀ i, SecondCountableTopology (H i)]

private theorem exists_map_eq_smul_pi (μ : Measure G) [μ.IsHaarMeasure] (ν : ∀ i, Measure (H i))
    [∀ i, (ν i).IsHaarMeasure] (Θ : G ≃* (∀ i, H i)) (hΘ : Continuous Θ) (hΘs : Continuous Θ.symm) :
    ∃ c : NNReal, c ≠ 0 ∧ Measure.map Θ μ = c • Measure.pi ν := by
  haveI : (Measure.map Θ μ).IsHaarMeasure := Θ.isHaarMeasure_map μ hΘ hΘs
  exact ⟨Measure.haarScalarFactor (Measure.map Θ μ) (Measure.pi ν),
    (Measure.haarScalarFactor_pos_of_isHaarMeasure _ _).ne',
    Measure.isMulLeftInvariant_eq_smul _ _⟩

end Generic

section Instance

open NumberField IsDedekindDomain AutomorphicForm
open scoped TensorProduct
open scoped TensorProduct.RightActions

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K))

private noncomputable local instance instBorelSemiLocal : MeasurableSpace (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :=
  glBorelOf (L ⊗[K] v.adicCompletion K)

private noncomputable local instance instBorelLocal :
    MeasurableSpace (GL (Fin 2) (v.adicCompletion K)) := localGLBorel K v

private theorem exists_map_semiLocalHaar_eq_smul_pi_localHaar (p : ℕ)
    [SecondCountableTopology (GL (Fin 2) (v.adicCompletion K))]
    (Θ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) ≃* (Fin p → GL (Fin 2) (v.adicCompletion K)))
    (hΘ : Continuous Θ) (hΘs : Continuous Θ.symm) :
    ∃ c : NNReal, c ≠ 0 ∧
      Measure.map Θ (semiLocalHaar K L v) = c • Measure.pi (fun _ : Fin p => localHaar K v) := by
  exact @exists_map_eq_smul_pi _ _ _ (isTopologicalGroup_tensorGL K L (v.adicCompletion K))
    (glBorelOf (L ⊗[K] v.adicCompletion K)) (borelSpace_glBorelOf (L ⊗[K] v.adicCompletion K))
    (Fin p) _ (fun _ => GL (Fin 2) (v.adicCompletion K)) _ _ _
    (fun _ => localGLBorel K v) (fun _ => borelSpace_localGLBorel K v) (fun _ => locallyCompactSpace_localGL K v)
    (fun _ => inferInstance)
    (semiLocalHaar K L v) (isHaarMeasure_semiLocalHaar K L v)
    (fun _ => localHaar K v) (fun _ => isHaarMeasure_localHaar K v) Θ hΘ hΘs

end Instance

end HaarScalar

end

section

open MeasureTheory Topology AutomorphicForm
open scoped TensorProduct
open scoped TensorProduct.RightActions

namespace CentralizerEmbedding

section Embed

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]

private theorem continuous_algebraMap_tensor : Continuous (algebraMap A (L ⊗[K] A)) :=
  IsModuleTopology.continuous_of_linearMap (Algebra.linearMap A (L ⊗[K] A))

omit [FiniteDimensional K L] [TopologicalSpace A] [IsTopologicalRing A] in
private theorem coe_toTensorGL (g : GL (Fin 2) A) :
    ((toTensorGL K L A g : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A))
      = (g : Matrix (Fin 2) (Fin 2) A).map (algebraMap A (L ⊗[K] A)) := by
  ext i j
  simp [toTensorGL, Matrix.GeneralLinearGroup.map_apply, TensorProduct.RightActions.algebraMap_eval]

private theorem continuous_toTensorGL : Continuous (toTensorGL K L A) := by
  rw [Units.continuous_iff]
  refine ⟨?_, ?_⟩
  · have h : (Units.val ∘ toTensorGL K L A) =
        fun g : GL (Fin 2) A => (g : Matrix (Fin 2) (Fin 2) A).map (algebraMap A (L ⊗[K] A)) :=
      funext fun g => coe_toTensorGL K L A g
    rw [h]
    exact Units.continuous_val.matrix_map (continuous_algebraMap_tensor K L A)
  · have h : (fun g : GL (Fin 2) A => ((toTensorGL K L A g)⁻¹ : GL (Fin 2) (L ⊗[K] A)).val) =
        fun g : GL (Fin 2) A => ((g⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A).map (algebraMap A (L ⊗[K] A)) :=
      funext fun g => by rw [← map_inv, coe_toTensorGL]
    rw [h]
    exact Units.continuous_coe_inv.matrix_map (continuous_algebraMap_tensor K L A)

private theorem measurable_toTensorGL :
    @Measurable _ _ (glBorelOf A) (glBorelOf (L ⊗[K] A)) (toTensorGL K L A) := by
  letI := glBorelOf A
  letI := glBorelOf (L ⊗[K] A)
  haveI := borelSpace_glBorelOf A
  haveI := borelSpace_glBorelOf (L ⊗[K] A)
  exact (continuous_toTensorGL K L A).measurable

private theorem measurableEmbedding_conj (y : GL (Fin 2) (L ⊗[K] A)) :
    @MeasurableEmbedding _ _ (glBorelOf (L ⊗[K] A)) (glBorelOf (L ⊗[K] A))
      (fun t : GL (Fin 2) (L ⊗[K] A) => y⁻¹ * t * y) := by
  letI := glBorelOf (L ⊗[K] A)
  haveI := borelSpace_glBorelOf (L ⊗[K] A)
  haveI := isTopologicalGroup_tensorGL K L A
  exact ((Homeomorph.mulLeft y⁻¹).trans (Homeomorph.mulRight y)).measurableEmbedding

end Embed

section Tori

variable (A : Type) [CommRing A] [TopologicalSpace A]

private theorem measurableEmbedding_centralizer_val (γ : GL (Fin 2) A)
    (hc : IsClosed ((Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) : Subgroup (GL (Fin 2) A)) :
      Set (GL (Fin 2) A))) :
    @MeasurableEmbedding _ _ (centralizerBorel A γ) (glBorelOf A)
      ((↑) : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) → GL (Fin 2) A) := by
  letI := glBorelOf A
  letI := centralizerBorel A γ
  haveI := borelSpace_glBorelOf A
  haveI : BorelSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) := ⟨rfl⟩
  have he : IsClosedEmbedding ((↑) : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) → GL (Fin 2) A) :=
    hc.isClosedEmbedding_subtypeVal
  exact he.measurableEmbedding

end Tori

section TwistedTori

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] (σ : L ≃ₐ[K] L)

private theorem measurableEmbedding_twistedCentralizer_val (δ : GL (Fin 2) (L ⊗[K] A))
    (hc : IsClosed ((twistedCentralizer K L A σ δ : Subgroup (GL (Fin 2) (L ⊗[K] A))) :
      Set (GL (Fin 2) (L ⊗[K] A)))) :
    @MeasurableEmbedding _ _ (twistedCentralizerBorel K L A σ δ) (glBorelOf (L ⊗[K] A))
      ((↑) : twistedCentralizer K L A σ δ → GL (Fin 2) (L ⊗[K] A)) := by
  letI := glBorelOf (L ⊗[K] A)
  letI := twistedCentralizerBorel K L A σ δ
  haveI := borelSpace_glBorelOf (L ⊗[K] A)
  haveI : BorelSpace (twistedCentralizer K L A σ δ) := ⟨rfl⟩
  have he : IsClosedEmbedding ((↑) : twistedCentralizer K L A σ δ → GL (Fin 2) (L ⊗[K] A)) :=
    hc.isClosedEmbedding_subtypeVal
  exact he.measurableEmbedding

end TwistedTori

end CentralizerEmbedding

end

section

open MeasureTheory NumberField

open scoped TensorProduct
open scoped TensorProduct.RightActions

namespace CoupledProjection

section Main

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] (σ : L ≃ₐ[K] L)

open AutomorphicForm in
private theorem map_conj_eq_map_val_of_coupled (γ : GL (Fin 2) A) (δ y : GL (Fin 2) (L ⊗[K] A))
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (centralizerBorel A γ))
    (τ' : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ))
    (hc : Coupled K L A σ γ δ y τ τ')
    (ρ : GL (Fin 2) (L ⊗[K] A) → GL (Fin 2) A)
    (hρ : @Measurable _ _ (glBorelOf (L ⊗[K] A)) (glBorelOf A) ρ)
    (hρi : ∀ s : GL (Fin 2) A, ρ (toTensorGL K L A s) = s)
    (hρy : ∀ g, ρ (y⁻¹ * g * y) = (ρ y)⁻¹ * ρ g * ρ y)
    (hval' : @Measurable _ _ (twistedCentralizerBorel K L A σ δ) (glBorelOf (L ⊗[K] A))
      (fun t : twistedCentralizer K L A σ δ => (t : GL (Fin 2) (L ⊗[K] A))))
    (hval : @Measurable _ _ (centralizerBorel A γ) (glBorelOf A)
      (fun s : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) => (s : GL (Fin 2) A)))
    (htor : @Measurable _ _ (glBorelOf A) (glBorelOf (L ⊗[K] A)) (toTensorGL K L A)) :
    @Measure.map _ _ (twistedCentralizerBorel K L A σ δ) (glBorelOf A)
        (fun t : twistedCentralizer K L A σ δ => (ρ y)⁻¹ * ρ (t : GL (Fin 2) (L ⊗[K] A)) * ρ y) τ' =
      @Measure.map _ _ (centralizerBorel A γ) (glBorelOf A)
        (fun s : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) => (s : GL (Fin 2) A)) τ := by
  letI := glBorelOf (L ⊗[K] A)
  letI := glBorelOf A
  letI := centralizerBorel A γ
  letI := twistedCentralizerBorel K L A σ δ
  haveI : BorelSpace (GL (Fin 2) (L ⊗[K] A)) := borelSpace_glBorelOf (L ⊗[K] A)
  haveI := isTopologicalGroup_tensorGL K L A
  have hconj : Measurable (fun t : twistedCentralizer K L A σ δ => y⁻¹ * (t : GL (Fin 2) (L ⊗[K] A)) * y) :=
    (hval'.const_mul y⁻¹).mul_const y
  dsimp only [Coupled] at hc
  have h := congrArg (Measure.map ρ) hc
  have hts : Measurable (fun s : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) =>
      toTensorGL K L A (s : GL (Fin 2) A)) := htor.comp hval
  rw [Measure.map_map hρ hconj, Measure.map_map hρ hts] at h
  convert h using 2 <;> funext t <;> simp only [Function.comp_def, hρy, hρi]

end Main

end CoupledProjection

end

section

open MeasureTheory Topology Filter

namespace FibreIntegralTestClass

open TwistedShift

section Alg

variable {G : Type} [Group G]

private def proj (n : ℕ) (y : Fin (n + 1) → G) : G := (List.ofFn (Fin.init y)).prod * y (Fin.last n)

private theorem proj_snoc (n : ℕ) (c : Fin n → G) (h : G) :
    proj n (Fin.snoc c ((List.ofFn c).prod⁻¹ * h) : Fin (n + 1) → G) = h := by
  simp only [proj, Fin.init_snoc, Fin.snoc_last, mul_inv_cancel_left]

private theorem snoc_mul_mulSingle (n : ℕ) (c : Fin n → G) (a u : G) :
    (Fin.snoc c a : Fin (n + 1) → G) * Pi.mulSingle (Fin.last n) u = Fin.snoc c (a * u) := by
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [Pi.mul_apply, Fin.snoc_last, Pi.mulSingle_eq_same]
  · simp only [Pi.mul_apply, Fin.snoc_castSucc, Pi.mulSingle_eq_of_ne (Fin.castSucc_lt_last i).ne, mul_one]

end Alg

section NormCast

variable {G : Type} [TopologicalSpace G] {n : ℕ} {Φ : (Fin (n + 1) → G) → ℂ}

private theorem isLocallyConstant_norm_cast (hΦ : IsLocallyConstant Φ) :
    IsLocallyConstant fun y => (‖Φ y‖ : ℂ) :=
  hΦ.comp fun z => ((‖z‖ : ℝ) : ℂ)

private theorem hasCompactSupport_norm_cast (hc : HasCompactSupport Φ) :
    HasCompactSupport fun y => (‖Φ y‖ : ℂ) :=
  hc.comp_left (g := fun z : ℂ => ((‖z‖ : ℝ) : ℂ)) (by simp)

end NormCast

section Top

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

private theorem continuous_ofFn_prod (n : ℕ) : Continuous fun c : Fin n → G => (List.ofFn c).prod := by
  simp only [List.ofFn_eq_map]
  exact continuous_list_prod _ fun i _ => continuous_apply i

private theorem continuous_proj (n : ℕ) : Continuous (proj (G := G) n) := by
  unfold proj
  have h1 : Continuous fun y : Fin (n + 1) → G => Fin.init y :=
    continuous_pi fun i => continuous_apply (Fin.castSucc i)
  exact ((continuous_ofFn_prod n).comp h1).mul (continuous_apply (Fin.last n))

private theorem continuous_fibrePoint (n : ℕ) (h : G) :
    Continuous fun c : Fin n → G => (Fin.snoc c ((List.ofFn c).prod⁻¹ * h) : Fin (n + 1) → G) := by
  refine continuous_pi fun j => ?_
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [Fin.snoc_last]
    exact ((continuous_ofFn_prod n).inv).mul continuous_const
  · simp only [Fin.snoc_castSucc]
    exact continuous_apply i

section Fib

variable [MeasurableSpace G] (μ : Measure G) {n : ℕ} {Φ : (Fin (n + 1) → G) → ℂ}

private theorem hasCompactSupport_fib (hc : HasCompactSupport Φ) : HasCompactSupport (fib μ Φ) := by
  refine HasCompactSupport.intro (IsCompact.image hc (continuous_proj n)) fun h hh => ?_
  have hzero : (fun c : Fin n → G => Φ (Fin.snoc c ((List.ofFn c).prod⁻¹ * h))) = fun _ => 0 := by
    funext c
    by_contra hne
    exact hh ⟨_, subset_closure (Function.mem_support.2 hne), proj_snoc n c h⟩
  rw [fib, hzero, integral_zero]

private theorem isLocallyConstant_fib (hΦ : IsLocallyConstant Φ) (hc : HasCompactSupport Φ) :
    IsLocallyConstant (fib μ Φ) := by
  obtain ⟨W, hW, hWinv⟩ := RegularCentralizer.exists_mem_nhds_one_forall_mul_eq hΦ hc
  have hU : ∀ᶠ u in 𝓝 (1 : G), (Pi.mulSingle (Fin.last n) u : Fin (n + 1) → G) ∈ W := by
    refine (continuous_mulSingle (A := fun _ : Fin (n + 1) => G) (Fin.last n)).continuousAt.eventually_mem ?_
    show W ∈ 𝓝 (Pi.mulSingle (Fin.last n) (1 : G) : Fin (n + 1) → G)
    rw [Pi.mulSingle_one]
    exact hW
  have hinv : ∀ h u : G, (Pi.mulSingle (Fin.last n) u : Fin (n + 1) → G) ∈ W →
      fib μ Φ (h * u) = fib μ Φ h := by
    intro h u hu
    simp only [fib]
    congr 1
    funext c
    rw [← mul_assoc, ← snoc_mul_mulSingle n c ((List.ofFn c).prod⁻¹ * h) u]
    exact (hWinv _ hu _).2
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun h => ?_
  have ht : Tendsto (fun h' : G => h⁻¹ * h') (𝓝 h) (𝓝 (h⁻¹ * h)) :=
    (continuous_const.mul continuous_id).tendsto h
  rw [inv_mul_cancel] at ht
  filter_upwards [ht.eventually hU] with h' hh'
  calc fib μ Φ h' = fib μ Φ (h * (h⁻¹ * h')) := by rw [mul_inv_cancel_left]
    _ = fib μ Φ h := hinv h _ hh'

private theorem hasCompactSupport_fib_norm (hc : HasCompactSupport Φ) :
    HasCompactSupport (fib μ fun y => (‖Φ y‖ : ℂ)) :=
  hasCompactSupport_fib μ (hasCompactSupport_norm_cast hc)

private theorem isLocallyConstant_fib_norm (hΦ : IsLocallyConstant Φ) (hc : HasCompactSupport Φ) :
    IsLocallyConstant (fib μ fun y => (‖Φ y‖ : ℂ)) :=
  isLocallyConstant_fib μ (isLocallyConstant_norm_cast hΦ) (hasCompactSupport_norm_cast hc)

private theorem measurable_fib [OpensMeasurableSpace G] (hΦ : IsLocallyConstant Φ) (hc : HasCompactSupport Φ) :
    Measurable (fib μ Φ) :=
  (isLocallyConstant_fib μ hΦ hc).continuous.measurable

private theorem fib_norm_ne_zero_of_continuous [SecondCountableTopology G] [OpensMeasurableSpace G] [SigmaFinite μ]
    [μ.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts μ] (hΦ : Continuous Φ) (hc : HasCompactSupport Φ) {h : G}
    {c₀ : Fin n → G} (hne : Φ (Fin.snoc c₀ ((List.ofFn c₀).prod⁻¹ * h)) ≠ 0) :
    fib μ (fun y => (‖Φ y‖ : ℂ)) h ≠ 0 := by
  set g : (Fin n → G) → ℝ := fun c => ‖Φ (Fin.snoc c ((List.ofFn c).prod⁻¹ * h))‖ with hg
  have hgcont : Continuous g := (hΦ.comp (continuous_fibrePoint n h)).norm
  have hinit : Continuous fun y : Fin (n + 1) → G => Fin.init y :=
    continuous_pi fun i => continuous_apply (Fin.castSucc i)
  have hgsupp : HasCompactSupport g := by
    refine HasCompactSupport.intro (IsCompact.image hc hinit) fun c hcnot => ?_
    by_contra hgc
    have hgc' : ‖Φ (Fin.snoc c ((List.ofFn c).prod⁻¹ * h))‖ ≠ 0 := hgc
    exact hcnot ⟨Fin.snoc c ((List.ofFn c).prod⁻¹ * h),
      subset_closure (Function.mem_support.2 (norm_ne_zero_iff.1 hgc')), Fin.init_snoc _ _⟩
  have hgi : Integrable g (Measure.pi fun _ : Fin n => μ) := hgcont.integrable_of_hasCompactSupport hgsupp
  have hg0 : 0 ≤ g := fun c => norm_nonneg _
  have hpos : 0 < ∫ c, g c ∂(Measure.pi fun _ : Fin n => μ) := by
    refine (integral_pos_iff_support_of_nonneg hg0 hgi).2 ?_
    have hopen : IsOpen (Function.support g) := by
      have : Function.support g = g ⁻¹' {0}ᶜ := by
        ext c
        simp [Function.mem_support]
      rw [this]
      exact isOpen_compl_singleton.preimage hgcont
    have hc₀ : g c₀ ≠ 0 := norm_ne_zero_iff.2 hne
    exact hopen.measure_pos _ ⟨c₀, Function.mem_support.2 hc₀⟩
  have hcast : fib μ (fun y => (‖Φ y‖ : ℂ)) h = ((∫ c, g c ∂(Measure.pi fun _ : Fin n => μ) : ℝ) : ℂ) := by
    simp only [fib, hg]
    exact integral_complex_ofReal
  rw [hcast]
  exact_mod_cast hpos.ne'

private theorem fib_norm_ne_zero [SecondCountableTopology G] [OpensMeasurableSpace G] [SigmaFinite μ]
    [μ.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts μ] (hΦ : IsLocallyConstant Φ) (hc : HasCompactSupport Φ) {h : G}
    {c₀ : Fin n → G} (hne : Φ (Fin.snoc c₀ ((List.ofFn c₀).prod⁻¹ * h)) ≠ 0) :
    fib μ (fun y => (‖Φ y‖ : ℂ)) h ≠ 0 :=
  fib_norm_ne_zero_of_continuous μ hΦ.continuous hc hne

end Fib

end Top

end FibreIntegralTestClass

end

section Tail
open AutomorphicForm
open MeasureTheory

private theorem isMulCommutative_of_le {G : Type} [Group G] {H₁ H₂ : Subgroup G} (hle : H₁ ≤ H₂)
    (hc : IsMulCommutative H₂) : IsMulCommutative H₁ :=
  ⟨⟨fun a b => Subtype.ext (congrArg (Subtype.val : H₂ → G)
    (hc.is_comm.comm (⟨a.1, hle a.2⟩ : H₂) ⟨b.1, hle b.2⟩))⟩⟩

section SigmaContinuous

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] (σ : L ≃ₐ[K] L)

omit [IsTopologicalRing A] in
private theorem continuous_sigmaTensor : Continuous (sigmaTensor K L A σ) := by
  have hs : ∀ (a : A) (x : L) (b : A), a • (x ⊗ₜ[K] b : L ⊗[K] A) = x ⊗ₜ (a * b) := by
    intro a x b
    simp only [TensorProduct.RightActions.smul_def, TensorProduct.comm_tmul]
    rw [TensorProduct.smul_tmul']
    simp only [smul_eq_mul, TensorProduct.comm_symm_tmul]
  let f : L ⊗[K] A →ₗ[A] L ⊗[K] A :=
    { toFun := sigmaTensor K L A σ
      map_add' := fun x y => map_add (sigmaTensor K L A σ) x y
      map_smul' := fun a z => by
        rw [RingHom.id_apply]
        induction z with
        | zero => rw [smul_zero, map_zero, smul_zero]
        | tmul x b => rw [hs, SplitModel.sigmaTensor_tmul K L A σ, SplitModel.sigmaTensor_tmul K L A σ, hs]
        | add y w hy hw => rw [smul_add, map_add, map_add, smul_add, hy, hw] }
  exact IsModuleTopology.continuous_of_linearMap f

omit [IsTopologicalRing A] in
private theorem continuous_sigmaGL : Continuous (sigmaGL K L A σ) := by
  rw [Units.continuous_iff]
  exact ⟨Units.continuous_val.matrix_map (continuous_sigmaTensor K L A σ),
    Units.continuous_coe_inv.matrix_map (continuous_sigmaTensor K L A σ)⟩

end SigmaContinuous

namespace SplitMatching

open AutomorphicForm TwistedShift

section Interface

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (σ : L ≃ₐ[K] L) (v : HeightOneSpectrum (𝓞 K))

private structure Model (n : ℕ) where
  Θ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) ≃* (Fin (n + 1) → GL (Fin 2) (v.adicCompletion K))
  continuous_Θ : Continuous Θ
  continuous_symm : Continuous Θ.symm
  Θ_toTensorGL : ∀ g, Θ (toTensorGL K L (v.adicCompletion K) g) = fun _ => g
  Θ_twist : ∀ x δ, Θ (x⁻¹ * δ * sigmaGL K L (v.adicCompletion K) σ x) =
    fun j => (Θ x j)⁻¹ * Θ δ j * Θ x (j + 1)
  Θ_normString : ∀ δ (j : Fin (n + 1)),
    Θ (normString K L (v.adicCompletion K) σ δ) j = (List.ofFn fun k => Θ δ (j + k)).prod

private theorem pow_finrank_eq_one' : σ ^ Module.finrank K L = 1 := by
  rw [← orderOf_dvd_iff_pow_eq_one, ← Nat.card_zpowers, ← IntermediateField.finrank_fixedField_eq_card]
  exact Dvd.intro_left _
    (Module.finrank_mul_finrank K (IntermediateField.fixedField (Subgroup.zpowers σ)) L)

private theorem exists_model (hdeg : (Module.finrank K L).Prime) (hσ : σ ≠ 1)
    (ι : L →ₐ[K] v.adicCompletion K) : ∃ n : ℕ, Nonempty (Model K L σ v n) := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, Module.finrank K L = n + 1 :=
    ⟨Module.finrank K L - 1, (Nat.succ_pred_eq_of_pos hdeg.pos).symm⟩
  have hσ1 : σ ^ (n + 1) = 1 := hn ▸ pow_finrank_eq_one' K L σ
  have hprime : (n + 1).Prime := hn ▸ hdeg
  have hbij := SplitModel.psiL_bijective K L (v.adicCompletion K) ι hn hσ1 hprime hσ
  exact ⟨n, ⟨{ Θ := (SplitModel.Theta K L (v.adicCompletion K) ι hbij).toMulEquiv
               continuous_Θ := map_continuous (SplitModel.Theta K L (v.adicCompletion K) ι hbij)
               continuous_symm := map_continuous (SplitModel.Theta K L (v.adicCompletion K) ι hbij).symm
               Θ_toTensorGL := SplitModel.Theta_toTensorGL K L (v.adicCompletion K) ι hbij
               Θ_twist := SplitModel.Theta_sigmaConj K L (v.adicCompletion K) ι hbij hσ1
               Θ_normString := SplitModel.Theta_normString_apply K L (v.adicCompletion K) ι hbij hn hσ1 }⟩⟩

private theorem secondCountable_localGL : SecondCountableTopology (GL (Fin 2) (v.adicCompletion K)) :=
  OrbitalCarriers.secondCountableTopology_gl (v.adicCompletion K)

private theorem borelSpace_pi (m : ℕ) :
    @BorelSpace (Fin m → GL (Fin 2) (v.adicCompletion K)) _
      (@MeasurableSpace.pi _ _ fun _ => localGLBorel K v) :=
  OrbitalCarriers.borelSpace_pi_gl (v.adicCompletion K) m

private theorem measurable_model {n : ℕ} (M : Model K L σ v n) :
    @Measurable _ _ (glBorelOf (L ⊗[K] v.adicCompletion K))
        (@MeasurableSpace.pi _ _ fun _ => localGLBorel K v) M.Θ ∧
      @Measurable _ _ (@MeasurableSpace.pi _ _ fun _ => localGLBorel K v)
        (glBorelOf (L ⊗[K] v.adicCompletion K)) M.Θ.symm := by
  letI : MeasurableSpace (GL (Fin 2) (v.adicCompletion K)) := localGLBorel K v
  letI : MeasurableSpace (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) := glBorelOf (L ⊗[K] v.adicCompletion K)
  haveI : BorelSpace (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) := borelSpace_glBorelOf _
  haveI : BorelSpace (Fin (n + 1) → GL (Fin 2) (v.adicCompletion K)) := borelSpace_pi K v (n + 1)
  exact ⟨M.continuous_Θ.measurable, M.continuous_symm.measurable⟩

private theorem local_group_facts :
    @MeasurableMul₂ (GL (Fin 2) (v.adicCompletion K)) (localGLBorel K v) _ ∧
      @MeasurableInv (GL (Fin 2) (v.adicCompletion K)) _ (localGLBorel K v) ∧
      @SigmaFinite _ (localGLBorel K v) (localHaar K v) ∧
      @Measure.IsMulLeftInvariant _ (localGLBorel K v) _ (localHaar K v) := by
  letI := localGLBorel K v
  haveI := borelSpace_localGLBorel K v
  haveI := OrbitalCarriers.secondCountableTopology_gl (v.adicCompletion K)
  haveI := OrbitalCarriers.sigmaCompactSpace_gl (v.adicCompletion K)
  haveI := isHaarMeasure_localHaar K v
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

private theorem carrier_facts (γ : GL (Fin 2) (v.adicCompletion K)) :
    @MeasurableInv (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))) _
        (centralizerBorel (v.adicCompletion K) γ) ∧
      @Measurable _ _ (centralizerBorel (v.adicCompletion K) γ) (localGLBorel K v)
        (fun s : Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))) =>
          (s : GL (Fin 2) (v.adicCompletion K))) := by
  letI := localGLBorel K v
  letI := centralizerBorel (v.adicCompletion K) γ
  haveI := borelSpace_localGLBorel K v
  haveI : BorelSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))) := ⟨rfl⟩
  exact ⟨inferInstance, continuous_subtype_val.measurable⟩

private theorem twisted_carrier_facts (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    @MeasurableInv (twistedCentralizer K L (v.adicCompletion K) σ δ) _
        (twistedCentralizerBorel K L (v.adicCompletion K) σ δ) ∧
      @Measurable _ _ (twistedCentralizerBorel K L (v.adicCompletion K) σ δ)
        (glBorelOf (L ⊗[K] v.adicCompletion K))
        (fun t : twistedCentralizer K L (v.adicCompletion K) σ δ =>
          (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K))) := by
  letI := glBorelOf (L ⊗[K] v.adicCompletion K)
  letI := twistedCentralizerBorel K L (v.adicCompletion K) σ δ
  haveI := borelSpace_glBorelOf (L ⊗[K] v.adicCompletion K)
  haveI := isTopologicalGroup_tensorGL K L (v.adicCompletion K)
  haveI : BorelSpace (twistedCentralizer K L (v.adicCompletion K) σ δ) := ⟨rfl⟩
  exact ⟨inferInstance, continuous_subtype_val.measurable⟩

private theorem torus_facts (γ : GL (Fin 2) (v.adicCompletion K)) (hγ : IsRegularSemisimple γ)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))))
      (centralizerBorel (v.adicCompletion K) γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel (v.adicCompletion K) γ) τ) :
    @SFinite _ (centralizerBorel (v.adicCompletion K) γ) τ ∧
      @Measure.IsInvInvariant _ (centralizerBorel (v.adicCompletion K) γ) _ τ := by
  haveI := OrbitalCarriers.secondCountableTopology_gl (v.adicCompletion K)
  haveI := OrbitalCarriers.locallyCompactSpace_gl (v.adicCompletion K)
  have hT := OrbitalCarriers.isClosed_centralizer (v.adicCompletion K) γ
  exact ⟨OrbitalCarriers.sfinite_of_isHaarMeasure_of_isClosed _ hT τ hτ,
    OrbitalCarriers.isInvInvariant_of_isHaarMeasure_of_isClosed _ hT
      (RegularCentralizer.isMulCommutative_localCentralizer K v hγ) τ hτ⟩

private theorem twisted_torus_facts (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ : IsRegularSemisimple (normString K L (v.adicCompletion K) σ δ))
    (τ' : @Measure (twistedCentralizer K L (v.adicCompletion K) σ δ)
      (twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ') :
    @SFinite _ (twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ' ∧
      @Measure.IsInvInvariant _ (twistedCentralizerBorel K L (v.adicCompletion K) σ δ) _ τ' := by
  haveI := isTopologicalRing_tensor K L (v.adicCompletion K)
  haveI := t2Space_tensor K L (v.adicCompletion K)
  haveI := locallyCompactSpace_tensor K L (v.adicCompletion K)
  haveI := OrbitalCarriers.secondCountableTopology_semiLocal K L v
  haveI := isTopologicalGroup_tensorGL K L (v.adicCompletion K)
  haveI := OrbitalCarriers.locallyCompactSpace_gl (L ⊗[K] v.adicCompletion K)
  haveI := OrbitalCarriers.secondCountableTopology_gl (L ⊗[K] v.adicCompletion K)
  have hT := OrbitalCarriers.isClosed_twistedCentralizer K L (v.adicCompletion K) σ
    (continuous_sigmaGL K L (v.adicCompletion K) σ) δ
  have hle := RegularCentralizer.twistedCentralizer_le_centralizer_normString K L (v.adicCompletion K) σ δ
  have hcN := RegularCentralizer.isMulCommutative_centralizer_of_isRegularSemisimple hδ
  have hcomm : IsMulCommutative (twistedCentralizer K L (v.adicCompletion K) σ δ) :=
    isMulCommutative_of_le hle hcN
  exact ⟨OrbitalCarriers.sfinite_of_isHaarMeasure_of_isClosed _ hT τ' hτ',
    OrbitalCarriers.isInvInvariant_of_isHaarMeasure_of_isClosed _ hT hcomm τ' hτ'⟩

private theorem exists_scalar {n : ℕ} (M : Model K L σ v n) :
    ∃ c : NNReal, c ≠ 0 ∧
      @Measure.map _ _ (glBorelOf (L ⊗[K] v.adicCompletion K))
          (@MeasurableSpace.pi _ _ fun _ => localGLBorel K v) M.Θ (semiLocalHaar K L v) =
        c • @Measure.pi (Fin (n + 1)) (fun _ => GL (Fin 2) (v.adicCompletion K)) _
          (fun _ => localGLBorel K v) (fun _ => localHaar K v) := by
  haveI := OrbitalCarriers.secondCountableTopology_gl (v.adicCompletion K)
  exact HaarScalar.exists_map_semiLocalHaar_eq_smul_pi_localHaar K L v (n + 1) M.Θ M.continuous_Θ M.continuous_symm

private theorem coupling {n : ℕ} (M : Model K L σ v n) (γ : GL (Fin 2) (v.adicCompletion K))
    (δ y : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))))
      (centralizerBorel (v.adicCompletion K) γ))
    (τ' : @Measure (twistedCentralizer K L (v.adicCompletion K) σ δ)
      (twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (hc : Coupled K L (v.adicCompletion K) σ γ δ y τ τ') :
    @Measure.map _ _ (twistedCentralizerBorel K L (v.adicCompletion K) σ δ) (localGLBorel K v)
        (fun t : twistedCentralizer K L (v.adicCompletion K) σ δ =>
          (M.Θ y 0)⁻¹ * M.Θ (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 * M.Θ y 0) τ' =
      @Measure.map _ _ (centralizerBorel (v.adicCompletion K) γ) (localGLBorel K v)
        (fun s : Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))) =>
          (s : GL (Fin 2) (v.adicCompletion K))) τ := by
  have hρ : @Measurable _ _ (glBorelOf (L ⊗[K] v.adicCompletion K)) (glBorelOf (v.adicCompletion K))
      (fun g => M.Θ g 0) := by
    letI := glBorelOf (L ⊗[K] v.adicCompletion K)
    letI := glBorelOf (v.adicCompletion K)
    haveI := borelSpace_glBorelOf (L ⊗[K] v.adicCompletion K)
    haveI := borelSpace_glBorelOf (v.adicCompletion K)
    exact ((continuous_apply (0 : Fin (n + 1))).comp M.continuous_Θ).measurable
  exact CoupledProjection.map_conj_eq_map_val_of_coupled K L (v.adicCompletion K) σ γ δ y τ τ' hc (fun g => M.Θ g 0) hρ
    (fun s => congrFun (M.Θ_toTensorGL s) 0) (fun g => by simp)
    (twisted_carrier_facts K L σ v δ).2 (carrier_facts K v γ).2
    (CentralizerEmbedding.measurable_toTensorGL K L (v.adicCompletion K))

private theorem phi_facts (φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) (hφv : IsSemiLocalTestFn K L v φv) :
    @Measurable _ _ (glBorelOf (L ⊗[K] v.adicCompletion K)) _ φv ∧ ∃ C, ∀ x, ‖φv x‖ ≤ C := by
  letI : MeasurableSpace (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) := glBorelOf (L ⊗[K] v.adicCompletion K)
  haveI : BorelSpace (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) := borelSpace_glBorelOf _
  refine ⟨hφv.1.continuous.measurable, ?_⟩
  obtain ⟨C, hC⟩ := hφv.2.isCompact.exists_bound_of_continuousOn hφv.1.continuous.continuousOn
  refine ⟨max C 0, fun x => ?_⟩
  by_cases hx : x ∈ tsupport φv
  · exact (hC x hx).trans (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport hx, norm_zero]
    exact le_max_right _ _

private theorem isLocalTestFn_fib {n : ℕ} (Φ : (Fin (n + 1) → GL (Fin 2) (v.adicCompletion K)) → ℂ)
    (hΦ : IsLocallyConstant Φ) (hcs : HasCompactSupport Φ) (a : ℂ) :
    IsLocalTestFn K v fun g => a * @fib _ _ (localGLBorel K v) (localHaar K v) n Φ g := by
  letI := localGLBorel K v
  refine ⟨?_, ?_⟩
  · exact (FibreIntegralTestClass.isLocallyConstant_fib (localHaar K v) hΦ hcs).comp (fun z : ℂ => a * z)
  · exact (FibreIntegralTestClass.hasCompactSupport_fib (localHaar K v) hcs).mul_left

private theorem section_supply {n : ℕ} (Φ : (Fin (n + 1) → GL (Fin 2) (v.adicCompletion K)) → ℂ)
    (hΦ : IsLocallyConstant Φ) (hcs : HasCompactSupport Φ) (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : IsRegularSemisimple γ)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))))
      (centralizerBorel (v.adicCompletion K) γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel (v.adicCompletion K) γ) τ) :
    ∃ w₁ : GL (Fin 2) (v.adicCompletion K) → ℝ, (∀ h, 0 ≤ w₁ h) ∧
      @Measurable _ _ (localGLBorel K v) _ w₁ ∧ @Integrable ℝ _ _ _ (localGLBorel K v) w₁ (localHaar K v) ∧
      ∀ h, @fib _ _ (localGLBorel K v) (localHaar K v) n (fun y => (‖Φ y‖ : ℂ)) (h⁻¹ * γ * h) ≠ 0 →
        @integral _ _ _ _ (centralizerBorel (v.adicCompletion K) γ) τ
          (fun s : Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))) =>
            w₁ ((s : GL (Fin 2) (v.adicCompletion K)) * h)) = 1 := by
  have hfv : IsLocalTestFn K v
      (fun h => @fib _ _ (localGLBorel K v) (localHaar K v) n (fun y => (‖Φ y‖ : ℂ)) h) := by
    letI := localGLBorel K v
    exact ⟨FibreIntegralTestClass.isLocallyConstant_fib_norm (localHaar K v) hΦ hcs,
      FibreIntegralTestClass.hasCompactSupport_fib_norm (localHaar K v) hcs⟩
  haveI : @Measure.IsHaarMeasure _ _ _ (localCentralizerBorel K v γ) τ := hτ
  obtain ⟨w, ⟨hw0, hwm, hwcs, hw1⟩, hwlc⟩ :=
    AutomorphicForm.exists_isSectionFn_and_isLocallyConstant_of_isRegularSemisimple_of_isLocalTestFn
      K v γ hγ τ _ hfv
  refine ⟨w, hw0, hwm, ?_, hw1⟩
  letI := localGLBorel K v
  haveI := borelSpace_localGLBorel K v
  haveI := isHaarMeasure_localHaar K v
  exact hwlc.continuous.integrable_of_hasCompactSupport hwcs

private theorem cutoff_supply {n : ℕ} (Φ : (Fin (n + 1) → GL (Fin 2) (v.adicCompletion K)) → ℂ)
    (hcs : HasCompactSupport Φ) :
    ∃ β : (Fin n → GL (Fin 2) (v.adicCompletion K)) → ℝ, (∀ c, 0 ≤ β c) ∧
      @Measurable _ _ (@MeasurableSpace.pi _ _ fun _ => localGLBorel K v) _ β ∧
      @Integrable ℝ _ _ _ (@MeasurableSpace.pi _ _ fun _ => localGLBorel K v) β
        (@Measure.pi (Fin n) (fun _ => GL (Fin 2) (v.adicCompletion K)) _ (fun _ => localGLBorel K v)
          fun _ => localHaar K v) ∧
      ∀ c h, Φ (Fin.snoc c h) ≠ 0 → β c = 1 := by
  letI : MeasurableSpace (GL (Fin 2) (v.adicCompletion K)) := localGLBorel K v
  haveI : BorelSpace (GL (Fin 2) (v.adicCompletion K)) := borelSpace_localGLBorel K v
  haveI := secondCountable_localGL K v
  haveI := OrbitalCarriers.sigmaCompactSpace_gl (v.adicCompletion K)
  haveI : (localHaar K v).IsHaarMeasure := isHaarMeasure_localHaar K v
  exact exists_cutoff (localHaar K v) Φ hcs

private theorem sectionIndependence : SectionIndependenceStatement :=
  AutomorphicForm.integral_mul_eq_integral_mul_of_forall_integral_subgroup_mul_eq_one

private theorem shiftIdentity : ShiftIdentityStatement :=
  @AutomorphicForm.integral_twistedConj_mul_eq_integral_conj_fibreIntegral_mul

end Interface

section Assembly

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  {σ : L ≃ₐ[K] L} {v : HeightOneSpectrum (𝓞 K)}

private theorem isNormOf_of_model {n : ℕ} (M : Model K L σ v n) (γ : GL (Fin 2) (v.adicCompletion K)) :
    ∃ δ, IsNormOf K L (v.adicCompletion K) σ γ δ := by
  refine ⟨M.Θ.symm (Pi.mulSingle 0 γ), 1, ?_⟩
  show toTensorGL K L (v.adicCompletion K) γ =
    (1 : GL (Fin 2) (L ⊗[K] v.adicCompletion K))⁻¹ *
      normString K L (v.adicCompletion K) σ (M.Θ.symm (Pi.mulSingle 0 γ)) * 1
  rw [inv_one, one_mul, mul_one]
  apply M.Θ.injective
  funext j
  rw [M.Θ_toTensorGL, M.Θ_normString, MulEquiv.apply_symm_apply]
  exact (RotatedString.prod_ofFn_mulSingle_add γ j).symm

private theorem exists_isLocalTestFn_areMatchingLocal_of_algHom
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : HeightOneSpectrum (𝓞 K)) (ι : L →ₐ[K] v.adicCompletion K)
    (φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) (hφv : IsSemiLocalTestFn K L v φv) :
    ∃ fv : GL (Fin 2) (v.adicCompletion K) → ℂ, IsLocalTestFn K v fv ∧ AreMatchingLocal K L v σ φv fv := by
  obtain ⟨n, ⟨M⟩⟩ := exists_model K L σ v hdeg hσ ι
  letI : MeasurableSpace (GL (Fin 2) (v.adicCompletion K)) := localGLBorel K v
  letI : MeasurableSpace (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) := glBorelOf (L ⊗[K] v.adicCompletion K)
  obtain ⟨hmul₂, hinv, hsf, hli⟩ := local_group_facts K v
  haveI := hmul₂; haveI := hinv; haveI := hsf; haveI := hli
  obtain ⟨hΘm, hΘsm⟩ := measurable_model K L σ v M
  obtain ⟨c, hc0, hmap⟩ := exists_scalar K L σ v M
  obtain ⟨hφm, hφb⟩ := phi_facts K L v φv hφv
  set Φ : (Fin (n + 1) → GL (Fin 2) (v.adicCompletion K)) → ℂ := φv ∘ M.Θ.symm with hΦ_def
  have hΦlc : IsLocallyConstant Φ := hφv.1.comp_continuous M.continuous_symm
  have hΦcs : HasCompactSupport Φ :=
    hφv.2.comp_homeomorph ⟨M.Θ.symm.toEquiv, M.continuous_symm, M.continuous_Θ⟩
  refine ⟨fun g => ((c : ℝ) : ℂ) * fib (localHaar K v) Φ g, isLocalTestFn_fib K v Φ hΦlc hΦcs _, ?_⟩
  unfold AreMatchingLocal AreMatchingOn
  refine ⟨?_, ?_⟩
  · intro δ hδ γ hγ y hy τ τ' hτH hτ'H hcoup I I' hI' hI
    obtain ⟨W, ⟨hW0, hWm, -, hW1⟩, hI'eq⟩ := hI'
    obtain ⟨w₀, ⟨hw₀0, hw₀m, -, hw₀1⟩, hIeq⟩ := hI
    letI : MeasurableSpace (twistedCentralizer K L (v.adicCompletion K) σ δ) :=
      twistedCentralizerBorel K L (v.adicCompletion K) σ δ
    letI : MeasurableSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))) :=
      centralizerBorel (v.adicCompletion K) γ
    obtain ⟨hTwinv, hTwval⟩ := twisted_carrier_facts K L σ v δ
    obtain ⟨hCinv, hCval⟩ := carrier_facts K v γ
    haveI := hTwinv; haveI := hCinv
    obtain ⟨hτ'sf, hτ'inv⟩ := twisted_torus_facts K L σ v δ hδ τ' hτ'H
    obtain ⟨hτsf, hτinv⟩ := torus_facts K v γ hγ τ hτH
    haveI := hτ'sf; haveI := hτ'inv; haveI := hτsf; haveI := hτinv
    have hy' : toTensorGL K L (v.adicCompletion K) γ =
        y⁻¹ * normString K L (v.adicCompletion K) σ δ * y := hy
    have hγ' : γ = (M.Θ y 0)⁻¹ * nrm (M.Θ δ) * M.Θ y 0 := by
      have h1 := congrArg (fun g => M.Θ g 0) hy'
      simp only [M.Θ_toTensorGL, map_mul, map_inv, Pi.mul_apply, Pi.inv_apply, M.Θ_normString,
        zero_add] at h1
      exact h1
    have hTw : ∀ s, s ∈ twistedCentralizer K L (v.adicCompletion K) σ δ ↔
        ∀ j, (M.Θ s j)⁻¹ * M.Θ δ j * M.Θ s (j + 1) = M.Θ δ j := by
      intro s
      rw [twistedCentralizer, mem_sigmaCentralizer_iff_inv, ← M.Θ.injective.eq_iff, M.Θ_twist,
        funext_iff]
    rw [hI'eq, hIeq]
    exact integral_twconj_mul_eq_integral_fib_mul (localHaar K v) sectionIndependence shiftIdentity
      (M.Θ δ) M.Θ hΘm hΘsm
      (semiLocalHaar K L v) c hc0 hmap (fun x => x⁻¹ * δ * sigmaGL K L (v.adicCompletion K) σ x)
      (fun x => M.Θ_twist x δ) (twistedCentralizer K L (v.adicCompletion K) σ δ) hTwval hTw τ'
      (M.Θ y 0) γ hγ' hCval τ (coupling K L σ v M γ δ y τ τ' hcoup) φv hφm hφb W hW0 hWm hW1 w₀ hw₀0
      hw₀m hw₀1 (section_supply K v Φ hΦlc hΦcs γ hγ τ hτH) (cutoff_supply K v Φ hΦcs)
  · intro γ _ hno _ _ _ _
    exact (hno (isNormOf_of_model M γ)).elim

end Assembly

end SplitMatching

end Tail

open AutomorphicForm in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : HeightOneSpectrum (𝓞 K)) (ι : L →ₐ[K] v.adicCompletion K)
    (φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) (hφv : IsSemiLocalTestFn K L v φv) :
    ∃ fv : GL (Fin 2) (v.adicCompletion K) → ℂ, IsLocalTestFn K v fv ∧ AreMatchingLocal K L v σ φv fv :=
  SplitMatching.exists_isLocalTestFn_areMatchingLocal_of_algHom K L hdeg σ hσ v ι φv hφv

end S_AutomorphicForm_exists_isLocalTestFn_areMatchingLocal_of_algHom
end P2MW
export P2MW.S_AutomorphicForm_exists_isLocalTestFn_areMatchingLocal_of_algHom (solution)
