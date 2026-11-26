-- Prove2me | Definitions.Def_Section5Verified_Section5ProductSampling
-- name    : Section5Verified_Section5ProductSampling
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:37:39.369591+00:00
-- url     : https://prove2.me/theorems/b447521f-a5a4-5113-8a2e-b84c10240816
-- title:
--   Section5ProductSampling — verified interface
-- statement:
--   Proves L2 energy/triangle identities, product synthesis norm bounds for arbitrary complex coefficient arrays, and the full finite-coordinate analytic tensor hybrid estimate ((1+delta)^n-1), with all integrability and measure-preserving coordinate changes proved.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5ProductSampling; mechanically extracted with exact Lean declaration spans.

import Mathlib
section
set_option autoImplicit false

open MeasureTheory

/-! Product-space estimates for the multivariate Hermite sampling argument.
All product integrals are justified before Fubini is used.
-/





theorem section5_memLp_product {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    (f : α → ℂ) (g : β → ℂ) (hf : MemLp f 2 μ) (hg : MemLp g 2 ν) :
    MemLp (fun z : α×β => f z.1*g z.2) 2 (μ.prod ν) := by
  apply (memLp_two_iff_integrable_sq_norm (hf.1.comp_fst.mul hg.1.comp_snd)).mpr
  change Integrable (fun z : α×β => ‖f z.1*g z.2‖^2) (μ.prod ν)
  simp_rw [norm_mul,mul_pow]
  exact hf.norm.integrable_sq.mul_prod hg.norm.integrable_sq

theorem section5_memLp_synthesis {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    {μ : Measure α} (f : ι → α → ℂ) (hf : ∀ i, MemLp (f i) 2 μ) (c : ι → ℂ) :
    MemLp (fun x => ∑ i, c i*f i x) 2 μ := by
  exact memLp_finsetSum _ (fun i _ => (hf i).const_mul (c i))





def section5_SynthesisBound {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    (μ : Measure α) (f : ι → α → ℂ) (A : ℝ) : Prop :=
  ∀ c : ι → ℂ, (∫ x, ‖∑ i, c i*f i x‖^2 ∂μ) ≤ A^2*∑ i, ‖c i‖^2







noncomputable def section5_tensor_family {α ι : Type*} (f : ι → α → ℂ)
    (n : ℕ) (a : Fin n → ι) (x : Fin n → α) : ℂ := ∏ i, f (a i) (x i)



theorem section5_tensor_family_memLp {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) [SigmaFinite μ] (f : ι → α → ℂ)
    (hf : ∀ i, MemLp (f i) 2 μ) (n : ℕ) (a : Fin n → ι) :
    MemLp (section5_tensor_family f n a) 2 (Measure.pi (fun _ : Fin n => μ)) := by
  induction n with
  | zero =>
    haveI : ∀ i : Fin 0, IsFiniteMeasure ((fun _ : Fin 0 => μ) i) := fun i => Fin.elim0 i
    simpa [section5_tensor_family] using
      (memLp_const (1:ℂ) : MemLp (fun _ : Fin 0 → α => (1:ℂ)) 2 _)
  | succ n ih =>
    have hprod := section5_memLp_product (f (a 0)) (section5_tensor_family f n (Fin.tail a))
      (hf (a 0)) (ih (Fin.tail a))
    have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) 0
    have h := hprod.comp_measurePreserving hmp
    convert h using 1
    funext x
    simp only [Function.comp_apply,section5_tensor_family,Fin.prod_univ_succ]
    rfl















theorem section5_unit_phase_memLp {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (u f : α → ℂ) (hu : AEStronglyMeasurable u μ) (hf : MemLp f 2 μ)
    (hunit : ∀ x, ‖u x‖=1) : MemLp (fun x => u x*f x) 2 μ := by
  apply hf.congr_norm (hu.mul hf.1)
  exact Filter.Eventually.of_forall (fun x => by rw [Pi.mul_apply,norm_mul,hunit x,one_mul])







end


