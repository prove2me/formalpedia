-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LeviFormWeightMetricOrthonormalDiagonal
-- name    : Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LeviFormWeightMetricOrthonormalDiagonal
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T01:23:29.682846+00:00
-- url     : https://prove2.me/theorems/8b9889d7-8471-4663-8693-5ac2573a86b7
-- title:
--   Levi Form Weight Metric Orthonormal Diagonal
-- statement:
--   Definitions and structural lemmas for Levi Form Weight Metric Orthonormal Diagonal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/LeviFormWeightMetricOrthonormalDiagonal.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_V_zero_app
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_const
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_const
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_const
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_differentiableAt_wdb
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_eventually_differentiableAt_of_contDiffAt
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wd_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wd_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wdb_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wdb_mul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.AR.Up.IW.V_zero_app


set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
namespace GlobalTheory.LeviZero
open Filter
open scoped ComplexConjugate
noncomputable section
section Jets
variable {n : ℕ}
def dDir (ξ : Fin n → ℂ) (f : V n → ℂ) (x : V n) : ℂ := ∑ j, wd n j f x * ξ j
def dbDir (ξ : Fin n → ℂ) (f : V n → ℂ) (x : V n) : ℂ := ∑ k, wdb n k f x * conj (ξ k)
theorem wd_congr' {j : Fin n} {f g : V n → ℂ} {x : V n} (h : f =ᶠ[𝓝 x] g) :
    wd n j f x = wd n j g x := by
  simp only [wd, h.fderiv_eq]
theorem leviV_add' {f g : V n → ℂ} {x : V n} (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x)
    (ξ : Fin n → ℂ) : leviV n (fun y => f y + g y) x ξ = leviV n f x ξ + leviV n g x ξ := by
  have hev : ∀ k : Fin n, wdb n k (fun y => f y + g y) =ᶠ[𝓝 x]
      fun y => wdb n k f y + wdb n k g y := by
    intro k
    filter_upwards [eventually_differentiableAt_of_contDiffAt hf,
      eventually_differentiableAt_of_contDiffAt hg] with y h1 h2
    exact wdb_add h1 h2
  simp only [leviV, wd_congr' (hev _), wd_add (differentiableAt_wdb hf) (differentiableAt_wdb hg),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring
theorem leviV_mul' {f g : V n → ℂ} {x : V n} (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x)
    (ξ : Fin n → ℂ) : leviV n (fun y => f y * g y) x ξ =
      f x * leviV n g x ξ + dbDir ξ f x * dDir ξ g x + (dDir ξ f x * dbDir ξ g x +
        leviV n f x ξ * g x) := by
  have hf1 : DifferentiableAt ℝ f x := hf.differentiableAt (by simp)
  have hg1 : DifferentiableAt ℝ g x := hg.differentiableAt (by simp)
  have hev : ∀ k : Fin n, wdb n k (fun y => f y * g y) =ᶠ[𝓝 x]
      fun y => wdb n k f y * g y + f y * wdb n k g y := by
    intro k
    filter_upwards [eventually_differentiableAt_of_contDiffAt hf,
      eventually_differentiableAt_of_contDiffAt hg] with y h1 h2
    exact wdb_mul h1 h2
  have hterm : ∀ j k : Fin n, wd n j (wdb n k (fun y => f y * g y)) x =
      wd n j (wdb n k f) x * g x + wdb n k f x * wd n j g x +
        (wd n j f x * wdb n k g x + f x * wd n j (wdb n k g) x) := by
    intro j k
    rw [wd_congr' (hev k), wd_add (f := fun y => wdb n k f y * g y) (g := fun y => f y * wdb n k g y)
      ((differentiableAt_wdb hf).mul hg1) (hf1.mul (differentiableAt_wdb hg)),
      wd_mul (differentiableAt_wdb hf) hg1, wd_mul hf1 (differentiableAt_wdb hg)]
  rw [mul_comm (dbDir ξ f x)]
  simp only [leviV, hterm, dDir, dbDir, Finset.sum_mul_sum]
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring
theorem leviV_const' (c : ℂ) (x : V n) (ξ : Fin n → ℂ) : leviV n (fun _ => c) x ξ = 0 := by
  have h0 : ∀ k : Fin n, wdb n k (fun _ : V n => c) = fun _ => 0 := fun k => by
    funext y; simp [wdb]
  simp [leviV, h0, wd]
abbrev JetRing : Type := DualNumber (DualNumber ℂ)
def sJ : JetRing := DualNumber.eps
def tJ : JetRing := TrivSqZeroExt.inl DualNumber.eps
def cJ (c : ℂ) : JetRing := TrivSqZeroExt.inl (TrivSqZeroExt.inl c)
structure HasJet (ξ : Fin n → ℂ) (x : V n) (f : V n → ℂ) (a : JetRing) : Prop where
  cd : ContDiffAt ℝ 2 f x
  val : f x = a.fst.fst
  hol : dDir ξ f x = a.snd.fst
  anti : dbDir ξ f x = a.fst.snd
  lev : leviV n f x ξ = a.snd.snd
variable {ξ : Fin n → ℂ} {x : V n}
theorem HasJet.const (c : ℂ) : HasJet ξ x (fun _ => c) (cJ c) :=
  ⟨contDiffAt_const, by simp [cJ], by simp [cJ, dDir, wd], by simp [cJ, dbDir, wdb],
    by simp [cJ, leviV_const']⟩
theorem HasJet.add {f g : V n → ℂ} {a b : JetRing} (hf : HasJet ξ x f a) (hg : HasJet ξ x g b) :
    HasJet ξ x (fun y => f y + g y) (a + b) := by
  have hf1 : DifferentiableAt ℝ f x := hf.cd.differentiableAt (by simp)
  have hg1 : DifferentiableAt ℝ g x := hg.cd.differentiableAt (by simp)
  refine ⟨hf.cd.add hg.cd, by simp [hf.val, hg.val], ?_, ?_, ?_⟩
  · simp [← hf.hol, ← hg.hol, dDir, wd_add hf1 hg1, add_mul, Finset.sum_add_distrib]
  · simp [← hf.anti, ← hg.anti, dbDir, wdb_add hf1 hg1, add_mul, Finset.sum_add_distrib]
  · simp [← hf.lev, ← hg.lev, leviV_add' hf.cd hg.cd]
theorem HasJet.mul {f g : V n → ℂ} {a b : JetRing} (hf : HasJet ξ x f a) (hg : HasJet ξ x g b) :
    HasJet ξ x (fun y => f y * g y) (a * b) := by
  have hf1 : DifferentiableAt ℝ f x := hf.cd.differentiableAt (by simp)
  have hg1 : DifferentiableAt ℝ g x := hg.cd.differentiableAt (by simp)
  refine ⟨hf.cd.mul hg.cd, by simp [hf.val, hg.val], ?_, ?_, ?_⟩
  · have : dDir ξ (fun y => f y * g y) x = f x * dDir ξ g x + dDir ξ f x * g x := by
      simp only [dDir, wd_mul hf1 hg1, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [this, hf.val, hg.val, hf.hol, hg.hol]
    simp [DualNumber.snd_mul]
  · have : dbDir ξ (fun y => f y * g y) x = f x * dbDir ξ g x + dbDir ξ f x * g x := by
      simp only [dbDir, wdb_mul hf1 hg1, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [this, hf.val, hg.val, hf.anti, hg.anti]
    simp [DualNumber.snd_mul]
  · rw [leviV_mul' hf.cd hg.cd, hf.val, hg.val, hf.anti, hg.anti, hf.hol, hg.hol, hf.lev, hg.lev]
    simp [DualNumber.snd_mul]
theorem HasJet.sum {ι : Type*} (s : Finset ι) {f : ι → V n → ℂ} {a : ι → JetRing}
    (h : ∀ i ∈ s, HasJet ξ x (f i) (a i)) : HasJet ξ x (fun y => ∑ i ∈ s, f i y) (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa [cJ] using HasJet.const (ξ := ξ) (x := x) 0
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
theorem HasJet.prod {ι : Type*} (s : Finset ι) {f : ι → V n → ℂ} {a : ι → JetRing}
    (h : ∀ i ∈ s, HasJet ξ x (f i) (a i)) : HasJet ξ x (fun y => ∏ i ∈ s, f i y) (∏ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa [cJ] using HasJet.const (ξ := ξ) (x := x) 1
  | insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).mul (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
theorem HasJet.det {m : ℕ} {M : V n → Matrix (Fin m) (Fin m) ℂ} {A : Matrix (Fin m) (Fin m) JetRing}
    (h : ∀ a b, HasJet ξ x (fun y => M y a b) (A a b)) : HasJet ξ x (fun y => (M y).det) A.det := by
  simp only [Matrix.det_apply']
  refine HasJet.sum _ fun σ _ => HasJet.mul ?_ (HasJet.prod _ fun i _ => h _ _)
  have := HasJet.const (ξ := ξ) (x := x) (((Equiv.Perm.sign σ : ℤ) : ℂ))
  simpa [cJ] using this
end Jets
section Alg
variable {A : Type*} [CommRing A]
end Alg
section Log
variable {n : ℕ} {ξ : Fin n → ℂ} {x : V n}
end Log
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
def zMat (ξ : Fin (nd X) → ℂ) (τ : X.Ψ) (a b : Fin r) : ℂ :=
  if h : b < a then ξ ((Fintype.equivFin (Ent X)) ⟨τ, ⟨(a, b), h⟩⟩) else 0
def cH : ℂ →+* JetRing := (TrivSqZeroExt.inlHom _ _).comp (TrivSqZeroExt.inlHom _ _)
end
end GlobalTheory.LeviZero


