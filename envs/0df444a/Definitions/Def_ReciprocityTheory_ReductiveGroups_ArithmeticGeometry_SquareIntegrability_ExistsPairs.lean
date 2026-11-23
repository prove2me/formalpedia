-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ExistsPairs
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ExistsPairs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:26:21.715915+00:00
-- url     : https://prove2.me/theorems/020456b2-1b7d-4f9f-972b-558bdeafcd37
-- title:
--   Exists Pairs
-- statement:
--   Definitions and structural lemmas for Exists Pairs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ExistsPairs.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PerpSurj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContinuousRl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimB_Pm_diff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.I2
open Complex Module
noncomputable section
namespace DimC
variable {ι : Type} [Fintype ι]
theorem Hf_inner (v w : EuclideanSpace ℂ ι) : Hf v w = inner ℂ w v := by
  simp only [Hf, PiLp.inner_apply, RCLike.inner_apply]
  all_goals (refine Finset.sum_congr rfl fun i _ => ?_; ring)
theorem Hf_add_l (v v' w : EuclideanSpace ℂ ι) : Hf (v + v') w = Hf v w + Hf v' w := by
  simp only [Hf, PiLp.add_apply, add_mul, Finset.sum_add_distrib]
theorem Hf_add_r (v w w' : EuclideanSpace ℂ ι) : Hf v (w + w') = Hf v w + Hf v w' := by
  simp only [Hf, PiLp.add_apply, map_add, mul_add, Finset.sum_add_distrib]
theorem Hf_smul_l (a : ℂ) (v w : EuclideanSpace ℂ ι) : Hf (a • v) w = a * Hf v w := by
  simp only [Hf, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring
theorem Hf_smul_r (a : ℂ) (v w : EuclideanSpace ℂ ι) : Hf v (a • w) = (starRingEnd ℂ) a * Hf v w := by
  simp only [Hf, PiLp.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring
theorem Hf_self (v : EuclideanSpace ℂ ι) : Hf v v = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
  rw [Hf_inner]
  first
    | exact_mod_cast inner_self_eq_norm_sq_to_K (𝕜 := ℂ) v
    | (rw [inner_self_eq_norm_sq_to_K]; simp)
    | (rw [inner_self_eq_norm_sq_to_K]; norm_cast)
theorem Hf_sum_l {k : ℕ} (a : Fin k → ℂ) (v : Fin k → EuclideanSpace ℂ ι) (w : EuclideanSpace ℂ ι) :
    Hf (∑ i, a i • v i) w = ∑ i, a i * Hf (v i) w := by
  have h := map_sum (AddMonoidHom.mk' (fun x => Hf x w) (fun x x' => Hf_add_l x x' w))
    (fun i => a i • v i) Finset.univ
  simp only [AddMonoidHom.mk'_apply, Hf_smul_l] at h
  exact h
theorem Hf_sum_r {k : ℕ} (a : Fin k → ℂ) (v : EuclideanSpace ℂ ι) (w : Fin k → EuclideanSpace ℂ ι) :
    Hf v (∑ l, a l • w l) = ∑ l, (starRingEnd ℂ) (a l) * Hf v (w l) := by
  have h := map_sum (AddMonoidHom.mk' (fun x => Hf v x) (fun x x' => Hf_add_r v x x'))
    (fun i => a i • w i) Finset.univ
  simp only [AddMonoidHom.mk'_apply, Hf_smul_r] at h
  exact h
theorem Hf_zsmul_l (c : ℤ) (v w : EuclideanSpace ℂ ι) : (Hf (c • v) w).im = c * (Hf v w).im := by
  rw [← Int.cast_smul_eq_zsmul ℂ, Hf_smul_l]
  simp
theorem Hf_zsmul_r (c : ℤ) (v w : EuclideanSpace ℂ ι) : (Hf v (c • w)).im = c * (Hf v w).im := by
  rw [← Int.cast_smul_eq_zsmul ℂ, Hf_smul_r]
  simp
variable (Y : GT ι)
def nz (x y : EuclideanSpace ℂ ι) : ℤ := ⌊(Hf x y).im⌋
theorem nz_eq {x y : EuclideanSpace ℂ ι} (hx : x ∈ lat Y.b) (hy : y ∈ lat Y.b) :
    (nz x y : ℝ) = (Hf x y).im := by
  obtain ⟨k, hk⟩ := Y.integral x y hx hy
  rw [nz, hk, Int.floor_intCast]
def Bz : lat Y.b →ₗ[ℤ] lat Y.b →ₗ[ℤ] ℤ :=
  LinearMap.mk₂ ℤ (fun x y => nz (x : EuclideanSpace ℂ ι) y)
    (fun x x' y => by
      apply Int.cast_injective (α := ℝ)
      rw [Int.cast_add, nz_eq Y (x + x').2 y.2, nz_eq Y x.2 y.2, nz_eq Y x'.2 y.2, Submodule.coe_add,
        Hf_add_l, Complex.add_im])
    (fun c x y => by
      apply Int.cast_injective (α := ℝ)
      rw [smul_eq_mul, Int.cast_mul, nz_eq Y (c • x).2 y.2, nz_eq Y x.2 y.2, Submodule.coe_smul, Hf_zsmul_l])
    (fun x y y' => by
      apply Int.cast_injective (α := ℝ)
      rw [Int.cast_add, nz_eq Y x.2 (y + y').2, nz_eq Y x.2 y.2, nz_eq Y x.2 y'.2, Submodule.coe_add,
        Hf_add_r, Complex.add_im])
    (fun c x y => by
      apply Int.cast_injective (α := ℝ)
      rw [smul_eq_mul, Int.cast_mul, nz_eq Y x.2 (c • y).2, nz_eq Y x.2 y.2, Submodule.coe_smul, Hf_zsmul_r])
section Core
variable {Y} (e f : Fin (Fintype.card ι) → EuclideanSpace ℂ ι)
  (hee : ∀ i j, (Hf (e i) (e j)).im = 0)
  (hef : ∀ i j, (Hf (e i) (f j)).im = if i = j then 1 else 0)
include hee hef in
theorem e_li : LinearIndependent ℂ e := by
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have hS : ∀ i l, (Hf (e i) (e l)).im = 0 := hee
  have h0 : ∀ y, ∑ i, c i * Hf (e i) y = 0 := by
    intro y
    rw [← Hf_sum_l, hc]
    simp [Hf]
  have hre : ∀ l, ∑ i, (c i).re * (Hf (e i) (e l)).re = 0 := by
    intro l
    have h := congrArg Complex.re (h0 (e l))
    simpa [Complex.re_sum, Complex.mul_re, hS] using h
  have him : ∀ l, ∑ i, (c i).im * (Hf (e i) (e l)).re = 0 := by
    intro l
    have h := congrArg Complex.im (h0 (e l))
    simpa [Complex.im_sum, Complex.mul_im, hS] using h
  have hzero : ∀ r : Fin (Fintype.card ι) → ℝ, (∀ l, ∑ i, r i * (Hf (e i) (e l)).re = 0) →
      ∑ i, ((r i : ℂ)) • e i = 0 := by
    intro r hr
    have hcol : ∀ l, ∑ i, (r i : ℂ) * Hf (e i) (e l) = 0 := by
      intro l
      apply Complex.ext
      · simpa [Complex.re_sum, hS] using hr l
      · simp [Complex.im_sum, hS]
    have hH : Hf (∑ i, ((r i : ℂ)) • e i) (∑ l, ((r l : ℂ)) • e l) = 0 := by
      rw [Hf_sum_l]
      simp only [Hf_sum_r, Complex.conj_ofReal, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun l _ => ?_
      calc ∑ i, (r i : ℂ) * ((r l : ℂ) * Hf (e i) (e l))
          = (r l : ℂ) * ∑ i, (r i : ℂ) * Hf (e i) (e l) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => by ring
        _ = 0 := by rw [hcol l, mul_zero]
    rw [Hf_self] at hH
    have h2 : ‖∑ i, ((r i : ℂ)) • e i‖ ^ 2 = 0 := by exact_mod_cast hH
    exact norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h2)
  have hcoef : ∀ r : Fin (Fintype.card ι) → ℝ, ∑ i, ((r i : ℂ)) • e i = 0 → r j = 0 := by
    intro r hr0
    have h1 : (Hf (∑ i, ((r i : ℂ)) • e i) (f j)).im = r j := by
      rw [Hf_sum_l]
      simp [Complex.im_sum, hef]
    rw [hr0] at h1
    simpa [Hf] using h1.symm
  apply Complex.ext
  · simpa using hcoef (fun i => (c i).re) (hzero _ hre)
  · simpa using hcoef (fun i => (c i).im) (hzero _ him)
def eb : Module.Basis (Fin (Fintype.card ι)) ℂ (EuclideanSpace ℂ ι) :=
  Module.Basis.mk (e_li e f hee hef)
    ((e_li e f hee hef).span_eq_top_of_card_eq_finrank' (by simp)).ge
end Core
section Gauge
variable {Y} (e f : Fin (Fintype.card ι) → EuclideanSpace ℂ ι)
  (hee : ∀ i j, (Hf (e i) (e j)).im = 0)
  (hef : ∀ i j, (Hf (e i) (f j)).im = if i = j then 1 else 0)
def Phi (z : Fin (Fintype.card ι) → ℂ) : EuclideanSpace ℂ ι := ∑ i, z i • e i
def tau (j : Fin (Fintype.card ι)) : Fin (Fintype.card ι) → ℂ := fun l => (eb e f hee hef).repr (f j) l
def S (i l : Fin (Fintype.card ι)) : ℂ := Hf (e i) (e l)
def Qf (z : Fin (Fintype.card ι) → ℂ) : ℂ := ∑ i, ∑ l, z i * z l * S e i l
end Gauge
section Final
variable (e f : Fin (Fintype.card ι) → EuclideanSpace ℂ ι)
  (hee : ∀ i j, (Hf (e i) (e j)).im = 0)
  (hef : ∀ i j, (Hf (e i) (f j)).im = if i = j then 1 else 0)
def Lk (l : Fin (Fintype.card ι)) : ℂ := Complex.log (Y.ka (e l))
def hF (q : ℕ) (F : EuclideanSpace ℂ ι → ℂ) (z : Fin (Fintype.card ι) → ℂ) : ℂ :=
  F (Phi e z) * cexp (-((q : ℂ) * Real.pi / 2) * Qf e z - ∑ l, Lk Y e l * z l)
theorem hF_diff (q : ℕ) (F : EuclideanSpace ℂ ι → ℂ) (hd : Differentiable ℂ F) :
    Differentiable ℂ (hF Y e q F) := by
  have hPhi : Differentiable ℂ (Phi e) := by
    unfold Phi
    first
      | fun_prop
      | exact Differentiable.sum fun i _ => (differentiable_apply i).smul_const (e i)
  have hQ : Differentiable ℂ (Qf e) := by
    unfold Qf
    first
      | fun_prop
      | exact Differentiable.sum fun i _ => Differentiable.sum fun l _ =>
          ((differentiable_apply i).mul (differentiable_apply l)).mul_const _
  have hL : Differentiable ℂ (fun z : Fin (Fintype.card ι) → ℂ => ∑ l, Lk Y e l * z l) := by
    first
      | fun_prop
      | exact Differentiable.sum fun l _ => (differentiable_apply l).const_mul _
  unfold hF
  exact (hd.comp hPhi).mul (((differentiable_const _).mul hQ).sub hL).cexp
end Final
section Count
theorem av_int {k : ℕ} (Ψ : (Fin k → ℂ) → ℂ) (hc : Continuous Ψ) (w : Fin k → ℂ) :
    MeasureTheory.IntegrableOn (fun x => Ψ (DimB.rl x + w)) (DimB.ubox k) := by
  have hrl : Continuous fun x : Fin k → ℝ => DimB.rl x := by
    unfold DimB.rl
    fun_prop
  have hcont : Continuous fun x : Fin k → ℝ => Ψ (DimB.rl x + w) :=
    hc.comp (hrl.add continuous_const)
  refine (hcont.integrableOn_Icc (a := 0) (b := 1)).mono_set ?_
  intro x hx
  refine Set.mem_Icc.2 ⟨Pi.le_def.2 fun i => ?_, Pi.le_def.2 fun i => ?_⟩
  · have h := hx i
    simp only [Set.mem_Ioc, Pi.zero_apply, zero_add] at h
    exact h.1.le
  · have h := hx i
    simp only [Set.mem_Ioc, Pi.zero_apply, zero_add] at h
    exact h.2
theorem Av_add {k : ℕ} (Ψ Ψ' : (Fin k → ℂ) → ℂ) (hc : Continuous Ψ) (hc' : Continuous Ψ')
    (w : Fin k → ℂ) : DimB.Av (fun z => Ψ z + Ψ' z) w = DimB.Av Ψ w + DimB.Av Ψ' w := by
  simp only [DimB.Av]
  exact MeasureTheory.integral_add (av_int Ψ hc w) (av_int Ψ' hc' w)
theorem Av_smul {k : ℕ} (Ψ : (Fin k → ℂ) → ℂ) (c : ℂ) (w : Fin k → ℂ) :
    DimB.Av (fun z => c * Ψ z) w = c * DimB.Av Ψ w := by
  simp only [DimB.Av]
  first
    | exact MeasureTheory.integral_const_mul c _
    | exact MeasureTheory.integral_mul_left c _
variable (e f : Fin (Fintype.card ι) → EuclideanSpace ℂ ι)
  (hee : ∀ i j, (Hf (e i) (e j)).im = 0)
  (hef : ∀ i j, (Hf (e i) (f j)).im = if i = j then 1 else 0)
def T (q : ℕ) : Y.Sec q →ₗ[ℂ] ((Fin (Fintype.card ι) → Fin q) → ℂ) where
  toFun F := fun r => DimB.Av (DimB.Pm (hF Y e q F.1) (fun l => ((r l : ℕ) : ℤ))) 0
  map_add' F G := by
    funext r
    have h1 : DimB.Pm (hF Y e q (F + G).1) (fun l => ((r l : ℕ) : ℤ)) =
        fun z => DimB.Pm (hF Y e q F.1) (fun l => ((r l : ℕ) : ℤ)) z +
          DimB.Pm (hF Y e q G.1) (fun l => ((r l : ℕ) : ℤ)) z := by
      funext z; simp only [DimB.Pm, hF, Submodule.coe_add, Pi.add_apply]; ring
    rw [Pi.add_apply, h1, Av_add]
    · exact (DimB.Pm_diff _ (hF_diff Y e q F.1 F.2.1) _).continuous
    · exact (DimB.Pm_diff _ (hF_diff Y e q G.1 G.2.1) _).continuous
  map_smul' c F := by
    funext r
    have h1 : DimB.Pm (hF Y e q (c • F).1) (fun l => ((r l : ℕ) : ℤ)) =
        fun z => c * DimB.Pm (hF Y e q F.1) (fun l => ((r l : ℕ) : ℤ)) z := by
      funext z; simp only [DimB.Pm, hF, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]; ring
    rw [Pi.smul_apply, h1, Av_smul, RingHom.id_apply, smul_eq_mul]
end Count
end DimC
end
end ReciprocityTheory.ChartRestriction.G.I2


