-- Prove2me | solution 1 for Auto.HeatData.smeared_plane_dissipation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:37:23.298475+00:00
-- url     : https://prove2.me/submissions/a34c6009-2a59-480f-8d12-c198c21b618a

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_hasDerivAt_gaussianD_variance
public import Theorems.Thm_Auto_HeatData_e_heat_s
public import Theorems.Thm_Auto_sum_three_eq
public import Theorems.Thm_Auto_good_integrable
public import Theorems.Thm_Auto_HeatData_family_good
public import Theorems.Thm_Auto_HeatData_vertex_identities
public import Theorems.Thm_Auto_HeatData_pointwise_dissipation

set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
open Auto
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
open Auto.HeatData
variable (Hd : HeatData ι) (α : Fin 3 → ℝ) (η : ℝ)
namespace Auto.HeatData
theorem _root_.solution (hh : 0 < Hd.h) (hη : 0 < η)
    (hα : ∀ k, α k = 1 ∨ α k = 11 / 10) (hsum : α 0 + α 1 + α 2 = 16 / 5) {sa sb : ℝ}
    (hsa : 0 < sa) (hab : sa ≤ sb) :
    (1 / 28) * ∫ s in sa..sb, ∑ v, Hd.Vbar α η v s ≤ Hd.Jbar α η sa - Hd.Jbar α η sb := by
  set β : ℝ := 1 / 10 with hβdef
  have hβ : 0 < β := by norm_num
  have hα1 : ∀ k, 1 ≤ α k := fun k => by rcases hα k with h | h <;> rw [h]; norm_num
  have hα2 : ∀ k, α k ≤ 2 := fun k => by rcases hα k with h | h <;> rw [h] <;> norm_num
  have hα0 : ∀ k, 0 < α k := fun k => zero_lt_one.trans_le (hα1 k)
  have hsb : 0 < 2 * sb := by linarith
  have G := fun v => Hd.family_good α η v hh hη hα1 hα2 hsa hab
  have slice : ∀ v, ∀ Q ∈ ({Hd.qE α η v, Hd.qDr α η v, Hd.qDn α η v, Hd.qDp α η v,
      Hd.qV α η v + Hd.qA α η v, Hd.qYn α η v + Hd.qB α η v, Hd.qYp α η v + Hd.qC α η v,
      Hd.qZ α η v, Hd.qV α η v, Hd.qYn α η v, Hd.qYp α η v, Hd.qA α η v, Hd.qB α η v,
      Hd.qC α η v} : Set (ℝ → (Fin 3 → ℝ) → ℝ)), ∀ m, ∀ s ∈ Set.Icc sa sb,
      Integrable (fun p => Gm β m s p * Q s p) := fun v Q hQ m =>
    (good_integrable (Q := fun z => Q z.1 z.2) hsa hsb hβ v (G v Q hQ).1 (G v Q hQ).2 m).1
  have joint : ∀ v, ∀ Q ∈ ({Hd.qE α η v, Hd.qDr α η v, Hd.qDn α η v, Hd.qDp α η v,
      Hd.qV α η v + Hd.qA α η v, Hd.qYn α η v + Hd.qB α η v, Hd.qYp α η v + Hd.qC α η v,
      Hd.qZ α η v, Hd.qV α η v, Hd.qYn α η v, Hd.qYp α η v, Hd.qA α η v, Hd.qB α η v,
      Hd.qC α η v} : Set (ℝ → (Fin 3 → ℝ) → ℝ)), ∀ m,
      Integrable (fun z : ℝ × (Fin 3 → ℝ) => Gm β m z.1 z.2 * Q z.1 z.2) ((volume.restrict (Set.Ioc
          sa sb)).prod volume) := fun v Q hQ m =>
    (good_integrable (Q := fun z => Q z.1 z.2) hsa hsb hβ v (G v Q hQ).1 (G v Q hQ).2 m).2
  set F : ℝ → (Fin 3 → ℝ) → ℝ := fun s p => Gm β 0 s p * ∑ v, Hd.qE α η v s p with hF
  set Φ : Fin 3 → ℝ × (Fin 3 → ℝ) → ℝ := fun v z =>
    β / 2 * (Gm β 2 z.1 z.2 * Hd.qE α η v z.1 z.2) +
      α v / 2 * (Gm β 0 z.1 z.2 * Hd.qA α η v z.1 z.2) +
      α (v + 1) / 2 * (Gm β 0 z.1 z.2 * Hd.qB α η v z.1 z.2) +
      α (v - 1) / 2 * (Gm β 0 z.1 z.2 * Hd.qC α η v z.1 z.2) with hΦ
  set Fs : ℝ → (Fin 3 → ℝ) → ℝ := fun s p => ∑ v, Φ v (s, p) with hFs
  have hderiv : ∀ p, ∀ s, 0 < s → HasDerivAt (fun t => F t p) (Fs s p) s := by
    intro p s hs
    have hG0 : HasDerivAt (fun t => Gm β 0 t p) (gaussianD 2 (β * s) (p 0 + p 1 + p 2) / 2 * β)
        s := by
      have := (hasDerivAt_gaussianD_variance 0 (mul_pos hβ hs) (p 0 + p 1 + p 2)).comp s
          ((hasDerivAt_id s).const_mul β)
      simpa [Gm, Function.comp_def] using this
    have hE : HasDerivAt (fun t => ∑ v, Hd.qE α η v t p) (∑ v, (α v * Hd.qA α η v s p + α (v + 1) *
        Hd.qB α η v s p +
          α (v - 1) * Hd.qC α η v s p) / 2) s :=
      HasDerivAt.fun_sum fun v _ => Hd.e_heat_s p hh hη hα0 hs v
    refine (hG0.mul hE).congr_deriv ?_
    simp only [hFs, hΦ, Gm, Fin.sum_univ_three]
    ring
  have mem : ∀ v, ∀ Q, Q = Hd.qE α η v ∨ Q = Hd.qA α η v ∨ Q = Hd.qB α η v ∨
      Q = Hd.qC α η v ∨ Q = Hd.qV α η v → Q ∈ ({Hd.qE α η v, Hd.qDr α η v, Hd.qDn α η v,
      Hd.qDp α η v, Hd.qV α η v + Hd.qA α η v, Hd.qYn α η v + Hd.qB α η v,
      Hd.qYp α η v + Hd.qC α η v, Hd.qZ α η v, Hd.qV α η v, Hd.qYn α η v, Hd.qYp α η v,
      Hd.qA α η v, Hd.qB α η v, Hd.qC α η v} : Set (ℝ → (Fin 3 → ℝ) → ℝ)) := by
    intro v Q hQ
    rcases hQ with rfl | rfl | rfl | rfl | rfl <;> simp
  have hΦint : ∀ v, Integrable (Φ v) ((volume.restrict (Set.Ioc sa sb)).prod volume) := by
    intro v
    exact ((((joint v _ (mem v _ (Or.inl rfl)) 2).const_mul (β / 2)).add ((joint v _ (mem v _
        (Or.inr (Or.inl rfl))) 0).const_mul (α v / 2))).add ((joint v _ (mem v _ (Or.inr (Or.inr
        (Or.inl rfl)))) 0).const_mul (α (v + 1) / 2))).add ((joint v _ (mem v _ (Or.inr (Or.inr
        (Or.inr (Or.inl rfl))))) 0).const_mul (α (v - 1) / 2))
  have hFsint : Integrable (fun z : ℝ × (Fin 3 → ℝ) => Fs z.1 z.2) ((volume.restrict (Set.Ioc sa
      sb)).prod volume) :=
    integrable_finsetSum _ fun v _ => hΦint v
  have hFint : ∀ s ∈ Set.Icc sa sb, Integrable (F s) := by
    intro s hs
    have : F s = fun p => ∑ v, Gm β 0 s p * Hd.qE α η v s p := by
      funext p; simp only [hF, Finset.mul_sum]
    rw [this]
    exact integrable_finsetSum _ fun v _ => slice v _ (mem v _ (Or.inl rfl)) 0 s hs
  have hVint : ∀ v, Integrable (fun z : ℝ × (Fin 3 → ℝ) => Gm β 0 z.1 z.2 * Hd.qV α η v z.1 z.2)
      ((volume.restrict (Set.Ioc sa sb)).prod volume) := fun v =>
    joint v _ (mem v _ (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) 0
  have hstep : ∀ s ∈ Set.Icc sa sb, ∫ p, Fs s p ≤ -(1 / 28) * ∑ v, Hd.Vbar α η v s := by
    intro s hs
    have hs0 : 0 < s := hsa.trans_le hs.1
    have hσ : ∀ k, 0 < sig α s k := fun k => mul_pos (hα0 k) hs0
    have sl := fun v Q (hQ : Q ∈ ({Hd.qE α η v, Hd.qDr α η v, Hd.qDn α η v, Hd.qDp α η v,
      Hd.qV α η v + Hd.qA α η v, Hd.qYn α η v + Hd.qB α η v, Hd.qYp α η v + Hd.qC α η v,
      Hd.qZ α η v, Hd.qV α η v, Hd.qYn α η v, Hd.qYp α η v, Hd.qA α η v, Hd.qB α η v,
      Hd.qC α η v} : Set (ℝ → (Fin 3 → ℝ) → ℝ))) m => slice v Q hQ m s hs
    set K : Fin 3 → (Fin 3 → ℝ) → ℝ := fun v p =>
      β / 2 * (Gm β 2 s p * Hd.qE α η v s p) +
        α v / 2 * (Gm β 0 s p * (Hd.qV α η v + Hd.qA α η v) s p) +
        α (v + 1) / 2 * (Gm β 0 s p * (Hd.qYn α η v + Hd.qB α η v) s p) +
        α (v - 1) / 2 * (Gm β 0 s p * (Hd.qYp α η v + Hd.qC α η v) s p) -
        33 / 20 * (Gm β 0 s p * Hd.qZ α η v s p) with hK
    have hKint : ∀ v, Integrable (K v) := fun v =>
      (((((sl v _ (by simp) 2).const_mul (β / 2)).add ((sl v _ (by simp) 0).const_mul (α v /
          2))).add ((sl v _ (by simp) 0).const_mul (α (v + 1) / 2))).add ((sl v _ (by simp)
          0).const_mul (α (v - 1) / 2))).sub ((sl v (Hd.qZ α η v) (by simp) 0).const_mul (33 / 20))
    have hK0 : ∀ v, ∫ p, K v p = 0 := by
      intro v
      obtain ⟨i1, i2, i3, i4⟩ := Hd.vertex_identities α η v hh hη hα1 hα2 hβ hsa hab hs
      have hsv := (sum_three_eq v α).1
      simp only [hK]
      rw [integral_sub, integral_add, integral_add, integral_add, integral_const_mul,
        integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul, i1, i2,
        i3, i4]
      · have hs3 : α v + α (v + 1) + α (v - 1) = 16 / 5 := by linarith
        linear_combination ((∫ p, Gm β 2 s p * Hd.qE α η v s p) / 2) * hs3 + ((∫ p, Gm β 2 s p *
            Hd.qE α η v s p) / 2) * hβdef
      all_goals first
        | exact (sl v _ (by simp) _).const_mul _
        | exact ((sl v _ (by simp) _).const_mul _).add ((sl v _ (by simp) _).const_mul _)
        | exact (((sl v _ (by simp) _).const_mul _).add ((sl v _ (by simp) _).const_mul _)).add ((sl
            v _ (by simp) _).const_mul _)
        | exact ((((sl v _ (by simp) _).const_mul _).add ((sl v _ (by simp) _).const_mul _)).add
            ((sl v _ (by simp) _).const_mul _)).add ((sl v _ (by simp) _).const_mul _)
    set H : (Fin 3 → ℝ) → ℝ := fun p => ∑ v, (33 / 20 * Hd.qZ α η v s p - (α v * Hd.qV α η v s p + α
        (v + 1) * Hd.qYn α η v s p +
        α (v - 1) * Hd.qYp α η v s p) / 2) with hH
    have hsplit : ∀ p, Fs s p = Gm β 0 s p * H p + ∑ v, K v p := by
      intro p
      simp only [hFs, hΦ, hH, hK, Pi.add_apply, Fin.sum_univ_three]
      ring
    have hHint : Integrable (fun p => Gm β 0 s p * H p) := by
      have : (fun p => Gm β 0 s p * H p) = fun p => ∑ v, (33 / 20 * (Gm β 0 s p * Hd.qZ α η v s p) -
          (α v * (Gm β 0 s p * Hd.qV α η v s p) + α (v + 1) * (Gm β 0 s p * Hd.qYn α η v s p) +
              α (v - 1) * (Gm β 0 s p * Hd.qYp α η v s p)) / 2) := by
        funext p; simp only [hH, Finset.mul_sum]; refine Finset.sum_congr rfl fun v _ => ?_; ring
      rw [this]
      refine integrable_finsetSum _ fun v _ => ?_
      exact ((sl v _ (by simp) 0).const_mul _).sub (((((sl v _ (by simp) 0).const_mul _).add ((sl v
          _ (by simp) 0).const_mul _)).add ((sl v _ (by simp) 0).const_mul _)).div_const _)
    have hG0nn : ∀ p, 0 ≤ Gm β 0 s p := fun p => by
      simp only [Gm, gaussianD_zero, gaussian]; positivity
    have hpt : ∀ p, Gm β 0 s p * H p ≤ -(1 / 28) * ∑ v, Gm β 0 s p * Hd.qV α η v s p := by
      intro p
      have := Hd.pointwise_dissipation hh hη p (sig α s) hσ hα hsum
      rw [← Finset.mul_sum]
      have h' := mul_le_mul_of_nonneg_left this (hG0nn p)
      simp only [hH]
      unfold qZ qV qYn qYp
      linarith
    calc ∫ p, Fs s p = ∫ p, (Gm β 0 s p * H p + ∑ v, K v p) := by
          congr 1; funext p; exact hsplit p
      _ = ∫ p, Gm β 0 s p * H p := by
          rw [integral_add hHint (integrable_finsetSum _ fun v _ => hKint v),
            integral_finsetSum _ fun v _ => hKint v]
          simp [hK0]
      _ ≤ ∫ p, -(1 / 28) * ∑ v, Gm β 0 s p * Hd.qV α η v s p :=
          integral_mono hHint ((integrable_finsetSum _ fun v _ =>
            sl v _ (by simp) 0).const_mul _) hpt
      _ = -(1 / 28) * ∑ v, Hd.Vbar α η v s := by
          rw [integral_const_mul, integral_finsetSum _ fun v _ => sl v _ (by simp) 0]
          rfl
  have hIoc : Set.uIoc sa sb = Set.Ioc sa sb := Set.uIoc_of_le hab
  have hae : ∀ᵐ p ∂(volume : Measure (Fin 3 → ℝ)),
      IntervalIntegrable (fun s => Fs s p) volume sa sb := by
    filter_upwards [hFsint.prod_left_ae] with p hp
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2 hp
  have hFTC : ∀ᵐ p ∂(volume : Measure (Fin 3 → ℝ)),
      ∫ s in sa..sb, Fs s p = F sb p - F sa p := by
    filter_upwards [hae] with p hp
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s hs => hderiv p s ?_) hp
    rw [Set.uIcc_of_le hab] at hs
    exact hsa.trans_le hs.1
  have hswap : ∫ p, ∫ s in sa..sb, Fs s p = ∫ s in sa..sb, ∫ p, Fs s p := by
    refine (intervalIntegral_integral_swap ?_).symm
    rw [hIoc]
    exact hFsint
  have hJ : Hd.Jbar α η sb - Hd.Jbar α η sa = ∫ s in sa..sb, ∫ p, Fs s p := by
    rw [← hswap, Jbar, Jbar, ← integral_sub (hFint sb ⟨hab, le_rfl⟩) (hFint sa ⟨le_rfl, hab⟩)]
    exact integral_congr_ae (hFTC.mono fun p hp => hp.symm)
  have hint1 : IntervalIntegrable (fun s => ∫ p, Fs s p) volume sa sb :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2 hFsint.integral_prod_left
  have hint2 : IntervalIntegrable (fun s => -(1 / 28) * ∑ v, Hd.Vbar α η v s) volume sa sb := by
    refine ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2 ?_).const_mul _
    exact integrable_finsetSum _ fun v _ => (hVint v).integral_prod_left
  have hmono := intervalIntegral.integral_mono_on hab hint1 hint2 hstep
  rw [intervalIntegral.integral_const_mul] at hmono
  linarith
end Auto.HeatData
