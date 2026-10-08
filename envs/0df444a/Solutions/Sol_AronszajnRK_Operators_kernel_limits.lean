-- Prove2me | solution 1 for AronszajnRK.Operators.kernel_limits
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T11:57:57.341002+00:00
-- url     : https://prove2.me/submissions/d18d85f5-a72e-4581-b6b2-f0594d929658

import Mathlib
import Definitions.Def_AronszajnRK_Sum_kernelFn
import Definitions.Def_AronszajnRK_Operators_opKernel

open scoped InnerProductSpace Topology
open Filter

set_option autoImplicit false

namespace P869438ba

open ComplexConjugate

lemma eval_eq_inner {H : Type*} {X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [RKHS ℂ H X ℂ] (f : H) (x : X) :
    f x = ⟪RKHS.kerFun H x (1 : ℂ), f⟫_ℂ := by
  rw [RKHS.kerFun_inner]
  simp

lemma opKernel_eq {H : Type*} {X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [RKHS ℂ H X ℂ] (L : H →L[ℂ] H) (x y : X) :
    AronszajnRK.Operators.opKernel L x y
      = conj ⟪RKHS.kerFun H y (1 : ℂ), L (RKHS.kerFun H x (1 : ℂ))⟫_ℂ := by
  unfold AronszajnRK.Operators.opKernel
  rw [eval_eq_inner _ x, ContinuousLinearMap.adjoint_inner_right, inner_conj_symm]

lemma opKernel_sub {H : Type*} {X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [RKHS ℂ H X ℂ] (A B : H →L[ℂ] H) (x y : X) :
    AronszajnRK.Operators.opKernel A x y - AronszajnRK.Operators.opKernel B x y
      = conj ⟪RKHS.kerFun H y (1 : ℂ), (A - B) (RKHS.kerFun H x (1 : ℂ))⟫_ℂ := by
  rw [opKernel_eq, opKernel_eq, ContinuousLinearMap.sub_apply, inner_sub_right, map_sub]

lemma norm_kerFun_sq {H : Type*} {X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [RKHS ℂ H X ℂ] (x : X) :
    ‖RKHS.kerFun H x (1 : ℂ)‖ ^ 2 = ‖AronszajnRK.Sum.kernelFn H x x‖ := by
  have h1 : ⟪RKHS.kerFun H x (1 : ℂ), RKHS.kerFun H x (1 : ℂ)⟫_ℂ
      = AronszajnRK.Sum.kernelFn H x x := by
    rw [← eval_eq_inner, RKHS.kerFun_apply]
    rfl
  rw [← h1, inner_self_eq_norm_sq_to_K]
  simp

end P869438ba

open scoped InnerProductSpace Topology in open Filter in open ComplexConjugate in open AronszajnRK.Operators in
theorem solution {H : Type*} {X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [RKHS ℂ H X ℂ] (L : H →L[ℂ] H) (Ls : ℕ → H →L[ℂ] H) :
    ((∀ u v : H, Tendsto (fun n => ⟪v, Ls n u⟫_ℂ) atTop (𝓝 ⟪v, L u⟫_ℂ)) →
        ∀ x y : X, Tendsto (fun n => opKernel (Ls n) x y) atTop (𝓝 (opKernel L x y))) ∧
      (Tendsto (fun n => ‖Ls n - L‖) atTop (𝓝 0) →
        ∀ S : Set (X × X),
          (∃ C : ℝ, ∀ p ∈ S, ‖AronszajnRK.Sum.kernelFn H p.1 p.1‖ ≤ C ∧ ‖AronszajnRK.Sum.kernelFn H p.2 p.2‖ ≤ C) →
            TendstoUniformlyOn (fun n (p : X × X) => opKernel (Ls n) p.1 p.2)
              (fun p => opKernel L p.1 p.2) atTop S) := by
  constructor
  · intro hw x y
    simp only [P869438ba.opKernel_eq]
    exact (Complex.continuous_conj.tendsto _).comp
      (hw (RKHS.kerFun H x (1 : ℂ)) (RKHS.kerFun H y (1 : ℂ)))
  · intro hn S ⟨C, hC⟩
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    set C' : ℝ := max C 0 + 1 with hC'
    have hC'pos : 0 < C' := by positivity
    have hev : ∀ᶠ n in atTop, ‖Ls n - L‖ < ε / C' :=
      (tendsto_order.1 hn).2 _ (div_pos hε hC'pos)
    filter_upwards [hev] with n hn'
    intro p hp
    obtain ⟨h1, h2⟩ := hC p hp
    set a := ‖RKHS.kerFun H p.1 (1 : ℂ)‖
    set b := ‖RKHS.kerFun H p.2 (1 : ℂ)‖
    have ha : a ^ 2 ≤ C := by rw [P869438ba.norm_kerFun_sq]; exact h1
    have hb : b ^ 2 ≤ C := by rw [P869438ba.norm_kerFun_sq]; exact h2
    have hab : b * a ≤ C' := by
      nlinarith [sq_nonneg (a - b), le_max_left C 0, norm_nonneg (RKHS.kerFun H p.1 (1 : ℂ)),
        norm_nonneg (RKHS.kerFun H p.2 (1 : ℂ))]
    rw [dist_comm, dist_eq_norm, P869438ba.opKernel_sub, Complex.norm_conj]
    calc ‖⟪RKHS.kerFun H p.2 (1 : ℂ), (Ls n - L) (RKHS.kerFun H p.1 (1 : ℂ))⟫_ℂ‖
        ≤ b * ‖(Ls n - L) (RKHS.kerFun H p.1 (1 : ℂ))‖ := norm_inner_le_norm _ _
      _ ≤ b * (‖Ls n - L‖ * a) :=
          mul_le_mul_of_nonneg_left ((Ls n - L).le_opNorm _) (norm_nonneg _)
      _ = ‖Ls n - L‖ * (b * a) := by ring
      _ ≤ ‖Ls n - L‖ * C' := mul_le_mul_of_nonneg_left hab (norm_nonneg _)
      _ < ε / C' * C' := mul_lt_mul_of_pos_right hn' hC'pos
      _ = ε := div_mul_cancel₀ ε hC'pos.ne'
