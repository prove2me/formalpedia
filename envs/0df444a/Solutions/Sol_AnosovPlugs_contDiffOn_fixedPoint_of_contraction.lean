-- Prove2me | solution 1 for AnosovPlugs.contDiffOn_fixedPoint_of_contraction
-- status  : ACCEPTED   (prove)
-- author  : @ebayuser
-- created : 2026-10-04T09:37:13.097145+00:00
-- url     : https://prove2.me/submissions/5d005097-5084-4f7d-97c6-63649c503a24

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing

open scoped Manifold ContDiff Topology
open Set AnosovPlugs

theorem fx_contDiffAt_fixedPoint
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
    (T : P → B → B) (hT : ContDiff ℝ 1 (fun q : P × B => T q.1 q.2))
    (U : Set P) (hU : IsOpen U)
    (hlip : ∀ p ∈ U, ∃ K : NNReal, K < 1 ∧ LipschitzWith K (T p))
    (fp : P → B) (hfp : ∀ p ∈ U, T p (fp p) = fp p) (p₀ : P) (hp₀ : p₀ ∈ U) :
    ContDiffAt ℝ 1 fp p₀ := by
  set F : P × B → B := fun q => q.2 - T q.1 q.2 with hFdef
  set u : P × B := (p₀, fp p₀) with hu
  have hF : ContDiff ℝ 1 F := contDiff_snd.sub hT
  have cdf : ContDiffAt ℝ 1 F u := hF.contDiffAt
  have hTp : DifferentiableAt ℝ (T p₀) (fp p₀) := by
    have h1 : DifferentiableAt ℝ (fun q : P × B => T q.1 q.2) (p₀, fp p₀) :=
      hT.contDiffAt.differentiableAt one_ne_zero
    have h2 : DifferentiableAt ℝ (fun γ : B => (p₀, γ)) (fp p₀) :=
      (differentiableAt_const p₀).prodMk differentiableAt_id
    exact h1.comp (fp p₀) h2
  set D := fderiv ℝ (T p₀) (fp p₀) with hD
  have hcomp : HasFDerivAt (fun γ : B => F (p₀, γ))
      ((fderiv ℝ F u).comp (ContinuousLinearMap.inr ℝ P B)) (fp p₀) :=
    (cdf.differentiableAt one_ne_zero).hasFDerivAt.comp (fp p₀)
      (hasFDerivAt_prodMk_right p₀ (fp p₀))
  have hpart : HasFDerivAt (fun γ : B => F (p₀, γ))
      (ContinuousLinearMap.id ℝ B - D) (fp p₀) :=
    (hasFDerivAt_id (fp p₀)).sub hTp.hasFDerivAt
  have heq : (fderiv ℝ F u).comp (ContinuousLinearMap.inr ℝ P B) =
      ContinuousLinearMap.id ℝ B - D := hcomp.unique hpart
  obtain ⟨K, hK1, hKl⟩ := hlip p₀ hp₀
  have hDn : ‖D‖ < 1 :=
    lt_of_le_of_lt (norm_fderiv_le_of_lipschitz ℝ hKl) (by exact_mod_cast hK1)
  have hunit : IsUnit (ContinuousLinearMap.id ℝ B - D) := by
    change IsUnit ((1 : B →L[ℝ] B) - D)
    exact isUnit_one_sub_of_norm_lt_one hDn
  have if₂ : ((fderiv ℝ F u).comp (ContinuousLinearMap.inr ℝ P B)).IsInvertible := by
    rw [heq]
    exact ⟨ContinuousLinearEquiv.ofUnit hunit.unit, rfl⟩
  set ψ := cdf.implicitFunction one_ne_zero if₂ with hψ
  have hψcd : ContDiffAt ℝ 1 ψ p₀ := cdf.contDiffAt_implicitFunction one_ne_zero if₂
  have hev : ∀ᶠ x in 𝓝 p₀, F (x, ψ x) = F u :=
    cdf.eventually_apply_implicitFunction one_ne_zero if₂
  have hFu : F u = 0 := by
    simp only [hFdef, hu, hfp p₀ hp₀, sub_self]
  have hfpψ : fp =ᶠ[𝓝 p₀] ψ := by
    filter_upwards [hev, hU.mem_nhds hp₀] with x hx hxU
    rw [hFu] at hx
    have hfix : T x (ψ x) = ψ x := (sub_eq_zero.mp hx).symm
    obtain ⟨Kx, hKx1, hKxl⟩ := hlip x hxU
    have hc : ContractingWith Kx (T x) := ⟨hKx1, hKxl⟩
    exact hc.fixedPoint_unique' (hfp x hxU) hfix
  exact hψcd.congr_of_eventuallyEq hfpψ

theorem solution
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
    (T : P → B → B) (hT : ContDiff ℝ 1 (fun q : P × B => T q.1 q.2))
    (U : Set P) (hU : IsOpen U)
    (hlip : ∀ p ∈ U, ∃ K : NNReal, K < 1 ∧ LipschitzWith K (T p))
    (fp : P → B) (hfp : ∀ p ∈ U, T p (fp p) = fp p) :
    ContDiffOn ℝ 1 fp U := fun p hp =>
  (fx_contDiffAt_fixedPoint T hT U hU hlip fp hfp p hp).contDiffWithinAt
