-- Prove2me | solution 1 for AronszajnRK.Operators.kernel_double_series
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T12:16:19.394449+00:00
-- url     : https://prove2.me/submissions/517ff8e3-e5f2-4c74-96c2-67f6c1aa40fe

import Mathlib
import Definitions.Def_AronszajnRK_Operators_opKernel

set_option autoImplicit false

open scoped InnerProductSpace Topology
open ComplexConjugate Filter

open scoped InnerProductSpace Topology in open ComplexConjugate Filter AronszajnRK.Operators in
theorem solution {H : Type*} {X : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [RKHS ℂ H X ℂ] {ι κ : Type*}
    (g₁ : HilbertBasis ι ℂ H) (g₂ : HilbertBasis κ ℂ H) (L : H →L[ℂ] H) (x y : X) :
    Tendsto (fun PQ : Finset ι × Finset κ => ∑ m ∈ PQ.1, ∑ n ∈ PQ.2,
        ⟪L (g₁ m), g₂ n⟫_ℂ * (g₁ m) x * conj ((g₂ n) y))
      (atTop ×ˢ atTop) (𝓝 (opKernel L x y)) := by
  set a : H := RKHS.kerFun H x (1 : ℂ) with ha_def
  set b : H := RKHS.kerFun H y (1 : ℂ) with hb_def
  -- evaluation as inner product
  have hev : ∀ (f : H) (z : X), f z = ⟪RKHS.kerFun H z (1 : ℂ), f⟫_ℂ := by
    intro f z
    rw [RKHS.kerFun_inner]
    simp
  have ha : Tendsto (fun P : Finset ι => ∑ m ∈ P, g₁.repr a m • g₁ m) atTop (𝓝 a) :=
    g₁.hasSum_repr a
  have hb : Tendsto (fun Q : Finset κ => ∑ n ∈ Q, g₂.repr b n • g₂ n) atTop (𝓝 b) :=
    g₂.hasSum_repr b
  have hpair := ha.prodMap hb
  rw [← nhds_prod_eq] at hpair
  have hcont : Continuous (fun p : H × H => ⟪L p.1, p.2⟫_ℂ) :=
    (L.continuous.comp continuous_fst).inner continuous_snd
  have hlim := (hcont.tendsto (a, b)).comp hpair
  have hval : opKernel L x y = ⟪L a, b⟫_ℂ := by
    unfold opKernel
    rw [hev, ContinuousLinearMap.adjoint_inner_right]
  rw [hval]
  have key : ∀ PQ : Finset ι × Finset κ,
      ⟪L (∑ m ∈ PQ.1, g₁.repr a m • g₁ m), ∑ n ∈ PQ.2, g₂.repr b n • g₂ n⟫_ℂ =
        ∑ m ∈ PQ.1, ∑ n ∈ PQ.2, ⟪L (g₁ m), g₂ n⟫_ℂ * (g₁ m) x * conj ((g₂ n) y) := by
    intro PQ
    rw [map_sum, sum_inner]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [map_smul, inner_smul_left, inner_smul_right, HilbertBasis.repr_apply_apply,
      HilbertBasis.repr_apply_apply, hev (g₁ m) x, hev (g₂ n) y, ← ha_def, ← hb_def]
    simp only [inner_conj_symm]
    ring
  exact hlim.congr' (Eventually.of_forall fun PQ => key PQ)
