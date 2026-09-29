-- Prove2me | solution 1 for AlgebraicCurve.Differential.pullbackAlong_traceAlong_pullbackAlong_eq_traceAlong_pullbackAlong_pullbackAlong_of_swap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/f98b65c8-7948-52c8-bca6-0ddedd820b4b

import Mathlib
import Definitions.Def_AlgebraicCurve_DifferentialPushPull
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Differential_pullbackAlong_traceAlong_pullbackAlong_eq_traceAlong_pullbackAlong_pullbackAlong_of_swap

set_option autoImplicit false

open AlgebraicCurve KaehlerDifferential
open scoped TensorProduct

namespace E3WBody

variable {K F F' F'' : Type*} [Field K] [Field F] [Field F'] [Field F'']
  [Algebra K F] [Algebra K F'] [Algebra K F'']

theorem pullbackAlong_comp (f : F →ₐ[K] F') (g : F' →ₐ[K] F'') (ω : Ω[F⁄K]) :
    Differential.pullbackAlong (g.comp f) ω =
      Differential.pullbackAlong g (Differential.pullbackAlong f ω) := by
  have hmem : ω ∈ Submodule.span F (Set.range (D K F)) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hmem using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx
    rw [Differential.pullbackAlong_D, Differential.pullbackAlong_D, Differential.pullbackAlong_D,
      AlgHom.comp_apply]
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul a x _ hx =>
    rw [Differential.pullbackAlong_smul, Differential.pullbackAlong_smul, Differential.pullbackAlong_smul,
      hx, AlgHom.comp_apply]

theorem pullbackAlong_congr {f g : F →ₐ[K] F'} (h : ∀ x, f x = g x) :
    Differential.pullbackAlong f = Differential.pullbackAlong g := by
  have : f = g := AlgHom.ext h
  subst this; rfl

theorem pullbackAlong_traceAlong_of_conj (φ φ' : F →ₐ[K] F') (hφ : SeparableAlong K φ)
    (hφ' : SeparableAlong K φ') (w : F ≃ₐ[K] F) (w' : F' ≃ₐ[K] F')
    (hconj : ∀ x : F, w' (φ x) = φ' (w x)) (η : Ω[F'⁄K]) :
    Differential.pullbackAlong (w : F →ₐ[K] F) (Differential.traceAlong φ η) =
      Differential.traceAlong φ' (Differential.pullbackAlong (w' : F' →ₐ[K] F') η) := by

  have htrace : ∀ u : F',
      (letI := algebraAlong φ'; Algebra.trace F F' (w' u)) =
        w (letI := algebraAlong φ; Algebra.trace F F' u) := by
    intro u
    have he : RingHom.comp (@algebraMap F F' _ _ (algebraAlong φ')) ↑(w : F ≃+* F) =
        RingHom.comp ↑(w' : F' ≃+* F') (@algebraMap F F' _ _ (algebraAlong φ)) := by
      ext x
      exact (hconj x).symm
    have := @Algebra.trace_eq_of_equiv_equiv F F' F F' _ _ _ _ (algebraAlong φ) (algebraAlong φ')
      (w : F ≃+* F) (w' : F' ≃+* F') he u
    rw [this]
    exact (RingEquiv.apply_symm_apply (w : F ≃+* F) _).symm

  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI : Algebra.IsSeparable F F' := hφ
  haveI : Algebra.FormallyEtale F F' := Algebra.FormallyEtale.of_isSeparable F F'
  obtain ⟨t, rfl⟩ := (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K F F').surjective η
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul u ω =>
    have h1 : (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K F F') (u ⊗ₜ ω) =
        u • Differential.pullbackAlong φ ω := by
      rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply, KaehlerDifferential.mapBaseChange_tmul]
      rfl
    rw [h1, Differential.traceAlong_smul_pullbackAlong φ hφ]

    rw [Differential.pullbackAlong_smul]

    rw [Differential.pullbackAlong_smul, ← pullbackAlong_comp,
      pullbackAlong_congr (f := (w' : F' →ₐ[K] F').comp φ) (g := φ'.comp (w : F →ₐ[K] F))
        (fun x => by simp only [AlgHom.comp_apply, AlgEquiv.coe_algHom]; exact hconj x),
      pullbackAlong_comp, Differential.traceAlong_smul_pullbackAlong φ' hφ']
    show _ = (letI := algebraAlong φ'; Algebra.trace F F' (w' u)) • _
    rw [htrace]
    rfl

end E3WBody

theorem solution
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (α β : F →ₐ[K] F') (hα : SeparableAlong K α) (hβ : SeparableAlong K β)
    (w : F ≃ₐ[K] F) (w' : F' ≃ₐ[K] F')
    (hswapα : ∀ x : F, w' (α x) = β (w x)) (hswapβ : ∀ x : F, w' (β x) = α (w x))
    (ω : Ω[F⁄K]) :
    Differential.pullbackAlong w.toAlgHom (Differential.traceAlong α (Differential.pullbackAlong β ω)) =
      Differential.traceAlong β (Differential.pullbackAlong α (Differential.pullbackAlong w.toAlgHom ω)) := by
  have h := E3WBody.pullbackAlong_traceAlong_of_conj α β hα hβ w w' hswapα (Differential.pullbackAlong β ω)
  rw [h, ← E3WBody.pullbackAlong_comp,
    E3WBody.pullbackAlong_congr (f := (w' : F' →ₐ[K] F').comp β) (g := α.comp (w : F →ₐ[K] F))
      (fun x => by simp only [AlgHom.comp_apply, AlgEquiv.coe_algHom]; exact hswapβ x),
    E3WBody.pullbackAlong_comp]

end S_AlgebraicCurve_Differential_pullbackAlong_traceAlong_pullbackAlong_eq_traceAlong_pullbackAlong_pullbackAlong_of_swap
end P2MW
export P2MW.S_AlgebraicCurve_Differential_pullbackAlong_traceAlong_pullbackAlong_eq_traceAlong_pullbackAlong_pullbackAlong_of_swap (solution)
