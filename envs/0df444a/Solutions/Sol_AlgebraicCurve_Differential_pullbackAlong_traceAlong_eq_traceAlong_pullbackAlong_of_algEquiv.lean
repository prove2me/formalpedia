-- Prove2me | solution 1 for AlgebraicCurve.Differential.pullbackAlong_traceAlong_eq_traceAlong_pullbackAlong_of_algEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/139b821c-0afe-5418-a5ab-8cd7284cb4dc

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_DifferentialPushPull
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Differential_pullbackAlong_traceAlong_eq_traceAlong_pullbackAlong_of_algEquiv

set_option autoImplicit false

open AlgebraicCurve AlgebraicCurve.Differential KaehlerDifferential TensorProduct

namespace TraceNatSol

variable {K F F' F₀ F₀' : Type*} [Field K] [Field F] [Field F'] [Field F₀] [Field F₀']
  [Algebra K F] [Algebra K F'] [Algebra K F₀] [Algebra K F₀']

theorem pullbackAlong_square (φ' : F →ₐ[K] F') (φ : F₀ →ₐ[K] F₀') (θ : F →ₐ[K] F₀) (θ' : F' →ₐ[K] F₀')
    (hφ : ∀ x : F, θ' (φ' x) = φ (θ x)) (ω : Ω[F⁄K]) :
    pullbackAlong θ' (pullbackAlong φ' ω) = pullbackAlong φ (pullbackAlong θ ω) := by
  have key : ∀ ω ∈ Submodule.span F (Set.range (D K F)),
      pullbackAlong θ' (pullbackAlong φ' ω) = pullbackAlong φ (pullbackAlong θ ω) := by
    intro ω hω
    induction hω using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, rfl⟩ := hx
      rw [pullbackAlong_D, pullbackAlong_D, pullbackAlong_D, pullbackAlong_D, hφ]
    | zero => simp only [map_zero]
    | add x y _ _ hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
    | smul a x _ hx =>
      rw [pullbackAlong_smul, pullbackAlong_smul, pullbackAlong_smul, pullbackAlong_smul, hx, hφ]
  exact key ω (by rw [KaehlerDifferential.span_range_derivation]; trivial)

theorem separableAlong_of_algEquiv (φ' : F →ₐ[K] F') (φ : F₀ →ₐ[K] F₀') (θ : F ≃ₐ[K] F₀) (θ' : F' ≃ₐ[K] F₀')
    (hφ : ∀ x : F, θ' (φ' x) = φ (θ x)) (hsep : SeparableAlong K φ') : SeparableAlong K φ := by
  letI := algebraAlong φ'
  letI := algebraAlong φ
  haveI : Algebra.IsSeparable F F' := hsep
  exact Algebra.IsSeparable.of_equiv_equiv θ.toRingEquiv θ'.toRingEquiv (by
    ext x
    exact (hφ x).symm)

theorem trace_of_algEquiv (φ' : F →ₐ[K] F') (φ : F₀ →ₐ[K] F₀') (θ : F ≃ₐ[K] F₀) (θ' : F' ≃ₐ[K] F₀')
    (hφ : ∀ x : F, θ' (φ' x) = φ (θ x)) (u : F') :
    θ (letI := algebraAlong φ'; Algebra.trace F F' u) = (letI := algebraAlong φ; Algebra.trace F₀ F₀' (θ' u)) := by
  letI := algebraAlong φ'
  letI := algebraAlong φ
  have h := Algebra.trace_eq_of_equiv_equiv θ.toRingEquiv θ'.toRingEquiv (by
    ext x
    exact (hφ x).symm) u
  rw [h]
  exact θ.toRingEquiv.apply_symm_apply _

end TraceNatSol

open TraceNatSol in
theorem solution
    {K F F' F₀ F₀' : Type*} [Field K] [Field F] [Field F'] [Field F₀] [Field F₀']
    [Algebra K F] [Algebra K F'] [Algebra K F₀] [Algebra K F₀']
    (φ' : F →ₐ[K] F') (φ : F₀ →ₐ[K] F₀') (θ : F ≃ₐ[K] F₀) (θ' : F' ≃ₐ[K] F₀')
    (hφ : ∀ x : F, θ' (φ' x) = φ (θ x)) (hsep : AlgebraicCurve.SeparableAlong K φ') (η : Ω[F'⁄K]) :
    AlgebraicCurve.Differential.pullbackAlong (θ : F →ₐ[K] F₀) (AlgebraicCurve.Differential.traceAlong φ' η) =
      AlgebraicCurve.Differential.traceAlong φ (AlgebraicCurve.Differential.pullbackAlong (θ' : F' →ₐ[K] F₀') η) := by
  classical
  have hsep₀ : SeparableAlong K φ := separableAlong_of_algEquiv φ' φ θ θ' hφ hsep

  letI := algebraAlong φ'
  haveI := isScalarTower_along φ'
  haveI : Algebra.IsSeparable F F' := hsep
  haveI : Algebra.FormallyEtale F F' := Algebra.FormallyEtale.of_isSeparable F F'
  let e := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K F F'
  obtain ⟨t, rfl⟩ := e.surjective η
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul u ω =>
    have he : e (u ⊗ₜ ω) = u • pullbackAlong φ' ω := by
      change KaehlerDifferential.mapBaseChange K F F' (u ⊗ₜ ω) = _
      rw [KaehlerDifferential.mapBaseChange_tmul]
      rfl
    rw [he, traceAlong_smul_pullbackAlong φ' hsep, pullbackAlong_smul, pullbackAlong_smul,
      pullbackAlong_square φ' φ (θ : F →ₐ[K] F₀) (θ' : F' →ₐ[K] F₀') hφ,
      traceAlong_smul_pullbackAlong φ hsep₀]
    congr 1
    exact trace_of_algEquiv φ' φ θ θ' hφ u
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, map_add, hx, hy]

end S_AlgebraicCurve_Differential_pullbackAlong_traceAlong_eq_traceAlong_pullbackAlong_of_algEquiv
end P2MW
export P2MW.S_AlgebraicCurve_Differential_pullbackAlong_traceAlong_eq_traceAlong_pullbackAlong_of_algEquiv (solution)
