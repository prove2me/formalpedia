-- Prove2me | Definitions.Def_HamLocality237_Testing_SpectralMeasure
-- name    : HamLocality237_Testing_SpectralMeasure
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:33:36.967289+00:00
-- url     : https://prove2.me/theorems/7448a6d6-e468-4272-aaa6-78acffb8eb1b
-- title:
--   Scalar Riesz measure for a bounded self-adjoint operator
-- statement:
--   Let $A$ be a bounded self-adjoint operator on a complex Hilbert space $E$ and let $v\in E$. The real positive functional on continuous compactly supported functions on the real spectrum is
--
--   $$\Lambda_{A,v}(f)=\operatorname{Re}\langle v,f(A)v\rangle.$$
--
--   The file constructs its Riesz measure on the spectrum and pushes that measure forward by the continuous inclusion of the spectrum into the real line. Positivity and linearity of the functional are proved in Lean. No probability or representing-identity hypothesis is stored as a structure field.
--
--   The Adversary definition instantiates this constructor at the actual block operator and distinguished unit vector. The Definition 3.1 and Lemma 3.2 item states its probability, support, representation, uniqueness and moment guarantees as conclusions.The Adversary definition instantiates this constructor at the actual block operator and distinguished unit vector. The Definition 3.1 and Lemma 3.2 item states its probability, support, representation, uniqueness and moment guarantees as conclusions.
-- source:
--   Francisco Escudero Gutiérrez, Junseo Lee, Sebastian Zur, STOC 2027 submission #237 (October 2026), Definition 3.1, p.13 (Riesz construction infrastructure). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/237.pdf

import Mathlib

open MeasureTheory
open scoped ComplexOrder
noncomputable section

namespace HamLocality237.Testing

/-- The scalar positive functional used for Definition 3.1, p.13. -/
def spectralFunctional {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (A : E →L[ℂ] E) (hA : IsSelfAdjoint A) (v : E) :
    CompactlySupportedContinuousMap (spectrum ℝ A) ℝ →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀
    { toFun := fun f => (inner ℂ v ((cfcHom hA f.toContinuousMap) v)).re
      map_add' := by
        intro f g
        change (inner ℂ v ((cfcHom hA (f.toContinuousMap + g.toContinuousMap)) v)).re = _
        rw [map_add]
        simp
      map_smul' := by
        intro c f
        change (inner ℂ v ((cfcHom hA (c • f.toContinuousMap)) v)).re = _
        rw [map_smul]
        simp [inner_smul_right] }
    (by
      intro f hf
      have hp : 0 ≤ cfcHom hA f.toContinuousMap :=
        (cfcHom_nonneg_iff hA).mpr (fun x => hf x)
      exact (ContinuousLinearMap.nonneg_iff_isPositive _).mp hp |>.re_inner_nonneg_right v)

/-- An actual Riesz measure on the real spectrum, not a postulated representing measure. -/
def spectralMeasureOnSpectrum {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (A : E →L[ℂ] E) (hA : IsSelfAdjoint A) (v : E) :
    Measure (spectrum ℝ A) :=
  RealRMK.rieszMeasure (spectralFunctional A hA v)

/-- Push the spectral measure forward by the continuous inclusion into the real line. -/
def scalarSpectralMeasure {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (A : E →L[ℂ] E) (hA : IsSelfAdjoint A) (v : E) : Measure ℝ :=
  Measure.map (fun x : spectrum ℝ A => (x : ℝ)) (spectralMeasureOnSpectrum A hA v)

end HamLocality237.Testing


