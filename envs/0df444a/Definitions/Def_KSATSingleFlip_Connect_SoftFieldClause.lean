-- Prove2me | Definitions.Def_KSATSingleFlip_Connect_SoftFieldClause
-- name    : KSATSingleFlip_Connect_SoftFieldClause
-- status  : Definition
-- author  : @wcysai
-- created : 2026-11-13T10:29:11.980192+00:00
-- url     : https://prove2.me/theorems/d2da1219-1a56-4110-ac28-3f23fc2779bf
-- title:
--   Binary test perspective and single-clause gain
-- statement:
--   For a test ψ, the binary perspective is Ψ(v₀,v₁)=(v₀+v₁)ψ(v₁/(v₀+v₁)), with value zero at (0,0). The single-clause gain is one half the sum of the perspectives after multiplying either coordinate by 1−s, minus (1−s)Ψ(v₀,v₁). These are the functions used to compare Poisson soft-field updates.
-- source:
--   Wang–Yin–Yu–Zhang, Single-Variable Connectivity in Random k-SAT, proof of Lemma 4.5, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_SoftFieldOrder
import Mathlib
set_option autoImplicit false
noncomputable section
namespace KSATSingleFlip.Connect

/-- The binary one-homogeneous perspective of a concave test. At (0,0) its value is 0. -/
def softPerspective (ψ : ℝ → ℝ) (v0 v1 : ℝ) : ℝ :=
  (v0+v1)*ψ (v1/(v0+v1))

/-- The signed one-clause perturbation in the Poisson comparison proof. -/
def softClauseGain (ψ : ℝ → ℝ) (v0 v1 s : ℝ) : ℝ :=
  (softPerspective ψ ((1-s)*v0) v1 + softPerspective ψ v0 ((1-s)*v1))/2 -
    (1-s)*softPerspective ψ v0 v1

end KSATSingleFlip.Connect


