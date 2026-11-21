-- Prove2me | Definitions.Def_MasulloRH_RationalThetaSpace
-- name    : MasulloRH_RationalThetaSpace
-- status  : Definition
-- author  : @marozols
-- created : 2026-11-21T01:18:00.771499+00:00
-- url     : https://prove2.me/theorems/3f5ecfe4-c16f-43b6-8bc2-cab4d2e2962e
-- title:
--   The rational real-place theta annihilator and its convolution operator
-- statement:
--   For $w_p(x)=(1+x^2)^{-p/2}$, define the Hilbert subspace $E_p$ of $L^2(\mathbb R)$ as the orthogonal complement of all conjugated profiles $\overline{w_p^{-1}T_g}$, where $T_g(x)=e^{x/2}\sum_{n\in\mathbb Z}g(ne^x)$ and $g$ ranges over the complex Schwartz functions with $g(0)=\int g=0$. The conjugation gives the bilinear distributional pairing $\int w_p^{-1}T_g u$ the source uses. The convolution predicate specifies the operator on $E_p$ by its matrix coefficients against every ambient $L^2$ vector: it integrates $u(x)\mapsto w_p(x)u(x+y)/w_p(x+y)$ against $\varphi(e^y)\,dy$.
-- source:
--   A. Connes, Trace formula in noncommutative geometry and the zeros of the Riemann zeta function, Appendix I, equations (15)–(30), https://arxiv.org/abs/math/9811068. Rational real-place model for the fixed-line dual and weighted translations of A. M. Masullo, The Music of the Primes, §10.2.1.1 (10.2.1.7)–(10.2.1.9), and §10.3.1.

import Mathlib

open MeasureTheory Filter
open scoped InnerProductSpace SchwartzMap

namespace MasulloRH

/-- The rational real-place theta annihilator in the weighted logarithmic model,
realized as the orthogonal complement of the conjugated theta profiles in complex L². -/
noncomputable def rationalThetaAnnihilator (p : ℝ) :
    Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ)) :=
  (Submodule.span ℂ {v : Lp ℂ 2 (volume : Measure ℝ) |
    ∃ g : 𝓢(ℝ,ℂ), g 0 = 0 ∧ (∫ t : ℝ, g t) = 0 ∧
      (v : ℝ → ℂ) =ᵐ[volume] fun x : ℝ =>
        (starRingEnd ℂ) (((↑((1+x^2)^(p/2) : ℝ)) : ℂ) *
          ((Real.exp (x/2) : ℂ) * ∑' n : ℤ, g ((n:ℝ) * Real.exp x)))} )ᗮ

noncomputable instance rationalThetaAnnihilator_completeSpace (p : ℝ) :
    CompleteSpace (rationalThetaAnnihilator p) := by
  unfold rationalThetaAnnihilator
  infer_instance

/-- Weak weighted-translation convolution on the rational real-place theta annihilator. -/
def IsRationalThetaConvolution (p : ℝ) (φ : ℝ → ℂ)
    (T : rationalThetaAnnihilator p →L[ℂ] rationalThetaAnnihilator p) : Prop :=
  ∀ (u : rationalThetaAnnihilator p) (g : Lp ℂ 2 (volume : Measure ℝ)),
    ⟪g, (T u : Lp ℂ 2 (volume : Measure ℝ))⟫_ℂ =
      ∫ y : ℝ, φ (Real.exp y) * ∫ x : ℝ, (starRingEnd ℂ) (g x) *
        ((((1+x^2)^(-p/2) / (1+(x+y)^2)^(-p/2) : ℝ) : ℂ) *
          (u : Lp ℂ 2 (volume : Measure ℝ)) (x+y))

end MasulloRH


