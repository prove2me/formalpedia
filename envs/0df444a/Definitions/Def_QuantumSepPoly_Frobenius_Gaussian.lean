-- Prove2me | Definitions.Def_QuantumSepPoly_Frobenius_Gaussian
-- name    : QuantumSepPoly_Frobenius_Gaussian
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:09:10.830608+00:00
-- url     : https://prove2.me/theorems/7a675426-5782-464f-ade9-1d980aac5901
-- title:
--   Standard complex Gaussian laws and nonnegative moments
-- statement:
--   Let $G_a,H_a$ be independent real $N(0,1)$ variables and put
--   $$X_a=(G_a+iH_a)/\sqrt2.$$
--   The underlying measure is their finite product. For a nonnegative scalar function $f$, the $L^q$ magnitude is $(\int f^q)^{1/q}$, represented using a nonnegative extended-real Lebesgue integral. Thus infinite moments remain infinite. These laws fix the variance normalization and avoid the default zero value of a nonintegrable Bochner integral.
-- source:
--   Giulio Malavolta, STOC 2027 submission #1577 (October 2026), §§2–5, p. 7 (PDF p. 7); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1577.pdf

import Definitions.Def_QuantumSepPoly_Frobenius_MatrixGeometry

noncomputable section

namespace QuantumSepPoly.Frobenius
open MeasureTheory ProbabilityTheory

/-- §2.2, p.7: two independent variance-one real coordinates per complex coordinate. -/
def realGaussian (d : ℕ) : Measure ((Fin d × Bool) → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 1)

def complexGaussian {d : ℕ} (g : (Fin d × Bool) → ℝ) : Vec d :=
  fun i => ((g (i,false) : ℂ) + Complex.I * g (i,true)) / (Real.sqrt 2 : ℂ)

/-- Nonnegative Lebesgue moments avoid Bochner's nonintegrable default. -/
def Lq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (q : ℝ) (f : Ω → ℝ) : ENNReal :=
  (∫⁻ x, ENNReal.ofReal (f x) ^ q ∂μ) ^ (1 / q)

end QuantumSepPoly.Frobenius


