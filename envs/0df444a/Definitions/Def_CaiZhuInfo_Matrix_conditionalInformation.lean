-- Prove2me | Definitions.Def_CaiZhuInfo_Matrix_conditionalInformation
-- name    : CaiZhuInfo_Matrix_conditionalInformation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:15:26.343954+00:00
-- url     : https://prove2.me/theorems/fe750b4e-bf49-4db3-8430-b54aa83367ff
-- title:
--   Finite entropy, conditional laws and information in bits
-- statement:
--   A finite law is Mathlib's probability mass function, whose nonnegative masses sum to one. The finite Shannon entropy is the published entropy in bits, with $0\log_2 0=0$, and divergence to uniform is
--   $$D(P\|U_A)=\log_2|A|-H(P).$$
--   For a finite-valued random variable $X$ and a sub-σ-algebra $\mathcal G$, the conditional masses are the conditional expectations $P(X=a\mid\mathcal G)$. Conditional entropy and conditional information are
--   $$H(X\mid\mathcal G)=\mathbb E H(P_{X\mid\mathcal G}),\qquad I(X;T\mid Y)=H(X\mid Y)-H(X\mid Y,T).$$
--   The constants are $C_0=16+8\sqrt2$ and $c_0=\log_2C_0$. These objects supply actual information quantities even when the public tape has infinite entropy. Every use has a probability measure, measurable variables and a conditioning σ-algebra contained in the ambient one; finite-variable entropy is bounded and integrable. No general infinite KL divergence is converted to a real number.
-- source:
--   Xiaohong Cai, Mingyang Zhu, STOC 2027 submission #616 (October 2026), §§1,3, (1), (12), printed pp.1,10 / PDF pp.2,11; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/616.pdf

import Mathlib
import Definitions.Def_FuchsVdGraaf_entropy

open MeasureTheory
open scoped ENNReal

namespace CaiZhuInfo.Matrix

/-! Cai–Zhu, STOC 2027 submission #616, §3, printed p.10 / PDF p.11.
Finite laws use Mathlib PMF. All information is in bits. Only divergence to a
strictly positive uniform law is represented here; no general infinite KL is truncated. -/
noncomputable section

abbrev logTwo (x : ℝ) : ℝ := Real.logb 2 x

def C₀ : ℝ := 16 + 8 * Real.sqrt 2

def c₀ : ℝ := logTwo C₀

def mass {A : Type} (p : PMF A) (a : A) : ℝ := (p a).toReal

def mean {A : Type} [Fintype A] (p : PMF A) (f : A → ℝ) : ℝ :=
  ∑ a, mass p a * f a

def finiteEntropy {A : Type} [Fintype A] (p : PMF A) : ℝ :=
  FuchsVdGraaf.entropy (mass p)

def uniformDivergence {A : Type} [Fintype A] (p : PMF A) : ℝ :=
  logTwo (Fintype.card A) - finiteEntropy p

/-- Conditional mass on the original sample space, defined up to null sets.
The conditioning σ-algebra must be contained in the ambient one in every use. -/
def conditionalMass {Ω A : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → A) (s : MeasurableSpace Ω) (a : A) : Ω → ℝ :=
  μ[Set.indicator {ω | X ω = a} (fun _ => (1 : ℝ)) | s]

/-- Expectation of the entropy of the actual conditional law of a finite variable.
This never subtracts two possibly infinite entropies of a public tape. -/
def entropyGiven {Ω A : Type} {mΩ : MeasurableSpace Ω} [Fintype A]
    (μ : Measure Ω) (X : Ω → A) (s : MeasurableSpace Ω) : ℝ :=
  ∫ ω, FuchsVdGraaf.entropy (fun a => @conditionalMass Ω A mΩ μ X s a ω) ∂μ

abbrev observedSigma {Ω T : Type} [MeasurableSpace T] (Tvar : Ω → T) : MeasurableSpace Ω :=
  MeasurableSpace.comap Tvar inferInstance

def conditionalInformation {Ω A T B : Type} [MeasurableSpace Ω] [Fintype A]
    [MeasurableSpace T] [MeasurableSpace B]
    (μ : Measure Ω) (X : Ω → A) (Tvar : Ω → T) (Y : Ω → B) : ℝ :=
  entropyGiven μ X (observedSigma Y) -
    entropyGiven μ X (observedSigma (fun ω => (Y ω, Tvar ω)))

end
end CaiZhuInfo.Matrix


