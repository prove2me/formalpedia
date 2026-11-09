-- Prove2me | Definitions.Def_SpatialHalfspace_FullLabels_Information
-- name    : SpatialHalfspace_FullLabels_Information
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:14:19.13712+00:00
-- url     : https://prove2.me/theorems/164b50c2-1a7a-4621-916c-45235aa5d699
-- title:
--   Binary entropy $h_2$ and conditional mutual information $I(\Psi;T\mid S)$ in bits
-- statement:
--   Let $h_2(t)=-t\log_2t-(1-t)\log_2(1-t)$ be binary entropy in bits, with $0\log_2 0=0$. Thus $h_2(0)=h_2(1)=0$ and $h_2(1/2)=1$.
--
--   For measurable random variables $\Psi,T,S$ on a probability space, define conditional mutual information in bits by
--
--   $$I(\Psi;T\mid S)=\sup_{n,f}\frac{D\!\left(P_{(S,\Psi),f(T)}\,\middle\|\,P_{S,\Psi}\otimes P_{f(T)\mid S}\right)}{\ln 2}\in[0,\infty],$$
--
--   where $f$ ranges over every measurable map from the observation space to $\{0,\ldots,n\}$. Each finite observation $f(T)$ has a regular conditional law given $S$, with no standard Borel assumption on the original observation space. For standard Borel observations this is the usual conditional KL formula; for discrete variables it is Shannon conditional mutual information. These are the quantities in §2.3 and Lemmas 2.6 and 4.1.
--
--   **Formalization Note** Binary entropy uses `Real.binEntropy / Real.log 2`. Conditional information is an extended nonnegative supremum of finite-observation KL divergences, implemented with `klDiv` and `condDistrib`. Only the finite target `Fin (n+1)` needs a regular conditional distribution. All three original random-variable spaces are arbitrary measurable spaces. Measurability is required in the theorems using the definition; infinite information has value $+\infty$.
-- source:
--   Yang, Spatial Communication Complexity of Agnostic Halfspace Learning, STOC 2027 submission #119 (2026), preprint, SHA-256 e5822ae144143c29214b0dab09b1a1863f55740d17b6f50ed091ddf8ffcaa692, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/119.pdf, printed p. 6, PDF p. 7, §2.3 (H, I in bits, binary entropy h₂), PDF p. 7; Lemma 2.6 and Lemma 4.1

import Mathlib

/-!
# Information measures in bits (Yang, STOC 2027 submission #119, §2.3, printed p. 6)

* `h2 t` — the binary entropy `h₂(t) = −t log₂ t − (1−t) log₂(1−t)`, with `0 log₂ 0 = 0`.
* `condMutualInfoBits Ψ T S μ` — conditional mutual information `I(Ψ; T | S)` in bits,
  defined by the supremum over finite measurable quantizations of `T`. For each quantization
  `f`, use the Kullback–Leibler divergence of the joint law of `(S, Ψ, f(T))` from
  `P_{SΨ} ⊗ P_{f(T)|S}`, divided by `ln 2`. Only the finite quantization needs a regular
  conditional law. Thus the observation and conditioning spaces are arbitrary measurable
  spaces, as in Lemma 4.1. For standard Borel observations this is the usual conditional KL
  formula, and for discrete variables it is Shannon's conditional information.
-/

namespace SpatialHalfspace.FullLabels

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Binary entropy in bits: `h₂(t) = −t log₂ t − (1 − t) log₂(1 − t)` (`h₂(0) = h₂(1) = 0`). -/
noncomputable def h2 (t : ℝ) : ℝ := Real.binEntropy t / Real.log 2

/-- Conditional mutual information in bits on arbitrary measurable spaces: the supremum of
`D(P_{(S,Ψ),f(T)} ‖ P_{S,Ψ} ⊗ P_{f(T)|S}) / ln 2` over all finite measurable quantizations `f`.
The finite alphabets `Fin (n+1)` suffice, including constant quantizations. -/
noncomputable def condMutualInfoBits {Ω α β γ : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSpace γ]
    (Ψ : Ω → α) (T : Ω → β) (S : Ω → γ) (μ : Measure Ω) [IsFiniteMeasure μ] : ℝ≥0∞ :=
  ⨆ (n : ℕ) (f : β → Fin (n + 1)) (_ : Measurable f),
    InformationTheory.klDiv (μ.map fun ω => ((S ω, Ψ ω), f (T ω)))
        ((μ.map fun ω => (S ω, Ψ ω)) ⊗ₘ
          ((condDistrib (fun ω => f (T ω)) S μ).comap Prod.fst measurable_fst))
      / ENNReal.ofReal (Real.log 2)

end SpatialHalfspace.FullLabels


