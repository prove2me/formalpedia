-- Prove2me | Definitions.Def_QNatProofs_complexGaussian
-- name    : QNatProofs_complexGaussian
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:59:09.151146+00:00
-- url     : https://prove2.me/theorems/62088bf5-5ea4-488f-9376-300db55996b9
-- title:
--   The standard complex Gaussian and $(s,\xi,\eta)$-complex Gaussian samplers
-- statement:
--   The **standard complex Gaussian** $\mathcal N_{\mathbb C}(0,1)$ has independent real and imaginary parts with law $\mathcal N(0,1/2)$; so $\mathbb E|G|^2=1$ and $\Pr[|G|>r]=e^{-r^2}$.
--
--   A **sampler** $\mathrm{Samp}:\{0,1\}^R\to\{0,1\}^{2q}$ outputs the $q$-bit binary encodings of polar coordinates $(r,\theta)\in[0,1)^2$, identified with the complex number $re^{i2\pi\theta}$.
--
--   For $s>0$, $\xi\ge0$ and $\eta\in[0,1]$, $\mathrm{Samp}$ is an **$(s,\xi,\eta)$-complex Gaussian sampler** (Definition 3.1) if, for a uniformly random tape $\omega\in\{0,1\}^R$, the random variable $\mathrm{Samp}(\omega)$ can be coupled to $G\sim\mathcal N_{\mathbb C}(0,1)$ so that
--   $$
--   \Pr\big[|s\cdot\mathrm{Samp}(\omega)-G|>\xi\big]\le\eta.\tag{4}
--   $$
--
--   Samplers supply the approximately Gaussian amplitudes of the PRAL states.
--
--   **Formalization Note** A coupling is a probability measure on $\{0,1\}^R\times\mathbb C$ whose marginals are the uniform tape law and $\mathcal N_{\mathbb C}(0,1)$. A $q$-bit fraction is $\sum_j b_j2^{-(j+1)}$, most significant bit first; any finite binary-fraction encoding becomes one of this form by padding with zeros.
-- source:
--   Li, Parham, Natural proofs for quantum state preparation lower bounds, arXiv:2610.06826 (held copy sha256 b604fa11…), Definition 3.1, (4), p.11; p.13; (29), p.19

import Mathlib

set_option autoImplicit false

namespace QNatProofs

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- The **standard complex Gaussian** `N_ℂ(0, 1)`: real and imaginary parts independent `N(0, 1/2)`
(Li, Parham, arXiv:2610.06826 (held copy sha256 b604fa11…), p.13: "the complex gaussian variable
`g ∈ N_ℂ(0, 1)` has real and imaginary parts that are real Gaussian variables from `N(0, 1/2)`"),
so `E|G|² = 1` and `Pr[|G| > r] = e^{-r²}` ((29), p.19). -/
noncomputable def stdComplexGaussian : Measure ℂ :=
  ((gaussianReal 0 (1 / 2 : ℝ≥0)).prod (gaussianReal 0 (1 / 2 : ℝ≥0))).map
    fun p => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I

/-- The uniform distribution on the random tapes `{0,1}^R`. -/
noncomputable def uniformTape (R : ℕ) : Measure (Fin R → Bool) :=
  (PMF.uniformOfFintype (Fin R → Bool)).toMeasure

/-- The `q`-bit binary fraction `0.b₀b₁⋯b_{q−1} = Σ_j b_j 2^{-(j+1)} ∈ [0, 1)` (most significant bit
first). -/
noncomputable def binFrac {q : ℕ} (b : Fin q → Bool) : ℝ :=
  ∑ j : Fin q, if b j then (2 : ℝ)⁻¹ ^ (j.val + 1) else 0

/-- A deterministic **sampler** `Samp : {0,1}^R → {0,1}^{2q}`: the output is the pair of `q`-bit
binary encodings of polar coordinates `(r, θ) ∈ [0, 1)²` (Definition 3.1, p.11). -/
abbrev Sampler (R q : ℕ) : Type := (Fin R → Bool) → (Fin q → Bool) × (Fin q → Bool)

/-- The complex number `r e^{i2πθ}` encoded by a sampler output `(r, θ)` (Definition 3.1, p.11:
"we identify the samplers output with the corresponding complex number it encodes", p.11). -/
noncomputable def polarVal {q : ℕ} (o : (Fin q → Bool) × (Fin q → Bool)) : ℂ :=
  (binFrac o.1 : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (binFrac o.2 : ℂ))

/-- **`(s, ξ, η)`-complex Gaussian sampler** (Li, Parham, arXiv:2610.06826 (held copy sha256
b604fa11…), Definition 3.1, (4), p.11): `s > 0`, `ξ ≥ 0`, `η ∈ [0, 1]`, and for a uniformly
random tape `ω ∈ {0,1}^R` the random variable `V = Samp(ω)` can be coupled to `G ∼ N_ℂ(0, 1)` so
that `Pr[|s · Samp(ω) − G| > ξ] ≤ η`.

**Formalization Note** A coupling is a probability measure on `{0,1}^R × ℂ` whose marginals are
the uniform tape law and `N_ℂ(0,1)`. The output encodes `(r, θ)` as two `q`-bit binary fractions;
any finite binary-fraction encoding becomes one of this form after padding with zeros. -/
def IsComplexGaussianSampler {R q : ℕ} (s ξ η : ℝ) (Samp : Sampler R q) : Prop :=
  0 < s ∧ 0 ≤ ξ ∧ 0 ≤ η ∧ η ≤ 1 ∧
  ∃ π : Measure ((Fin R → Bool) × ℂ), IsProbabilityMeasure π ∧
    π.map Prod.fst = uniformTape R ∧ π.map Prod.snd = stdComplexGaussian ∧
    π {p | ξ < ‖(s : ℂ) * polarVal (Samp p.1) - p.2‖} ≤ ENNReal.ofReal η

end QNatProofs


