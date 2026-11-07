-- Prove2me | Definitions.Def_GeoSemialgCSP_noiseK
-- name    : GeoSemialgCSP_noiseK
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:46:57.798357+00:00
-- url     : https://prove2.me/theorems/b6658bfe-7bd1-4f4c-a69b-8524f75fef32
-- title:
--   Noise kernel on $W^R$
-- statement:
--   For a finite alphabet $W$ and $0\le\sigma\le1$, the noisy copy $\tilde z$ of $z\in W^R$ keeps each coordinate independently with probability $\sigma$ and otherwise resamples it uniformly from $W$. Its law is
--   $$\Pr(\tilde z=z')=\prod_{r=1}^R\Bigl(\sigma\,[z'_r=z_r]+\frac{1-\sigma}{|W|}\Bigr).$$
--
--   A resampled coordinate may coincide with the old one, which is why the uniform term is present for every value.
-- source:
--   Arvanitakis, Chatziafratis, Makarychev, Hardness of Approximation for Semialgebraic CSPs, manuscript (STOC 2027 submission, held version sha256 ee702c42…), §3, p.8 (PDF p.9); §4.3, p.12 (PDF p.13)

import Mathlib

namespace GeoSemialgCSP

open Classical in
/-- **Noise kernel.** Arvanitakis, Chatziafratis, Makarychev, *Hardness of Approximation for Semialgebraic CSPs*,
manuscript (STOC 2027 submission, held version sha256 ee702c42…), §3 "Product spaces, influences, and noise", printed p.8 (PDF
p.9), and §4.3, printed p.12 (PDF p.13): the noise operator `T_σ` keeps each coordinate with
probability `σ` and otherwise resamples it uniformly. `noiseK σ z z'` is the probability that the
noisy copy of `z ∈ W^R` is `z'`.

**Formalization Note.** A resampled coordinate may equal the old one, hence the per-coordinate
probability `σ·[z'ᵣ = zᵣ] + (1 − σ)/|W|`. Coordinates are `Fin R`. -/
noncomputable def noiseK {W : Type*} [Fintype W] {R : ℕ} (σ : ℝ) (z z' : Fin R → W) : ℝ :=
  ∏ r, (σ * (if z' r = z r then 1 else 0) + (1 - σ) / (Fintype.card W : ℝ))

end GeoSemialgCSP


