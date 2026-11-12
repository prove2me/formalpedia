-- Prove2me | Definitions.Def_MultStretchAPASP_Weighted_Sampling
-- name    : MultStretchAPASP_Weighted_Sampling
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T07:08:40.49434+00:00
-- url     : https://prove2.me/theorems/ef15b2a8-c0a4-407b-90cd-c4ab18cabb54
-- title:
--   Bernoulli sampling of a vertex set: n independent indicators with probability q
-- statement:
--   Algorithm 3 and §2.2 obtain a random set $S\subseteq V$ by keeping every vertex independently with probability $q\in(0,1)$. An outcome is an indicator vector $x\in\{\mathrm{true},\mathrm{false}\}^n$ and the sampled set is $S(x)=\{v : x_v=\mathrm{true}\}$. Its law is the product measure
--   $$\mathbb P_q=\bigotimes_{v=0}^{n-1}\bigl(q\,\delta_{\mathrm{true}}+(1-q)\,\delta_{\mathrm{false}}\bigr).$$
--   The probability of an event about $S$ is the measure of the corresponding set of indicator vectors.
--
--   **Formalization Note.** `sampleLaw n q` is `Measure.pi` of the two-point laws, `sampled x` the set $S(x)$. The space is finite, so every set is measurable.
-- source:
--   Saggi, Sapir, Smallest Multiplicative Stretch for an α-APASP Below Õ(n^ω) Runtime, arXiv:2611.04736 (version of November 3, 2026, sha256 7cbb8123…), p. 5, §2.2, and p. 13, Algorithm 3

import Mathlib

set_option autoImplicit false

open MeasureTheory

namespace MultStretchAPASP.Weighted

/-!
# Bernoulli sampling of a vertex set (Algorithm 3)

Saggi, Sapir, *Smallest Multiplicative Stretch for an α-APASP Below Õ(n^ω) Runtime*,
arXiv:2611.04736 (version of November 3, 2026, sha256 7cbb8123…), §2.2 (p. 5) and Algorithm 3
(p. 13): "let S ⊆ V be obtained by sampling each vertex independently with probability q".

* An outcome of the sampling is an indicator vector `x : Fin n → Bool`; `sampled x` is the set of
  the vertices `v` with `x v = true`.
* `sampleLaw n q` is the product over the `n` vertices of the law putting mass `q` on `true` and
  `1 − q` on `false` (independent Bernoulli(q) indicators), for `q ∈ (0, 1)`.
* A probability bound is the measure of the event, a set of indicator vectors (every set is
  measurable here: the space is finite with the discrete σ-algebra).
-/

/-- The law of `n` independent Bernoulli(`q`) indicators. -/
noncomputable def sampleLaw (n : ℕ) (q : ℝ) : Measure (Fin n → Bool) :=
  Measure.pi fun _ : Fin n =>
    ENNReal.ofReal q • Measure.dirac true + ENNReal.ofReal (1 - q) • Measure.dirac false

/-- The sampled set `S = {v | x v = true}` of an outcome `x`. -/
def sampled {n : ℕ} (x : Fin n → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun v => x v = true

end MultStretchAPASP.Weighted


