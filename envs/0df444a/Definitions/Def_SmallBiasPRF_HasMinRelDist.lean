-- Prove2me | Definitions.Def_SmallBiasPRF_HasMinRelDist
-- name    : SmallBiasPRF_HasMinRelDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:09:38.018206+00:00
-- url     : https://prove2.me/theorems/5621cdaf-92f8-469f-af78-fa5093dd2334
-- title:
--   Linear code of minimum relative distance at least $\delta$
-- statement:
--   A binary linear code $H:\mathbb F_2^n\to\mathbb F_2^{m}$ has **minimum relative distance at least $\delta$** if
--
--   $$\mathrm{wt}(H(v))\ \ge\ \delta\, m\qquad\text{for every nonzero } v\in\mathbb F_2^n,$$
--
--   where $\mathrm{wt}$ is the Hamming weight. For a linear code this is the usual relative minimum distance between distinct codewords. The theorems of the mission use $\delta=7/16$ for the code $H:\mathbb F_2^n\to\mathbb F_2^{m_1}$ that encodes the input.
--
--   **Formalization Note** The weight is Mathlib's `hammingNorm`, compared in $\mathbb R$.
-- source:
--   Dinur–Ishai, Towards Asymptotically Optimal Pseudorandom Functions: Linear-Size Circuits with Exponentially Small Bias, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), Theorem 7, p.16 (PDF 19); Theorems 4, 6, 8, pp.14–16

import Mathlib

namespace SmallBiasPRF

/-- A binary linear code `H : 𝔽₂ⁿ → 𝔽₂^{m}` has **minimum relative distance at least `δ`**
(Theorems 4, 6, 7, 8, pp.14–16 (PDF pp.17–19)): every nonzero message has a codeword of Hamming
weight at least `δ·m`.
Dinur–Ishai, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), Theorem 7, p.16
(PDF p.19).

**Formalization Note.** For a linear code the minimum distance between distinct codewords is the
minimum weight `wt(H(v))` over `v ≠ 0`, which is what is bounded; the weight is Mathlib's
`hammingNorm` (number of nonzero coordinates). With `δ > 0` and `m ≥ 1` the predicate forces `H`
to be injective. -/
def HasMinRelDist {n m : ℕ} (H : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2)) (δ : ℝ) : Prop :=
  ∀ v : Fin n → ZMod 2, v ≠ 0 → δ * (m : ℝ) ≤ (hammingNorm (H v) : ℝ)

end SmallBiasPRF


