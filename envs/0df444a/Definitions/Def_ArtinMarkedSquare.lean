-- Prove2me | Definitions.Def_ArtinMarkedSquare
-- name    : ArtinMarkedSquare
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T17:01:57.168989+00:00
-- url     : https://prove2.me/theorems/7b75f59d-bf97-4bfe-80bd-9e2a900ff156
-- title:
--   The expanded Cauchy square Q_Y of the marked Type II sum and its major form Q_Y^maj, with the major arcs and the smooth cutoffs, as in the proof of Lemma 10.2
-- statement:
--   Objects of the proof of Lemma 10.2 (OpenAI, *Primitive roots for every admissible integer base*, pp. 64–66), which re-runs §§3–5 of OpenAI's *The Poisson–Dirichlet law for prime predecessors*. Write $L = \log x$, $\mathcal P_i$ for the $i$th prime group (`primeGroup x (a i)`) and $V_i = \sum_{p \in \mathcal P_i} 1/p$.
--
--   - `dyadicBump` is the smooth cutoff $\eta(t) = \phi(t) - \phi(t/2)$ with $\phi(t) = $ `Real.smoothTransition (t − 1)`. It is nonnegative and supported in $[1, 4]$, and $\sum_{j \in \mathbb Z}\eta(t/2^j) = 1$ for $t > 0$.
--   - `arcCutoff` is $\psi(t) = $ `smoothTransition (5 − t) · smoothTransition (5 + t)`, equal to one on $[-4, 4]$ and supported in $[-5, 5]$.
--   - `labelTuples x a` is the set of tuples choosing one prime from each group; `squareNorm x a` is $\prod_i V_i^{-2}$.
--   - `majorArcs x A₀ Y` is the set $\mathfrak M$ of $\theta \in [0, 1)$ within $2L^{A_0}/Y$ of some $c/k$ with $(c, k) = 1$ and $1 \le k \le L^{A_0}$.
--   - `majorKernel x A₀ Y t a b` is $H_{\mathfrak M}(t; a, b) = \psi(t/Y)\int_{\mathfrak M} e(\theta(t - b + a))\,d\theta$, with $e(u) = \exp(2\pi iu)$.
--   - `expandedSquare x a Y Hm Hn α β` is $Q_Y = \prod_iV_i^{-2}\sum \eta(a/Y)\eta(b/Y)\,\alpha_m\overline{\alpha_r}\,\beta_n\overline{\beta_s}$ over label tuples with products $a, b$ and over $m, r \le 2H_m$, $n, s \le 2H_n$ with $mn - 1 = ah$ and $rs - 1 = bh$ for a common $h$.
--   - `majorSquare x a A₀ Y Hm Hn α β` is $Q_Y^{\mathrm{maj}}$, the same normalized sum over independent label tuples and all $m, n, r, s$, with the solution condition replaced by $H_{\mathfrak M}(bmn - ars; a, b)$.
--
--   **Formalization note.** The papers write $\alpha_m\alpha_{m'}\beta_n\beta_{n'}$ in the expanded square; since it is the square $\sum_h|G(h)|^2$ from Cauchy's inequality, the second pair carries complex conjugates. The papers' "fixed real smooth dyadic cutoff supported in $[1, 4]$" and "fixed $\psi \in C_c^\infty$, equal to one on $[-4, 4]$" are fixed here as the explicit functions above.
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 65: “$Q_Y = \bigl(\prod_iV_i^{-2}\bigr)\sum_{a,b,m,n,m',n':\ mn-1=ah,\ m'n'-1=bh\text{ for some }h}\rho(a/Y)\rho(b/Y)\alpha_m\alpha_{m'}\beta_n\beta_{n'}$. (10.7) Here $a, b$ each select one prime from every group, and $\rho$ is the fixed real smooth dyadic cutoff supported in $[1, 4]$.” and “$H_{\mathfrak M}(t; a, b) = \psi(t/Y)\int_{\mathfrak M}e(\theta(t - b + a))\,d\theta$.”
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 64–66, proof of Lemma 10.2 (expanded square Q_Y (10.7), major arcs, major form Q_Y^maj (10.8))

import Mathlib
import Definitions.Def_ArtinSieve

namespace ArtinPrimitiveRoots

open Real

/-- The smooth dyadic cutoff `η(t) = φ(t) − φ(t/2)` with `φ(t) = smoothTransition (t − 1)`: it is
smooth, nonnegative, supported in `[1, 4]`, and `∑_{j ∈ ℤ} η(t/2^j) = 1` for `t > 0`. -/
noncomputable def dyadicBump (t : ℝ) : ℝ :=
  Real.smoothTransition (t - 1) - Real.smoothTransition (t / 2 - 1)

/-- The smooth cutoff `ψ(t) = smoothTransition (5 − t) · smoothTransition (5 + t)`: equal to one on
`[−4, 4]` and supported in `[−5, 5]`. -/
noncomputable def arcCutoff (t : ℝ) : ℝ :=
  Real.smoothTransition (5 - t) * Real.smoothTransition (5 + t)

/-- The label tuples: one prime from each group `𝒫_i = primeGroup x (a i)`. -/
noncomputable def labelTuples (x : ℝ) {K : ℕ} (a : Fin K → ℝ) : Finset (Fin K → ℕ) :=
  Fintype.piFinset fun i => primeGroup x (a i)

/-- The normalization `∏_i V_i^{-2}` of the expanded square, `V_i = ∑_{p ∈ 𝒫_i} 1/p`. -/
noncomputable def squareNorm (x : ℝ) {K : ℕ} (a : Fin K → ℝ) : ℝ :=
  ∏ i, (groupReciprocalSum x (a i))⁻¹ ^ 2

/-- The major arcs `𝔐 ⊆ [0, 1)` (the circle `ℝ/ℤ`): the points within `2 L^{A₀}/Y` of a fraction
`c/k` in lowest terms with `1 ≤ k ≤ L^{A₀}`, `L = log x`. -/
def majorArcs (x A₀ Y : ℝ) : Set ℝ :=
  {θ | 0 ≤ θ ∧ θ < 1 ∧ ∃ k : ℕ, 1 ≤ k ∧ (k : ℝ) ≤ log x ^ A₀ ∧
    ∃ c : ℤ, Int.gcd c k = 1 ∧ |θ - c / k| ≤ 2 * log x ^ A₀ / Y}

/-- The major kernel `H_𝔐(t; a, b) = ψ(t/Y) ∫_𝔐 e(θ(t − b + a)) dθ`, `e(u) = exp(2πiu)`. -/
noncomputable def majorKernel (x A₀ Y : ℝ) (t a b : ℤ) : ℂ :=
  (arcCutoff (t / Y) : ℂ) *
    ∫ θ in majorArcs x A₀ Y, Complex.exp (2 * π * Complex.I * ((θ * (t - b + a) : ℝ) : ℂ))

open Classical in
/-- The expanded Cauchy square `Q_Y` of the marked bilinear sum: the normalized sum over label
tuples `p, p'` with products `a = ∏ p`, `b = ∏ p'`, and over `m, r ≤ 2H_m`, `n, s ≤ 2H_n`, of
`η(a/Y) η(b/Y) α_m conj(α_r) β_n conj(β_s)` over the solutions of `mn − 1 = ah`, `rs − 1 = bh`
for a common natural number `h`. -/
noncomputable def expandedSquare (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (Y Hm Hn : ℝ)
    (α β : ℕ → ℂ) : ℂ :=
  (squareNorm x a : ℂ) *
    ∑ p ∈ labelTuples x a, ∑ p' ∈ labelTuples x a,
      ∑ m ∈ Finset.range (⌊2 * Hm⌋₊ + 1), ∑ n ∈ Finset.range (⌊2 * Hn⌋₊ + 1),
      ∑ r ∈ Finset.range (⌊2 * Hm⌋₊ + 1), ∑ s ∈ Finset.range (⌊2 * Hn⌋₊ + 1),
        if ∃ h : ℕ, m * n - 1 = (∏ i, p i) * h ∧ r * s - 1 = (∏ i, p' i) * h then
          ((dyadicBump ((∏ i, p i : ℕ) / Y) * dyadicBump ((∏ i, p' i : ℕ) / Y) : ℝ) : ℂ) *
            α m * (starRingEnd ℂ) (α r) * β n * (starRingEnd ℂ) (β s)
        else 0

/-- The major form `Q_Y^maj` of the expanded square: the same normalized sum over independent label
tuples `p, p'` and all `m, n, r, s`, with the solution condition replaced by the major kernel
`H_𝔐(bmn − ars; a, b)`. -/
noncomputable def majorSquare (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (A₀ Y Hm Hn : ℝ)
    (α β : ℕ → ℂ) : ℂ :=
  (squareNorm x a : ℂ) *
    ∑ p ∈ labelTuples x a, ∑ p' ∈ labelTuples x a,
      ∑ m ∈ Finset.range (⌊2 * Hm⌋₊ + 1), ∑ n ∈ Finset.range (⌊2 * Hn⌋₊ + 1),
      ∑ r ∈ Finset.range (⌊2 * Hm⌋₊ + 1), ∑ s ∈ Finset.range (⌊2 * Hn⌋₊ + 1),
        ((dyadicBump ((∏ i, p i : ℕ) / Y) * dyadicBump ((∏ i, p' i : ℕ) / Y) : ℝ) : ℂ) *
          α m * (starRingEnd ℂ) (α r) * β n * (starRingEnd ℂ) (β s) *
          majorKernel x A₀ Y
            (((∏ i, p' i : ℕ) : ℤ) * (m : ℤ) * (n : ℤ) - ((∏ i, p i : ℕ) : ℤ) * (r : ℤ) * (s : ℤ))
            ((∏ i, p i : ℕ) : ℤ) ((∏ i, p' i : ℕ) : ℤ)

end ArtinPrimitiveRoots


