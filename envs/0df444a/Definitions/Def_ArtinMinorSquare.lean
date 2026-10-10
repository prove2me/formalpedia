-- Prove2me | Definitions.Def_ArtinMinorSquare
-- name    : ArtinMinorSquare
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T18:00:23.742461+00:00
-- url     : https://prove2.me/theorems/4294057f-7d15-4558-bedb-9f7eb1c2b7a6
-- title:
--   The coprime minor-arc part Q_Y^min of the expanded square, as in the proof of Lemma 10.2 ([21] (3.10)–(3.11))
-- statement:
--   Objects for the minor-arc part of the expanded square of Lemma 10.2's proof (OpenAI, *Primitive roots for every admissible integer base*, pp. 64–66, re-running §§3–4 of OpenAI's *The Poisson–Dirichlet law for prime predecessors*). They use the bundle `Def_ArtinMarkedSquare`.
--
--   - `minorKernel x A₀ Y t a b` is $\psi(t/Y)\int_{[0,1)\setminus\mathfrak M} e(\theta(t - b + a))\,d\theta$, the kernel of $H_{\mathfrak M}$ with the major arcs $\mathfrak M = $ `majorArcs x A₀ Y` replaced by their complement in $[0, 1)$.
--   - `sqWeight Y a b m n r s α β` is $\eta(a/Y)\eta(b/Y)\,\alpha_m\overline{\alpha_r}\,\beta_n\overline{\beta_s}$, and `sqDet a b m n r s` is $t = bmn - ars \in \mathbb Z$.
--   - `minInner x A₀ Y Hm Hn α β a b` is the sum over $m, r \le 2H_m$ and $n, s \le 2H_n$ of the weight times the minor kernel at $t = bmn - ars$.
--   - `minorSquare x a A₀ Y Hm Hn α β` is $Q_Y^{\min} = \prod_iV_i^{-2}$ times the sum of `minInner` over label tuples whose products $a, b$ are coprime.
--
--   For coprime $a, b$ and $mn, rs \ge 1$, the solvability of $mn - 1 = ah$, $rs - 1 = bh$ is equivalent to $t = b - a$ ([21] (3.10)), and $\mathbf 1_{t = b - a} = \int_0^1 e(\theta(t - b + a))\,d\theta$. So $Q_Y - Q_Y^{\mathrm{maj}}$ is $Q_Y^{\min}$ plus the parts over label pairs that share a prime.
--
--   OpenAI, *The Poisson–Dirichlet law for prime predecessors* (2026), p. 11: “For the remaining pairs $(a, b) = 1$. Their two equations in (3.8) are equivalent to $t = bmn - ars = b - a$. (3.10)” and “The replacement for (3.10) is $H_{\mathfrak M}(t; a, b) = \psi(t/Y)\int_{\mathfrak M}e(\theta(t - b + a))\,d\theta$. (3.11)”
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 65, proof of Lemma 10.2 (the coprime minor-arc part of the expanded square, [21] (3.10)–(3.11))

import Mathlib
import Definitions.Def_ArtinMarkedSquare

namespace ArtinPrimitiveRoots

open Real

/-- The minor kernel `ψ(t/Y) ∫_{[0,1) ∖ 𝔐} e(θ(t − b + a)) dθ`, `𝔐 = majorArcs x A₀ Y`. -/
noncomputable def minorKernel (x A₀ Y : ℝ) (t a b : ℤ) : ℂ :=
  (arcCutoff (t / Y) : ℂ) *
    ∫ θ in Set.Ico (0 : ℝ) 1 \ majorArcs x A₀ Y,
      Complex.exp (2 * π * Complex.I * ((θ * (t - b + a) : ℝ) : ℂ))

/-- The weight `η(a/Y) η(b/Y) α_m conj(α_r) β_n conj(β_s)` of the expanded square. -/
noncomputable def sqWeight (Y : ℝ) (a b m n r s : ℕ) (α β : ℕ → ℂ) : ℂ :=
  ((dyadicBump ((a : ℕ) / Y) * dyadicBump ((b : ℕ) / Y) : ℝ) : ℂ) *
    α m * (starRingEnd ℂ) (α r) * β n * (starRingEnd ℂ) (β s)

/-- The determinant `t = bmn − ars`. -/
def sqDet (a b m n r s : ℕ) : ℤ := (b : ℤ) * (m : ℤ) * (n : ℤ) - (a : ℤ) * (r : ℤ) * (s : ℤ)

/-- The inner minor-arc sum for fixed label products `a, b`: over `m, r ≤ 2H_m`, `n, s ≤ 2H_n`, of
the weight times the minor kernel at `t = bmn − ars`. -/
noncomputable def minInner (x A₀ Y Hm Hn : ℝ) (α β : ℕ → ℂ) (a b : ℕ) : ℂ :=
  ∑ m ∈ Finset.range (⌊2 * Hm⌋₊ + 1), ∑ n ∈ Finset.range (⌊2 * Hn⌋₊ + 1),
  ∑ r ∈ Finset.range (⌊2 * Hm⌋₊ + 1), ∑ s ∈ Finset.range (⌊2 * Hn⌋₊ + 1),
    sqWeight Y a b m n r s α β * minorKernel x A₀ Y (sqDet a b m n r s) a b

/-- The coprime minor-arc square `Q_Y^min`: the normalized sum, over label tuples `p, p'` whose
products `a, b` are coprime, of the inner minor-arc sum. -/
noncomputable def minorSquare (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (A₀ Y Hm Hn : ℝ)
    (α β : ℕ → ℂ) : ℂ :=
  (squareNorm x a : ℂ) * ∑ p ∈ labelTuples x a, ∑ p' ∈ labelTuples x a,
    if Nat.Coprime (∏ i, p i) (∏ i, p' i) then minInner x A₀ Y Hm Hn α β (∏ i, p i) (∏ i, p' i)
    else 0

end ArtinPrimitiveRoots


