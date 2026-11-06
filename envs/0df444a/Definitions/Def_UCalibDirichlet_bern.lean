-- Prove2me | Definitions.Def_UCalibDirichlet_bern
-- name    : UCalibDirichlet_bern
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:24:10.275789+00:00
-- url     : https://prove2.me/theorems/16277285-7d29-4347-b9cb-38b84fac6ced
-- title:
--   Bernstein polynomial $B_nf$
-- statement:
--   The $n$-th Bernstein polynomial of $f:[0,1]\to\mathbb R$ is
--   $$B_nf(x)=\mathbb E_{S\sim\mathrm{Bin}(n,x)}[f(S/n)]=\sum_{k=0}^n\binom nk x^k(1-x)^{n-k}f(k/n).$$
--   Its uniform distance to $f$ (the Bernstein approximation gap) is the scalar complexity that controls the stability term (Lemma 1.7) and the chord gaps of Appendix B.
--
--   **Formalization Note** The binomial expectation is written as its finite sum, so $B_nf$ is a polynomial function on all of $\mathbb R$ and its derivatives are those of the polynomial.
-- source:
--   Frongillo, Luo, Mehta & Schneider, Near-Optimal Regret in U-Calibration for Every Proper Loss (manuscript, STOC 2027 submission), p.5 (definition before Lemma 1.7); Lemma A.1, p.23; Lemma B.1, p.28

import Mathlib

namespace UCalibDirichlet

/-- **The Bernstein polynomial `B_n f`.** Frongillo, Luo, Mehta & Schneider (manuscript, STOC 2027
submission), p.5: "Let `B_n f` be the `n`-th *Bernstein polynomial* for `f` …, defined as a mapping
on domain `[0, 1]` via `B_n f(p) = E_{S∼Bin(n,p)}[f(S/n)]`"; also Lemma A.1 (p.23) and Lemma B.1
(p.28).

`bern f n x = ∑_{k=0}^{n} C(n,k) x^k (1 − x)^{n−k} f(k/n)`.

**Formalization Note.** The binomial expectation is written out as its finite sum, so `bern f n`
is a polynomial function of `x` on all of `ℝ` (its derivatives are those of the polynomial). Only
the values `f(k/n) ∈ f([0,1])` enter. The paper uses `n ≥ 1`. -/
noncomputable def bern (f : ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * x ^ k * (1 - x) ^ (n - k) * f (k / n)

end UCalibDirichlet


