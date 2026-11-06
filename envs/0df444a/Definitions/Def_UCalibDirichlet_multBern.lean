-- Prove2me | Definitions.Def_UCalibDirichlet_multBern
-- name    : UCalibDirichlet_multBern
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:24:12.630323+00:00
-- url     : https://prove2.me/theorems/0c4f3268-7c80-4417-8dc3-085eee9c08c2
-- title:
--   Multivariate Bernstein polynomial $B_nF(q)=\mathbb E_{M\sim\mathrm{Mult}(n,q)}[F(M/n)]$
-- statement:
--   For $F:\Delta_K\to\mathbb R$, $n\ge1$ and $q\in\Delta_K$,
--   $$B_nF(q)=\mathbb E_{M\sim\mathrm{Mult}(n,q)}\big[F(M/n)\big]=\sum_{\substack{M\in\mathbb N^K\\ M_1+\dots+M_K=n}}\frac{n!}{M_1!\cdots M_K!}\prod_{j=1}^K q_j^{M_j}\,F(M/n),$$
--   the expectation of $F$ at the empirical distribution of $n$ i.i.d. labels drawn from $q$.
--
--   **Formalization Note** The multinomial expectation is its finite sum over count vectors with total $n$, with $0^0=1$.
-- source:
--   Frongillo, Luo, Mehta & Schneider, Near-Optimal Regret in U-Calibration for Every Proper Loss (manuscript, STOC 2027 submission), Theorem 1.8, display (14), p.6; proof of Lemma 2.2, p.25

import Mathlib

namespace UCalibDirichlet

/-- **The multivariate Bernstein polynomial `B_n F(q) = E_{M∼Mult(n,q)}[F(M/n)]`.** Frongillo, Luo,
Mehta & Schneider (manuscript, STOC 2027 submission), Theorem 1.8, p.6 ("with Mult being the
multinomial distribution"), and the proof of Lemma 2.2, p.25: "`B_n F` … defined as a mapping on
domain `Δ_K` as `B_n F(q) = E_{M∼Mult(n,q)} F(M/n)`."

`multBern F n q = ∑_{M ∈ ℕ^K, ∑ M = n} (n! / ∏_j M_j!) ∏_j q_j^{M_j} · F(M/n)`.

**Formalization Note.** The multinomial expectation is its finite sum over
`Finset.Nat.antidiagonalTuple K n` (the count vectors with total `n`), with `Nat.multinomial`
the multinomial coefficient and `0^0 = 1`. For `q ∈ Δ_K` and `n ≥ 1`, `M/n ∈ Δ_K`. -/
noncomputable def multBern {K : ℕ} (F : (Fin K → ℝ) → ℝ) (n : ℕ) (q : Fin K → ℝ) : ℝ :=
  ∑ M ∈ Finset.Nat.antidiagonalTuple K n,
    (Nat.multinomial Finset.univ M : ℝ) * (∏ j, q j ^ M j) * F (fun j => (M j : ℝ) / n)

end UCalibDirichlet


