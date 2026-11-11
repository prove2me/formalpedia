-- Prove2me | Definitions.Def_DesignTest_dilutedLaw
-- name    : DesignTest_dilutedLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T04:08:21.890544+00:00
-- url     : https://prove2.me/theorems/9f975da8-581f-4cfd-a172-cc6110896c14
-- title:
--   The diluted-subset law $p_S=(1-\lambda)\,\mathrm{Unif}([L])+\lambda\,\mathrm{Unif}(S)$
-- statement:
--   Let $L,M$ be integers with $1\le M\le L$, $\lambda\in(0,1]$, and $S\subseteq[L]$ a subset of size $M$. The **diluted-subset law** on $[L]$ is
--   $$p_S=(1-\lambda)\,\mathrm{Unif}([L])+\lambda\,\mathrm{Unif}(S),\qquad p_S(j)=\frac{1-\lambda}{L}+\frac{\lambda}{M}\mathbf 1\{j\in S\}.$$
--
--   It is the law of the list index of a sample under the hard NO inputs of Theorem 4.16.
--
--   **Formalization Note** $[L]$ is `Fin L` (from $0$); $M$ is passed explicitly and equals $|S|$ in every use.
-- source:
--   Kawachi–Nakata–Takeuchi, Testing State and Unitary Designs, STOC 2027 submission (sha256 e2f0a429…), Lemma 4.15, p.41; p.43 (formula for p_S(j))

import Mathlib

set_option autoImplicit false

namespace DesignTest

/-- **The diluted-subset law** `p_S := (1 − λ) Unif([L]) + λ Unif(S)` on `[L]`, i.e.
`p_S(j) = (1 − λ)/L + (λ/M)·1{j ∈ S}` for a subset `S` of size `M` (STOC 2027 submission
(sha256 e2f0a429…), Lemma 4.15, p.41; the formula for `p_S(j)` is on p.43).

**Formalization Note.** `[L]` is `Fin L` (from `0`); `M` is passed explicitly and is the size of `S` in
every use. -/
noncomputable def dilutedLaw (L M : ℕ) (lam : ℝ) (S : Finset (Fin L)) (j : Fin L) : ℝ :=
  (1 - lam) / L + (if j ∈ S then lam / M else 0)

end DesignTest


