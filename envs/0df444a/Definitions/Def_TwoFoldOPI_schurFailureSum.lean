-- Prove2me | Definitions.Def_TwoFoldOPI_schurFailureSum
-- name    : TwoFoldOPI_schurFailureSum
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:44:41.323197+00:00
-- url     : https://prove2.me/theorems/46a8ebb6-ac08-4d00-bb57-6b1b98d6d069
-- title:
--   The ambiguity sum $E=\sum_{c\in C^\perp\setminus0}q^{\dim((C^\perp)^{*2}[Z(c)])}/(q-1)^{\mathrm{wt}(c)}$
-- statement:
--   For a linear code $D\subseteq\mathbb F_q^M$ (in the mission $D=C^\perp$), the sum
--   $$E(D)=\sum_{c\in D\setminus\{0\}}\frac{q^{\dim\left((D^{*2})[Z(c)]\right)}}{(q-1)^{\operatorname{wt}(c)}},$$
--   where $D^{*2}$ is the Schur square, $Z(c)$ the zero set of $c$, $W[S]$ the shortened code and $\operatorname{wt}$ the Hamming weight. It bounds the probability that the linear relaxation of Lemma 7.3 has more than one solution, and $2|C^\perp|\,E$ is the failure bound of Theorem 7.4.
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §7.2, Lemma 7.3, p. 39; proof of Theorem 7.4, p. 40

import Mathlib
import Definitions.Def_TwoFoldOPI_zeroSet
import Definitions.Def_TwoFoldOPI_shorten
import Definitions.Def_TwoFoldOPI_schurSquare

namespace TwoFoldOPI

/-- **The ambiguity sum `E` of the Schur-square relaxation.**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §7, Lemma 7.3, p.39, and proof of Theorem 7.4, p.40: for a linear code `D = C^⊥ ⊆ F_q^m`,
`E = Σ_{c ∈ D∖{0}} q^{dim((D^{∗2})[Z(c)])} / (q − 1)^{wt(c)}`,
where `D^{∗2}` is the Schur square, `Z(c)` the zero set of `c`, `W[S]` the shortened code and
`wt` the Hamming weight.

**Formalization Note.** `q = |K|`; `dim` is `Module.finrank K`. The sum is finite. -/
noncomputable def schurFailureSum {K : Type*} [Field K] [Fintype K] [DecidableEq K] {M : ℕ}
    (D : Submodule K (Fin M → K)) : ℝ :=
  open scoped Classical in
  ∑ c ∈ Finset.univ.filter (fun c : Fin M → K => c ∈ D ∧ c ≠ 0),
    (Fintype.card K : ℝ) ^ Module.finrank K (shorten (schurSquare D) (zeroSet c)) /
      ((Fintype.card K : ℝ) - 1) ^ hammingNorm c

end TwoFoldOPI


