-- Prove2me | Definitions.Def_FuchsThesis_Chernoff_productDist
-- name    : FuchsThesis_Chernoff_productDist
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:55:18.381982+00:00
-- url     : https://prove2.me/theorems/fe1313ba-0e9d-47ca-97ec-416b174399f9
-- title:
--   Distribution of $N$ independent samplings, eqs. (2.21)–(2.22)
-- statement:
--   If $p$ is a distribution on a finite outcome set and the observer samples $N$ times independently, the outcome string $b_1 b_2 \dots b_N$ has probability
--
--   $$
--   p(b_1 b_2 \dots b_N) = p(b_1)\, p(b_2) \cdots p(b_N).
--   $$
--
--   These product distributions turn the $N$-sample decision problem into a one-sample problem on the set of strings.
--
--   **Formalization Note** Strings of length $N$ are functions from $\mathrm{Fin}\,N$ to the outcome type (trial $k$ is indexed from $0$). The empty string ($N = 0$) has probability $1$. The source's (2.21) prints $p_1(b_N)$ as the last factor of $p_0(b_1\dots b_N)$; the product of the $p_0(b_k)$ is meant.
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, §2.2.2, eqs. (2.21)–(2.22), p.17 (PDF p.26)

import Mathlib

namespace FuchsThesis.Chernoff

/-- Fuchs, *Distinguishability and Accessible Information in Quantum Theory*,
arXiv:quant-ph/9601020v1, §2.2.2, eqs. (2.21)–(2.22), p.17 (PDF p.26).

The distribution of the outcome string `b⃗ = (b1, …, bN)` of `N` independent samplings of `p`:
`p(b1 b2 … bN) = p(b1) p(b2) ⋯ p(bN)`.

**Formalization Note.** Strings of length `N` are functions `Fin N → B` (the `k`-th trial is
`s k`, indexed from `0`). (2.21) prints `p1(bN)` as the last factor of `p0(b1 … bN)`; the
product of the `p0(bk)` is meant, as the third line of (2.28) confirms. At `N = 0` the only
string is empty and has probability `1`. -/
def productDist {B : Type} (p : B → ℝ) (N : ℕ) : (Fin N → B) → ℝ :=
  fun s => ∏ k, p (s k)

end FuchsThesis.Chernoff


