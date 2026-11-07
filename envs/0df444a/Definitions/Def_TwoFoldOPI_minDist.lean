-- Prove2me | Definitions.Def_TwoFoldOPI_minDist
-- name    : TwoFoldOPI_minDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:43:22.045725+00:00
-- url     : https://prove2.me/theorems/49e06273-c167-4273-bf8a-98ff2ca3825c
-- title:
--   The minimum distance $\mathrm{dist}(C)$
-- statement:
--   The minimum distance of a linear code $C\subseteq\mathbb F_q^M$ is the least Hamming weight of a nonzero codeword:
--   $$\operatorname{dist}(C)=\min\{\operatorname{wt}(c): c\in C,\ c\neq0\}.$$
--
--   **Formalization Note** For $C=\{0\}$ the minimum is over an empty set and the value is $0$; the goal reads $\operatorname{dist}(C^\perp)$ only when $C^\perp\neq\{0\}$, and Lemma 7.3's second inequality holds for any value at $C^\perp=\{0\}$.
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §5, Notation, p. 20

import Mathlib

namespace TwoFoldOPI

/-- **The minimum distance `dist(C)`.**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §5, Notation, p.20: "wt(x) is its Hamming weight … dist(C) is the minimum distance of a code
C". For a linear code this is the least Hamming weight of a nonzero codeword.

**Formalization Note.** For the zero code the set is empty and Lean's `sInf ∅ = 0`; every
statement of the mission that reads `minDist` either assumes `C ≠ {0}` or holds for any value at
`C = {0}` (see the statements). -/
noncomputable def minDist {K : Type*} [Field K] [DecidableEq K] {M : ℕ}
    (C : Submodule K (Fin M → K)) : ℕ :=
  sInf {w | ∃ c ∈ C, c ≠ 0 ∧ hammingNorm c = w}

end TwoFoldOPI


