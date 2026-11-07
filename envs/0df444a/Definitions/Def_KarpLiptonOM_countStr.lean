-- Prove2me | Definitions.Def_KarpLiptonOM_countStr
-- name    : KarpLiptonOM_countStr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:37:04.553855+00:00
-- url     : https://prove2.me/theorems/1a897c9c-a25f-4586-939a-bf6c5861b0f7
-- title:
--   Number of strings of length $m$ satisfying a predicate
-- statement:
--   For $m \in \mathbb N$ and a predicate $P$ on binary strings, $\#\{r \in \{0,1\}^m : P(r)\}$ is the number of strings of length exactly $m$ satisfying $P$. Every probability in this development is uniform over a set $\{0,1\}^m$ and is written through this count:
--   $$
--   \Pr_{r \in \{0,1\}^m}[P(r)] = \frac{\#\{r \in \{0,1\}^m : P(r)\}}{2^m}.
--   $$
--
--   **Formalization Note** Probability bounds such as $\Pr_r[\cdot] < 1/4$ are stated as the equivalent integer inequalities $4\cdot\# < 2^m$.
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), §A.2.1, p.20 (uniform probabilities over strings of fixed length)

import Mathlib

namespace KarpLiptonOM

/-- The number of strings `r ∈ {0,1}^m` satisfying `P` (Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b), §A.2.1, p.20: "probabilities `Pr_r`
(always over the uniform distribution) range over strings of exactly this length"). A probability
`Pr_r[P(r)]` over `{0,1}^m` is `countStr m P / 2^m`.

**Formalization Note** Strings of length `m` are enumerated as `List.ofFn r` for `r : Fin m → Bool`;
probability bounds are stated as integer inequalities between `countStr m P` and `2^m`. -/
noncomputable def countStr (m : ℕ) (P : List Bool → Prop) : ℕ := by
  classical exact (Finset.univ.filter (fun r : Fin m → Bool => P (List.ofFn r))).card

end KarpLiptonOM


