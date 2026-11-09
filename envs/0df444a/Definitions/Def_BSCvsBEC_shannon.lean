-- Prove2me | Definitions.Def_BSCvsBEC_shannon
-- name    : BSCvsBEC_shannon
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T08:29:34.165943+00:00
-- url     : https://prove2.me/theorems/5944bbb3-3f94-4729-a54c-c8550e687cdb
-- title:
--   Probability mass functions and Shannon entropy $H(P)$ in bits
-- statement:
--   A **probability mass function** (pmf) on a finite set $\alpha$ is a function $P:\alpha\to\mathbb R$ with $P(x)\ge 0$ for every $x$ and $\sum_x P(x)=1$; a random variable $X$ on a finite set is represented by its pmf $P_X$.
--
--   The **Shannon entropy** of $P$, in bits, is
--   $$H(P)=\sum_x P(x)\log_2\frac{1}{P(x)}=-\sum_x P(x)\log_2 P(x),$$
--   with the convention $0\log 0=0$.
--
--   These are the classical entropies of the paper: "Unless otherwise specified, log denotes $\log_2$", and $H(X)$ is the Shannon entropy of $P_X$.
--
--   **Formalization Note** The convention $0\log 0=0$ comes from Lean's $\log_2 0=0$. The entropy is defined for every real function but is only applied to pmfs.
-- source:
--   J. Hązła, R. O'Donnell, BSC vs. BEC vs. PSC, manuscript of November 3, 2026 (STOC 2027 submission, preprint basis, sha256 a44ed9262ff4e01c0cbd7e204728d4ad8bf4cfda8dbf126b96022d4c84b56186), §2.1, p.5

import Mathlib

namespace BSCvsBEC

/-- A probability mass function on a finite type: nonnegative weights summing to `1`.
Hązła–O'Donnell, *BSC vs. BEC vs. PSC*, manuscript of November 3, 2026 (STOC 2027 submission,
sha256 a44ed926…), §2.1, p.5 ("a random variable `X ∈ Ωⁿ` … with distribution `P_X`").

**Formalization Note.** A random variable on a finite set is represented by its pmf
`P : α → ℝ`; this predicate says `P` is one. -/
def IsPMF {α : Type*} [Fintype α] (P : α → ℝ) : Prop :=
  (∀ x, 0 ≤ P x) ∧ ∑ x, P x = 1

/-- Shannon entropy in bits, `H(P) = ∑ₓ P(x) log₂ (1 / P(x)) = −∑ₓ P(x) log₂ P(x)`.
Hązła–O'Donnell, manuscript of November 3, 2026 (sha256 a44ed926…), §2.1, p.5:
"Unless otherwise specified, log denotes log₂ … the Shannon entropy, `H(X) := ∑ₓ P_X(x) log(1/P_X(x))`."

**Formalization Note.** The convention `0 log 0 = 0` holds because `Real.logb 2 0 = 0`.
The definition is applied to pmfs only (`IsPMF`). -/
noncomputable def shannon {α : Type*} [Fintype α] (P : α → ℝ) : ℝ :=
  -∑ x, P x * Real.logb 2 (P x)

end BSCvsBEC


