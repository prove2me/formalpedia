-- Prove2me | Definitions.Def_NearOptOWF_Supplement_relDensity
-- name    : NearOptOWF_Supplement_relDensity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:10:23.441488+00:00
-- url     : https://prove2.me/theorems/51ef113d-91d2-4b00-9792-a38aae9b7080
-- title:
--   Density $\mu$ of a $t$-ary relation ensemble
-- statement:
--   A **$t$-ary relation ensemble** $\mathcal R$ assigns to each input length $n$ a set $\mathcal R_n$ of $t(n)$-tuples of strings in $\{0,1\}^{m(n)}$. Its **density** is
--   $$
--   \mu(n) = \Pr_{y_1,\dots,y_t\leftarrow\{0,1\}^{m}}\bigl[(y_1,\dots,y_t)\in\mathcal R_n\bigr] = \frac{|\mathcal R_n|}{2^{m(n)\,t(n)}} .
--   $$
--
--   **Formalization Note** The paper indexes the ensemble by $m$; since the arity $t$ is a function of $n$, it is indexed by $n$ here. $\mathcal R_n$ is an arbitrary set, not necessarily efficiently decidable.
-- source:
--   Ilango–Lombardi–Tu, Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Theorem 5.2 and Definition 5.1, p.23 (PDF p.25)

import Mathlib

namespace NearOptOWF.Supplement

/-- The **density** of a `t`-ary relation ensemble (Ilango–Lombardi–Tu, *Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP*, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Theorem 5.2, p.23 (PDF p.25):
"`µ = Pr_{y₁,…,y_t←{0,1}^m}[(y₁, …, y_t) ∈ R]`"): at input length `n`, `R n` is a set of `t(n)`-tuples of
strings in `{0,1}^{m(n)}`, and its density is `|R n| / 2^{m(n)·t(n)}`, the probability that `t(n)`
independent uniform strings of length `m(n)` form a tuple in `R n`.

**Formalization Note** Definition 5.1 indexes the ensemble by `m`; since `t` is a function of `n`, the
ensemble is indexed by `n` here (every ensemble indexed by `m(n)` is one of these). `R n` is arbitrary,
not necessarily efficiently decidable. -/
noncomputable def relDensity (m t : ℕ → ℕ) (R : (n : ℕ) → Set (Fin (t n) → Fin (m n) → Bool))
    (n : ℕ) : ℝ :=
  ((R n).ncard : ℝ) / 2 ^ (m n * t n)

end NearOptOWF.Supplement


