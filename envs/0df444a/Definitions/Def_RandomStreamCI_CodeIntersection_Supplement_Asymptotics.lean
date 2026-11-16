-- Prove2me | Definitions.Def_RandomStreamCI_CodeIntersection_Supplement_Asymptotics
-- name    : RandomStreamCI_CodeIntersection_Supplement_Asymptotics
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:47:21.727288+00:00
-- url     : https://prove2.me/theorems/ffa87a61-3d13-4c0e-8377-69b81471edb1
-- title:
--   All power-of-two OPI blocklengths and degree families
-- statement:
--   An admissible blocklength is an integer $n$ with $n+1=2^e$ for some $e\ge1$. Limits are taken as $n\to\infty$ through all these blocklengths. A degree family $d(n)$ has $1\le d(n)\le n$ at every admissible $n$.
--
--   These definitions specify only the parameter domain and limit filter. They impose neither the classical nor the quantum rate conditions, which are distinct hypotheses of their respective theorems. Values of a family outside the admissible lengths are irrelevant.
-- source:
--   Bouland–Ding–Jain, Exponential quantum space advantage in random data streams, STOC 2027 submission #71, preprint dated 2026-11-02, release papers-1/71.pdf, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/71.pdf, SHA256 3fe1835efedc1b9f29103379085d28d84ab1057dc30c3e3f05a8dce9f536a797, Problem 2, p. 6; Theorem 27, p. 22; Theorem 29, p. 28

import Definitions.Def_RandomStreamCI_CodeIntersection_Supplement_OPI

namespace RandomStreamCI.CodeIntersection.Supplement

open Filter Topology

/-- All source blocklengths n=2^e-1, e>=1, not a prime-only subsequence. -/
def AdmissibleLength (n : ℕ) : Prop := ∃ e : ℕ, 1 ≤ e ∧ n + 1 = 2^e

/-- Tending to infinity along all source-admissible blocklengths. -/
def opiAtTop : Filter ℕ := Filter.atTop ⊓ Filter.principal {n | AdmissibleLength n}

/-- Problem 2's dimension range at each admissible length. -/
def DegreeFamily (d : ℕ → ℕ) : Prop :=
  ∀ n, AdmissibleLength n → 1 ≤ d n ∧ d n ≤ n

end RandomStreamCI.CodeIntersection.Supplement


