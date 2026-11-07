-- Prove2me | Definitions.Def_NSWBetter_Inst
-- name    : NSWBetter_Inst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:48:05.467853+00:00
-- url     : https://prove2.me/theorems/cb855aef-f6b9-4e5c-92fb-19d2a6eae1a5
-- title:
--   Rational fair allocation instance with additive valuations
-- statement:
--   A **fair allocation instance** with additive valuations consists of $n$ agents $N=[n]$, $m$ goods $G=\{g_1,\dots,g_m\}$, and for every agent $i$ and good $g$ a value $v_i(g)$; the value of a bundle $S\subseteq G$ is $v_i(S)=\sum_{g\in S}v_i(g)$.
--
--   This is the input of the Nash social welfare maximization problem of Theorem 1.1.
--
--   **Formalization Note** Agents and goods are $0$-based (`Fin n`, `Fin m`). Values are rational because the instance is an algorithm's input; nonnegativity is stated separately by `Inst.WellFormed`.
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Section 2, p.8 (fair allocation instance; additive valuations)

import Mathlib

namespace NSWBetter

/-- **A fair allocation instance with additive valuations, rational input.**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Section 2, p.8: "A fair allocation instance I is defined by a set of n agents N = [n] and a set of m goods G … Each agent i ∈ N has a valuation function vi : 2^G → R≥0 … we assume agent valuations are additive".

`Inst` records `n`, `m` and the value `v i g = v_i({g})` of agent `i` for good `g`; the value of a bundle is the sum.

**Formalization Note.** Agents are `Fin n`, goods `Fin m` (0-based). Values are rationals because the instance is the input of an algorithm (finite binary input); nonnegativity is the separate predicate `Inst.WellFormed`. `n = 0`, `m = 0` and zero values are allowed. -/
structure Inst where
  /-- the number of agents -/
  n : ℕ
  /-- the number of goods -/
  m : ℕ
  /-- `v i g`: value of agent `i` for good `g` -/
  v : Fin n → Fin m → ℚ

end NSWBetter


