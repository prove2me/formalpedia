-- Prove2me | Definitions.Def_SecondBestBT_Mechanism
-- name    : SecondBestBT_Mechanism
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:42:36.170223+00:00
-- url     : https://prove2.me/theorems/1dc47f88-e72b-412d-be0b-61c62d779ecf
-- title:
--   Direct mechanism $(x, p_B, p_S)$ for bilateral trade
-- statement:
--   A **mechanism** for bilateral trade consists of three functions of the reported profile $(s,b)$, the seller's report first:
--
--   1. the **allocation rule** $x(s,b)$, the probability that the good is traded;
--   2. the buyer's expected **payment** $p_B(s,b)\in\mathbb R$;
--   3. the seller's expected **revenue** $p_S(s,b)\in\mathbb R$.
--
--   Transfers are signed. The requirement $x\in[0,1]$ on the type set, measurability and integrability are collected in the predicate *well defined*.
--
--   **Formalization Note** The three rules are functions $\mathbb R\times\mathbb R\to\mathbb R$; values outside the type set play no role in any notion of the mission.
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), Section 2, p.4

import Mathlib

namespace SecondBestBT

/-- A direct mechanism for bilateral trade (Liu–Qin–Ren–Wang, arXiv:2606.03849, held version
sha256 17184930…, Section 2, p.4): an allocation rule `x`, the probability of trade at the
reported profile, the buyer's expected payment `pB` and the seller's expected revenue `pS`.

**Formalization Note** Every rule is a function of the reported profile `(s, b) : ℝ × ℝ` with the
**seller's report first**, as in the paper's `x(s, b)`. Payments are signed reals ("we allow
signed transfers", p.1). Values outside the type set are irrelevant to every notion of the
mission; the constraint `x ∈ [0, 1]` on the type set is part of `WellDefined`. -/
structure Mechanism where
  /-- allocation rule `x(s, b)`: probability of trade at reports `(s, b)` -/
  x : ℝ × ℝ → ℝ
  /-- buyer's expected payment `p_B(s, b)` -/
  pB : ℝ × ℝ → ℝ
  /-- seller's expected revenue `p_S(s, b)` -/
  pS : ℝ × ℝ → ℝ

end SecondBestBT


