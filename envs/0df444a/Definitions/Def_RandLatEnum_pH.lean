-- Prove2me | Definitions.Def_RandLatEnum_pH
-- name    : RandLatEnum_pH
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:13:04.636516+00:00
-- url     : https://prove2.me/theorems/b0c43d33-0b19-415d-b7af-e534d7a5f1d9
-- title:
--   HKZ prefix profile $p_H(t)=-\frac{1-t}{2}\ln(1-t)$
-- statement:
--   $$
--   p_H(t)=-\frac{1-t}{2}\ln(1-t)\qquad(0\le t\le1).
--   $$
--   By Lemma 4.1 it bounds the normalized prefix log-determinants $P_{\lfloor td\rfloor}(B_H)/(d\ln d)$ of every HKZ basis of a unimodular rank-$d$ lattice, up to $o(1)$.
--
--   **Formalization Note** At $t=1$ Lean's convention $\ln 0=0$ gives $p_H(1)=0$, which is the limit of $p_H(t)$ as $t\to1$.
-- source:
--   Laarhoven, Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices, arXiv:2610.15265 (held version, sha256 8fa7a08a…), Lemma 4.1, (4.3), p.19

import Mathlib

namespace RandLatEnum

/-- The HKZ prefix profile `p_H(t) = −((1 − t)/2) ln(1 − t)` (Laarhoven, *Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices*, arXiv:2610.15265 (held version, sha256 8fa7a08a…), Lemma 4.1, (4.3), p.19).

**Formalization Note.** At `t = 1` Lean's `Real.log 0 = 0` gives `p_H(1) = 0`, which is the limit
of `p_H(t)` as `t → 1`; the lemma uses `0 ≤ t ≤ 1`. -/
noncomputable def pH (t : ℝ) : ℝ :=
  -((1 - t) / 2) * Real.log (1 - t)

end RandLatEnum


