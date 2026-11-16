-- Prove2me | Definitions.Def_SubexpPrimes_Supplement_rootCount
-- name    : SubexpPrimes_Supplement_rootCount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:44:49.649306+00:00
-- url     : https://prove2.me/theorems/d9e558a4-7259-41c4-af3b-60a868122b08
-- title:
--   Number $r_p$ of roots of $f\in\mathbb Z[X]$ modulo $p$
-- statement:
--   For $f\in\mathbb Z[X]$ and an integer $m\ge1$, let
--
--   $$
--   r_m=\#\{u\in\{0,1,\dots,m-1\} : f(u)\equiv 0 \pmod m\}.
--   $$
--
--   For a prime $p$ this is the number of $u\in\mathbb Z/p\mathbb Z$ with $f(u)\equiv0\pmod p$: **distinct** roots of $f$ modulo $p$, not counted with multiplicity. The module also fixes the input encoding of an integer polynomial: its coefficients $f_0,f_1,\dots,f_d$, each written as a sign bit followed by the absolute value in binary.
--
--   This is the root count used in the last item of Theorem 3 and in Theorem 8.2.
--
--   **Formalization Note** Residues modulo $m$ are represented by $0\le u<m$; the count is used only at primes.
-- source:
--   Gajulapalli, Deterministic Construction of Primes in Subexponential Time (manuscript, sha256 6ad4d3de…), Theorem 8.2, p.35 (PDF p.37), and proof of Theorem 8.2, p.36 (PDF p.38)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_SubexpPrimes_RunsWithin

set_option autoImplicit false

namespace SubexpPrimes.Supplement

open OAI.Algorithms.SubexponentialSAT

/-- **The number of roots of `f` modulo `m`** — Gajulapalli, *Deterministic Construction of Primes
in Subexponential Time* (manuscript, sha256 6ad4d3de…), Theorem 8.2, p.35 ("for a prime p, let r_p be
the number of u ∈ Z/pZ with f(u) ≡ 0 (mod p)") and proof of Theorem 8.2, p.36 ("for m ≥ 2 let r_m be
the number of u ∈ [0, m) with f(u) ≡ 0 (mod m)").

`rootCount f m = #{u ∈ [0, m) : m ∣ f(u)}`.

**Formalization Note.** Distinct roots, not counted with multiplicity: the residues `u ∈ ℤ/pℤ` are
represented by `0 ≤ u < p`. It is used only at primes `p`, where it is `r_p`. -/
def rootCount (f : Polynomial ℤ) (m : ℕ) : ℕ :=
  ((Finset.range m).filter (fun u : ℕ => (m : ℤ) ∣ f.eval (u : ℤ))).card

/-- The input word of an integer polynomial: its coefficients `f₀, f₁, …, f_d` (`d` its degree), each
as an `intWord` (sign bit, then the absolute value in binary, least significant bit first). -/
def coeffWord (f : Polynomial ℤ) : List Bool :=
  Encoding.encodeList intWord ((List.range (f.natDegree + 1)).map f.coeff)

end SubexpPrimes.Supplement


