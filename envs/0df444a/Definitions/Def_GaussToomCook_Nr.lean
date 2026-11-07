-- Prove2me | Definitions.Def_GaussToomCook_Nr
-- name    : GaussToomCook_Nr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:45:04.75347+00:00
-- url     : https://prove2.me/theorems/b8bc4c33-a8dc-4ea6-8745-bf28c524dd1d
-- title:
--   Norm $\mathrm{Nr}(p)$ of a Gaussian integer
-- statement:
--   For a Gaussian integer $p=a+bi\in\mathbb Z[i]$ the **norm** is
--   $$\mathrm{Nr}(p)=a^2+b^2 .$$
--   For $p\neq 0$ it equals the number of residue classes $|\mathbb Z[i]/p\mathbb Z[i]|$, which is how the paper uses it: the projective line over $\mathbb Z[i]/p\mathbb Z[i]$ has $\mathrm{Nr}(p)+1$ points when $p$ is a Gaussian prime. For example $\mathrm{Nr}(1+i)=2$ and $\mathrm{Nr}(2+i)=5$.
--
--   **Formalization Note** The norm is the natural number $|a^2+b^2|$, the absolute value of Mathlib's `Zsqrtd.norm`.
-- source:
--   Y. Spiizer, R. S. Steiner, Rational and Gaussian long integer multiplication, manuscript (STOC 2027 submission; held version sha256 f50b53628a53a03bd55785424af241d0ac5ea751714330838e4017b90b27ad70), §9.2, proof of Proposition 9.1, p. 31 (PDF p. 33)

import Mathlib

namespace GaussToomCook

/-- **The norm `Nr(p)` of a Gaussian integer**, Spiizer, Steiner, *Rational and Gaussian long integer multiplication*, manuscript (STOC 2027 submission; sha256 f50b5362…27ad70), §9.2, proof of
Proposition 9.1, p. 31 (PDF 33): `Nr(p) = |ℤ[i]/pℤ[i]|`, the number of residue classes modulo `p`.

**Formalization Note.** Defined as the natural number `|a² + b²|` for `p = a + bi`, i.e. the absolute
value of Mathlib's `Zsqrtd.norm`. For `p ≠ 0` this is the cardinality of `ℤ[i]/pℤ[i]`; the paper only
evaluates `Nr` at Gaussian primes and at nonzero divisors `λ`. -/
def Nr (p : GaussianInt) : ℕ := (Zsqrtd.norm p).natAbs

end GaussToomCook


