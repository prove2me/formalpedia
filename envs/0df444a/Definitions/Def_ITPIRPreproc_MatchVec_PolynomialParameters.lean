-- Prove2me | Definitions.Def_ITPIRPreproc_MatchVec_PolynomialParameters
-- name    : ITPIRPreproc_MatchVec_PolynomialParameters
-- status  : Definition
-- author  : @Jesko
-- created : 2026-11-13T17:19:36.191185+00:00
-- url     : https://prove2.me/theorems/7ef0c615-58fa-42d1-9285-8a1193e40da7
-- title:
--   Appendix A — least word length and prime-power parameters
-- statement:
--   For a family with $2^h$ rows, define $\ell(h)$ to be the least natural number satisfying $\ell(h)^{\ell(h)}\ge2^h$, as in Appendix A. Define $e_p(\ell)=\lceil\log_p(\lfloor\sqrt\ell\rfloor+1)\rceil$ for $p=2,3$. Thus $p^{e_p(\ell)}$ is the least power of $p$ strictly exceeding $\sqrt\ell$. The family uses exponents $a(h)=e_2(\ell(h))$ and $b(h)=e_3(\ell(h))$.
--
--   The prime-power choice uses the square-root threshold needed by the dimension bound, as noted in the formalization of the original matching-vector milestone. These are mathematical parameter definitions, not RAM programs. The least-word-length definition uses the witness $\ell=2^h$ solely to justify existence; it does not claim that this witness is used by an efficient implementation.
-- source:
--   Jesko Dujmovic, Zhengnan Lai, Daniel Wichs, Nearly Optimal Information-Theoretic PIR with Client Preprocessing, STOC 2027 submission #572, Appendix A, printed pp.36-37 (PDF pp.38-39), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/572.pdf

import Definitions.Def_ITPIRPreproc_MatchVec_PolynomialConstruction
import Mathlib.Data.Nat.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.Order.Floor.Semiring

namespace ITPIRPreproc.MatchVec.PolynomialConstruction

/-- The least word length with enough row words, as in Appendix A. -/
noncomputable def wordLength (h : ℕ) : ℕ := Nat.find (show ∃ ell : ℕ, 2^h ≤ ell^ell from
  ⟨2^h, le_self_pow (by
    have hp : 0 < 2^h := by positivity
    omega) (by positivity)⟩)

/-- The least exponent whose prime power exceeds the square root of the word length. -/
def primeExponent (p ell : ℕ) : ℕ := Nat.clog p (Nat.sqrt ell + 1)

/-- The prime-power exponents used for the indexed family at size 2^h. -/
noncomputable def exponent2 (h : ℕ) : ℕ := primeExponent 2 (wordLength h)
noncomputable def exponent3 (h : ℕ) : ℕ := primeExponent 3 (wordLength h)

end ITPIRPreproc.MatchVec.PolynomialConstruction


