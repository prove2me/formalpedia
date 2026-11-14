-- Prove2me | Definitions.Def_ITPIRPreproc_MatchVec_PolynomialConstruction
-- name    : ITPIRPreproc_MatchVec_PolynomialConstruction
-- status  : Definition
-- author  : @Jesko
-- created : 2026-11-13T17:12:33.923988+00:00
-- url     : https://prove2.me/theorems/ea94c2a5-741e-46e6-a1eb-5c2dd911125f
-- title:
--   Appendix A — indexed polynomial matching-vector construction
-- statement:
--   Definitions for the polynomial matching-vector construction in Appendix A. For a word length $\ell$, exponents $a,b$, and agreement count $j$, the CRT signal is
--   $$F(j)=3\mathbf1[j\equiv\ell\pmod{2^a}]+4\mathbf1[j\equiv\ell\pmod{3^b}]\in\mathbb Z_6.$$
--   The coefficient $c_t$ is its binomial inverse $\sum_{j=0}^t(-1)^{t-j}\binom tjF(j)$, and the degree cutoff is $k=\max(2^a,3^b)-1$. A coordinate is a pair $(I,\alpha)$ with $I\subseteq[\ell]$, $|I|\le k$, and $\alpha:I\to[\ell]$. The vectors for a word $\sigma$ have entries $u_\sigma(I,\alpha)=c_{|I|}\mathbf1[\sigma|_I=\alpha]$ and $v_\sigma(I,\alpha)=\mathbf1[\sigma|_I=\alpha]$.
--
--   The definitions keep the prime-power exponents as parameters. They do not assume or certify a degree bound, a matching-vector property, or a RAM implementation. The use of congruence of $j$ and $\ell$ agrees with the paper's divisibility condition $p^e\mid\ell-j$ when $0\le j\le\ell$, and extends it periodically to all natural $j$.
-- source:
--   Jesko Dujmovic, Zhengnan Lai, Daniel Wichs, Nearly Optimal Information-Theoretic PIR with Client Preprocessing, STOC 2027 submission #572, Appendix A, printed pp.36-37 (PDF pp.38-39), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/572.pdf

import Definitions.Def_ITPIRPreproc_MatchVec_MatchingVectors
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators

namespace ITPIRPreproc.MatchVec.PolynomialConstruction

open Finset

/-- The symmetric CRT indicator from Appendix A. Its arguments are the word length,
the exponents of the powers of 2 and 3, and the number of agreeing coordinates. -/
def signal (ell a b j : ℕ) : ZMod 6 :=
  3 * (if j % 2^a = ell % 2^a then 1 else 0) +
  4 * (if j % 3^b = ell % 3^b then 1 else 0)

/-- Coefficients obtained by binomial inversion (Appendix A, printed p.36). -/
def coefficient (ell a b t : ℕ) : ZMod 6 :=
  ∑ j ∈ range (t+1), (-1 : ZMod 6)^(t-j) * (t.choose j : ZMod 6) * signal ell a b j

/-- The degree cutoff of the CRT polynomial. -/
def degree (a b : ℕ) : ℕ := max (2^a) (3^b) - 1

/-- Subsets indexing monomials up to the chosen degree. -/
abbrev Subsets (ell k : ℕ) := {I : Finset (Fin ell) // I.card ≤ k}

/-- A coordinate consists of a small subset and an alphabet assignment to that subset. -/
abbrev Coordinate (ell k : ℕ) := Σ I : Subsets ell k, (I.val → Fin ell)

/-- Restriction of a row word to a subset. -/
def restriction {ell : ℕ} (sigma : Fin ell → Fin ell) (I : Finset (Fin ell)) :
    I → Fin ell := fun j => sigma j

/-- Left vector of the polynomial matching-vector construction. -/
def leftVector {ell k : ℕ} (c : ℕ → ZMod 6) (sigma : Fin ell → Fin ell)
    (z : Coordinate ell k) : ZMod 6 :=
  if restriction sigma z.1.val = z.2 then c z.1.val.card else 0

/-- Right vector; its singleton coordinates distinguish all row words modulo 2. -/
def rightVector {ell k : ℕ} (sigma : Fin ell → Fin ell)
    (z : Coordinate ell k) : ZMod 6 :=
  if restriction sigma z.1.val = z.2 then 1 else 0

/-- Coordinates on which two row words agree. -/
def agreement {ell : ℕ} (sigma tau : Fin ell → Fin ell) : Finset (Fin ell) :=
  univ.filter fun j => sigma j = tau j

end ITPIRPreproc.MatchVec.PolynomialConstruction


