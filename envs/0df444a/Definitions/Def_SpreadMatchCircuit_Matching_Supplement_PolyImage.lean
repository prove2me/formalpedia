-- Prove2me | Definitions.Def_SpreadMatchCircuit_Matching_Supplement_PolyImage
-- name    : SpreadMatchCircuit_Matching_Supplement_PolyImage
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:32:54.663788+00:00
-- url     : https://prove2.me/theorems/03162eb5-5d9f-4d91-8bec-8094f3ba4f3b
-- title:
--   The polynomial-image Boolean function $F_{k,d}$ over $\mathbb F_n$
-- statement:
--   Let $n$ be a prime and $\mathbb F_n$ the field with $n$ elements. Consider $n$ Boolean variables $x_i$, one for each field element $i\in\mathbb F_n$. Let $D_d$ be the set of univariate polynomials over $\mathbb F_n$ of degree exactly $d$. For $w\in D_d$ and a natural number $k$, let
--   $$w([k])=\{w(1),w(2),\dots,w(k)\}\subseteq\mathbb F_n$$
--   be the set of values of $w$ at the integers $1,\dots,k$, read in $\mathbb F_n$, without multiplicities. Define
--   $$F_{k,d}(x)=\bigvee_{\substack{w\in D_d\\ |w([k])|\ge k/2}}\ \bigwedge_{i\in w([k])}x_i .$$
--   Thus $F_{k,d}(x)=1$ exactly when some polynomial of degree $d$ whose image on $[k]$ has at least $k/2$ distinct values has all its image points set to $1$ in $x$. An empty disjunction is false.
--
--   This explicit monotone function is the subject of Theorem 9.
--
--   **Formalization Note** $\mathbb F_n$ is `ZMod n` and the variables are indexed by `ZMod n` itself. "Degree exactly $d$" is `w.degree = d`, which excludes the zero polynomial also when $d=0$. The condition $|w([k])|\ge k/2$ is written $k\le 2\,|w([k])|$. The definition is stated for every natural number $n$; primality is a hypothesis of Theorem 9.
-- source:
--   Anup Rao, STOC 2027 submission #299 (October 2026), p. 5 (§1.3: "Without loss of generality, assume n is a prime. Let D_d denote the set of univariate polynomials of degree d over F_n", displayed definition of F_{k,d})

import Mathlib

namespace SpreadMatchCircuit.Matching.Supplement

open Polynomial

/-- `w([k]) = {w(1), …, w(k)}`: the set of values of the polynomial `w` over `𝔽_n = ZMod n` at the
integers `1, …, k` (read in the field), without multiplicities. -/
def polyImage (n k : ℕ) (w : (ZMod n)[X]) : Finset (ZMod n) :=
  (Finset.Icc 1 k).image fun j : ℕ => w.eval (j : ZMod n)

/-- The Boolean function `F_{k,d}` on the `n` variables `x_i`, `i ∈ 𝔽_n`:
`F_{k,d}(x) = ⋁_{w ∈ D_d, |w([k])| ≥ k/2} ⋀_{i ∈ w([k])} x_i`, where `D_d` is the set of
univariate polynomials over `𝔽_n` of degree exactly `d` (so the zero polynomial is excluded).
An empty disjunction is false. -/
def PolyImageFun (n k d : ℕ) (x : ZMod n → Bool) : Prop :=
  ∃ w : (ZMod n)[X], w.degree = (d : WithBot ℕ) ∧ k ≤ 2 * (polyImage n k w).card ∧
    ∀ i ∈ polyImage n k w, x i = true

end SpreadMatchCircuit.Matching.Supplement


