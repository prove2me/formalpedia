-- Prove2me | Definitions.Def_OptTwoSrcExt_Supplement_fingerprint
-- name    : OptTwoSrcExt_Supplement_fingerprint
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:37:17.111723+00:00
-- url     : https://prove2.me/theorems/3fea83eb-7df9-4c21-b286-c978d3fa0d06
-- title:
--   Polynomial fingerprints $P_x$ and the advice function $\mathrm{Adv}$
-- statement:
--   Fix a representation of $F=\mathbb F_{2^q}$ by $q$-bit strings and let $h=\lceil n/q\rceil$. Pad an $n$-bit string $x$ with zeros to $hq$ bits and read its consecutive $q$-bit blocks as $x_0,\dots,x_{h-1}\in F$. The **polynomial fingerprint** of $x$ is
--   $$P_x(T)=\sum_{j=0}^{h-1}x_jT^j\in F[T].$$
--   Given a function $S:\{0,1\}^n\times\{0,1\}^n\to F$, the **advice function** is
--   $$\mathrm{Adv}(x,y)=\big(S(x,y),\,P_x(S(x,y)),\,P_y(S(x,y))\big)\in F^3.\tag{5.3}$$
--
--   The map $x\mapsto P_x$ is injective, so two distinct strings have fingerprints that agree at no more than $h-1$ points; this is what makes the advice of Theorem 5.10 separate honest and tampered inputs.
-- source:
--   X. Li, Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate, STOC 2027 submission (manuscript sha256 2edb00b2…), §5.1.5, p.106 (PDF p.108); (5.3), p.107 (PDF p.109)

import Mathlib

namespace OptTwoSrcExt.Supplement

/-- **The number of `q`-bit blocks of an `n`-bit string**, `h = ⌈n/q⌉`. -/
def numBlocks (n q : ℕ) : ℕ := (n + q - 1) / q

/-- **The `j`-th `q`-bit block of `x ∈ {0,1}ⁿ` after zero padding to `hq` bits**: bits
`jq, …, jq + q − 1` of `x`, a bit past position `n − 1` read as `0`. -/
def bitBlock {n : ℕ} (q : ℕ) (x : Fin n → Bool) (j : ℕ) : Fin q → Bool :=
  fun i => if h : j * q + (i : ℕ) < n then x ⟨j * q + i, h⟩ else false

/-- **The polynomial fingerprint `P_x(T) = Σ_{j=0}^{h−1} x_j T^j`.**
Li, *Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate*, STOC 2027
submission (manuscript sha256 2edb00b2…), §5.1.5 "Polynomial fingerprints give separated advice",
printed p.106 (PDF p.108): "Fix a representation of F = F_{2^q}, and let h = ⌈n/q⌉. Pad an n-bit
string x with zeros to hq bits, interpret its consecutive blocks as x0, . . . , x_{h−1} ∈ F, and
define Px(T) = Σ_{j=0}^{h−1} xj T^j ∈ F[T]."

`fingerprint rep x` with `rep : {0,1}^q → F` the fixed representation of field elements by `q` bits. -/
noncomputable def fingerprint {F : Type*} [CommRing F] {n q : ℕ} (rep : (Fin q → Bool) → F)
    (x : Fin n → Bool) : Polynomial F :=
  ∑ j ∈ Finset.range (numBlocks n q), Polynomial.C (rep (bitBlock q x j)) * Polynomial.X ^ j

/-- **The advice function (5.3)** `Adv(x, y) = (S(x, y), P_x(S(x, y)), P_y(S(x, y))) ∈ F³`
(Theorem 5.10, printed p.107, PDF p.109). -/
noncomputable def advice {F : Type*} [CommRing F] {n q : ℕ} (rep : (Fin q → Bool) → F)
    (S : (Fin n → Bool) → (Fin n → Bool) → F) (x y : Fin n → Bool) : F × F × F :=
  (S x y, (fingerprint rep x).eval (S x y), (fingerprint rep y).eval (S x y))

end OptTwoSrcExt.Supplement


