-- Prove2me | Definitions.Def_FasterPrimeEnum_Supplement_Delta
-- name    : FasterPrimeEnum_Supplement_Delta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:49:15.000551+00:00
-- url     : https://prove2.me/theorems/758c1bc6-849c-417c-a0bd-deebe7e778c1
-- title:
--   Sieve data for a $g$-tuple: bad primes, $Q(u)$, $|B_p|$, $\Delta(u)$, $\theta(g,Q)$
-- statement:
--   Let $g,U$ be positive integers and $u=(u_1,\dots,u_g)$ pairwise distinct with $0\le u_i<U$.
--
--   1. For a prime $p$, $B_{p,i}:=\{k\in\mathbb Z/p^2\mathbb Z:\ Uk+u_i\equiv0\pmod p,\ Uk+u_i\not\equiv0\pmod{p^2}\}$ and $B_p:=\bigcup_i B_{p,i}$.
--   2. A prime $p$ is **bad** if $p\mid U$, or $p\mid u_i-u_j$ for some $i\ne j$, or $p\le 4g^2$; $Q(u):=\prod_{p\text{ bad}}p$ (so $Q\ge6$).
--   3. $\displaystyle \Delta(u):=\prod_p\Big(1-\frac{|B_p|}{p^2}\Big)\Big(1-\frac1p\Big)^{-g}$, over all primes.
--   4. $\theta(g,Q):=g^2\log 5Q\,\log\log 5Q$.
--
--   These are the local densities and the error scale of the sieve bound for square-rough $g$-tuples (Theorem 8.7).
--
--   **Formalization Note** Under the hypotheses above every bad prime is at most $\max(U,4g^2)$, and $Q$ is the product over the bad primes up to that bound. $\Delta$ is Mathlib's unconditional product over `Nat.Primes`; it is $0$ if a factor vanishes and absolutely convergent otherwise (p.69, Corollary 8.25), so it is the paper's $\Delta$.
-- source:
--   Harvey, Faster enumeration of primes, arXiv:2606.22851 (held version, sha256 7fc13f17…), §8.1, eqs. (8.3)–(8.5), pp.68–69

import Mathlib

set_option autoImplicit false

namespace FasterPrimeEnum

namespace Supplement

/-- **Bad primes** — D. Harvey, *Faster enumeration of primes*, arXiv:2606.22851 (held version,
sha256 7fc13f17…), §8.1, p.69: "We say that a prime p is bad (with respect to the parameters g, U
and u) if any of the following hold: (i) p | U, (ii) p divides some u_i − u_j (for i ≠ j), or
(iii) p ⩽ 4g². Otherwise p is good." -/
def IsBadPrime (U : ℕ) {g : ℕ} (u : Fin g → ℕ) (p : ℕ) : Prop :=
  p ∣ U ∨ (∃ i j : Fin g, i ≠ j ∧ (p : ℤ) ∣ (u i : ℤ) - (u j : ℤ)) ∨ p ≤ 4 * g ^ 2

open Classical in
/-- **`Q(u) := ∏_{p bad} p`** — p.69. For `U ≥ 1` and pairwise distinct `0 ≤ u_i < U`, every bad
prime is at most `max(U, 4g²)` (a prime dividing `U` or a nonzero `u_i − u_j` with `|u_i − u_j| < U`
is at most `U`), so the product runs over the bad primes `p ≤ max(U, 4g²)`. -/
noncomputable def Qbad (U : ℕ) {g : ℕ} (u : Fin g → ℕ) : ℕ :=
  ∏ p ∈ (Finset.range (max U (4 * g ^ 2) + 1)).filter (fun p => p.Prime ∧ IsBadPrime U u p), p

open Classical in
/-- `|B_p|` — eq. (8.3), p.68 and p.69: `B_{p,i} := {k ∈ Z/p²Z : Uk + u_i ≡ 0 (mod p) and
Uk + u_i ≢ 0 (mod p²)}` and `B_p := ⋃_{1⩽i⩽g} B_{p,i} ⊆ Z/p²Z`. The residues `k ∈ Z/p²Z` are
`0, …, p² − 1`; the conditions depend only on `k mod p²`. -/
noncomputable def Bcard (U : ℕ) {g : ℕ} (u : Fin g → ℕ) (p : ℕ) : ℕ :=
  ((Finset.range (p ^ 2)).filter fun k =>
    ∃ i : Fin g, p ∣ U * k + u i ∧ ¬ p ^ 2 ∣ U * k + u i).card

/-- **`Δ(u)`** — eq. (8.4), p.69: "Δ = Δ(u) := ∏_p (1 − |B_p|/p²)(1 − 1/p)^{−g}", the product over
all primes.

**Formalization Note.** The infinite product is Mathlib's unconditional product `∏'` over
`Nat.Primes`. It is a genuine (multipliable) product for every `u` the paper considers: if some
factor vanishes it is `0`, and otherwise the paper shows absolute convergence (p.69, Corollary 8.25;
for good `p` the factor is `1 + O(g²/p²)` by Lemma 8.6). -/
noncomputable def Delta (U : ℕ) {g : ℕ} (u : Fin g → ℕ) : ℝ :=
  ∏' p : Nat.Primes, (1 - (Bcard U u p : ℝ) / ((p : ℝ) ^ 2)) * ((1 - 1 / (p : ℝ))⁻¹) ^ g

/-- **`θ(g, Q) := g² log 5Q log log 5Q`** — eq. (8.5), p.69 (natural logarithms; `log 5Q` is
`log(5Q)`; for `Q ≥ 6` both logarithms are positive). -/
noncomputable def theta (g Q : ℕ) : ℝ :=
  (g : ℝ) ^ 2 * Real.log (5 * Q) * Real.log (Real.log (5 * Q))

end Supplement

end FasterPrimeEnum


