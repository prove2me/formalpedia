-- Prove2me | Definitions.Def_SamplingAC0_Supplement_slice
-- name    : SamplingAC0_Supplement_slice
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:38:31.490201+00:00
-- url     : https://prove2.me/theorems/9fc6f80f-f10d-4e2d-927f-098655ddd3ba
-- title:
--   Hamming slice distribution $D\sim\binom{[n]}{k}$
-- statement:
--   For $x\in\{0,1\}^n$ let $|x|$ be its **Hamming weight**, the number of coordinates equal to $1$. For $0\le k\le n$ the **Hamming slice** is the set
--   $$\binom{[n]}{k}=\{x\in\{0,1\}^n : |x|=k\},$$
--   the $k$-subsets of $[n]$ written as indicator strings, and $D\sim\binom{[n]}{k}$ is the uniform distribution on it, so $D(x)=\binom nk^{-1}$ for every $x$ of weight $k$.
--
--   This is the target distribution of Theorem 6, which shows that non-adaptive cell-probe samplers cannot approximate it.
--
--   **Formalization Note** For $k>n$ the slice is empty and has no uniform distribution; the definition then returns the point mass at the all-zero string. Theorem 6 assumes $0.1n\le k\le 0.9n$, so the slice is nonempty there.
-- source:
--   Riazanov–Viola, Sampling Tools and the Power of AC0, STOC 2027 submission (manuscript sha256 99c33d30…), Theorem 6 p.4; §6 p.17 (supp(D) = ([n] choose k))

import Mathlib
set_option autoImplicit false

namespace SamplingAC0.Supplement

/-- The Hamming weight `|x|` of `x ∈ {0,1}^n`: the number of coordinates equal to `1` (`true`). -/
def weight {n : ℕ} (x : Fin n → Bool) : ℕ :=
  (Finset.univ.filter fun j => x j = true).card

/-- The Hamming slice `([n] choose k)` as a set of strings: the `x ∈ {0,1}^n` of weight `k`. -/
def weightSet (n k : ℕ) : Finset (Fin n → Bool) :=
  Finset.univ.filter fun x => weight x = k

/-- **The Hamming-slice distribution `D ∼ ([n] choose k)`.** Riazanov–Viola, *Sampling Tools and the
Power of AC0*, STOC 2027 submission (manuscript sha256 99c33d30…), Theorem 6, p.4 ("Let
D ∼ ([n] choose k)"), and p.17 ("supp(D) = ([n] choose k)"): the uniform distribution on the
`k`-subsets of `[n]`, each written as its indicator string in `{0,1}^n`, i.e. the uniform
distribution on the strings of Hamming weight exactly `k`.

**Formalization Note.** For `k > n` the slice is empty and there is no uniform distribution on it;
the definition then returns the point mass at the all-zero string. Every statement using it assumes
`k ≤ n` (Theorem 6 assumes `0.1n ≤ k ≤ 0.9n`), where the slice is nonempty. -/
noncomputable def slice (n k : ℕ) : PMF (Fin n → Bool) :=
  if h : (weightSet n k).Nonempty then PMF.uniformOfFinset (weightSet n k) h
  else PMF.pure fun _ => false

end SamplingAC0.Supplement


