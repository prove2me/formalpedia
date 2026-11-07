-- Prove2me | Definitions.Def_MinBisectFPT_expN
-- name    : MinBisectFPT_expN
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:52:40.874233+00:00
-- url     : https://prove2.me/theorems/9ffa4b7a-e8d2-4c7d-a69f-8d57966ec4f4
-- title:
--   Finite series $\exp$ and $\log$ on truncated polynomials
-- statement:
--   For $f$ in a commutative $\mathbb{Q}$-algebra and $N\ge0$,
--   $$\exp(f)=\sum_{r=0}^{N}\frac{f^r}{r!},\qquad \log(1+f)=\sum_{r=1}^{N}(-1)^{r+1}\frac{f^r}{r}.$$
--   These are the finite series the paper uses throughout, on elements with $f^{N+1}=0$; the paper never applies them to numbers.
--
--   **Formalization Note** The logarithm takes $f$ as its argument, not $1+f$, so $\log F(W)$ is written with $f=F(W)-1$.
-- source:
--   Anand, Kipouridis, Węgrzycki, Counting over Unbreakable Decompositions, STOC 2027 submission (manuscript sha256 8db80a52…), §3, p.10

import Mathlib

namespace MinBisectFPT

variable {A : Type} [CommRing A] [Algebra ℚ A]

/-- **The finite exponential series** `exp(f) = Σ_{r=0}^{N} f^r/r!`. Anand, Kipouridis, Węgrzycki,
*Counting over Unbreakable Decompositions*, STOC 2027 submission (manuscript sha256 8db80a52…), §3,
p.10. -/
noncomputable def expN (N : ℕ) (f : A) : A :=
  ∑ r ∈ Finset.range (N + 1), ((r.factorial : ℚ)⁻¹) • f ^ r

/-- **The finite logarithm series** `log(1 + f) = Σ_{r=1}^{N} (−1)^{r+1} f^r/r` (p.10).

**Formalization Note** `logN N f` is `log(1 + f)`: its argument is `f`, not `1 + f`. -/
noncomputable def logN (N : ℕ) (f : A) : A :=
  ∑ r ∈ Finset.Icc 1 N, ((-1 : ℚ) ^ (r + 1) / (r : ℚ)) • f ^ r

end MinBisectFPT


