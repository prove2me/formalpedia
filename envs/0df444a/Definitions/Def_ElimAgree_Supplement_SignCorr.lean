-- Prove2me | Definitions.Def_ElimAgree_Supplement_SignCorr
-- name    : ElimAgree_Supplement_SignCorr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:34:09.506679+00:00
-- url     : https://prove2.me/theorems/18515c39-b938-4e30-ab00-fbe118308c81
-- title:
--   Uniform sign correlation and $\beta_k(\delta)$
-- statement:
--   For $f:\mathcal X\times\mathcal Y\to\{0,1\}$ write $\chi=2f-1\in\{-1,1\}$. $f$ has **uniform sign correlation** $\delta>0$ if some distribution on pairs of functions $a:\mathcal X\to\{-1,1\}$, $b:\mathcal Y\to\{-1,1\}$ satisfies
--
--   $$\chi(x,y)\,\mathbb E[a(x)b(y)]\ge\delta\qquad\text{for every input }(x,y).\tag{3.4}$$
--
--   For $k\in\mathbb N$ and $Z\sim\mathrm{Bin}\big(k,\tfrac{1+\delta}2\big)$,
--
--   $$\beta_k(\delta)=2\Pr\big[Z<\tfrac k2\big]+\Pr\big[Z=\tfrac k2\big]=\sum_{j=0}^k w_j\binom kj p^j(1-p)^{k-j},\qquad p=\tfrac{1+\delta}2,$$
--
--   with $w_j=2$ for $j<k/2$, $w_{k/2}=1$, and $w_j=0$ otherwise.
--
--   These are the hypothesis and the error bound of the one-majority-bit protocol (Theorem 3.10).
--
--   **Formalization Note** Sign-valued functions are `Bool`-valued functions read through `sgn` (`true` ↦ $1$); the distribution is a law on the finite set of pairs $(a,b)$. $\beta_k$ is the explicit binomial sum, defined for every real $\delta$.
-- source:
--   Ben Daniel, Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination, manuscript (STOC 2027 submission; held version sha256 eea57875…), (3.4) and Theorem 3.10, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_ElimAgree_IsLaw

namespace ElimAgree

namespace Supplement

/-- A sign in `{−1, 1}` from a bit: `true ↦ 1`, `false ↦ −1`. For a Boolean `f`,
`χ = 2f − 1 = sgn ∘ f` (Ben Daniel, *Can Many Instances Be Cheaper Than One? The Price of
Agreement in Elimination*, manuscript, STOC 2027 submission, §3.5, p.11). -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

/-- Uniform sign correlation (3.4), p.11: `f` has uniform sign correlation `δ > 0` if some
distribution `w` on pairs of functions `a : X → {−1, 1}`, `b : Y → {−1, 1}` satisfies
`χ(x, y) E[a(x) b(y)] ≥ δ` for every input `(x, y)`.

**Formalization Note.** Sign-valued functions are `Bool`-valued functions read through `sgn`; the
distribution is a law (nonnegative weights summing to `1`) on the finite set of such pairs. -/
def HasUniformSignCorr {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (f : X → Y → Bool) (δ : ℝ) : Prop :=
  0 < δ ∧ ∃ w : (X → Bool) × (Y → Bool) → ℝ, IsLaw w ∧
    ∀ x y, δ ≤ sgn (f x y) * ∑ ab, w ab * (sgn (ab.1 x) * sgn (ab.2 y))

/-- `β_k(δ) = 2 Pr[Z < k/2] + Pr[Z = k/2]` with `Z ∼ Bin(k, (1 + δ)/2)` (Theorem 3.10, p.11),
written as the binomial sum: the term `j` has weight `2` if `j < k/2`, `1` if `j = k/2`, and `0`
otherwise. -/
noncomputable def betaK (k : ℕ) (δ : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1),
    (if 2 * j < k then (2 : ℝ) else if 2 * j = k then 1 else 0) *
      ((k.choose j : ℝ) * ((1 + δ) / 2) ^ j * (1 - (1 + δ) / 2) ^ (k - j))

end Supplement

end ElimAgree


