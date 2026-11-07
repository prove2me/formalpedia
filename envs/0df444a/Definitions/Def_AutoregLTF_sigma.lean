-- Prove2me | Definitions.Def_AutoregLTF_sigma
-- name    : AutoregLTF_sigma
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:55:08.632585+00:00
-- url     : https://prove2.me/theorems/1093ce76-d983-400e-8b44-3aa248bfda3f
-- title:
--   The extended history $\widehat E$, the position set $\Pi$, and the scores $\sigma_r$ of (24)
-- statement:
--   Fix $i\in[m]$ and $t\ge0$. Let $\widehat E=(0,E^t_{\theta,i},E^{t+1}_{\theta,i})$, indexed by $-p-1,\dots,p-1$, and let
--
--   $$\Pi=\{0\}\cup\{\pi(\mathrm{row},j):j\in[m]\}\cup\bigcup_b\{\pi(b),\pi(b)+1\},$$
--
--   $b$ ranging over test, $(\mathrm{out},j)$ for $j\in[m]$ and $(\mathrm{ptr},j)$ for $j\in[m+1]$. For $0\le r<p$ the score is
--
--   $$\sigma_r=-B+\sum_{\ell=1}^{p+1}a_\ell\,\widehat E_{r-\ell}\qquad(24)$$
--
--   with $B$ and $a$ of the proof of Lemma 2.
--
--   **Formalization Note** `Ehat m θ i t k` is $\widehat E_k$ for integer $k$, `false` outside $[-p-1,p-1]$, where (24) never reads. `InPi m r` is membership in $\Pi$, and `sigma m θ i t r` is $\sigma_r$ with `Bconst m` and `aCoef m θ`.
-- source:
--   Doron-Arad, Mehalel, Mossel, On the VC Dimension of Autoregressive Linear Threshold Functions, arXiv:2610.36970 (version of 2026-11-02, sha256 e3428ab7…91c9e), proof of Lemma 2, Ê, Π and (24), p.9

import Mathlib
import Definitions.Def_AutoregLTF_coef

namespace AutoregLTF

/-!
# The extended history `Ê`, the position set `Π`, and the scores `σ_r` of (24)

I. Doron-Arad, I. Mehalel, E. Mossel, *On the VC Dimension of Autoregressive Linear Threshold
Functions*, arXiv:2610.36970 (version of 2026-11-02, sha256 e3428ab7…91c9e), proof of Lemma 2, p.9.

"Fix `i ∈ [m]` and `t ≥ 0`. Let `Ê = (0, E^t_{θ,i}, E^{t+1}_{θ,i})`, indexed by `−p − 1, …, p − 1`,
and define the set of positions specified in (15) by
`Π = {0} ∪ {π(row, j) : j ∈ [m]} ∪ ⋃_b {π(b), π(b) + 1}`", `b` ranging over `test`, `(out, j)` for
`j ∈ [m]` and `(ptr, j)` for `j ∈ [m + 1]`. For `0 ≤ r < p`,
`σ_r = −B + ∑_{ℓ=1}^{p+1} a_ℓ Ê_{r−ℓ}` (24).

**Formalization Note.**
* `Ehat m θ i t k` is `Ê_k` for `k ∈ ℤ`: `0` at `k = −p − 1`, `E^t_{θ,i,k+p}` for `−p ≤ k < 0`,
  `E^{t+1}_{θ,i,k}` for `0 ≤ k < p`; it is `false` below `−p − 1` and at `k ≥ p` (outside the paper's
  index range; (24) never reads there).
* `σ_r` uses the specific `B = Bconst m` and `a = aCoef m θ` of the proof of Lemma 2.
-/

/-- `Ê = (0, E^t_{θ,i}, E^{t+1}_{θ,i})`, indexed by `−p − 1, …, p − 1`. -/
def Ehat (m : ℕ) (θ : ℕ → ℤ) (i t : ℕ) (k : ℤ) : Bool :=
  if k < -(p m : ℤ) then false
  else if k < 0 then E m θ i t (k + p m).toNat
  else E m θ i (t + 1) k.toNat

/-- Membership in the position set `Π` of p.9. -/
def InPi (m : ℕ) (r : ℕ) : Prop :=
  r = 0 ∨ (∃ j ∈ Finset.Icc 1 m, r = piRow m j) ∨
    (r = piTest m ∨ r = piTest m + 1) ∨
    (∃ j ∈ Finset.Icc 1 m, r = piOut m j ∨ r = piOut m j + 1) ∨
    (∃ j ∈ Finset.Icc 1 (m + 1), r = piPtr m j ∨ r = piPtr m j + 1)

/-- The score `σ_r = −B + ∑_{ℓ=1}^{p+1} a_ℓ Ê_{r−ℓ}` of (24). -/
def sigma (m : ℕ) (θ : ℕ → ℤ) (i t r : ℕ) : ℤ :=
  -Bconst m + ∑ ℓ ∈ Finset.Icc 1 (p m + 1),
    aCoef m θ ℓ * ((Ehat m θ i t ((r : ℤ) - ℓ)).toNat : ℤ)

end AutoregLTF


