-- Prove2me | Definitions.Def_PermLimits_Shared_StepLimit
-- name    : PermLimits_Shared_StepLimit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T13:56:49.886637+00:00
-- url     : https://prove2.me/theorems/011e8fa5-34ec-47c3-b1f2-f43f9a6fa2d5
-- title:
--   The limit permutation $Z_\sigma$ of a permutation $\sigma$
-- statement:
--   Let $\sigma\in S_n$. The random point $(X_\sigma,Y_\sigma)$ has joint density
--   $$f_\sigma(x,y)=n\cdot\mathbf 1\big[\sigma(\lceil n x\rceil)=\lceil n y\rceil\big],$$
--   and the limit permutation of $\sigma$ is
--   $$Z_\sigma(x,y)=\int_0^y f_\sigma(x,\tilde y)\,d\tilde y .$$
--   Explicitly, for $x\in\big(\tfrac{i-1}{n},\tfrac in\big]$ the function $Z_\sigma(x,\cdot)$ is the cdf of the uniform distribution on $\big[\tfrac{\sigma(i)-1}{n},\tfrac{\sigma(i)}{n}\big]$, i.e. $Z_\sigma(x,y)=\min\{1,\max\{0,\,ny-(\sigma(i)-1)\}\}$.
--
--   $Z_\sigma$ is the "picture" of the permutation matrix of $\sigma$ as a limit permutation. It lets permutations and limit permutations be compared, through $t(\tau,Z_\sigma)\approx t(\tau,\sigma)$ and the rectangular distance.
--
--   **Formalization Note** The integral is written in the closed form above, with 0-based indices. At $x=0$ the source's formula refers to $\sigma(0)$, which is undefined; the row index is taken to be the first row there. This changes $Z_\sigma$ only on the null set $\{x=0\}$ and makes $Z_\sigma(x,\cdot)$ a cdf for every $x$, as membership in $\mathcal Z$ requires. For the empty permutation ($n=0$, not a permutation in the source) the uniform limit permutation $Z_u(x,y)=y$ is returned.
--
--   This definition is shared by both missions of this series: mission 1 (`01-limit-existence`, existence and uniqueness of the limit permutation) (Lemma 3.5, p. 11; Lemma 4.2, p. 13; Eq. (49), p. 17) and mission 2 (`02-cauchy-rectangular`, convergent sequences are Cauchy for the rectangular distance) (Lemma 3.5, p. 11; the rectangular distance of permutations, Sect. 4.1, pp. 12–13; Eq. (49), p. 17).
-- source:
--   Hoppen, Kohayakawa, Moreira, Ráth, Sampaio, Limits of permutation sequences, arXiv:1103.5844v2, https://arxiv.org/abs/1103.5844v2, p. 11, Definition 3.4 (Eqs. (25)–(26))

import Mathlib

/-!
# The limit permutation `Z_σ` of a permutation

C. Hoppen, Y. Kohayakawa, C. G. Moreira, B. Ráth, R. M. Sampaio, *Limits of permutation
sequences*, arXiv:1103.5844v2, p. 11, Definition 3.4, Eqs. (25)–(26).
-/

namespace PermLimits.Shared

open unitInterval

/-- **The limit permutation `Z_σ`** (Hoppen et al., arXiv:1103.5844v2, Definition 3.4,
Eqs. (25)–(26), p. 11). For `σ ∈ S_n`, `(X_σ, Y_σ)` has density
`f_σ(x, y) = n · 1[σ(⌈n x⌉) = ⌈n y⌉]` and `Z_σ(x, y) = ∫₀^y f_σ(x, ỹ) dỹ`.

**Formalization Note.** The integral (26) is written in closed form. With 0-based indices
(`σ : Equiv.Perm (Fin n)`), a point `x ∈ ((i-1)/n, i/n]` lies in row `i - 1 = ⌈n x⌉ - 1` and
`Z_σ(x, y) = min(1, max(0, n y - j))` with `j = σ(⌈n x⌉ - 1)` (as a natural number): the uniform
cdf on `[j/n, (j+1)/n]`. At `x = 0`, where `⌈n x⌉ = 0` and the paper's density refers to the
undefined `σ(0)`, the natural-number subtraction gives row `0`, so `Z_σ(0, ·)` is the cdf of row
`0`; this changes `Z_σ` only on the null set `{x = 0}` and makes `Z_σ(x, ·)` a cdf for every `x`,
as Definition 1.3(a) requires. The argument is named `π` because `σ` is reserved notation once
`unitInterval` is opened. The `min … (n - 1)` never changes the index for `x ∈ [0, 1]`
(`⌈n x⌉ ≤ n`); it only certifies the bound `< n`. For the empty permutation (`n = 0`, not a
permutation in the paper, which has `n ≥ 1`) the uniform limit permutation `Z_u(x, y) = y` is
returned. -/
noncomputable def stepLimit {n : ℕ} (π : Equiv.Perm (Fin n)) (x y : I) : ℝ :=
  if h : 0 < n then
    min 1 (max 0 ((n : ℝ) * (y : ℝ) -
      ((π ⟨min (⌈(n : ℝ) * (x : ℝ)⌉₊ - 1) (n - 1), by omega⟩ : Fin n) : ℕ)))
  else (y : ℝ)

end PermLimits.Shared


