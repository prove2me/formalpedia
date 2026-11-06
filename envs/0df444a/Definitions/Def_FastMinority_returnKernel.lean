-- Prove2me | Definitions.Def_FastMinority_returnKernel
-- name    : FastMinority_returnKernel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:05:18.115536+00:00
-- url     : https://prove2.me/theorems/f7d5bcc6-a5e2-42f6-98eb-58630bbc64ad
-- title:
--   Induced kernel $K(i,j)=\sum_{\ell\ge1}P^\ell(i,j\mid\cdot)$ of the chain observed on $A$
-- statement:
--   For a finite Markov chain with transition matrix $P$ and a set of states $A$, the chain observed only at its successive visits to $A$ has transition probabilities
--   $$
--   K(i,j)=P(i,j)+\sum_{\ell\ge2}P^\ell_A(i,j)=\sum_{\ell\ge1}\Pr_i\big(X_1,\dots,X_{\ell-1}\notin A,\ X_\ell=j\big),\qquad j\in A,
--   $$
--   the probability that the next visit to $A$ after time $0$ is at $j$. With $A=\mathcal C\cup\mathcal H^+$ this is the kernel of the source's chain $\mathcal R$.
--
--   **Formalization Note** The series has nonnegative terms and is taken in $[0,\infty]$, so it is never a default value; each term is a real taboo probability mapped to $[0,\infty]$.
-- source:
--   Berenbrink–Giriyan–Götte–Richa, Fast Minority Dynamics with Θ(log² n)-Size Samples, STOC 2027 submission (manuscript sha256 841077e0…abcdd1), Section 3, p.7 (PDF p.9)

import Mathlib
import Definitions.Def_FastMinority_firstEntryAt

set_option autoImplicit false

open Classical

namespace FastMinority

/-- The transition kernel of the chain **observed only at its visits to `A`** (Berenbrink–Giriyan–Götte–Richa, *Fast Minority Dynamics with Θ(log² n)-Size Samples*, STOC 2027 submission manuscript (sha256 841077e0…abcdd1), §3, p.7 =
PDF p.9: "`K(i, j) = P(i, j) + ∑_{ℓ=2}^∞ P^ℓ(i, j | 𝓛 ∪ 𝓤)`"):
`returnKernel P A i j = ∑_{ℓ ≥ 1} Pr_i(X_1, …, X_{ℓ−1} ∉ A, X_ℓ = j)`, the probability that the
next visit to `A` after time `0` is at `j`, when `j ∈ A`.

**Formalization Note** The series is a sum of nonnegative terms, taken in `ℝ≥0∞` so that it is never
a junk value (each term is `ENNReal.ofReal` of `firstEntryAt`). With `A = 𝓒 ∪ 𝓗⁺` the intermediate
states are those outside `𝓒 ∪ 𝓗⁺`, i.e. `𝓛 ∪ (𝓤 \ 𝓗)`: the paper's `𝓛 ∪ [R′, ⌊n/2⌋]`, not
`𝓛 ∪ [R, ⌊n/2⌋]`, because `[R, ⌊n/2⌋]` overlaps `𝓗` for large `n` (`R` itself is good). -/
noncomputable def returnKernel {α : Type*} [Fintype α] (P : α → α → ℝ) (A : Set α) (i j : α) :
    ENNReal :=
  ∑' ℓ : ℕ, ENNReal.ofReal (firstEntryAt P A (ℓ + 1) i j)

end FastMinority


