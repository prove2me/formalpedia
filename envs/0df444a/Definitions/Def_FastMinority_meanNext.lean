-- Prove2me | Definitions.Def_FastMinority_meanNext
-- name    : FastMinority_meanNext
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:04:33.255249+00:00
-- url     : https://prove2.me/theorems/ee1f3979-2cd0-4167-9657-bb757f900f92
-- title:
--   One-step mean $\mathbb E[X_{t+1}\mid X_t=x]$ of the minority size
-- statement:
--   Let $X=(X_t)_{t\ge0}$ be the minority-size chain of MINORITY with $n$ agents and sample size $k$: $X_t\in\{0,\dots,\lfloor n/2\rfloor\}$ is the number of agents holding the minority opinion after $t$ rounds, and given $X_t=x$ the next state is $\min(Y,n-Y)$ with $Y\sim\mathrm{Bin}(n,r(x/n))$. The **one-step mean** is
--   $$
--   m(x)=\mathbb E[X_{t+1}\mid X_t=x]=\sum_{s=0}^{n} s\,P(x,s),
--   $$
--   where $P(x,s)$ is the transition probability of $X$.
--
--   It defines the good states (3.1).
--
--   **Formalization Note** States are counts in $\{0,\dots,n\}$; $P$ is the published kernel `MinorityDynamics.actualKernel n k`, the folded law of $\mathrm{Bin}(n,p_{\mathrm{adopt}}(x/n))$, which equals the folded law of $\mathrm{Bin}(n,r(x/n))$ because folding identifies $Y$ and $n-Y$.
-- source:
--   Berenbrink–Giriyan–Götte–Richa, Fast Minority Dynamics with Θ(log² n)-Size Samples, STOC 2027 submission (manuscript sha256 841077e0…abcdd1), Section 2.1, pp.4–5 (PDF pp.6–7), and Eq. (3.1), p.6 (PDF p.8)

import Mathlib
import Definitions.Def_MinorityDynamics_Chain

set_option autoImplicit false

open Classical

namespace FastMinority

/-- The **one-step mean** `E[X_{t+1} | X_t = x]` of the minority-size chain `X` (Berenbrink–Giriyan–Götte–Richa, *Fast Minority Dynamics with Θ(log² n)-Size Samples*, STOC 2027 submission manuscript (sha256 841077e0…abcdd1), §2.1,
pp.4–5 = PDF pp.6–7, and (3.1), p.6 = PDF p.8): the expectation of the next minority size under the
transition probabilities `P(x, ·)`, here the published `MinorityDynamics.actualKernel n k x`.

**Formalization Note** States are minority counts in `Fin (n + 1)`. `actualKernel n k x` is the law of
`min(Z, n − Z)` for `Z ∼ Bin(n, pAdopt k (x/n))`; since folding identifies `Z` and `n − Z`, this is the
paper's law of `min(Y, n − Y)`, `Y ∼ Bin(n, r(x/n))`. -/
noncomputable def meanNext (n k : ℕ) (x : Fin (n + 1)) : ℝ :=
  ∑ s : Fin (n + 1), ((s : ℕ) : ℝ) * MinorityDynamics.actualKernel n k x s

end FastMinority


