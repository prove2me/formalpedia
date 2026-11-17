-- Prove2me | Definitions.Def_MultiCollQ_Supplement_FTrunc
-- name    : MultiCollQ_Supplement_FTrunc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:58:13.674845+00:00
-- url     : https://prove2.me/theorems/a370a1f6-1b51-45a4-9d13-6cb3c13ce8c7
-- title:
--   Truncated-trajectory bound $F_{j,m}(s,L)$ of (4.17)
-- statement:
--   Fix the bucket bound $k$, the domain size $N$ and a query horizon $1\le T<N$, and put $d=N-T$. With $c_j=\sqrt{8(k-j+1)}$ (for every $j\ge1$) and the falling factorial $(L)_m=L(L-1)\cdots(L-m+1)$, define for integers $j,m,s,L\ge0$
--
--   $$
--   F_{j,m}(s,L)=\begin{cases}1, & m=0,\\[2pt] \dbinom{s}{m}\Bigl(\dfrac{c_j}{\sqrt d}\Bigr)^{m}\sqrt{(L)_m}, & 1\le m\le\min\{s,L\},\\[4pt] 0, & m>\min\{s,L\}.\end{cases}
--   $$
--
--   The denominator $d=N-T$ stays fixed as $s$ ranges over $0\le s\le T$. These are the bounds on the truncated database amplitudes in the simultaneous-truncation argument; Theorem 4.5 bounds the target amplitude by a sum of them.
--
--   **Formalization Note** The function carries $k$, $N$ and $T$ as explicit arguments, since $c_j$ depends on $k$ and $d$ on $N,T$; $d$ is computed in $\mathbb R$.
-- source:
--   Peng, Hou, Dong, Quantum multi-collision lower bounds for arbitrary bounded types, manuscript (Oct. 2026; STOC 2027 submission, sha256 e20a0870b16226a4c1b2ff8ccbc19ad9605f91268e96586242ff551b9f17fdf1), §4.4, (4.17), p.39

import Mathlib
import Definitions.Def_MultiCollQ_Aconst

namespace MultiCollQ.Supplement

/-- The truncated-trajectory bound `F_{j,m}(s, L)` of (4.17) (Peng, Hou, Dong, *Quantum
multi-collision lower bounds for arbitrary bounded types*, manuscript (Oct. 2026), §4.4, (4.17),
p.39): with the query horizon `T` fixed and `d = N − T`,
`F_{j,m}(s, L) = 1` if `m = 0`;
`F_{j,m}(s, L) = binom(s, m) (c_j/√d)^m √((L)_m)` if `1 ≤ m ≤ min{s, L}`;
`F_{j,m}(s, L) = 0` if `m > min{s, L}`,
where `(L)_m = L(L − 1)⋯(L − m + 1)` is the falling factorial and `c_j = √(8(k − j + 1))`
(extended to `j = 1`, p.35).

**Formalization Note.** The arguments are `k` (through `c_j = MultiCollQ.cConst k j`), `N` and `T`
(through `d = N − T`, computed in `ℝ`), then `j, m, s, L`. `(L)_m` is `Nat.descFactorial L m`.
Every use has `1 ≤ T < N`, so `d > 0`. -/
noncomputable def FTrunc (k N T j m s L : ℕ) : ℝ :=
  if m = 0 then 1
  else if m ≤ min s L then
    (s.choose m : ℝ) * (cConst k j / Real.sqrt ((N : ℝ) - T)) ^ m * Real.sqrt (L.descFactorial m)
  else 0

end MultiCollQ.Supplement


