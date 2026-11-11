-- Prove2me | Definitions.Def_AcceptSubcube_ratio11
-- name    : AcceptSubcube_ratio11
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:58:38.193224+00:00
-- url     : https://prove2.me/theorems/a5211c94-fc81-44cb-afc2-9efea77ca4b8
-- title:
--   The approximation guarantees of Theorem 1.1 and of (22)
-- statement:
--   For $1\le h\le k-1$ and $\Pi=\binom{n}{k-h-1}$, the guarantee of Theorem 1.1 is the bound
--   $$C_{\mathcal I}(Y)\le\begin{cases}A_k\,\mathrm{OPT},&h=1,\\ A_k\sqrt{\log(2+\mathrm{OPT}/\Pi)}\,\mathrm{OPT},&h=2,\\ A_k\big(n/\log(n+2)\big)^{h-2}\,\mathrm{OPT},&h\ge3.\end{cases}$$
--   For $0\le t\le k-2$, $\ell=k-t$ and $\Pi_t=\binom nt$, the ratio of (22) is $A_k$ ($\ell=2$), $A_k\sqrt{\log(2+B/\Pi_t)}$ ($\ell=3$), $A_k(n/\log(n+2))^{\ell-3}$ ($\ell\ge4$).
--
--   **Formalization Note** Natural logarithms (p.9). When $n<k-h-1$ there are no constraints, $\mathrm{OPT}=0$ and the bound is $0$ in every case.
-- source:
--   Cai, Jiang, Liu, Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs, STOC 2027 submission (manuscript sha256 66626baf…), Theorem 1.1, p.4; Theorem 5.1, (22), p.25

import Mathlib
import Definitions.Def_AcceptSubcube_GInst
import Definitions.Def_AcceptSubcube_cost

namespace AcceptSubcube

/-- **The guarantee of Theorem 1.1**, as a bound on the cost.

Cai, Jiang, Liu, *Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs*,
STOC 2027 submission (manuscript sha256 66626baf…), Theorem 1.1, p.4:
`C_I(Y) ≤ A_k OPT` (h = 1), `A_k √log(2 + OPT/Π) OPT` (h = 2),
`A_k (n/log(n + 2))^{h−2} OPT` (h ≥ 3), with `Π = (n choose k−h−1)`.

**Formalization Note.** Natural logarithms (p.9). `Π ≥ 1` for `h ≤ k − 1` and `n ≥ k − h − 1`; for
smaller `n` (no constraints, `OPT = 0`) the bound is `0` in every case. -/
noncomputable def ratio11 (k h : ℕ) (A : ℝ) (I : GInst) : ℝ :=
  if h = 1 then A * (OPT I : ℝ)
  else if h = 2 then
    A * Real.sqrt (Real.log (2 + (OPT I : ℝ) / (I.n.choose (k - h - 1) : ℝ))) * (OPT I : ℝ)
  else A * ((I.n : ℝ) / Real.log ((I.n : ℝ) + 2)) ^ (h - 2) * (OPT I : ℝ)

/-- **The ratio of (22)** (Theorem 5.1, p.25): `A_k` (ℓ = 2), `A_k √log(2 + B/Π_t)` (ℓ = 3),
`A_k (n/log(n + 2))^{ℓ−3}` (ℓ ≥ 4), with `ℓ = k − t`, `Π_t = (n choose t)`, `B = OPT`.

Cai, Jiang, Liu, STOC 2027 submission (manuscript sha256 66626baf…), Theorem 5.1, (22), p.25. -/
noncomputable def ratio51 (k t : ℕ) (A : ℝ) (I : GInst) : ℝ :=
  if k - t = 2 then A
  else if k - t = 3 then
    A * Real.sqrt (Real.log (2 + (OPT I : ℝ) / (I.n.choose t : ℝ)))
  else A * ((I.n : ℝ) / Real.log ((I.n : ℝ) + 2)) ^ (k - t - 3)

end AcceptSubcube


