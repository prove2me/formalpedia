-- Prove2me | Definitions.Def_GeoSemialgCSP_jWeight
-- name    : GeoSemialgCSP_jWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:48:26.839472+00:00
-- url     : https://prove2.me/theorems/fe2581b3-a9a1-4e16-88c6-8f88d15a50a3
-- title:
--   The randomly embedded instance $J_R$
-- statement:
--   Let $L$ be a random map from the leaves of $T_m$ to $[M]$ and $R\ge1$. Take independent copies $L^{(1)},\dots,L^{(R)}$ of $L$ and set $\Lambda(a)=(L^{(1)}(a),\dots,L^{(R)}(a))\in[M]^R$. Independently choose one constraint $(a_1,\dots,a_k)$ of the multiscale template $\tilde I$ and output the $k\times R$ matrix with rows $\Lambda(a_1),\dots,\Lambda(a_k)$. The instance $J_R$ gives each $k$-tuple $(Z_1,\dots,Z_k)$ of variables in $[M]^R$ the probability that it is output.
--
--   All columns use the same base constraint; given it, the columns are independent.
--
--   **Formalization Note** Columns are indexed $0,\dots,R-1$ (the paper's $1,\dots,R$).
-- source:
--   Arvanitakis, Chatziafratis, Makarychev, Hardness of Approximation for Semialgebraic CSPs, manuscript (STOC 2027 submission, held version sha256 ee702c42…), §4.2, p.11 (PDF p.12)

import Mathlib
import Definitions.Def_GeoSemialgCSP_Wd
import Definitions.Def_GeoSemialgCSP_msWeight

namespace GeoSemialgCSP

open Classical in
/-- **The randomly embedded instance `J_R`.** Arvanitakis, Chatziafratis, Makarychev, *Hardness of Approximation for Semialgebraic CSPs*,
manuscript (STOC 2027 submission, held version sha256 ee702c42…), §4.2, printed p.11 (PDF p.12):
choose independent copies `L^{(1)}, …, L^{(R)}` of `L_{m,M}`, put
`Λ(a) = (L^{(1)}(a), …, L^{(R)}(a))`, independently choose one constraint `(a₁, …, a_k)` of `Ĩ`,
and output `(Λ(a₁), …, Λ(a_k))`. The weight of a `k`-tuple `Z` of variables in `[M]^R` is the
probability that it is output.

**Formalization Note.** `Z j r` is the entry in row `j`, column `r`. The sum runs over base
constraints `l` (weighted by `msWeight`) and over the `R` independent maps `g r` (weighted by the
product of their probabilities). Column indices are `Fin R` (the paper's `1, …, R`). -/
noncomputable def jWeight {k h H : ℕ} (L : PMF ((Fin h → Fin k) → Wd k H)) (R : ℕ)
    (Z : Fin k → (Fin R → Wd k H)) : ℝ :=
  ∑ l : Fin k → (Fin h → Fin k), msWeight h l *
    ∑ g : Fin R → ((Fin h → Fin k) → Wd k H),
      (∏ r, (L (g r)).toReal) * (if ∀ j r, Z j r = g r (l j) then 1 else 0)

end GeoSemialgCSP


