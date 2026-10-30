-- Prove2me | Definitions.Def_NestedLogitNBR_factor6
-- name    : NestedLogitNBR_factor6
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:39:47.52828+00:00
-- url     : https://prove2.me/theorems/33547b92-822a-4a5c-8002-81cce3996c0b
-- title:
--   Performance factor $\alpha$ of the nested-by-revenue assortments, $\max\{1,(6)\}$
-- statement:
--   The performance guarantee of the nested-by-revenue assortments (eq. (6), p. 19) is
--
--   $$
--   \alpha=\max\Big\{1,\ \max_{i\in M,\ j=2,\dots,n}\Big\{\frac{R_i(N_{i,j-1})}{R_i(N_{ij})}\wedge\frac{R_i(N_{ij})}{R_i(N_{i,j-1})}\frac{V_i(N_{ij})^{\gamma_i}}{V_i(N_{i,j-1})^{\gamma_i}}\Big\}\Big\}.
--   $$
--
--   Theorem 7 shows that scaling the optimal solution of the nested-by-revenue linear program (4) by $\alpha$ gives a feasible solution of the full program (3), so that the best combination of nested-by-revenue assortments loses at most a factor $\alpha$ of the optimal expected revenue.
--
--   **Formalization Note** The paper's $\alpha$ is the inner maximum (6). Where every term of (6) is defined and some $\gamma_i>1$ (the standing assumption of Section 4), Lemma 14 gives (6) $\ge1$, so the outer maximum with $1$ changes nothing. On data with a $0/0$ term (zero weights or zero revenues, allowed by the model) the paper's expression is undefined and the literal Lean value of the inner maximum can be below $1$, where Theorem 7 fails; the $1$ is needed there. For $n\le1$ the index range is empty and $\alpha=1$.
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript dated June 18, 2013 (published as Operations Research 62(2), 2014, doi:10.1287/opre.2014.1256), eq. (6), p. 19; Theorem 7, p. 21 (α); Lemma 14, p. 43

import Mathlib
import Definitions.Def_NestedLogitNBR_factor6Term

namespace NestedLogitNBR

/-- **The performance factor `α` of nested-by-revenue assortments, read as `max{1, (6)}`.**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript dated June 18, 2013 (published as Operations Research 62(2), 2014,
doi:10.1287/opre.2014.1256), eq. (6), p. 19: the nested-by-revenue assortments give a solution "whose expected revenue
deviates from the optimal expected revenue by no more than a factor of
`max_{i∈M, j=2,…,n} { R_i(N_{i,j−1})/R_i(N_ij) ∧ (R_i(N_ij)/R_i(N_{i,j−1}))
(V_i(N_ij)^{γ_i}/V_i(N_{i,j−1})^{γ_i}) }`"; Theorem 7 (p. 21) uses "`α` to denote the
expression in (6)".

`factor6 r v γ = max {1, factor6Term r v γ i j : i ∈ M, j = 2, …, n}`.

**Formalization Note.** The maximum is a `Finset.fold max` with seed `1`, so
`factor6 = max{1, (6)}`. Where every term of (6) is defined and some `γ_i > 1` (the standing
assumption of Section 4, p. 16), Lemma 14 (p. 43) gives `(6) ≥ 1` and this is the paper's
value. On data where some term of (6) is `0/0` (zero weights or zero revenues, which the model
allows, p. 7) the paper's expression is undefined; the seed `1` is then needed, since the
literal Lean value of the maximum without it can be `< 1` and Theorem 7 then fails. For
`n ≤ 1` the index range is empty and `factor6 = 1`. -/
noncomputable def factor6 {m n : ℕ} (r v : Fin m → Fin n → ℝ) (γ : Fin m → ℝ) : ℝ :=
  ((Finset.univ : Finset (Fin m)) ×ˢ Finset.Icc 2 n).fold max 1
    (fun p => factor6Term r v γ p.1 p.2)

end NestedLogitNBR


