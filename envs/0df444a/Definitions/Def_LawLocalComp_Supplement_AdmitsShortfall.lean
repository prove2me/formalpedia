-- Prove2me | Definitions.Def_LawLocalComp_Supplement_AdmitsShortfall
-- name    : LawLocalComp_Supplement_AdmitsShortfall
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:04:42.774734+00:00
-- url     : https://prove2.me/theorems/f025c3c1-651b-4f4b-aa6e-e68cdb2aa6c4
-- title:
--   Forward shortfall $s_\pi \le \beta\,\mathbb E X$
-- statement:
--   Let $X$, $Y$ be finite nonnegative laws and $\beta \in \mathbb R$. For a coupling $\pi$ of $X$ and $Y$, the **forward shortfall** is
--   $$
--   s_\pi = \mathbb E\bigl(X - \mathbb E_\pi[Y \mid X]\bigr)_+ = \sum_{x} \Bigl(x\,P(X = x) - \sum_y y\,\pi(x, y)\Bigr)_+ .
--   $$
--   The pair $(X, Y)$ **admits shortfall at most $\beta\,\mathbb E X$** if some coupling $\pi$ of $X$ and $Y$ has $s_\pi \le \beta\,\mathbb E X$.
--
--   Zero forward shortfall means $\mathbb E[Y \mid X] \ge X$, the opposite of the conditional-mean contraction $\mathbb E[X \mid Y] = Y$. Theorem 6.2's second lower bound applies to maps whose input/output pairs all admit shortfall at most $\beta\,\mathbb E X$.
--
--   **Formalization Note** $P(X = x)\,(x - \mathbb E_\pi[Y \mid X = x])_+ = (x\,P(X = x) - \sum_y y\,\pi(x, y))_+$, so the shortfall is written without division.
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), §6.1, p.10 (definition of s_π); Theorem 6.2, p.10

import Mathlib
import Definitions.Def_LawLocalComp_mean
import Definitions.Def_LawLocalComp_Supplement_IsCoupling

open Classical

namespace LawLocalComp

namespace Supplement

/-- **The input/output pair admits forward shortfall at most `β E X`.**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), §6.1, p.10: "For an input/output coupling π put s_π = E(X − E_π[Y | X])_+"; Theorem 6.2, p.10
("whose input/output pairs admit s_π ≤ βEX").

`AdmitsShortfall β X Y`: there is a coupling `π` of `X` and `Y` with
`s_π = ∑_x (x · P(X = x) − ∑_y y · π(x, y))_+ ≤ β · E X`.

**Formalization Note.** `P(X = x) · (x − E_π[Y | X = x])_+ = (x · P(X = x) − ∑_y y π(x, y))_+`,
so the shortfall is written without division. -/
def AdmitsShortfall (β : ℝ) (X Y : Law) : Prop :=
  ∃ π : ℝ × ℝ →₀ ℝ, IsCoupling π X Y ∧
    ∑ x ∈ X.w.support, max 0 (x * X.w x - ∑ z ∈ π.support with z.1 = x, z.2 * π z) ≤ β * mean X

end Supplement

end LawLocalComp


