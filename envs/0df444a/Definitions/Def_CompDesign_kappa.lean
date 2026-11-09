-- Prove2me | Definitions.Def_CompDesign_kappa
-- name    : CompDesign_kappa
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:52:23.459817+00:00
-- url     : https://prove2.me/theorems/48ef5129-587f-4153-8fed-6205d1095021
-- title:
--   Cost concentration term $\kappa(\lambda)$ (20)
-- statement:
--   For $\lambda\ge 0$, the **cost concentration term** is
--
--   $$
--   \kappa(\lambda)=\max\Big\{\sum_{i\in S}\frac{x_i}{1-x_i} : 0\le x_i\le\lambda \text{ and } \sum_i x_i\le 1 \text{ for a finite } S\Big\}.
--   $$
--
--   It measures how much the relative marginal gains $x_i/(1-x_i)$, $x_i=c_i/B$, of agents missing from an equilibrium can add up when the agents' costs fit in the budget. It is the constant of the price-of-anarchy bound $1+\kappa(\lambda)$ of Theorem 5.1; the paper notes $\kappa(\lambda)\le 1/(1-\lambda)$.
--
--   **Formalization Note** `λ` is a Lean keyword, so the parameter is `l`. A finite family is `x : Fin m → ℝ` for some `m`, over every `m`, independent of the number of agents of an instance. The maximum is a real `sSup`; for $0\le\lambda<1$ the set contains $0$ (the empty family) and is bounded above by $1/(1-\lambda)$, so this is a genuine supremum, and by Claim 5.1 it is attained. Every statement using $\kappa$ assumes $0\le\lambda<1$, so the Lean value $x/0=0$ at $x_i=1$ never arises.
-- source:
--   Anagnostides, Bhawalkar, Liaw, Mehta, Paes Leme, Teng, Velegkas, Zheng, Compensation Design, arXiv:2607.14438 (version of November 3, 2026, sha256 3d305d4d…), §5.1, eq. (20), p.26 (PDF 29)

import Mathlib

namespace CompDesign

/-- The cost concentration term (20) of Anagnostides et al., *Compensation Design*, arXiv:2607.14438
(version of November 3, 2026, sha256 3d305d4d…), §5.1, p.26 (PDF 29):
`κ(λ) = max { ∑_{i∈S} x_i/(1 − x_i) : 0 ≤ x_i ≤ λ and ∑_i x_i ≤ 1 for a finite S }`.

**Formalization Note.** `λ` is a Lean keyword, so the parameter is `l`. A finite family is
`x : Fin m → ℝ` for some `m : ℕ`; the range is every finite family, independent of the number of
agents of any instance. The maximum is written as a real `sSup`. For `0 ≤ l < 1` the set is nonempty
(`m = 0` gives `0`) and bounded above by `1/(1 − l)`, so the `sSup` is a genuine supremum (the paper's
Claim 5.1 shows it is attained). Every use of `kappa` assumes `0 ≤ l < 1`; then `x_j ≤ l < 1`, so the
Lean convention `x/0 = 0` at `x_j = 1` is never reached. -/
noncomputable def kappa (l : ℝ) : ℝ :=
  sSup {s : ℝ | ∃ (m : ℕ) (x : Fin m → ℝ), (∀ j, 0 ≤ x j ∧ x j ≤ l) ∧ ∑ j, x j ≤ 1 ∧
    s = ∑ j, x j / (1 - x j)}

end CompDesign


