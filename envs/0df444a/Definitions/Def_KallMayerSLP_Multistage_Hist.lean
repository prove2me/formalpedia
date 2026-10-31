-- Prove2me | Definitions.Def_KallMayerSLP_Multistage_Hist
-- name    : KallMayerSLP_Multistage_Hist
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:13:01.274264+00:00
-- url     : https://prove2.me/theorems/cd871dc9-524e-42da-805f-6eb02f3632e2
-- title:
--   State space $\mathbb R^{r_2+\dots+r_t}$ of $\zeta_t$
-- statement:
--   For dimensions $r_2,\dots,r_T$ and a stage $t$, this is the space $\mathbb R^{r_2+\dots+r_t}$ in which the state variable $\zeta_t=(\xi_2,\dots,\xi_t)$ takes its values. A point consists of one vector of $\mathbb R^{r_s}$ for each stage $s$ with $2\le s\le t$.
--
--   At $t=1$ there are no such stages, so the space is a single point; this is the deterministic state of the first stage.
--
--   **Formalization Note** Stages keep the book's 1-based index $t\in\mathbb N$, and the family is indexed by the subtype `Set.Icc 2 t`.
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 3, §3, (3.1), p.248 (PDF 257), and Remark 3.1, p.249 (PDF 258)

import Mathlib

namespace KallMayerSLP.Multistage

/-- The space `ℝ^{r_2 + ⋯ + r_t}` in which the state variable `ζ_t = (ξ_2, …, ξ_t)` of stage `t`
lives (Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3, §3, (3.1), p.248, PDF 257,
and Remark 3.1, p.249, PDF 258).

**Formalization Note.** Stages keep the book's 1-based index `t : ℕ`. A point of `Hist r t` is a
family indexed by the stages `s` with `2 ≤ s ≤ t`. At `t = 1` there are no such stages, so
`Hist r 1` is a single point: the deterministic state of the first stage. -/
abbrev Hist (r : ℕ → ℕ) (t : ℕ) : Type := ∀ s : Set.Icc 2 t, Fin (r s) → ℝ

end KallMayerSLP.Multistage


