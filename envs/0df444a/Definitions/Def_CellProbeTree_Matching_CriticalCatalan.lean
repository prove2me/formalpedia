-- Prove2me | Definitions.Def_CellProbeTree_Matching_CriticalCatalan
-- name    : CellProbeTree_Matching_CriticalCatalan
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T18:34:42.24728+00:00
-- url     : https://prove2.me/theorems/a6c2263e-ceda-4de1-b179-4f565ef962a3
-- title:
--   The critical Catalan law $p_s = C_s/(2\cdot 4^s)$ and its conditioned vector
-- statement:
--   Let $Z_1, Z_2, \dots$ be independent with the **critical Catalan law** (69)
--   $$\Pr[Z = s] = p_s = \frac{C_s}{2\cdot 4^s}, \qquad s \ge 0,$$
--   where $C_s$ is the $s$-th Catalan number. Put $T_v = Z_1 + \dots + Z_v$ and $a_{v,s} = \Pr[T_v = s]$. For $v \ge 1$, conditioned on $T_v = s$ the vector $(Z_1,\dots,Z_v)$ has the law $\prod_i p_{b_i} / a_{v,s}$ on the tuples $(b_1,\dots,b_v)$ of nonnegative integers with $\sum b_i = s$. This module defines $p_s$, $a_{v,s}$, the conditional marginal $\Pr[Z_i = z \mid T_v = s]$ and the conditional truncated mean $\mathbb E[\min(Z_i + 1, A) \mid T_v = s]$.
--
--   **Formalization Note.** Each quantity is the corresponding finite sum over the tuples `Finset.Nat.antidiagonalTuple v s`; coordinates are 0-based (`i : Fin v`). The conditional quantities divide by $a_{v,s} > 0$ ($v \ge 1$).
-- source:
--   Liang, Liu, Nearly Tight Cell-Probe Lower Bounds for Querying on Tree via Talagrand Inequality, STOC 2027 submission (manuscript sha256 0e5a8eb2…), p. 41, Appendix A.3, equations (69)–(71); p. 42, Appendix A.4

import Mathlib

/-!
# The critical Catalan law and its conditioned vector

Liang, Liu, *Nearly Tight Cell-Probe Lower Bounds for Querying on Tree via Talagrand Inequality*,
STOC 2027 submission, Appendix A.3–A.4, pp. 41–42, equations (69)–(71).

`Z_1, Z_2, …` are independent with `Pr[Z = s] = p_s = C_s / (2·4^s)`, `T_v = Z_1 + ⋯ + Z_v`,
`a_{v,s} = Pr[T_v = s]`. Conditioned on `T_v = s`, the vector `(Z_1, …, Z_v)` has the law
`∏ p_{b_i} / a_{v,s}` on tuples summing to `s`.

**Formalization Note.** All quantities are written as finite sums over the tuples
`Finset.Nat.antidiagonalTuple v s` (`b : Fin v → ℕ` with `Σ b_i = s`); coordinates are 0-based
(`i : Fin v`). The conditional quantities divide by `a_{v,s}`, which is positive for `v ≥ 1`.
-/

namespace CellProbeTree.Matching

/-- `p_s = C_s / (2·4^s)` of (69). -/
noncomputable def critP (s : ℕ) : ℝ := (catalan s : ℝ) / (2 * 4 ^ s)

/-- `a_{v,s} = Pr[T_v = s]` for `v` independent copies of the law (69). -/
noncomputable def critA (v s : ℕ) : ℝ :=
  ∑ b ∈ Finset.Nat.antidiagonalTuple v s, ∏ i, critP (b i)

/-- `Pr[Z_i = z | T_v = s]`. -/
noncomputable def critCondProb (v s : ℕ) (i : Fin v) (z : ℕ) : ℝ :=
  (∑ b ∈ (Finset.Nat.antidiagonalTuple v s).filter (fun b => b i = z), ∏ k, critP (b k))
    / critA v s

/-- `E[min(Z_i + 1, A) | T_v = s]`. -/
noncomputable def critCondTruncMean (v s : ℕ) (i : Fin v) (A : ℝ) : ℝ :=
  (∑ b ∈ Finset.Nat.antidiagonalTuple v s, min ((b i : ℝ) + 1) A * ∏ k, critP (b k))
    / critA v s

end CellProbeTree.Matching


