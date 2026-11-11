-- Prove2me | Definitions.Def_SchattenSketch_Main_Cycle
-- name    : SchattenSketch_Main_Cycle
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T03:56:43.362893+00:00
-- url     : https://prove2.me/theorems/4c66a029-75f9-45e7-9bdd-638bebb5525f
-- title:
--   The Gaussian injective cycle statistic $\hat p_j$ of (5.29)
-- statement:
--   Let $z_1,\dots,z_s\in\mathbb R^n$ be samples and $j\ge 2$. The **injective cycle statistic** is
--   $$\hat p_j=\frac1{(s)_j}\sum_{a_1,\dots,a_j\ \text{distinct}}\langle z_{a_1},z_{a_2}\rangle\langle z_{a_2},z_{a_3}\rangle\cdots\langle z_{a_j},z_{a_1}\rangle,\qquad (s)_j=s(s-1)\cdots(s-j+1).$$
--   For i.i.d. $N(0,\Sigma)$ samples it is unbiased for the spectral moment $\mathrm{tr}(\Sigma^j)$ (5.30).
--
--   **Formalization Note.** The samples are the rows of `z : Matrix (Fin s) (Fin n) ℝ`; the ordered tuples of distinct labels are the embeddings `Fin j ↪ Fin s`, the cyclic successor is `finRotate j`, and $(s)_j$ is `Nat.descFactorial s j`.
-- source:
--   Lin F. Yang, Near-Optimal Bounds for Sketching the Schatten Norms, arXiv:2608.22247 (held version, sha256 c29a210a…), p. 29, (5.29)

import Mathlib

namespace SchattenSketch.Main

/-- The injective cycle statistic (5.29) (Yang, p. 29) of samples `z₁, …, z_s ∈ ℝⁿ` (the rows of
`z`), for `j ≥ 2`:
`p̂_j = (s)_j⁻¹ ∑_{a₁, …, a_j distinct} ⟨z_{a₁}, z_{a₂}⟩⟨z_{a₂}, z_{a₃}⟩ ⋯ ⟨z_{a_j}, z_{a₁}⟩`,
with `(s)_j = s(s - 1)⋯(s - j + 1)`. The sum runs over injective maps `a : Fin j → Fin s`,
and `finRotate j` sends position `l` to the next position `l + 1` cyclically. -/
noncomputable def cycleStat {s n : ℕ} (z : Matrix (Fin s) (Fin n) ℝ) (j : ℕ) : ℝ :=
  (1 / (Nat.descFactorial s j : ℝ)) *
    ∑ a : Fin j ↪ Fin s, ∏ l : Fin j, (z (a l) ⬝ᵥ z (a (finRotate j l)))

end SchattenSketch.Main


