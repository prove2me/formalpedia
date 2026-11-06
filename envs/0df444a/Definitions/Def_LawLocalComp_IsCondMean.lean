-- Prove2me | Definitions.Def_LawLocalComp_IsCondMean
-- name    : LawLocalComp_IsCondMean
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:11:24.361878+00:00
-- url     : https://prove2.me/theorems/db26667d-4a30-4907-a7d2-c87e75aa7dce
-- title:
--   Conditional-mean replacement $\mathbb E[X\mid Y]=Y$
-- statement:
--   A law $Y$ is a **conditional-mean replacement** of a law $X$ if there is a coupling $\pi$ of $X$ and $Y$ — a finitely supported joint law on $\mathbb R^2$ with first marginal $X$ and second marginal $Y$ — under which
--   $$\mathbb E_\pi[X\mid Y]=Y,\qquad\text{i.e.}\qquad \sum_x x\,\pi(x,y)=y\,\mathbb P(Y=y)\ \text{ for every } y.$$
--   Equivalently $Y=\mathbb E[X\mid\Lambda]$ for a randomized label $\Lambda$: in the paper's words, "labels may be unordered and randomly split", and boundary atoms are split between cells.
--
--   **Formalization Note** This is not $Y=\mathbb E[X\mid f(X)]$ for a deterministic labelling $f$, which would forbid split atoms.
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), §1, p.2; §6, p.9

import Mathlib
import Definitions.Def_LawLocalComp_Law
open Classical

namespace LawLocalComp

/-- **`Y` is a conditional-mean replacement of `X`.**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), §1, p.2 ("Our contracting maps use actual conditional means"); §6, p.9 ("Here Y = E[X | Λ];
labels may be unordered and randomly split"); §3, p.5 ("split boundary atoms rationally").

`IsCondMean X Y` holds when there is a coupling `π` of `X` and `Y` (a finitely supported joint law
on `ℝ × ℝ` with first marginal `X` and second marginal `Y`) under which `E[X | Y] = Y`: for every
output value `y`, `∑_x x · π(x, y) = y · P(Y = y)`.

**Formalization Note.** `E[X | Y] = Y` under some coupling is equivalent to `Y = E[X | Λ]` for a
randomized label `Λ` (take `Λ = Y`), which is the paper's reading: labels may split atoms at random.
It is not `Y = E[X | σ(f(X))]` for a deterministic labelling `f`. -/
def IsCondMean (X Y : Law) : Prop :=
  ∃ π : ℝ × ℝ →₀ ℝ, (∀ z, 0 ≤ π z) ∧
    (∀ x : ℝ, ∑ z ∈ π.support with z.1 = x, π z = X.w x) ∧
    (∀ y : ℝ, ∑ z ∈ π.support with z.2 = y, π z = Y.w y) ∧
    (∀ y : ℝ, ∑ z ∈ π.support with z.2 = y, z.1 * π z = y * Y.w y)

end LawLocalComp


