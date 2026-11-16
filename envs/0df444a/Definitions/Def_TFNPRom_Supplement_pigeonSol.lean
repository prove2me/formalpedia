-- Prove2me | Definitions.Def_TFNPRom_Supplement_pigeonSol
-- name    : TFNPRom_Supplement_pigeonSol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:26:00.851077+00:00
-- url     : https://prove2.me/theorems/e182e586-7b2c-4c5f-9e5a-bc1811afe1b4
-- title:
--   Solutions of Pigeon (collisions)
-- statement:
--   For $m>n$, **Pigeon** asks, given $x\in[n]^m$, for a collision: a pair $i\neq j\in[m]$ with $x_i=x_j$. For $m=2n$ this is the PWPP-complete problem WeakPigeon.
--
--   Theorem 36 shows that Pigeon on $[n]^{2n}$ has no low-error public reduction to the canonical PLS-complete problem.
--
--   **Formalization Note** $[m]$ and $[n]$ are `Fin m` and `Fin n`; the unordered pair $\{i,j\}$ is represented by the ordered pair $(i,j)$, and both orders of a collision are solutions.
-- source:
--   Fleming, Göös, Guan, Korten, Mitropolsky, Pitassi, Riazanov, Sokolov, Yang, Yuan, TFNP in the Random Oracle Model, arXiv:2611.05308 (held version, sha256 e11eb9c3…9bb), §5.3, p.32; App. A, p.41 (PWPP)

import Mathlib

namespace TFNPRom.Supplement

/-- The solutions of Pigeon on `[n]^m` (Fleming et al., *TFNP in the Random Oracle Model*, arXiv:2611.05308 (held version, sha256 e11eb9c3…9bb), §5.3, p.32: "the problem `Pigeon ⊆ [n]^m × ([m] choose 2)`,
for `m > n`, of finding a collision `x_i = x_j` in a given `x ∈ [n]^m`"; App. A, p.41, PWPP
(WeakPigeon) for `m = 2n`). A pair `(i, j)` solves `x` iff `i ≠ j` and `x_i = x_j`.

**Formalization Note** `[m]`, `[n]` are `Fin m`, `Fin n` (0-based). The unordered pair `{i, j}` is
represented by the ordered pair `(i, j)`; both orders of a collision are solutions. -/
def pigeonSol {m n : ℕ} (x : Fin m → Fin n) (o : Fin m × Fin m) : Prop :=
  o.1 ≠ o.2 ∧ x o.1 = x o.2

end TFNPRom.Supplement


