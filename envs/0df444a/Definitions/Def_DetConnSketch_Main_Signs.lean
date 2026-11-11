-- Prove2me | Definitions.Def_DetConnSketch_Main_Signs
-- name    : DetConnSketch_Main_Signs
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T06:41:22.857604+00:00
-- url     : https://prove2.me/theorems/3e7785a0-e812-46ad-bcff-b16d6227ea83
-- title:
--   Signs $\pm1$ encoded by bits, and real sign matrices
-- statement:
--   A sign $\pm1$ is encoded by a bit: $\mathrm{sgn}(\text{true}) = 1$, $\mathrm{sgn}(\text{false}) = -1$. A uniformly random sign vector $\sigma \in \{-1,1\}^k$ is then a uniformly random bit vector, and a uniformly random sign matrix $A \in \{-1,1\}^{D\times n}$ a uniformly random $D \times n$ bit array. A real matrix $S$ is a **sign matrix** when every entry is $1$ or $-1$.
--
--   **Formalization Note.** `sgn : Bool → ℝ` and `IsSignMatrix S : Prop` for `S : Matrix ι κ ℝ`.
-- source:
--   Khanna, Putterman, Sudan, Deterministic Connectivity Sketches Under Edge Deletions, arXiv:2611.06626 (copy sha256 fff87f5b…), p. 29 (PDF 33), Fact 4.9; pp. 48–49 (PDF 52–53), §8.1–8.2

import Mathlib

namespace DetConnSketch.Main

/-!
# Signs and sign matrices

Khanna, Putterman, Sudan, *Deterministic Connectivity Sketches Under Edge Deletions*,
arXiv:2611.06626 (copy sha256 fff87f5b…), p. 29 (Fact 4.9), pp. 48–49 (§8.1–8.2).

A sign `±1` is encoded by a bit: `sgn true = 1`, `sgn false = -1`, so a uniformly random sign
vector in `{−1, 1}^k` is a uniformly random `Fin k → Bool`, and a uniformly random sign matrix in
`{−1, 1}^{D×n}` is a uniformly random `Fin D → Fin n → Bool`. A real sign matrix is a real matrix
all of whose entries are `1` or `−1`.
-/

/-- The sign encoded by a bit: `true ↦ 1`, `false ↦ -1`. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

/-- `S` is a sign matrix: every entry is `1` or `-1`. -/
def IsSignMatrix {ι κ : Type} (S : Matrix ι κ ℝ) : Prop :=
  ∀ i j, S i j = 1 ∨ S i j = -1

end DetConnSketch.Main


