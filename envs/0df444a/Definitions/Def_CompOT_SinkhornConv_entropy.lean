-- Prove2me | Definitions.Def_CompOT_SinkhornConv_entropy
-- name    : CompOT_SinkhornConv_entropy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:19:57.360685+00:00
-- url     : https://prove2.me/theorems/d0be4c39-fc1b-4d42-bb2f-604ca9b64006
-- title:
--   Discrete entropy $H(P)$ of a coupling
-- statement:
--   For an $n\times m$ matrix $P$, the **discrete entropy** is
--   $$H(P) = -\sum_{i,j} P_{i,j}\,(\log P_{i,j} - 1).$$
--
--   On nonnegative matrices $-H$ is strictly convex; it is the regularizer added to the transport cost in entropic optimal transport.
--
--   **Formalization Note** A zero entry contributes $0$ (the convention $0\log 0 = 0$, the limit of $x(\log x - 1)$ as $x\to 0^+$), because Mathlib's `Real.log 0 = 0`. The paper's convention $H(a)=-\infty$ for a vector with a zero or negative entry is stated for vectors; in this mission $H$ is applied only to couplings, which are nonnegative.
-- source:
--   Peyré, Cuturi, Computational Optimal Transport, Found. Trends Mach. Learn. 11(5–6) (2019), doi:10.1561/2200000073, §4.1, eq. (4.1), p. 425

import Mathlib

namespace CompOT.SinkhornConv

/-- **Discrete entropy of a coupling `H(P) = −Σ_{i,j} P_{i,j}(log P_{i,j} − 1)`.**
Peyré, Cuturi, *Computational Optimal Transport*, Found. Trends Mach. Learn. 11(5–6) (2019), §4.1, eq. (4.1), p. 425: "H(P) := −Σi,j Pi,j(log(Pi,j) − 1)".

`entropy P` is `−Σ_{i,j} P i j * (log (P i j) − 1)`.

**Formalization Note.** Lean's `Real.log 0 = 0` gives the term `0 · (log 0 − 1) = 0` for a zero
entry, i.e. the usual convention `0 log 0 = 0` (the limit of `x (log x − 1)` as `x → 0⁺`). The
paper's separate convention "H(a) = −∞ if one of the entries a_j is 0 or negative" is stated for
vectors; this definition is used only on couplings (nonnegative matrices) in this mission. -/
noncomputable def entropy {n m : ℕ} (P : Matrix (Fin n) (Fin m) ℝ) : ℝ :=
  -∑ i, ∑ j, P i j * (Real.log (P i j) - 1)

end CompOT.SinkhornConv


