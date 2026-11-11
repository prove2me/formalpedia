-- Prove2me | Definitions.Def_PosIndexNash_PPADS_LCP
-- name    : PosIndexNash_PPADS_LCP
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:31:29.469469+00:00
-- url     : https://prove2.me/theorems/5fd74f12-a866-4180-a5e3-4197da39f466
-- title:
--   Solutions of the linear complementarity problem LCP(M, q) (p. 37)
-- statement:
--   For $M \in \mathbb{R}^{m\times m}$ and $q \in \mathbb{R}^m$, the **linear complementarity problem** $\mathrm{LCP}(M, q)$ asks for $x \in \mathbb{R}^m$ with
--   $$x \ge 0,\qquad Mx + q \ge 0,\qquad x_i\,(Mx+q)_i = 0 \quad (i \in [m]).$$
--   `LCPSol M q` is its solution set. The paper's LCP (39) is $\mathrm{LCP}(M, -b)$: the vector $b$ is the right-hand side and the offset is $-b$.
-- source:
--   Kontogiannis, Panageas, Pollatos, Yan, Finding a Positive Index Nash Equilibrium is PPADS-Complete, arXiv:2609.23879 (held PDF, sha256 00d5c5ce…cbb6), p. 37, the LCP(M, q) convention after (39)

import Mathlib

namespace PosIndexNash.PPADS

open Matrix

/-- **Solutions of the linear complementarity problem `LCP(M, q)`** (Kontogiannis, Panageas,
Pollatos, Yan, *Finding a Positive Index Nash Equilibrium is PPADS-Complete*, arXiv:2609.23879,
p. 37: "LCP(M, q) denotes x ≥ 0, Mx + q ≥ 0, x_i (Mx + q)_i = 0 (i ∈ [m])").

`LCPSol M q` is the set of real vectors `x ∈ ℝ^m` with `x ≥ 0`, `Mx + q ≥ 0` and
`x_i (Mx + q)_i = 0` for every `i`. -/
def LCPSol {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ) (q : Fin m → ℝ) : Set (Fin m → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ (∀ i, 0 ≤ (M *ᵥ x + q) i) ∧ ∀ i, x i * (M *ᵥ x + q) i = 0}

end PosIndexNash.PPADS


