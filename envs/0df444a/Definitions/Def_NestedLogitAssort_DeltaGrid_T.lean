-- Prove2me | Definitions.Def_NestedLogitAssort_DeltaGrid_T
-- name    : NestedLogitAssort_DeltaGrid_T
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:02:40.166668+00:00
-- url     : https://prove2.me/theorems/687a5e20-9ec3-48a0-bafc-a127405cad7d
-- title:
--   Constraint value $V_i(S_i)^{\gamma_i}(R_i(S_i)-x)$
-- statement:
--   For a nest $i$, an assortment $S\subseteq N$ and a number $x$, this is the right side
--
--   $$
--   V_i(S)^{\gamma_i}\bigl(R_i(S)-x\bigr)
--   $$
--
--   of the second set of constraints of the linear programs (3) and (4). The variable $y_i$ of nest $i$ must be at least this value for every assortment considered.
--
--   **Formalization Note** The power is the real power `Real.rpow`, with $0^0=1$ and $0^\gamma=0$ for $\gamma\neq0$. The case $V_i(S)=0=\gamma_i$ is not discussed by the paper; Lean's value $1$ is kept.
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript of June 18, 2013, eq. (3), p. 11 and eq. (4), p. 12

import Mathlib
import Definitions.Def_NestedLogitAssort_DeltaGrid_R

namespace NestedLogitAssort.DeltaGrid

/-- **Right side `V_i(S_i)^{γ_i} (R_i(S_i) − x)` of the second constraints of problems (3) and (4).**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript of June 18, 2013, eq. (3), p. 11 and eq. (4), p. 12.

**Formalization Note.** The power is `Real.rpow`: `0 ^ 0 = 1` and `0 ^ γ = 0` for `γ ≠ 0`. The
case `V_i(S_i) = 0 = γ_i` is a `0^0` the paper does not discuss; Lean's value `1` is kept. -/
noncomputable def T {M : Type*} {n : ℕ} (I : Instance M n) (i : M) (S : Finset (Fin n)) (x : ℝ) :
    ℝ :=
  (V I i S) ^ (I.γ i) * (R I i S - x)

end NestedLogitAssort.DeltaGrid


