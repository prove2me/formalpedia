-- Prove2me | Definitions.Def_RobustMultiStop_dualMax
-- name    : RobustMultiStop_dualMax
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:30:55.986252+00:00
-- url     : https://prove2.me/theorems/f3ac71d8-4cbf-4490-825b-d2ce3dba89ef
-- title:
--   The pathwise dual maximum $\max_{t\le j_1<\dots<j_L}\sum_k(H_{j_k}+M^{(k)}_{j_{k-1}}-M^{(k)}_{j_k})$
-- statement:
--   For a reward process $H$, a start date $t$ and processes $M^{(1)},\dots,M^{(L)}$, the **pathwise dual maximum** is
--
--   $$\max_{t\le j_1<j_2<\dots<j_L\le N}\ \sum_{k=1}^{L}\Big(H_{j_k}+M^{(k)}_{j_{k-1}}-M^{(k)}_{j_k}\Big),\qquad j_0=t,$$
--
--   taken pointwise (almost surely). In Theorem 3.1 the value $Y^{*,L}_t$ is the infimum over $\rho$-martingales of $\rho_t$ of this quantity, attained at the $\rho$-Doob martingales, and under sensitivity it equals the quantity itself.
--
--   **Formalization Note** The maximum is `Finset.sup'` in the lattice of a.e.-classes over the finite set of tuples. When no tuple exists ($L\ge1$ and $t+L>N+1$) the value is $0$; every statement that uses it either assumes $t+L\le N+1$ or is vacuous otherwise. For $L=0$ the value is $0$. Legs are $0$-based.
-- source:
--   Laeven, Schoenmakers, Schweizer & Stadje, Robust Multiple Stopping — A Pathwise Duality Approach, arXiv:2006.01802v2, (3.1)–(3.3), p.8; j_0 = t from the proof, p.41

import Mathlib
import Definitions.Def_RobustMultiStop_prevIdx
import Definitions.Def_RobustMultiStop_tuples

open MeasureTheory

namespace RobustMultiStop

/-- The pathwise maximum of the dual, Laeven, Schoenmakers, Schweizer & Stadje, *Robust Multiple
Stopping — A Pathwise Duality Approach*, arXiv:2006.01802v2, (3.1)–(3.3), p.8:

`max_{t ≤ j_1 < j_2 < ⋯ < j_L} Σ_{k=1}^L (H_{j_k} + M^{(k)}_{j_{k−1}} − M^{(k)}_{j_k})`, with
`j_0 = t` (proof of Theorem 3.1, p.41).

For `M : Fin L → ℕ → Ω →ₘ[P] ℝ` (the `k`-th leg uses `M k`, `0`-based) `dualMax N H t M` is the
finite lattice supremum, over the tuples `t ≤ j 0 < ⋯ < j (L-1) ≤ N`, of the sum over legs of
`H (j k) + M k (j_{k−1}) − M k (j k)`, with `j_{−1} := t`.

**Formalization Note** The maximum is `Finset.sup'` in the lattice `Ω →ₘ[P] ℝ` (pointwise a.s.
maximum). When no tuple exists, i.e. `L ≥ 1` and `t + L > N + 1`, the value is `0`; every statement
of the mission that uses `dualMax` either has `t + L ≤ N + 1` or is vacuous without it. For `L = 0`
the only tuple is empty and the value is `0`, the paper's `Θ⁰ = 0` (p.16). With `0`-based legs, the
paper's `M^{*,L−k+1}` (`1`-based `k`) is the leg `k - 1`'s `M`, i.e. the leg `k` (`0`-based) carries
`M^{*,L−k}`. -/
noncomputable def dualMax {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω} {L : ℕ}
    (N : ℕ) (H : ℕ → Ω →ₘ[P] ℝ) (t : ℕ) (M : Fin L → ℕ → Ω →ₘ[P] ℝ) : Ω →ₘ[P] ℝ :=
  if h : (tuples N t L).Nonempty then
    (tuples N t L).sup' h (fun j => ∑ k, (H (j k) + M k (prevIdx t (fun k => (j k : ℕ)) k)
      - M k (j k)))
  else 0

end RobustMultiStop


