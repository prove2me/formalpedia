-- Prove2me | Definitions.Def_QPSpinParisi_IsFreeEnergyLimit
-- name    : QPSpinParisi_IsFreeEnergyLimit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:07:45.393442+00:00
-- url     : https://prove2.me/theorems/2af3bccd-3e14-4653-b8c5-7ce460e5b0ca
-- title:
--   $A$ is the limiting free energy $A_\xi$
-- statement:
--   A function $A$ is the limiting free energy when, for every $\beta>0$ and every choice of realizations of $Y_n$,
--   $$A_\xi(\beta)=\lim_{n\to\infty}A^Y_n(\beta)$$
--   equals $A(\beta)$. The existence of such an $A$ is part of Lemma 3.4.
--
--   **Formalization Note** Values of $A$ at $\beta\le0$ are unconstrained.
-- source:
--   Bhattacharya, Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), Lemma 3.4, p.16 (PDF p.16)

import Mathlib
import Definitions.Def_QPSpinParisi_AY

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal Matrix

namespace QPSpinParisi

/-- `A` is the limit `A_ξ(β) := lim_{n→∞} A^Y_n(β)` for every `β > 0` (Bhattacharya, *Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians*, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), Lemma 3.4, p.16, PDF p.16).

**Formalization Note** The limit is required along every choice of realizations of the fields `Y_n`. The values of
`A` at `β ≤ 0` are unconstrained. -/
def IsFreeEnergyLimit (c : ℕ → ℝ) (A : ℝ → ℝ) : Prop :=
  ∀ β : ℝ, 0 < β → ∀ F : ∀ n, OverlapField c n, Tendsto (fun n => AY (F n) β) atTop (𝓝 (A β))

end QPSpinParisi


