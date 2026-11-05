-- Prove2me | Definitions.Def_BauerleRiederMDP_FiniteHorizon_pathKernel
-- name    : BauerleRiederMDP_FiniteHorizon_pathKernel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:24:05.158793+00:00
-- url     : https://prove2.me/theorems/2d0a6a28-139b-4881-bd26-20d37f172f77
-- title:
--   Law of the next $k$ transitions of the controlled process
-- statement:
--   Given a path of $j_0$ transitions at calendar time $n_0$ and measurable rules giving the action at each time $n_0+i<N$ as a function of the path so far, the kernel $P_k$ sends the path to the law of its continuation by $k$ transitions:
--
--   $$P_0=\mathrm{id},\qquad P_{k+1}=\text{(one transition at time } n_0+k)\circ P_k .$$
--
--   This is the finite-horizon Ionescu–Tulcea construction of the law of the Markov Decision Process, composed forwards in time.
--
--   **Formalization Note.** No value function and no operator $T_n$ enters this definition. Beyond the horizon the kernel is $0$; every use stops exactly at time $N$.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), pp.16–17

import Mathlib
import Definitions.Def_MDPFinance_Bellman_Model
import Definitions.Def_MDPFinance_Bellman_Policy
import Definitions.Def_MDPFinance_Bellman_Operators
import Definitions.Def_MDPFinance_Bellman_History
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_stepKernel

open MeasureTheory ProbabilityTheory
open MDPFinance.Bellman (MarkovDecisionModel Hist)

namespace BauerleRiederMDP.FiniteHorizon

universe u

/-- The law of the next `k` transitions of the controlled process (Bäuerle & Rieder (2011),
pp.16–17, PDF 31–32; the finite-horizon Ionescu–Tulcea construction, Appendix B): the kernel from
a path of `j₀` transitions at calendar time `n₀` to its continuation by `k` transitions, obtained
by composing `stepKernel` forwards in time. The action at calendar time `n₀ + i` is given by
`rule i`, a measurable function of the path so far, available while `n₀ + i < N`.

**Formalization Note.** This is a forward composition of the transition kernels: no value function
and no operator `L_n`, `T_n` enters it. Beyond the horizon (`n₀ + k ≥ N`) the kernel is `0`; every
use below stops exactly at `N`. -/
noncomputable def pathKernel {E A : Type u} [MeasurableSpace E] [MeasurableSpace A] {N : ℕ}
    (M : MarkovDecisionModel E A N) (n₀ j₀ : ℕ)
    (rule : (i : ℕ) → n₀ + i < N → {f : Hist E A (j₀ + i) → A // Measurable f}) :
    (k : ℕ) → Kernel (Hist E A j₀) (Hist E A (j₀ + k))
  | 0 => Kernel.id
  | k + 1 =>
      if hk : n₀ + k < N then
        stepKernel M (n₀ + k) (j₀ + k) (rule k hk).1 (rule k hk).2 ∘ₖ pathKernel M n₀ j₀ rule k
      else 0

end BauerleRiederMDP.FiniteHorizon


