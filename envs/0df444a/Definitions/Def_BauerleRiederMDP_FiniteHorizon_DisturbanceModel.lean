-- Prove2me | Definitions.Def_BauerleRiederMDP_FiniteHorizon_DisturbanceModel
-- name    : BauerleRiederMDP_FiniteHorizon_DisturbanceModel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:23:46.861436+00:00
-- url     : https://prove2.me/theorems/ad436640-cae6-4a8f-9615-fcc49bfce804
-- title:
--   Markov Decision Model with disturbances $(E,A,D_n,Z,T_n,Q^Z_n,r_n,g_N)$
-- statement:
--   The data of a Markov Decision Model with disturbances: $E$, $A$, $D_n$, $r_n$, $g_N$ as in a Markov Decision Model; a measurable disturbance space $Z$; for each $n$ a stochastic kernel $Q^Z_n$ giving the law of the disturbance $Z_{n+1}$ given the current state and action; and a measurable transition function $T_n$, with $x_{n+1}=T_n(x_n,a_n,z_{n+1})$.
--
--   Many models in the book, among them the financial markets, are specified this way.
--
--   **Formalization Note.** $Q^Z_n$, $T_n$ and $r_n$ are extended from $D_n$ to $E\times A$, and only their values on $D_n$ enter any statement.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 2.1.3, p.15

import Mathlib
import Definitions.Def_MDPFinance_Bellman_Model
import Definitions.Def_MDPFinance_Bellman_Policy
import Definitions.Def_MDPFinance_Bellman_Operators
import Definitions.Def_MDPFinance_Bellman_History

open MeasureTheory ProbabilityTheory
open MDPFinance.Bellman (MarkovDecisionModel)

namespace BauerleRiederMDP.FiniteHorizon

universe u v w

/-- The data `(E, A, D_n, Z, T_n, Q^Z_n, r_n, g_N)` of a Markov Decision Model with disturbances
(Bäuerle & Rieder (2011), Theorem 2.1.3, p.15, PDF 30).

**Formalization Note.** As in `MDPFinance.Bellman.MarkovDecisionModel`, the book's objects on
`D_n` are extended to `E × A` and the time index is `ℕ`, with only `n < N` meaningful; `D_n` is
measurable, so every book model extends (`Q^Z_n` by any fixed law when `Z` is nonempty, `T_n` by
`(x, a, z) ↦ x`, `r_n` by `0`), and nothing off `D_n` enters a statement. -/
structure DisturbanceModel (E : Type u) (A : Type v) (Z : Type w) [MeasurableSpace E]
    [MeasurableSpace A] [MeasurableSpace Z] (N : ℕ) where
  /-- `D n ⊆ E × A`, the admissible state-action pairs at time `n`. -/
  D : ℕ → Set (E × A)
  hD_meas : ∀ n < N, MeasurableSet (D n)
  /-- `D n` contains the graph of a measurable mapping. -/
  hD_sel : ∀ n < N, ∃ f : E → A, Measurable f ∧ ∀ x, (x, f x) ∈ D n
  /-- The law `Q^Z_n(· | x, a)` of the disturbance `Z_{n+1}`. -/
  QZ : ℕ → Kernel (E × A) Z
  hQZ_prob : ∀ n < N, ∀ xa, IsProbabilityMeasure (QZ n xa)
  /-- The transition function `T_n(x, a, z)`. -/
  Tr : ℕ → (E × A) × Z → E
  hTr_meas : ∀ n < N, Measurable (Tr n)
  /-- The one-stage reward `r_n(x, a)`. -/
  r : ℕ → E × A → ℝ
  hr_meas : ∀ n < N, Measurable (r n)
  /-- The terminal reward `g_N(x)`. -/
  g : E → ℝ
  hg_meas : Measurable g

end BauerleRiederMDP.FiniteHorizon


