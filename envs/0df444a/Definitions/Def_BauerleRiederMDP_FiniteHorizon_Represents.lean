-- Prove2me | Definitions.Def_BauerleRiederMDP_FiniteHorizon_Represents
-- name    : BauerleRiederMDP_FiniteHorizon_Represents
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:24:46.636693+00:00
-- url     : https://prove2.me/theorems/7a006044-a3b0-4b73-9a9a-e7927023f5ef
-- title:
--   Disturbance data representing a Markov Decision Model
-- statement:
--   Disturbance data and a Markov Decision Model describe the same model when $D_n$, $r_n$ on $D_n$ and $g_N$ agree and
--
--   $$Q_n(B\mid x,a)=Q^Z_n\big(\{z\in Z\mid T_n(x,a,z)\in B\}\,\big|\,x,a\big)$$
--
--   for all $(x,a)\in D_n$ and measurable $B\subset E$, for $n<N$. This is the relation between the two descriptions in the proof of Theorem 2.1.3.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 2.1.3 and its proof, p.15

import Mathlib
import Definitions.Def_MDPFinance_Bellman_Model
import Definitions.Def_MDPFinance_Bellman_Policy
import Definitions.Def_MDPFinance_Bellman_Operators
import Definitions.Def_MDPFinance_Bellman_History
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_DisturbanceModel

open MeasureTheory ProbabilityTheory
open MDPFinance.Bellman (MarkovDecisionModel)

namespace BauerleRiederMDP.FiniteHorizon

universe u v w

/-- The disturbance data `DM` and the Markov Decision Model `M` describe the same model (Bäuerle &
Rieder (2011), Theorem 2.1.3 and its proof, p.15, PDF 30): `E, A, D_n, r_n, g_N` agree and
`Q_n(B | x, a) = Q^Z_n({z ∈ Z | T_n(x, a, z) ∈ B} | x, a)` for `(x, a) ∈ D_n` and measurable `B`. -/
def Represents {E : Type u} {A : Type v} {Z : Type w} [MeasurableSpace E] [MeasurableSpace A]
    [MeasurableSpace Z] {N : ℕ} (DM : DisturbanceModel E A Z N) (M : MarkovDecisionModel E A N) :
    Prop :=
  (∀ n < N, DM.D n = M.D n) ∧
  (∀ n < N, ∀ xa ∈ M.D n, DM.r n xa = M.r n xa) ∧
  (∀ x, DM.g x = M.g x) ∧
  ∀ n < N, ∀ xa ∈ M.D n, ∀ B : Set E, MeasurableSet B →
    M.Q n xa B = DM.QZ n xa {z | DM.Tr n (xa, z) ∈ B}

end BauerleRiederMDP.FiniteHorizon


