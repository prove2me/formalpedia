-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_TWMarket_bellmanQ
-- name    : BauerleRiederMDP_LQ_Supplement_TWMarket_bellmanQ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:34:26.906421+00:00
-- url     : https://prove2.me/theorems/4c3516f6-1fc7-4f8e-8960-dde338a55f6a
-- title:
--   The one-step objective of the terminal wealth problem
-- statement:
--   **The one-step objective of the terminal wealth problem** $\mathbb E  v((1 + i_{n+1})(x + a \cdot  R_{n+1}))$ (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), Theorem 4.2.2 b), p.81, PDF 95), the quantity maximized over $a \in  D_n(x)$ in the Bellman equation with $v = V_{n+1}$.
--
--   **Formalization Note.** The expectation is the published `eint` against the law of $R_{n+1}$.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011)

import Mathlib
import Definitions.Def_BauerleRiederMDP_RegimeSwitching_eint
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_TWMarket

open MeasureTheory

namespace BauerleRiederMDP.LQ.Supplement

/-- **The one-step objective of the terminal wealth problem**
`𝔼 v((1 + i_{n+1})(x + a · R_{n+1}))` (Bäuerle & Rieder, *Markov Decision Processes with Applications
to Finance* (2011), Theorem 4.2.2 b), p.81, PDF 95), the quantity maximized over `a ∈ D_n(x)` in the
Bellman equation with `v = V_{n+1}`.

**Formalization Note.** The expectation is the published `eint` against the law of `R_{n+1}`. -/
noncomputable def TWMarket.bellmanQ {d : ℕ} (Mk : TWMarket d) (n : ℕ) (v : ℝ → EReal) (x : ℝ)
    (a : Fin d → ℝ) : EReal :=
  BauerleRiederMDP.RegimeSwitching.eint (Mk.ν (n + 1) : Measure (Fin d → ℝ))
    (fun z => v ((1 + Mk.i (n + 1)) * (x + a ⬝ᵥ z)))

end BauerleRiederMDP.LQ.Supplement


