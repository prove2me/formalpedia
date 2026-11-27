-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_Htil
-- name    : BauerleRiederMDP_LQ_Supplement_Htil
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T22:56:03.919447+00:00
-- url     : https://prove2.me/theorems/6882dd90-f1fd-5640-82c1-0eddf1c495d8
-- title:
--   The observable histories including the disturbance
-- statement:
--   **The observable histories including the disturbance** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), §5.2, p.154, PDF 167): $\tilde{H}_0 := E_X$, $\tilde{H}_n := \tilde{H}_{n-1} \times  A \times  \mathcal Z  \times  E_X$, with elements $\tilde{h}_n = (x_0, a_0, z_1, x_1, \dots , z_n, x_n)$.
--
--   **Formalization Note.** Defined by recursion on $n$, with the product σ-algebra at each stage (as the published `MDPFinance.Bellman.Hist`, which has no disturbance coordinate).
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §5.2, p.154, PDF 167

import Mathlib

namespace BauerleRiederMDP.LQ.Supplement

universe u

/-- **The observable histories including the disturbance** (Bäuerle & Rieder, *Markov Decision
Processes with Applications to Finance* (2011), §5.2, p.154, PDF 167): `H̃_0 := E_X`,
`H̃_n := H̃_{n−1} × A × 𝒵 × E_X`, with elements `h̃_n = (x_0, a_0, z_1, x_1, …, z_n, x_n)`.

**Formalization Note.** Defined by recursion on `n`, with the product σ-algebra at each stage (as the
published `MDPFinance.Bellman.Hist`, which has no disturbance coordinate). -/
def Htil (EX A Z : Type u) : ℕ → Type u
  | 0 => EX
  | n + 1 => Htil EX A Z n × A × Z × EX

/-- The product σ-algebra on `H̃_n`. -/
instance Htil.instMeasurableSpace (EX A Z : Type u) [MeasurableSpace EX] [MeasurableSpace A]
    [MeasurableSpace Z] : (n : ℕ) → MeasurableSpace (Htil EX A Z n)
  | 0 => ‹MeasurableSpace EX›
  | n + 1 =>
      @Prod.instMeasurableSpace (Htil EX A Z n) (A × Z × EX) (Htil.instMeasurableSpace EX A Z n)
        inferInstance

end BauerleRiederMDP.LQ.Supplement


