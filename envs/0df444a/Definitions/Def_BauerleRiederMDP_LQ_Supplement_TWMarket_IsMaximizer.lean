-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_TWMarket_IsMaximizer
-- name    : BauerleRiederMDP_LQ_Supplement_TWMarket_IsMaximizer
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:34:53.660377+00:00
-- url     : https://prove2.me/theorems/4a0910bd-6133-5f9f-8c17-2fd07ef40b81
-- title:
--   A maximizer of $v$ at time $n$
-- statement:
--   **A maximizer of $v$ at time $n$** in the terminal wealth model (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), Definition 2.3.6, p.21, PDF 36, in the model of §4.2, as used in Theorem 4.2.2 c), p.81, PDF 95): a decision rule $f$ (measurable, with $f(x) \in  D_n(x)$ for $x \in  E_n$) such that $f(x)$ attains $\sup _{a \in  D_n(x)} \mathbb E  v((1 + i_{n+1})(x + a \cdot  R_{n+1}))$ at every $x \in  E_n$.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Definition 2.3.6, p.21, PDF 36, in the model of §4.2, as used in Theorem 4.2.2 c), p.81, PDF 95

import Mathlib
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_TWMarket
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_TWMarket_D
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_TWMarket_bellmanQ

namespace BauerleRiederMDP.LQ.Supplement

/-- **A maximizer of `v` at time `n`** in the terminal wealth model (Bäuerle & Rieder, *Markov
Decision Processes with Applications to Finance* (2011), Definition 2.3.6, p.21, PDF 36, in the
model of §4.2, as used in Theorem 4.2.2 c), p.81, PDF 95): a decision rule `f` (measurable, with
`f(x) ∈ D_n(x)` for `x ∈ E_n`) such that `f(x)` attains `sup_{a ∈ D_n(x)} 𝔼 v((1 + i_{n+1})(x + a · R_{n+1}))`
at every `x ∈ E_n`. -/
def TWMarket.IsMaximizer {d : ℕ} (Mk : TWMarket d) (Es : ℕ → Set ℝ) (n : ℕ) (v : ℝ → EReal)
    (f : ℝ → Fin d → ℝ) : Prop :=
  Measurable f ∧ ∀ x ∈ Es n, f x ∈ Mk.D Es n x ∧
    ∀ a ∈ Mk.D Es n x, Mk.bellmanQ n v x a ≤ Mk.bellmanQ n v x (f x)

end BauerleRiederMDP.LQ.Supplement


