-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_TWMarket_IsPolicy
-- name    : BauerleRiederMDP_LQ_Supplement_TWMarket_IsPolicy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:35:32.869812+00:00
-- url     : https://prove2.me/theorems/51b7de88-e745-493d-87a2-97d103844382
-- title:
--   A policy of the terminal wealth Markov Decision Model
-- statement:
--   **A policy of the terminal wealth Markov Decision Model** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), §4.2, p.80, PDF 94, with Definition 2.1.5, p.16, PDF 31): a sequence $(f_0, \dots , f_{N-1})$ of decision rules, i.e. measurable $f_n : E_n \to  \mathbb R ^d$ with $f_n(x) \in  D_n(x)$ for all $x \in  E_n$.
--
--   **Formalization Note.** A rule is a function on $\mathbb R $, constrained on $E_n$ only; values for $n \ge  N$ are unused.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §4.2, p.80, PDF 94, with Definition 2.1.5, p.16, PDF 31

import Mathlib
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_TWMarket
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_TWMarket_D

namespace BauerleRiederMDP.LQ.Supplement

/-- **A policy of the terminal wealth Markov Decision Model** (Bäuerle & Rieder, *Markov Decision
Processes with Applications to Finance* (2011), §4.2, p.80, PDF 94, with Definition 2.1.5, p.16,
PDF 31): a sequence `(f_0, …, f_{N−1})` of decision rules, i.e. measurable `f_n : E_n → ℝ^d` with
`f_n(x) ∈ D_n(x)` for all `x ∈ E_n`.

**Formalization Note.** A rule is a function on `ℝ`, constrained on `E_n` only; values for `n ≥ N`
are unused. -/
def TWMarket.IsPolicy {d : ℕ} (Mk : TWMarket d) (Es : ℕ → Set ℝ) (N : ℕ)
    (f : ℕ → ℝ → Fin d → ℝ) : Prop :=
  ∀ k < N, Measurable (f k) ∧ ∀ x ∈ Es k, f k x ∈ Mk.D Es k x

end BauerleRiederMDP.LQ.Supplement


