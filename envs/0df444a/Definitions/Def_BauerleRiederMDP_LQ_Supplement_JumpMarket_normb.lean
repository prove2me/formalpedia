-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket_normb
-- name    : BauerleRiederMDP_LQ_Supplement_JumpMarket_normb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:12:39.7678+00:00
-- url     : https://prove2.me/theorems/d3d6e47c-cf61-4fe9-a2eb-0593e4315d05
-- title:
--   The weighted supremum norm $\|v\|_b$
-- statement:
--   **The weighted supremum norm $\|v\|_b$** on $E$ (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), p.29 and Definition 7.3.1, p.205, used in Theorems 9.3.4 c) and 9.3.7, pp.287–290): $\|v\|_b = \sup _{(t,x) \in  E} |v(t, x)|/b(t, x)$, `b = bfun γ`.
--
--   **Formalization Note.** A supremum in $\mathbb R \ge 0\infty $ (of $|v|/b$, $b > 0$), so an unbounded quotient gives $\infty $, not a junk real value.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), p.29 and Definition 7.3.1, p.205, used in Theorems 9.3.4 c) and 9.3.7, pp.287–290

import Mathlib
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket_Eset
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket_bfun

namespace BauerleRiederMDP.LQ.Supplement

/-- **The weighted supremum norm `‖v‖_b`** on `E` (Bäuerle & Rieder, *Markov Decision Processes with
Applications to Finance* (2011), p.29 and Definition 7.3.1, p.205, used in Theorems 9.3.4 c) and
9.3.7, pp.287–290): `‖v‖_b = sup_{(t,x) ∈ E} |v(t, x)|/b(t, x)`, `b = bfun γ`.

**Formalization Note.** A supremum in `ℝ≥0∞` (of `|v|/b`, `b > 0`), so an unbounded quotient gives
`∞`, not a junk real value. -/
noncomputable def JumpMarket.normb {d : ℕ} (Mk : JumpMarket d) (γ : ℝ) (v : ℝ × ℝ → ℝ) : ENNReal :=
  ⨆ p ∈ Mk.Eset, ENNReal.ofReal (|v p| / Mk.bfun γ p)

end BauerleRiederMDP.LQ.Supplement


