-- Prove2me | Definitions.Def_MultiSelectPandora_IsWeitzmanRule
-- name    : MultiSelectPandora_IsWeitzmanRule
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:08:39.9972+00:00
-- url     : https://prove2.me/theorems/6ae1d5ac-4b44-484e-bbc3-a0400ecfcc0c
-- title:
--   The generalized Weitzman rule
-- statement:
--   A rule maps the set $U$ of unopened boxes and the state $\alpha$ to the next box to open or to "stop". It is a generalized Weitzman rule when: if some $i\in U$ has $\sigma_i>\alpha_k$, it opens a box of $U$ of largest reservation value; otherwise it stops. Thus it opens boxes in nonincreasing order of reservation value and stops as soon as the largest reservation value among the unopened boxes is at most $\alpha_k$.
--
--   **Formalization Note** Ties among boxes of largest reservation value are broken arbitrarily, as a function of $(U,\alpha)$.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), §2.3, p.6 (PDF p.7)

import Mathlib
import Definitions.Def_MultiSelectPandora_Inst
import Definitions.Def_MultiSelectPandora_resv
import Definitions.Def_MultiSelectPandora_stFloor

namespace MultiSelectPandora

/-- **The generalized Weitzman rule, with any tie-breaking.** Beyhaghi–Han–Luqman manuscript, §2.3, p.6 (PDF p.7): it "opens
boxes in nonincreasing order of reservation value and stops as soon as the largest reservation value among the unopened
boxes is at most the `k`-th best value `α_k`".

**Formalization Note.** A rule maps a set of unopened boxes and a state to the next box, or to `none` for stopping. The
ties among boxes of largest `σ` are broken by the rule itself, as a function of `(U, α)`. -/
def IsWeitzmanRule (I : Inst) (k : ℕ) (rule : Finset (Fin I.n) → (Fin k → ℝ) → Option (Fin I.n)) : Prop :=
  ∀ U α,
    ((∃ i ∈ U, stFloor α < resv I i) → ∃ i, rule U α = some i ∧ i ∈ U ∧ ∀ l ∈ U, resv I l ≤ resv I i) ∧
    ((∀ i ∈ U, resv I i ≤ stFloor α) → rule U α = none)

end MultiSelectPandora


