-- Prove2me | Definitions.Def_FRouting_Supplement_InDTIME
-- name    : FRouting_Supplement_InDTIME
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:20:32.932079+00:00
-- url     : https://prove2.me/theorems/05308fa5-5642-484b-bdb4-b99c99132238
-- title:
--   The deterministic time class $\mathbf{DTIME}(B)$
-- statement:
--   For $B:\mathbb N\to\mathbb N$, a promise problem $(\Pi_{\mathrm{yes}},\Pi_{\mathrm{no}})$ on binary strings is in $\mathbf{DTIME}(B)$ if a single deterministic machine $M$, on every instance $w\in\Pi_{\mathrm{yes}}\cup\Pi_{\mathrm{no}}$, halts within $\max(1,B(|w|))$ steps with output $1$ if $w\in\Pi_{\mathrm{yes}}$ and $0$ if $w\in\Pi_{\mathrm{no}}$. A language $L$ is the promise problem $(L, L^{\mathrm c})$.
--
--   This is the class in the conclusion of Theorem 1.5.
--
--   **Formalization Note** Machines are the base mission's string machines (Mathlib multi-stack Turing machines over $\{0,1\}$).
-- source:
--   Renard, Computational Bounds for f-Routing, arXiv:2609.40278 (held copy, sha256 4a327f29…), Theorem 1.5, p.5

import Definitions.Def_FRouting_StrMachine
import Definitions.Def_FRouting_languageOf

set_option autoImplicit false

namespace FRouting.Supplement

open QAlgorithms.Complexity

/-- **Membership in `DTIME(B)`.** Renard, *Computational Bounds for f-Routing*, arXiv:2609.40278 (held
copy, sha256 4a327f29…), Theorem 1.5, p.5, uses the deterministic time class without defining it. A
promise problem is in `DTIME(B)` when one deterministic machine `M`, on every instance `w`, halts within
the budget of `B |w|` steps, printing `[true]` on Yes instances and `[false]` on No instances.

**Formalization Note** The machine is the published `FRouting.StrMachine` (a Mathlib `FinTM2`), the same
model as the base mission's verifiers. `budget B` is `max 1 B`, which differs from `B` only where
`B = 0`. -/
def InDTIME (P : PromiseProblem) (B : ℕ → ℕ) : Prop :=
  ∃ M : StrMachine,
    (∀ w ∈ P.Yes, PrintsInTime M w [true] (budget B w.length)) ∧
    (∀ w ∈ P.No, PrintsInTime M w [false] (budget B w.length))

end FRouting.Supplement


