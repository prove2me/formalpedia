-- Prove2me | Definitions.Def_DoublyEffIP_Lt
-- name    : DoublyEffIP_Lt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:15:52.677781+00:00
-- url     : https://prove2.me/theorems/4fafeeef-b9f7-4762-a679-6f1a8237eb47
-- title:
--   The transition language $L_t$
-- statement:
--   Fix a set $C$ of configurations and a deterministic step function $\mathrm{step}:C\to C$. For $t\in\mathbb N$, the **transition language** $L_t$ consists of the pairs $(x_{\mathrm{start}},x_{\mathrm{end}})\in C\times C$ such that the machine moves from $x_{\mathrm{start}}$ to $x_{\mathrm{end}}$ in exactly $t$ steps:
--
--   $$
--   L_t=\{(a,b)\in C\times C \mid \mathrm{step}^{t}(a)=b\}.
--   $$
--
--   **Formalization Note** In the paper $C=\{0,1\}^{S(n)}$ and the step function is the transition of the fixed machine $M$; here both are arbitrary, since only determinism is used.
-- source:
--   Chen–Hong–Kalai–Xi, Towards a Doubly Efficient IP = PSPACE, arXiv:2606.21799 (version of 2026-11-02, sha256 14d170db…), Section 4, p.14

import Mathlib

set_option autoImplicit false

namespace DoublyEffIP

/-- **The transition language `L_t`** — Chen–Hong–Kalai–Xi, *Towards a Doubly Efficient
IP = PSPACE*, arXiv:2606.21799 (version of 2026-11-02, sha256 14d170db…), Section 4, p.14: "let
the language L_t consist of all pairs (x_start, x_end) ∈ {0,1}^{S(n)} × {0,1}^{S(n)} such that M
transitions from configuration x_start to configuration x_end in exactly t steps."

For a type `C` of configurations and a deterministic step function `step`, `Lt step t` is the set
of pairs `(a, b)` with `step^t(a) = b`.

**Formalization Note.** Configurations are an arbitrary type and `step` an arbitrary function, in
place of `{0,1}^S` and the transition of the fixed machine `M`; only determinism is used. -/
def Lt {C : Type*} (step : C → C) (t : ℕ) : Set (C × C) :=
  {p | step^[t] p.1 = p.2}

end DoublyEffIP


