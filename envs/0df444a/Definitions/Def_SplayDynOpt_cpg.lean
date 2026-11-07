-- Prove2me | Definitions.Def_SplayDynOpt_cpg
-- name    : SplayDynOpt_cpg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:56:44.469494+00:00
-- url     : https://prove2.me/theorems/973d8557-8baf-43a3-aadc-1bfbb165e620
-- title:
--   The contracted point gap $\lceil 1+\log_2(1+z)\rceil$
-- statement:
--   For a heavy path with point gap $z$, the **contracted point gap** is
--   $$
--   \operatorname{cpg}(z)=\lceil 1+\log_2(1+z)\rceil .
--   $$
--   For example $\operatorname{cpg}(0)=1$, $\operatorname{cpg}(1)=2$, $\operatorname{cpg}(3)=3$ and $\operatorname{cpg}(4)=\operatorname{cpg}(5)=4$.
--
--   Contracting gaps by a logarithm is what brings the damage of a boundary pairing down to $O(\log\log n)$.
--
--   **Formalization Note** The function is defined on all integers. Only $z\ge0$ occurs in the statements.
-- source:
--   Chmel et al., Splay trees are almost dynamically optimal, arXiv:2607.18498 (version of 2026-11-02, sha256 6881e83c…), Definition 8, p.19; footnote 6, p.19

import Mathlib

set_option autoImplicit false

namespace SplayDynOpt

/-- The **contracted point gap** of a heavy path with point gap `z`: `⌈1 + log₂(1 + z)⌉`.

Chmel et al., *Splay trees are almost dynamically optimal*, arXiv:2607.18498 (version of
2026-11-02, sha256 6881e83c…), Definition 8, p.19: "We define the contracted point gap of a heavy
path P as ⌈1 + log(1 + pointgap(P))⌉."; footnote 6: "All logarithms in this work are binary."

**Formalization Note.** Defined on all integers `z`; only `z ≥ 0` (point gaps) is used. -/
noncomputable def cpg (z : ℤ) : ℤ :=
  ⌈1 + Real.logb 2 (1 + (z : ℝ))⌉

end SplayDynOpt


