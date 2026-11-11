-- Prove2me | Definitions.Def_DepthOptQC_Synth_precLog
-- name    : DepthOptQC_Synth_precLog
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T04:13:55.664122+00:00
-- url     : https://prove2.me/theorems/e575f771-d809-4ab7-8c41-7ab629871814
-- title:
--   The precision scale $L(\varepsilon)=\log_2(2/\varepsilon)$
-- statement:
--   For $\varepsilon\in(0,1)$ let
--   $$
--   L(\varepsilon) := \log_2\frac{2}{\varepsilon} = 1+\log_2\frac1\varepsilon > 1 .
--   $$
--   The resource bounds "$O(\log(1/\varepsilon))$" and "$O(\log\log(1/\varepsilon))$" of the paper are stated for every $\varepsilon\in(0,1)$ as $C\cdot L(\varepsilon)$ and $C\cdot(1+\log_2 L(\varepsilon))$ with a constant $C$. As $\varepsilon\to0$ these are the paper's asymptotics; near $\varepsilon=1$, where $\log(1/\varepsilon)\to0$, they stay bounded away from $0$, as any bound on a circuit that must contain at least one gate has to.
-- source:
--   Vasconcelos, Depth-Optimal Quantum Compilation, arXiv:2609.34659, reading of the resource bounds of Theorem 1, p.6, Theorem 8, p.23 and Corollary 1, p.26

import Mathlib

namespace DepthOptQC.Synth

/-- **The precision scale `L(ε) := log₂(2/ε)`** (Vasconcelos, *Depth-Optimal Quantum Compilation*,
arXiv:2609.34659; reading R1 of the resource bounds of Theorem 1, p.6, Theorem 8, p.23, and
Corollary 1, p.26).

**Formalization Note.** The paper's bounds `O(log(1/ε))` and `O(log log(1/ε))` are stated for every
`ε ∈ (0, 1)` as `C · L(ε)` and `C · (1 + log₂ L(ε))`. On `(0, 1)`, `L(ε) = 1 + log₂(1/ε) > 1`, so
these are positive even as `ε → 1`, where `log(1/ε) → 0` would make any `C · log(1/ε)` bound false;
as `ε → 0` they are the paper's asymptotics. Only `ε ∈ (0, 1)` is used (for `ε ≤ 0`, Lean's
`Real.logb` of a nonpositive number is a junk value). -/
noncomputable def precLog (ε : ℝ) : ℝ :=
  Real.logb 2 (2 / ε)

end DepthOptQC.Synth


