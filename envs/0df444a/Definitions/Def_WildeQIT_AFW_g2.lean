-- Prove2me | Definitions.Def_WildeQIT_AFW_g2
-- name    : WildeQIT_AFW_g2
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:35:58.06104+00:00
-- url     : https://prove2.me/theorems/78af0f30-7a80-47b2-a846-0c8e0fa77b6b
-- title:
--   The function $g_2(\varepsilon) = (\varepsilon+1)\log_2(\varepsilon+1) - \varepsilon\log_2\varepsilon$
-- statement:
--   For a real number $\varepsilon$ put
--
--   $$
--   g_2(\varepsilon) \equiv (\varepsilon + 1)\log_2(\varepsilon + 1) - \varepsilon\log_2\varepsilon ,
--   $$
--
--   with the convention $0\log_2 0 = 0$, so that $g_2(0) = 0$. On $[0,1]$ it equals $(1+\varepsilon)\,h_2\!\left(\frac{\varepsilon}{1+\varepsilon}\right)$, where $h_2$ is the binary entropy, and it increases from $g_2(0) = 0$ to $g_2(1) = 2$.
--
--   It is the additive term in the Alicki–Fannes–Winter continuity bound for conditional entropy and in the bounds on mutual information and conditional mutual information derived from it.
--
--   **Formalization Note** The logarithm is base 2 (`Real.logb 2`). The function is defined on all of $\mathbb R$; Lean's `Real.logb 2 0 = 0` gives the convention $0\log 0 = 0$. The book evaluates it on $[0,1]$ only.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 11.10.3, p. 359 (definition of g2 after (11.253)); identity g2(ε) = (1+ε)h2(ε/(1+ε)) on p. 361

import Mathlib

namespace WildeQIT.AFW

/-- Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 11.10.3, p. 359:
"g₂(ε) ≡ (ε + 1) log₂(ε + 1) − ε log₂ ε".

**Formalization Note.** Base-2 logarithm (`Real.logb 2`). The book evaluates `g₂` on `[0, 1]`;
the function is total on `ℝ`, and `Real.logb 2 0 = 0` gives `g₂(0) = 0` (the convention
`0 log 0 = 0`). -/
noncomputable def g2 (ε : ℝ) : ℝ :=
  (ε + 1) * Real.logb 2 (ε + 1) - ε * Real.logb 2 ε

end WildeQIT.AFW


