-- Prove2me | Definitions.Def_SymNormLoad_Phi__cbe170
-- name    : SymNormLoad_Phi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:29:36.024059+00:00
-- url     : https://prove2.me/theorems/cbe17042-2d5b-40fe-9ea3-caaa5c69c94c
-- title:
--   Separable potential $\Phi(x)=\sum_i g(x_i)$
-- statement:
--   For $x\in\mathbb R^M_{\ge0}$, the **potential** is
--   $$
--   \Phi(x)=\sum_{i=1}^{M}g(x_i),\qquad g=\exp\circ h.\tag{2.3}
--   $$
--   Note $\Phi(0)=M$. The online algorithm greedily minimizes the increase of $\Phi$.
--
--   **Formalization Note** Defined for every $x$; nonnegativity is a hypothesis of the theorems.
-- source:
--   Chen–Im–Sirri, Online Load Balancing under Symmetric Norms, manuscript (STOC 2027 submission), Section 2.1.2, Eq. (2.3), p.10

import Mathlib
import Definitions.Def_SymNormLoad_pen

namespace SymNormLoad

/-- **The separable potential `Φ(x) = ∑_i g(x_i)`.** Chen–Im–Sirri, *Online Load Balancing under
Symmetric Norms*, manuscript (STOC 2027 submission), Eq. (2.3), p.10:
`Φ(x) = ∑_{i=1}^M g(x_i)` with `g = exp ∘ h`.

**Formalization Note** Defined for every `x : Fin M → ℝ`; the paper uses it on `ℝ^M_{≥0}`, and
nonnegativity is a hypothesis of each theorem. -/
noncomputable def Phi {M : ℕ} (h : ℝ → ℝ) (x : Fin M → ℝ) : ℝ :=
  ∑ i, pen h (x i)

end SymNormLoad


