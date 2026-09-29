-- Prove2me | Definitions.Def_PhiDivRobust_Counterpart_phiDiv
-- name    : PhiDivRobust_Counterpart_phiDiv
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T18:46:26.994897+00:00
-- url     : https://prove2.me/theorems/f9861ef2-a38d-47a4-b800-8c241fed9c14
-- title:
--   φ-divergence I_φ(p, q) = Σ q_i φ(p_i/q_i), Eq. (2)
-- statement:
--   For vectors $p, q\in\mathbb R^m$ and a φ-divergence function $\phi$, the **φ-divergence** of $p$ from $q$ is
--
--   $$I_\phi(p,q) = \sum_{i=1}^m q_i\,\phi\!\left(\frac{p_i}{q_i}\right)\in\mathbb R\cup\{+\infty\}.$$
--
--   It measures the "distance" of a candidate probability vector $p$ from a nominal one $q$, and is the quantity bounded by $\rho$ in the uncertainty region (12).
--
--   **Formalization Note** The sum is taken in `EReal`. The mission uses $I_\phi(p,q)$ only for $q>0$ componentwise, so the paper's conventions $0\phi(a/0) := a\lim_{t\to\infty}\phi(t)/t$ and $0\phi(0/0):=0$ are not formalized; for $q_i = 0$ the Lean expression is not the paper's value and no statement of the mission uses it there.
-- source:
--   Ben-Tal, den Hertog, De Waegenaere, Melenberg, Rennen, Robust Solutions of Optimization Problems Affected by Uncertain Probabilities, Management Sci. 59(2), 2013, p. 343, Eq. (2)

import Mathlib
open Matrix

namespace PhiDivRobust.Counterpart

/-- The φ-divergence `I_φ(p, q) = ∑ᵢ qᵢ φ(pᵢ / qᵢ)` (Ben-Tal et al. 2013, p. 343, Eq. (2)), valued in
`EReal`. It is used only with `q > 0`, so the paper's conventions for `qᵢ = 0` are not needed. -/
noncomputable def phiDiv {m : ℕ} (φ : ℝ → EReal) (p q : Fin m → ℝ) : EReal :=
  ∑ i, (q i : EReal) * φ (p i / q i)

end PhiDivRobust.Counterpart


