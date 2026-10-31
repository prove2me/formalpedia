-- Prove2me | Definitions.Def_FuchsThesis_Chernoff_chernoffConst
-- name    : FuchsThesis_Chernoff_chernoffConst
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:55:58.371123+00:00
-- url     : https://prove2.me/theorems/9fa432a4-01e7-4d3d-a714-44f5cdf436e0
-- title:
--   Chernoff constant $\lambda = \min_{\alpha\in[0,1]} F_\alpha(p_0/p_1)$, eq. (2.19)
-- statement:
--   The **Chernoff constant** of two distributions $p_0, p_1$ on a finite outcome set is
--
--   $$
--   \lambda = \inf_{0 \le \alpha \le 1} F_\alpha(p_0/p_1), \qquad F_\alpha(p_0/p_1) = \sum_{b} p_0(b)^{\alpha} p_1(b)^{1-\alpha}.
--   $$
--
--   It does not depend on the priors or on the number of samples, and it governs the exponential rate at which the Bayes error decreases with the number of samplings.
--
--   **Formalization Note** The source writes $\min_\alpha$. With the convention $0^0 = 1$ the minimum need not be attained: for $p_0 = (1, 0)$, $p_1 = (\tfrac12, \tfrac12)$ one has $F_\alpha = 2^{\alpha - 1}$ for $0 < \alpha \le 1$ but $F_0 = 1$, and the infimum $\tfrac12$ is the Chernoff constant. For probability vectors the set of values is nonempty and bounded below by $0$, so the infimum is a genuine one.
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, Theorem 2.1, eq. (2.19), p.16 (PDF p.25)

import Mathlib
import Definitions.Def_FuchsThesis_Chernoff_renyiOverlap

namespace FuchsThesis.Chernoff

/-- Fuchs, *Distinguishability and Accessible Information in Quantum Theory*,
arXiv:quant-ph/9601020v1, Theorem 2.1, eq. (2.19), p.16 (PDF p.25).

The Chernoff constant `λ = min_α Fα(p0/p1)`, `α` restricted to `[0, 1]`.

**Formalization Note.** Defined as the infimum `sInf {Fα(p0/p1) | α ∈ [0, 1]}`. With
`Real.rpow`'s `0 ^ 0 = 1` the minimum need not be attained: for `p0 = (1, 0)`,
`p1 = (½, ½)` one has `Fα = 2^{α−1}` for `α ∈ (0, 1]` but `F0 = 1`, and the infimum `½` is the
Chernoff constant. For probability vectors the set is nonempty and bounded below by `0`, so the
infimum is a genuine one. -/
noncomputable def chernoffConst {B : Type} [Fintype B] (p0 p1 : B → ℝ) : ℝ :=
  sInf (renyiOverlap p0 p1 '' Set.Icc (0 : ℝ) 1)

end FuchsThesis.Chernoff


