-- Prove2me | Definitions.Def_FuchsThesis_Chernoff_renyiOverlap
-- name    : FuchsThesis_Chernoff_renyiOverlap
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:55:14.460583+00:00
-- url     : https://prove2.me/theorems/9c9308b4-b4b6-4007-abc7-63cfb47f2252
-- title:
--   Overlap $F_\alpha(p_0/p_1) = \sum_b p_0(b)^\alpha p_1(b)^{1-\alpha}$, eq. (2.20)
-- statement:
--   For distributions $p_0, p_1$ on a finite outcome set and a real parameter $\alpha$,
--
--   $$
--   F_\alpha(p_0/p_1) = \sum_{b=1}^{n} p_0(b)^{\alpha}\, p_1(b)^{1-\alpha}.
--   $$
--
--   For $0 \le \alpha \le 1$ this overlap lies between $0$ and $1$; its minimum over $\alpha$ is the Chernoff constant.
--
--   **Formalization Note** Real powers follow Lean's convention $0^0 = 1$, so $F_0 = \sum_b p_1(b)$ and $F_1 = \sum_b p_0(b)$ even at outcomes where the other distribution vanishes.
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, Theorem 2.1, eq. (2.20), p.16 (PDF p.25)

import Mathlib

namespace FuchsThesis.Chernoff

/-- Fuchs, *Distinguishability and Accessible Information in Quantum Theory*,
arXiv:quant-ph/9601020v1, Theorem 2.1, eq. (2.20), p.16 (PDF p.25).

`Fα(p0/p1) = ∑_{b=1}^{n} p0(b)^α p1(b)^{1−α}`.

**Formalization Note.** Real powers are `Real.rpow`, which has `0 ^ 0 = 1`; so at `α = 0` the
value is `∑_b p1(b)` and at `α = 1` it is `∑_b p0(b)`, also at outcomes where the other
distribution vanishes. -/
noncomputable def renyiOverlap {B : Type} [Fintype B] (p0 p1 : B → ℝ) (α : ℝ) : ℝ :=
  ∑ b, p0 b ^ α * p1 b ^ (1 - α)

end FuchsThesis.Chernoff


