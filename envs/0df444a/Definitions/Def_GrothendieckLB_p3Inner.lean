-- Prove2me | Definitions.Def_GrothendieckLB_p3Inner
-- name    : GrothendieckLB_p3Inner
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:48:34.907718+00:00
-- url     : https://prove2.me/theorems/8667f6a0-31ed-46f3-8860-3d5d7066c30f
-- title:
--   $\langle P_3F,P_3G\rangle$
-- statement:
--   The inner product of the degree-three Hermite parts of $F,G:\mathbb R^d\to\mathbb R$:
--   $$
--   \langle P_3F,P_3G\rangle=\frac16\sum_{i,j,l=1}^dT_F(i,j,l)\,T_G(i,j,l).
--   $$
--   For $d=1$ and $F=G=\operatorname{sgn}$ this equals $\nu^2/6$, as on p.31.
--
--   **Formalization Note** The moment sum is the definition, and no $L^2$ projection is constructed. The factor $1/6$ is forced. The direction $\mathrm{He}_3(X_i)=T_F(i,i,i)/\sqrt6$ occurs once in the ordered sum, $\mathrm{He}_2(X_i)X_j$ with coefficient $T_F(i,i,j)/\sqrt2$ occurs three times, and $X_iX_jX_l$ with distinct indices occurs six times, so each squared orthonormal coefficient has total weight one.
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Section 7, p.31

import Mathlib
import Definitions.Def_GrothendieckLB_cubicMoment

namespace GrothendieckLB

/-- `⟨P₃F, P₃G⟩ = (1/6) ∑_{i,j,l} T_F(i,j,l) T_G(i,j,l)`, the inner product of the degree-three
Hermite parts (Saha et al., *New Lower and Upper Bounds for the Grothendieck Constant*, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Section 7, p.31).

**Formalization Note** The factor `1/6` is forced. A pure direction `He₃(X_i) = T/√6` occurs once
in the ordered sum, `He₂(X_i)He₁(X_j) = T/√2` occurs 3 times and `X_i X_j X_l` occurs 6 times, so
each squared orthonormal coefficient is counted with weight one. For `d = 1` and `F = G = sgn` this
gives `ν²/6` as on p.31. The moment sum is the definition; no `L²` projection is constructed. -/
noncomputable def p3Inner {d : ℕ} (F G : (Fin d → ℝ) → ℝ) : ℝ :=
  (1 / 6) * ∑ i, ∑ j, ∑ l, cubicMoment F i j l * cubicMoment G i j l

end GrothendieckLB


