-- Prove2me | Definitions.Def_AlgoTransparency_InRegion
-- name    : AlgoTransparency_InRegion
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:49:45.295458+00:00
-- url     : https://prove2.me/theorems/8761bab4-729e-41d2-a32c-d545e1f4bbd1
-- title:
--   The regions of Theorem 1 in the $(C_H,C_L)$ plane (corrected)
-- statement:
--   The regions of Theorem 1, as open subsets of the $(C_H,C_L)$ plane:
--
--   1. $N_1$: $R<C_H$;
--   2. $N_2$: $C_H<(1-\lambda)R$ and $R<C_L$;
--   3. $C_4$: $(1-\lambda)R<C_H<R$ and $R<C_L$;
--   4. $C_1$: $(1-\lambda)R<C_H$ and $\lambda R<C_L<R$;
--   5. $C_2'$ (corrected): $C_L<\lambda R$ and $(1-\lambda)C_L<\lambda C_H$;
--   6. $N_3'$ (corrected): $C_L<(1-\lambda)R$ and $\lambda C_H<(1-\lambda)C_L$;
--   7. $C_3'$ (corrected): $C_H<(1-\lambda)R$, $(1-\lambda)R<C_L<R$ and $\lambda C_H<(1-\lambda)C_L$.
--
--   The theorems intersect them with the feasible cone $0<C_H<C_L$.
--
--   **Formalization Note** The paper defines the regions only by its Figure 4; the inequalities are read off the figure and no boundary is claimed. The printed regions are $C_2$: $(1-\lambda)R<C_H$, $C_L<\lambda R$; $C_3$: $C_H<(1-\lambda)R$, $(1-\lambda)R<C_L<R$; $N_3$: $C_L<(1-\lambda)R$. Theorem 1 fails on the parts of $N_3$ and $C_3$ where $\lambda C_H>(1-\lambda)C_L$, because a both-types-mixing opaque equilibrium is selected there. The corrected regions move those parts into $C_2'$, which contains the printed $C_2$; $N_3'$ and $C_3'$ are the printed $N_3$ and $C_3$ cut by the ray $\lambda C_H=(1-\lambda)C_L$, so $C_3'$ keeps the printed bound $C_H<(1-\lambda)R$ and is disjoint from $C_1$.
-- source:
--   Wang, Huang, Jasin & Singh, Algorithmic Transparency with Strategic Users, arXiv:2008.09283v1, Figure 4, p.21 (PDF 22); Figure 1, p.15 (PDF 16)

import Mathlib
import Definitions.Def_AlgoTransparency_Params
import Definitions.Def_AlgoTransparency_Region

namespace AlgoTransparency

/-- **The regions of Theorem 1 in the `(C_H, C_L)` plane**, Wang, Huang, Jasin & Singh,
arXiv:2008.09283v1, Figure 4, p.21 (PDF 22), as open sets, corrected where marked:

* `N1`: `R < C_H`;
* `N2`: `C_H < (1 − λ)R` and `R < C_L`;
* `C4`: `(1 − λ)R < C_H < R` and `R < C_L`;
* `C1`: `(1 − λ)R < C_H` and `λR < C_L < R`;
* `C2'` (corrected): `C_L < λR` and `(1 − λ)C_L < λC_H`;
* `N3'` (corrected): `C_L < (1 − λ)R` and `λC_H < (1 − λ)C_L`;
* `C3'` (corrected): `C_H < (1 − λ)R`, `(1 − λ)R < C_L < R` and `λC_H < (1 − λ)C_L`.

Every statement of the mission intersects these sets with the feasible cone `0 < C_H < C_L`
(Figure 1, p.15: "the region above the diagonal line is infeasible").

**Formalization Note.** The paper defines the regions only by Figure 4; the inequalities are read
off the figure, as open sets (no boundary is claimed, as in the paper). The printed regions are
`C2`: `(1 − λ)R < C_H`, `C_L < λR`; `C3`: `C_H < (1 − λ)R`, `(1 − λ)R < C_L < R`; `N3`:
`C_L < (1 − λ)R`. Theorem 1 is false on the parts of the printed `N3` and `C3` where
`λC_H > (1 − λ)C_L` (there a both-types-mixing opaque equilibrium is selected); the corrected sets
move those parts into `C2'`, which contains the printed `C2`; `N3'` and `C3'` are the printed
`N3` and `C3` cut by the ray `λC_H = (1 − λ)C_L` (so `C3'` keeps the printed bound
`C_H < (1 − λ)R` and is disjoint from `C1`). The seven corrected sets, like the
printed seven, cover the feasible cone up to boundaries. -/
def InRegion (p : Params) (CH CL : ℝ) : Region → Prop
  | .N1 => p.R < CH
  | .N2 => CH < (1 - p.lam) * p.R ∧ p.R < CL
  | .C4 => (1 - p.lam) * p.R < CH ∧ CH < p.R ∧ p.R < CL
  | .C1 => (1 - p.lam) * p.R < CH ∧ p.lam * p.R < CL ∧ CL < p.R
  | .C2' => CL < p.lam * p.R ∧ (1 - p.lam) * CL < p.lam * CH
  | .N3' => CL < (1 - p.lam) * p.R ∧ p.lam * CH < (1 - p.lam) * CL
  | .C3' => CH < (1 - p.lam) * p.R ∧ (1 - p.lam) * p.R < CL ∧ CL < p.R ∧
      p.lam * CH < (1 - p.lam) * CL

end AlgoTransparency


