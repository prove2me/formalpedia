-- Prove2me | Definitions.Def_UCalibDirichlet_counts
-- name    : UCalibDirichlet_counts
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:24:13.005389+00:00
-- url     : https://prove2.me/theorems/4e679080-d562-4789-9aaf-f6ee4962a111
-- title:
--   Label counts $N_t$
-- statement:
--   For outcomes $i_1,\dots,i_t$, the count vector is $N_t=\sum_{s=1}^t e_{i_s}$: its $j$-th coordinate is the number of rounds $s\le t$ with $i_s=j$. Algorithm 1 uses $a_t=N_{t-1}+\mathbf 1$, and $\hat p_T=N_T/T$ is the empirical distribution of the outcomes.
-- source:
--   Frongillo, Luo, Mehta & Schneider, Near-Optimal Regret in U-Calibration for Every Proper Loss (manuscript, STOC 2027 submission), §1.1, p.2

import Mathlib

namespace UCalibDirichlet

/-- **Label counts `N_t`.** Frongillo, Luo, Mehta & Schneider (manuscript, STOC 2027 submission),
§1.1, p.2: "With `N_t = ∑_{s=1}^t e_{i_s}` being the vector of label counts through round `t`".

For a history `h : Fin t → Fin K` (the outcomes `i_1, …, i_t`), `counts h j` is the number of
rounds `s` with `h s = j`, i.e. the `j`-th coordinate of `N_t`. -/
def counts {K t : ℕ} (h : Fin t → Fin K) (j : Fin K) : ℕ :=
  (Finset.univ.filter fun s => h s = j).card

end UCalibDirichlet


