-- Prove2me | Definitions.Def_ProjFPOracle_kappa
-- name    : ProjFPOracle_kappa
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:31:57.977468+00:00
-- url     : https://prove2.me/theorems/8073b959-dc7a-4737-939a-a2b8fb097140
-- title:
--   $\kappa(M)=\tfrac12\lambda_{\max}(M+M^\top)$
-- statement:
--   For a real $d\times d$ matrix $M$ ($d\ge1$),
--   $$
--   \kappa(M):=\tfrac12\,\lambda_{\max}\big(M+M^\top\big),
--   $$
--   half the largest eigenvalue of the symmetric matrix $M+M^\top$. Equivalently, $\kappa(M)$ is the largest value of $u^\top Mu$ over unit vectors $u\in\mathbb R^d$.
--
--   The condition $\kappa(M)<1$ makes $I_d-M$ invertible, so the projected fixed-point equation has a unique solution; $1-\kappa(M)$ is the stability margin that enters every bound of the mission.
--
--   **Formalization Note** $\lambda_{\max}$ is the published `LowRankMEG.lam · 1`, the largest eigenvalue (with multiplicity) of a real symmetric matrix. At $d=0$ there is no eigenvalue and the value is a junk $0$; every statement assumes $d\ge1$.
-- source:
--   Mou, Pananjady & Wainwright, Optimal Oracle Inequalities for Projected Fixed-Point Equations, arXiv:2012.05299v1, §2.1, p.7, Eq. (9); p.12

import Mathlib
import Definitions.Def_LowRankMEG_lam

namespace ProjFPOracle

/-- **`κ(M) := ½ λ_max(M + Mᵀ)`** (Mou, Pananjady & Wainwright, *Optimal Oracle Inequalities for
Projected Fixed-Point Equations*, arXiv:2012.05299v1, Eq. (9), p.7, and p.12): half the largest
eigenvalue of the symmetrized matrix `M + Mᵀ`.

**Formalization Note** `λ_max` is the published `LowRankMEG.lam · 1`, the largest eigenvalue of a
real symmetric matrix counted with multiplicity; `M + Mᵀ` is symmetric. For `d = 0` there is no
eigenvalue and the value is a junk `0`; every statement of the mission assumes `1 ≤ d`. -/
noncomputable def kappa {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  (1 / 2 : ℝ) * LowRankMEG.lam (M + M.transpose) 1

end ProjFPOracle


