-- Prove2me | Definitions.Def_GeomRescale_Ltwo
-- name    : GeomRescale_Ltwo
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:14:40.071436+00:00
-- url     : https://prove2.me/theorems/defde931-665a-4f14-ab5c-3be0963c0200
-- title:
--   The complexity parameter $L_{f,2}$
-- statement:
--   $$L_{f,2} = \max\{\|z\|_2 : z \in B(f)\}.$$
--
--   This quantity enters the number of iterations and the running time of Rescaling-SFM.
--
--   **Formalization Note** The maximum is a `sSup`. `claim_2_2` states that it is attained for submodular $f$ with $f(\emptyset) = 0$.
-- source:
--   Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, §2, p.4

import Mathlib
import Definitions.Def_SchrijverSFM_Alg_Setting
import Definitions.Def_GeomRescale_norm2

namespace GeomRescale

/-- `L_{f,2} = max {‖z‖₂ : z ∈ B(f)}` (Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, §2, p.4).

**Formalization Note.** `sSup`, as for `Lone`; `claim_2_2` states that it is the attained maximum. -/
noncomputable def Ltwo {n : ℕ} (f : Finset (Fin n) → ℝ) : ℝ :=
  sSup (norm2 '' SchrijverSFM.Alg.baseB f)

end GeomRescale


