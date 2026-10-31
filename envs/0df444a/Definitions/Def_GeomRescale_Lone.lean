-- Prove2me | Definitions.Def_GeomRescale_Lone
-- name    : GeomRescale_Lone
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:14:03.631627+00:00
-- url     : https://prove2.me/theorems/aa78b7a3-c72b-4b32-a0c0-5255f8f24a66
-- title:
--   The complexity parameter $L_f$
-- statement:
--   $$L_f = \max\{\|z\|_1 : z \in B(f)\}.$$
--
--   **Formalization Note** The maximum is a `sSup`, over the published base polytope `SchrijverSFM.Alg.baseB`. `claim_2_2` states that it is attained for submodular $f$ with $f(\emptyset) = 0$.
-- source:
--   Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, §2, p.4

import Mathlib
import Definitions.Def_SchrijverSFM_Alg_Setting
import Definitions.Def_GeomRescale_norm1

namespace GeomRescale

/-- `L_f = max {‖z‖₁ : z ∈ B(f)}` (Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, §2, p.4).

**Formalization Note.** `sSup`, with `B(f)` the published `SchrijverSFM.Alg.baseB`. A real `sSup`
returns `0` on an unbounded set, so `claim_2_2` states that for submodular `f` with `f(∅) = 0` this
value is the attained maximum. -/
noncomputable def Lone {n : ℕ} (f : Finset (Fin n) → ℝ) : ℝ :=
  sSup (norm1 '' SchrijverSFM.Alg.baseB f)

end GeomRescale


