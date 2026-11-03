-- Prove2me | Definitions.Def_WeightedCongestionBR_groupLoad
-- name    : WeightedCongestionBR_groupLoad
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:16:09.032407+00:00
-- url     : https://prove2.me/theorems/f6cca46a-dc7a-486f-a09f-6c991836886e
-- title:
--   Group load $x_{R,e}(s)$
-- statement:
--   For a group $R$, a resource $e$ and a state $s$,
--
--   $$
--   x_{R,e}(s)=\sum_{u\in R:\ e\in s_u} w_u .
--   $$
--
--   For $R=N$ it is the load $x_e(s)$.
--
--   **Formalization Note** The game is the published `HarksKlimm.Consistency.Game n r`: players `Fin n`, resources `Fin r` with $n, r \ge 1$, nonempty finite strategy sets $S_u \subseteq 2^E$, weights $w_u > 0$ (the field `demand`) and cost functions of the load. The value is real (the published `load` is the same sum in $\mathbb R_{\ge0}$).
-- source:
--   Giannakopoulos, Noarov, Schulz, Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses, arXiv:1810.12806v6, §2, p.6

import Mathlib
import Definitions.Def_HarksKlimm_Consistency_Game
set_option autoImplicit false
open scoped NNReal
open HarksKlimm.Consistency

namespace WeightedCongestionBR

/-- The load of a group on a resource (Giannakopoulos, Noarov, Schulz, *Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses*, arXiv:1810.12806v6, §2, p.6): `x_{R,e}(s) := ∑_{u ∈ R : e ∈ s_u} w_u`. For
`R = N` it is the load `x_e(s)` (the published `HarksKlimm.Consistency.load`, read in `ℝ`).

**Formalization Note** Real-valued, so that it can be fed to `phiPoly`. -/
noncomputable def groupLoad {n r : ℕ} (G : Game n r) (s : G.Profile) (R : Finset (Fin n))
    (e : Fin r) : ℝ :=
  ∑ u ∈ R, if e ∈ (s u).val then (G.demand u : ℝ) else 0

end WeightedCongestionBR


