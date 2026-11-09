-- Prove2me | Definitions.Def_MWCSherali_densTable
-- name    : MWCSherali_densTable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:09:13.330697+00:00
-- url     : https://prove2.me/theorems/ff00051d-4002-4a4a-bc28-91d55b1866a5
-- title:
--   The density vectors of Table 5
-- statement:
--   For unknowns $p_c,q_c,p_s,q_s,p_t$, the density vectors $c^T$ of the six representative tetrahedra (Table 5), in the order of `tetVerts`:
--
--   $$(0,p_c,p_c,1-2p_c),\ (0,1-2q_c,q_c,q_c),\ (p_s,p_s,1-2p_s,0),\ (1-2q_s,q_s,q_s,0),\ (0,0,p_t,1-p_t),\ (0,0,\tfrac12,\tfrac12).$$
--
--   In a tetrahedron $T$ the flows are $dB^T_i=dF^T_{a,i}=Cc^T_i\,dt$ for all $i\neq a$.
-- source:
--   Brakensiek–Huang–Potechin–Zwick, Improved lower bounds on the approximability of Multiway Cut using Sherali–Adams relaxations, arXiv:2611.05511 (version of Nov. 3, 2026), Table 5, p.38

import Mathlib

namespace MWCSherali

/-- **The density vectors `c^T` of Table 5.** Brakensiek–Huang–Potechin–Zwick, arXiv:2611.05511 (version of Nov. 3, 2026), Table 5, p.38, as functions of the
unknowns `p_c, q_c, p_s, q_s, p_t`: for the six representative tetrahedra (in the order of
`tetVerts`)
`(0, p_c, p_c, 1 − 2p_c)`, `(0, 1 − 2q_c, q_c, q_c)`, `(p_s, p_s, 1 − 2p_s, 0)`,
`(1 − 2q_s, q_s, q_s, 0)`, `(0, 0, p_t, 1 − p_t)`, `(0, 0, 1/2, 1/2)`.

**Formalization Note.** Vectors are in Lean's 0-based coordinates (the paper's coordinate `i` is
index `i − 1`); the printed order of entries is kept. -/
noncomputable def densTable (pc qc ps qs pt : ℝ) : Fin 6 → Fin 4 → ℝ :=
  ![![0, pc, pc, 1 - 2 * pc], ![0, 1 - 2 * qc, qc, qc], ![ps, ps, 1 - 2 * ps, 0],
    ![1 - 2 * qs, qs, qs, 0], ![0, 0, pt, 1 - pt], ![0, 0, 1 / 2, 1 / 2]]

end MWCSherali


