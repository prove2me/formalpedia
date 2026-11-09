-- Prove2me | Definitions.Def_MWCSherali_densVec
-- name    : MWCSherali_densVec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:10:18.763484+00:00
-- url     : https://prove2.me/theorems/1ebff024-4052-4c9e-9365-328978ae7cb5
-- title:
--   The density vectors with the parameters of Lemma 4.6
-- statement:
--   The density vectors of Table 5 with Lemma 4.6's choice of parameters
--
--   $$q_c=p_t=\tfrac12,\quad p_c=\frac{2\alpha-2+3\beta}{6(\alpha-1+2\beta)},\quad p_s=\tfrac12-\beta,\quad q_s=1-2\alpha+(4\alpha-1)p_c .$$
-- source:
--   Brakensiek–Huang–Potechin–Zwick, Improved lower bounds on the approximability of Multiway Cut using Sherali–Adams relaxations, arXiv:2611.05511 (version of Nov. 3, 2026), Lemma 4.6, p.39; Table 5, p.38

import Mathlib
import Definitions.Def_MWCSherali_densTable

namespace MWCSherali

/-- **The density vectors with Lemma 4.6's parameters.** Brakensiek–Huang–Potechin–Zwick, arXiv:2611.05511 (version of Nov. 3, 2026), Lemma 4.6, p.39: the
vectors of Table 5 with "`q_c = p_t = 1/2`, `p_c = (2α − 2 + 3β)/(6(α − 1 + 2β))`,
`p_s = 1/2 − β`, `q_s = 1 − 2α + (4α − 1)p_c`". -/
noncomputable def densVec (α β : ℝ) : Fin 6 → Fin 4 → ℝ :=
  let pc := (2 * α - 2 + 3 * β) / (6 * (α - 1 + 2 * β))
  densTable pc (1 / 2) (1 / 2 - β) (1 - 2 * α + (4 * α - 1) * pc) (1 / 2)

end MWCSherali


