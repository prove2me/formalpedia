-- Prove2me | Definitions.Def_AutobidSPPE_highestOther
-- name    : AutobidSPPE_highestOther
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:56:52.216541+00:00
-- url     : https://prove2.me/theorems/578d80aa-6c8c-44e6-98b6-14aba3380277
-- title:
--   Highest competing bid $v_{-i}=\max_{j\ne i}\alpha_j v_j$
-- statement:
--   The **highest competing bid** faced by bidder $i$ is
--   $$
--   v_{-i} = \max_{j\neq i} \alpha_j v_j ,
--   $$
--   which is the price bidder $i$ pays in the second-price auction when it wins.
--
--   **Formalization Note** The maximum over an empty set of rivals (only possible when $n=1$, excluded by every theorem) is $0$. With endpoints $y$ in place of $\alpha$ and unit uniforms $U$ in place of $v$ the same function is $Z_i=\max_{j\ne i}y_jU_j$ of (6).
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), Problem 1.1, p.4; Table 1, p.9

import Mathlib

namespace AutobidSPPE

/-- The highest competing bid `v₋ᵢ = max_{j ≠ i} αⱼvⱼ` (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), Problem 1.1, p.4; Table 1, p.9),
the second-price payment of bidder `i` when it wins.

**Formalization Note** The maximum over an empty set of rivals is `0` (only for `n = 1`, which
the theorems exclude). With `α := y` and `v := U` it is also `Zᵢ = max_{j≠i} yⱼUⱼ` of (6). -/
noncomputable def highestOther {n : ℕ} (α v : Fin n → ℝ) (i : Fin n) : ℝ :=
  if h : (Finset.univ.erase i).Nonempty then (Finset.univ.erase i).sup' h (fun j => α j * v j)
  else 0

end AutobidSPPE


