-- Prove2me | Definitions.Def_GeomRescale_alpha
-- name    : GeomRescale_alpha
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:13:48.493726+00:00
-- url     : https://prove2.me/theorems/5a83cd72-de62-43d5-8771-bdd81ab8b971
-- title:
--   The vector $\alpha$ of upper bounds
-- statement:
--   For $v \in V$,
--
--   $$\alpha(v) = \max\{|f(\{v\})|,\ |f(V) - f(V \setminus \{v\})|\}.$$
--
--   Its norms are easily computable upper bounds on $L_f$ and $L_{f,2}$ (Claim 2.2).
-- source:
--   Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, §2, p.4

import Mathlib

namespace GeomRescale

/-- The vector `α(v) = max {|f({v})|, |f(V) − f(V ∖ {v})|}` (Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, §2, p.4). -/
noncomputable def alpha {n : ℕ} (f : Finset (Fin n) → ℝ) (v : Fin n) : ℝ :=
  max |f {v}| |f Finset.univ - f (Finset.univ.erase v)|

end GeomRescale


