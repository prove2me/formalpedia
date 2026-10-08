-- Prove2me | Definitions.Def_SmoothedSimplex_TwoPhase_shadow
-- name    : SmoothedSimplex_TwoPhase_shadow
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T13:33:47.731022+00:00
-- url     : https://prove2.me/theorems/b5d1875c-d607-4091-95fb-ae22e75c2684
-- title:
--   Definition 3.2.4 — polar shadow
-- statement:
--   For linearly independent objectives $t,z\in\mathbb R^d$ and positive right-hand sides $y_i$, the polar shadow collects every optimal simplex whose supporting objective lies in the plane they span:
--   $$\operatorname{Shadow}_{t,z}(a;y)=\bigcup_{q\in\operatorname{Span}(t,z)}\operatorname{optSimp}_q(a;y).$$
--   Its cardinality bounds the number of polar shadow-vertex pivots. The same definition is used for the first phase in dimension $d$ and for the lifted second phase in dimension $d+1$.
--
--   **Formalization Note** The result is a finite set of $d$-subsets of `Fin n`. The formula remains total when the plane degenerates; source bounds are applied to positive right-hand sides and nondegenerate planes or their almost-sure Gaussian instances.
-- source:
--   Spielman & Teng, Smoothed Analysis of Algorithms, arXiv:cs/0111050v7, Definition 3.2.4, printed p. 32, PDF p. 32

import Mathlib
import Definitions.Def_SmoothedSimplex_TwoPhase_optSimp

namespace SmoothedSimplex.TwoPhase

/-- The union of `optSimp_q` over the plane spanned by `t,z` (Spielman–Teng,
Definition 3.2.4, printed p. 32, PDF p. 32). The paper states it for independent
`t,z` and strictly positive `y`; the same finite-set formula is total in Lean and
is used on degenerate data only inside Gaussian-null events. -/
noncomputable def shadow {n d : ℕ} (a : Fin n → Point d) (y : Fin n → ℝ)
    (t z : Point d) : Finset (Finset (Fin n)) := by
  classical
  exact (Finset.univ.powersetCard d).filter (fun I =>
    ∃ q : Point d, q ∈ Submodule.span ℝ ({t, z} : Set (Point d)) ∧ I ∈ optSimp a y q)

end SmoothedSimplex.TwoPhase


