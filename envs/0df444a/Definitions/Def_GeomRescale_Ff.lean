-- Prove2me | Definitions.Def_GeomRescale_Ff
-- name    : GeomRescale_Ff
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:13:35.015509+00:00
-- url     : https://prove2.me/theorems/84bca322-7d08-416b-92a2-23647e45a31a
-- title:
--   The complexity parameter $F_f$
-- statement:
--   $$F_f = \max\{|f(S)| : S \subseteq V\}.$$
--
--   The maximum is over a finite nonempty family of sets.
-- source:
--   Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, §2, p.4

import Mathlib

namespace GeomRescale

/-- `F_f = max {|f(S)| : S ⊆ V}` (Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, §2, p.4). A maximum over the finite nonempty family of
all subsets, so no junk value can occur. -/
noncomputable def Ff {n : ℕ} (f : Finset (Fin n) → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun S => |f S|)

end GeomRescale


