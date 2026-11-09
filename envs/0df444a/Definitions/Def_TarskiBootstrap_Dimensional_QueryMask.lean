-- Prove2me | Definitions.Def_TarskiBootstrap_Dimensional_QueryMask
-- name    : TarskiBootstrap_Dimensional_QueryMask
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T07:09:32.304741+00:00
-- url     : https://prove2.me/theorems/38e1f229-c364-4677-8b96-3b40b76fcb13
-- title:
--   Whole-answer query distinguisher
-- statement:
--   Let an oracle return $q_f(x)$ for input $f$ and query $x$. Its **distinguisher matrix** at $x$ is
--
--   $$\Delta_x[f,g]=\mathbf1\{q_f(x)\ne q_g(x)\}.$$
--
--   The comparison uses the entire oracle answer, including all grid coordinates. The definition does not convert a grid query into a collection of bit queries.
-- source:
--   Li, Ma, Yang and Zhao, Bootstrapping Classical and Quantum Query Lower Bounds for Finding Tarski Fixed Points, STOC 2027 submission #6 (2026), frozen preprint, Definition 2.5, equation (2.7), PDF/printed p. 7, SHA-256 320afa8333f95589a388b30ffbfd6d7b7e5d93cdf07fa8630825fbf7d0107d59; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/6.pdf. No arXiv identifier/version supplied.

import Mathlib

open scoped Matrix

namespace TarskiBootstrap.Dimensional

/-- Definition 2.5, p. 7: query answers are whole alphabet values. -/
noncomputable def queryMask {S Q O : Type*} (oracle : S → Q → O)
    (x : Q) : Matrix S S ℝ := by
  classical
  exact fun f g => if oracle f x ≠ oracle g x then 1 else 0

end TarskiBootstrap.Dimensional


