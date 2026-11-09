-- Prove2me | Definitions.Def_TarskiBootstrap_Dimensional_FixedPoint
-- name    : TarskiBootstrap_Dimensional_FixedPoint
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T07:13:24.822198+00:00
-- url     : https://prove2.me/theorems/a42b2872-16b0-43df-9a2e-6d86349d3701
-- title:
--   Restricted fixed-point answer map
-- statement:
--   For an endomap $f$ with a unique fixed point, its restricted oracle problem has answer $f^*$. For a family $F$, the set of possible answers is
--
--   $$A=\{f^*:f\in F\}.$$
--
--   The answer selector chooses a fixed point whenever one exists. On a nonempty carrier without a fixed point it returns an arbitrary carrier element; every theorem using the selector assumes existence and uniqueness for the functions concerned. The selector imposes no extra premise or conclusion on those functions. This makes the answer alphabet the entire grid.
-- source:
--   Li, Ma, Yang and Zhao, Bootstrapping Classical and Quantum Query Lower Bounds for Finding Tarski Fixed Points, STOC 2027 submission #6 (2026), frozen preprint, §2.1–2.2, PDF/printed pp. 6–7; Theorem 1.1, PDF/printed pp. 4, 10, SHA-256 320afa8333f95589a388b30ffbfd6d7b7e5d93cdf07fa8630825fbf7d0107d59; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/6.pdf. No arXiv identifier/version supplied.

import Definitions.Def_TarskiBootstrap_Dimensional_Grid

open scoped Matrix

namespace TarskiBootstrap.Dimensional

/-- Restricted answer map f ↦ f*, §2.2, p. 7. The fallback is unused under uniqueness. -/
noncomputable def fixedPoint {X : Type*} [Nonempty X] (f : X → X) : X := by
  classical
  exact if h : ∃ x, f x = x then h.choose else Classical.choice inferInstance

/-- The set of all possible answers of a family, Theorem 1.1, pp. 4, 10. -/
def possibleAnswers {X : Type*} [Nonempty X] (F : Set (X → X)) : Set X :=
  Set.range (fun f : F => fixedPoint f.val)

end TarskiBootstrap.Dimensional


