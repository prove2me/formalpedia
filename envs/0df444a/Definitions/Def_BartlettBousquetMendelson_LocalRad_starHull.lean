-- Prove2me | Definitions.Def_BartlettBousquetMendelson_LocalRad_starHull
-- name    : BartlettBousquetMendelson_LocalRad_starHull
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:57:29.735601+00:00
-- url     : https://prove2.me/theorems/0fb0258b-e8c6-4992-a654-d532ab0eb4c2
-- title:
--   Star-hull $\mathrm{star}(\mathcal F,f_0)$
-- statement:
--   The **star-hull** of a class $\mathcal F$ around a function $f_0$ is
--
--   $$
--   \mathrm{star}(\mathcal F,f_0)=\{f_0+\alpha(f-f_0):f\in\mathcal F,\ \alpha\in[0,1]\}.
--   $$
--
--   The goal theorem uses $\mathrm{star}(\mathcal F,0)=\{\alpha f:f\in\mathcal F,\alpha\in[0,1]\}$: localizing over the star-hull, rather than over $\mathcal F$, gives the small constants of Theorem 3.3, part 2.
-- source:
--   Bartlett, Bousquet, Mendelson, Local Rademacher Complexities, Ann. Statist. 33(4) (2005), §2, p. 7 (IMS electronic reprint, arXiv:math/0508275v1)

import Mathlib

namespace BartlettBousquetMendelson.LocalRad

/-- **Star-hull `star(F, f₀)`.**
Bartlett, Bousquet, Mendelson, *Local Rademacher Complexities*, Ann. Statist. 33(4) (2005) (IMS electronic reprint, arXiv:math/0508275v1), §2, p. 7: "Recall that the star-hull of F around f0 is defined by
star(F,f0) = {f0 + α(f − f0): f ∈ F, α ∈ [0,1]}."

`starHull F f₀` is the set of functions `f₀ + α (f − f₀)` with `f ∈ F` and `α ∈ [0, 1]`.
The mission uses `starHull F 0 = {α f : f ∈ F, α ∈ [0, 1]}`. -/
def starHull {X : Type*} (F : Set (X → ℝ)) (f₀ : X → ℝ) : Set (X → ℝ) :=
  {g | ∃ f ∈ F, ∃ α ∈ Set.Icc (0 : ℝ) 1, g = f₀ + α • (f - f₀)}

end BartlettBousquetMendelson.LocalRad


