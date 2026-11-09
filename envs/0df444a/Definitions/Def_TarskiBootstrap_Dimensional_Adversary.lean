-- Prove2me | Definitions.Def_TarskiBootstrap_Dimensional_Adversary
-- name    : TarskiBootstrap_Dimensional_Adversary
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T07:09:21.892222+00:00
-- url     : https://prove2.me/theorems/72792f4b-28c9-43e8-babd-348c809e8aa6
-- title:
--   Nonnegative adversary matrix
-- statement:
--   Let $S$ be an input set with answer map $\Phi:S\to O$. A real matrix $\Gamma$ indexed by $S\times S$ is a **nonnegative adversary matrix** when it is symmetric, has nonnegative entries, and
--
--   $$\Phi(f)=\Phi(g)\implies\Gamma[f,g]=0.$$
--
--   The answer type is unrestricted. There is no positive semidefinite or nonzero requirement. The definition applies to grid-valued answers and keeps distinct inputs with shared fixed-point answers distinct.
-- source:
--   Li, Ma, Yang and Zhao, Bootstrapping Classical and Quantum Query Lower Bounds for Finding Tarski Fixed Points, STOC 2027 submission #6 (2026), frozen preprint, Definition 2.4, equation (2.6), PDF/printed p. 7, SHA-256 320afa8333f95589a388b30ffbfd6d7b7e5d93cdf07fa8630825fbf7d0107d59; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/6.pdf. No arXiv identifier/version supplied.

import Mathlib

open scoped Matrix

namespace TarskiBootstrap.Dimensional

/-- Definition 2.4, p. 7, with unrestricted answer alphabet. -/
def NonnegativeAdversary {S O : Type*} (answer : S → O)
    (Γ : Matrix S S ℝ) : Prop :=
  (∀ f g, 0 ≤ Γ f g) ∧ Γ.IsSymm ∧ ∀ f g, answer f = answer g → Γ f g = 0

end TarskiBootstrap.Dimensional


