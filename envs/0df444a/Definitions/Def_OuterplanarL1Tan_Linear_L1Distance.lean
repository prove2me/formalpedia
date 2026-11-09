-- Prove2me | Definitions.Def_OuterplanarL1Tan_Linear_L1Distance
-- name    : OuterplanarL1Tan_Linear_L1Distance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:01:12.386416+00:00
-- url     : https://prove2.me/theorems/a1f243d2-b3eb-49f6-8381-8a119df61044
-- title:
--   Pullback distances from full real summable sequences
-- statement:
--   A real-valued distance function $\delta$ on a set $X$ is an $\ell_1$ pullback distance if there is a map $f$ from $X$ into the space of all absolutely summable real sequences such that
--
--   $$\delta(x,y)=\|f(x)-f(y)\|_1\qquad(x,y\in X).$$
--
--   No finite-support condition is imposed on $f$. The map may identify distinct points; this includes every $\ell_1$ metric and also the pseudometrics needed for the pullback by $g_H$ in §3.3. Prescribed norms need not be constant on zero-distance classes.
--
--   This is an independent general object for localization. It assumes neither a cut representation nor the existence of a norm-prescribing output map.
--
--   **Formalization Note** The sequence space is Mathlib's `lp (fun _ : ℕ => ℝ) 1`, whose elements already satisfy summability. The finite-set restriction appears in Lemma 6, not in this definition. In particular no Bochner integral or finite-dimensional input truncation changes the domain.
-- source:
--   Zihan Tan, Improved Embedding of k-Outerplanar Metrics into ℓ₁, STOC 2027 submission #262 (October 2026), p. 5–7, §3.2 Lemma 6 and §3.3 pullback δ_H (PDF p. 6–8); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/262.pdf; SHA256 0ec64e77e85f536fdf7dc42bb8fdeedaf8861f751861d02b2d5edbdef75ee0ab

import Mathlib

namespace OuterplanarL1Tan.Linear

/-- An ℓ₁ pullback distance from actual summable real sequences. It can be a
pseudometric: no injectivity, finite support, or cut representation is assumed. -/
def IsL1Distance {X : Type} (δ : X → X → ℝ) : Prop :=
  ∃ f : X → lp (fun _ : ℕ => ℝ) 1, ∀ x y, δ x y = ‖f x - f y‖

end OuterplanarL1Tan.Linear


