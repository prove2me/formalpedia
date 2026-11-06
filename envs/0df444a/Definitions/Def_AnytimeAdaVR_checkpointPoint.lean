-- Prove2me | Definitions.Def_AnytimeAdaVR_checkpointPoint
-- name    : AnytimeAdaVR_checkpointPoint
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:35:52.534972+00:00
-- url     : https://prove2.me/theorems/17ab9438-9f28-440a-bb3e-8de3a02efeeb
-- title:
--   Published point $Z^{\mathrm{lin}}_n$ at checkpoint $n=2^k$
-- statement:
--   At checkpoint $n=2^k$ the three reports $X_S,X_M,X_D$ (after $n$ local queries) are frozen, and $n$ fresh validation gradients are averaged at each:
--   $$
--   \bar g_i=\frac1n\sum_{j=1}^{n} g(X_i;\xi^{\mathrm{val}}_{i,j}),\qquad i\in\{S,M,D\}.
--   $$
--   The published point is $Z^{\mathrm{lin}}_n=X_{i^*}$, where $i^*$ is the first index in the order S, M, D with minimal $\|\bar g_i\|$.
-- source:
--   Jiang–Wang–Yang–Zhang–Li, Adaptive Variance Reduction across Smoothness and Noise Conditions (preprint, 2026; held artifact sha256 6f3caf41…74006), App. E.1, p.26; Algorithm 4, p.9

import Mathlib
import Definitions.Def_AnytimeAdaVR_pathReport

namespace AnytimeAdaVR

/-- **The point `Z^lin_n` published at checkpoint `n = 2^k`.** Jiang–Wang–Yang–Zhang–Li, *Adaptive Variance Reduction across Smoothness and Noise Conditions*
(preprint, 2026), App. E.1, p.26: "At the end of
round n = 1, 2, 4, …, freeze all three reports X_S, X_M, X_D. During each of rounds n + 1, …, 2n,
collect one fresh validation gradient at each frozen point … Form the three means
ḡ_i = (1/n) Σ_{k=1}^n g(X_i; ξ^val_{i,k}) and publish the candidate with smallest ‖ḡ_i‖ at the end of
round 2n, breaking ties in the order S, M, D." Also Algorithm 4, lines 5, 8, 11, p.9.

`checkpointPoint g xinit k ω` is `X_{i*}` for `n = 2^k`, `X_i = pathReport g xinit i ω n`, the means
over the validation samples `ω.2.2 (i, k, j)`, `j < n`, and `i*` the first of S, M, D with minimal
`‖ḡ_i‖`. -/
noncomputable def checkpointPoint {d : ℕ} {Ξ : Type*}
    (g : EuclideanSpace ℝ (Fin d) → Ξ → EuclideanSpace ℝ (Fin d))
    (xinit : EuclideanSpace ℝ (Fin d)) (k : ℕ) (ω : Tape Ξ) : EuclideanSpace ℝ (Fin d) :=
  let n := 2 ^ k
  let X : Path → EuclideanSpace ℝ (Fin d) := fun i => pathReport g xinit i ω n
  let gbar : Path → EuclideanSpace ℝ (Fin d) := fun i =>
    ((n : ℝ)⁻¹) • ∑ j ∈ Finset.range n, g (X i) (ω.2.2 (i, k, j))
  if ‖gbar .S‖ ≤ ‖gbar .M‖ ∧ ‖gbar .S‖ ≤ ‖gbar .D‖ then X .S
  else if ‖gbar .M‖ ≤ ‖gbar .D‖ then X .M
  else X .D

end AnytimeAdaVR


