-- Prove2me | Definitions.Def_ReflectedBSDE_Obstacle_Subjet
-- name    : ReflectedBSDE_Obstacle_Subjet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:13:31.907987+00:00
-- url     : https://prove2.me/theorems/ce58fb51-e106-407c-89ca-cc61814ef6ac
-- title:
--   Parabolic subjet
-- statement:
--   At an interior point $(t,x)$, the parabolic subjet of $u$ consists of symmetric triples $(p,q,X)$ for which, as $(s,y)\to(t,x)$ within the time strip,
--
--   $$
--   u(s,y)\ge u(t,x)+p(s-t)+\langle q,y-x\rangle+\tfrac12\langle X(y-x),y-x\rangle+o(|s-t|+|y-x|^2).
--   $$
--
--   The remainder is one-sided and local. This definition supplies the test triples for viscosity supersolutions.
-- source:
--   El Karoui, Kapoudjian, Pardoux, Peng & Quenez, Reflected solutions of backward SDE's, and related obstacle problems for PDE's, Ann. Probab. 25(2) (1997), p. 728, Definition 8.1

import Definitions.Def_ReflectedBSDE_Obstacle_Jet

open Filter Topology
open scoped NNReal

namespace ReflectedBSDE.Obstacle

/-- Definition 8.1, parabolic subjet, using the corresponding one-sided
little-o lower remainder. -/
def Subjet {d : ℕ} (T : ℝ≥0) (u : ℝ≥0 → (Fin d → ℝ) → ℝ)
    (t : ℝ≥0) (x : Fin d → ℝ) (j : Jet d) : Prop :=
  0 < t ∧ t < T ∧
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ z : ℝ≥0 × (Fin d → ℝ) in
      nhdsWithin (t, x) (Set.Ioo 0 T ×ˢ Set.univ),
      (u t x + j.p * ((z.1 : ℝ) - t) +
        (∑ i, j.q i * (z.2 i - x i)) +
        (1 / 2 : ℝ) * (∑ i, ∑ k, j.X i k * (z.2 k - x k) * (z.2 i - x i))) - u z.1 z.2 ≤
        ε * (|((z.1 : ℝ) - t)| + ∑ i, (z.2 i - x i) ^ 2)

end ReflectedBSDE.Obstacle


