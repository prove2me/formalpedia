-- Prove2me | Definitions.Def_MultiItemRev_BundlingOpt_Bundling
-- name    : MultiItemRev_BundlingOpt_Bundling
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T20:24:49.437105+00:00
-- url     : https://prove2.me/theorems/e0d709d8-4943-4922-bf01-bf6f370d0e2b
-- title:
--   pp. 32, 44–46 — symmetric two-good mechanisms, symmetrization µ̄, the bundled majorant µ̂, the law with density f
-- statement:
--   Objects specific to two goods, from Appendix A.1 and A.6 of Hart and Nisan.
--
--   1. For a two-good valuation $(y, z)$ let $\mathrm{swap}(y,z) = (z,y)$. A two-good mechanism $\mu = (q,s)$ is **symmetric** if $q_1(y,z) = q_2(z,y)$ and $s(y,z) = s(z,y)$ for all $y, z \ge 0$ (p. 32).
--   2. The **symmetrization** $\bar\mu = (\bar q, \bar s)$ of $\mu$ is (p. 32)
--   $$\bar q_1(y,z) = \bar q_2(z,y) = \frac{q_1(y,z) + q_2(z,y)}{2}, \qquad \bar s(y,z) = \frac{s(y,z) + s(z,y)}{2}.$$
--   3. Given $a \ge 0$, the **bundled majorant** $\hat\mu = (\hat q, \hat s)$ of $\mu$ (pp. 45–46) is defined with $t = y + z - a$ by
--   $$\hat q(y,z) = \bigl(q_1(t, a),\, q_1(t, a)\bigr), \qquad \hat s(y,z) = \hat q(y,z)\cdot(y,z) - b(t, a),$$
--   where $b$ is the buyer payoff of $\mu$. Its buyer payoff is $\hat b(y,z) = b(y+z-a, a)$, and $\hat q, \hat s$ depend on $(y,z)$ only through $y + z$.
--   4. For a function $f$ on $\mathbb{R}$, the law with Lebesgue density $f$ is the image of the measure $f(x)\,dx$ under $x \mapsto \max(x, 0)$, a measure on $\mathbb{R}_+$; when $f \ge 0$ vanishes on $(-\infty, 0)$ and integrates to $1$ this is the law on $\mathbb{R}_+$ with density $f$.
--
--   The bundled majorant is the bundled mechanism that the proof of Theorem 16 compares with an arbitrary symmetric mechanism.
--
--   **Formalization Note** The paper defines $\hat\mu$ only on the quadrant $[a,\infty)^2$, where $y + z - a \ge a$. Off the quadrant the Lean definition truncates $y + z - a$ at $0$ (subtraction in $\mathbb{R}_{\ge 0}$); this region carries no mass in Theorem 16 and no statement of the mission uses $\hat\mu$ there except through its revenue. The law with density $f$ is the pushforward of $f\,dx$ on $\mathbb{R}$ under $x \mapsto \max(x,0)$, which loses nothing when $f = 0$ below $a > 0$.
-- source:
--   Hart and Nisan, Approximate Revenue Maximization with Multiple Items, arXiv:1204.1846v3, p. 32 (symmetric mechanism, symmetrization); pp. 45–46, proof of Theorem 16 (b̂, q̂, ŝ)

import Mathlib
import Definitions.Def_MultiItemRev_BundlingOpt_Model
open MeasureTheory
open scoped NNReal ENNReal

namespace MultiItemRev.BundlingOpt

/-- The swap `(y, z) ↦ (z, y)` of a two-good valuation. -/
def swap2 (x : Fin 2 → ℝ≥0) : Fin 2 → ℝ≥0 :=
  x ∘ Equiv.swap 0 1

/-- A symmetric two-good mechanism (p. 32): `q₁(y, z) = q₂(z, y)` and `s(y, z) = s(z, y)`. -/
def IsSymmetric (M : Mechanism (Fin 2)) : Prop :=
  ∀ x, M.q x 0 = M.q (swap2 x) 1 ∧ M.s x = M.s (swap2 x)

/-- The symmetrization `µ̄` of a two-good mechanism (p. 32):
`q̄₁(y, z) = q̄₂(z, y) = (q₁(y, z) + q₂(z, y))/2`, `s̄(y, z) = (s(y, z) + s(z, y))/2`. -/
noncomputable def symmetrize (M : Mechanism (Fin 2)) : Mechanism (Fin 2) where
  q x := ![(M.q x 0 + M.q (swap2 x) 1) / 2, (M.q x 1 + M.q (swap2 x) 0) / 2]
  s x := (M.s x + M.s (swap2 x)) / 2

/-- The bundled majorant `µ̂ = (q̂, ŝ)` of a two-good mechanism `µ` at the level `a` (pp. 45–46):
with `t = y + z − a` (truncated at `0`, exact on the quadrant `[a, ∞)²`),
`q̂(y, z) = (q₁(t, a), q₁(t, a))` and `ŝ(y, z) = q̂(y, z) · (y, z) − b(t, a)`, so that the buyer
payoff of `µ̂` is `b̂(y, z) = b(y + z − a, a)`. -/
noncomputable def bundledMajorant (M : Mechanism (Fin 2)) (a : ℝ≥0) : Mechanism (Fin 2) where
  q x _ := M.q ![x 0 + x 1 - a, a] 0
  s x := (∑ i, M.q ![x 0 + x 1 - a, a] 0 * (x i : ℝ)) - buyerPayoff M ![x 0 + x 1 - a, a]

/-- The one-good law on `ℝ≥0` with Lebesgue density `f` on `ℝ`. -/
noncomputable def densityLaw (f : ℝ → ℝ) : Measure ℝ≥0 :=
  (volume.withDensity (fun x => ENNReal.ofReal (f x))).map Real.toNNReal

end MultiItemRev.BundlingOpt


