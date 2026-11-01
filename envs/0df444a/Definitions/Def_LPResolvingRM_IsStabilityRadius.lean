-- Prove2me | Definitions.Def_LPResolvingRM_IsStabilityRadius
-- name    : LPResolvingRM_IsStabilityRadius
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T14:40:58.464083+00:00
-- url     : https://prove2.me/theorems/9df456de-5e44-4a17-b157-6b1f55c299a6
-- title:
--   Stability radius $L$ of the fluid LP (the property of Lemma 1)
-- statement:
--   A number $L$ is a **stability radius** of the instance when, for the optimal solution $y^*$ of (6) with binding set $\mathcal I^*$ and non-binding set $\mathcal I'$, and for all perturbed data $(\hat\mu,\hat C,\hat b)$ with
--   $$\max\Big\{\|\hat C-C\|_\infty,\ \|\hat\mu-\mu\|_\infty,\ \max_{i\in\mathcal I^*}|b_i-\hat b_i|,\ \max_{i\in\mathcal I'}(b_i-\hat b_i)\Big\}\le L,$$
--   the perturbed LP
--   $$\max\ \hat\mu^\top y\quad\text{s.t.}\quad \hat Cy+s=\hat b,\quad y+z=\mathbf1,\quad y,s,z\ge0 \tag{8}$$
--   has a unique optimal solution $(\hat y,\hat s,\hat z)$, with the same nonzero coordinates as $(y^*,s^*,z^*)$ (the same basis) and the same binding constraints ($\hat s_i=0$ iff $i\in\mathcal I^*$). Here $\mu,C$ are the normalized data.
--
--   Lemma 1 asserts that some $L>0$ is a stability radius; the regret bounds are expressed in terms of such an $L$.
--
--   **Formalization Note** $\|\hat C-C\|_\infty$ is the entrywise maximum, as the proofs use it. Uniqueness is from Appendix E.2.
-- source:
--   Chen, Li, Ye, An Improved Analysis of LP-based Control for Revenue Management, arXiv:2101.11092v3, Lemma 1, p.9; Appendix E.2, p.50

import Definitions.Def_LPResolvingRM_Assumption2

open scoped Classical

namespace LPResolvingRM

/-- **Stability radius of the fluid LP** (arXiv:2101.11092v3, Lemma 1, p.9, with Appendix E.2,
p.50). `L` is a stability radius when, for every optimal solution `y*` of LP (6) with binding set
`I*` and non-binding set `I'`, and every perturbed data `(μ̂, Ĉ, b̂)` with

`max{‖Ĉ − C‖_∞, ‖μ̂ − μ‖_∞, max_{i∈I*}|b_i − b̂_i|, max_{i∈I'}(b_i − b̂_i)} ≤ L`,

the perturbed LP (8) `max μ̂ᵀy s.t. Ĉy + s = b̂, y + z = 1, y, s, z ≥ 0` has a **unique** optimal
solution `(ŷ, ŝ, ẑ)`, which has the same basis as `(y*, s*, z*)` (the same nonzero coordinates
among the `2n + m` variables) and the same set of binding constraints (`ŝ_i = 0` iff `i ∈ I*`).
Here `μ` and `C` are the normalized data `p_jμ_j`, `p_jc_{ij}`.

**Formalization Note.** Lemma 1 says such an `L > 0` exists; the paper's later results use only
this property of `L` (reading R1 of the mission). "Unique" is from E.2 ("the optimal solution to
LP (8) is unique and it shares the same optimal basis and binding/non-binding structure", p.50).
`‖Ĉ − C‖_∞` is the entrywise maximum (reading R3: the proof of Proposition 2, p.24, and E.2 bound
it entrywise). Under Assumption 2 the optimal `y*` is unique, so the quantifier over `y*` is over
one point. -/
def IsStabilityRadius {n m : ℕ} (I : Instance n m) (L : ℝ) : Prop :=
  ∀ ystar, LPAllocRM.IsLPOptimal (normC I) I.b 1 (normMu I) ystar →
  ∀ (μh : Fin n → ℝ) (Ch : Matrix (Fin m) (Fin n) ℝ) (bh : Fin m → ℝ),
    (∀ i j, |Ch i j - normC I i j| ≤ L) → (∀ j, |μh j - normMu I j| ≤ L) →
    (∀ i ∈ binding I ystar, |I.b i - bh i| ≤ L) → (∀ i ∉ binding I ystar, I.b i - bh i ≤ L) →
    ∃ yh, LPAllocRM.IsLPOptimal Ch bh 1 μh yh ∧
      (∀ y', LPAllocRM.IsLPOptimal Ch bh 1 μh y' → y' = yh) ∧
      (∀ j, yh j ≠ 0 ↔ ystar j ≠ 0) ∧
      (∀ i, slack Ch bh yh i ≠ 0 ↔ slack (normC I) I.b ystar i ≠ 0) ∧
      (∀ j, 1 - yh j ≠ 0 ↔ 1 - ystar j ≠ 0) ∧
      (∀ i, slack Ch bh yh i = 0 ↔ i ∈ binding I ystar)

end LPResolvingRM


