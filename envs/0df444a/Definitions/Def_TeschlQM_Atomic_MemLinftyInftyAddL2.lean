-- Prove2me | Definitions.Def_TeschlQM_Atomic_MemLinftyInftyAddL2
-- name    : TeschlQM_Atomic_MemLinftyInftyAddL2
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T08:47:29.877809+00:00
-- url     : https://prove2.me/theorems/d0a55ea2-4753-40de-8063-a7a7134c2bb2
-- title:
--   Potentials in L^∞_∞(ℝ^d) + L²(ℝ^d)
-- statement:
--   $L^\infty_\infty(\mathbb R^d)$ denotes the bounded Borel functions on $\mathbb R^d$ which vanish at infinity. A real-valued function $V$ on $\mathbb R^d$ belongs to $L^\infty_\infty(\mathbb R^d) + L^2(\mathbb R^d)$ if
--   $$V = V_1 + V_2, \qquad V_1 \in L^\infty_\infty(\mathbb R^d), \quad V_2 \in L^2(\mathbb R^d).$$
--
--   This is the class of potentials in Kato's theorem (Theorem 11.1); for $d = 3$ it contains the Coulomb potential $\gamma/|x|$ (split at $|x| = 1$).
--
--   **Formalization Note.** Stated for `V : EuclideanSpace ℝ (Fin d) → ℝ` as the existence of `V₁ V₂` with `V x = V₁ x + V₂ x` for every `x`, `V₁` measurable, bounded, and tending to $0$ along the cocompact filter ($|x| \to \infty$), and `MemLp V₂ 2 volume`.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 170, Lemma 7.11, and p. 241, Theorem 11.1

import Mathlib

namespace TeschlQM.Atomic

open MeasureTheory Filter Topology

/-- Teschl, Lemma 7.11 (p. 170) and Theorem 11.1 (p. 241): `V ∈ L^∞_∞(ℝ^d) + L²(ℝ^d)`, where
`L^∞_∞(ℝ^d)` is the space of bounded Borel functions which vanish at infinity: `V = V₁ + V₂` with
`V₁` Borel measurable, bounded and `V₁(x) → 0` as `|x| → ∞`, and `V₂ ∈ L²(ℝ^d)`. -/
def MemLinftyInftyAddL2 {d : ℕ} (V : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ∃ V₁ V₂ : EuclideanSpace ℝ (Fin d) → ℝ, (∀ x, V x = V₁ x + V₂ x) ∧
    Measurable V₁ ∧ (∃ M : ℝ, ∀ x, |V₁ x| ≤ M) ∧ Tendsto V₁ (cocompact _) (𝓝 0) ∧
    MemLp V₂ 2 volume

end TeschlQM.Atomic


