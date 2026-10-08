-- Prove2me | Definitions.Def_RobustPower_StochGap_SymmetricMeasure
-- name    : RobustPower_StochGap_SymmetricMeasure
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T17:14:40.278188+00:00
-- url     : https://prove2.me/theorems/9e5bae1b-9c45-4b06-a085-42833e852481
-- title:
--   Definition 1.4 — symmetric probability measure on a symmetric set
-- statement:
--   Let $P\subseteq\mathbb R^n$ be symmetric with point of symmetry $u^0$ (Definition 1.2). A probability measure $\mu$ on $P$ is **symmetric** if
--   $$\mu(S)=\mu(\hat S)\quad\text{for every } S\subseteq P,\qquad \hat S=\{2u^0-x : x\in S\}.$$
--   The uniform distribution on a bounded symmetric set is an example. Lemma 2.1 shows that the mean of a symmetric measure is the point of symmetry, so such measures satisfy condition (2.1) of Theorem 2.1.
--
--   **Formalization Note** A measure "on $P$" is encoded as a measure on $\mathbb R^n$ (`Fin n → ℝ`, Borel) that gives $P^{\mathrm c}$ measure zero. The equality $\mu(S)=\mu(\hat S)$ is required for measurable $S\subseteq P$, the sets on which a measure is defined; the predicate also records that $P$ is symmetric about $u^0$.
-- source:
--   Bertsimas & Goyal, On the Power of Robust Solutions in Two-Stage Stochastic and Adaptive Optimization Problems, authors' manuscript (MIT DSpace) of Math. Oper. Res. DOI 10.1287/moor.1090.0440, p. 6, Definition 1.4

import Mathlib
import Definitions.Def_RobustPower_StochGap_SymmetricSets

open MeasureTheory

namespace RobustPower.StochGap

/-- Definition 1.4 (p. 6): a probability measure `μ` on the symmetric set `P ⊆ ℝⁿ` with point of
symmetry `u⁰` is symmetric if `μ(S) = μ(Ŝ)` for every (measurable) `S ⊆ P`, where
`Ŝ = {2u⁰ - x | x ∈ S}`. "A measure on `P`" is encoded as a measure on `ℝⁿ` that gives `Pᶜ`
measure zero. -/
def IsSymmetricMeasure {n : ℕ} (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (P : Set (Fin n → ℝ))
    (u₀ : Fin n → ℝ) : Prop :=
  IsSymmetricAbout P u₀ ∧ μ Pᶜ = 0 ∧
    ∀ S : Set (Fin n → ℝ), S ⊆ P → MeasurableSet S →
      μ S = μ ((fun x => (2 : ℝ) • u₀ - x) '' S)

end RobustPower.StochGap


