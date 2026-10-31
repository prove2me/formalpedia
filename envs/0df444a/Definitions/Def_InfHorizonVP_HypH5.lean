-- Prove2me | Definitions.Def_InfHorizonVP_HypH5
-- name    : InfHorizonVP_HypH5
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:16:28.43359+00:00
-- url     : https://prove2.me/theorems/6c7c8394-3cd7-444f-9fa1-0afa3ad5d0b3
-- title:
--   Hypothesis (H5): measurability of $\Gamma(\cdot,x)$
-- statement:
--   **(H5)** For every $x\in E$ the multifunction $\Gamma(\cdot,x)$ is measurable: for every open $O\subseteq E$, the set $\{t\in\mathbb R_+\mid\Gamma(t,x)\cap O\neq\emptyset\}$ belongs to the Lebesgue $\sigma$-algebra $\mathcal L$.
-- source:
--   Frankowska, Sagara, Value Functions and Optimality Conditions for Nonconvex Variational Problems with an Infinite Horizon in Banach Spaces, arXiv:1801.00400v3, §3.1, p.8, (H5)

import Mathlib
open MeasureTheory Filter Topology Set
open scoped Pointwise

namespace InfHorizonVP

/-- **Hypothesis (H5): `Γ(·, x)` is measurable.**
Frankowska, Sagara, arXiv:1801.00400v3, §3.1, p.8: "For given x ∈ E, the multifunction
Γ(·, x) ⇝ E is said to be measurable if the set {t ∈ R+ | Γ(t, x) ∩ O ≠ ∅} belongs to 𝓛 for every
open subset O of E. … (H5) Γ(·, x) is measurable for every x ∈ E."

**Formalization Note.** "Belongs to the Lebesgue σ-algebra 𝓛" is `NullMeasurableSet` for Lebesgue
measure. -/
def HypH5 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Γ : ℝ → E → Set E) : Prop :=
  ∀ x : E, ∀ O : Set E, IsOpen O →
    NullMeasurableSet {t : ℝ | 0 ≤ t ∧ (Γ t x ∩ O).Nonempty} volume

end InfHorizonVP


