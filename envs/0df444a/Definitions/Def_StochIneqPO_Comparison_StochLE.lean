-- Prove2me | Definitions.Def_StochIneqPO_Comparison_StochLE
-- name    : StochIneqPO_Comparison_StochLE
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T11:58:12.147904+00:00
-- url     : https://prove2.me/theorems/eb8faec1-10a9-47ec-b815-57464669b816
-- title:
--   Sec. 1, p. 899 — the stochastic order $P_1 \prec P_2$ on a partially ordered Polish space
-- statement:
--   Let $E$ be a measurable space carrying a preorder $\le$ (in the paper: a Polish space with a closed partial order and its Borel $\sigma$-algebra). Write $\mathcal I^*(E)$ for the set of **bounded increasing** real functions on $E$, i.e. measurable $f : E \to \mathbb R$ with $\sup_x |f(x)| < \infty$ and $x \le y \Rightarrow f(x) \le f(y)$.
--
--   For measures $P_1, P_2$ on $E$, $P_1$ is **stochastically smaller** than $P_2$, written $P_1 \prec P_2$, if
--   $$\int f\,dP_1 \le \int f\,dP_2 \qquad \text{for all } f \in \mathcal I^*(E).$$
--
--   This is the order studied throughout the paper; every result of the mission compares measures through it.
--
--   **Formalization Note** The definition is stated for arbitrary measures under the minimal structure (a measurable space with a preorder), so that it applies verbatim to finite products, the countable product and $E \times E$; every theorem adds the hypothesis that the measures are probability measures and that $E$ is a partially ordered Polish space. Boundedness is $\exists C,\ \forall x,\ |f(x)| \le C$; measurability of $f$ is the paper's standing convention (Sec. 1). The paper's equivalent formulation through increasing sets is *not* used as the definition.
-- source:
--   Kamae, Krengel, O'Brien, Stochastic Inequalities on Partially Ordered Spaces, Ann. Probab. 5 (1977), Sec. 1, p. 899 (PDF p. 1)

import Mathlib

namespace StochIneqPO.Comparison

open MeasureTheory

/-- The stochastic order of Kamae–Krengel–O'Brien (1977), Sec. 1, p. 899:
`StochLE P₁ P₂` (written `P₁ ≺ P₂`) iff `∫ f dP₁ ≤ ∫ f dP₂` for every bounded, measurable,
increasing `f : E → ℝ`. Probability-ness of `P₁`, `P₂` is a separate hypothesis of each theorem. -/
def StochLE {E : Type*} [MeasurableSpace E] [Preorder E] (P₁ P₂ : Measure E) : Prop :=
  ∀ f : E → ℝ, Measurable f → Monotone f → (∃ C : ℝ, ∀ x, |f x| ≤ C) →
    ∫ x, f x ∂P₁ ≤ ∫ x, f x ∂P₂

end StochIneqPO.Comparison


