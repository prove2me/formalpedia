-- Prove2me | Definitions.Def_DataDrivenRO_Guarantee_Supplement_LCX
-- name    : DataDrivenRO_Guarantee_Supplement_LCX
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T19:48:27.781857+00:00
-- url     : https://prove2.me/theorems/1903655a-a247-4451-ac1e-748bc012ba3f
-- title:
--   (30)–(31), p. 22 — LCX tests, confidence region and the uncertainty set as printed
-- statement:
--   For data $S=(\hat u^1,\ldots,\hat u^N)$ in $\mathbb R^d$, let $\mathcal B=\{(a,b):\sum_i|a_i|+|b|\le1\}$ and $\Gamma(a,b)=N^{-1}\sum_j(a^T\hat u^j-b)^++g$. The region $\mathcal P^{LCX}$ consists of probability measures satisfying the hinge expectation bounds and the lower second-moment bound of (30). The uncertainty set is exactly the printed (31):
--   $$
--   \mathcal U^{LCX}_\epsilon=\{u:\exists r,\ 1\le z\le1/\epsilon,\quad (a^Tr-b(z-1))^++(a^Tu-b)^+\le(z/N)\sum_j(a^T\hat u^j-b)^++g\ \ \forall(a,b)\in\mathcal B\}.
--   $$
--   This bundle preserves the printed set so that its claimed guarantee and support identity can be tested without silently repairing it.
--
--   **Formalization Note** Coordinates and samples are indexed from zero by `Fin d` and `Fin N`; applications have $N>0$, $g>0$, $g_\sigma\ge0$ and $0<\epsilon<1$. Expectations of nonnegative quantities use extended nonnegative integrals, including infinite second moments. The stray sum over $i$ in (30) is removed: the test immediately above it uses $\mathbb E[u^Tu]$. The additive $g$ in (31b) is deliberately not multiplied by $z$.
-- source:
--   Bertsimas, Gupta & Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, §7, (30)–(31), p. 22; Γ after (EC.9), p. ec6 (PDF 44)

import Mathlib
import Definitions.Def_DataDrivenRO_Guarantee_Setting

open MeasureTheory

namespace DataDrivenRO.Guarantee.Supplement

/-- The compact index set ℬ on p. 22; the norm on a is ℓ¹. -/
def tests (d : ℕ) : Set ((Fin d → ℝ) × ℝ) :=
  {ab | (∑ i, |ab.1 i|) + |ab.2| ≤ 1}

/-- Γ(a,b), defined on p. ec6 after (EC.9). -/
noncomputable def gammaLCX {d N : ℕ} (S : Fin N → (Fin d → ℝ))
    (g : ℝ) (ab : (Fin d → ℝ) × ℝ) : ℝ :=
  (∑ j, max (S j ⬝ᵥ ab.1 - ab.2) 0) / N + g

/-- (30), correcting the extraneous sum over i in the second-moment constraint.
Nonnegative extended expectations retain infinite moments. -/
def regionLCX {d N : ℕ} (S : Fin N → (Fin d → ℝ)) (g gs : ℝ) :
    Set (Measure (Fin d → ℝ)) :=
  {P | IsProbabilityMeasure P ∧
    (∀ ab ∈ tests d,
      (∫⁻ u, ENNReal.ofReal (max (u ⬝ᵥ ab.1 - ab.2) 0) ∂P) ≤
        ENNReal.ofReal (gammaLCX S g ab)) ∧
    ENNReal.ofReal ((∑ j, ∑ i, (S j i) ^ 2) / N - gs) ≤
      ∫⁻ u, ENNReal.ofReal (∑ i, (u i) ^ 2) ∂P}

/-- Exactly the printed (31): the additive threshold is not multiplied by z. -/
def ULCXPrinted {d N : ℕ} (S : Fin N → (Fin d → ℝ)) (g ε : ℝ) :
    Set (Fin d → ℝ) :=
  {u | ∃ (r : Fin d → ℝ) (z : ℝ), 1 ≤ z ∧ z ≤ 1 / ε ∧
    ∀ ab ∈ tests d,
      max (r ⬝ᵥ ab.1 - ab.2 * (z - 1)) 0 + max (u ⬝ᵥ ab.1 - ab.2) 0 ≤
        (z / N) * (∑ j, max (S j ⬝ᵥ ab.1 - ab.2) 0) + g}

end DataDrivenRO.Guarantee.Supplement


