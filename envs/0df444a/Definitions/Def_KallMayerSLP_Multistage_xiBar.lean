-- Prove2me | Definitions.Def_KallMayerSLP_Multistage_xiBar
-- name    : KallMayerSLP_Multistage_xiBar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:16:04.203875+00:00
-- url     : https://prove2.me/theorems/e1d0070c-e08e-45db-b69a-ddf35187d957
-- title:
--   Conditional mean $\bar\xi^n_t$ of a cell
-- statement:
--   For a node $n$ of stage $t$ with cell $\Xi^t_n$,
--   $$
--   \bar\xi^n_t:=\mathbb E[\xi_t\mid\xi_t\in\Xi^t_n].
--   $$
--
--   **Formalization Note** Written as $\mathbb P(\xi_t\in\Xi^t_n)^{-1}\int_{\{\xi_t\in\Xi^t_n\}}\xi_t\,d\mathbb P$. On a null cell the book's conditional mean is undefined and this is $0$; such a node has $p_n=0$, and the value of (3.14) does not depend on this choice.
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 3, p.263 (PDF 272)

import Mathlib
import Definitions.Def_KallMayerSLP_Multistage_ScenarioTree

namespace KallMayerSLP.Multistage

open MeasureTheory

/-- The conditional mean `ξ̄^n_t := 𝔼[ξ_t | ξ_t ∈ Ξ^t_n]` of a node `n` of stage `t` (Kall & Mayer,
*Stochastic Linear Programming* (2005), Chapter 3, p.263, PDF 272).

**Formalization Note.** Explicitly `ℙ(ξ_t ∈ Ξ^t_n)⁻¹ • ∫_{ξ_t ∈ Ξ^t_n} ξ_t dP`. On a `P`-null cell
the book's conditional mean is undefined and this is `0`, Lean's `0⁻¹ = 0`. Such a node has
`p_n = 0`, so it carries no weight in (3.14) and its constraints are met by complete recourse; the
value of (3.14) does not depend on this choice. Bounded `ξ_t` (Assumption 3.2) makes the integral
genuine. -/
noncomputable def xiBar {D : MSLP} {Ξ : ∀ t, Set (Fin (D.r t) → ℝ)} (𝒯 : ScenarioTree D Ξ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (ξ : ∀ t, Ω → Fin (D.r t) → ℝ)
    (t : ℕ) (n : 𝒯.Node t) : Fin (D.r t) → ℝ :=
  (P.real (ξ t ⁻¹' 𝒯.cell t n))⁻¹ • ∫ ω in ξ t ⁻¹' 𝒯.cell t n, ξ t ω ∂P

end KallMayerSLP.Multistage


