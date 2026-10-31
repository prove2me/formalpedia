-- Prove2me | Definitions.Def_KallMayerSLP_Multistage_Assumption32
-- name    : KallMayerSLP_Multistage_Assumption32
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:14:51.256486+00:00
-- url     : https://prove2.me/theorems/f37bc24c-aab4-433f-a6b7-7dbe09cb5111
-- title:
--   Assumption 3.2
-- statement:
--   For the problem data of (3.10), random vectors $\xi_t:\Omega\to\mathbb R^{r_t}$ on a probability space and sets $\Xi^t\subset\mathbb R^{r_t}$, **Assumption 3.2** asks that:
--
--   1. only the right-hand sides $b_t$ are random, and linear affine in $\zeta_t$;
--   2. the distributions of the $\xi_t$ are bounded within intervals: each $\Xi^t$ is a bounded interval and $\xi_t\in\Xi^t$ almost surely;
--   3. the random vectors $\xi_2,\dots,\xi_T$ are stochastically independent;
--   4. the $A_{tt}$ are complete fixed recourse matrices.
--
--   This is the hypothesis under which aggregation gives a lower bound. Example 3.1 shows that the independence item cannot be dropped.
--
--   **Formalization Note** Item 1 is built into the structure `MSLP`. The book writes $\operatorname{supp}\mathbb P_{\xi_t}\subseteq\Xi^t$, which implies the almost sure form used here and is equivalent to it when $\Xi^t$ is closed. Item 4, printed "$\forall t$", is read as $t=2,\dots,T$: $A_{11}$ is not a recourse matrix, and the book's Example 3.1, a "complete fixed recourse problem", has a first stage that is not complete.
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 3, Assumption 3.2, p.262 (PDF 271)

import Mathlib
import Definitions.Def_KallMayerSLP_Multistage_MSLP
import Definitions.Def_KallMayerSLP_Multistage_IsCompleteRecourse
import Definitions.Def_KallMayerSLP_Multistage_IsInterval

namespace KallMayerSLP.Multistage

open MeasureTheory ProbabilityTheory

/-- **Assumption 3.2** (Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3, p.262,
PDF 271), for the problem data `D`, random vectors `ξ_t` on `(Ω, P)` and intervals `Ξ^t`:

* only the right-hand sides `b_t` are random, and linear affine in `ζ_t`: built into `MSLP`;
* the `ξ_t`, `t = 2, …, T`, are random vectors (measurable);
* the distributions of the `ξ_t` are bounded within intervals `Ξ^t`: each `Ξ^t` is a bounded
  interval and `ξ_t ∈ Ξ^t` almost surely;
* `ξ_2, …, ξ_T` are stochastically independent;
* the `A_tt` are complete fixed recourse matrices.

**Formalization Note.** The book's `supp ℙ_{ξ_t} ⊆ Ξ^t` implies `ξ_t ∈ Ξ^t` a.s., and is equivalent
to it when `Ξ^t` is closed; the a.s. form is what is stated. "The `A_tt` … `∀t`" is read as
`t = 2, …, T`: `A_11` is not a recourse matrix, and the book's own Example 3.1 (p.257, PDF 266),
called a "complete fixed recourse problem", has a first stage that is not complete. -/
structure Assumption32 (D : MSLP) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ξ : ∀ t, Ω → Fin (D.r t) → ℝ) (Ξ : ∀ t, Set (Fin (D.r t) → ℝ)) : Prop where
  measurable_xi : ∀ t, 2 ≤ t → t ≤ D.T → Measurable (ξ t)
  isInterval : ∀ t, 2 ≤ t → t ≤ D.T → IsInterval (Ξ t)
  isBounded : ∀ t, 2 ≤ t → t ≤ D.T → Bornology.IsBounded (Ξ t)
  ae_mem : ∀ t, 2 ≤ t → t ≤ D.T → ∀ᵐ ω ∂P, ξ t ω ∈ Ξ t
  indep : iIndepFun (fun s : Set.Icc 2 D.T => ξ s) P
  complete : ∀ t, 2 ≤ t → t ≤ D.T → IsCompleteRecourse (D.A t t)

end KallMayerSLP.Multistage


