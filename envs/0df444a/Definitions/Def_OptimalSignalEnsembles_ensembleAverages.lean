-- Prove2me | Definitions.Def_OptimalSignalEnsembles_ensembleAverages
-- name    : OptimalSignalEnsembles_ensembleAverages
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:17:57.129074+00:00
-- url     : https://prove2.me/theorems/8654ed56-25a4-4b48-a8e4-23cb0a28935c
-- title:
--   Average states of ensembles of $A$-states
-- statement:
--   For a set $A$ of states, the set of **average states of ensembles of $A$-states** is
--
--   $$\{\, \textstyle\sum_{k=1}^n p_k\rho_k \;:\; n\in\mathbb N,\ (p_k,\rho_k) \text{ a finite ensemble of } A\text{-states} \,\},$$
--
--   that is, the convex hull of $A$. It is the range of the outer minimum in the min-max formula (19).
--
--   **Formalization Note** Ensembles are finite and indexed by $\mathrm{Fin}\,n$, as in `IsEnsemble`.
-- source:
--   Schumacher–Westmoreland, Optimal signal ensembles, arXiv:quant-ph/9912122v1, Min-max formula for χ∗, eq. (19), p.9

import Mathlib
import Definitions.Def_OptimalSignalEnsembles_avgState
import Definitions.Def_OptimalSignalEnsembles_IsEnsemble

namespace OptimalSignalEnsembles

/-- The set of **average states of ensembles of `A`-states**:
`{σ | σ = ∑ₖ pₖ ρₖ for some finite ensemble (p, ρ) of A-states}`
(the convex hull of `A`).

Schumacher–Westmoreland, *Optimal signal ensembles*, arXiv:quant-ph/9912122v1, Min-max formula
for χ∗, eq. (19), p.9 ("the minimum is taken over all average states ρ of ensembles of
A-states").

**Formalization Note.** Ensembles are finite and indexed by `Fin n`, as in
`OptimalSignalEnsembles.IsEnsemble`. -/
def ensembleAverages {d : Type} [Fintype d] (A : Set (Matrix d d ℂ)) : Set (Matrix d d ℂ) :=
  {σ | ∃ (n : ℕ) (p : Fin n → ℝ) (ρ : Fin n → Matrix d d ℂ), IsEnsemble A p ρ ∧ avgState p ρ = σ}

end OptimalSignalEnsembles


