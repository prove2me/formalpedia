-- Prove2me | Definitions.Def_OptimalSignalEnsembles_IsChiOptimal
-- name    : OptimalSignalEnsembles_IsChiOptimal
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:19:41.596994+00:00
-- url     : https://prove2.me/theorems/41123c00-1736-48cf-8ee1-48f90dfcb248
-- title:
--   $\chi$-optimal ensemble
-- statement:
--   A finite ensemble $(p_k,\rho_k)$ is **$\chi$-optimal** for a set $A$ of states if it is an ensemble of $A$-states and its Holevo quantity attains the maximum:
--
--   $$\chi(p,\rho) = \chi^*(A).$$
--
--   Its average state is denoted $\rho^*$. The properties of $\chi$-optimal ensembles (maximal distance, equal distance, the min-max formula) are the main results of the paper.
--
--   **Formalization Note** The equality is in `EReal`; it forces $\chi^*(A)$ to be a finite real number that is attained.
-- source:
--   Schumacher–Westmoreland, Optimal signal ensembles, arXiv:quant-ph/9912122v1, Sec. 3, p.3; Sec. 5, p.7

import Mathlib
import Definitions.Def_OptimalSignalEnsembles_chiStar

namespace OptimalSignalEnsembles

/-- `IsChiOptimal A p ρ`: `(p, ρ)` is a **χ-optimal ensemble** for `A` — a finite ensemble of
`A`-states whose Holevo quantity equals `χ*(A)`.

Schumacher–Westmoreland, *Optimal signal ensembles*, arXiv:quant-ph/9912122v1, Sec. 3, p.3
("Any ensemble of signal states that achieves this value of the Holevo bound will be called an
optimal signal ensemble") and Sec. 5, p.7 ("the ensemble of A-states for which χ takes on its
maximum value. Call this the “χ-optimal ensemble”").

**Formalization Note.** The equality is in `EReal`; it forces `χ*(A)` to be a finite real number
that is attained. -/
def IsChiOptimal {d : Type} [Fintype d] [DecidableEq d] (A : Set (Matrix d d ℂ)) {n : ℕ}
    (p : Fin n → ℝ) (ρ : Fin n → Matrix d d ℂ) : Prop :=
  IsEnsemble A p ρ ∧ (holevoChi p ρ : EReal) = chiStar A

end OptimalSignalEnsembles


