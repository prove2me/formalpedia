-- Prove2me | Definitions.Def_OptimalSignalEnsembles_chiStar
-- name    : OptimalSignalEnsembles_chiStar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:18:38.751343+00:00
-- url     : https://prove2.me/theorems/1591dece-bfb1-46e9-a5ac-0554f2e086c3
-- title:
--   Maximal Holevo quantity $\chi^*(A)$ of a set of states
-- statement:
--   For a set $A$ of density matrices on $\mathbb C^d$, $\chi^*(A)$ is the supremum of the Holevo quantity over all finite ensembles of $A$-states:
--
--   $$\chi^*(A) \;=\; \sup\Big\{\, \chi(p,\rho) \;:\; n \in \mathbb N,\ (p_k,\rho_k)_{k=1}^n \text{ a finite ensemble of } A\text{-states} \Big\} \in [-\infty, +\infty].$$
--
--   The paper writes "the maximum of $\chi$ for a given set $A$ of available states"; for $A$ the output set of a channel it is the one-shot classical capacity of the channel.
--
--   **Formalization Note** The supremum is taken in the extended reals `EReal`, so that the definition is meaningful before attainment is known; attainment is a separate theorem (`exists_chiOptimal`). For empty $A$ there is no ensemble and the value is $-\infty$.
-- source:
--   Schumacher–Westmoreland, Optimal signal ensembles, arXiv:quant-ph/9912122v1, Sec. 3, p.3; Sec. 5, p.7

import Mathlib
import Definitions.Def_OptimalSignalEnsembles_IsEnsemble
import Definitions.Def_OptimalSignalEnsembles_holevoChi

namespace OptimalSignalEnsembles

/-- `χ*(A)`, the **maximal Holevo quantity** over finite ensembles of `A`-states:
the supremum of `χ` over all `n`, all probability vectors `p : Fin n → ℝ` and all
`ρ : Fin n → A`.

Schumacher–Westmoreland, *Optimal signal ensembles*, arXiv:quant-ph/9912122v1, Sec. 3, p.3
("We will denote the maximum of χ for a given set A of available states by χ∗") and Sec. 5,
p.7 ("Denote max χ by χ∗").

**Formalization Note.** The paper writes "maximum"; it is defined here as the supremum in
`EReal`, so that it is meaningful before attainment is known (attainment is a separate
statement). For empty `A` there is no ensemble and the value is `⊥`. -/
noncomputable def chiStar {d : Type} [Fintype d] [DecidableEq d] (A : Set (Matrix d d ℂ)) :
    EReal :=
  ⨆ (n : ℕ) (p : Fin n → ℝ) (ρ : Fin n → Matrix d d ℂ) (_ : IsEnsemble A p ρ),
    (holevoChi p ρ : EReal)

end OptimalSignalEnsembles


