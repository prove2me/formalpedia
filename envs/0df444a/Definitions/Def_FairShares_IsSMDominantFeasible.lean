-- Prove2me | Definitions.Def_FairShares_IsSMDominantFeasible
-- name    : FairShares_IsSMDominantFeasible
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:15:50.666571+00:00
-- url     : https://prove2.me/theorems/48c8def7-fbe9-48bc-930d-2532d16358ef
-- title:
--   SM-dominant feasible share
-- statement:
--   A share $s$ for the class $\mathcal C$ that is feasible for $\mathcal C$ is an **SM-dominant feasible share** if it dominates on $\mathcal C$ every share $s'$ for $\mathcal C$ that is both feasible and self-maximizing for $\mathcal C$. The share $s$ itself need not be self-maximizing.
--
--   **Formalization Note** The source's "every other" share is rendered as "every" share: domination is reflexive, so the two readings agree.
-- source:
--   Babaioff & Feige, Fair Shares: Feasibility, Domination and Incentives, arXiv:2205.07519v1, §3.3, pp.13–14

import Mathlib
import Definitions.Def_FairShares_IsShare
import Definitions.Def_FairShares_Feasible
import Definitions.Def_FairShares_SelfMax
import Definitions.Def_FairShares_Dominates

namespace FairShares

/-- **SM-dominant feasible share.**
Babaioff & Feige, *Fair Shares: Feasibility, Domination and Incentives*, arXiv:2205.07519v1, §3.3, pp.13–14: "We say that a feasible share s is a SM-dominant feasible share for a class
of valuations functions C, if for the class C it dominates every other feasible and
self-maximizing (SM) share s′."

`IsSMDominantFeasible C s`: `s` is a share for `C`, feasible for `C`, and dominates on `C` every
share `s'` for `C` that is feasible and self-maximizing for `C`.

**Formalization Note.** "every other" is rendered as "every": domination is reflexive, so
including `s' = s` changes nothing. `s` itself is not required to be self-maximizing. -/
def IsSMDominantFeasible (C : (m : ℕ) → Set (Finset (Fin m) → ℝ))
    (s : (m n : ℕ) → (Finset (Fin m) → ℝ) → ℝ) : Prop :=
  IsShare C s ∧ Feasible C s ∧
    ∀ s' : (m n : ℕ) → (Finset (Fin m) → ℝ) → ℝ,
      IsShare C s' → Feasible C s' → SelfMax C s' → Dominates C s s'

end FairShares


