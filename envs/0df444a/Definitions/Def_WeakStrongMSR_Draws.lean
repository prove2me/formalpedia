-- Prove2me | Definitions.Def_WeakStrongMSR_Draws
-- name    : WeakStrongMSR_Draws
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T08:25:33.096416+00:00
-- url     : https://prove2.me/theorems/aed3d95c-2dcf-4682-ba4c-c17f165279bc
-- title:
--   Independent and sequential draws
-- statement:
--   The law of $m$ draws is a probability distribution on lists, the first draw first. In **sequential draws** with kernel $\kappa$, the next draw has law $\kappa(\mathrm{hist})$, where $\mathrm{hist}$ is the list of earlier draws. **Independent draws** from $p$ is the case $\kappa\equiv p$. The independent outcomes of a list of laws are their product, in order.
--
--   These are the draw models of Lemma 3.11 and of the sampling step (Algorithm 1).
-- source:
--   Friggstad–Jamshidian–Vakilian, Minimum Sum-of-Radii Clustering with Strong and Weak Oracles (manuscript, STOC 2027 submission, sha256 5f8fbaf3…67e8f92a0), Lemma 3.11, p.13 (PDF 14); Algorithm 1, p.9 (PDF 10)

import Mathlib

set_option autoImplicit false

namespace WeakStrongMSR

/-!
# Independent and sequential draws

Friggstad–Jamshidian–Vakilian, *Minimum Sum-of-Radii Clustering with Strong and Weak Oracles*
(manuscript, sha256 5f8fbaf3…67e8f92a0), Lemma 3.11, p.13 ("In 2m independent draws from p …
sequential draws whose conditional probability of each outcome is always at most 1/(8m)");
Algorithm 1, p.9 ("Draw h independent samples").

**Formalization Note.** The law of a sequence of draws is a `PMF` on lists, the first draw first.
In `seqDraws κ m` each draw has the law `κ hist`, where `hist` is the list of the earlier draws;
`iidDraws p m` is `m` independent draws from `p`. -/

/-- `m` sequential draws: the next draw has the law `κ hist`, `hist` the earlier draws in order. -/
noncomputable def seqDraws {α : Type*} (κ : List α → PMF α) : ℕ → PMF (List α)
  | 0 => PMF.pure []
  | m + 1 => (seqDraws κ m).bind (fun l => (κ l).map (fun x => l ++ [x]))

/-- `m` independent draws from `p`. -/
noncomputable def iidDraws {α : Type*} (p : PMF α) : ℕ → PMF (List α)
  | 0 => PMF.pure []
  | m + 1 => (iidDraws p m).bind (fun l => p.map (fun x => l ++ [x]))

/-- Independent outcomes of a list of laws, in order. -/
noncomputable def seqLaw {α : Type*} : List (PMF α) → PMF (List α)
  | [] => PMF.pure []
  | μ :: rest => μ.bind (fun a => (seqLaw rest).map (fun l => a :: l))

end WeakStrongMSR


