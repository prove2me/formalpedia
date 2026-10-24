-- Prove2me | Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_FiniteInf
-- name    : KLS408915f_BrownianMotion_Auxiliary_FiniteInf
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T08:04:26.514309+00:00
-- url     : https://prove2.me/theorems/656afd87-bd76-4850-b0f5-e1089f45232d
-- title:
--   Finite-set infimum comparison
-- statement:
--   Vendored from `RemyDegenne/brownian-motion` at commit `a7ad7af662044313bc80a7c0756360fb3745f931` under Apache-2.0. `Set.Finite.lt_iInf_iff` characterizes $a<\inf_{i∈s}f(i)$ for a nonempty finite set `s` in a complete linear order by the pointwise conditions $a<f(x)$ for every $x∈s$.
-- source:
--   Lean source: https://github.com/RemyDegenne/brownian-motion/blob/a7ad7af662044313bc80a7c0756360fb3745f931/BrownianMotion/Auxiliary/FiniteInf.lean#L57-L61 (repository human-ai-mathematics/kls-lean, commit 408915f, module `BrownianMotion.Auxiliary.FiniteInf`, definition bundle `KLS408915f_BrownianMotion_Auxiliary_FiniteInf`; the repository is private at upload time). Vendored from https://github.com/RemyDegenne/brownian-motion at commit a7ad7af662044313bc80a7c0756360fb3745f931 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Mathlib.Data.Finset.Max
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Order.ConditionallyCompletePartialOrder.Indexed

-- Vendored from https://github.com/RemyDegenne/brownian-motion at commit a7ad7af662044313bc80a7c0756360fb3745f931 (upstream path BrownianMotion/Auxiliary/FiniteInf.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
variable {α ι : Type*} [CompleteLinearOrder α]
lemma Set.Finite.lt_iInf_iff {α ι : Type*} [CompleteLinearOrder α]
    {s : Set ι} {f : ι → α} (h : s.Nonempty) (hs : s.Finite) {a : α} :
    a < ⨅ i ∈ s, f i ↔ ∀ x ∈ s, a < f x := by
  rw [Set.Finite.lt_ciInf_iff hs]
  simpa


