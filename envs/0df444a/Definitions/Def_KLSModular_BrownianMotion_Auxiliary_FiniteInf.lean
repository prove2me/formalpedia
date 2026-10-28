-- Prove2me | Definitions.Def_KLSModular_BrownianMotion_Auxiliary_FiniteInf
-- name    : KLSModular_BrownianMotion_Auxiliary_FiniteInf
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:34:11.169977+00:00
-- url     : https://prove2.me/theorems/7f2a8f31-51ad-4bfb-b609-4165192c112c
-- title:
--   Finite-set infimum comparison
-- statement:
--   Vendored from `RemyDegenne/brownian-motion` at commit `a7ad7af662044313bc80a7c0756360fb3745f931` under Apache-2.0. `Set.Finite.lt_iInf_iff` characterizes $a<\inf_{i∈s}f(i)$ for a nonempty finite set `s` in a complete linear order by the pointwise conditions $a<f(x)$ for every $x∈s$.
--
--   **Original module imports**
--
--   ```lean
--   public import Mathlib.Data.Finset.Max
--   public import Mathlib.Data.Set.Finite.Lattice
--   public import Mathlib.Order.CompletePartialOrder
--   public import Mathlib.Order.ConditionallyCompletePartialOrder.Indexed
--   import Mathlib.Order.ConditionallyCompleteLattice.Finset
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   lemma Set.Finite.lt_iInf_iff {α ι : Type*} [CompleteLinearOrder α]
--       {s : Set ι} {f : ι → α} (h : s.Nonempty) (hs : s.Finite) {a : α} :
--       a < ⨅ i ∈ s, f i ↔ ∀ x ∈ s, a < f x := by
--     rw [Set.Finite.lt_ciInf_iff hs]
--     simpa
--   ```
--
--   **Module navigation**
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/BrownianMotion/BrownianMotion/Auxiliary/FiniteInf.lean) · `BrownianMotion.Auxiliary.FiniteInf` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/RemyDegenne/brownian-motion/blob/a7ad7af662044313bc80a7c0756360fb3745f931/BrownianMotion/Auxiliary/FiniteInf.lean#L57-L61 (repository human-ai-mathematics/kls-lean, commit 408915f, module `BrownianMotion.Auxiliary.FiniteInf`, definition bundle `KLSModular_BrownianMotion_Auxiliary_FiniteInf`; the repository is private at upload time). Vendored from https://github.com/RemyDegenne/brownian-motion at commit a7ad7af662044313bc80a7c0756360fb3745f931 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Mathlib.Data.Finset.Max
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.ConditionallyCompletePartialOrder.Indexed
import Mathlib.Order.ConditionallyCompleteLattice.Finset

-- Vendored from https://github.com/RemyDegenne/brownian-motion at commit a7ad7af662044313bc80a7c0756360fb3745f931 (upstream path BrownianMotion/Auxiliary/FiniteInf.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
variable {α ι : Type*} [CompleteLinearOrder α]
lemma Set.Finite.lt_iInf_iff {α ι : Type*} [CompleteLinearOrder α]
    {s : Set ι} {f : ι → α} (h : s.Nonempty) (hs : s.Finite) {a : α} :
    a < ⨅ i ∈ s, f i ↔ ∀ x ∈ s, a < f x := by
  rw [Set.Finite.lt_ciInf_iff hs]
  simpa


