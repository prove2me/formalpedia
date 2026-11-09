-- Prove2me | Definitions.Def_NAMatchEst_RandAlg_guard
-- name    : NAMatchEst_RandAlg_guard
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:52:41.112204+00:00
-- url     : https://prove2.me/theorems/cc1281ab-f86f-4956-adcd-f503835602ad
-- title:
--   Aborting a non-adaptive algorithm on a seed condition
-- statement:
--   Given an algorithm $A$, a condition $\mathrm{ok}$ on its seeds and a default output $b_0$, the **guarded** algorithm behaves like $A$ on seeds with $\mathrm{ok}(\omega)$, and on the other seeds issues no query and outputs $b_0$.
--
--   The abort decision uses only the internal randomness, so the result is non-adaptive. This models the paper's truncation (24): "abort the trial and output No if $|S|>\lceil 2np+100L\rceil$."
-- source:
--   Khanna–Mukhopadhyay–Shah, Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §3.9, p.29 (PDF 33)

import Mathlib
import Definitions.Def_NAMatchEst_RandAlg

namespace NAMatchEst

/-- **Abort on a seed condition**: the algorithm that, under seed `ω`, behaves like `A` when
`ok ω` holds and otherwise issues no query and outputs `b₀`.

Khanna–Mukhopadhyay–Shah, *Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation*, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §3.9, p.29 (PDF 33): "abort the trial and output No if |S| > ⌈2np + 100L⌉. (24) Both vertex
sets and this abort decision are generated before issuing any queries for the trial. The decision
uses only internal randomness and does not depend on oracle answers."

**Formalization Note** The abort decision is a function of the seed only, so the result is again
non-adaptive. -/
noncomputable def RandAlg.guard {n : ℕ} {β : Type} (A : RandAlg n β) (ok : A.Ω → Prop)
    (b₀ : β) : RandAlg n β :=
  open Classical in
  { Ω := A.Ω
    dist := A.dist
    queries := fun ω => if ok ω then A.queries ω else []
    output := fun ω d m => if ok ω then A.output ω d m else b₀ }

end NAMatchEst


