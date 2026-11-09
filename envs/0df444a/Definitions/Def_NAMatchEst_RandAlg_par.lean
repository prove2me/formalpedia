-- Prove2me | Definitions.Def_NAMatchEst_RandAlg_par
-- name    : NAMatchEst_RandAlg_par
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:52:13.762642+00:00
-- url     : https://prove2.me/theorems/fdc55264-2399-43a6-8e3d-368b87fe956c
-- title:
--   Independent parallel composition of two non-adaptive algorithms
-- statement:
--   Given non-adaptive algorithms $A$ and $B$ and a combining map $f$, their **independent parallel composition** draws the seeds of $A$ and $B$ independently (the product distribution `WildeQIT.FinDist.prod`), issues the queries of both, runs each on the answers to its own queries and outputs $f$ of the two outputs.
--
--   It is non-adaptive again. The paper builds its trials this way: "All samples used by different tests, and all random adjacency-list indices, are chosen independently."
--
--   **Formalization Note** Queries common to both components are charged twice.
-- source:
--   Khanna–Mukhopadhyay–Shah, Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §3.2, p.20 (PDF 24) and §3.7, p.28 (PDF 32)

import Mathlib
import Definitions.Def_WildeQIT_FinDist
import Definitions.Def_NAMatchEst_RandAlg

namespace NAMatchEst

/-- **Independent parallel composition** of two non-adaptive algorithms: draw the seeds of `A` and
`B` independently (the product distribution `WildeQIT.FinDist.prod`), issue the queries of both, run each on the answers to its own
queries, and combine the two outputs with `f`.

Khanna–Mukhopadhyay–Shah, *Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation*, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §3.2, p.20 (PDF 24) ("All samples used by different tests, and all random adjacency-list
indices, are chosen independently.") and §3.7, p.28 (PDF 32) ("All these random choices are
independent and are made before receiving any answers.").

**Formalization Note** Each component sees only the answers to its own queries, so the composite
run is `f (A.run G ω.1) (B.run G ω.2)`. Queries common to both components are charged twice. -/
noncomputable def RandAlg.par {n : ℕ} {β γ δ : Type} (A : RandAlg n β) (B : RandAlg n γ) (f : β → γ → δ) :
    RandAlg n δ where
  Ω := A.Ω × B.Ω
  dist := A.dist.prod B.dist
  queries ω := A.queries ω.1 ++ B.queries ω.2
  output ω d m := f
    (A.output ω.1 (fun v => if Query.deg v ∈ A.queries ω.1 then d v else none)
      (fun v i => if Query.nbr v i ∈ A.queries ω.1 then m v i else none))
    (B.output ω.2 (fun v => if Query.deg v ∈ B.queries ω.2 then d v else none)
      (fun v i => if Query.nbr v i ∈ B.queries ω.2 then m v i else none))

end NAMatchEst


