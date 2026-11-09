-- Prove2me | Definitions.Def_NAMatchEst_smallEdgeTest
-- name    : NAMatchEst_smallEdgeTest
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:53:37.238975+00:00
-- url     : https://prove2.me/theorems/df3b4e7e-3f96-4a8b-a9c2-896191b302a6
-- title:
--   The small-scale edge test
-- statement:
--   The **small-scale edge test** (§3.8). Include every vertex independently in $S^L$ with probability $p^L:=cL\sqrt\alpha/k$ and in $S^R$ with probability $p^R:=1/\sqrt\alpha$ (23). For $v\in S^L$ query its degree and its first $\Delta$ neighbours; for $v\in S^R$ query only its degree. Retain $S^L_0:=S^L\cap U$ and $S^R_0:=S^R\cap U$ and count
--
--   $$
--   Z_0:=|\{(u,v):u\in S^L_0,\ v\in S^R_0,\ \{u,v\}\in E\}|.
--   $$
--
--   The test accepts if $Z_0\ge kp^Lp^R/4=cL/4$.
--
--   **Formalization Note** The inclusion probabilities are clamped to $[0,1]$ (`bernW`).
-- source:
--   Khanna–Mukhopadhyay–Shah, Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §3.8, display (23), pp.28–29 (PDF 32–33)

import Mathlib
import Definitions.Def_NAMatchEst_RandAlg
import Definitions.Def_WildeQIT_FinDist
import Definitions.Def_NAMatchEst_bernDist
import Definitions.Def_NAMatchEst_cc
import Definitions.Def_NAMatchEst_L
import Definitions.Def_NAMatchEst_Delta
import Definitions.Def_NAMatchEst_rowQueries
import Definitions.Def_NAMatchEst_rowNbrs

namespace NAMatchEst

/-- The **small-scale edge test** (§3.8). Include every vertex independently in `S^L` with
probability `p^L := cL√α/k` and in `S^R` with probability `p^R := 1/√α` (23). For `v ∈ S^L` query
its degree and its first `∆` neighbours; for `v ∈ S^R` query only its degree. Retain
`S^L_0 := S^L ∩ U`, `S^R_0 := S^R ∩ U`, count the ordered pairs `(u, v) ∈ S^L_0 × S^R_0` with
`{u, v} ∈ E` (`Z₀`), and accept iff `Z₀ ⩾ kp^Lp^R/4 = cL/4`.

Khanna–Mukhopadhyay–Shah, *Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation*, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §3.8, pp.28–29 (PDF 32–33): "Independently generate the first-layer degree sample and two
Bernoulli vertex samples SL, SR with probabilities pL := cL√α/k, pR := 1/√α, pLpR = cL/k. (23) For
every v ∈ SL, query its degree and its first ∆ neighbours. For every v ∈ SR, query only its degree.
After receiving the answers, retain SL0 := SL ∩ U and SR0 := SR ∩ U, and count Z0 := |{(u, v) :
u ∈ SL0, v ∈ SR0, {u, v} ∈ E}|. … The small-scale edge test accepts if Z0 ⩾ kpLpR/4 = cL/4."

**Formalization Note** Membership in `U` is read from the degree answers; the edge `{u, v}` is read
from the row of `u ∈ U` ("The full left rows reveal all counted incidences", p.29). The Bernoulli
probabilities are clamped to `[0, 1]` (`bernDist`). -/
noncomputable def smallEdgeTest (n : ℕ) (α : ℝ) (k : ℕ) : RandAlg n Bool :=
  open Classical in
  { Ω := (Fin n → Bool) × (Fin n → Bool)
    dist := (bernDist (cc * L n * Real.sqrt α / k)).prod (bernDist (1 / Real.sqrt α))
    queries := fun ω => (List.finRange n).flatMap fun v =>
      (if ω.1 v then rowQueries v (Delta k α) else []) ++ (if ω.2 v then [Query.deg v] else [])
    output := fun ω d m =>
      let SL0 := Finset.univ.filter fun v => ω.1 v = true ∧ ∃ x ∈ d v, x < Delta k α
      let SR0 := Finset.univ.filter fun v => ω.2 v = true ∧ ∃ x ∈ d v, x < Delta k α
      decide (cc * L n / 4 ≤
        (((SL0 ×ˢ SR0).filter fun p => p.2 ∈ rowNbrs m p.1 (Delta k α)).card : ℝ)) }

end NAMatchEst


