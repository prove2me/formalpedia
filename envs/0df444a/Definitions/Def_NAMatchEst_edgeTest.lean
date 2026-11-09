-- Prove2me | Definitions.Def_NAMatchEst_edgeTest
-- name    : NAMatchEst_edgeTest
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:55:15.518229+00:00
-- url     : https://prove2.me/theorems/19424af5-e20d-4bee-b845-484efbf9bdd0
-- title:
--   The certified-edge test (large scale)
-- statement:
--   The **certified-edge test** of the large-scale regime (displays (14)–(19)).
--
--   1. Include every vertex independently in $S^L$ with probability $p^L:=cL/\sqrt{k\alpha}$ and in $S^R$ with probability $p^R:=\sqrt{\alpha/k}$ (14), the two samples independent.
--   2. For $v\in S^L$ query its degree and the first $\Delta$ positions of its list. For $v\in S^R$ query its degree and $r:=\lceil c\Delta L/\alpha\rceil$ (15) independent uniform positions in $[\Delta]$, with replacement.
--   3. Discard sampled vertices outside $U$. Retain a left vertex if $d_{\bar H}(v)<2\alpha$ and a right vertex if $\widehat d_{\bar H}(v):=(\Delta/r)\,Y_v<2\alpha$, where $Y_v$ counts the queried positions that return a neighbour outside $H$. These are $S^L_3$ and $S^R_3$ (16).
--   4. Count the directed incidences $Z_E:=|\{(u,v):u\in S^L_3,\ v\in S^R_3,\ \{u,v\}\in E\}|$ (18). The test accepts when $Z_E\ge kp^Lp^R/4=cL/4$ (19).
--
--   **Formalization Note** The output is the record (`EdgeStats`) as a function of $H$. The right-sample positions are drawn for every vertex and queried only for $v\in S^R$, which leaves their law unchanged. An edge is read from the row of its left endpoint $u\in U$. The inclusion probabilities are clamped to $[0,1]$ (`bernW`).
-- source:
--   Khanna–Mukhopadhyay–Shah, Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §3.5, displays (14)–(19), pp.24–25 (PDF 28–29)

import Mathlib
import Definitions.Def_NAMatchEst_RandAlg
import Definitions.Def_WildeQIT_FinDist
import Definitions.Def_ShallowShadows_ShadowNorm_uniformDist
import Definitions.Def_NAMatchEst_bernDist
import Definitions.Def_NAMatchEst_cc
import Definitions.Def_NAMatchEst_L
import Definitions.Def_NAMatchEst_Delta
import Definitions.Def_NAMatchEst_rowQueries
import Definitions.Def_NAMatchEst_rowNbrs
import Definitions.Def_NAMatchEst_EdgeStats

namespace NAMatchEst

/-- The **certified-edge test** of the large-scale regime (displays (14)–(19)), with its statistics
given as a function of the set `H`.

1. Include every vertex independently in `S^L` with probability `p^L := cL/√(kα)` and in `S^R` with
   probability `p^R := √(α/k)` (14), the two samples independent.
2. For `v ∈ S^L` query its degree and the first `∆` positions of its list. For `v ∈ S^R` query its
   degree and `r := ⌈c∆L/α⌉` (15) independent uniform positions in `[∆]`, with replacement.
3. Discard sampled vertices outside `U` (degree answer `⩾ ∆`). Retain a left vertex if
   `d_{H̄}(v) < 2α` (read from its row) and a right vertex if `d̂_{H̄}(v) := (∆/r) Y_v < 2α`, where
   `Y_v` counts the queried positions that return a neighbour outside `H`; these are
   `S^L_3`, `S^R_3` (16).
4. `Z_E` (18) counts the ordered pairs `(u, v)` with `u ∈ S^L_3`, `v ∈ S^R_3` and `v` revealed in the
   row of `u`. The test accepts when `Z_E ⩾ kp^Lp^R/4 = cL/4` (19).

Khanna–Mukhopadhyay–Shah, *Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation*, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §3.5, pp.24–25 (PDF 28–29), displays (14)–(19).

**Formalization Note**
1. The seed is `(S^L, S^R, pos)` with `pos v j ∈ Fin ∆` the `j`-th position drawn for `v` (position
   `pos v j + 1 ∈ [∆]`); positions are drawn for every vertex but queried only for `v ∈ S^R`, which
   leaves the law of the queried positions unchanged.
2. The edge `{u, v}` is detected through the row of its left endpoint `u ∈ U`, whose first `∆`
   positions list all of `N(u)` ("Every counted incidence is revealed by the full row of its left
   endpoint", p.25).
3. The Bernoulli probabilities are clamped to `[0, 1]` (`bernDist`); under the standing assumption
   `cL/√α ⩽ 1` both lie in `[0, 1]`. -/
noncomputable def edgeTest (n : ℕ) (α : ℝ) (k : ℕ) : RandAlg n (Finset (Fin n) → EdgeStats n) :=
  open Classical in
  { Ω := (Fin n → Bool) × (Fin n → Bool) ×
      (Fin n → Fin ⌈cc * Delta k α * L n / α⌉₊ → Fin (Delta k α))
    dist :=
      have : Nonempty (Fin n → Fin ⌈cc * Delta k α * L n / α⌉₊ → Fin (Delta k α)) := by
        rcases Nat.eq_zero_or_pos (Delta k α) with h | h
        · have hr : ⌈cc * Delta k α * L n / α⌉₊ = 0 := by simp [h]
          rw [hr]
          exact ⟨fun _ i => i.elim0⟩
        · exact ⟨fun _ _ => ⟨0, h⟩⟩
      (bernDist (cc * L n / Real.sqrt (k * α))).prod
        ((bernDist (Real.sqrt (α / k))).prod (ShallowShadows.ShadowNorm.uniformDist _))
    queries := fun ω => (List.finRange n).flatMap fun v =>
      (if ω.1 v then rowQueries v (Delta k α) else []) ++
      (if ω.2.1 v then Query.deg v :: List.ofFn (fun j => Query.nbr v ((ω.2.2 v j : ℕ) + 1))
        else [])
    output := fun ω d m H =>
      let inU : Fin n → Prop := fun v => ∃ x ∈ d v, x < Delta k α
      let SL := Finset.univ.filter fun v => ω.1 v = true
      let SR := Finset.univ.filter fun v => ω.2.1 v = true
      let Y : Fin n → ℕ := fun v => (Finset.univ.filter fun j =>
        ∃ u, m v ((ω.2.2 v j : ℕ) + 1) = some (some u) ∧ u ∉ H).card
      let SL3 := SL.filter fun v =>
        inU v ∧ ((rowNbrs m v (Delta k α) \ H).card : ℝ) < 2 * α
      let SR3 := SR.filter fun v =>
        inU v ∧ (Delta k α : ℝ) / ⌈cc * Delta k α * L n / α⌉₊ * Y v < 2 * α
      { SL := SL, SR := SR, SL3 := SL3, SR3 := SR3
        ZE := ((SL3 ×ˢ SR3).filter fun p => p.2 ∈ rowNbrs m p.1 (Delta k α)).card } }

end NAMatchEst


