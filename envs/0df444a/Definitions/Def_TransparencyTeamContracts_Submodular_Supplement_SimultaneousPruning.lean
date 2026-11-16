-- Prove2me | Definitions.Def_TransparencyTeamContracts_Submodular_Supplement_SimultaneousPruning
-- name    : TransparencyTeamContracts_Submodular_Supplement_SimultaneousPruning
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T07:12:18.15719+00:00
-- url     : https://prove2.me/theorems/4c5aab3b-a1ed-4dad-a904-f4c35d6b6863
-- title:
--   Simultaneous pruning with recorded shares and inexact comparisons
-- statement:
--   For Lemma D.4, the current team, cached reward, recorded shares and centered errors $E_w,E_f,E_p$ form the processing state. Agents are processed in increasing index order. One new marginal query gives $m_i$; put $r_i=\min\{1,m_i/\sqrt{c_i}\}$, replacing it by zero below $\xi$. Retention records $c_i/m_i$ at that processing time. The payment increment is explicitly zero when $r_i=0$.
--
--   The two candidate quadratic potentials determine retention, allowing a comparison bias $e_i$; Lemma D.4 quantifies over every bias with $|e_i|\le\xi^2/(2n)$. The module stores the actual query list, including the initial reward query. No total-share-at-most-one assumption is built into this procedure. Later deletions preserve the recorded incentive support by submodularity.
-- source:
--   Paul Duetting, Yingkai Li, Inbal Talgam-Cohen, Jinzhao Wu, STOC 2027 submission #1292 (October 2026), Appendix D, printed pp. 33–46 (PDF pp. 35–48)

import Mathlib
import Definitions.Def_TransparencyTeamContracts_Submodular_Supplement_Benchmarks

open Finset
open scoped Classical

namespace TransparencyTeamContracts.Submodular.Supplement

/-- Processing state of Lemma D.4. The cached reward saves a value query. -/
structure PruneState (n : ℕ) where
  team : Finset (Fin n)
  reward : ℝ
  shares : Fin n → ℝ
  ew : ℝ
  ef : ℝ
  ep : ℝ
  queries : List (Finset (Fin n))

def PruneState.potential {n : ℕ} (s : PruneState n) : ℝ := s.ew ^ 2 + s.ef ^ 2 + s.ep ^ 2

/-- One marginal query, then one comparison of the two quadratic potentials.
The comparison bias e is bounded in the theorem, rather than silently set to zero. -/
noncomputable def pruneStep {n : ℕ} (f : Finset (Fin n) → ℝ) (c : Fin n → ℝ)
    (ξ e : ℝ) (s : PruneState n) (i : Fin n) : PruneState n :=
  let nextReward := f (s.team.erase i)
  let m := s.reward - nextReward
  let w := weight c i
  let raw := min 1 (m / w)
  let r := if raw < ξ then 0 else raw
  let payment := if r = 0 then 0 else c i / m
  let candidate := fun x : ℝ =>
    (s.ew + w * (x - r)) ^ 2 + (s.ef - m * (x - r)) ^ 2 +
      (s.ep + payment * (x - r)) ^ 2
  let keep := r = 1 ∨ (r ≠ 0 ∧ candidate 1 ≤ candidate 0 + e)
  let x : ℝ := if keep then 1 else 0
  ⟨if keep then s.team else s.team.erase i,
    if keep then s.reward else nextReward,
    Function.update s.shares i (if keep then payment else 0),
    s.ew + w * (x - r), s.ef - m * (x - r), s.ep + payment * (x - r),
    s.queries ++ [s.team.erase i]⟩

/-- Fixed increasing agent order; all bounded comparison errors are allowed.
Every recorded share is the processing snapshot, not a final recomputation. -/
noncomputable def simultaneousPrune {n : ℕ} (f : Finset (Fin n) → ℝ)
    (c : Fin n → ℝ) (S : Finset (Fin n)) (ξ : ℝ) (e : Fin n → ℝ) : PruneState n :=
  (S.sort (· ≤ ·)).foldl (fun s i => pruneStep f c ξ (e i) s i)
    ⟨S, f S, fun _ => 0, 0, 0, 0, [S]⟩

end TransparencyTeamContracts.Submodular.Supplement


