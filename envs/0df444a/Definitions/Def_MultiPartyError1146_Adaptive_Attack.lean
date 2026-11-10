-- Prove2me | Definitions.Def_MultiPartyError1146_Adaptive_Attack
-- name    : MultiPartyError1146_Adaptive_Attack
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T18:33:27.042897+00:00
-- url     : https://prove2.me/theorems/75203e51-832b-4f81-b264-e64705ff1da4
-- title:
--   Finite greedy isolation and recursive party/round erasures
-- statement:
--   For a one-bit protocol, $S_{i,b}$ is the set of rounds in which party $i$ speaks on private bit $b$ when its entire received prefix is $\perp$. The greedy construction starts with two copies of every round and repeatedly chooses the first eligible party/bit pair. Selection fixes that party's bit and removes one copy of each round in its speaking set. Multiset intersection uses minimum multiplicities: $S_{i,b}$ itself has multiplicity one. Therefore
--   $$|S_{i,b}\cap Z|=\sum_{t\in S_{i,b}}\min(1,Z(t)).$$
--   After at most $n$ steps, the first unchosen party is the target. The erased-party set is the chosen set plus the target, and erased rounds are the remaining support intersected with both target speaking sets. The erasure strategy recursively delivers $\perp$ on this mask and the actual current CAS baseline elsewhere. No adversary budget or collision property is assumed in the construction.
-- source:
--   Klim Efremenko, Gillat Kol, Raghuvansh Saxena, Zhijun Zhang, STOC 2027 submission #1146 (October 2026), Section 5, pp.31–32, printed p.31, PDF p.33

import Mathlib
import Definitions.Def_MultiPartyError1146_Adaptive_Protocol

set_option autoImplicit false

namespace MultiPartyError1146.Adaptive

noncomputable def silentSpeaking {n T : ℕ} (P : Protocol n 1 T) (i : Fin n) (b : Bool) :
    Finset (Fin T) := by
  classical
  exact Finset.univ.filter fun t => (P.send t i (fun _ => b) (fun _ => none)).isSome

/-- Remaining multiplicities start at two. Each selection removes only one copy. -/
structure GreedyState (n T : ℕ) where
  chosen : Finset (Fin n)
  input : Fin n → Bool
  copies : Fin T → ℕ

/-- Multiset intersection with S_{i,b}, which has multiplicity ONE in the source.
The min is essential: an intersection is not the sum of all copies on the support. -/
noncomputable def intersectionSize {n T : ℕ} (P : Protocol n 1 T)
    (z : GreedyState n T) (i : Fin n) (b : Bool) : ℕ :=
  ∑ t ∈ silentSpeaking P i b, min 1 (z.copies t)

noncomputable def greedyStep {n T : ℕ} (P : Protocol n 1 T) (k : ℕ)
    (z : GreedyState n T) : GreedyState n T := by
  classical
  let candidates := (List.finRange n).flatMap fun i => [(i,false),(i,true)]
  exact match candidates.find? (fun e => decide (e.1 ∉ z.chosen ∧
      (T : ℝ) / k < (intersectionSize P z e.1 e.2 : ℝ))) with
  | none => z
  | some (i,b) =>
      ⟨insert i z.chosen, Function.update z.input i b,
        fun t => if t ∈ silentSpeaking P i b then z.copies t - 1 else z.copies t⟩

/-- n steps exhaust the finite greedy loop; a terminated step is the identity. -/
noncomputable def greedy {n T : ℕ} (P : Protocol n 1 T) (k : ℕ) : GreedyState n T :=
  (greedyStep P k)^[n] ⟨∅, fun _ => false, fun _ => 2⟩

noncomputable def remainingRounds {n T : ℕ} (P : Protocol n 1 T) (k : ℕ) : Finset (Fin T) := by
  classical
  exact Finset.univ.filter fun t => 0 < (greedy P k).copies t

noncomputable def target {n T : ℕ} (P : Protocol n 1 T) (k : ℕ) : Option (Fin n) := by
  classical
  exact (List.finRange n).find? fun i => decide (i ∉ (greedy P k).chosen)

noncomputable def erasedParties {n T : ℕ} (P : Protocol n 1 T) (k : ℕ) : Finset (Fin n) :=
  (greedy P k).chosen ∪ (target P k).toList.toFinset

noncomputable def erasedRounds {n T : ℕ} (P : Protocol n 1 T) (k : ℕ) : Finset (Fin T) :=
  match target P k with
  | none => ∅
  | some i => remainingRounds P k ∩ (silentSpeaking P i false ∪ silentSpeaking P i true)

/-- Recursive execution of the party/round erasure policy on an arbitrary protocol.
Outside the mask it delivers the actual current CAS symbol, not a preselected transcript. -/
noncomputable def maskedHistory {n m T : ℕ} (P : Protocol n m T) (x : Input n m)
    (parties : Finset (Fin n)) (rounds : Finset (Fin T)) : ℕ → List (Fin n → Symbol)
  | 0 => []
  | j + 1 => by
      classical
      let history := maskedHistory P x parties rounds j
      exact history ++ [fun i =>
        if ht : j < T then
          if i ∈ parties ∨ (⟨j,ht⟩ : Fin T) ∈ rounds then none else
            cas (fun q => P.send ⟨j,ht⟩ q (x q)
              (fun t => (history[t.val]?.getD (fun _ => none)) q))
        else none]

noncomputable def maskedAdversary {n m T : ℕ} (P : Protocol n m T) (x : Input n m)
    (parties : Finset (Fin n)) (rounds : Finset (Fin T)) : Adversary n T :=
  fun t => (maskedHistory P x parties rounds T)[t.val]?.getD (fun _ => none)

noncomputable def isolationAttack {n T : ℕ} (P : Protocol n 1 T) (k : ℕ)
    (x : Input n 1) : Adversary n T :=
  maskedAdversary P x (erasedParties P k) (erasedRounds P k)

end MultiPartyError1146.Adaptive


