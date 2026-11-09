-- Prove2me | Definitions.Def_OnlineSteinitz_Reduction_Router
-- name    : OnlineSteinitz_Reduction_Router
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:50:12.591001+00:00
-- url     : https://prove2.me/theorems/dc75cae6-1e53-4a2f-b207-ac290299e510
-- title:
--   Algorithm 1: immediate routing with quota overrides
-- statement:
--   At an internal node of capacity $m$, call its persistent signer on every arriving vector, retaining its proposal $\varepsilon$. If the left child is full, route right; otherwise if the right child is full, route left; otherwise follow $\varepsilon$. Record the proposed and actual signs separately and descend to the selected child. At a singleton, place the vector in that slot. Child counts and sums are determined by the visit records.
--
--   The execution function folds this transition over the arrival list, starting with empty local histories and no placements. A second execution accepts an adaptive adversary that selects the next vector from the round and previous placements. The completed output at a slot is the sum of vectors recorded at that slot; the goal theorem asserts that each slot contains exactly one arrival and recovers the permutation.
--
--   This is a concrete total algorithm, without an assumed routing-validity or discrepancy contract. Its recorded local histories also provide the actual data for the quota-repair analysis. The proposed history continues to update after a child fills; the signer never receives an overridden sign as its own proposal.
-- source:
--   Russo–Wei, The Online Steinitz Problem, STOC 2027 submission #22 (2026 preprint), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/22.pdf, SHA-256 32ff14f15a94c95630765c77f4fa5a429fb294bcf03a9055ed67c60658769366, Algorithm 1 and explanatory paragraphs, p.5; online/adaptive protocol, pp.1–2

import Definitions.Def_OnlineSteinitz_Reduction_Tree
import Definitions.Def_OnlineSteinitz_Reduction_Signer

namespace OnlineSteinitz.Reduction

/-! Algorithm 1, p.5. Records preserve the proposal and destination separately.
Every visit calls the signer, including after one child fills. -/
structure Visit (E : Type*) where
  vector : E
  proposed : Bool
  actual : Bool

def proposedHistory {E : Type*} (h : List (Visit E)) : ProposalHistory E :=
  h.map (fun e => (e.vector, e.proposed))

def leftCount {E : Type*} (h : List (Visit E)) : ℕ :=
  (h.filter (fun e => e.actual)).length

def quotaSign {E : Type*} (m : ℕ) (h : List (Visit E)) (ε : Bool) : Bool :=
  if leftCount h = leftSize m then false
  else if h.length - leftCount h = rightSize m then true else ε

def repair {E : Type*} (m : ℕ) (xs : List (E × Bool)) : List (Visit E) :=
  xs.foldl (fun h e => h ++ [⟨e.1, e.2, quotaSign m h e.2⟩]) []

structure Run (T : ℕ) (E : Type*) where
  localHistory : Node T → List (Visit E)
  placed : List (ℕ × E)

def emptyRun (T : ℕ) (E : Type*) : Run T E := ⟨fun _ => [], []⟩

def descend {T : ℕ} {E Ω : Type*} (rules : Node T → Signer E Ω)
    (tapes : Node T → Ω) : ℕ → ℕ → ℕ → (Node T → List (Visit E)) → E →
      ℕ × (Node T → List (Visit E))
  | 0, a, _, histories, _ => (a, histories)
  | fuel + 1, a, m, histories, x =>
    if m ≤ 1 then (a, histories) else
      let u := nodeKey T a m
      let h := histories u
      let ε := rules u (tapes u) (proposedHistory h) x
      let actual := quotaSign m h ε
      let histories' := Function.update histories u (h ++ [⟨x, ε, actual⟩])
      if actual then descend rules tapes fuel a (leftSize m) histories' x
      else descend rules tapes fuel (a + leftSize m) (rightSize m) histories' x

def place {T : ℕ} {E Ω : Type*} (rules : Node T → Signer E Ω)
    (tapes : Node T → Ω) (r : Run T E) (x : E) : Run T E :=
  let result := descend rules tapes T 0 T r.localHistory x
  ⟨result.2, r.placed ++ [(result.1, x)]⟩

def execute {T : ℕ} {E Ω : Type*} (rules : Node T → Signer E Ω)
    (tapes : Node T → Ω) (xs : List E) : Run T E :=
  xs.foldl (place rules tapes) (emptyRun T E)

def adaptiveExecute {T : ℕ} {E Ω : Type*} (rules : Node T → Signer E Ω)
    (tapes : Node T → Ω) (adversary : ℕ → List (ℕ × E) → E) : Run T E :=
  (List.range T).foldl
    (fun r t => place rules tapes r (adversary t r.placed)) (emptyRun T E)

noncomputable def output {T : ℕ} {E : Type*} [AddCommGroup E]
    (r : Run T E) (j : ℕ) : E :=
  ((r.placed.filter (fun e => e.1 == j)).map Prod.snd).sum

end OnlineSteinitz.Reduction


