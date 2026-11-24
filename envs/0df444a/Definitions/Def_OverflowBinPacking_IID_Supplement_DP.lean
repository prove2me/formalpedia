-- Prove2me | Definitions.Def_OverflowBinPacking_IID_Supplement_DP
-- name    : OverflowBinPacking_IID_Supplement_DP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T04:53:55.639591+00:00
-- url     : https://prove2.me/theorems/fc8cfcda-015c-433c-86bb-66477741d3f5
-- title:
--   Operational backward dynamic program and exact reachable states
-- statement:
--   For discretized input, a state is the multiset of opened unbroken bin loads, represented by a sorted list; multiplicities are the paper's load-count vector. Empty opened bins are retained and overflowed bins are retired. The backward value has terminal value zero. Every action chooses a new bin or an existing live bin, and its value is
--   $$\mathbf1_{\mathrm{new}}+\sum_x\Pr(\widehat X_t=x)\bigl(C\mathbf1_{\mathrm{overflow}}+V_{t+1}(S')\bigr).$$
--   The finite action minimum and all reachable states are explicitly enumerated. The definition keeps $\varepsilon^4$ as a separate support value because the paper's lattice identification is invalid without a reciprocal-integer convention. No such convention is imposed. A finite table stores time, multiset state, value and action. The operation-count expression is defined by enumerating state/action/outcome evaluations; it does not assume the paper's runtime estimate. A polynomial implementation must share next-layer entries rather than expand the recursive expression into an outcome tree. The source recursion's load is $j\varepsilon^5$, not the count $k_j$ in its overflow expression; existing bins at load zero are eligible. Excluding those bins would open a new bin for every zero-sized item. The generic recurrence also charges overflow on an opening action when its outcome exceeds capacity.
-- source:
--   Perez-Salazar, Singh & Toriello, Adaptive Bin Packing with Overflow, arXiv:2007.11532v2, p. 21, §6.2; p. 26, §6.5

import Mathlib
import Definitions.Def_OverflowBinPacking_IID_Supplement_Discretization

namespace OverflowBinPacking.IID.Supplement
open MeasureTheory

/-- Exact discrete outcome set on the full positive ε domain: ε⁴ is retained
separately because it need not be a multiple of ε⁵. Repeated values are removed. -/
noncomputable def hatSupport (ε : ℝ) : Finset ℝ := by
  classical
  exact insert 0 (insert (ε ^ 4)
    ((Finset.range (⌈(1 + ε) / ε ^ 5⌉₊ + 2)).image (fun k => (k : ℝ) * ε ^ 5)))

/-- A state is the multiset of opened, unbroken loads. An opened empty bin is
retained. Sorting makes bins with identical loads interchangeable. -/
abbrev LoadState := List ℝ

noncomputable def normalizeState (s : LoadState) : LoadState := s.mergeSort (· ≤ ·)

noncomputable def dpUpdate (c : ℝ) (s : LoadState) (j : ℕ) (x : ℝ) : LoadState :=
  normalizeState <| if j < s.length then
    if c < s[j]! + x then s.eraseIdx j else s.set j (s[j]! + x)
  else if c < x then s else s ++ [x]

/-- Minimum of a nonempty explicit action list. Empty has the harmless terminal
value zero and is never used by the recurrence below. -/
noncomputable def listMinimum (vs : List ℝ) : ℝ := vs.foldl min vs[0]!

/-- One action's immediate opening/overflow cost and expected continuation. The
source's missing opening overflow term is included on general input. -/
noncomputable def dpAction (S : Finset ℝ) (ν : Measure ℝ) (C c : ℝ)
    (V : LoadState → ℝ) (s : LoadState) (j : ℕ) : ℝ :=
  let old := if j < s.length then s[j]! else 0
  (if j < s.length then 0 else 1) +
    ∑ x ∈ S, ν.real {x} *
      ((if c < old + x then C else 0) + V (dpUpdate c s j x))

/-- Backward DP, terminal value zero. The outer recursion is on the remaining
ordered list of laws, so the decision is made before sampling its head. -/
noncomputable def dpValue (S : Finset ℝ) (C c : ℝ) :
    List (Measure ℝ) → LoadState → ℝ
  | [], _ => 0
  | ν :: rest, s => listMinimum <|
    (List.range (s.length + 1)).map (dpAction S ν C c (dpValue S C c rest) s)

/-- Every reachable state, with count vectors represented by sorted load lists.
The constructor enumerates every action and every discrete outcome at each level. -/
noncomputable def reachableStates (S : Finset ℝ) (c : ℝ) : ℕ → Finset LoadState
  | 0 => {[]}
  | t + 1 => by
    classical
    exact (reachableStates S c t).biUnion fun s =>
      (Finset.range (s.length + 1)).biUnion fun j => S.image (dpUpdate c s j)

/-- The Bellman table, in backward time order. This is a finite decision table,
not an outcome tree. Each row stores time, load-count state, value, action. -/
structure DPRow where
  time : ℕ
  state : LoadState
  value : ℝ
  action : ℕ

noncomputable def dpBestAction (S : Finset ℝ) (ν : Measure ℝ) (C c : ℝ)
    (V : LoadState → ℝ) (s : LoadState) : ℕ :=
  ((List.range (s.length + 1)).foldl (fun best j =>
    if dpAction S ν C c V s j < dpAction S ν C c V s best then j else best) 0)

/-- Table entries are defined by backward induction; a compiled implementation
must reuse next-layer entries rather than expanding dpValue's expression tree. -/
noncomputable def dpTable (S : Finset ℝ) (C c : ℝ) (laws : List (Measure ℝ)) : List DPRow :=
  ((List.range (laws.length + 1)).reverse).flatMap fun t =>
    ((reachableStates S c t).toList).map fun s =>
      ⟨t, s, dpValue S C c (laws.drop t) s,
        match laws[t]? with
        | none => 0
        | some ν => dpBestAction S ν C c (dpValue S C c (laws.drop (t + 1))) s⟩

/-- Primitive action/outcome evaluation count for a memoized implementation.
No runtime estimate is assumed. -/
noncomputable def dpOperationCount (S : Finset ℝ) (c : ℝ)
    (laws : List (Measure ℝ)) : ℕ :=
  ∑ t ∈ Finset.range laws.length,
    ∑ s ∈ reachableStates S c t, (s.length + 1) * (12 * S.card + 3)

end OverflowBinPacking.IID.Supplement


