-- Prove2me | Definitions.Def_GreedySuperstring_LowerBound_Supplement_CycleCover
-- name    : GreedySuperstring_LowerBound_Supplement_CycleCover
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:35:46.182203+00:00
-- url     : https://prove2.me/theorems/84edf50b-e954-476d-b830-b67715583e2a
-- title:
--   MGREEDY's cycle-cover stage, cycle overlaps, cycle prefixes and cycle strings
-- statement:
--   Let $S$ be a finite set of words. $\mathrm{OPT}(S)$ is the minimum length of a word containing every member of $S$ as a contiguous substring, and a **shortest common superstring** is such a word of that length.
--
--   The first stage of MGREEDY maintains a set of current blocks (a current word with the ordered list of input words merged into it), initially one singleton block per member of $S$, and an initially empty list of representatives. While the current set is nonempty it selects an ordered pair $(a,b)$ of current blocks, **allowing $a=b$**, whose proper overlap $|\mathrm{ov}(a,b)|$ is maximum over all ordered pairs of current blocks, self-pairs included, breaking ties arbitrarily. If $a\ne b$ they are replaced by their overlap merge $\langle a,b\rangle$; if $a=b$, the block is removed and appended unchanged to the representatives. A complete run ends with no current block.
--
--   An extracted block with history $(t_1,\dots,t_r)$ is the cycle $C=(t_1,\dots,t_r,t_1)$ of the constructed cycle cover, with $t_{r+1}=t_1$:
--
--   $$o(C)=|\mathrm{ov}(t_r,t_1)|,\qquad w(C)=\sum_{i=1}^{r}|\mathrm{pref}(t_i,t_{i+1})|,\qquad \tau(C)=\mathrm{pref}(t_1,t_2)\circ\cdots\circ\mathrm{pref}(t_r,t_1).$$
--
--   Finally $O=\sum_C o(C)$ and $W=\sum_C w(C)$ over all extracted cycles. These are the quantities of the cycle-cover inequality (Theorem 3.1) and its tightness (Theorem 3.3).
--
--   **Formalization Note** The alphabet is any type with decidable equality, and blocks, overlaps and merges are the published ones. A run is the reflexive–transitive closure of the step relation from the initial state to a state with no current block; nothing about cycle covers, optimality, or $|\sigma(C)|=w(C)+o(C)$ is assumed. An empty history (never produced) is assigned $o=0$.
-- source:
--   Nikolai Chukhin, Rishikesh Gajjala, Juha Harviainen, Alexander S. Kulikov, Ivan Mihajlin, Hiroki Shibata, Alexander V. Smal, The Greedy Superstring Conjecture Is False, STOC 2027 submission #316 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/316.pdf, SHA-256 84e171350ae4e20ed6899c32b480753dae49f7b418819656dfedbcac0f60e8fa, §2, §2.3, §2.4 and §2.6, printed pp.5, 7–9 = PDF pp.5, 7–9

import Mathlib
import Definitions.Def_GreedySuperstring_LowerBound_GreedyModel

universe cc_u

namespace GreedySuperstring.LowerBound.Supplement

open GreedySuperstring.LowerBound

/-- §2, p.5: `OPT(S)`, the minimum length of a word over the alphabet `α` containing every
member of `S` as a contiguous substring. Same formula as `OAI.Superstring.opt`, with an
arbitrary alphabet in place of `Symbol`. The set is nonempty (the concatenation of `S` is a
common superstring), so this is a genuine minimum. -/
noncomputable def opt {α : Type cc_u} (S : Finset (List α)) : ℕ :=
  sInf {n : ℕ | ∃ T : List α, (∀ s ∈ S, s <:+: T) ∧ T.length = n}

/-- `T` is a shortest common superstring of `S`: it contains every member of `S` and has
length `OPT(S)`. -/
def IsShortestSuperstring {α : Type cc_u} (S : Finset (List α)) (T : List α) : Prop :=
  (∀ s ∈ S, s <:+: T) ∧ T.length = opt S

/-- State of MGREEDY's first stage (§2.4, p.8): the current blocks (published `Block`: word
and ordered history of input words) and the list of extracted representatives, in order of
extraction. -/
structure CCState (α : Type cc_u) where
  current : Finset (Block α)
  reps : List (Block α)

/-- One step of MGREEDY's first stage (§2.4, p.8). Choose current blocks `a`, `b`, possibly
`a = b`, whose overlap `ov(a.word, b.word)` is maximum over ALL ordered pairs of current
blocks, self-pairs included; ties are arbitrary (including ties between a merge and an
extraction). If `a ≠ b`, both are replaced by their overlap merge; if `a = b`, `a` is removed
from the current set and appended unchanged to the representatives. -/
def CCStep {α : Type cc_u} [DecidableEq α] (s s' : CCState α) : Prop :=
  ∃ a ∈ s.current, ∃ b ∈ s.current,
    (∀ c ∈ s.current, ∀ d ∈ s.current,
      overlapLength c.word d.word ≤ overlapLength a.word b.word) ∧
    ((a ≠ b ∧ s' = ⟨insert (mergeBlocks a b) ((s.current.erase a).erase b), s.reps⟩) ∨
     (a = b ∧ s' = ⟨s.current.erase a, s.reps ++ [a]⟩))

/-- A complete run of MGREEDY's first stage on `S`: finitely many steps from the singleton
blocks of `S` with no representatives to the state with no current block. `reps` is the list
of extracted blocks; each extracted block with history `(t₁, …, t_r)` is the cycle
`C = (t₁, …, t_r, t₁)` of the constructed cycle cover. -/
def IsCycleCoverRun {α : Type cc_u} [DecidableEq α] (S : Finset (List α))
    (reps : List (Block α)) : Prop :=
  Relation.ReflTransGen CCStep (⟨initialBlocks S, []⟩ : CCState α) ⟨∅, reps⟩

/-- Cyclically consecutive pairs `(t₁,t₂), …, (t_{r-1},t_r), (t_r,t₁)` of a history
(`[(t₁,t₁)]` when `r = 1`). -/
def cyclePairs {α : Type cc_u} (h : List (List α)) : List (List α × List α) :=
  h.zip (h.rotate 1)

/-- `o(C)` (§2.4, p.8): the overlap length of the cycle-closing edge `(t_r, t₁)` of input
words. An empty history (never extracted) is assigned `0`. -/
def cycleOverlap {α : Type cc_u} [DecidableEq α] (h : List (List α)) : ℕ :=
  match h.head?, h.getLast? with
  | some t₁, some tr => overlapLength tr t₁
  | _, _ => 0

/-- `w(C)` (§2.3, p.7): the total prefix `Σ_{i=1}^{r} |pref(t_i, t_{i+1})|`, `t_{r+1} = t₁`. -/
def cyclePrefix {α : Type cc_u} [DecidableEq α] (h : List (List α)) : ℕ :=
  ((cyclePairs h).map (fun p => (pref p.1 p.2).length)).sum

/-- `τ(C)` (§2.6, p.9): the cycle string `pref(t₁,t₂) ∘ ⋯ ∘ pref(t_r,t₁)`. -/
def cycleString {α : Type cc_u} [DecidableEq α] (h : List (List α)) : List α :=
  (cyclePairs h).flatMap (fun p => pref p.1 p.2)

/-- `O = Σ_C o(C)` over the extracted cycles. -/
def totalOverlap {α : Type cc_u} [DecidableEq α] (reps : List (Block α)) : ℕ :=
  (reps.map (fun b => cycleOverlap b.history)).sum

/-- `W = Σ_C w(C)` over the extracted cycles. -/
def totalPrefix {α : Type cc_u} [DecidableEq α] (reps : List (Block α)) : ℕ :=
  (reps.map (fun b => cyclePrefix b.history)).sum

end GreedySuperstring.LowerBound.Supplement


