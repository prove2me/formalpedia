-- Prove2me | Definitions.Def_GreedySuperstring_LowerBound_GreedyModel
-- name    : GreedySuperstring_LowerBound_GreedyModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:28:02.331972+00:00
-- url     : https://prove2.me/theorems/8b5769bf-631f-4801-92f5-d9534a1fca63
-- title:
--   Maximum-overlap greedy steps, finite runs, and constituent histories
-- statement:
--   A current block records an actual word and the ordered list of original words merged into it. Initially each input word is a singleton block. A step chooses two distinct current words $s,t$ whose overlap length is maximal among every ordered distinct current pair, removes their blocks, and inserts their actual overlap merge. Their histories are concatenated in the same order. No restriction is imposed on ties, including ties at zero overlap.
--
--   $$\mathcal B\longmapsto (\mathcal B\setminus\{a,b\})\cup\{(\langle s,t\rangle,h_a\circ h_b)\}.$$
--
--   A finite run consists of zero or more such updates and records the selected overlap lengths in chronological order. A greedy output is the word of the singleton block at the end of a complete run. The definitions assume no substring-free invariant, endpoint-overlap identity, termination certificate, successful schedule, or length formula. Lemma 2.1 supplies invariants for runs from admissible inputs.
--
--   **Formalization Note** States are finite sets of blocks over an arbitrary alphabet with decidable equality. Distinctness for a chosen pair concerns the words themselves. Source inputs have distinct nonempty substring-free members; Lemma 2.1 also ensures that distinct reachable blocks have distinct words, so the histories only annotate the source's current set.
-- source:
--   Nikolai Chukhin, Rishikesh Gajjala, Juha Harviainen, Alexander S. Kulikov, Ivan Mihajlin, Hiroki Shibata, Alexander V. Smal, The Greedy Superstring Conjecture Is False, STOC 2027 submission #316 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/316.pdf, §2.2, printed pp.5–7 = PDF pp.5–7, operational algorithm and bookkeeping for Lemma 2.1

import Mathlib
import Definitions.Def_GreedySuperstring_LowerBound_WordModel

universe greedy_u

namespace GreedySuperstring.LowerBound

/-- Bookkeeping only: current word and the ordered list of original constituents. -/
structure Block (α : Type greedy_u) where
  word : List α
  history : List (List α)
  deriving DecidableEq

def initialBlocks {α : Type greedy_u} [DecidableEq α] (S : Finset (List α)) : Finset (Block α) :=
  S.image (fun s => ⟨s, [s]⟩)

def mergeBlocks {α : Type greedy_u} [DecidableEq α] (a b : Block α) : Block α :=
  ⟨merge a.word b.word, a.history ++ b.history⟩

/-- Section 2.2, p.5. Maximality ranges over ALL ordered pairs of DISTINCT
current words. The chosen overlap length is recorded; ties include length zero. -/
def GreedyStep {α : Type greedy_u} [DecidableEq α]
    (B : Finset (Block α)) (l : ℕ) (B' : Finset (Block α)) : Prop :=
  ∃ a ∈ B, ∃ b ∈ B, a.word ≠ b.word ∧
    (∀ c ∈ B, ∀ d ∈ B, c.word ≠ d.word →
      overlapLength c.word d.word ≤ overlapLength a.word b.word) ∧
    l = overlapLength a.word b.word ∧
    B' = insert (mergeBlocks a b) ((B.erase a).erase b)

/-- Finite prefixes, including zero steps. No invariant or endpoint identity
is assumed; every nontrivial transition is an actual maximum-overlap update. -/
inductive GreedyRun {α : Type greedy_u} [DecidableEq α] :
    Finset (Block α) → List ℕ → Finset (Block α) → Prop where
  | nil (B : Finset (Block α)) : GreedyRun B [] B
  | cons {B B' B'' : Finset (Block α)} {l : ℕ} {ls : List ℕ} :
      GreedyStep B l B' → GreedyRun B' ls B'' → GreedyRun B (l :: ls) B''

/-- A complete execution must end at a singleton block with the given word. -/
def IsGreedyOutput {α : Type greedy_u} [DecidableEq α] (S : Finset (List α)) (g : List α) : Prop :=
  ∃ (h : List (List α)) (ls : List ℕ), GreedyRun (initialBlocks S) ls {⟨g, h⟩}

end GreedySuperstring.LowerBound


