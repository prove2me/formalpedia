-- Prove2me | Definitions.Def_DeletionHash_MixedEdit_Channel
-- name    : DeletionHash_MixedEdit_Channel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:40:58.327767+00:00
-- url     : https://prove2.me/theorems/d24158fb-baa3-4c62-838c-ceb690fd733b
-- title:
--   Reachability, common descendants and correction
-- statement:
--   For words $x,y$, bounded reachability means that an actual valid record of at most $t$ bounded substring edits transforms $x$ to $y$. Two words are confusable when some finite word is reachable from each within that budget. A finite length-$n$ code corrects the channel when every pair of distinct codewords fails to be confusable. In symbols,
--   $$x\sim_{b,t}y\iff \exists u:\ x\leadsto_{b,t}u\ \land\ y\leadsto_{b,t}u.$$
--   The budget is a total number of edits on each side, and the common word has unrestricted length. For $b=1$ the permitted proper replacements are exactly single insertions, deletions and substitutions. This operational relation is shared by the goals and conflict graph.
-- source:
--   Eyal En Gad, STOC 2027 submission #408 (October 2026), §1.1, confusability and correcting codes, printed p. 1 (PDF p. 3); §1.3, bounded substring channel, printed p. 2 (PDF p. 4); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/408.pdf

import Definitions.Def_DeletionHash_MixedEdit_Edits

namespace DeletionHash.MixedEdit

universe u

def Reaches {α : Type u} (b t : ℕ) (x y : List α) : Prop :=
  ∃ record : List (Edit α), record.length ≤ t ∧ ValidRecord b x record ∧ target x record = y

def Confusable {α : Type u} (b t : ℕ) (x y : List α) : Prop :=
  ∃ z : List α, Reaches b t x z ∧ Reaches b t y z

/-- At b=1 these are precisely unit-cost insertion, deletion and proper substitution. -/
def Corrects {α : Type u} {n : ℕ} (b t : ℕ) (C : Finset (Word α n)) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, x ≠ y → ¬ Confusable b t (letters x) (letters y)

end DeletionHash.MixedEdit


