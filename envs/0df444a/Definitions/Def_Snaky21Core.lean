-- Prove2me | Definitions.Def_Snaky21Core
-- name    : Snaky21Core
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-08T07:32:41.072604+00:00
-- url     : https://prove2.me/theorems/e4e6d1fa-2900-4c83-a455-ab723ed1409b
-- title:
--   Snaky21Core
-- statement:
--   Definitions for the finite conditional-claim proof of Snaky in 21 Maker moves. They use the existing integer-grid game and target, and encode the required Maker cells, the Breaker-free envelope, and the bound on actual further Maker claims. The numbered certificate data use the fixed 2026-09-25 source. No game-winning theorem is assumed.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Snaky-in-21-Maker-moves-September-25-2026/article.pdf; Definition 2, Lemma 3 and Proposition 5; pinned certificate supplement.

import Definitions.Def_SnakyTwentyOne

namespace OAI.Snaky21
open SnakyPrototype

def CanForce : ℕ → Finset Cell → Finset Cell → Prop
  | 0, M, _ => HasSnaky M
  | n + 1, M, B => ∃ m, m ∉ M ∧ m ∉ B ∧
      (HasSnaky (insert m M) ∨ ∀ b, b ∉ insert m M → b ∉ B →
        CanForce n (insert m M) (insert b B))

structure Card where
  required : Finset Cell
  envelope : Finset Cell
  height : ℕ
  deriving DecidableEq

def Valid (c : Card) : Prop :=
  c.required ⊆ c.envelope ∧ 0 < c.height ∧
    ∀ M B, c.required ⊆ M → Disjoint B c.envelope →
      CanForce c.height M B

def unionRequired (cs : List Card) : Finset Cell :=
  (cs.map Card.required).foldr (· ∪ ·) ∅
def unionEnvelope (cs : List Card) : Finset Cell :=
  (cs.map Card.envelope).foldr (· ∪ ·) ∅
def commonEnvelope : List Card → Finset Cell
  | [] => ∅
  | c :: cs => cs.foldr (fun d s => d.envelope ∩ s) c.envelope
def maxHeight (cs : List Card) : ℕ :=
  (cs.map Card.height).foldr max 0

def combine (p : Cell) (cs : List Card) : Card :=
  ⟨(unionRequired cs ∪ commonEnvelope cs).erase p,
    insert p (unionEnvelope cs), 1 + maxHeight cs⟩

def placed (r : Fin 8) (t : Cell) (c : Card) : Card :=
  ⟨c.required.image (placement r t), c.envelope.image (placement r t), c.height⟩

def basePoint (i : Fin 6) : Cell := ![(0,0),(1,0),(2,0),(3,0),(3,1),(4,1)] i
def baseCard (i : Fin 6) : Card := ⟨snaky.erase (basePoint i), snaky, 1⟩

def MoveOK (r : ℕ) (M B : Finset Cell) (m : Cell) : Prop :=
  m ∉ M ∧ m ∉ B ∧ (HasSnaky (insert m M) ∨
    ∀ b, b ∉ insert m M → b ∉ B → CanForce (r - 1) (insert m M) (insert b B))

def freshCell (M B : Finset Cell) : Cell :=
  (((M ∪ B).sup (fun x => x.1.natAbs) + 1 : ℕ), 0)

noncomputable def forcePolicy : SnakyPrototype.OrdinaryStrategy.Policy Cell := by
  classical
  exact fun r M B => if h : ∃ m, MoveOK r M B m then Classical.choose h else freshCell M B

end OAI.Snaky21


