-- Prove2me | Definitions.Def_Bagaria_reinhardt
-- name    : Bagaria_reinhardt
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-19T23:05:52.775073+00:00
-- url     : https://prove2.me/theorems/5ac51d74-3935-4eb9-88be-6c63834e47f1
-- title:
--   The Reinhardt hierarchy: super, A-super, and totally Reinhardt cardinals
-- statement:
--   The Reinhardt hierarchy of large cardinals beyond Choice. A cardinal κ is Reinhardt when there is a non-trivial elementary self-embedding of the universe whose critical point is κ. It is super Reinhardt when for every ordinal λ some such embedding sends the code of κ to the code of an ordinal above λ, and A-super Reinhardt for a class A when moreover every witnessing embedding fixes A pointwise. Inside a rank segment below γ, the segment contains a Reinhardt cardinal when some non-trivial elementary self-embedding of the segment has a critical point; δ' is super Reinhardt within the segment below δ when for every λ below δ some non-trivial elementary self-embedding of the segment with critical point δ' sends the code of δ' above λ; and similarly A-super Reinhardt with classes of the segment. A cardinal κ is totally Reinhardt when the segment below κ satisfies ZF and, for every class A of the segment, the segment contains an A-super Reinhardt cardinal. A cardinal κ is extendible when for every λ above κ there is an elementary embedding of the segment below λ into some higher segment with critical point κ sending the code of κ above λ; and the critical point of an embedding between segments is the least ordinal whose code inside the domain the embedding moves.
-- source:
--   Bagaria (2017), Large Cardinals beyond Choice, AILA XXVI slides, pp. 10-11 and 16; Kanamori (2003), The Higher Infinite, for extendible cardinals

import Mathlib
import Definitions.Def_Bagaria_arena

universe v

/-!
# Large cardinals beyond Choice: the Reinhardt hierarchy

Reinhardt, super Reinhardt, A-super Reinhardt, and totally Reinhardt
cardinals, the relativized internal forms within rank segments, critical
points of embeddings between segments, and extendible cardinals
(slides 8-11 and 13 of the source).
-/

namespace Bagaria

namespace Universe

variable (U : Universe.{v})

/-- κ is a Reinhardt cardinal (slide 8): there is a non-trivial elementary
self-embedding of the universe whose critical point is κ. -/
def isReinhardt (κ : Ordinal.{v}) : Prop :=
  ∃ j : U.carrier → U.carrier,
    j ≠ id ∧ IsElementaryOf U.mem U.mem j ∧ U.critIs j κ

/-- κ is super Reinhardt (slide 10): for every ordinal α there is a
non-trivial elementary self-embedding of the universe with critical point
κ whose value at the code of κ is the code of an ordinal above α. -/
def isSuperReinhardt (κ : Ordinal.{v}) : Prop :=
  ∀ α : Ordinal.{v}, ∃ j : U.carrier → U.carrier,
    j ≠ id ∧ IsElementaryOf U.mem U.mem j ∧ U.critIs j κ ∧
    ∃ μ : Ordinal.{v}, α < μ ∧ j (U.ord κ) = U.ord μ

/-- κ is A-super Reinhardt for the class A of the universe (slide 10): the
super Reinhardt property with every witnessing embedding fixing the class
A pointwise. The class condition j(A) = A of the source is approximated by
pointwise invariance of the predicate A along the embedding. -/
def isASuperReinhardt (κ : Ordinal.{v}) (A : U.carrier → Prop) : Prop :=
  ∀ α : Ordinal.{v}, ∃ j : U.carrier → U.carrier,
    j ≠ id ∧ IsElementaryOf U.mem U.mem j ∧ U.critIs j κ ∧
    ∃ μ : Ordinal.{v}, α < μ ∧ j (U.ord κ) = U.ord μ ∧
    ∀ x : U.carrier, A x ↔ A (j x)

/-- The rank segment below γ contains a Reinhardt cardinal (slides 10-11):
there is a non-trivial elementary self-embedding of the segment with a
critical point. This is the first-order approximation of the statement
that ⟨V_γ, V_{γ+1}⟩ satisfies "There exists a Reinhardt cardinal". -/
def hasReinhardtIn (γ : Ordinal.{v}) : Prop :=
  ∃ κ : Ordinal.{v}, ∃ j : U.segment γ → U.segment γ,
    j ≠ id ∧ IsElementaryOf (U.segmentMem γ) (U.segmentMem γ) j ∧
      U.critIsIn γ j κ

/-- δ' is super Reinhardt within the rank segment below δ (slide 16): for
every ordinal α below δ there is a non-trivial elementary self-embedding
of the segment with critical point δ' whose value at the code of δ' is the
code of an ordinal above α. -/
def superReinhardtIn (δ δ' : Ordinal.{v}) : Prop :=
  ∀ h : δ' < δ,
    ∀ α : Ordinal.{v}, α < δ →
      ∃ j : U.segment δ → U.segment δ,
        j ≠ id ∧ IsElementaryOf (U.segmentMem δ) (U.segmentMem δ) j ∧
          U.critIsIn δ j δ' ∧
          ∃ μ : Ordinal.{v}, α < μ ∧ (j (U.segOrd δ δ' h)).val = U.ord μ

/-- δ' is A-super Reinhardt within the rank segment below γ (slide 10,
relativized): for every ordinal α below γ there is a non-trivial
elementary self-embedding of the segment with critical point δ' whose
value at the code of δ' is the code of an ordinal above α, and which fixes
the class A of the segment pointwise. -/
def aSuperReinhardtIn (γ δ' : Ordinal.{v}) (A : U.segment γ → Prop) : Prop :=
  ∀ h : δ' < γ,
    ∀ α : Ordinal.{v}, α < γ →
      ∃ j : U.segment γ → U.segment γ,
        j ≠ id ∧ IsElementaryOf (U.segmentMem γ) (U.segmentMem γ) j ∧
          U.critIsIn γ j δ' ∧
          ∃ μ : Ordinal.{v}, α < μ ∧ (j (U.segOrd γ δ' h)).val = U.ord μ ∧
          ∀ x : U.segment γ, A x ↔ A (j x)

/-- κ is totally Reinhardt (slide 10): the rank segment below κ satisfies
ZF and for every class A of the segment — the first-order approximation of
every A ∈ V_{κ+1} — the segment contains an A-super Reinhardt cardinal. -/
def isTotallyReinhardt (κ : Ordinal.{v}) : Prop :=
  SatisfiesZF (U.segmentMem κ) ∧
  ∀ A : U.segment κ → Prop, ∃ δ' : Ordinal.{v}, U.aSuperReinhardtIn κ δ' A

/-- The critical point of an embedding between two rank segments
j : V_α → V_β: the ordinal κ whose code inside the domain segment the
embedding moves, while fixing the code of every smaller ordinal. -/
def critIsOf (α β : Ordinal.{v}) (j : U.segment α → U.segment β)
    (κ : Ordinal.{v}) : Prop :=
  ∃ hκ : κ < α,
    (j (U.segOrd α κ hκ)).val ≠ U.ord κ ∧
    ∀ ν : Ordinal.{v}, ν < κ → ∀ hν : ν < α,
      (j (U.segOrd α ν hν)).val = U.ord ν

/-- κ is extendible: for every ordinal α above κ there are an ordinal β
and a non-trivial elementary embedding of rank segments j : V_α → V_β with
critical point κ whose value at the code of κ is the code of an ordinal
above α. -/
def isExtendible (κ : Ordinal.{v}) : Prop :=
  ∀ α : Ordinal.{v}, ∀ hα : κ < α,
    ∃ β : Ordinal.{v}, ∃ j : U.segment α → U.segment β,
      IsElementaryOf (U.segmentMem α) (U.segmentMem β) j ∧ U.critIsOf α β j κ ∧
      ∃ μ : Ordinal.{v}, α < μ ∧ (j (U.segOrd α κ hα)).val = U.ord μ

end Universe

end Bagaria


