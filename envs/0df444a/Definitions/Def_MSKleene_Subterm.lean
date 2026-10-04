-- Prove2me | Definitions.Def_MSKleene_Subterm
-- name    : MSKleene_Subterm
-- status  : Definition
-- author  : @Cosme
-- created : 2026-09-08T12:28:58.887126+00:00
-- url     : https://prove2.me/theorems/f16219db-7aac-4268-814c-d69bd8ab2ff3
-- title:
--   The subterm order
-- statement:
--   The **subterm order** on the free many-sorted algebra (Definitions 2.30, 3.7, 3.8).
--
--   `ImmSub a b` holds when the sorted term `a` (an element of the coproduct $\coprod_s \mathrm{T}_\Sigma(X)_s$, `STerm`) is an immediate argument of `b` in `b`'s unique decomposition. Its transitive closure `SubtermLT` is the strict proper-subterm order `<`; its reflexive–transitive closure `SubtermLE` is `≤`; `Min b` says `b` has no proper subterm; `Subt P` is the $S$-sorted set of subterms of `P`. `TermVec.Mem` is entry membership in an argument vector.
--
--   Proposition 3.6 (a milestone) states that `SubtermLT` is Artinian and that its minimal elements are exactly the variables and the constant symbols.
-- source:
--   Gong, Ruiz Mora, Sanmartín Vich, Cosme Llópez, "A Kleene theorem for free many-sorted algebras", 2026

/-
The subterm order on the free many-sorted algebra (Definitions 2.30, 3.7).

`ImmSub a b` holds when the sorted term `a` is an immediate argument of `b`
(one decomposition step). Its transitive closure `SubtermLT` is the strict
proper-subterm order `<`, its reflexive–transitive closure `SubtermLE` is `≤`,
and `Min` picks out the minimal sorted terms.

Proposition 3.6 (`PArtOrd`) — proved as a milestone — states that `SubtermLT` is
Artinian (well-founded) on the free algebra and that its minimal elements are
exactly the variables and the constant symbols.
-/
import Definitions.Def_MSKleene_Term
import Mathlib.Logic.Relation

namespace MSKleene

universe u

variable {S : Type u} {sig : Signature S} {X : SSet S}

/-- A **sorted term**: an element of the coproduct `∐_s T_Σ(X)_s`. -/
def STerm (sig : Signature S) (X : SSet S) : Type u := Σ s : S, Term sig X s

/-- `p` occurs as one of the entries of the term vector `ts`. -/
inductive TermVec.Mem {sig : Signature S} {X : SSet S} :
    {t : S} → {w : List S} → Term sig X t → TermVec sig X w → Prop
  | head {t : S} {w : List S} (p : Term sig X t) (ps : TermVec sig X w) :
      TermVec.Mem p (.cons p ps)
  | tail {t s : S} {w : List S} {p : Term sig X t} (q : Term sig X s)
      {ps : TermVec sig X w} : TermVec.Mem p ps → TermVec.Mem p (.cons q ps)

/-- The immediate-subterm relation `<_{T_Σ(X)}` (Definition 2.30): `a` is an
immediate argument of `b` in `b`'s unique decomposition. -/
def ImmSub (a b : STerm sig X) : Prop :=
  ∃ (w : List S) (σ : sig w b.1) (ts : TermVec sig X w),
    b.2 = Term.app σ ts ∧ TermVec.Mem a.2 ts

/-- The strict proper-subterm order `<` — the transitive closure of `ImmSub`. -/
def SubtermLT (a b : STerm sig X) : Prop := Relation.TransGen ImmSub a b

/-- The subterm order `≤` — the reflexive–transitive closure of `ImmSub`. -/
def SubtermLE (a b : STerm sig X) : Prop := Relation.ReflTransGen ImmSub a b

/-- A sorted term is **minimal** when it has no proper subterm. -/
def Min (b : STerm sig X) : Prop := ∀ a : STerm sig X, ¬ ImmSub a b

/-- `Subt P` — the `S`-sorted set of subterms of `P` (Definition 3.8). -/
def Subt {s : S} (P : Term sig X s) : SSub (Term sig X) :=
  fun t => { Q : Term sig X t | SubtermLE ⟨t, Q⟩ ⟨s, P⟩ }

end MSKleene


