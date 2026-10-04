-- Prove2me | Definitions.Def_MSKleene_RegSig
-- name    : MSKleene_RegSig
-- status  : Definition
-- author  : @Cosme
-- created : 2026-09-08T12:28:10.549066+00:00
-- url     : https://prove2.me/theorems/19516141-ccc5-467b-b968-a9c5fadbba92
-- title:
--   The regular signature $\mathrm{Reg}(S,\Sigma,Z)$
-- statement:
--   (updated) The regular signature $\mathrm{Reg}(S,\Sigma,Z)$. See the mission's other definition items for the surrounding development.
-- source:
--   Gong, Ruiz Mora, Sanmartín Vich, Cosme Llópez, "A Kleene theorem for free many-sorted algebras", 2026

/-
The regular signature `Reg(S,Σ,Z)` (Definition 4.1) and regular expressions
(Definition 4.2).

`Reg(S,Σ,Z)` expands `Σ`, for a fixed `S`-sorted set `Z`, by:
  * an empty constant `∅_s` of coarity `s`               (rank `([], s)`);
  * a binary sum `+_s` of coarity `s`                    (rank `([s,s], s)`);
  * a unary `z`-iteration `(·)^{⋆z}` for each `z ∈ Z_s`  (rank `([s], s)`);
  * a `z`-substitution `⟨z/·⟩^♯ᵖ_s(·)` for each `z ∈ Z_t` (rank `([t,s], s)`).

A **regular expression over `(S,Σ,Z)` of type `s`** is a term of the free
`Reg(S,Σ,Z)`-algebra on `Z`, i.e. an element of `Term (regSig sig Z) Z s`.

Also here: `Term.relabel`, the action of `T_Σ(-)` on an `S`-sorted map of
variables, used to view `T_Σ(X)` inside `T_Σ(Z)` when `X ⊆ Z`.
-/
import Definitions.Def_MSKleene_Term

namespace MSKleene

universe u

variable {S : Type u}

/-- The operation symbols of the regular signature `Reg(S,Σ,Z)` (Definition 4.1),
indexed by rank `(w, s)`. `base` re-uses every symbol of `Σ`; the four extra
constructors are `∅_s`, `+_s`, `(·)^{⋆z}`, and `⟨z/·⟩^♯ᵖ_s(·)`. -/
inductive RegSym (sig : Signature S) (Z : SSet S) : List S → S → Type u where
  | base {w : List S} {s : S} : sig w s → RegSym sig Z w s
  | empty (s : S) : RegSym sig Z [] s
  | iter (s : S) : Z s → RegSym sig Z [s] s
  | plus (s : S) : RegSym sig Z [s, s] s
  | subst (t s : S) : Z t → RegSym sig Z [t, s] s

/-- The regular signature `Reg(S,Σ,Z)` as an `S`-sorted signature. -/
def regSig (sig : Signature S) (Z : SSet S) : Signature S := RegSym sig Z

/-- A regular expression over `(S,Σ,Z)` of type `s` (Definition 4.2). -/
abbrev RegExpr (sig : Signature S) (Z : SSet S) (s : S) : Type u :=
  Term (regSig sig Z) Z s

-- Relabel the variables of a term along an `S`-sorted map `ι : X → Y`
-- (functoriality of `T_Σ(-)`). Used with an inclusion `X ↪ Z`.
mutual
def Term.relabel {sig : Signature S} {X Y : SSet S} (ι : SMap X Y) :
    {s : S} → Term sig X s → Term sig Y s
  | _, .var x => Term.var (ι _ x)
  | _, .app σ ts => Term.app σ (TermVec.relabel ι ts)
def TermVec.relabel {sig : Signature S} {X Y : SSet S} (ι : SMap X Y) :
    {w : List S} → TermVec sig X w → TermVec sig Y w
  | _, .nil => .nil
  | _, .cons t ts => .cons (Term.relabel ι t) (TermVec.relabel ι ts)
end

-- Embed a `Σ`-term as a regular expression over `(S,Σ,Z)` of the same type:
-- every operation symbol `σ` becomes `RegSym.base σ` (Lemma 4.9).
mutual
def Term.toReg {sig : Signature S} {Z : SSet S} :
    {s : S} → Term sig Z s → RegExpr sig Z s
  | _, .var x => Term.var x
  | _, .app σ ts => Term.app (RegSym.base σ) (TermVec.toReg ts)
def TermVec.toReg {sig : Signature S} {Z : SSet S} :
    {w : List S} → TermVec sig Z w → TermVec (regSig sig Z) Z w
  | _, .nil => .nil
  | _, .cons t ts => .cons (Term.toReg t) (TermVec.toReg ts)
end

end MSKleene


