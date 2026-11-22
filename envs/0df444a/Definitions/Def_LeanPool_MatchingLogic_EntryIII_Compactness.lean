-- Prove2me | Definitions.Def_LeanPool_MatchingLogic_EntryIII_Compactness
-- name    : LeanPool_MatchingLogic_EntryIII_Compactness
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:14:51.17232+00:00
-- url     : https://prove2.me/theorems/093b733c-eedf-4bad-8927-e45a1e584220
-- title:
--   Compactness
-- statement:
--   Definitions and structural lemmas for Compactness, from Aurélien Eveil; Anthropic; OpenAI; LeanPool contributors's pinned Global completeness of one-sorted definedness-free matching logic development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Compactness.lean

module
public import Definitions.Def_LeanPool_MatchingLogic_Semantics
public import Mathlib.ModelTheory.Satisfiability
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace MatchingLogic.EntryIII
open FirstOrder
universe u
variable {S : Signature} {Var : Type} [DecidableEq Var]
def relLanguage (S : Signature) : FirstOrder.Language where
  Functions := fun _ => Empty
  Relations := fun n => { sigma : S.Sym // S.arity sigma + 1 = n }
instance relLanguage_isRelational (S : Signature) : (relLanguage S).IsRelational :=
  fun _ => ⟨fun x => nomatch x⟩
def relSym (sigma : S.Sym) : (relLanguage S).Relations (S.arity sigma + 1) :=
  ⟨sigma, rfl⟩
noncomputable def Pattern.toFOAux :
    (p : Pattern S Var) →
      ∀ {alpha : Type u}, (Var → alpha) → alpha → (relLanguage S).Formula alpha
  | .var x, _, eta, cur =>
      FirstOrder.Language.Term.equal (.var cur) (.var (eta x))
  | .bot, _, _, _ => ⊥
  | .imp phi psi, _, eta, cur =>
      (toFOAux phi eta cur).imp (toFOAux psi eta cur)
  | .ex x phi, alpha, eta, cur =>
      let eta' : Var → alpha ⊕ Unit :=
        Function.update (Sum.inl ∘ eta) x (Sum.inr ())
      (toFOAux phi eta' (Sum.inl cur)).iExs Unit
  | .app sigma args, alpha, eta, cur =>
      let body : (relLanguage S).Formula (alpha ⊕ Fin (S.arity sigma)) :=
        (relSym sigma).formula
            (Fin.cons (.var (Sum.inl cur)) (fun i => .var (Sum.inr i))) ⊓
          FirstOrder.Language.Formula.iInf
            (fun i => toFOAux (args i) (Sum.inl ∘ eta) (Sum.inr i))
      body.iExs (Fin (S.arity sigma))
noncomputable def Pattern.toFOFormula (p : Pattern S Var) :
    (relLanguage S).Formula (Option Var) :=
  MatchingLogic.EntryIII.Pattern.toFOAux p some none
noncomputable def Pattern.toFOSentence (p : Pattern S Var) :
    (relLanguage S)[[Option Var]].Sentence :=
  FirstOrder.Language.Formula.equivSentence
    (MatchingLogic.EntryIII.Pattern.toFOFormula p)
namespace Model
@[instance_reducible] def toFOStructure (M : Model S) :
    (relLanguage S).Structure M.carrier where
  RelMap := fun {n} r xs =>
    let ys : Fin (S.arity r.1 + 1) → M.carrier := fun i => xs (Fin.cast r.2 i)
    ys 0 ∈ M.interp r.1 (fun i => ys i.succ)
abbrev ofFOStructure (A : Type) [Nonempty A]
    [(relLanguage S)[[Option Var]].Structure A] : Model S where
  carrier := A
  nonempty := inferInstance
  interp sigma args :=
    {out | @FirstOrder.Language.Structure.RelMap
      ((relLanguage S)[[Option Var]]) A inferInstance (S.arity sigma + 1)
      (Sum.inl (relSym sigma)) (Fin.cons out args)}
def ofFOValuation (A : Type) [(relLanguage S)[[Option Var]].Structure A] : Var → A :=
  fun x => ((relLanguage S).con (some x) : A)
def ofFOCurrent (A : Type) [(relLanguage S)[[Option Var]].Structure A] : A :=
  ((relLanguage S).con (none : Option Var) : A)
end Model
def Model.toFOParameters (M : Model S) (rho : Var → M.carrier) (u : M.carrier) :
    Option Var → M.carrier
  | none => u
  | some x => rho x
noncomputable def counterTheory (Delta : Set (Pattern S Var)) (phi : Pattern S Var) :
    (relLanguage S)[[Option Var]].Theory :=
  MatchingLogic.EntryIII.Pattern.toFOSentence '' Delta ∪
    {(MatchingLogic.EntryIII.Pattern.toFOSentence phi).not}
end MatchingLogic.EntryIII
namespace MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
end MatchingLogic


