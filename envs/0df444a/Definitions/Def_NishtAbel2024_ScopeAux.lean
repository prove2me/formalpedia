-- Prove2me | Definitions.Def_NishtAbel2024_ScopeAux
-- name    : NishtAbel2024_ScopeAux
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-01T20:55:54.717727+00:00
-- url     : https://prove2.me/theorems/bdf7341a-db01-452e-bcf8-7095aab3a893
-- title:
--   Function-reference scope for signature extensions
-- statement:
--   For the existing Nisht–Abel Lean syntax, collect all function references in a term, elimination or clause. A signature is closed when its function names are unique and every declaration references only those names. A scoped block extension has unique new names disjoint from the old names, a closed old signature, and declarations that reference only the combined old and new names. These are auxiliary syntactic conditions, not an assertion that semantic typing is preserved.
-- source:
--   Auxiliary result for the current Lean model inspired by Kanstantsin Nisht, Type-Based Termination Checking in Agda (2024), supervised by Andreas Abel, https://knisht.github.io/agda/msc.pdf, Section 5.4.2, pp. 36–37. The exact syntactic predicates and iff theorem are not stated verbatim in the thesis.

import Definitions.Def_NishtAbel2024_Syntax

namespace NishtAbel2024

/-!
Candidate *syntactic* scope discipline for the ordered global environment in
Nisht–Abel §5.4.2. This is not an environment-extension theorem and is not
claimed to suffice for reducibility-candidate stability.
-/

mutual

/-- Collect all function references, including those under nested clauses. -/
def scopeTermRefs : Term → List FunName
  | .var _ => []
  | .funRef f _ => [f]
  | .app r e => scopeTermRefs r ++ scopeElimRefs e
  | .unit => []
  | .pair a b => scopeTermRefs a ++ scopeTermRefs b
  | .cons _ _ t => scopeTermRefs t
  | .pack _ t => scopeTermRefs t
  | .lamClauses ds => scopeClausesRefs ds
  | .ascr t _ => scopeTermRefs t

def scopeElimRefs : Elim → List FunName
  | .term t => scopeTermRefs t
  | .tyArg _ => []
  | .proj _ _ => []

def scopeClauseRefs : Clause → List FunName
  | .mk _ t => scopeTermRefs t

def scopeClausesRefs : List Clause → List FunName
  | [] => []
  | d :: ds => scopeClauseRefs d ++ scopeClausesRefs ds

end

def scopeNames (sig : GlobalSig) : List FunName := sig.map FunDecl.name

/-- Each syntactic call in a declaration resolves within `allowed`. -/
def scopeDeclClosed (allowed : List FunName) (decl : FunDecl) : Prop :=
  ∀ f ∈ scopeClausesRefs decl.clauses, f ∈ allowed

/-- A flat signature is name-unique and has no unresolved function names. -/
def scopeSignatureClosed (sig : GlobalSig) : Prop :=
  (scopeNames sig).Nodup ∧ ∀ decl ∈ sig, scopeDeclClosed (scopeNames sig) decl

/-- A block may refer to the earlier signature and its own mutual names;
its names are fresh and unique. -/
def scopeBlockExtension (sig : GlobalSig) (block : MutualBlock) : Prop :=
  scopeSignatureClosed sig ∧
  (scopeNames block).Nodup ∧
  (∀ f ∈ scopeNames block, f ∉ scopeNames sig) ∧
  (∀ decl ∈ block, scopeDeclClosed (scopeNames sig ++ scopeNames block) decl)


end NishtAbel2024


