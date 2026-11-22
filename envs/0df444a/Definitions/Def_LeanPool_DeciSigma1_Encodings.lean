-- Prove2me | Definitions.Def_LeanPool_DeciSigma1_Encodings
-- name    : LeanPool_DeciSigma1_Encodings
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T15:19:17.247807+00:00
-- url     : https://prove2.me/theorems/4f8a931b-fc5f-471f-a8c3-68f0d0aee5f6
-- title:
--   Encodings
-- statement:
--   Definitions and structural lemmas for Encodings, from Yaoyu Zhao; LeanPool contributors's pinned Decidability of the Sigma-one theory of non-structural subtyping development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Encodings.lean

module
public import Definitions.Def_LeanPool_DeciSigma1_Entailment_Logic
public import Definitions.Def_LeanPool_DeciSigma1_Full_Logic
public import Theorems.Thm_DeciSigma1_Constraints_UpperAt_map

set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DeciSigma1.Logic
variable {T : Type → Type} {D V : Type} (I : Interpretation T D)
namespace QuantifierFreeFormula
def conj : List (QuantifierFreeFormula T V) → QuantifierFreeFormula T V
  | [] => .tt
  | φ :: φs => .and φ (conj φs)
def disj : List (QuantifierFreeFormula T V) → QuantifierFreeFormula T V
  | [] => .ff
  | φ :: φs => .or φ (disj φs)
end QuantifierFreeFormula
variable {m : ℕ}
def satisfiabilitySentence (φs : List (QuantifierFreeFormula T (Fin m))) : BooleanSentence T :=
  .ex ⟨m, .conj φs⟩
def entailmentSentence (φs ψs : List (QuantifierFreeFormula T (Fin m))) : BooleanSentence T :=
  .all ⟨m, .or (.not (.conj φs)) (.disj ψs)⟩
end DeciSigma1.Logic
namespace DeciSigma1.Full.Logic
open DeciSigma1.Constraints DeciSigma1.Logic DeciSigma1.Semantics
variable {n k m : ℕ} {V : Type} (c : Fin n → Bool)
def literal : LitT n V → QuantifierFreeFormula (Term n) V
  | .le x y => .le (.var x) (.var y)
  | .fLe a x => .le (.node fun i => .var (a i)) (.var x)
  | .leF x a => .le (.var x) (.node fun i => .var (a i))
  | .eqBot x => .eq (.var x) .bot
  | .eqTop x => .eq (.var x) .top
def queryFormulas (q : Fin k → V × V) : List (QuantifierFreeFormula (Term n) V) :=
  List.ofFn fun i => .le (.var (q i).1) (.var (q i).2)
def satisfiabilitySentence (Γ : List (LitT n (Fin m))) : BooleanSentence n :=
  DeciSigma1.Logic.satisfiabilitySentence (Γ.map literal)
def entailmentSentence (Γ : List (LitT n (Fin m))) (q : Fin k → Fin m × Fin m) :
    BooleanSentence n :=
  DeciSigma1.Logic.entailmentSentence (Γ.map literal) (queryFormulas q)
end DeciSigma1.Full.Logic
namespace DeciSigma1.Entailment.Logic
open DeciSigma1.Constraints.TopFree DeciSigma1.Logic DeciSigma1.Semantics
variable {n k m : ℕ} {V : Type}
def literal : Lit n V → QuantifierFreeFormula (BFTerm n) V
  | .le x y => .le (.var x) (.var y)
  | .fLe a x => .le (.node fun i => .var (a i)) (.var x)
  | .leF x a => .le (.var x) (.node fun i => .var (a i))
  | .eqBot x => .eq (.var x) .bot
def queryFormulas (q : Fin k → V × V) : List (QuantifierFreeFormula (BFTerm n) V) :=
  List.ofFn fun i => .le (.var (q i).1) (.var (q i).2)
def satisfiabilitySentence (Γ : List (Lit n (Fin m))) : BooleanSentence n :=
  DeciSigma1.Logic.satisfiabilitySentence (Γ.map literal)
def entailmentSentence (Γ : List (Lit n (Fin m))) (q : Fin k → Fin m × Fin m) :
    BooleanSentence n :=
  DeciSigma1.Logic.entailmentSentence (Γ.map literal) (queryFormulas q)
end DeciSigma1.Entailment.Logic


