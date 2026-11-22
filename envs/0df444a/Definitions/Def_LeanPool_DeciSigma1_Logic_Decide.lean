-- Prove2me | Definitions.Def_LeanPool_DeciSigma1_Logic_Decide
-- name    : LeanPool_DeciSigma1_Logic_Decide
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T15:06:07.552805+00:00
-- url     : https://prove2.me/theorems/6bc6a3e8-45a6-49f8-941a-c952ba2809c3
-- title:
--   Decide
-- statement:
--   Definitions and structural lemmas for Decide, from Yaoyu Zhao; LeanPool contributors's pinned Decidability of the Sigma-one theory of non-structural subtyping development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Logic/Decide.lean

module
public import Mathlib.Data.Fintype.Sum
public import Definitions.Def_LeanPool_DeciSigma1_Logic_Flatten
public import Theorems.Thm_DeciSigma1_Logic_BooleanSentence_all_iff_not_ex_not
public import Theorems.Thm_DeciSigma1_Logic_ConjunctiveClause_holds_append
public import Theorems.Thm_DeciSigma1_Logic_ConjunctiveClause_realizable_iff_not_disjEntailsIn
public import Theorems.Thm_DeciSigma1_Logic_QuantifierFreeFormula_holds_iff_dnf
attribute [local simp] DeciSigma1.Logic.ConjunctiveClause.holds_append


set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DeciSigma1.Logic
variable {T : Type → Type} {D : Type} {I : Interpretation T D} (F : Flattening I)
abbrev DisjEntailmentDecider (C : D → Prop) :=
  ∀ {W : Type} [Fintype W] [DecidableEq W] {k : ℕ} (Γ : List (F.Lit W)) (q : Fin k → W × W),
    Decidable (F.DisjEntailsIn C Γ q)
def ConjunctiveClause.Realizable {V : Type} (c : ConjunctiveClause T V) (I : Interpretation T D)
    (C : D → Prop) :
    Prop :=
  ∃ ρ : V → D, (∀ v, C (ρ v)) ∧ c.Holds I ρ
theorem Sigma1.holdsIn_iff_exists_realizable (s : Sigma1 T) (C : D → Prop) :
    s.HoldsIn I C ↔ ∃ c ∈ s.body.dnf, c.Realizable I C := by
  simp only [Sigma1.HoldsIn, QuantifierFreeFormula.holds_iff_dnf, ConjunctiveClause.Realizable]
  aesop
variable [∀ m, DecidableEq (T (Fin m))] {C : D → Prop}
def decideRealizable (hC : I.TermClosed C) (dec : DisjEntailmentDecider F C) {m : ℕ}
    (c : ConjunctiveClause T (Fin m)) : Decidable (c.Realizable I C) :=
  letI := dec (c.constraints F) (c.queries F)
  decidable_of_iff _ (c.realizable_iff_not_disjEntailsIn F hC).symm
def decideSigma1 (hC : I.TermClosed C) (dec : DisjEntailmentDecider F C) (s : Sigma1 T) :
    Decidable (s.HoldsIn I C) :=
  letI (c : ConjunctiveClause T (Fin s.variableCount)) := decideRealizable F hC dec c
  decidable_of_iff _ (s.holdsIn_iff_exists_realizable C).symm
def decideBooleanSentence (hC : I.TermClosed C) (dec : DisjEntailmentDecider F C) :
    (φ : BooleanSentence T) → Decidable (φ.HoldsIn I C)
  | .ex s => decideSigma1 F hC dec s
  | .all s =>
    letI := decideSigma1 F hC dec ⟨s.variableCount, .not s.body⟩
    decidable_of_iff _ (BooleanSentence.all_iff_not_ex_not I C s).symm
  | .not φ =>
    letI := decideBooleanSentence hC dec φ
    inferInstanceAs (Decidable (¬ φ.HoldsIn I C))
  | .and φ ψ =>
    letI := decideBooleanSentence hC dec φ
    letI := decideBooleanSentence hC dec ψ
    inferInstanceAs (Decidable (φ.HoldsIn I C ∧ ψ.HoldsIn I C))
  | .or φ ψ =>
    letI := decideBooleanSentence hC dec φ
    letI := decideBooleanSentence hC dec ψ
    inferInstanceAs (Decidable (φ.HoldsIn I C ∨ ψ.HoldsIn I C))
end DeciSigma1.Logic


