-- Prove2me | Definitions.Def_LeanPool_DeciSigma1_Examples_Sentences
-- name    : LeanPool_DeciSigma1_Examples_Sentences
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T15:22:27.268165+00:00
-- url     : https://prove2.me/theorems/08f46c38-c30d-42bc-b67c-6933ec324d90
-- title:
--   Sentences
-- statement:
--   Definitions and structural lemmas for Sentences, from Yaoyu Zhao; LeanPool contributors's pinned Decidability of the Sigma-one theory of non-structural subtyping development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Examples/Sentences.lean

module
public import Definitions.Def_LeanPool_DeciSigma1_Examples_Entailment
public import Definitions.Def_LeanPool_DeciSigma1_Main
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DeciSigma1.Examples
open DeciSigma1.Semantics DeciSigma1.Full.Models
def comparable (n : ℕ) : DeciSigma1.Entailment.Logic.BooleanSentence n :=
  .all ⟨2, .or (.le (.var 0) (.var 1)) (.le (.var 1) (.var 0))⟩
def postFixedPoint : DeciSigma1.Entailment.Logic.BooleanSentence 1 :=
  .ex ⟨1, .le (.node fun _ => .var 0) (.var 0)⟩
def fixedPoint : DeciSigma1.Full.Logic.BooleanSentence 1 :=
  .ex ⟨1, .eq (.var 0) (.node (fun _ => .var 0))⟩
end DeciSigma1.Examples


