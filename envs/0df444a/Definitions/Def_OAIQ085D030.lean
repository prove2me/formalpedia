-- Prove2me | Definitions.Def_OAIQ085D030
-- name    : OAIQ085D030
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T17:01:32.752896+00:00
-- url     : https://prove2.me/theorems/b35a860c-2d7b-4d33-8dea-516d490444fc
-- title:
--   Definitions bundle OAIQ085D030 of the split of OpenAI, Constant-factor hardness of directed feedback vertex set (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DirectedFeedback.main`, carved from OpenAI's openai/math development (OpenAI, *Constant-factor hardness of directed feedback vertex set (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 6 declarations of OpenAI's Lean: 1 definition and 5 theorems. The definitions and types are `OAI.DirectedFeedback.RawFamily.reduction`.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: [`DirectedFeedback_Main`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DirectedFeedback/Main.lean), [`DirectedFeedback_RankGraph_PacketLocality`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DirectedFeedback/RankGraph/PacketLocality.lean), [`DirectedFeedback_RankGraph_Rational`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DirectedFeedback/RankGraph/Rational.lean).
--
--   **Imports.** It imports the published bundle `Def_DirectedFeedback`; the bundles `OAIQ085D027` and `OAIQ085D028` of this split.
--
--   **Imported by** (directly, in this split): the proof of `OAI.DirectedFeedback.main`.
-- source:
--   OpenAI, Constant-factor hardness of directed feedback vertex set (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Constant-factor-hardness-of-directed-feedback-vertex-set-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Definitions.Def_DirectedFeedback
import Definitions.Def_OAIQ085D027
import Definitions.Def_OAIQ085D028

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_Rational
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.GameRead
open BoundedExpr BoundedExpr.UnaryRead
open DFVSGames.Foundations DFVSGames.Foundations.Target DFVSGames.Foundations.Complexity
open DFVSGames.Explicit.MachineOutputContract

variable (q : Nat) [NeZero q]

omit [NeZero q] in
theorem left_encoded (I : Instance q) (e : FullGame.Edge I) :
    left q (gameBits I) e.val=I.constraints[e].source.val := by
  rw [left,field_encoded q I e 0 (by omega),n_encoded]
  simp only [constraintWords,List.getElem?_append,List.length_cons,List.length_nil,
    List.getElem?_cons_zero,Option.getD_some,show (0:Nat)<0+1+1 by omega,ite_true, if_true]
  exact Nat.mod_eq_of_lt I.constraints[e].source.isLt

omit [NeZero q] in
theorem right_encoded (I : Instance q) (e : FullGame.Edge I) :
    right q (gameBits I) e.val=I.constraints[e].target.val := by
  rw [right,field_encoded q I e 1 (by omega),n_encoded]
  simp only [constraintWords,List.getElem?_append,List.length_cons,List.length_nil,
    List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,show (1:Nat)<0+1+1 by omega,ite_true, if_true]
  exact Nat.mod_eq_of_lt I.constraints[e].target.isLt

end DirectedFeedback.GameRead

end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_PacketLocality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.RawFamily
open Construction Games PacketSeeds SourceProbability FiniteDistribution RankGraph
open DFVSGames.Foundations DFVSGames.Foundations.Target DFVSGames.Foundations.Complexity
open DFVSGames.Explicit.MachineOutputContract
variable {D : Nat} (P : Parameters D) (S : BinaryGapReduction P.theta P.theta)
variable (R : RankParameters P (X S.alphabet)) [NeZero R.N]
variable (C : Nat) (c : Seed S.alphabet P.M P.T R.N → Nat) (hC : 0<C)
variable (hc : ∀ s, (C:ℝ)*mass R.law (8*(D+1)) P.K s=c s)

attribute [local instance] OAI.DirectedFeedback.RawFamily.packetLocalityAlphabetNeZero
lemma encoded_model (I : Instance S.alphabet)
    (p : (U : Type) → [Fintype U] → (E : Type) → [Fintype E] →
      Game U U E (X S.alphabet) (Y S.alphabet) → Prop)
    (hp : p _ _ (FullGame.game I)) :
    ∃ (G : Game (W (gameBits I)) (W (gameBits I)) (E (gameBits I)) (X S.alphabet) (Y S.alphabet))
      (f : E (gameBits I) → X S.alphabet ≃ Y S.alphabet × Bool),
      Model P S (gameBits I) G f ∧ p _ _ G := by
  have aux (n m : Nat) [Nonempty (Fin m)] (hn : n=I.vertices)
      (hm : m=I.constraints.length) :
      ∃ (G : Game (Fin n) (Fin n) (Fin m) (X S.alphabet) (Y S.alphabet))
        (f : Fin m → X S.alphabet ≃ Y S.alphabet × Bool),
        ((∀ e, GameRead.left S.alphabet (gameBits I) e.val=(G.left e).val) ∧
        (∀ e, GameRead.right S.alphabet (gameBits I) e.val=(G.right e).val) ∧
        (∀ e, GameRead.fiber S.alphabet (gameBits I) e.val=f e) ∧
        G.edgeLaw=uniform (Fin m) ∧ (∀ e a, (f e a).1=G.project e a)) ∧ p _ _ G := by
    subst n m
    refine ⟨FullGame.game I,FullGame.fiber I,?_,hp⟩
    exact ⟨GameRead.left_encoded S.alphabet I,GameRead.right_encoded S.alphabet I,
      GameRead.fiber_encoded S.alphabet I,rfl,FullGame.fiber_project I⟩
  exact aux _ _ (GameRead.n_encoded _ _) (GameRead.m_encoded _ _)

include hc in
theorem encoded_yes (input : List Bool) (h : DFVSGames.BinaryLanguage.language input) :
    ((family S.alphabet P.M P.T R.N D C c hC).printer.inst (gameBits (S.construct input))).graph.dfvs ≤
    ((family S.alphabet P.M P.T R.N D C c hC).printer.inst (gameBits (S.construct input))).k := by
  obtain ⟨G,f,⟨hl,hr,hf,hE,hproj⟩,a,b,hab⟩ := encoded_model P S (S.construct input)
    (fun _ _ _ _ G => ∃ a b, 1-(P.theta:ℝ)≤G.score a b) (FullGame.completeness S input h)
  exact completeness P R C c hC hc _ G f hl hr hf hE hproj a b hab

include hc in
theorem encoded_no (A : ℝ) (hA : 4*A≤D) (input : List Bool)
    (h : ¬DFVSGames.BinaryLanguage.language input) :
    A*((family S.alphabet P.M P.T R.N D C c hC).printer.inst (gameBits (S.construct input))).k <
    (((family S.alphabet P.M P.T R.N D C c hC).printer.inst (gameBits (S.construct input))).graph.dfvs:ℝ) := by
  obtain ⟨G,f,⟨hl,hr,hf,hE,hproj⟩,hg⟩ := encoded_model P S (S.construct input)
    (fun _ _ _ _ G => G.Sound P.theta) (FullGame.soundness S input h)
  have hh := soundness P R C c hC hc _ G f hl hr hf hE hproj hg
  apply lt_of_le_of_lt _ hh
  change A*((4*scale P.T C (gameBits (S.construct input)):Nat):ℝ)≤_
  push_cast
  nlinarith [mul_le_mul_of_nonneg_right hA (Nat.cast_nonneg (α:=ℝ) (scale P.T C (gameBits (S.construct input))))]

end DirectedFeedback.RawFamily

end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback
open Construction Games PacketSeeds SourceProbability FiniteDistribution RankGraph
open DFVSGames.Foundations DFVSGames.Foundations.Target DFVSGames.Foundations.Complexity
open DFVSGames.Explicit.MachineOutputContract

namespace RawFamily
variable {D : Nat} (P : Parameters D) (S : BinaryGapReduction P.theta P.theta)
variable (R : RankParameters P (X S.alphabet)) [NeZero R.N]
variable (C : Nat) (c : Seed S.alphabet P.M P.T R.N → Nat) (hC : 0<C)
variable (hc : ∀ s, (C:ℝ)*mass R.law (8*(D+1)) P.K s=c s)

variable (A : ℝ) (hA : 4*A≤D) (language : List Bool → Prop) (V : NPVerifier)
variable (hV : ∀ x, language x ↔ V.Accepts x)

attribute [local instance] OAI.DirectedFeedback.RawFamily.reductionAlphabetNeZero
def reduction : GapReduction A language where
  construct x := (family S.alphabet P.M P.T R.N D C c hC).printer.inst
    (gameBits (S.construct (CookLevin.NPTableau.binaryInput V x)))
  computation := MachineSequential.composeBits
    (f := fun x => S.construct (CookLevin.NPTableau.binaryInput V x))
    (g := fun I => (family S.alphabet P.M P.T R.N D C c hC).printer.inst (gameBits I))
    (CookLevin.NPTableau.sourceComputation V S) (gameComputation P S R C c hC)
  finiteAlphabet := MachineFiniteAlphabet.composeBits (CookLevin.NPTableau.sourceComputation V S)
    (gameComputation P S R C c hC) (CookLevin.NPTableau.sourceComputation_finite V S)
    (gameComputation_finite P S R C c hC)
  completeness x hx := encoded_yes P S R C c hC hc _
    ((CookLevin.NPTableau.binaryInput_correct V x).mpr ((hV x).mp hx))
  soundness x hx := encoded_no P S R C c hC hc A hA _ (by
    intro hb
    exact hx ((hV x).mpr ((CookLevin.NPTableau.binaryInput_correct V x).mp hb)))
end RawFamily

end DirectedFeedback

end
end

end OAI
end


