-- Prove2me | Definitions.Def_OAIQ076M013
-- name    : OAIQ076M013
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T09:05:55.043413+00:00
-- url     : https://prove2.me/theorems/8a49cec8-3855-432d-ad0b-7527f3e9e653
-- title:
--   Definitions bundle OAIQ076M013 of the split of OpenAI, Constant-factor hardness of Min-UnCut (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MinUncut.main`, carved from OpenAI's openai/math development (OpenAI, *Constant-factor hardness of Min-UnCut (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 16 declarations of OpenAI's Lean: 4 definitions, 7 instances and 5 theorems. The definitions and types are `OAI.MinUncut.Preprocess.Syntax.prefCode`, `OAI.MinUncut.Preprocess.Syntax.stepCode`, `OAI.MinUncut.Preprocess.oldGridDecode`, `OAI.MinUncut.Preprocess.oldGridEncode`.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: [`MinUncut_Encoding_DerivedResolver`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/MinUncut/Encoding/DerivedResolver.lean), [`MinUncut_Estimates_BlocksEffectivity`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/MinUncut/Estimates/BlocksEffectivity.lean), [`MinUncut_Machines_PoweringMachineField`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/MinUncut/Machines/PoweringMachineField.lean), [`MinUncut_Machines_PoweringMachineRotor`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/MinUncut/Machines/PoweringMachineRotor.lean), [`MinUncut_PCP_ExpanderFamily`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/MinUncut/PCP/ExpanderFamily.lean), [`MinUncut_PCP_PoweringOpinionTables`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/MinUncut/PCP/PoweringOpinionTables.lean), [`MinUncut_PCP_PreprocessingTableSpectral`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/MinUncut/PCP/PreprocessingTableSpectral.lean), [`MinUncut_Search_UniformFiniteSum`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/MinUncut/Search/UniformFiniteSum.lean).
--
--   **Imports.** It imports the bundles `OAIQ076M000`, `OAIQ076M001`, `OAIQ076M002`, `OAIQ076M003` and `OAIQ076M005` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ076M021`.
-- source:
--   OpenAI, Constant-factor hardness of Min-UnCut (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Constant-factor-hardness-of-Min-UnCut-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ076M000
import Definitions.Def_OAIQ076M001
import Definitions.Def_OAIQ076M002
import Definitions.Def_OAIQ076M003
import Definitions.Def_OAIQ076M005

section
-- module Solutions.OAIQ076_MU.MinUncut_Encoding_DerivedResolver
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncut.Preprocess
open MinUncut.FiniteGaussian

abbrev oldGridEncode (g : GridData) : ℕ := @Encodable.encode GridData instEncodableGridData g
abbrev oldGridDecode (n : ℕ) : Option GridData := @Encodable.decode GridData instEncodableGridData n

lemma oldGridEncode_eq (g : GridData) : oldGridEncode g=Nat.pair (Nat.pair 0 0+1)
  (Nat.pair (Nat.pair 0 g.T+1) (Nat.pair (Nat.pair 0 g.L+1) (Nat.pair (Nat.pair 0 g.r+1) (Nat.pair 0 0)))) := rfl

lemma oldGridDecode_canonical (n : ℕ) (g : GridData) (h : oldGridDecode n=some g) :
    oldGridEncode g=n := by
  apply encode_ofLeftInjection_canonical (h := h)
  intro tree result htree
  cases tree with
  | nat _ => cases htree
  | cons tag fields =>
    cases tag with
    | cons _ _ => cases htree
    | nat tag =>
      cases tag with
      | succ _ => cases htree
      | zero =>
        cases fields with
        | nat _ => cases htree
        | cons t fields =>
          cases t with
          | cons _ _ => cases htree
          | nat t =>
            cases fields with
            | nat _ => cases htree
            | cons l fields =>
              cases l with
              | cons _ _ => cases htree
              | nat l =>
                cases fields with
                | nat _ => cases htree
                | cons r fields =>
                  cases r with
                  | cons _ _ => cases htree
                  | nat r =>
                    cases fields with
                    | cons _ _ => cases htree
                    | nat last =>
                      cases last with
                      | succ _ => cases htree
                      | zero =>
                        cases htree
                        rfl

end MinUncut.Preprocess

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_BlocksEffectivity
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace MinUncut.Preprocess.Syntax
open MinUncut.Costed MinUncut.CodeEffective Turing.ToPartrec

def prefCode (cs : List Code) : Code :=
  cs.foldr (fun c b=>.cons (.comp c Blocks.extractor.code) b) (PolyProgram.drop 2).code
lemma p_prefCode : Primrec prefCode :=
  Primrec.list_foldr Primrec.id (Primrec.const _)
    (primrec_cons.comp
      (primrec_comp.comp (Primrec.fst.comp Primrec.snd) (Primrec.const _))
      (Primrec.snd.comp Primrec.snd)).to₂

def stepCode (cs : List Code) : Code :=
  .cons PolyProgram.succ.code
    (.cons (bin PolyProgram.add.code (PolyProgram.projection 1).code (constCode cs.length)) (prefCode cs))
lemma p_iterCode : Primrec iterCode := by
  exact primrec_fix.comp (primrec_case.comp (Primrec.const _)
    (primrec_cons.comp (Primrec.const _)
      (primrec_cons.comp (Primrec.const _) (primrec_comp.comp Primrec.id (Primrec.const _)))))
end MinUncut.Preprocess.Syntax

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_ExpanderFamily
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.PCP.ExpanderFamily

open PoweringWalks SpectralReturn Expanders

instance vertexFintype (n : Nat) : Fintype (Vertex n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ n ih =>
    letI : Fintype (Vertex n) := ih
    change Fintype (Vertex n × CloudPort)
    infer_instance

instance basePortNonempty : Nonempty BasePort :=
  ⟨fun _ => ⟨0, by norm_num [initialQuarterDegree]⟩⟩

instance vertexNonempty (n : Nat) : Nonempty (Vertex n) := by
  induction n with
  | zero => exact inferInstanceAs (Nonempty Unit)
  | succ n ih =>
    let : Nonempty (Vertex n) := ih
    change Nonempty (Vertex n × CloudPort)
    infer_instance

end MinUncutGames.Foundations.PCP.ExpanderFamily

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_PreprocessingTableSpectral
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.PoweringLabels

open PoweringWalks
open scoped BigOperators

variable {V D A : Type*}

instance finitePortWords [Finite D] (t : Nat) : Finite (PortWords D t) := by
  let := Fintype.ofFinite D
  exact Finite.of_fintype _

end MinUncutGames.Foundations.PCP.PoweringLabels

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_PoweringOpinionTables
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.GenericGraphTables

open MinUncutGames.Foundations.Complexity

variable {q : Nat}

instance instDecidableValid {n m : Nat} (rows : Rows q n m) : Decidable (Valid rows) := by
  unfold Valid
  infer_instance

end MinUncutGames.Foundations.PCP.GenericGraphTables

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_PoweringMachineRotor
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.PoweringMachineWord

open _root_.Turing
open MachineComposition
open PCP

variable {K Λ σ : Type} [DecidableEq K]
variable {n d : Nat}

instance labelDecidableEq (t : Nat) : DecidableEq (Label t) := by
  induction t with
  | zero => exact inferInstanceAs (DecidableEq MachineUnaryAffineAt.Label)
  | succ t ih =>
      letI := ih
      exact inferInstanceAs (DecidableEq (PoweringMachineRotor.Label ⊕ Label t))

end MinUncutGames.Foundations.Complexity.PoweringMachineWord

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_PoweringMachineField
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.PoweringMachineField

open _root_.Turing MachineComposition PCP PoweringFieldPlan

variable {K Λ A : Type} [DecidableEq K] {n d max : Nat}

instance labelDecidableEq (op : Instruction d) : DecidableEq (Label op) := by
  cases op <;> dsimp only [Label] <;> infer_instance

end MinUncutGames.Foundations.Complexity.PoweringMachineField

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Search_UniformFiniteSum
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncut.Preprocess

variable {α β : Type} [Primcodable α] [Primcodable β]

lemma computable_searchWith (e : Encodable β) {p : α → β → Prop} [DecidableRel p]
    (hd : Computable (@Encodable.decode β e))
    (hp : ComputablePred (fun q : α × β=>p q.1 q.2))
    (h : ∀a,∃b,p a b) (d : β) : Computable (searchWith e h) := by
  have hn : ∀a,∃n,decodeGood (@Encodable.decode β e) p a n := by
    intro a
    obtain ⟨b,hb⟩:=h a
    refine ⟨@Encodable.encode β e b,?_⟩
    simp only [decodeGood,Encodable.encodek,Option.elim_some,hb]
  have hc : Computable (fun a=>Nat.find (hn a)) :=
    Computable.find (computable_decodeGood hd hp) hn
  exact (Computable.option_getD (hd.comp hc) (ca_const d)).of_eq (by
    intro a
    convert (@choose_getD β e (p a) _ (h a) d).symm using 3
    all_goals try with_reducible_and_instances rfl
    all_goals congr 1)
end MinUncut.Preprocess

end

end OAI
end


