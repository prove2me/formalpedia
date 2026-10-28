-- Prove2me | Definitions.Def_OAIQ076M021
-- name    : OAIQ076M021
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T09:14:49.222348+00:00
-- url     : https://prove2.me/theorems/f4a36ae3-d8a2-4b8c-8356-669675308278
-- title:
--   Definitions bundle OAIQ076M021 of the split of OpenAI, Constant-factor hardness of Min-UnCut (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MinUncut.main`, carved from OpenAI's openai/math development (OpenAI, *Constant-factor hardness of Min-UnCut (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 26 declarations of OpenAI's Lean: 6 definitions, 1 instance and 19 theorems. The definitions and types are `OAI.MinUncut.Preprocess.Syntax.forwardCode`, `OAI.MinUncut.Preprocess.chosenL`, `OAI.MinUncut.Preprocess.chosenM`, `OAI.MinUncut.Preprocess.chosenN`, `OAI.MinUncut.Preprocess.chosenT`, `OAI.MinUncut.Preprocess.selectedParameters`.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: [`MinUncut_Encoding_BitOutputBound`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/MinUncut/Encoding/BitOutputBound.lean), [`MinUncut_Estimates_BlocksEffectivity`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/MinUncut/Estimates/BlocksEffectivity.lean), [`MinUncut_Estimates_Bridge`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/MinUncut/Estimates/Bridge.lean), [`MinUncut_Estimates_UniformTransport`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/MinUncut/Estimates/UniformTransport.lean), [`MinUncut_Graphs_CompleteGraphProgram`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/MinUncut/Graphs/CompleteGraphProgram.lean), [`MinUncut_Search_ArithmeticTactic`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/MinUncut/Search/ArithmeticTactic.lean), [`MinUncut_Search_UniformFind`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/MinUncut/Search/UniformFind.lean).
--
--   **Imports.** It imports the published bundle `Def_MinUncut`; the bundles `OAIQ076M006`, `OAIQ076M007`, `OAIQ076M012` and `OAIQ076M013` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ076M027`.
-- source:
--   OpenAI, Constant-factor hardness of Min-UnCut (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Constant-factor-hardness-of-Min-UnCut-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Definitions.Def_MinUncut
import Definitions.Def_OAIQ076M006
import Definitions.Def_OAIQ076M007
import Definitions.Def_OAIQ076M012
import Definitions.Def_OAIQ076M013

section
-- module Solutions.OAIQ076_MU.MinUncut_Encoding_BitOutputBound
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncut
open _root_.Turing MinUncutGames.Foundations.Complexity
lemma graph_size_of_runtime (M : FinTM2) (G : Output)
    (input : List (M.Γ M.k₀)) (out : List (M.Γ M.k₁)) (B : ℕ)
    (hlen : out.length=G.bits.length)
    (hr : TM2OutputsInTime M input (some out) B) :
    G.vertices+G.bits.length≤2*(input.length+B*Runtime.programPushBound M) := by
  have hb:=Runtime.outputLength_le M input out B hr
  rw [hlen] at hb
  calc
    _ ≤ G.bits.length+G.bits.length := Nat.add_le_add_right G.vertices_le_bits _
    _ = 2*G.bits.length := (two_mul _).symm
    _ ≤ _ := Nat.mul_le_mul_left 2 hb
end MinUncut

end

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

lemma p_stepCode : Primrec stepCode :=
  primrec_cons.comp (Primrec.const _)
    (primrec_cons.comp
      ((p_bin _).comp (Primrec.const _) (p_constCode.comp Primrec.list_length)) p_prefCode)
lemma prefCode_eq (es : List AExpr) : prefCode (es.map (fun e=>e.program.code)) =
    (Blocks.stepProgram.go es).code := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [prefCode,List.map_cons,List.foldr_cons] at *; rw [ih]; rfl
lemma stepCode_eq (es : List AExpr) : stepCode (es.map (fun e=>e.program.code))=(Blocks.stepProgram es).code := by
  simp only [stepCode,List.length_map,prefCode_eq]
  rfl
def forwardCode (cs : List Code) (N : Code) : Code :=
  .comp reversePrefixProgram.code (.comp PolyProgram.tail.code
    (.comp (iterCode (stepCode cs.reverse))
      (.cons N (.cons (constCode 0) (.cons (constCode 0) Code.id)))))
lemma p_forwardCode : Primrec₂ forwardCode := by
  exact primrec_comp.comp (Primrec.const _)
    (primrec_comp.comp (Primrec.const _)
      (primrec_comp.comp (p_iterCode.comp (p_stepCode.comp (Primrec.list_reverse.comp Primrec.fst)))
        (primrec_cons.comp Primrec.snd (Primrec.const _))))
lemma forwardCode_eq (es : List AExpr) (N : AExpr) :
    forwardCode (es.map (fun e=>e.program.code)) N.program.code=(Blocks.forward es N).code := by
  unfold forwardCode
  rw [←List.map_reverse,stepCode_eq]
  rfl
end MinUncut.Preprocess.Syntax

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_Bridge
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace MinUncut.SourceBridge
open MinUncut.Inner MinUncut.Outer
open MinUncutGames.Reduction
attribute [local instance] Classical.propDecidable

instance entriesNonempty (input : SourceEncoding.Input) : Nonempty (Fin input.equations.length) :=
  Fin.pos_iff_nonempty.mp (List.length_pos_iff.mpr input.nonempty)

end MinUncut.SourceBridge

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_UniformTransport
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncut.Preprocess
open MinUncutGames.Foundations.Hastad.SourceOccurrences

namespace UEncoding
variable {P : Type} [Primcodable P] {A B C Γ : P → Type}
variable {p : P}
lemma map_case {g : UEncoding P Γ} {a : UEncoding P A} {b : UEncoding P B}
    {c : UEncoding P C} {f : ∀p,Γ p × A p → C p} {h : ∀p,Γ p × B p → C p}
    (hf : (g.prod a).Map c f) (hh : (g.prod b).Map c h) :
    (g.prod (a.sum b)).Map c (fun p x=>Sum.elim (fun y=>f p (x.1,y)) (fun y=>h p (x.1,y)) x.2) := by
  obtain ⟨f',hf',hf⟩:=hf
  obtain ⟨h',hh',hh⟩:=hh
  let leftSize : P × ℕ → ℕ := fun q=>(a.enc q.1).size
  let rightSize : P × ℕ → ℕ := fun q=>(b.enc q.1).size
  let tag : P × ℕ → ℕ := fun q=>q.2 % (leftSize q+rightSize q)
  let ctxt : P × ℕ → ℕ := fun q=>q.2 / (leftSize q+rightSize q)
  have hl : Computable leftSize := a.computableSize.comp Computable.fst
  have hr : Computable rightSize := b.computableSize.comp Computable.fst
  have ht : Computable tag := ca_mod Computable.snd (ca_add hl hr)
  have hc : Computable ctxt := ca_div Computable.snd (ca_add hl hr)
  let raw : P × ℕ → ℕ := fun q=>if tag q<leftSize q then f' (q.1,ctxt q*leftSize q+tag q)
    else h' (q.1,ctxt q*rightSize q+(tag q-leftSize q))
  have hraw : Computable raw :=
    (Computable.cond (ca_natLt ht hl).decide (hf'.comp (Computable.fst.pair (ca_add (ca_mul hc hl) ht)))
      (hh'.comp (Computable.fst.pair (ca_add (ca_mul hc hr) (ca_sub ht hl))))).of_eq (by intro q; simp only [raw,Bool.cond_eq_ite,decide_eq_true_eq])
  refine ⟨raw,hraw,?_⟩
  intro p ⟨s,z⟩
  have hz : (((a.enc p).sum (b.enc p)).code z).val<(a.enc p).size+(b.enc p).size :=
    (((a.enc p).sum (b.enc p)).code z).isLt
  have hs : 0<(a.enc p).size+(b.enc p).size := by exact Nat.zero_lt_of_lt hz
  have hc' : ctxt (p,(((g.enc p).prod ((a.enc p).sum (b.enc p))).code (s,z)).val)=((g.enc p).code s).val := by
    simp only [ctxt,leftSize,rightSize]
    change ((((a.enc p).sum (b.enc p)).code z).val+((a.enc p).size+(b.enc p).size)*((g.enc p).code s).val)/
      ((a.enc p).size+(b.enc p).size)=_
    rw [Nat.add_mul_div_left _ _ hs,Nat.div_eq_of_lt hz,Nat.zero_add]
  have ht' : tag (p,(((g.enc p).prod ((a.enc p).sum (b.enc p))).code (s,z)).val)=(((a.enc p).sum (b.enc p)).code z).val := by
    simp only [tag,leftSize,rightSize]
    change ((((a.enc p).sum (b.enc p)).code z).val+((a.enc p).size+(b.enc p).size)*((g.enc p).code s).val)%
      ((a.enc p).size+(b.enc p).size)=_
    rw [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hz]
  change raw (p,(((g.enc p).prod ((a.enc p).sum (b.enc p))).code (s,z)).val)=_
  dsimp only [raw]
  rw [hc',ht']
  cases z with
  | inl x =>
    have he:=hf p (s,x)
    change f' (p,(((g.enc p).prod (a.enc p)).code (s,x)).val)=_ at he
    rw [prod_code] at he
    simpa only [show (((a.enc p).sum (b.enc p)).code (.inl x)).val=((a.enc p).code x).val from rfl,
      leftSize,rightSize,((a.enc p).code x).isLt,ite_true,Sum.elim_inl] using he
  | inr x =>
    have he:=hh p (s,x)
    change h' (p,(((g.enc p).prod (b.enc p)).code (s,x)).val)=_ at he
    rw [prod_code] at he
    simpa only [show (((a.enc p).sum (b.enc p)).code (.inr x)).val=(a.enc p).size+((b.enc p).code x).val from rfl,
      leftSize,rightSize,Nat.add_sub_cancel_left,Nat.not_lt.mpr (Nat.le_add_right _ _),ite_false,Sum.elim_inr] using he
end UEncoding
end MinUncut.Preprocess

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Search_UniformFind
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncut.Preprocess
open MinUncutGames.Foundations.Hastad.SourceOccurrences
namespace UEncoding
variable {P : Type} [Primcodable P] {A B Γ : P → Type}

lemma map_option_elim {g : UEncoding P Γ} {a : UEncoding P A} {b : UEncoding P B}
    {f : ∀p,Γ p → B p} {h : ∀p,Γ p × A p → B p}
    (hf : g.Map b f) (hh : (g.prod a).Map b h) :
    (g.prod a.option).Map b (fun p x=>x.2.elim (f p x.1) (fun y=>h p (x.1,y))) := by
  have hc:=map_case hh (hf.first (c:=fixed Encoding.unit))
  have ht : (g.prod a.option).Map (g.prod (a.sum (fixed Encoding.unit)))
      (fun p x=>(x.1,optionEquiv (A p) x.2)) :=
    map_pair (map_fst g a.option)
      (map_comp (map_snd g a.option) (map_to (a.sum (fixed Encoding.unit)) (fun p=>optionEquiv (A p))))
  obtain ⟨raw, hraw, hraw_spec⟩ := map_comp ht hc
  refine ⟨raw, hraw, ?_⟩
  rintro parameter ⟨context, value⟩
  cases value <;> exact hraw_spec parameter _

end UEncoding
end MinUncut.Preprocess

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Search_ArithmeticTactic
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

set_option maxHeartbeats 1000000
section
namespace MinUncut.Preprocess
open MinUncut.Inner MinUncut.Outer MinUncut.FiniteGaussian
attribute [fun_prop] c_listBound c_radicand
lemma c_qError : Computable (fun p : ℕ × ℚ=>qError p.1 p.2) := by unfold qError; iterate 12 (all_goals first | with_reducible exact MinUncut.Preprocess.ca_const _ | with_reducible apply MinUncut.Preprocess.ca_ratAdd | with_reducible apply MinUncut.Preprocess.ca_ratMul | with_reducible apply MinUncut.Preprocess.ca_ratSub | with_reducible apply MinUncut.Preprocess.ca_ratDiv | with_reducible apply MinUncut.Preprocess.ca_ratPow | with_reducible apply MinUncut.Preprocess.ca_ratInv | with_reducible apply MinUncut.Preprocess.ca_ratCast | with_reducible apply MinUncut.Preprocess.ca_ratCeil | with_reducible apply MinUncut.Preprocess.ca_ratLe | with_reducible apply MinUncut.Preprocess.ca_ratLt | with_reducible apply MinUncut.Preprocess.ca_add | with_reducible apply MinUncut.Preprocess.ca_mul | with_reducible apply MinUncut.Preprocess.ca_sub | with_reducible apply MinUncut.Preprocess.ca_div | with_reducible apply MinUncut.Preprocess.ca_mod | with_reducible apply MinUncut.Preprocess.ca_pow | with_reducible apply MinUncut.Preprocess.ca_choose | with_reducible apply MinUncut.Preprocess.ca_factorial | with_reducible apply MinUncut.Preprocess.ca_and | with_reducible apply MinUncut.Preprocess.ca_natLe | with_reducible apply MinUncut.Preprocess.ca_natLt | with_reducible fun_prop | fun_prop)
attribute [fun_prop] c_qError
end MinUncut.Preprocess

end
section
namespace MinUncut.Preprocess
open MinUncut.FiniteGaussian

lemma c_gridExtract₁ : Computable (fun n=>gridField (gridTail n)) :=
  c_gridField.comp c_gridTail
lemma c_gridExtract₂ : Computable (fun n=>gridField (gridTail (gridTail n))) :=
  c_gridExtract₁.comp c_gridTail
lemma c_gridExtract₃ : Computable (fun n=>gridField (gridTail (gridTail (gridTail n)))) :=
  c_gridExtract₂.comp c_gridTail
lemma c_gridExtractPair : Computable (fun n=>(gridField (gridTail n),
    gridField (gridTail (gridTail n)),gridField (gridTail (gridTail (gridTail n))))) :=
  c_gridExtract₁.pair (c_gridExtract₂.pair c_gridExtract₃)
end MinUncut.Preprocess

end
section
namespace MinUncut.Preprocess
open MinUncut.Inner MinUncut.Outer MinUncut.FiniteGaussian

attribute [local irreducible] selectedInner

lemma selectedOuter_check (K : ℕ) : (selectedOuter K).Check (parameterJ K) (selectedInner K) :=
  search_spec outer_exists K
noncomputable def selectedParameters (K : ℕ) : Parameters (parameterJ K) :=
  ⟨parameterJ_pos K,selectedInner K,selectedInner_check K,selectedOuter K,selectedOuter_check K⟩

end MinUncut.Preprocess

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Graphs_CompleteGraphProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MinUncut.Preprocess
open MinUncut.Inner MinUncut.Outer MinUncut.FiniteGaussian UEncoding
open MinUncutGames.Foundations.Hastad.SourceOccurrences MinUncut.OuterSmoothness.Density
attribute [local irreducible] selectedInner selectedOuter
open MinUncut.Costed MinUncut.Costed.SourceWords MinUncut.SourceTemplate MinUncut.OuterSmoothness
abbrev chosenM (K : ℕ) := (selectedInner K).m
abbrev chosenN (K : ℕ) := (selectedInner K).n
abbrev chosenT (K : ℕ) := (selectedOuter K).t
abbrev chosenL (K : ℕ) := (selectedOuter K).k
lemma c_chosenM : Computable chosenM := c_innerData_m.comp c_selectedInner
lemma c_chosenN : Computable chosenN := c_innerData_n.comp c_selectedInner
lemma c_chosenT : Computable chosenT := c_outerData_t.comp c_selectedOuter
lemma c_chosenL : Computable chosenL := c_outerData_k.comp c_selectedOuter
lemma chosenN_pos (K : ℕ) : 0 < chosenN K := by
  have h := (selectedInner_check K).2.1
  change (selectedInner K).k+2 ≤ chosenN K at h
  omega
end MinUncut.Preprocess

end

end OAI
end


