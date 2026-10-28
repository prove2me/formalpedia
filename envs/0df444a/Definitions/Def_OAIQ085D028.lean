-- Prove2me | Definitions.Def_OAIQ085D028
-- name    : OAIQ085D028
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T16:31:30.976676+00:00
-- url     : https://prove2.me/theorems/bc5876d8-6f95-4be7-8ea5-fd4c72c127c2
-- title:
--   Definitions bundle OAIQ085D028 of the split of OpenAI, Constant-factor hardness of directed feedback vertex set (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DirectedFeedback.main`, carved from OpenAI's openai/math development (OpenAI, *Constant-factor hardness of directed feedback vertex set (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 19 declarations of OpenAI's Lean: 3 definitions and 16 theorems. The definitions and types are `OAI.DirectedFeedback.RawFamily.embed`, `OAI.DirectedFeedback.RawFamily.family`, `OAI.DirectedFeedback.RawFamily.gameComputation`.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: [`DirectedFeedback_Main`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DirectedFeedback/Main.lean), [`DirectedFeedback_RankGraph_PacketLocality`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DirectedFeedback/RankGraph/PacketLocality.lean).
--
--   **Imports.** It imports the published bundle `Def_DirectedFeedback`; the bundle `OAIQ085D023` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ085D030`.
-- source:
--   OpenAI, Constant-factor hardness of directed feedback vertex set (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Constant-factor-hardness-of-directed-feedback-vertex-set-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Definitions.Def_DirectedFeedback
import Definitions.Def_OAIQ085D023

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_PacketLocality
attribute [-instance] _root_.OAI.DirectedFeedback.CookLevin.NPTableau.codec_width_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.RawFamily
open BoundedExpr Construction PacketSeeds Games RankGraph
variable (q M T N : Nat) [NeZero q] [NeZero M] [NeZero T] [NeZero N]
variable (D C : Nat) (c : Seed q M T N → Nat)
omit [NeZero q] [NeZero M] [NeZero T] [NeZero N] in
theorem copy_def : Def (r:=1) (fun x a => copy q M T N D C c x (a 0)) :=
  BoxCodec.copy_def (base_def 1) (copies_def q M T N D C c 1) (Def.arg 0) (T+1)
omit [NeZero q] [NeZero M] [NeZero T] in
theorem u_def (j : Fin (T+1)) : Def (r:=1) (fun x a => u q M T N D C c x (a 0) j) :=
  (isRank_def q M T N D C c).nite (digit_def q M T N D C c j)
    (GameRead.left_def q (digit_def q M T N D C c j))
omit [NeZero q] [NeZero M] [NeZero T] in
theorem v_def (j : Fin (T+1)) : Def (r:=1) (fun x a => v q M T N D C c x (a 0) j) :=
  (isRank_def q M T N D C c).nite (digit_def q M T N D C c j)
    (GameRead.right_def q (digit_def q M T N D C c j))
omit [NeZero q] [NeZero M] [NeZero T] in
theorem valid_def : PDef (r:=1) (fun x a => valid q M T N D C c x (a 0)) := by
  let f : Tag q M T N → Nat := Sum.elim (fun _ => 0) c
  have ht := tag_def q M T N D C c
  have hd := digit_def q M T N D C c
  have hj := copy_def q M T N D C c
  have hi := isRank_def q M T N D C c
  have h := (hi.and ((PDef.all (fun j => PDef.lt (hd j) (GameRead.n_def 1))).and
      (PDef.lt hj (r_def T D C 1)))).or
    (hi.not.and ((PDef.all (fun j => PDef.lt (hd j) (GameRead.m_def 1))).and
      (PDef.lt hj (ht.toDef f))))
  apply h.congr
  intro x a
  unfold valid SumBox.valid
  simp only [tag,digit,copy]
  cases SumBox.tag (Shape q T N) (Seed q M T N) (GameRead.n x) (GameRead.m x) (T+1) (r T D C x) c (a 0) <;> simp [isRank,f]

def family (hC : 0<C) : LocalPrinter.Family (Fin (T+1)) (Fin (T+1)) (X q) (Y q) (2*N+1) where
  n := size q M T N D C c
  k := fun x => 4*scale T C x
  valid := valid q M T N D C c
  u := u q M T N D C c
  v := v q M T N D C c
  rule := rule q M T N D C c
  n_def := size_def q M T N D C c
  k_def := (Def.lit 4).mul (scale_def T C 0)
  valid_def := valid_def q M T N D C c
  u_def := u_def q M T N D C c
  v_def := v_def q M T N D C c
  rule_def := rule_def q M T N D C c
  k_pos x := by unfold scale; have := GameRead.m_pos x; positivity

end DirectedFeedback.RawFamily

end
end

section

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.RawFamily
open Construction Games PacketSeeds SourceProbability FiniteDistribution RankGraph
variable {q M T N : Nat} [NeZero q] [NeZero M] [NeZero T] [NeZero N]
variable (D C : Nat) (c : Seed q M T N → Nat) (hC : 0<C) (x : List Bool)

def embed (z : Live D C c x) : Fin ((family q M T N D C c hC).n x) :=
  SumBox.embed (Shape q T N) (Seed q M T N) (GameRead.n x) (GameRead.m x) (T+1) (r T D C x) c z

omit [NeZero M] [NeZero T] in
theorem embed_injective : Function.Injective (embed D C c hC x) := SumBox.embed_injective _ _ _ _ _ _ _
omit [NeZero M] [NeZero T] in
theorem valid_embed (z : Live D C c x) : (family q M T N D C c hC).valid x (embed D C c hC x z).val :=
  SumBox.valid_embed _ _ _ _ _ _ _ z
omit [NeZero M] [NeZero T] in
theorem valid_surjective (i : Fin ((family q M T N D C c hC).n x))
    (hi : (family q M T N D C c hC).valid x i.val) : ∃z, embed D C c hC x z=i :=
  SumBox.valid_surjective _ _ _ _ _ _ _ i hi

omit [NeZero M] [NeZero T] in
theorem tag_embed (z : Live D C c x) :
    tag q M T N D C c x (embed D C c hC x z).val=
    (match z with | .inl a => .inl a.1.1 | .inr a => .inr a.1) := by
  have h := SumBox.tag_embed (Shape q T N) (Seed q M T N) (GameRead.n x) (GameRead.m x) (T+1) (r T D C x) c z
  rcases z with a | a <;> exact h

omit [NeZero M] [NeZero T] in
theorem digit_embed (z : Live D C c x) (j : Fin (T+1)) :
    digit q M T N D C c x (embed D C c hC x z).val j=
    (match z with | .inl a => (a.1.2 j).val | .inr a => (a.2.1 j).val) := by
  have h := SumBox.digits_embed (Shape q T N) (Seed q M T N) (GameRead.n x) (GameRead.m x) (T+1) (r T D C x) c z j
  rcases z with a | a <;> exact h

variable (G : Game (W x) (W x) (E x) (X q) (Y q))
variable (fiber : E x → X q ≃ Y q × Bool)
variable (hl : ∀e : E x, GameRead.left q x e.val=(G.left e).val)
variable (hr : ∀e : E x, GameRead.right q x e.val=(G.right e).val)
variable (hf : ∀e : E x, GameRead.fiber q x e.val=fiber e)
include hl hr hf

omit [NeZero M] [NeZero T] in
theorem value_embed (z : Live D C c x) (a : Nat → X q) (b : Nat → Y q) :
    (family q M T N D C c hC).value x (embed D C c hC x z).val a b=
    AllLabels.code G (hYX q) fiber (a ∘ Fin.val) (b ∘ Fin.val)
      (LivePackets.project G (r T D C x) c z) := by
  change rule q M T N D C c x (embed D C c hC x z).val
    (a ∘ u q M T N D C c x (embed D C c hC x z).val)
    (b ∘ v q M T N D C c x (embed D C c hC x z).val)=_
  unfold rule u v
  simp_rw [tag_embed D C c hC x z,digit_embed D C c hC x z]
  rcases z with ⟨⟨s,e⟩,j⟩ | ⟨s,e,j⟩
  · dsimp +instances only [isRank,tagRule,LivePackets.project]
    unfold AllLabels.code
    simp +instances only [AllLabels.deleted,TestGraph.LabelDeleted]
    congr 2
    apply Fin.ext
    change 2*(eval _ _ (RankPackets.fill s id)).val=2*(eval _ _ (RankPackets.fill s e)).val
    rw [RankPackets.eval_fill s e (a ∘ Fin.val) (b ∘ Fin.val)]
    simp +instances only [ite_true, if_true]
    rfl
  · simp only [isRank,tagRule,LivePackets.project]
    simp_rw [hl,hr,hf]
    exact (PacketLocality.code_fill G (hYX q) fiber s e (a ∘ Fin.val) (b ∘ Fin.val)).symm

omit [NeZero M] [NeZero T] in
theorem cover_arc (a b : Live D C c x)
    (h : AllArc G (hYX q) fiber (LivePackets.project G (r T D C x) c a)
      (LivePackets.project G (r T D C x) c b)) :
    (family q M T N D C c hC).Arc x (embed D C c hC x a).val (embed D C c hC x b).val := by
  rw [LocalPrinter.Family.arc_global]
  refine ⟨?_,valid_embed D C c hC x a,valid_embed D C c hC x b,?_⟩
  · intro he
    have hab := embed_injective D C c hC x (Fin.ext he)
    subst b
    exact TestGraph.arc_irrefl _ _ _ h
  · intro l k
    rw [value_embed D C c hC x G fiber hl hr hf,value_embed D C c hC x G fiber hl hr hf]
    exact AllLabels.ordered_arc G (hYX q) fiber _ _ h

omit [NeZero M] [NeZero T] in
theorem deleted_eq_image (a : Nat → X q) (b : Nat → Y q) :
    (family q M T N D C c hC).deleted x a b =
    (liveDeleted D C c x G fiber (a ∘ Fin.val) (b ∘ Fin.val)).image (embed D C c hC x) := by
  ext i
  constructor
  · intro hi
    obtain ⟨hv,hd⟩ := (Finset.mem_filter.mp hi).2
    obtain ⟨z,rfl⟩ := valid_surjective D C c hC x i hv
    refine Finset.mem_image.mpr ⟨z,?_,rfl⟩
    rw [value_embed D C c hC x G fiber hl hr hf] at hd
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(AllLabels.code_none _ _ _ _ _ _).mp hd⟩
  · intro hi
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,valid_embed D C c hC x z,?_⟩
    rw [value_embed D C c hC x G fiber hl hr hf]
    exact (AllLabels.code_none _ _ _ _ _ _).mpr (Finset.mem_filter.mp hz).2

end DirectedFeedback.RawFamily

end
end

section

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.RawFamily
open Construction Games PacketSeeds SourceProbability FiniteDistribution RankGraph
variable {q D : Nat} [NeZero q] (P : Parameters D) (R : RankParameters P (X q)) [NeZero R.N]
variable (C : Nat) (c : Seed q P.M P.T R.N → Nat) (hC : 0<C)
variable (hc : ∀s, (C:ℝ)*mass R.law (8*(D+1)) P.K s=c s)
variable (x : List Bool)
variable (G : Game (W x) (W x) (E x) (X q) (Y q))
variable (fiber : E x → X q ≃ Y q × Bool)
variable (hl : ∀e : E x, GameRead.left q x e.val=(G.left e).val)
variable (hr : ∀e : E x, GameRead.right q x e.val=(G.right e).val)
variable (hf : ∀e : E x, GameRead.fiber q x e.val=fiber e)
variable (hE : G.edgeLaw=uniform (E x))
variable (hproj : ∀e a, (fiber e a).1=G.project e a)

theorem feedback_printer_iff (F : Finset (Fin ((family q P.M P.T R.N D C c hC).n x))) :
    ((family q P.M P.T R.N D C c hC).printer.graph x).Feedback F ↔
    FeedbackR (fun i j => (family q P.M P.T R.N D C c hC).Arc x i.val j.val) F := by
  let Pn := (family q P.M P.T R.N D C c hC).printer
  constructor
  · intro h n f hi ha
    apply h n f
    exact ⟨hi,fun i => (Pn.mem_pairs x _ _).mpr (ha i)⟩
  · intro h n f hh
    exact h n f hh.1 (fun i => (Pn.mem_pairs x _ _).mp (hh.2 i))

include hc hl hr hf hE hproj in
theorem completeness (a : W x → X q) (b : W x → Y q)
    (hscore : 1-(P.theta:ℝ)≤G.score a b) :
    ((family q P.M P.T R.N D C c hC).printer.graph x).dfvs ≤ 4*scale P.T C x := by
  let F := family q P.M P.T R.N D C c hC
  have hfb := F.deleted_feedback x (extend a) (extend b)
  have he := deleted_eq_image D C c hC x G fiber hl hr hf (extend a) (extend b)
  simp only [extend_restrict] at he
  have hcard := Finset.card_image_le (s:=liveDeleted D C c x G fiber a b) (f:=embed D C c hC x)
  have hb := live_card_bound P R C c hc x G fiber hE hproj a b hscore
  apply (Digraph.dfvs_le_iff _ _).mpr
  refine ⟨F.deleted x (extend a) (extend b),?_,?_⟩
  · exact (feedback_printer_iff P R C c hC x _).mpr hfb
  · change (F.deleted x (extend a) (extend b)).card≤_
    rw [he]
    have hnat : (liveDeleted D C c x G fiber a b).card≤4*scale P.T C x := by exact_mod_cast hb
    exact hcard.trans hnat

include hc hl hr hf hE hproj in
theorem soundness (hsound : G.Sound P.theta) :
    (D*scale P.T C x:Nat) < (((family q P.M P.T R.N D C c hC).printer.graph x).dfvs:ℝ) := by
  let F := family q P.M P.T R.N D C c hC
  obtain ⟨Q,hQ,hcard⟩ := Digraph.dfvs_attained (F.printer.graph x)
  have hfib := LivePackets.fiber_weight G R.law (r P.T D C x) c hE D (8*(D+1)) P.K C hc
    (by simp only [r,scale,E,Fintype.card_fin]; exact le_rfl)
  have hgap := all_soundness G P R (hYX q) fiber hproj hsound
  have hcast : ((8*(D+1):Nat):ℝ)=8*((D:ℝ)+1) := by push_cast; rfl
  rw [hcast] at hfib
  have hs : 0 < scale P.T C x := by unfold scale; have hm := GameRead.m_pos x; positivity
  have hh := FiniteLift.feedback_cost (embed D C c hC x) (embed_injective D C c hC x)
    (LivePackets.project G (r P.T D C x) c) (AllArc G (hYX q) fiber)
    (fun i j => F.Arc x i.val j.val)
    (cover_arc D C c hC x G fiber hl hr hf)
    (allCost G R.law D (8*((D:ℝ)+1)) P.K) (scale P.T C x) D
    (by simpa only [scale,E,Fintype.card_fin] using hfib)
    hgap hs Q ((feedback_printer_iff P R C c hC x Q).mp hQ)
  have hh' := lt_of_lt_of_eq hh (congrArg (fun n : Nat => (n:ℝ)) hcard)
  simpa only [Nat.mul_comm] using hh'

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

attribute [local instance] OAI.DirectedFeedback.RawFamily.reductionAlphabetNeZero
def gameComputation : Turing.TM2ComputableInPolyTime gameBits GapInstance.bits
    (fun I : Instance S.alphabet => (family S.alphabet P.M P.T R.N D C c hC).printer.inst (gameBits I)) := by
  let computation := (family S.alphabet P.M P.T R.N D C c hC).printer.computation
  exact {
    tm := computation.tm
    inputAlphabet := computation.inputAlphabet
    outputAlphabet := computation.outputAlphabet
    time := computation.time
    outputsFun := fun I => computation.outputsFun (gameBits I) }

theorem gameComputation_finite : FiniteAlphabet (gameComputation P S R C c hC).tm :=
  (family S.alphabet P.M P.T R.N D C c hC).printer.computation_finite

end RawFamily

end DirectedFeedback

end
end

end OAI
end


