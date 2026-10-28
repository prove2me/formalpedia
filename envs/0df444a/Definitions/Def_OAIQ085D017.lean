-- Prove2me | Definitions.Def_OAIQ085D017
-- name    : OAIQ085D017
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T16:09:33.672993+00:00
-- url     : https://prove2.me/theorems/592b01d2-1e7c-4bfc-8978-e8db8473a120
-- title:
--   Definitions bundle OAIQ085D017 of the split of OpenAI, Constant-factor hardness of directed feedback vertex set (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DirectedFeedback.main`, carved from OpenAI's openai/math development (OpenAI, *Constant-factor hardness of directed feedback vertex set (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 33 declarations of OpenAI's Lean: 3 definitions and 30 theorems. The definitions and types are `OAI.DFVSGames.Decoder.ActualMatrixContradiction.expectationOf_inline_ActualMatrixContradiction`, `OAI.DirectedFeedback.GraphPrinter.Family.computation`, `OAI.DirectedFeedback.LocalPrinter.Family.printer`.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: [`DirectedFeedback_Games_ActualAdviceSampling`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DirectedFeedback/Games/ActualAdviceSampling.lean), [`DirectedFeedback_RankGraph_AllGraph`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DirectedFeedback/RankGraph/AllGraph.lean), [`DirectedFeedback_RankGraph_PacketLocality`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DirectedFeedback/RankGraph/PacketLocality.lean), [`DirectedFeedback_RankGraph_Rational`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DirectedFeedback/RankGraph/Rational.lean), [`DirectedFeedback_RankGraph_SumBox`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DirectedFeedback/RankGraph/SumBox.lean).
--
--   **Imports.** It imports the published bundle `Def_DirectedFeedback`; the bundles `OAIQ085D007`, `OAIQ085D010` and `OAIQ085D011` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ085D023`; the proof of `OAI.DFVSGames.Decoder.ActualMatrixContradiction.contradiction`.
-- source:
--   OpenAI, Constant-factor hardness of directed feedback vertex set (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Constant-factor-hardness-of-directed-feedback-vertex-set-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Definitions.Def_DirectedFeedback
import Definitions.Def_OAIQ085D007
import Definitions.Def_OAIQ085D010
import Definitions.Def_OAIQ085D011

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_SumBox
attribute [-instance] _root_.OAI.DFVSGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.DFVSGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawBigFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.LivePackets.liveFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedBigFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCommonFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCompareFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFullFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedSmallFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain _root_.OAI.DirectedFeedback.RankPackets.shapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.SumBox
variable (A B : Type) [Fintype A] [Fintype B] [Nonempty (A ⊕ B)]
variable (n m L r : Nat) (c : B → Nat)

theorem valid_iff (i : Fin (size A B n m L r c)) : valid A B n m L r c i.val ↔
    validBox A B n m L r c ((BoxCodec.equiv (A ⊕ B) (base n m) (copies r c) L (base_pos n m)).symm i) := by
  unfold valid tag digits copy validBox
  rw [BoxCodec.decode_tag (A ⊕ B) (base n m) (copies r c) L (base_pos n m) i]
  simp_rw [BoxCodec.decode_digits (A ⊕ B) (base n m) (copies r c) L (base_pos n m) i,
    BoxCodec.decode_copy (A ⊕ B) (base n m) (copies r c) L (base_pos n m) i]

theorem valid_embed (v : Live A B n m L r c) : valid A B n m L r c (embed A B n m L r c v).val := by
  rw [valid_iff]
  simpa only [embed,Equiv.symm_apply_apply] using validBox_toBox A B n m L r c v

theorem valid_surjective (i : Fin (size A B n m L r c)) (hi : valid A B n m L r c i.val) :
    ∃ v, embed A B n m L r c v=i := by
  obtain ⟨v,hv⟩ := validBox_surjective A B n m L r c _ ((valid_iff A B n m L r c i).mp hi)
  refine ⟨v,?_⟩
  unfold embed
  rw [hv]
  exact (BoxCodec.equiv (A ⊕ B) (base n m) (copies r c) L (base_pos n m)).apply_symm_apply i

theorem tag_embed (v : Live A B n m L r c) :
    tag A B n m L r c (embed A B n m L r c v).val=(toBox A B n m L r c v).1 :=
  BoxCodec.tag_equiv _ _ _ _ _ _

end DirectedFeedback.SumBox

end


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_ActualAdviceSampling
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Decoder.ActualMatrixContradiction

open Integration.BinaryLinear Reduction ActualSource Foundations.Games
open scoped BigOperators Classical

noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

variable {k s d r : ℕ}

def expectationOf_inline_ActualMatrixContradiction {X : Type*} {i : Fintype X}
    (μ : @FiniteDistribution X i) (f : X → ℝ) : ℝ :=
  @FiniteDistribution.expectation X i μ f

end
end DFVSGames.Decoder.ActualMatrixContradiction

namespace DFVSGames.Gadget

universe u v

attribute [instance] Stage.inputAdd Stage.inputModule Stage.shiftAdd Stage.shiftModule
  Stage.inputFinite Stage.shiftFinite Stage.noiseFinite Stage.noiseNonempty

end DFVSGames.Gadget

end OAI
end

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
theorem m_def (r : Nat) : Def (r:=r) (fun x _ => m x) := (Def.lit 1).max (word_def (Def.lit 2))

end DirectedFeedback.GameRead

end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_AllGraph
attribute [-instance] _root_.OAI.DirectedFeedback.LivePackets.liveFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.GraphPrinter
open BoundedExpr

namespace Family
variable (F : Family)

theorem n_def_any (r : Nat) : Def (r:=r) (fun x _ => F.n x) :=
  F.n_def.subst Fin.elim0 (fun i => i.elim0)

theorem count_def : Def (r:=0) (fun x _ => F.count x) := by
  have ha : Def (r:=2) (fun x a => if F.arc x (a 1) (a 0) then 1 else 0) :=
    F.arc_def.rename ![1,0]
  simpa only [count,Fin.cons_zero,Fin.cons_one] using
    (F.n_def_any 0).sum ((F.n_def_any 1).sum ha)

theorem edgeBits_def : OutDef (r:=0) (fun x _ => F.edgeBits x) := by
  have ha : PDef (r:=2) (fun x a => F.arc x (a 1) (a 0)) :=
    F.arc_def.rename ![1,0]
  have hb : OutDef (r:=2) (fun x a => if F.arc x (a 1) (a 0)
      then natBits (a 1)++natBits (a 0) else []) :=
    ((OutDef.nat (Def.arg 1)).append (OutDef.nat (Def.arg 0))).when ha
  simpa only [edgeBits,Fin.cons_zero,Fin.cons_one] using
    OutDef.loop (F.n_def_any 0) (OutDef.loop (F.n_def_any 1) hb)

theorem bits_def : OutDef (r:=0) (fun x _ => F.bits x) := by
  have hv : OutDef (r:=0) (fun x _ => (List.range (F.n x)).flatMap natBits) := by
    change OutDef (fun x (_ : Fin 0 → Nat) => (List.range (F.n x)).flatMap (fun i => List.replicate i true++[false]))
    simpa only [Fin.cons_zero] using OutDef.loop (F.n_def_any 0) (OutDef.nat (Def.arg 0))
  exact ((((OutDef.nat F.k_def).append (OutDef.nat F.n_def)).append hv).append
    (OutDef.nat F.count_def)).append F.edgeBits_def

noncomputable def computation : Turing.TM2ComputableInPolyTime (id : List Bool → List Bool)
    GapInstance.bits F.inst := by
  let o := F.bits_def.choose
  have ho : ∀ x, o.eval x Fin.elim0=(F.inst x).bits := fun x =>
    (F.bits_def.choose_spec x Fin.elim0).trans (F.bits_correct x)
  exact Output.realizes _ _ o ho

theorem computation_finite (k : F.computation.tm.K) : Finite (F.computation.tm.Γ k) := by
  unfold computation
  exact Output.realizes_alphabet _ _ _ _ k

end Family
end DirectedFeedback.GraphPrinter

end
end

section

noncomputable section
open scoped Classical
namespace DirectedFeedback.LocalAssignments

namespace Definability
open BoundedExpr
variable {r : Nat} {S A : Type} [Fintype S] [Fintype A]

omit [Fintype A] in
 theorem consistent_def (c : S → List Bool → (Fin r → Nat) → Nat)
    (hc : ∀ i, Def (c i)) (a : S → A) :
    PDef (fun x z => Consistent (fun i => c i x z) a) := by
  exact PDef.all (fun i => PDef.all (fun j =>
    (PDef.nat_eq (hc i) (hc j)).imp (PDef.const (a i=a j))))

end Definability
end DirectedFeedback.LocalAssignments

end
end

section

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.LocalPrinter
open BoundedExpr LocalAssignments

namespace Family
variable {S T X Y : Type} [Fintype S] [Fintype T] [Fintype X] [Fintype Y]
  [Nonempty X] [Nonempty Y] {H : Nat} (F : Family S T X Y H)

omit [Nonempty X] [Nonempty Y] in
theorem arc_def : PDef (r:=2) (fun x a => F.Arc x (a 0) (a 1)) := by
  have hu (s : S ⊕ S) : Def (r:=2) (fun x a => Sum.elim (F.u x (a 0)) (F.u x (a 1)) s) := by
    cases s with
    | inl s => exact (F.u_def s).rename (fun _ => 0)
    | inr s => exact (F.u_def s).rename (fun _ => 1)
  have hv (t : T ⊕ T) : Def (r:=2) (fun x a => Sum.elim (F.v x (a 0)) (F.v x (a 1)) t) := by
    cases t with
    | inl t => exact (F.v_def t).rename (fun _ => 0)
    | inr t => exact (F.v_def t).rename (fun _ => 1)
  have hr0 := F.rule_def.rename (s:=2) (fun _ => 0)
  have hr1 := F.rule_def.rename (s:=2) (fun _ => 1)
  have hv0 : PDef (r:=2) (fun x a => F.valid x (a 0)) := F.valid_def.rename (fun _ => 0)
  have hv1 : PDef (r:=2) (fun x a => F.valid x (a 1)) := F.valid_def.rename (fun _ => 1)
  exact ((PDef.nat_eq (Def.arg 0) (Def.arg 1)).not).and
    (hv0.and (hv1.and
      (PDef.all (fun a => PDef.all (fun b =>
        (Definability.consistent_def _ hu a).imp
          ((Definability.consistent_def _ hv b).imp
            ((hr0.pair hr1).toDef (fun r => if Ordered (r.1 (a ∘ Sum.inl) (b ∘ Sum.inl))
              (r.2 (a ∘ Sum.inr) (b ∘ Sum.inr)) then 1 else 0))))))))

def printer : GraphPrinter.Family where
  n := F.n
  k := F.k
  arc := F.Arc
  n_def := F.n_def
  k_def := F.k_def
  arc_def := F.arc_def
  k_pos := F.k_pos
  irrefl := fun _ _ h => h.1 rfl

end Family
end DirectedFeedback.LocalPrinter

end
end

section

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.SourceProbability.FiniteDistribution

theorem iid_zip {A B : Type} [Fintype A] [Fintype B]
    (μ : FiniteDistribution A) (ν : FiniteDistribution B) (n : Nat) :
    ((μ.iid n).product (ν.iid n)).transport (zipEquiv A B n)=(μ.product ν).iid n := by
  apply eq_of_weight_eq
  intro z
  change (∏ i, μ.weight (z i).1)*(∏ i,ν.weight (z i).2)=
    ∏ i, μ.weight (z i).1*ν.weight (z i).2
  exact (Finset.prod_mul_distrib).symm

theorem expectation_iid_zip {A B : Type} [Fintype A] [Fintype B]
    (μ : FiniteDistribution A) (ν : FiniteDistribution B) (n : Nat)
    (f : (Fin n → A × B) → ℝ) :
    (μ.iid n).expectation (fun a => (ν.iid n).expectation (fun b => f (fun i => (a i,b i)))) =
      ((μ.product ν).iid n).expectation f := by
  rw [← iid_zip,expectation_transport,expectation_product]
  rfl

theorem expectation_iid_map {A B : Type} [Fintype A] [Fintype B]
    (μ : FiniteDistribution A) (g : A → B) (n : Nat) (f : (Fin n → B) → ℝ) :
    (μ.iid n).expectation (fun a => f (fun i => g (a i))) =
      ((μ.pushforward g).iid n).expectation f := by
  rw [iid_pushforward,expectation_pushforward]

theorem sample_prefix {E U S : Type} [Fintype E] [Fintype U] [Fintype S]
    (μ : FiniteDistribution E) (left : E → U) (ν : FiniteDistribution S)
    {t L : Nat} (ht : t≤L) (f : (Fin t → U × S) → ℝ) :
    (ν.iid t).expectation (fun s => (μ.iid L).expectation
      (fun e => f (fun j => (left (e (Fin.castLE ht j)),s j)))) =
      (((μ.pushforward left).product ν).iid t).expectation f := by
  rw [expectation_comm]
  change (μ.iid L).expectation (fun e => (ν.iid t).expectation
      (fun s => f (fun j => (left (takePrefix ht e j),s j)))) = _
  rw [expectation_iid_take μ ht (fun e => (ν.iid t).expectation
    (fun s => f (fun j => (left (e j),s j))))]
  rw [expectation_iid_map μ left t (fun a => (ν.iid t).expectation
    (fun s => f (fun j => (a j,s j))))]
  exact expectation_iid_zip _ _ _ _

theorem sample_prefix_fresh {E U S : Type} [Fintype E] [Fintype U] [Fintype S]
    (μ : FiniteDistribution E) (left : E → U) (ν : FiniteDistribution S)
    {t L : Nat} (ht : t<L) (f : (Fin t → U × S) → E → ℝ) :
    (ν.iid t).expectation (fun s => (μ.iid L).expectation
      (fun e => f (fun j => (left (e (Fin.castLE (Nat.le_of_lt ht) j)),s j)) (e ⟨t,ht⟩))) =
      (((μ.pushforward left).product ν).iid t).expectation
        (fun a => μ.expectation (f a)) := by
  have h (s : Fin t → S) := expectation_iid_prefix_fresh μ ht
    (fun e fresh => f (fun j => (left (e j),s j)) fresh)
  calc
    _ = (ν.iid t).expectation (fun s => (μ.iid t).expectation
      (fun e => μ.expectation (fun fresh => f (fun j => (left (e j),s j)) fresh))) :=
        expectation_congr _ h
    _ = _ := sample_prefix μ left ν le_rfl (fun a => μ.expectation (f a))

end DirectedFeedback.SourceProbability.FiniteDistribution

end
end

section

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.PacketSeeds
open SourceProbability FiniteDistribution Construction PrefixExperiment Games
variable {U V E X Y : Type} [Fintype U] [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
variable {M T N : Nat} [NeZero M] [NeZero T]

variable (ψLaw : FiniteDistribution (Emb (rankLength X T) N))

variable (G : Game U V E X Y)

omit [Fintype V] [Fintype Y] [Nonempty X] [Nonempty Y] [NeZero T] in
theorem sample_full (f : Full U X M T N → ℝ) :
    (fullLaw ψLaw).expectation (fun a => (G.edgeLaw.iid (T+1)).expectation (fun e => f (fillFull G a e))) =
      (Construction.fullLaw G ψLaw).expectation f := by
  simp only [fullLaw,Construction.fullLaw,expectation_product]
  apply expectation_congr
  intro ψ
  exact sample_prefix G.edgeLaw G.left slotLaw (Nat.le_succ T) (fun a => f (ψ,a))

omit [Fintype V] [Fintype Y] [Nonempty Y] in
theorem sample_big (f : Big U X M T N → ℝ) :
    (bigLaw ψLaw).expectation (fun a => (G.edgeLaw.iid (T+1)).expectation (fun e => f (fillBig G a e))) =
      (Construction.bigLaw G ψLaw).expectation f := by
  simp only [bigLaw,commonLaw,Construction.bigLaw,Construction.common,PrefixExperiment.commonLaw,
    expectation_product,expectation_sigma]
  apply expectation_congr
  intro ψ
  apply expectation_congr
  intro t
  simp_rw [expectation_comm Pivotal.labelOrderLaw (G.edgeLaw.iid (T+1))]
  simp only [Construction.bigMarginal,expectation_pushforward]
  exact sample_prefix_fresh G.edgeLaw G.left slotLaw (by have := t.isLt; omega : t.val<T+1)
    (fun a e => Pivotal.labelOrderLaw.expectation (fun o => f ((ψ,⟨t,a⟩),(G.left e,o))))

omit [Nonempty X] in
theorem sample_small (f : Small U V X Y M T N → ℝ) :
    (smallLaw ψLaw).expectation (fun a => (G.edgeLaw.iid (T+1)).expectation (fun e => f (fillSmall G a e))) =
      (Construction.smallLaw G ψLaw).expectation f := by
  simp only [smallLaw,commonLaw,Construction.smallLaw,Construction.common,PrefixExperiment.commonLaw,
    expectation_product,expectation_sigma]
  apply expectation_congr
  intro ψ
  apply expectation_congr
  intro t
  simp_rw [expectation_comm Pivotal.labelOrderLaw (G.edgeLaw.iid (T+1))]
  simp only [Construction.smallMarginal,expectation_pushforward]
  exact sample_prefix_fresh G.edgeLaw G.left slotLaw (by have := t.isLt; omega : t.val<T+1)
    (fun a e => Pivotal.labelOrderLaw.expectation (fun o => f ((ψ,⟨t,a⟩),(G.right e,o))))

omit [Fintype V] [Nonempty X] [Nonempty Y] in
theorem sample_compare (f : Compare U E X Y M T N → ℝ) :
    (compareLaw ψLaw).expectation (fun a => (G.edgeLaw.iid (T+1)).expectation (fun e => f (fillCompare G a e))) =
      (Construction.comparisonLaw G ψLaw).expectation f := by
  simp only [compareLaw,Construction.comparisonLaw,expectation_sigma]
  simp only [commonLaw,Construction.common,PrefixExperiment.commonLaw,expectation_product,expectation_sigma]
  apply expectation_congr
  intro ψ
  apply expectation_congr
  intro t
  change (slotLaw.iid t.val).expectation (fun a =>
    (localCompareLaw t.val).expectation (fun z => (G.edgeLaw.iid (T+1)).expectation
      (fun e => f (fillCompare G ⟨(ψ,⟨t,a⟩),z⟩ e)))) = _
  simp_rw [expectation_comm (localCompareLaw t.val) (G.edgeLaw.iid (T+1))]
  dsimp +unfoldPartialApp only [fillCompare,fillCommon,fillPrefix,fresh]
  simpa +unfoldPartialApp only [localCompareLaw,expectation_sigma,expectation_product,fillCompare,fillCommon,fillPrefix,fresh,
    PrefixExperiment.atomLaw,Construction.bigMarginal,slotLaw] using
    sample_prefix_fresh G.edgeLaw G.left slotLaw (by have := t.isLt; omega : t.val<T+1)
      (fun a e => (localCompareLaw t.val).expectation (fun z => f ⟨(ψ,⟨t,a⟩),e,z⟩))

end DirectedFeedback.PacketSeeds

end
end

end OAI
end

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

omit [NeZero T] in
theorem scale_def (s : Nat) : Def (r:=s) (fun x _ => scale T C x) :=
  (Def.lit C).mul ((GameRead.m_def s).pow (T+1))
omit [NeZero T] in
theorem r_def (s : Nat) : Def (r:=s) (fun x _ => r T D C x) :=
  (scale_def T C s).mul (Def.lit (D+1))
omit [NeZero q] [NeZero M] [NeZero T] [NeZero N] in
theorem copies_def (s : Nat) : Def (r:=s) (fun x _ => copies q M T N D C c x) :=
  ((r_def T D C s).add (Def.lit (∑ s,c s))).add (Def.lit 1)

end DirectedFeedback.RawFamily

end
end

section

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.PacketSeeds
open SourceProbability FiniteDistribution Construction PrefixExperiment Games
variable {U V E X Y : Type} [Fintype U] [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
variable {M T N : Nat} [NeZero M] [NeZero T]
variable (ψLaw : FiniteDistribution (Emb (rankLength X T) N))

variable (G : Game U V E X Y)

theorem moment (D H K : Nat) (f : AllVertex U V E X Y M T N → ℝ)
    (hf : ∀ r, f (.inl r)=0) :
    (∑ s, mass ψLaw H K s*(G.edgeLaw.iid (T+1)).expectation (fun e => f (fill G s e))) =
      ∑ v, allCost G ψLaw D H K v*f v := by
  have hex := sample_full ψLaw G (fun v => f (.inr (.inl (.inl v))))
  have heb := sample_big ψLaw G (fun v => f (.inr (.inl (.inr (.inl v)))))
  have hes := sample_small ψLaw G (fun v => f (.inr (.inl (.inr (.inr v)))))
  have hec := sample_compare ψLaw G (fun v => f (.inr (.inr v)))
  calc
    _ = H*(fullLaw ψLaw).expectation (fun s => (G.edgeLaw.iid (T+1)).expectation
          (fun e => f (.inr (.inl (.inl (fillFull G s e)))))) +
        (Fintype.card X)*(bigLaw ψLaw).expectation (fun s => (G.edgeLaw.iid (T+1)).expectation
          (fun e => f (.inr (.inl (.inr (.inl (fillBig G s e))))))) +
        (Fintype.card Y)*(smallLaw ψLaw).expectation (fun s => (G.edgeLaw.iid (T+1)).expectation
          (fun e => f (.inr (.inl (.inr (.inr (fillSmall G s e))))))) +
        K*(compareLaw ψLaw).expectation (fun s => (G.edgeLaw.iid (T+1)).expectation
          (fun e => f (.inr (.inr (fillCompare G s e))))) := by
      simp only [Fintype.sum_sum_type,mass,fill,expectation,Finset.mul_sum]
      ring_nf
    _ = _ := by
      rw [hex,heb,hes,hec]
      simp only [Fintype.sum_sum_type,allCost,hf,mul_zero,Finset.sum_const_zero,zero_add,
        expectation,Finset.mul_sum]
      ring_nf

theorem integer_moment [Nonempty E] (hE : G.edgeLaw=uniform E) (D H K C : Nat)
    (c : Seed X Y M T N → Nat) (hc : ∀ s, (C:ℝ)*mass ψLaw H K s=c s)
    (f : AllVertex U V E X Y M T N → ℝ) (hf : ∀ r, f (.inl r)=0) :
    (∑ s, (c s:ℝ)*∑ e : Fin (T+1) → E, f (fill G s e)) =
      (C*(Fintype.card E)^(T+1):Nat)*(∑ v, allCost G ψLaw D H K v*f v) := by
  rw [← moment ψLaw G D H K f hf]
  simp only [hE,iid_uniform_expectation,Nat.cast_mul,Nat.cast_pow,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  have hm : ((Fintype.card E:ℝ)^(T+1)) ≠ 0 := by positivity
  rw [← hc s]
  field_simp
  simp only [Finset.mul_sum]

end DirectedFeedback.PacketSeeds

end
end

section

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.LivePackets
open Construction SourceProbability FiniteDistribution Games RankGraph PacketSeeds
variable {W E X Y : Type} [Fintype W] [Fintype E] [Fintype X] [Fintype Y]
  [Nonempty W] [Nonempty E] [Nonempty X] [Nonempty Y]
variable {M T N : Nat} [NeZero M] [NeZero T]

variable (G : Game W W E X Y) (ψLaw : FiniteDistribution (Emb (rankLength X T) N))
variable (r : Nat) (c : Seed X Y M T N → Nat)

omit [Nonempty W] in
theorem sum_cost (hE : G.edgeLaw=uniform E) (D H K C : Nat)
    (hc : ∀ s, (C:ℝ)*mass ψLaw H K s=c s)
    (f : AllVertex W W E X Y M T N → ℝ) (hf : ∀ z, f (.inl z)=0) :
    (∑ a : Live (W:=W) (E:=E) r c, f (project G r c a)) =
      (C*(Fintype.card E)^(T+1):Nat)*(∑ v, allCost G ψLaw D H K v*f v) := by
  rw [sum_project G r c f hf]
  exact integer_moment ψLaw G hE D H K C c hc f hf

omit [Nonempty W] in
theorem test_fiber_count (hE : G.edgeLaw=uniform E) (D H K C : Nat)
    (hc : ∀ s, (C:ℝ)*mass ψLaw H K s=c s)
    (z : Wild W W X Y M T N ⊕ Compare W E X Y M T N) :
    (PotentialCover.fiberCount (project G r c) (.inr z):ℝ) =
      (C*(Fintype.card E)^(T+1):Nat)*allCost G ψLaw D H K (.inr z) := by
  have h := sum_cost G ψLaw r c hE D H K C hc (fun v => if v=.inr z then 1 else 0)
    (fun _ => by simp)
  simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true, if_true] at h
  rw [← h]
  simp only [PotentialCover.fiberCount,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]

theorem fiber_weight (hE : G.edgeLaw=uniform E) (D H K C : Nat)
    (hc : ∀ s, (C:ℝ)*mass ψLaw H K s=c s)
    (hr : C*(Fintype.card E)^(T+1)*(D+1) ≤ r)
    (v : AllVertex W W E X Y M T N) :
    (C*(Fintype.card E)^(T+1):Nat)*allCost G ψLaw D H K v ≤
      PotentialCover.fiberCount (project G r c) v := by
  cases v with
  | inl z =>
    have hh := le_trans hr (rank_fiber_bound G r c z)
    simpa only [allCost,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_pow] using
      (show (C*(Fintype.card E)^(T+1)*(D+1):Nat)≤PotentialCover.fiberCount (project G r c) (.inl z) from hh)
        |> (fun h => (Nat.cast_le (α:=ℝ)).mpr h)
  | inr z => exact (test_fiber_count G ψLaw r c hE D H K C hc z).symm.le

end DirectedFeedback.LivePackets

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

include hc hE hproj in
omit [NeZero R.N] in
theorem live_card_bound (a : W x → X q) (b : W x → Y q)
    (hscore : 1-(P.theta:ℝ)≤G.score a b) :
    ((liveDeleted D C c x G fiber a b).card:ℝ) ≤ 4*scale P.T C x := by
  have hsum := LivePackets.sum_cost G R.law (r P.T D C x) c hE D (8*(D+1)) P.K C hc
    (fun v => if AllLabels.deleted G (hYX q) fiber a b v then 1 else 0)
    (fun z => by simp [AllLabels.deleted,TestGraph.LabelDeleted])
  have hbound := AllLabels.completeness P R G (hYX q) fiber hproj a b hscore
  have hcard : ((liveDeleted D C c x G fiber a b).card:ℝ)=
      ∑ z : Live D C c x, (if AllLabels.deleted G (hYX q) fiber a b (LivePackets.project G (r P.T D C x) c z) then 1 else 0) := by
    simp only [liveDeleted,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  rw [hcard,hsum]
  simp only [Fintype.card_fin,E,mul_ite,mul_one,mul_zero,Nat.cast_mul,Nat.cast_add,Nat.cast_one,scale,Nat.cast_ofNat,Nat.cast_pow]
  have hs : (0:ℝ)≤C*(GameRead.m x)^(P.T+1) := by positivity
  have hh := mul_le_mul_of_nonneg_left hbound hs
  convert hh using 1 <;> first | rfl | ring

end DirectedFeedback.RawFamily

end
end

end OAI
end


