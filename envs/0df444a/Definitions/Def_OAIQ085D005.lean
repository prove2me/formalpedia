-- Prove2me | Definitions.Def_OAIQ085D005
-- name    : OAIQ085D005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T15:53:34.93672+00:00
-- url     : https://prove2.me/theorems/91094495-a9c4-4e2f-b39b-f7d35e81bcf4
-- title:
--   Definitions bundle OAIQ085D005 of the split of OpenAI, Constant-factor hardness of directed feedback vertex set (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DirectedFeedback.main`, carved from OpenAI's openai/math development (OpenAI, *Constant-factor hardness of directed feedback vertex set (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 271 declarations of OpenAI's Lean: 139 definitions, 5 inductive types or structures, 15 instances and 112 theorems. The definitions and types are `OAI.DirectedFeedback.BoundedExpr.UnaryRead.word`, `OAI.DirectedFeedback.BoundedExpr.UnaryRead.zerosBefore`, `OAI.DirectedFeedback.BoxCodec.Box`, `OAI.DirectedFeedback.BoxCodec.copy`, `OAI.DirectedFeedback.BoxCodec.digits`, `OAI.DirectedFeedback.BoxCodec.equiv`, `OAI.DirectedFeedback.BoxCodec.size`, `OAI.DirectedFeedback.BoxCodec.tag`, `OAI.DirectedFeedback.CookLevin.AgreeCone`, `OAI.DirectedFeedback.CookLevin.Atom`, `OAI.DirectedFeedback.CookLevin.FiniteCodec`, `OAI.DirectedFeedback.CookLevin.Follows`, `OAI.DirectedFeedback.CookLevin.InCone`, `OAI.DirectedFeedback.CookLevin.InitialConditions`, `OAI.DirectedFeedback.CookLevin.LocalCSP`, `OAI.DirectedFeedback.CookLevin.LocalCSP.Satisfiable`, `OAI.DirectedFeedback.CookLevin.LocalCSP.booleanize`, `OAI.DirectedFeedback.CookLevin.LocalCSP.padAt`, `OAI.DirectedFeedback.CookLevin.LocalData`, `OAI.DirectedFeedback.CookLevin.LocalData.wordCfg`, `OAI.DirectedFeedback.CookLevin.NPTableau.FixedSlot`, `OAI.DirectedFeedback.CookLevin.NPTableau.alphabetCodec`, `OAI.DirectedFeedback.CookLevin.NPTableau.capacity`, `OAI.DirectedFeedback.CookLevin.NPTableau.certBound`, `OAI.DirectedFeedback.CookLevin.NPTableau.decodeEvent`, `OAI.DirectedFeedback.CookLevin.NPTableau.eventCount`, `OAI.DirectedFeedback.CookLevin.NPTableau.fixedPrefix`, `OAI.DirectedFeedback.CookLevin.NPTableau.horizon`, `OAI.DirectedFeedback.CookLevin.NPTableau.inputBound`, `OAI.DirectedFeedback.CookLevin.NPTableau.queryNumber`, `OAI.DirectedFeedback.CookLevin.NPTableau.rawInitialAccepts`, `OAI.DirectedFeedback.CookLevin.NPTableau.rawQuery`, `OAI.DirectedFeedback.CookLevin.NPTableau.rawTableauQuery`, `OAI.DirectedFeedback.CookLevin.NPTableau.slotIndex`, `OAI.DirectedFeedback.CookLevin.NPTableau.tests`, `OAI.DirectedFeedback.CookLevin.NPTableau.variableIndex`, `OAI.DirectedFeedback.CookLevin.NoHoles`, `OAI.DirectedFeedback.CookLevin.Row`, `OAI.DirectedFeedback.CookLevin.StackAtom`, `OAI.DirectedFeedback.CookLevin.StepSlot` and 104 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `DirectedFeedback_CookLevin_NPTableau`, `DirectedFeedback_Main`, `DirectedFeedback_RankGraph_AllGraph`, `DirectedFeedback_RankGraph_Bias`, `DirectedFeedback_RankGraph_CellCount`, `DirectedFeedback_RankGraph_LastBias`, `DirectedFeedback_RankGraph_OutputDef`, `DirectedFeedback_RankGraph_PacketLocality`, `DirectedFeedback_RankGraph_Point`, `DirectedFeedback_RankGraph_PrefixBit`, `DirectedFeedback_RankGraph_Rational`, `DirectedFeedback_RankGraph_RoundBoolean`, `DirectedFeedback_RankGraph_StackFinite`, `DirectedFeedback_RankGraph_SumBox`, `DirectedFeedback_RankGraph_UnweightedIntegrated`.
--
--   **Imports.** It imports the published bundle `Def_DirectedFeedback`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ085D010` and `OAIQ085D011`.
-- source:
--   OpenAI, Constant-factor hardness of directed feedback vertex set (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Constant-factor-hardness-of-directed-feedback-vertex-set-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Definitions.Def_DirectedFeedback

section
-- module Solutions.OAIQ085_DF.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434

/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
/-- The first projection of a probability measure on a product: found by instance search in d13f23b
(total `Measure.map`), here a measurable map. -/
instance isProbabilityMeasure_map_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.fst) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
instance isProbabilityMeasure_map_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.snd) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
instance isProbabilityMeasure_map_subtype_val {α : Type*} [MeasurableSpace α] {p : α → Prop}
    {μ : MeasureTheory.Measure {a // p a}} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Subtype.val) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
/-- Mathlib d13f23b's `YoungDiagram.card_transpose`. -/
@[simp]
theorem _root_.YoungDiagram.card_transpose (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  unfold YoungDiagram.card
  apply Finset.card_bij (fun c _ => c.swap)
  · intro c hc
    have : c ∈ μ.transpose := hc
    rw [YoungDiagram.mem_transpose] at this
    exact this
  · intro a _ b _ h
    simpa using h
  · intro b hb
    refine ⟨b.swap, ?_, by simp⟩
    show b.swap ∈ μ.transpose
    rw [YoungDiagram.mem_transpose]
    simpa using hb
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
/-- `simp` closes `2 ≤ ∞` in `WithTop ℕ∞` (the smoothness order) in Mathlib d13f23b; ours has the
lemma only for `1` and casts (AffineBernstein, `isSymmSndFDerivAt (by simp)`, 2026-10-26). -/
@[simp]
theorem ofNat_le_infty (n : ℕ) [n.AtLeastTwo] : (no_index (OfNat.ofNat n) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  ENat.LEInfty.out
section Y
instance closedSubmoduleNormedAddCommGroup {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedAddCommGroup K :=
  inferInstanceAs (NormedAddCommGroup K.toSubmodule)
instance closedSubmoduleNormedSpace {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedSpace 𝕜 K :=
  inferInstanceAs (NormedSpace 𝕜 K.toSubmodule)
instance closedSubmoduleInner {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : InnerProductSpace 𝕜 K :=
  inferInstanceAs (InnerProductSpace 𝕜 K.toSubmodule)
end Y

/-- The underlying ⋆-subalgebra of a von Neumann algebra is norm closed, found by instance search in
d13f23b (Kadison similarity, oaiq-075). -/
instance vonNeumannToStarSubalgebraIsClosed {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (P : VonNeumannAlgebra H) : IsClosed (P.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  have := Set.isClosed_centralizer (Set.centralizer (P.carrier))
  rw [P.centralizer_centralizer'] at this
  exact this
/-- A closed commutative ⋆-subalgebra of a C⋆-algebra is a commutative C⋆-algebra, found by instance search
in d13f23b (Kadison similarity, oaiq-075). -/
noncomputable instance starSubalgebraCommCStarAlgebra {B : Type*} [CStarAlgebra B] (A : StarSubalgebra ℂ B)
    [IsClosed (A : Set B)] [IsMulCommutative A] : CommCStarAlgebra A :=
  { StarSubalgebra.cstarAlgebra A with
    mul_comm := fun a b => IsMulCommutative.is_comm.comm a b }
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_StackFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open scoped Classical
namespace DirectedFeedback.DigitCodec

def encode (b : Nat) : {L : Nat} → (Fin L → Nat) → Nat
  | 0,_ => 0
  | _+1,a => a 0+b*encode b (Fin.tail a)

def decode (b : Nat) : (L : Nat) → Nat → Fin L → Nat
  | 0,_ => Fin.elim0
  | L+1,n => Fin.cons (n%b) (decode b L (n/b))

theorem decode_lt (b : Nat) (hb : 0<b) (L n : Nat) (i : Fin L) : decode b L n i<b := by
  induction L generalizing n with
  | zero => exact i.elim0
  | succ L ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Nat.mod_lt _ hb
    · exact ih (n/b) j

theorem encode_lt (b : Nat) (_hb : 0<b) {L : Nat} (a : Fin L → Nat) (ha : ∀ i, a i<b) :
    encode b a < b^L := by
  induction L with
  | zero => simp [encode]
  | succ L ih =>
    have ht := ih (Fin.tail a) (fun i => ha i.succ)
    have h0 := ha 0
    simp only [encode,pow_succ]
    nlinarith

theorem decode_encode (b : Nat) (hb : 0<b) {L : Nat} (a : Fin L → Nat) (ha : ∀ i,a i<b) :
    decode b L (encode b a)=a := by
  induction L with
  | zero => funext i; exact i.elim0
  | succ L ih =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [decode,encode,Nat.add_mod,Nat.mod_eq_of_lt (ha 0)]
    · have he : (a 0+b*encode b (Fin.tail a))/b=encode b (Fin.tail a) := by
        rw [Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt (ha 0),zero_add]
      change decode b L ((a 0+b*encode b (Fin.tail a))/b) j=a j.succ
      rw [he]
      exact congrFun (ih (Fin.tail a) (fun i => ha i.succ)) j

theorem encode_decode (b : Nat) (hb : 0<b) (L n : Nat) (hn : n<b^L) :
    encode b (decode b L n)=n := by
  induction L generalizing n with
  | zero => simp only [pow_zero] at hn; simp [encode,show n=0 by omega]
  | succ L ih =>
    have ht : n/b<b^L := by
      apply (Nat.div_lt_iff_lt_mul hb).mpr
      simpa [pow_succ] using hn
    simp only [decode,encode,Fin.cons_zero,Fin.tail_cons,ih (n/b) ht]
    exact Nat.mod_add_div n b

noncomputable def equiv (b : Nat) (hb : 0<b) (L : Nat) : (Fin L → Fin b) ≃ Fin (b^L) where
  toFun a := ⟨encode b (fun i => (a i).val),encode_lt b hb _ (fun i => (a i).isLt)⟩
  invFun n := fun i => ⟨decode b L n.val i,decode_lt b hb L n.val i⟩
  left_inv a := by
    funext i
    apply Fin.ext
    exact congrFun (decode_encode b hb (fun i => (a i).val) (fun i => (a i).isLt)) i
  right_inv n := by apply Fin.ext; exact encode_decode b hb L n.val n.isLt

end DirectedFeedback.DigitCodec

end


noncomputable section
open scoped Classical
namespace DirectedFeedback.BoxCodec
variable (Tag : Type) [Fintype Tag] [Nonempty Tag]
variable (b C L : Nat) (hb : 0<b)

abbrev Box := Tag × ((Fin L → Fin b) × Fin C)
def size : Nat := Fintype.card Tag*(b^L*C)
def equiv : Box Tag b C L ≃ Fin (size Tag b C L) :=
  (Equiv.prodCongr (Fintype.equivFin Tag)
    ((Equiv.prodCongr (DigitCodec.equiv b hb L) (Equiv.refl (Fin C))).trans finProdFinEquiv)).trans
    finProdFinEquiv

def tag (i : Nat) : Tag :=
  if h : i/(b^L*C)<Fintype.card Tag then (Fintype.equivFin Tag).symm ⟨i/(b^L*C),h⟩
  else Classical.choice inferInstance
def digits (i : Nat) : Fin L → Nat := DigitCodec.decode b L ((i%(b^L*C))/C)
def copy (i : Nat) : Nat := (i%(b^L*C))%C

omit [Nonempty Tag] in
theorem digits_equiv (a : Box Tag b C L) (j : Fin L) :
    digits b C L (equiv Tag b C L hb a).val j=(a.2.1 j).val := by
  have h := (equiv Tag b C L hb).left_inv a
  have he := congrArg (fun z : Box Tag b C L => (z.2.1 j).val) h
  exact he

omit [Nonempty Tag] in
theorem copy_equiv (a : Box Tag b C L) :
    copy b C L (equiv Tag b C L hb a).val=a.2.2.val := by
  have h := (equiv Tag b C L hb).left_inv a
  exact congrArg (fun z : Box Tag b C L => z.2.2.val) h

omit [Nonempty Tag] in
theorem decode_digits (i : Fin (size Tag b C L)) (j : Fin L) :
    digits b C L i.val j=(((equiv Tag b C L hb).symm i).2.1 j).val := by
  simpa using digits_equiv Tag b C L hb ((equiv Tag b C L hb).symm i) j
omit [Nonempty Tag] in
theorem decode_copy (i : Fin (size Tag b C L)) :
    copy b C L i.val=((equiv Tag b C L hb).symm i).2.2.val := by
  simpa using copy_equiv Tag b C L hb ((equiv Tag b C L hb).symm i)

end DirectedFeedback.BoxCodec

end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_SumBox
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
abbrev Live := ((A × (Fin L → Fin n)) × Fin r) ⊕ (Σ s : B, (Fin L → Fin m) × Fin (c s))
def base : Nat := n+m+1
def copies {B : Type} [Fintype B] (r : Nat) (c : B → Nat) : Nat := r+(∑ s,c s)+1

theorem base_pos : 0<base n m := by unfold base; omega
theorem c_le {B : Type} [Fintype B] (r : Nat) (c : B → Nat) (s : B) : c s ≤ copies r c := by
  have hs := Finset.single_le_sum (fun s _ => Nat.zero_le (c s)) (Finset.mem_univ s)
  unfold copies
  omega

def toBox : Live A B n m L r c → BoxCodec.Box (A ⊕ B) (base n m) (copies r c) L
  | .inl ((s,a),j) => (.inl s, (fun i => ⟨a i,by have := (a i).isLt; unfold base; omega⟩),
      ⟨j,by have := j.isLt; unfold copies; omega⟩)
  | .inr ⟨s,a,j⟩ => (.inr s,(fun i => ⟨a i,by have := (a i).isLt; unfold base; omega⟩),
      ⟨j,lt_of_lt_of_le j.isLt (c_le r c s)⟩)

def validBox (z : BoxCodec.Box (A ⊕ B) (base n m) (copies r c) L) : Prop :=
  match z.1 with
  | .inl _ => (∀ i, (z.2.1 i).val < n) ∧ z.2.2.val < r
  | .inr s => (∀ i, (z.2.1 i).val < m) ∧ z.2.2.val < c s

omit [Fintype A] [Nonempty (A ⊕ B)] in
theorem toBox_injective : Function.Injective (toBox A B n m L r c) := by
  intro x y h
  rcases x with ⟨⟨s,a⟩,j⟩ | ⟨s,a,j⟩ <;> rcases y with ⟨⟨t,b⟩,k⟩ | ⟨t,b,k⟩
  · have hh := Prod.mk.inj h
    have hst : s=t := Sum.inl.inj hh.1
    subst t
    have hab : a=b := by
      funext i
      apply Fin.ext
      exact congrArg (fun z => (z.1 i).val) hh.2
    have hjk : j=k := Fin.ext (congrArg (fun z => z.2.val) hh.2)
    simp [hab,hjk]
  · have hh := congrArg (fun z : BoxCodec.Box (A ⊕ B) (base n m) (copies r c) L => z.1) h
    simp only [toBox] at hh
    cases hh
  · have hh := congrArg (fun z : BoxCodec.Box (A ⊕ B) (base n m) (copies r c) L => z.1) h
    simp only [toBox] at hh
    cases hh
  · have hh := Prod.mk.inj h
    have hst : s=t := Sum.inr.inj hh.1
    subst t
    have hab : a=b := by
      funext i
      apply Fin.ext
      exact congrArg (fun z => (z.1 i).val) hh.2
    have hjk : j=k := Fin.ext (congrArg (fun z => z.2.val) hh.2)
    simp [hab,hjk]

omit [Fintype A] [Nonempty (A ⊕ B)] in
theorem validBox_toBox (v : Live A B n m L r c) : validBox A B n m L r c (toBox A B n m L r c v) := by
  rcases v with ⟨⟨s,a⟩,j⟩ | ⟨s,a,j⟩ <;> exact ⟨fun i => (a i).isLt,j.isLt⟩

omit [Fintype A] [Nonempty (A ⊕ B)] in
theorem validBox_surjective (z : BoxCodec.Box (A ⊕ B) (base n m) (copies r c) L)
    (hz : validBox A B n m L r c z) : ∃ v, toBox A B n m L r c v=z := by
  rcases z with ⟨s|s,a,j⟩
  · refine ⟨.inl ((s,fun i => ⟨(a i).val,hz.1 i⟩),⟨j.val,hz.2⟩),?_⟩
    rfl
  · refine ⟨.inr ⟨s,(fun i => ⟨(a i).val,hz.1 i⟩),⟨j.val,hz.2⟩⟩,?_⟩
    rfl

def size := BoxCodec.size (A ⊕ B) (base n m) (copies r c) L
def tag (i : Nat) := BoxCodec.tag (A ⊕ B) (base n m) (copies r c) L i
def digits (i : Nat) := BoxCodec.digits (base n m) (copies r c) L i
def copy (i : Nat) := BoxCodec.copy (base n m) (copies r c) L i
def embed (v : Live A B n m L r c) : Fin (size A B n m L r c) :=
  BoxCodec.equiv (A ⊕ B) (base n m) (copies r c) L (base_pos n m) (toBox A B n m L r c v)
def valid (i : Nat) : Prop :=
  match tag A B n m L r c i with
  | .inl _ => (∀ j, digits B n m L r c i j < n) ∧ copy B n m L r c i < r
  | .inr s => (∀ j, digits B n m L r c i j < m) ∧ copy B n m L r c i < c s

omit [Nonempty (A ⊕ B)] in
theorem embed_injective : Function.Injective (embed A B n m L r c) :=
  (BoxCodec.equiv (A ⊕ B) (base n m) (copies r c) L (base_pos n m)).injective.comp
    (toBox_injective A B n m L r c)

omit [Nonempty (A ⊕ B)] in
theorem digits_embed (v : Live A B n m L r c) (j : Fin L) :
    digits B n m L r c (embed A B n m L r c v).val j=((toBox A B n m L r c v).2.1 j).val :=
  BoxCodec.digits_equiv _ _ _ _ _ _ _

end DirectedFeedback.SumBox

end


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_CookLevin_NPTableau
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace DirectedFeedback.CookLevin
open Turing
variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}

abbrev Words (Γ : K → Type) := ∀ k, ℕ → Option (Γ k)

def wordPush {α : Type} (a : α) (w : ℕ → Option α) : ℕ → Option α
  | 0 => some a
  | n+1 => w n

def wordPop {α : Type} (w : ℕ → Option α) : ℕ → Option α := fun n => w (n+1)

def wordsOfLists (S : ∀ k, List (Γ k)) : Words Γ := fun k n => (S k)[n]?

@[simp] theorem wordsOfLists_update (S : ∀ k, List (Γ k)) (k : K) (l : List (Γ k)) :
    wordsOfLists (Function.update S k l) =
      Function.update (wordsOfLists S) k (fun n => l[n]?) := by
  funext j n
  by_cases hj : j = k
  · subst j
    simp [wordsOfLists]
  · simp [wordsOfLists, hj]

@[simp] theorem wordsOfLists_push (S : ∀ k, List (Γ k)) (k : K) (a : Γ k) :
    wordsOfLists (Function.update S k (a :: S k)) =
      Function.update (wordsOfLists S) k (wordPush a (wordsOfLists S k)) := by
  rw [wordsOfLists_update]
  congr 1
  funext n
  cases n <;> rfl

@[simp] theorem wordsOfLists_pop (S : ∀ k, List (Γ k)) (k : K) :
    wordsOfLists (Function.update S k (S k).tail) =
      Function.update (wordsOfLists S) k (wordPop (wordsOfLists S k)) := by
  rw [wordsOfLists_update]
  congr 1
  funext n
  simp [wordPop, wordsOfLists]

structure WordCfg (Γ : K → Type) (Λ σ : Type) where
  label : Option Λ
  var : σ
  stk : Words Γ

def WordCfg.ofCfg (c : TM2.Cfg Γ Λ σ) : WordCfg Γ Λ σ :=
  ⟨c.l,c.var,wordsOfLists c.stk⟩

def wordStepAux : TM2.Stmt Γ Λ σ → σ → Words Γ → WordCfg Γ Λ σ
  | .push k f q, v, S => wordStepAux q v (Function.update S k (wordPush (f v) (S k)))
  | .peek k f q, v, S => wordStepAux q (f v (S k 0)) S
  | .pop k f q, v, S => wordStepAux q (f v (S k 0)) (Function.update S k (wordPop (S k)))
  | .load f q, v, S => wordStepAux q (f v) S
  | .branch f q r, v, S => if f v then wordStepAux q v S else wordStepAux r v S
  | .goto f, v, S => ⟨some (f v),v,S⟩
  | .halt, v, S => ⟨none,v,S⟩

theorem wordStepAux_ofLists (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) :
    wordStepAux q v (wordsOfLists S) = WordCfg.ofCfg (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih => simp only [wordStepAux, TM2.stepAux, WordCfg.ofCfg]; rw [← wordsOfLists_push]; exact ih _ _
  | peek k f q ih => simpa only [wordStepAux, TM2.stepAux, wordsOfLists, ← List.head?_eq_getElem?] using ih (f v (S k).head?) S
  | pop k f q ih =>
      simp only [wordStepAux, TM2.stepAux, WordCfg.ofCfg]
      rw [← wordsOfLists_pop]
      simpa only [wordsOfLists, ← List.head?_eq_getElem?, WordCfg.ofCfg] using ih (f v (S k).head?) (Function.update S k (S k).tail)
  | load f q ih => exact ih _ _
  | branch f q r iq ir => cases h : f v <;> simp [wordStepAux, TM2.stepAux, h, iq, ir]
  | goto f => rfl
  | halt => rfl

def radius : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => radius q + 1
  | .peek _ _ q => radius q + 1
  | .pop _ _ q => radius q + 1
  | .load _ q => radius q
  | .branch _ q r => max (radius q) (radius r)
  | .goto _ => 0
  | .halt => 0

def InCone (r j i : ℕ) : Prop := i < r ∨ (i ≤ j+r ∧ j ≤ i+r)

def AgreeCone (r j : ℕ) (S R : Words Γ) : Prop :=
  ∀ k i, InCone r j i → S k i = R k i

omit [DecidableEq K] in
theorem agreeCone_mono {r s j : ℕ} (hrs : r ≤ s) {S R : Words Γ}
    (h : AgreeCone s j S R) : AgreeCone r j S R := by
  intro k i hi
  apply h
  rcases hi with hi | ⟨hi,hj⟩
  · exact Or.inl (lt_of_lt_of_le hi hrs)
  · exact Or.inr ⟨by omega, by omega⟩

omit [DecidableEq K] in
theorem agreeCone_head {r j : ℕ} {S R : Words Γ}
    (h : AgreeCone (r+1) j S R) (k : K) : S k 0 = R k 0 :=
  h k 0 (Or.inl (Nat.succ_pos _))

theorem agreeCone_push {r j : ℕ} {S R : Words Γ}
    (h : AgreeCone (r+1) j S R) (k : K) (a : Γ k) :
    AgreeCone r j (Function.update S k (wordPush a (S k)))
      (Function.update R k (wordPush a (R k))) := by
  intro l i hi
  by_cases hl : l = k
  · subst l
    simp only [Function.update_self]
    cases i with
    | zero => rfl
    | succ i =>
      apply h
      rcases hi with hi | ⟨hi,hj⟩
      · exact Or.inl (by omega)
      · exact Or.inr ⟨by omega, by omega⟩
  · simpa only [Function.update_of_ne hl] using agreeCone_mono (Nat.le_succ r) h l i hi

theorem agreeCone_pop {r j : ℕ} {S R : Words Γ}
    (h : AgreeCone (r+1) j S R) (k : K) :
    AgreeCone r j (Function.update S k (wordPop (S k)))
      (Function.update R k (wordPop (R k))) := by
  intro l i hi
  by_cases hl : l = k
  · subst l
    simp only [Function.update_self, wordPop]
    apply h
    rcases hi with hi | ⟨hi,hj⟩
    · exact Or.inl (by omega)
    · exact Or.inr ⟨by omega, by omega⟩
  · simpa only [Function.update_of_ne hl] using agreeCone_mono (Nat.le_succ r) h l i hi

theorem wordStepAux_local (q : TM2.Stmt Γ Λ σ) (v : σ) (S R : Words Γ) (j : ℕ)
    (h : AgreeCone (radius q) j S R) :
    (wordStepAux q v S).label = (wordStepAux q v R).label ∧
    (wordStepAux q v S).var = (wordStepAux q v R).var ∧
    ∀ k, (wordStepAux q v S).stk k j = (wordStepAux q v R).stk k j := by
  induction q generalizing v S R with
  | push k f q ih => exact ih _ _ _ (agreeCone_push h k (f v))
  | peek k f q ih =>
    have hh := agreeCone_head h k
    simp only [wordStepAux, hh]
    exact ih _ _ _ (agreeCone_mono (Nat.le_succ _) h)
  | pop k f q ih =>
    have hh := agreeCone_head h k
    simp only [wordStepAux, hh]
    exact ih _ _ _ (agreeCone_pop h k)
  | load f q ih => exact ih _ _ _ h
  | branch f q r iq ir =>
    cases hf : f v
    · simpa only [wordStepAux, hf, Bool.false_eq_true, ↓reduceIte] using
        ir v S R (agreeCone_mono (Nat.le_max_right _ _) h)
    · simpa only [wordStepAux, hf, ↓reduceIte] using
        iq v S R (agreeCone_mono (Nat.le_max_left _ _) h)
  | goto f => exact ⟨rfl,rfl,fun k => h k j (Or.inr ⟨by omega,by omega⟩)⟩
  | halt => exact ⟨rfl,rfl,fun k => h k j (Or.inr ⟨by omega,by omega⟩)⟩

end DirectedFeedback.CookLevin

namespace DirectedFeedback.CookLevin
open Turing
variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}

theorem stepAux_length (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k))
    (B : ℕ) (hS : ∀ k, (S k).length ≤ B) :
    ∀ k, ((TM2.stepAux q v S).stk k).length ≤ B + radius q := by
  induction q generalizing v S B with
  | push k f q ih =>
    have hs : ∀ j, ((Function.update S k (f v :: S k)) j).length ≤ B+1 := by
      intro j
      by_cases hj : j = k
      · subst j; simpa only [Function.update_self, List.length_cons] using Nat.add_le_add_right (hS k) 1
      · rw [Function.update_of_ne hj]; exact (hS j).trans (Nat.le_succ B)
    intro j
    have hh := ih v _ (B+1) hs j
    simpa only [TM2.stepAux, radius, Nat.add_assoc, Nat.add_comm 1] using hh
  | peek k f q ih =>
    intro j
    exact (ih (f v (S k).head?) S B hS j).trans (by simp [radius])
  | pop k f q ih =>
    have hs : ∀ j, ((Function.update S k (S k).tail) j).length ≤ B := by
      intro j
      by_cases hj : j = k
      · subst j; simp only [Function.update_self, List.length_tail]; exact (Nat.sub_le _ _).trans (hS k)
      · rw [Function.update_of_ne hj]; exact hS j
    intro j
    exact (ih (f v (S k).head?) _ B hs j).trans (by simp [radius])
  | load f q ih => exact ih (f v) S B hS
  | branch f q r iq ir =>
    intro j
    cases hf : f v
    · simp only [TM2.stepAux, hf]
      exact (ir v S B hS j).trans (Nat.add_le_add_left (Nat.le_max_right _ _) B)
    · simp only [TM2.stepAux, hf]
      exact (iq v S B hS j).trans (Nat.add_le_add_left (Nat.le_max_left _ _) B)
  | goto f => simpa only [TM2.stepAux, radius, Nat.add_zero] using hS
  | halt => simpa only [TM2.stepAux, radius, Nat.add_zero] using hS

def cfgNext (M : Λ → TM2.Stmt Γ Λ σ) (c : TM2.Cfg Γ Λ σ) : TM2.Cfg Γ Λ σ :=
  match c.l with
  | none => c
  | some l => TM2.stepAux (M l) c.var c.stk

def wordNext (M : Λ → TM2.Stmt Γ Λ σ) (c : WordCfg Γ Λ σ) : WordCfg Γ Λ σ :=
  match c.label with
  | none => c
  | some l => wordStepAux (M l) c.var c.stk

theorem wordNext_ofCfg (M : Λ → TM2.Stmt Γ Λ σ) (c : TM2.Cfg Γ Λ σ) :
    wordNext M (WordCfg.ofCfg c) = WordCfg.ofCfg (cfgNext M c) := by
  cases c with
  | mk l v S =>
    cases l with
    | none => rfl
    | some l => exact wordStepAux_ofLists (M l) v S

noncomputable def programRadius [Fintype Λ] (M : Λ → TM2.Stmt Γ Λ σ) : ℕ :=
  Finset.univ.sup (fun l => radius (M l))

omit [DecidableEq K] in
theorem radius_le_programRadius [Fintype Λ] (M : Λ → TM2.Stmt Γ Λ σ) (l : Λ) :
    radius (M l) ≤ programRadius M := Finset.le_sup (f := fun l => radius (M l)) (Finset.mem_univ l)

theorem cfgNext_length [Fintype Λ] (M : Λ → TM2.Stmt Γ Λ σ)
    (c : TM2.Cfg Γ Λ σ) (B : ℕ) (hc : ∀ k, (c.stk k).length ≤ B) :
    ∀ k, ((cfgNext M c).stk k).length ≤ B + programRadius M := by
  cases c with
  | mk l v S =>
    cases l with
    | none => exact fun k => (hc k).trans (Nat.le_add_right _ _)
    | some l =>
      exact fun k => (stepAux_length (M l) v S B hc k).trans
        (Nat.add_le_add_left (radius_le_programRadius M l) B)

theorem cfgRun_length [Fintype Λ] (M : Λ → TM2.Stmt Γ Λ σ)
    (c : TM2.Cfg Γ Λ σ) (B t : ℕ) (hc : ∀ k, (c.stk k).length ≤ B) :
    ∀ k, (((cfgNext M)^[t] c).stk k).length ≤ B + t * programRadius M := by
  induction t with
  | zero => simpa using hc
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    have hh := cfgNext_length M ((cfgNext M)^[t] c) (B+t*programRadius M) ih
    simpa only [Nat.succ_mul, Nat.add_assoc] using hh

structure Window (Γ : K → Type) (Λ σ : Type) (S : ℕ) where
  label : Option Λ
  var : σ
  stk : ∀ k, Fin S → Option (Γ k)

def Window.words {S : ℕ} (c : Window Γ Λ σ S) : WordCfg Γ Λ σ :=
  ⟨c.label,c.var,fun k i => if h : i < S then c.stk k ⟨i,h⟩ else none⟩

def Window.ofCfg (S : ℕ) (c : TM2.Cfg Γ Λ σ) : Window Γ Λ σ S :=
  ⟨c.l,c.var,fun k i => (c.stk k)[i.val]?⟩

def Follows (M : Λ → TM2.Stmt Γ Λ σ) {S : ℕ} (a b : Window Γ Λ σ S) : Prop :=
  let next := wordNext M a.words
  b.label = next.label ∧ b.var = next.var ∧ ∀ k i, b.stk k i = next.stk k i.val

theorem window_follows_unique (M : Λ → TM2.Stmt Γ Λ σ) {S : ℕ}
    (a b c : Window Γ Λ σ S) (hb : Follows M a b) (hc : Follows M a c) : b = c := by
  cases b with
  | mk bl bv bs =>
    cases c with
    | mk cl cv cs =>
      obtain ⟨hl,hv,hs⟩ := hb
      obtain ⟨hl',hv',hs'⟩ := hc
      have hs'' : bs = cs := funext (fun k => funext (fun i => (hs k i).trans (hs' k i).symm))
      cases hl.trans hl'.symm
      cases hv.trans hv'.symm
      cases hs''
      rfl

theorem wordNext_local [Fintype Λ] (M : Λ → TM2.Stmt Γ Λ σ)
    (a b : WordCfg Γ Λ σ) (j : ℕ) (hl : a.label = b.label) (hv : a.var = b.var)
    (hS : AgreeCone (programRadius M) j a.stk b.stk) :
    (wordNext M a).label = (wordNext M b).label ∧
    (wordNext M a).var = (wordNext M b).var ∧
    ∀ k, (wordNext M a).stk k j = (wordNext M b).stk k j := by
  cases a with
  | mk al av aS =>
    cases b with
    | mk bl bv bS =>
      dsimp only at hl hv hS ⊢
      subst bl; subst bv
      cases al with
      | none => exact ⟨rfl,rfl,fun k => hS k j (Or.inr ⟨by omega,by omega⟩)⟩
      | some l =>
        exact wordStepAux_local (M l) av aS bS j
          (agreeCone_mono (radius_le_programRadius M l) hS)

end DirectedFeedback.CookLevin

namespace DirectedFeedback.CookLevin
open Turing
variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}

omit [DecidableEq K] in
theorem iterate_partial_none {α : Type} (f : α → Option α) (n : ℕ) :
    (fun p : Option α => p.bind f)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih]; rfl

omit [DecidableEq K] in

theorem iterate_partial_some {α : Type} (f : α → Option α) (n : ℕ) (a b : α)
    (h : (fun p : Option α => p.bind f)^[n] (some a) = some b) :
    (fun x => (f x).getD x)^[n] a = b := by
  induction n generalizing a with
  | zero => exact Option.some.inj h
  | succ n ih =>
    rw [Function.iterate_succ_apply] at h ⊢
    cases hf : f a with
    | none =>
      simp only [Option.bind_some, hf, iterate_partial_none] at h
      contradiction
    | some c =>
      simp only [Option.bind_some, hf] at h
      simpa only [hf, Option.getD_some] using ih c h

theorem cfgNext_eq_getD (M : Λ → TM2.Stmt Γ Λ σ) (c : TM2.Cfg Γ Λ σ) :
    cfgNext M c = (TM2.step M c).getD c := by
  cases c with
  | mk l v S => cases l <;> rfl

theorem output_run (tm : FinTM2) (input : List (tm.Γ tm.k₀))
    (output : List (tm.Γ tm.k₁)) (H : ℕ)
    (h : TM2OutputsInTime tm input (some output) H) :
    (cfgNext tm.m)^[H] (initList tm input) = haltList tm output := by
  rcases h with ⟨⟨n,hn⟩,hle⟩
  have hr := iterate_partial_some tm.step n (initList tm input) (haltList tm output) hn
  have he : (fun x => (tm.step x).getD x) = cfgNext tm.m := by
    funext c
    exact (cfgNext_eq_getD tm.m c).symm
  rw [he] at hr
  have hfix : cfgNext tm.m (haltList tm output) = haltList tm output := rfl
  have hmore := Function.iterate_add_apply (cfgNext tm.m) (H-n) n (initList tm input)
  unfold FinTM2.Cfg at *
  rw [Nat.sub_add_cancel hle,hr,Function.iterate_fixed hfix] at hmore
  exact hmore

end DirectedFeedback.CookLevin

namespace DirectedFeedback.CookLevin
open Turing
variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}

abbrev StackAtom (Γ : K → Type) := ∀ k, Option (Γ k)
abbrev Atom (Γ : K → Type) (Λ σ : Type) := (Option Λ × σ) × StackAtom Γ
abbrev Row (Γ : K → Type) (Λ σ : Type) (S : ℕ) := Fin (S+1) → Atom Γ Λ σ

def rowWindow {S : ℕ} (row : Row Γ Λ σ S) : Window Γ Λ σ S where
  label := (row 0).1.1
  var := (row 0).1.2
  stk := fun k j => (row j.succ).2 k

def windowRow {S : ℕ} (w : Window Γ Λ σ S) : Row Γ Λ σ S :=
  Fin.cases ((w.label,w.var), fun _ => none)
    (fun j => ((w.label,w.var), fun k => w.stk k j))

omit [DecidableEq K] in
@[simp] theorem rowWindow_windowRow {S : ℕ} (w : Window Γ Λ σ S) :
    rowWindow (windowRow w) = w := by
  cases w
  rfl

@[ext] structure LocalData (Γ : K → Type) (Λ σ : Type) (r : ℕ) where
  ctrl : Option Λ × σ
  head : Fin r → StackAtom Γ
  band : Fin (2*r+1) → StackAtom Γ

def LocalData.wordCfg {r : ℕ} (d : LocalData Γ Λ σ r) (j : ℕ) : WordCfg Γ Λ σ where
  label := d.ctrl.1
  var := d.ctrl.2
  stk := fun k i =>
    if hi : i < r then d.head ⟨i,hi⟩ k
    else if hb : j-r ≤ i ∧ i < j-r+(2*r+1) then d.band ⟨i-(j-r),by omega⟩ k
    else none

def localData (r j : ℕ) (w : WordCfg Γ Λ σ) : LocalData Γ Λ σ r where
  ctrl := (w.label,w.var)
  head := fun i k => w.stk k i.val
  band := fun i k => w.stk k (j-r+i.val)

omit [DecidableEq K] in
theorem localData_agree (r j : ℕ) (w : WordCfg Γ Λ σ) :
    AgreeCone r j (localData r j w |>.wordCfg j).stk w.stk := by
  intro k i hi
  dsimp [LocalData.wordCfg,localData]
  split_ifs with hh hb
  · rfl
  · congr 1
    omega
  · exfalso
    rcases hi with hi | ⟨h₁,h₂⟩
    · exact hh hi
    · apply hb
      omega

theorem localData_next [Fintype Λ] (M : Λ → TM2.Stmt Γ Λ σ)
    (j : ℕ) (w : WordCfg Γ Λ σ) :
    (wordNext M (localData (programRadius M) j w |>.wordCfg j)).label = (wordNext M w).label ∧
    (wordNext M (localData (programRadius M) j w |>.wordCfg j)).var = (wordNext M w).var ∧
    ∀ k, (wordNext M (localData (programRadius M) j w |>.wordCfg j)).stk k j =
      (wordNext M w).stk k j :=
  wordNext_local M _ _ j rfl rfl (localData_agree _ _ _)

abbrev StepSlot (r : ℕ) := Fin r ⊕ (Fin (2*r+1) ⊕ Fin 3)
abbrev TracePosition (H S : ℕ) := Fin (H+1) × Fin (S+1)

def cellAddress (S i : ℕ) : Fin (S+1) := if h : i < S then ⟨i+1,by omega⟩ else 0

def stepQuery {H S r : ℕ} (t : Fin H) (j : Fin (S+1)) :
    StepSlot r → TracePosition H S
  | .inl i => (t.castSucc,cellAddress S i.val)
  | .inr (.inl i) => (t.castSucc,cellAddress S (j.val-r+i.val))
  | .inr (.inr i) => if i.val = 0 then (t.castSucc,0)
    else if i.val = 1 then (t.succ,0) else (t.succ,cellAddress S j.val)

def dataOfQueries {S r : ℕ} (j : Fin (S+1))
    (a : StepSlot r → Atom Γ Λ σ) : LocalData Γ Λ σ r where
  ctrl := (a (.inr (.inr 0))).1
  head := fun i k => if i.val < S then (a (.inl i)).2 k else none
  band := fun i k => if j.val-r+i.val < S then (a (.inr (.inl i))).2 k else none

noncomputable def stepAccepts [Fintype Λ] (M : Λ → TM2.Stmt Γ Λ σ)
    {S : ℕ} (j : Fin (S+1)) (a : StepSlot (programRadius M) → Atom Γ Λ σ) : Bool := by
  classical
  let w := wordNext M ((dataOfQueries j a).wordCfg j.val)
  exact decide ((a (.inr (.inr 1))).1 = (w.label,w.var) ∧
    (j.val < S → ∀ k, (a (.inr (.inr 2))).2 k = w.stk k j.val))

omit [DecidableEq K] in
theorem dataOfQueries_eq {H S r : ℕ} (A : TracePosition H S → Atom Γ Λ σ)
    (t : Fin H) (j : Fin (S+1)) :
    dataOfQueries j (A ∘ stepQuery (r:=r) t j) =
      localData r j.val (rowWindow (fun p => A (t.castSucc,p))).words := by
  apply LocalData.ext
  · rfl
  · funext i k
    dsimp [dataOfQueries,localData,Window.words,rowWindow,stepQuery,cellAddress]
    split_ifs with hi <;> rfl
  · funext i k
    dsimp [dataOfQueries,localData,Window.words,rowWindow,stepQuery,cellAddress]
    split_ifs with hi <;> rfl

theorem stepAccepts_iff [Fintype Λ] (M : Λ → TM2.Stmt Γ Λ σ)
    {H S : ℕ} (A : TracePosition H S → Atom Γ Λ σ)
    (t : Fin H) (j : Fin (S+1)) :
    stepAccepts M j (A ∘ stepQuery t j) = true ↔
      let old := rowWindow (fun p => A (t.castSucc,p))
      let next := rowWindow (fun p => A (t.succ,p))
      next.label = (wordNext M old.words).label ∧
      next.var = (wordNext M old.words).var ∧
      (j.val < S → ∀ k, (A (t.succ,cellAddress S j.val)).2 k =
         (wordNext M old.words).stk k j.val) := by
  classical
  dsimp [stepAccepts]
  rw [decide_eq_true_eq,dataOfQueries_eq]
  have h := localData_next M j.val (rowWindow (fun p => A (t.castSucc,p))).words
  simp only [h.1,h.2.1,h.2.2,stepQuery]
  norm_num [rowWindow,Prod.ext_iff,and_assoc]

theorem stepAccepts_all_iff [Fintype Λ] (M : Λ → TM2.Stmt Γ Λ σ)
    {H S : ℕ} (A : TracePosition H S → Atom Γ Λ σ) (t : Fin H) :
    (∀ j, stepAccepts M j (A ∘ stepQuery t j) = true) ↔
      Follows M (rowWindow (fun p => A (t.castSucc,p)))
        (rowWindow (fun p => A (t.succ,p))) := by
  simp only [stepAccepts_iff]
  constructor
  · intro h
    refine ⟨(h 0).1,(h 0).2.1,?_⟩
    intro k j
    have hh := (h j.castSucc).2.2 j.isLt k
    simpa only [cellAddress,Fin.val_castSucc,j.isLt,↓reduceDIte,rowWindow,Fin.succ] using hh
  · rintro ⟨hl,hv,hs⟩ j
    refine ⟨hl,hv,?_⟩
    intro hj k
    simpa only [cellAddress,hj,↓reduceDIte,rowWindow,Fin.succ,Nat.add_comm] using hs k ⟨j.val,hj⟩

end DirectedFeedback.CookLevin

namespace DirectedFeedback.CookLevin

def prefixList {α : Type} : ℕ → (ℕ → Option α) → List α
  | 0, _ => []
  | n+1,w => match w 0 with
    | none => []
    | some a => a :: prefixList n (fun i => w (i+1))

theorem prefixList_length {α : Type} (n : ℕ) (w : ℕ → Option α) :
    (prefixList n w).length ≤ n := by
  induction n generalizing w with
  | zero => simp [prefixList]
  | succ n ih =>
    dsimp [prefixList]
    cases h : w 0 with
    | none => simp
    | some a => simpa using Nat.succ_le_succ (ih (fun i => w (i+1)))

def NoHoles {α : Type} (w : ℕ → Option α) : Prop :=
  ∀ i, w i = none → w (i+1) = none

theorem NoHoles.tail {α : Type} {w : ℕ → Option α} (h : NoHoles w) :
    NoHoles (fun i => w (i+1)) := fun i => h (i+1)

theorem NoHoles.propagate {α : Type} {w : ℕ → Option α} (h : NoHoles w)
    (i j : ℕ) (hij : i ≤ j) (hi : w i = none) : w j = none := by
  induction j, hij using Nat.le_induction with
  | base => exact hi
  | succ j hj ih => exact h j ih

theorem prefixList_getElem? {α : Type} (n : ℕ) (w : ℕ → Option α)
    (h : NoHoles w) (i : ℕ) (hi : i < n) :
    (prefixList n w)[i]? = w i := by
  induction n generalizing w i with
  | zero => omega
  | succ n ih =>
    cases h0 : w 0 with
    | none =>
      rw [prefixList,h0]
      exact (h.propagate 0 i (Nat.zero_le _) h0).symm
    | some a =>
      rw [prefixList,h0]
      cases i with
      | zero => simpa using h0.symm
      | succ i =>
        simpa using ih (fun i => w (i+1)) h.tail i (by omega)

theorem prefixList_getElem?_all {α : Type} (n : ℕ) (w : ℕ → Option α)
    (h : NoHoles w) (hbound : ∀ i, n ≤ i → w i = none) (i : ℕ) :
    (prefixList n w)[i]? = w i := by
  by_cases hi : i < n
  · exact prefixList_getElem? n w h i hi
  · rw [List.getElem?_eq_none ((prefixList_length n w).trans (by omega)),hbound i (by omega)]

theorem list_getElem?_noHoles {α : Type} (l : List α) : NoHoles (fun i => l[i]?) := by
  intro i hi
  exact List.getElem?_eq_none (by have := List.getElem?_eq_none_iff.mp hi; omega)

theorem reconstruct_suffix {α : Type} (pref : List α) (C : ℕ) (w : ℕ → Option α)
    (hp : ∀ i, i < pref.length → w i = pref[i]?)
    (ht : ∀ i, pref.length + C ≤ i → w i = none)
    (hn : ∀ i, pref.length ≤ i → w i = none → w (i+1) = none) :
    ∃ certificate : List α, certificate.length ≤ C ∧
      ∀ i, (pref ++ certificate)[i]? = w i := by
  let suffix := fun i => w (pref.length+i)
  have hs : NoHoles suffix := by
    intro i hi
    simpa only [suffix,Nat.add_assoc] using hn (pref.length+i) (by omega) hi
  refine ⟨prefixList C suffix,prefixList_length C suffix,?_⟩
  intro i
  by_cases hi : i < pref.length
  · rw [List.getElem?_append_left hi,hp i hi]
  · have hi' : pref.length ≤ i := by omega
    rw [List.getElem?_append_right hi']
    rw [prefixList_getElem?_all C suffix hs]
    · dsimp [suffix]
      congr 1
      omega
    · intro j hj
      exact ht (pref.length+j) (by omega)

end DirectedFeedback.CookLevin

namespace DirectedFeedback.CookLevin
open Turing

def InitialConditions (tm : FinTM2) (pref : List (tm.Γ tm.k₀)) (C : ℕ)
    (w : WordCfg tm.Γ tm.Λ tm.σ) : Prop :=
  w.label = some tm.main ∧ w.var = tm.initialState ∧
  (∀ k, k ≠ tm.k₀ → ∀ i, w.stk k i = none) ∧
  (∀ i, i < pref.length → w.stk tm.k₀ i = pref[i]?) ∧
  (∀ i, pref.length+C ≤ i → w.stk tm.k₀ i = none) ∧
  (∀ i, pref.length ≤ i → w.stk tm.k₀ i = none → w.stk tm.k₀ (i+1) = none)

def initialPredicate (tm : FinTM2) (pref : List (tm.Γ tm.k₀)) (C i : ℕ)
    (ctrl : Option tm.Λ × tm.σ) (current next : StackAtom tm.Γ) : Prop :=
  ctrl = (some tm.main,tm.initialState) ∧
  (∀ k, k ≠ tm.k₀ → current k = none) ∧
  (i < pref.length → current tm.k₀ = pref[i]?) ∧
  (pref.length+C ≤ i → current tm.k₀ = none) ∧
  (pref.length ≤ i → current tm.k₀ = none → next tm.k₀ = none)

def initialQuery {H S : ℕ} (j : Fin (S+1)) : Fin 3 → TracePosition H S := fun i =>
  if i.val = 0 then (0,0) else if i.val = 1 then (0,cellAddress S j.val)
  else (0,cellAddress S (j.val+1))

noncomputable def initialAccepts (tm : FinTM2) (pref : List (tm.Γ tm.k₀)) (C : ℕ)
    {S : ℕ} (j : Fin (S+1)) (a : Fin 3 → Atom tm.Γ tm.Λ tm.σ) : Bool := by
  classical
  exact decide (initialPredicate tm pref C j.val (a 0).1
    (fun k => if j.val < S then (a 1).2 k else none)
    (fun k => if j.val+1 < S then (a 2).2 k else none))

theorem row_cell_query (tm : FinTM2) {H S : ℕ}
    (A : TracePosition H S → Atom tm.Γ tm.Λ tm.σ) (t : Fin (H+1)) (i : ℕ) :
    (fun k => if i < S then (A (t,cellAddress S i)).2 k else none) =
      (fun k => (rowWindow (fun p => A (t,p))).words.stk k i) := by
  funext k
  dsimp [cellAddress,rowWindow,Window.words]
  split_ifs with hi <;> rfl

theorem initialAccepts_iff (tm : FinTM2) (pref : List (tm.Γ tm.k₀)) (C : ℕ)
    {H S : ℕ} (A : TracePosition H S → Atom tm.Γ tm.Λ tm.σ) (j : Fin (S+1)) :
    initialAccepts tm pref C j (A ∘ initialQuery j) = true ↔
      let w := (rowWindow (fun p => A (0,p))).words
      initialPredicate tm pref C j.val (w.label,w.var)
        (fun k => w.stk k j.val) (fun k => w.stk k (j.val+1)) := by
  classical
  dsimp [initialAccepts]
  rw [decide_eq_true_eq]
  change initialPredicate tm pref C j.val (A (0,0)).1
    (fun k => if j.val < S then (A (0,cellAddress S j.val)).2 k else none)
    (fun k => if j.val+1 < S then (A (0,cellAddress S (j.val+1))).2 k else none) ↔ _
  rw [row_cell_query tm A 0 j.val,row_cell_query tm A 0 (j.val+1)]
  rfl

theorem initialAccepts_all_iff (tm : FinTM2) (pref : List (tm.Γ tm.k₀)) (C : ℕ)
    {H S : ℕ} (hS : pref.length+C ≤ S)
    (A : TracePosition H S → Atom tm.Γ tm.Λ tm.σ) :
    (∀ j, initialAccepts tm pref C j (A ∘ initialQuery j) = true) ↔
      InitialConditions tm pref C (rowWindow (fun p => A (0,p))).words := by
  simp only [initialAccepts_iff]
  constructor
  · intro h
    have hc := (h 0).1
    refine ⟨(congrArg Prod.fst hc),(congrArg Prod.snd hc),?_,?_,?_,?_⟩
    · intro k hk i
      by_cases hi : i < S
      · exact (h ⟨i,by omega⟩).2.1 k hk
      · simp [Window.words,hi]
    · intro i hi
      exact (h ⟨i,by omega⟩).2.2.1 hi
    · intro i hi
      by_cases hiS : i < S
      · exact (h ⟨i,by omega⟩).2.2.2.1 hi
      · simp [Window.words,hiS]
    · intro i hi hnone
      by_cases hiS : i < S
      · exact (h ⟨i,by omega⟩).2.2.2.2 hi hnone
      · simp [Window.words,show ¬i+1 < S by omega]
  · rintro ⟨hl,hv,hk,hp,ht,hn⟩ j
    exact ⟨Prod.ext hl hv,fun k h => hk k h j.val,hp j.val,ht j.val,hn j.val⟩

theorem initial_reconstruct (tm : FinTM2) (pref : List (tm.Γ tm.k₀)) (C S : ℕ)
    (w : Window tm.Γ tm.Λ tm.σ S) (h : InitialConditions tm pref C w.words) :
    ∃ certificate : List (tm.Γ tm.k₀), certificate.length ≤ C ∧
      w = Window.ofCfg S (initList tm (pref ++ certificate)) := by
  obtain ⟨hl,hv,hk,hp,ht,hn⟩ := h
  obtain ⟨certificate,hC,he⟩ := reconstruct_suffix pref C (w.words.stk tm.k₀) hp ht hn
  refine ⟨certificate,hC,?_⟩
  cases w with
  | mk label var stk =>
    dsimp [Window.words] at hl hv
    subst label; subst var
    congr 1
    funext k i
    by_cases hkk : k = tm.k₀
    · subst k
      have hh := he i.val
      simpa [Window.words,Window.ofCfg,initList,i.isLt] using hh.symm
    · have hh := hk k hkk i.val
      simpa [Window.words,Window.ofCfg,initList,i.isLt,hkk] using hh

end DirectedFeedback.CookLevin

namespace DirectedFeedback.CookLevin

structure LocalCSP (Alphabet Variable Event Slot : Type) where
  query : Event → Slot → Variable
  accepts : Event → (Slot → Alphabet) → Bool

def LocalCSP.Satisfiable {A I E J : Type} (C : LocalCSP A I E J) : Prop :=
  ∃ assignment : I → A, ∀ e, C.accepts e (assignment ∘ C.query e) = true

structure FiniteCodec (A : Type) where
  width : ℕ
  encode : A → (Fin width → Bool)
  decode : (Fin width → Bool) → A
  decode_encode : ∀ a, decode (encode a) = a

noncomputable def oneHotCodec (A : Type) [Fintype A] [Nonempty A] : FiniteCodec A := by
  classical
  let enc : A → (Fin (Fintype.card A) → Bool) := fun a i =>
    decide ((Fintype.equivFin A).symm i = a)
  have hinj : Function.Injective enc := by
    intro a b hab
    have he := congrFun hab ((Fintype.equivFin A) a)
    simpa [enc] using he
  exact {
    width := Fintype.card A
    encode := enc
    decode := fun bits => if h : ∃ a, enc a = bits then h.choose else Classical.choice inferInstance
    decode_encode := fun a => by
      split_ifs with h
      · exact hinj h.choose_spec
      · exact False.elim (h ⟨a,rfl⟩) }

def LocalCSP.booleanize {A I E J : Type} (C : LocalCSP A I E J) (codec : FiniteCodec A) :
    LocalCSP Bool (I × Fin codec.width) E (J × Fin codec.width) where
  query := fun e j => (C.query e j.1,j.2)
  accepts := fun e pattern => C.accepts e (fun j => codec.decode (fun b => pattern (j,b)))

theorem LocalCSP.booleanize_satisfiable_iff {A I E J : Type}
    (C : LocalCSP A I E J) (codec : FiniteCodec A) :
    (C.booleanize codec).Satisfiable ↔ C.Satisfiable := by
  constructor
  · rintro ⟨B,hB⟩
    exact ⟨fun i => codec.decode (fun b => B (i,b)),hB⟩
  · rintro ⟨A,hA⟩
    refine ⟨fun i => codec.encode (A i.1) i.2,?_⟩
    intro e
    simpa only [booleanize,Function.comp_def,codec.decode_encode] using hA e

end DirectedFeedback.CookLevin

namespace DirectedFeedback.CookLevin
open Turing
attribute [local instance] FinTM2.ΛFin
abbrev TableauEvent (H S : ℕ) := Fin (S+1) ⊕ ((Fin H × Fin (S+1)) ⊕ Unit)
abbrev TableauSlot (tm : FinTM2) := Fin 3 ⊕ (StepSlot (programRadius tm.m) ⊕ Unit)

noncomputable def tableauQuery (tm : FinTM2) {H S : ℕ} :
    TableauEvent H S → TableauSlot tm → TracePosition H S
  | .inl j, .inl i => initialQuery j i
  | .inr (.inl (t,j)), .inr (.inl i) => stepQuery t j i
  | .inr (.inr _), .inr (.inr _) => (Fin.last H,cellAddress S 0)
  | _, _ => (0,0)

noncomputable def tableau (tm : FinTM2) (pref : List (tm.Γ tm.k₀)) (C H S : ℕ)
    (out : tm.Γ tm.k₁) : LocalCSP (Atom tm.Γ tm.Λ tm.σ)
      (TracePosition H S) (TableauEvent H S) (TableauSlot tm) where
  query := tableauQuery tm
  accepts := fun e a => match e with
    | .inl j => initialAccepts tm pref C j (a ∘ Sum.inl)
    | .inr (.inl (_,j)) => stepAccepts tm.m j (a ∘ Sum.inr ∘ Sum.inl)
    | .inr (.inr _) => by
      classical
      exact decide ((a (.inr (.inr ()))).2 tm.k₁ = some out)

end DirectedFeedback.CookLevin

namespace DirectedFeedback.CookLevin
open Turing
attribute [local instance] FinTM2.ΛFin

theorem natPoly_mono (p : Polynomial ℕ) {n m : ℕ} (h : n ≤ m) : p.eval n ≤ p.eval m := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [Polynomial.eval_add] using Nat.add_le_add hp hq
  | monomial k a => simpa only [Polynomial.eval_monomial] using
      Nat.mul_le_mul_left a (Nat.pow_le_pow_left h k)

namespace NPTableau

def certBound (V : NPVerifier) (n : ℕ) : ℕ := V.witnessBound.eval n
def inputBound (V : NPVerifier) (n : ℕ) : ℕ := 2*n+certBound V n+1
def horizon (V : NPVerifier) (n : ℕ) : ℕ := V.computation.time.eval (inputBound V n)
noncomputable def capacity (V : NPVerifier) (n : ℕ) : ℕ :=
  inputBound V n + horizon V n * programRadius V.computation.tm.m

def fixedPrefix (V : NPVerifier) (input : List Bool) : List (V.computation.tm.Γ V.computation.tm.k₀) :=
  (natBits input.length ++ input).map V.computation.inputAlphabet.invFun

theorem fixedPrefix_length (V : NPVerifier) (input : List Bool) :
    (fixedPrefix V input).length = 2*input.length+1 := by simp [fixedPrefix,natBits]; omega

noncomputable def tests (V : NPVerifier) (input : List Bool) :=
  tableau V.computation.tm (fixedPrefix V input) (certBound V input.length)
    (horizon V input.length) (capacity V input.length) (V.computation.outputAlphabet.invFun true)

theorem input_length_bound (V : NPVerifier) (input cert : List Bool)
    (hc : cert.length ≤ certBound V input.length) :
    (pairBits (input,cert)).length ≤ inputBound V input.length := by
  simp only [pairBits,natBits,List.length_append,List.length_replicate,List.length_singleton]
  unfold inputBound
  omega

theorem run_horizon (V : NPVerifier) (input : List Bool)
    (cert : List (V.computation.tm.Γ V.computation.tm.k₀))
    (hc : cert.length ≤ certBound V input.length) :
    ((cfgNext V.computation.tm.m)^[horizon V input.length]
      (initList V.computation.tm (fixedPrefix V input ++ cert))) =
    haltList V.computation.tm
      [V.computation.outputAlphabet.invFun (V.verify (input,cert.map V.computation.inputAlphabet))] := by
  let b := cert.map V.computation.inputAlphabet
  have hlen : b.length ≤ certBound V input.length := by simpa [b] using hc
  have hout := V.computation.outputsFun (input,b)
  have hmono := natPoly_mono V.computation.time (input_length_bound V input b hlen)
  have hr := output_run V.computation.tm
    ((pairBits (input,b)).map V.computation.inputAlphabet.invFun)
    (([V.verify (input,b)]).map V.computation.outputAlphabet.invFun)
    (horizon V input.length) ⟨hout.toEvalsTo,hout.steps_le_m.trans hmono⟩
  simpa [pairBits,fixedPrefix,b,List.map_append,List.map_map,Function.comp_def] using hr

theorem atom_finite (V : NPVerifier) : Finite (Atom V.computation.tm.Γ
    V.computation.tm.Λ V.computation.tm.σ) := by
  let tm := V.computation.tm
  let _ : Fintype tm.K := tm.kFin
  let _ : Fintype tm.Λ := tm.ΛFin
  let _ : Fintype tm.σ := tm.σFin
  have : ∀ k, Finite (tm.Γ k) := V.finiteAlphabet
  change Finite (Atom tm.Γ tm.Λ tm.σ)
  infer_instance

theorem atom_nonempty (V : NPVerifier) : Nonempty (Atom V.computation.tm.Γ
    V.computation.tm.Λ V.computation.tm.σ) :=
  ⟨((none,V.computation.tm.initialState),fun _ => none)⟩

end NPTableau
end DirectedFeedback.CookLevin

end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_UnweightedIntegrated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace DirectedFeedback

def CyclicWalk {V : Type*} (R : V → V → Prop) {n : ℕ}
    (f : Fin (n + 1) → V) : Prop := ∀ i, R (f i) (f (i + 1))

theorem cyclicWalk_contains_cycle {V : Type*} (R : V → V → Prop)
    (n : ℕ) (f : Fin (n + 1) → V) (hf : CyclicWalk R f) :
    ∃ (k : ℕ) (g : Fin (k + 1) → V),
      Function.Injective g ∧ CyclicWalk R g ∧ Set.range g ⊆ Set.range f := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hinj : Function.Injective f
    · exact ⟨n, f, hinj, hf, Set.Subset.rfl⟩
    · obtain ⟨a, b, hab, hne⟩ := Function.not_injective_iff.mp hinj
      have hneval : a.val ≠ b.val := fun h => hne (Fin.ext h)
      have hex : ∃ i j : Fin (n + 1), i.val < j.val ∧ f i = f j := by
        rcases lt_or_gt_of_ne hneval with hlt | hgt
        · exact ⟨a, b, hlt, hab⟩
        · exact ⟨b, a, hgt, hab.symm⟩
      obtain ⟨i, j, hij, heq⟩ := hex
      let k := j.val - i.val - 1
      have hklen : k + 1 = j.val - i.val := by dsimp [k]; omega
      have hkn : k < n := by dsimp [k]; omega
      let idx : Fin (k + 1) → Fin (n + 1) :=
        fun t => ⟨i.val + t.val, by have := t.isLt; have := j.isLt; omega⟩
      let g := f ∘ idx
      have hg : CyclicWalk R g := by
        intro t
        by_cases ht : t.val + 1 < k + 1
        · have hnext : idx (t + 1) = idx t + 1 := by
            apply Fin.ext
            have hsmall : (idx t).val + 1 < n + 1 := by
              dsimp [idx]; have := j.isLt; omega
            change i.val + (t + 1).val = (idx t + 1).val
            rw [Fin.val_add_one_of_lt' ht, Fin.val_add_one_of_lt' hsmall]
            dsimp [idx]
            omega
          simpa only [g, Function.comp_apply, hnext] using hf (idx t)
        · have htlast : t.val = k := by omega
          have hwrap : t + 1 = 0 := by
            apply Fin.ext
            simp [Fin.val_add, htlast]
          have hnext : idx t + 1 = j := by
            apply Fin.ext
            have hsmall : (idx t).val + 1 < n + 1 := by
              dsimp [idx]; have := j.isLt; omega
            rw [Fin.val_add_one_of_lt' hsmall]
            dsimp [idx]
            omega
          have hzero : idx 0 = i := by ext; simp [idx]
          dsimp [g]
          rw [hwrap, hzero, heq]
          simpa only [hnext] using hf (idx t)
      obtain ⟨q, c, hcinj, hc, hcrange⟩ := ih k hkn g hg
      refine ⟨q, c, hcinj, hc, ?_⟩
      rintro v ⟨t, rfl⟩
      obtain ⟨u, hu⟩ := hcrange ⟨t, rfl⟩
      exact ⟨idx u, hu⟩

def FeedbackR {V : Type*} (R : V → V → Prop) (F : Finset V) : Prop :=
  ∀ (n : ℕ) (f : Fin (n + 1) → V),
    Function.Injective f → CyclicWalk R f → ∃ i, f i ∈ F

theorem feedback_hits_walk {V : Type*} (R : V → V → Prop) (F : Finset V)
    (hF : FeedbackR R F) (n : ℕ) (f : Fin (n + 1) → V)
    (hf : CyclicWalk R f) : ∃ i, f i ∈ F := by
  obtain ⟨k, g, hginj, hg, hsub⟩ := cyclicWalk_contains_cycle R n f hf
  obtain ⟨i, hi⟩ := hF k g hginj hg
  obtain ⟨j, hj⟩ := hsub ⟨i, rfl⟩
  exact ⟨j, hj ▸ hi⟩

end DirectedFeedback

noncomputable section
open scoped BigOperators

namespace DirectedFeedback.RankGraph
variable {U V X Y : Type} {T N L : ℕ}
variable (ψ : Fin L → Fin N)

def usable (a c h : Fin L) : Prop :=
  1 ≤ a.val ∧ a < c ∧ 4 ≤ c.val ∧ c.val + 6 ≤ L ∧ c.val + 2 ≤ h.val

end DirectedFeedback.RankGraph

end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_CellCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical

noncomputable section
open scoped Classical

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Prefix
variable {S X : Type*} {k n : ℕ}

theorem block_prefix {a b r q : ℕ} (hb : b < n) (hq : q ≤ n) :
    n*a+b < n*r+q ↔ a < r ∨ a = r ∧ b < q := by
  constructor
  · intro h
    by_cases har : a < r
    · exact Or.inl har
    · have har' : r ≤ a := by omega
      by_cases hra : r < a
      · have hh := Nat.mul_le_mul_left n hra
        simp only [Nat.mul_succ] at hh
        omega
      · have he : a = r := by omega
        subst a
        exact Or.inr ⟨rfl, by omega⟩
  · rintro (ha | ⟨rfl, hbq⟩)
    · have hh := Nat.mul_le_mul_left n ha
      simp only [Nat.mul_succ] at hh
      omega
    · omega

end DirectedFeedback.Prefix

noncomputable section
open scoped BigOperators

namespace DirectedFeedback.Probability

def andBit {k : ℕ} (x : Fin k → Bool) : Bool := decide (∀ a, x a = true)

def blockAnd {I : Type*} {k : ℕ} (x : I → Fin k → Bool) : I → Bool := fun i => andBit (x i)

end DirectedFeedback.Probability

noncomputable section
open scoped BigOperators

namespace DirectedFeedback.Pivotal
open scoped BigOperators
variable {I : Type*} [Fintype I] [DecidableEq I]

def atom (p : ℝ) (b : Bool) : ℝ := if b then p else 1 - p

theorem atom_hasDerivAt (b : Bool) (p : ℝ) :
    HasDerivAt (fun q => atom q b) (if b then 1 else -1) p := by
  cases b
  · convert (hasDerivAt_id p).const_sub (1 : ℝ) using 1 <;> rfl
  · exact hasDerivAt_id p

end DirectedFeedback.Pivotal
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_Point
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators

noncomputable section
open scoped Classical BigOperators

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Pivotal
variable {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ}

def orderHit {J : Type*} [Fintype J] (event : (J → Bool) → Bool)
    (e : J ≃ Fin (Fintype.card J)) : Bool :=
  decide (∃ r ≤ Fintype.card J, event (fun x => decide ((e x).val < r)) = true)

def omittedHit (j : I) (event : ({i : I // i ≠ j} → Bool) → Bool)
    (e : I ≃ Fin (Fintype.card {i : I // i ≠ j} + 1)) : Bool :=
  decide (∃ r ≤ Fintype.card {i : I // i ≠ j} + 1,
    event (fun x => decide ((e x).val < r)) = true)

theorem succAbove_cut_forward (r : Fin (n+1)) (q : ℕ) (x : Fin n) :
    (r.succAbove x).val < (if q ≤ r.val then q else q+1) ↔ x.val < q := by
  unfold Fin.succAbove
  split_ifs <;> simp_all only [Fin.val_castSucc, Fin.val_succ, Fin.lt_def] <;> omega

theorem succAbove_cut_backward (r : Fin (n+1)) (q : ℕ) (x : Fin n) :
    (r.succAbove x).val < q ↔ x.val < (if q ≤ r.val then q else q-1) := by
  unfold Fin.succAbove
  split_ifs <;> simp_all only [Fin.val_castSucc, Fin.val_succ, Fin.lt_def] <;> omega

def permutationOrder (J : Type*) [Fintype J] : Equiv.Perm J ≃ (J ≃ Fin (Fintype.card J)) where
  toFun σ := σ.symm.trans (Fintype.equivFin J)
  invFun e := (e.trans (Fintype.equivFin J).symm).symm
  left_inv σ := by ext j; simp
  right_inv e := by ext j; simp

instance nonemptyOrder (J : Type*) [Fintype J] : Nonempty (J ≃ Fin (Fintype.card J)) :=
  ⟨Fintype.equivFin J⟩

end DirectedFeedback.Pivotal

noncomputable section
open scoped Classical BigOperators

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.SourceProbability.FiniteDistribution
variable {I : Type*} [Fintype I]

def splitSnoc (T : ℕ) : (Fin (T+1) → I) ≃ ((Fin T → I) × I) where
  toFun a := (Fin.init a, a (Fin.last T))
  invFun a := Fin.snoc a.1 a.2
  left_inv a := by funext i; exact Fin.lastCases (by simp) (fun j => by simp [Fin.init]) i
  right_inv a := by rcases a with ⟨a,x⟩; simp

end DirectedFeedback.SourceProbability.FiniteDistribution

noncomputable section
open scoped Classical BigOperators

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.SourceProbability.FiniteDistribution
variable {I B C D : Type*} [Fintype I] [Fintype B]

def Uses (S : Finset I) (f : (I → B) → C) : Prop :=
  ∀ x y, (∀ i ∈ S, x i = y i) → f x = f y

def splice (S : Finset I) (x y : I → B) : I → B :=
  fun i => if i ∈ S then x i else y i

end DirectedFeedback.SourceProbability.FiniteDistribution

end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_Bias
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
open DirectedFeedback.SourceProbability
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators

noncomputable section
open scoped Classical BigOperators

noncomputable section
open scoped Classical BigOperators

noncomputable section
open scoped Classical BigOperators

noncomputable section
open scoped Classical

noncomputable section
open scoped Classical BigOperators

noncomputable section
open scoped Classical BigOperators

noncomputable section
open scoped Classical BigOperators

noncomputable section
open scoped Classical BigOperators

namespace DirectedFeedback.Pivotal
open DirectedFeedback.SourceProbability FiniteDistribution
variable {I Ω : Type*} [Fintype I] [DecidableEq I] [Nonempty I] [Fintype Ω]

omit [Fintype I] [DecidableEq I] [Nonempty I] in

theorem subset_function_properties (f : Set I → Bool)
    (hm : Monotone f) (h0 : f ∅ = false) (h1 : f Set.univ = true) :
    Monotone (fun b : I → Bool => f {i | b i = true}) ∧
      (fun b : I → Bool => f {i | b i = true}) (fun _ => false) = false ∧
      (fun b : I → Bool => f {i | b i = true}) (fun _ => true) = true := by
  refine ⟨?_, by simpa using h0, by simpa using h1⟩
  intro a b hab
  apply hm
  intro i hi
  exact Bool.le_iff_imp.mp (hab i) hi

end DirectedFeedback.Pivotal

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_RoundBoolean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
open DirectedFeedback.SourceProbability
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
namespace DirectedFeedback.Junta
open scoped BigOperators
open Finset

def cubeEquiv {I J : Type*} (e : I ≃ J) : (I → Bool) ≃ (J → Bool) where
  toFun x := fun j => x (e.symm j)
  invFun y := fun i => y (e i)
  left_inv x := by funext i; simp
  right_inv y := by funext j; simp

def DependsOn {I : Type*} (J : Finset I) (f : (I → Bool) → ℝ) : Prop :=
  ∀ x y, (∀ i ∈ J, x i = y i) → f x = f y

def cubeInfluence {I : Type*} [Fintype I] [DecidableEq I]
    (f : (I → Bool) → ℝ) (i : I) : ℝ :=
  𝔼 x, (f x - f (Function.update x i (!x i))) ^ 2

def cubeError {I : Type*} [Fintype I] [DecidableEq I] (f g : (I → Bool) → ℝ) : ℝ :=
  𝔼 x, if f x = g x then 0 else 1

end DirectedFeedback.Junta

namespace DirectedFeedback.Junta
open DirectedFeedback.SourceProbability FiniteDistribution
open DirectedFeedback.Probability

variable {I : Type} [Fintype I] [DecidableEq I]

def merge (J : Finset I) (x y : I → Bool) : I → Bool :=
  fun i => if i ∈ J then x i else y i

def swapOutside (J : Finset I) : ((I → Bool) × (I → Bool)) ≃ ((I → Bool) × (I → Bool)) where
  toFun p := (merge J p.1 p.2, merge J p.2 p.1)
  invFun p := (merge J p.1 p.2, merge J p.2 p.1)
  left_inv p := by ext i <;> by_cases hi : i ∈ J <;> simp [merge, hi]
  right_inv p := by ext i <;> by_cases hi : i ∈ J <;> simp [merge, hi]

def disagree (a b : ℝ) : ℝ := if a = b then 0 else 1

end DirectedFeedback.Junta

namespace DirectedFeedback.Junta
open DirectedFeedback.SourceProbability FiniteDistribution
open DirectedFeedback.Probability
variable {I : Type} [Fintype I] [DecidableEq I]

def flatAnd {k : ℕ} (x : I × Fin k → Bool) : I → Bool :=
  fun i => andBit (fun a => x (i, a))

end DirectedFeedback.Junta

noncomputable section
open scoped Classical BigOperators

noncomputable section
open scoped Classical BigOperators

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Coupling
open DirectedFeedback.SourceProbability FiniteDistribution
variable {X Y : Type*} [Fintype X] [Fintype Y]

theorem product_pattern_lipschitz {a b c d ε δ : ℝ}
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hb1 : b ≤ 1) (hε : |a-c| ≤ ε) (hδ : |b-d| ≤ δ) :
    |a*(1-b)-c*(1-d)| ≤ ε + δ := by
  have hε0 : 0 ≤ ε := (abs_nonneg _).trans hε
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans hδ
  calc
    _ = |(a-c)*(1-b) + c*(d-b)| := by congr 1; ring
    _ ≤ |a-c| *|1-b| + |c| *|d-b| := by simpa only [abs_mul] using abs_add_le ((a-c)*(1-b)) (c*(d-b))
    _ = |a-c| *(1-b) + c*|b-d| := by rw [abs_of_nonneg (by linarith : 0 ≤ 1-b), abs_of_nonneg hc, abs_sub_comm d b]
    _ ≤ ε*(1-b) + c*δ := add_le_add (mul_le_mul_of_nonneg_right hε (by linarith))
      (mul_le_mul_of_nonneg_left hδ hc)
    _ ≤ ε + δ := by nlinarith [mul_nonneg hε0 hb, mul_nonneg (sub_nonneg.mpr hc1) hδ0]

end DirectedFeedback.Coupling

noncomputable section
open scoped Classical BigOperators

noncomputable section
open scoped Classical BigOperators

namespace DirectedFeedback

theorem transGen_loop_walk {V : Type*} {R : V → V → Prop} {a : V}
    (h : Relation.TransGen R a a) :
    ∃ (n : ℕ) (f : Fin (n + 1) → V), CyclicWalk R f := by
  obtain ⟨b, hab, hba⟩ := Relation.TransGen.head'_iff.mp h
  obtain ⟨l, hl, hend⟩ := List.exists_isChain_cons_of_relationReflTransGen hba
  have hc : List.IsChain R (a :: b :: l) := .cons_cons hab hl
  let f : Fin (l.length + 1) → V := fun i => (a :: b :: l)[i.val]'(by simp)
  refine ⟨l.length, f, ?_⟩
  intro i
  have hedge := List.isChain_iff_getElem.mp hc i.val (by simp; have := i.isLt; omega)
  by_cases hi : i.val + 1 < l.length + 1
  · simpa only [f, Fin.val_add_one_of_lt' hi] using hedge
  · have hilast : i.val = l.length := by have := i.isLt; omega
    have hwrap : i + 1 = 0 := by apply Fin.ext; simp [Fin.val_add, hilast]
    have he : (a :: b :: l)[i.val + 1]'(by simp; have := i.isLt; omega) = a := by
      have hlast : (a :: b :: l).getLast (by simp) = a := by
        simpa using hend
      rw [List.getLast_eq_getElem] at hlast
      simpa [hilast] using hlast
    simpa only [f, hwrap, Fin.val_zero, List.getElem_cons_zero, he] using hedge

theorem exists_topological_order {V : Type*} [Fintype V] [DecidableEq V]
    (R : V → V → Prop) (F : Finset V) (hF : FeedbackR R F) :
    ∃ order : V → ℕ, (∀ a b, a ∉ F → b ∉ F → R a b → order a < order b) ∧
      (∀ a b, a ∉ F → b ∉ F → order a = order b → a = b) := by
  classical
  let S := {v : V // v ∉ F}
  let r : S → S → Prop := fun a b => R a.val b.val
  have hr : ∀ a : S, ¬Relation.TransGen r a a := by
    intro a ha
    obtain ⟨n, f, hf⟩ := transGen_loop_walk ha
    have hw : CyclicWalk R (fun i => (f i).val) := hf
    obtain ⟨i, hi⟩ := feedback_hits_walk R F hF n (fun i => (f i).val) hw
    exact (f i).property hi
  let po : PartialOrder S :=
    { le := Relation.ReflTransGen r
      le_refl a := .refl
      le_trans _ _ _ := Relation.ReflTransGen.trans
      le_antisymm a b hab hba := by
        rcases Relation.reflTransGen_iff_eq_or_transGen.mp hab with heq | hne
        · exact heq.symm
        · exact False.elim (hr a (hne.trans_left hba)) }
  let := po
  let : Fintype (LinearExtension S) := Fintype.ofEquiv S (Equiv.refl _)
  let e := (Fintype.orderIsoFinOfCardEq (LinearExtension S) rfl).symm
  let rank (a : S) : ℕ := (e (toLinearExtension a)).val
  have hlt {a b : S} (h : r a b) : rank a < rank b := by
    apply e.strictMono
    apply (toLinearExtension.monotone (show a ≤ b from Relation.ReflTransGen.single h)).lt_of_ne
    intro heq
    have heq' : a = b := heq
    subst b
    exact hr a (.single h)
  have hinj {a b : S} (h : rank a = rank b) : a = b := by
    have hh := e.injective (Fin.ext h)
    exact hh
  refine ⟨fun a => if ha : a ∉ F then rank ⟨a, ha⟩ else 0, ?_, ?_⟩
  · intro a b ha hb hab
    simpa [ha, hb] using hlt (a := ⟨a, ha⟩) (b := ⟨b, hb⟩) hab
  · intro a b ha hb heq
    have hh : rank ⟨a, ha⟩ = rank ⟨b, hb⟩ := by simpa [ha, hb] using heq
    exact congrArg Subtype.val (hinj hh)

end DirectedFeedback

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_PrefixBit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
open DirectedFeedback.SourceProbability
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators

noncomputable section
open scoped Classical BigOperators

noncomputable section
open scoped BigOperators
namespace DirectedFeedback.Ranks

def Homogeneous {C : Type*} (r : ℕ) (color : Finset ℕ → C) (s : Finset ℕ) : Prop :=
  ∃ c, ∀ t ⊆ s, t.card = r → color t = c

end DirectedFeedback.Ranks

noncomputable section
open scoped BigOperators
namespace DirectedFeedback.Ranks

variable {I J : Type*} [Fintype I] [Fintype J]

def payoff (a : I → J → ℝ) (x : I → ℝ) (y : J → ℝ) : ℝ :=
  ∑ i, ∑ j, x i * y j * a i j

def probabilitySimplex (Index : Type*) [Fintype Index] : Set (Index → ℝ) :=
  {weights | (∀ index, 0 ≤ weights index) ∧ ∑ index, weights index = 1}

end DirectedFeedback.Ranks

noncomputable section
open scoped BigOperators
namespace DirectedFeedback.Ranks

def toFinite (N : ℕ) (s : Finset ℕ) : Finset (Fin N) :=
  s.preimage Fin.val Fin.val_injective.injOn

@[simp] theorem toFinite_image {N : ℕ} (s : Finset (Fin N)) :
    toFinite N (s.image Fin.val) = s := by
  classical
  ext x
  simp [toFinite, Fin.val_inj]

end DirectedFeedback.Ranks
open scoped Classical
namespace DirectedFeedback.Ranks
open DirectedFeedback.SourceProbability
open DirectedFeedback.SourceProbability.FiniteDistribution

def tripleVector {L : ℕ} (a c h : Fin L) : Fin 3 → Fin L := ![a, c, h]

theorem tripleVector_strict {L : ℕ} {a c h : Fin L} (hac : a < c) (hch : c < h) :
    StrictMono (tripleVector a c h) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [tripleVector]
  exact hac.trans hch

end DirectedFeedback.Ranks

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_LastBias
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
open DirectedFeedback.SourceProbability
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
open scoped Classical
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Soundness
open DirectedFeedback.SourceProbability
open FiniteDistribution
variable {Ω : Type*} [Fintype Ω]

theorem geometric_half_sum (n : ℕ) : ∑ i ∈ Finset.range (n + 1), (2 : ℝ)^i / 2 =
    2^n - 1 / 2 := by
  induction n with
  | zero => norm_num
  | succ n ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring

theorem dyadic_layer_cake (M : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    (∑ i ∈ Finset.range M, (2 : ℝ)^i / 2 * if 2^i ≤ x then 1 else 0) ≤ x := by
  induction M with
  | zero => simpa using hx
  | succ n ih =>
      by_cases hh : (2 : ℝ)^n ≤ x
      · calc
          _ ≤ ∑ i ∈ Finset.range (n + 1), (2 : ℝ)^i / 2 := by
            apply Finset.sum_le_sum
            intro i _
            split_ifs
            · simp
            · simp only [mul_zero]
              positivity
          _ = 2^n - 1 / 2 := geometric_half_sum n
          _ ≤ x := by linarith
      · simpa only [Finset.sum_range_succ, hh, ↓reduceIte, mul_zero, add_zero] using ih

end DirectedFeedback.Soundness

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_OutputDef
attribute [-instance] _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.BoundedExpr.UnaryRead

def zerosBefore (x : List Bool) (i : Nat) : Nat := (x.take i).count false

def word (x : List Bool) (j : Nat) : Nat :=
  ∑ i ∈ Finset.range x.length, if x[i]?=some true ∧ zerosBefore x i=j then 1 else 0

theorem count_eq_sum {A : Type} [DecidableEq A] (l : List A) (b : A) :
    l.count b = ∑ i ∈ Finset.range l.length, if l[i]?=some b then 1 else 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.length_cons,Finset.sum_range_succ']
    simp only [List.getElem?_cons_zero,List.getElem?_cons_succ,Option.some.injEq]
    rw [← ih]
    by_cases h : a=b <;> simp [h]

@[simp] theorem word_nil (j : Nat) : word [] j=0 := by simp [word]

theorem word_true (x : List Bool) (j : Nat) :
    word (true::x) j = (if j=0 then 1 else 0)+word x j := by
  rw [word,List.length_cons,Finset.sum_range_succ']
  simp only [List.getElem?_cons_zero,List.getElem?_cons_succ,zerosBefore,List.take_zero,
    List.count_nil,true_and,List.take_succ_cons]
  simp [eq_comm,word,zerosBefore,Nat.add_comm]

theorem word_false_zero (x : List Bool) : word (false::x) 0=0 := by
  rw [word,List.length_cons,Finset.sum_range_succ']
  simp [zerosBefore]

theorem word_false_succ (x : List Bool) (j : Nat) : word (false::x) (j+1)=word x j := by
  rw [word,List.length_cons,Finset.sum_range_succ']
  simp only [zerosBefore,List.take_zero,List.count_nil,List.getElem?_cons_zero,
    Bool.false_eq_true,Option.some.injEq,false_and,↓reduceIte,
    List.getElem?_cons_succ,List.take_succ_cons,List.count_cons_self,Nat.add_right_cancel_iff]
  rfl

theorem word_prefix_zero (n : Nat) (x : List Bool) :
    word (List.replicate n true ++ false::x) 0=n := by
  induction n with
  | zero => simp [word_false_zero]
  | succ n ih => simp [List.replicate_succ,word_true,ih,Nat.add_comm]

theorem word_prefix_succ (n : Nat) (x : List Bool) (j : Nat) :
    word (List.replicate n true ++ false::x) (j+1)=word x j := by
  induction n with
  | zero => simp [word_false_succ]
  | succ n ih => simp [List.replicate_succ,word_true,ih]

end DirectedFeedback.BoundedExpr.UnaryRead

end

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
open scoped BigOperators
open scoped Classical BigOperators
open scoped Classical
open scoped Classical
open scoped Classical BigOperators
open scoped BigOperators
open scoped BigOperators
open DirectedFeedback.SourceProbability
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators

open scoped Classical BigOperators
namespace DirectedFeedback

def Rational (x : ℝ) : Prop := ∃ q : ℚ, x = q
end DirectedFeedback

open scoped Classical BigOperators
namespace DirectedFeedback

namespace Digraph

theorem dfvs_le_iff (G : Digraph) (k : ℕ) :
    G.dfvs ≤ k ↔ ∃ F : Finset (Fin G.n), G.Feedback F ∧ F.card ≤ k := by
  constructor
  · intro hk
    obtain ⟨F,hF,hcard⟩ := Nat.find_spec
      (show ∃ k : ℕ, ∃ F : Finset (Fin G.n), G.Feedback F ∧ F.card = k from
        ⟨G.n,Finset.univ,by intro r c _; exact ⟨0,Finset.mem_univ _⟩,by simp⟩)
    exact ⟨F,hF,hcard.trans_le hk⟩
  · rintro ⟨F,hF,hcard⟩
    exact (Nat.find_min' _ ⟨F,hF,rfl⟩).trans hcard

theorem dfvs_attained (G : Digraph) :
    ∃ F : Finset (Fin G.n), G.Feedback F ∧ F.card = G.dfvs := by
  exact Nat.find_spec
    (show ∃ k : ℕ, ∃ F : Finset (Fin G.n), G.Feedback F ∧ F.card = k from
      ⟨G.n,Finset.univ,by intro r c _; exact ⟨0,Finset.mem_univ _⟩,by simp⟩)

end Digraph

end DirectedFeedback

open scoped Classical BigOperators

end

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.GameRead
open BoundedExpr BoundedExpr.UnaryRead

variable (q : Nat) [NeZero q]
def n (x : List Bool) : Nat := max 1 (word x 0)
def m (x : List Bool) : Nat := max 1 (word x 2)
def field (x : List Bool) (e j : Nat) : Nat := word x (3+e*(q+2)+j)
def left (x : List Bool) (e : Nat) : Nat := field q x e 0 % n x
def right (x : List Bool) (e : Nat) : Nat := field q x e 1 % n x
def table (x : List Bool) (e : Nat) : Fin q → Fin q := fun i =>
  ⟨field q x e (2+i.val)%q,Nat.mod_lt _ (NeZero.pos q)⟩
def asPerm (f : Fin q → Fin q) : Equiv.Perm (Fin q) :=
  if h : Function.Bijective f then Equiv.ofBijective f h else Equiv.refl _
def perm (x : List Bool) (e : Nat) : Equiv.Perm (Fin q) := asPerm q (table q x e)
def fiber (x : List Bool) (e : Nat) : (Fin q × Bool) ≃ (Fin q × Bool) :=
  Equiv.prodCongr (perm q x e) (Equiv.refl Bool)

theorem n_pos (x : List Bool) : 0<n x := by unfold n; omega
theorem m_pos (x : List Bool) : 0 < m x := by unfold m; omega

lemma get_flatMap {A : Type} (f : A → List Nat) (L : Nat) (hL : ∀ a,(f a).length=L)
    (as : List A) (e : Fin as.length) (j : Nat) (hj : j<L) :
    (as.flatMap f)[e.val*L+j]?.getD 0=(f as[e])[j]?.getD 0 := by
  induction as with
  | nil => exact e.elim0
  | cons a as ih =>
    refine Fin.cases ?_ (fun e => ?_) e
    · simp only [Fin.val_zero,zero_mul,zero_add,List.flatMap_cons]
      rw [List.getElem?_append_left (by simpa [hL] using hj)]
      rfl
    · simp only [Fin.val_succ,List.flatMap_cons]
      rw [List.getElem?_append_right (by rw [hL]; nlinarith)]
      rw [hL]
      have he : (e.val+1)*L+j-L=e.val*L+j := by rw [add_mul,one_mul]; omega
      rw [he]
      exact ih e

end DirectedFeedback.GameRead

end

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.PotentialCover

variable {L B I : Type} [Fintype L] [Fintype B]

def fullFibers (p : L → B) (F : Finset L) : Finset B :=
  Finset.univ.filter (fun b => ∀ a, p a=b → a ∈ F)

@[simp] theorem mem_fullFibers (p : L → B) (F : Finset L) (b : B) :
    b ∈ fullFibers p F ↔ ∀ a, p a=b → a ∈ F := by simp [fullFibers]

theorem feedback_project (p : L → B) (R : B → B → Prop) (S : L → L → Prop)
    (hcover : ∀ a b, R (p a) (p b) → S a b) (F : Finset L)
    (hF : FeedbackR S F) : FeedbackR R (fullFibers p F) := by
  intro n f hinj harc
  by_contra hn
  have hex (i) : ∃ a, p a=f i ∧ a ∉ F := by
    have hi : f i ∉ fullFibers p F := fun h => hn ⟨i,h⟩
    obtain ⟨a,ha⟩ := not_forall.mp ((mem_fullFibers p F (f i)).not.mp hi)
    exact ⟨a,Classical.not_imp.mp ha⟩
  choose g hg using hex
  have hginj : Function.Injective g := by
    intro i j hij
    apply hinj
    rw [← (hg i).1,← (hg j).1,hij]
  obtain ⟨i,hi⟩ := hF n g hginj (fun i => hcover _ _ (by
    rw [(hg i).1,(hg (i+1)).1]
    exact harc i))
  exact (hg i).2 hi

def fiberCount (p : L → B) (b : B) : Nat := (Finset.univ.filter (fun a => p a=b)).card

theorem fullFibers_cost_le (p : L → B) (F : Finset L) :
    ∑ b ∈ fullFibers p F, fiberCount p b ≤ F.card := by
  have he : ∑ b ∈ fullFibers p F, fiberCount p b =
      (Finset.univ.filter (fun a => p a ∈ fullFibers p F)).card := by
    simp only [fiberCount,Finset.card_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    simp
  rw [he]
  exact Finset.card_le_card (by
    intro a ha
    exact (mem_fullFibers p F (p a)).mp ((Finset.mem_filter.mp ha).2) a rfl)

theorem weight_le_card (p : L → B) (w : B → ℝ) (C : Nat)
    (hw : ∀ b, C*w b ≤ fiberCount p b) (F : Finset L) :
    C * (∑ b ∈ fullFibers p F, w b) ≤ F.card := by
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ b ∈ fullFibers p F, (fiberCount p b : ℝ) :=
      Finset.sum_le_sum (fun b _ => hw b)
    _ = ((∑ b ∈ fullFibers p F, fiberCount p b : Nat) : ℝ) := by simp
    _ ≤ F.card := by exact_mod_cast fullFibers_cost_le p F

end DirectedFeedback.PotentialCover

end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_AllGraph
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

theorem flatMap_filter {A B : Type} (l : List A) (p : A → Bool) (f : A → List B) :
    (l.filter p).flatMap f = l.flatMap (fun a => if p a then f a else []) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : p a=true <;> simp [h,ih]

theorem map_fin_values (n : Nat) : (List.finRange n).map Fin.val=List.range n := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp

end Family
end DirectedFeedback.GraphPrinter

end
end

section

noncomputable section
open scoped Classical
namespace DirectedFeedback.LocalAssignments

def Consistent {S A : Type} (coords : S → Nat) (labels : S → A) : Prop :=
  ∀ i j, coords i=coords j → labels i=labels j

theorem extend_global {S A : Type} [Nonempty A] (coords : S → Nat) (labels : S → A)
    (hc : Consistent coords labels) : ∃ all : Nat → A, all ∘ coords=labels := by
  let all : Nat → A := fun v => if h : ∃ i, coords i=v then labels h.choose
    else Classical.choice inferInstance
  exact ⟨all,funext (fun i => by
    dsimp [all]
    split_ifs with h
    · exact hc _ _ h.choose_spec
    · exact False.elim (h ⟨i,rfl⟩))⟩

theorem restriction_consistent {S A : Type} (coords : S → Nat) (all : Nat → A) :
    Consistent coords (all ∘ coords) := fun _ _ h => congrArg all h

theorem forall_iff {S T X Y : Type} [Nonempty X] [Nonempty Y]
    (u : S → Nat) (v : T → Nat) (P : (S → X) → (T → Y) → Prop) :
    (∀ a : Nat → X, ∀ b : Nat → Y, P (a ∘ u) (b ∘ v)) ↔
      ∀ a b, Consistent u a → Consistent v b → P a b := by
  constructor
  · intro h a b ha hb
    obtain ⟨la,hla⟩ := extend_global u a ha
    obtain ⟨lb,hlb⟩ := extend_global v b hb
    simpa only [hla,hlb] using h la lb
  · intro h a b
    exact h _ _ (restriction_consistent u a) (restriction_consistent v b)

end DirectedFeedback.LocalAssignments

end
end

section

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.LocalPrinter
open BoundedExpr LocalAssignments

abbrev Rule (S T X Y : Type) (H : Nat) := (S → X) → (T → Y) → Option (Fin H)

def potential {H : Nat} (a : Option (Fin H)) : Nat := (a.map Fin.val).getD 0

end DirectedFeedback.LocalPrinter

end
end

section

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.SourceProbability.FiniteDistribution

def zipEquiv (A B : Type) (n : Nat) :
    ((Fin n → A) × (Fin n → B)) ≃ (Fin n → A × B) where
  toFun p i := (p.1 i,p.2 i)
  invFun p := (fun i => (p i).1,fun i => (p i).2)
  left_inv _ := rfl
  right_inv _ := rfl

end DirectedFeedback.SourceProbability.FiniteDistribution

end
end

section

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.PacketSeeds
open SourceProbability FiniteDistribution
variable {U V E X Y : Type} [Fintype U] [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
variable {M T N : Nat} [NeZero M] [NeZero T]

abbrev SlotSeed (X : Type) (M : Nat) := Σ _ : Fin M, X → Bool
abbrev PrefixSeed (X : Type) (M t : Nat) := Fin t → SlotSeed X M

end DirectedFeedback.PacketSeeds

end
end

section

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.RankPackets
open RankGraph

abbrev Shape (X Y : Type) (T N : Nat) :=
  (Σ t : Fin (T+1), (Fin t.val → X) → Fin N) ⊕
  (Σ t : Fin T, ((Fin t.val → X) × Y) → Fin N)

instance shapeFintype {X Y : Type} [Fintype X] [Fintype Y] {T N : Nat} :
    Fintype (Shape X Y T N) := by unfold Shape; infer_instance

end DirectedFeedback.RankPackets

end
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
namespace DirectedFeedback.PacketLocality
open SourceProbability FiniteDistribution RankGraph PacketSeeds
variable {U V E X Y : Type} [Fintype U] [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
variable {M T N : Nat} [NeZero M] [NeZero T]

abbrev Slots (T : Nat) := Fin (T+1)

variable (hYX : Fintype.card Y≤Fintype.card X)
  (fiber : E → X ≃ Y × Bool)
variable (e : Slots T → E)
  (a : U → X)
  (b : V → Y)

lemma map_snoc_apply {t : Nat} {A B : Type} (f : A → B) (v : Fin t → A) (w : A) (i : Fin (t+1)) :
    f ((Fin.snoc v w : Fin (t+1) → A) i)= (Fin.snoc (fun i => f (v i)) (f w) : Fin (t+1) → B) i :=
  congrFun (Fin.comp_snoc f v w) i

end DirectedFeedback.PacketLocality

end
end

section

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.RawFamily
open BoundedExpr PacketSeeds RankGraph
variable (q M T N : Nat) [NeZero q] [NeZero M] [NeZero T] [NeZero N]
abbrev X := Fin q × Bool
abbrev Y := Fin q
abbrev Shape := RankPackets.Shape (X q) (Y q) T N
omit [NeZero q] in
theorem hYX : Fintype.card (Y q) ≤ Fintype.card (X q) := by simp [X,Y,Fintype.card_prod]; omega
variable (D C : Nat)
def scale (x : List Bool) : Nat := C*(GameRead.m x)^(T+1)
def r (x : List Bool) : Nat := scale T C x*(D+1)
def base (x : List Bool) := SumBox.base (GameRead.n x) (GameRead.m x)

end DirectedFeedback.RawFamily

end
end

section

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.FiniteLift
variable {L B : Type} [Fintype L] [Fintype B]
variable {n : Nat} (e : L → Fin n) (he : Function.Injective e)
include he
def pull (F : Finset (Fin n)) : Finset L := Finset.univ.filter (fun a => e a ∈ F)

 theorem pull_card (F : Finset (Fin n)) : (pull e F).card ≤ F.card := by
  calc
    _ = ((pull e F).image e).card := (Finset.card_image_of_injective _ he).symm
    _ ≤ F.card := Finset.card_le_card (by intro x hx; obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx; exact (Finset.mem_filter.mp ha).2)

theorem pull_feedback (R : Fin n → Fin n → Prop) (F : Finset (Fin n)) (hF : FeedbackR R F) :
    FeedbackR (fun a b => R (e a) (e b)) (pull e F) := by
  intro k f hi ha
  obtain ⟨i,hi⟩ := hF k (e ∘ f) (he.comp hi) ha
  exact ⟨i,by simp [pull] at hi ⊢; exact hi⟩

theorem feedback_cost (p : L → B) (R : B → B → Prop) (S : Fin n → Fin n → Prop)
    (hcover : ∀ a b, R (p a) (p b) → S (e a) (e b)) (w : B → ℝ) (C D : Nat)
    (hw : ∀ b, (C:ℝ)*w b ≤ PotentialCover.fiberCount p b)
    (hgap : ∀ F : Finset B, FeedbackR R F → (D:ℝ)<∑ b ∈ F,w b)
    (hC : 0<C) (F : Finset (Fin n)) (hF : FeedbackR S F) :
    (C*D:Nat) < (F.card:ℝ) := by
  have hp := pull_feedback e he S F hF
  have hb := PotentialCover.feedback_project p R (fun a b => S (e a) (e b)) hcover (pull e F) hp
  have hc := PotentialCover.weight_le_card p w C hw (pull e F)
  have hd := mul_lt_mul_of_pos_left (hgap _ hb) (show (0:ℝ)<C by exact_mod_cast hC)
  have hcard : ((pull e F).card:ℝ)≤F.card := by exact_mod_cast pull_card e he F
  rw [Nat.cast_mul]
  linarith
end DirectedFeedback.FiniteLift

end
end

section

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.RawFamily
open PacketSeeds SourceProbability FiniteDistribution RankGraph
variable {q M T N : Nat} [NeZero q] [NeZero M] [NeZero T] [NeZero N]
variable (D C : Nat)
  (hC : 0<C)
  (x : List Bool)
abbrev W := Fin (GameRead.n x)
abbrev E := Fin (GameRead.m x)
instance wNonempty : Nonempty (W x) := ⟨⟨0,GameRead.n_pos x⟩⟩
instance eNonempty : Nonempty (E x) := ⟨⟨0,GameRead.m_pos x⟩⟩

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
open scoped Classical
namespace DirectedFeedback.CookLevin

namespace NPTableau
open Turing
attribute [local instance] FinTM2.ΛFin

def alphabetCodec (V : NPVerifier) : FiniteCodec (Atom V.computation.tm.Γ
    V.computation.tm.Λ V.computation.tm.σ) := by
  have := atom_finite V
  have := atom_nonempty V
  letI := Fintype.ofFinite (Atom V.computation.tm.Γ V.computation.tm.Λ V.computation.tm.σ)
  exact oneHotCodec _

instance codec_width_nonempty (V : NPVerifier) : Nonempty (Fin (alphabetCodec V).width) := by
  have := atom_finite V
  have := atom_nonempty V
  let := Fintype.ofFinite (Atom V.computation.tm.Γ V.computation.tm.Λ V.computation.tm.σ)
  change Nonempty (Fin (Fintype.card (Atom V.computation.tm.Γ V.computation.tm.Λ V.computation.tm.σ)))
  infer_instance

end NPTableau
end DirectedFeedback.CookLevin

end
end

section

noncomputable section
open scoped Classical
namespace DirectedFeedback.CookLevin

def LocalCSP.padAt {A I E J : Type} (C : LocalCSP A I E J) (P : Type) (default : I) :
    LocalCSP A I E (J ⊕ P) :=
  ⟨fun e => Sum.elim (C.query e) (fun _ => default),
    fun e pattern => C.accepts e (pattern ∘ Sum.inl)⟩

theorem LocalCSP.padAt_satisfiable_iff {A I E J : Type} (C : LocalCSP A I E J) (P : Type) (d : I) :
    (C.padAt P d).Satisfiable ↔ C.Satisfiable := Iff.rfl

namespace NPTableau
open Turing
attribute [local instance] FinTM2.ΛFin

def eventCount (H S : Nat) := (S+1)+H*(S+1)+1

def decodeEvent (H S : Nat) (e : Fin (eventCount H S)) : TableauEvent H S :=
  if h : e.val < S+1 then .inl ⟨e.val,h⟩
  else if h' : e.val-(S+1) < H*(S+1) then
    .inr (.inl (finProdFinEquiv.symm ⟨e.val-(S+1),h'⟩))
  else .inr (.inr ())

abbrev FixedSlot (V : NPVerifier) :=
  (TableauSlot V.computation.tm × Fin (alphabetCodec V).width) ⊕ Fin 3

def queryNumber (V : NPVerifier) : Nat := Fintype.card (FixedSlot V)

def slotIndex (V : NPVerifier) : FixedSlot V ≃ Fin (queryNumber V) := Fintype.equivFin _

def variableIndex (H S w : Nat) : ((TracePosition H S) × Fin w) ≃ Fin ((H+1)*(S+1)*w) :=
  (Equiv.prodCongr finProdFinEquiv (Equiv.refl _)).trans finProdFinEquiv

theorem variableIndex_val (H S w : Nat) (p : TracePosition H S) (b : Fin w) :
    (variableIndex H S w (p,b)).val = (p.1.val*(S+1)+p.2.val)*w+b.val := by
  simp [variableIndex,finProdFinEquiv,Nat.mul_comm,Nat.add_comm]

theorem queryNumber_ge (V : NPVerifier) : 3 ≤ queryNumber V := by
  simp [queryNumber,FixedSlot]

end NPTableau
end DirectedFeedback.CookLevin

end
end

section

noncomputable section
open scoped Classical
namespace DirectedFeedback.CookLevin
open BoundedExpr Turing
variable {K : Type} [DecidableEq K] [Fintype K] {Γ : K → Type} {Λ σ : Type}
  [Fintype σ] [Fintype Λ] [∀ k, Fintype (Γ k)] {r R : Nat}

def rawData (S j : Nat) (a : StepSlot R → Atom Γ Λ σ) : LocalData Γ Λ σ R where
  ctrl := (a (.inr (.inr 0))).1
  head := fun i k => if i.val<S then (a (.inl i)).2 k else none
  band := fun i k => if j-R+i.val<S then (a (.inr (.inl i))).2 k else none

def rawStepAccepts (M : Λ → TM2.Stmt Γ Λ σ) (S j : Nat)
    (a : StepSlot (programRadius M) → Atom Γ Λ σ) : Bool :=
  let w := wordNext M ((rawData S j a).wordCfg j)
  decide ((a (.inr (.inr 1))).1=(w.label,w.var) ∧
    (j<S → ∀ k, (a (.inr (.inr 2))).2 k=w.stk k j))

omit [Fintype σ] [∀ k, Fintype (Γ k)] in
theorem rawStepAccepts_eq (M : Λ → TM2.Stmt Γ Λ σ) {S : Nat} (j : Fin (S+1))
    (a : StepSlot (programRadius M) → Atom Γ Λ σ) :
    rawStepAccepts M S j.val a = stepAccepts M j a := by
  have hd : rawData S j.val a = dataOfQueries j a := by
    apply LocalData.ext
    · rfl
    · funext i k; simp only [rawData,dataOfQueries]
    · funext i k; simp only [rawData,dataOfQueries]
  simp only [rawStepAccepts,stepAccepts,hd,decide_eq_decide]

namespace NPTableau
attribute [local instance] FinTM2.ΛFin FinTM2.kFin FinTM2.σFin

noncomputable instance verifierAlphabet (V : NPVerifier) (k : V.computation.tm.K) :
    Fintype (V.computation.tm.Γ k) := @Fintype.ofFinite _ (V.finiteAlphabet k)

def rawInitialAccepts (V : NPVerifier) (x : List Bool) (j : Nat)
    (a : Fin 3 → Atom V.computation.tm.Γ V.computation.tm.Λ V.computation.tm.σ) : Bool :=
  decide (initialPredicate V.computation.tm (fixedPrefix V x) (certBound V x.length) j (a 0).1
    (fun k => if j < capacity V x.length then (a 1).2 k else none)
    (fun k => if j+1 < capacity V x.length then (a 2).2 k else none))

theorem rawInitialAccepts_eq (V : NPVerifier) (x : List Bool) (j : Fin (capacity V x.length+1))
    (a : Fin 3 → Atom V.computation.tm.Γ V.computation.tm.Λ V.computation.tm.σ) :
    rawInitialAccepts V x j.val a =
      initialAccepts V.computation.tm (fixedPrefix V x) (certBound V x.length) j a := by
  simp only [rawInitialAccepts,initialAccepts]

end NPTableau
end DirectedFeedback.CookLevin

end
end

section

noncomputable section
open scoped Classical
namespace DirectedFeedback.CookLevin
open BoundedExpr Turing
attribute [local instance] FinTM2.ΛFin

def rawCell (S i : Nat) : Nat := if i < S then i+1 else 0

theorem rawCell_eq (S i : Nat) : rawCell S i = (cellAddress S i).val := by
  dsimp [rawCell,cellAddress]
  split_ifs <;> rfl

def rawInitialQuery (S j : Nat) (i : Fin 3) : Nat × Nat :=
  if i.val=0 then (0,0) else if i.val=1 then (0,rawCell S j) else (0,rawCell S (j+1))

def rawStepQuery {R : Nat} (S t j : Nat) : StepSlot R → Nat × Nat
  | .inl i => (t,rawCell S i.val)
  | .inr (.inl i) => (t,rawCell S (j-R+i.val))
  | .inr (.inr i) => if i.val=0 then (t,0) else if i.val=1 then (t+1,0) else (t+1,rawCell S j)

theorem rawInitialQuery_eq {H S : Nat} (j : Fin (S+1)) (i : Fin 3) :
    rawInitialQuery S j.val i = ((initialQuery (H:=H) j i).1.val,(initialQuery (H:=H) j i).2.val) := by
  dsimp [rawInitialQuery,initialQuery]
  split_ifs <;> simp [rawCell_eq]

theorem rawStepQuery_eq {H S R : Nat} (t : Fin H) (j : Fin (S+1)) (i : StepSlot R) :
    rawStepQuery S t.val j.val i = ((stepQuery t j i).1.val,(stepQuery t j i).2.val) := by
  rcases i with i | (i | i)
  · simp [rawStepQuery,stepQuery,rawCell_eq]
  · simp [rawStepQuery,stepQuery,rawCell_eq]
  · dsimp [rawStepQuery,stepQuery]; split_ifs <;> simp [rawCell_eq]

namespace NPTableau

def rawTableauQuery (tm : FinTM2) (H S e : Nat) (s : TableauSlot tm) : Nat × Nat :=
  if e < S+1 then match s with
    | .inl i => rawInitialQuery S e i
    | _ => (0,0)
  else if e-(S+1) < H*(S+1) then match s with
    | .inr (.inl i) => rawStepQuery S ((e-(S+1))/(S+1)) ((e-(S+1))%(S+1)) i
    | _ => (0,0)
  else match s with
    | .inr (.inr _) => (H,rawCell S 0)
    | _ => (0,0)

theorem rawTableauQuery_correct (tm : FinTM2) (H S : Nat) (e : Fin (eventCount H S))
    (s : TableauSlot tm) :
    rawTableauQuery tm H S e.val s =
      ((tableauQuery tm (decodeEvent H S e) s).1.val,(tableauQuery tm (decodeEvent H S e) s).2.val) := by
  unfold rawTableauQuery decodeEvent
  split_ifs with hi hs
  · rcases s with i | (i | u)
    · exact rawInitialQuery_eq (H:=H) (S:=S) ⟨e.val,hi⟩ i
    · rfl
    · rfl
  · rcases s with i | (i | u)
    · rfl
    · simpa only [tableauQuery,finProdFinEquiv_symm_apply,Fin.divNat,Fin.modNat] using
        rawStepQuery_eq (finProdFinEquiv.symm ⟨e.val-(S+1),hs⟩).1
          (finProdFinEquiv.symm ⟨e.val-(S+1),hs⟩).2 i
    · rfl
  · rcases s with i | (i | u)
    · rfl
    · rfl
    · simp [tableauQuery,rawCell_eq]

def rawQuery (V : NPVerifier) (s : FixedSlot V) (x : List Bool) (e : Nat) : Nat :=
  let w := (alphabetCodec V).width
  match s with
  | .inl (s,b) =>
    let p := rawTableauQuery V.computation.tm (horizon V x.length) (capacity V x.length) e s
    (p.1*(capacity V x.length+1)+p.2)*w+b.val
  | .inr _ => (Classical.choice (codec_width_nonempty V)).val

end NPTableau
end DirectedFeedback.CookLevin

end
end

end OAI
end


