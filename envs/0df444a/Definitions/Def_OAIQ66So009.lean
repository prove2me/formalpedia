-- Prove2me | Definitions.Def_OAIQ66So009
-- name    : OAIQ66So009
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T02:11:51.203402+00:00
-- url     : https://prove2.me/theorems/d0e2cfe0-9079-41da-8bb5-871b81c073e0
-- title:
--   Definitions bundle OAIQ66So009 of the split of OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SimpleFInftyOvergroups.main`, carved from OpenAI's openai/math development (OpenAI, *Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)*, OpenAI Math Release, September 23, 2026, result family 250, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 97 declarations of OpenAI's Lean: 41 definitions, 4 inductive types or structures, 11 instances and 41 theorems. The definitions and types are `OAI.SourceCorner.val`, `OAI.StageGeometry.instDecidableEq_solutions_1`, `OAI.StandardHomology.chainsIso`, `OAI.StandardHomology.coefficientMap`, `OAI.StandardHomology.homologyIso`, `OAI.SteinChains.Complex`, `OAI.SteinChains.ProperFace`, `OAI.SteinChains.boundaryComplex`, `OAI.Steinberg.matrixBlock`, `OAI.SteinbergFinitePresentation.Coeff`, `OAI.SteinbergFinitePresentation.Index`, `OAI.SteinbergFinitePresentation.Quad`, `OAI.SteinbergFinitePresentation.Triple`, `OAI.SteinbergFinitePresentation.coefficient`, `OAI.SteinbergWords.Away`, `OAI.SteinbergWords.Chain`, `OAI.SteinbergWords.Initial`, `OAI.SteinbergWords.middle`, `OAI.SteinbergWords.polynomial`, `OAI.SteinbergWords.polynomialAdd`, `OAI.SteinbergWords.rootSubgroup`, `OAI.SteinbergWords.word`, `OAI.SurjectiveTrivialInduction.backward`, `OAI.SurjectiveTrivialInduction.forward`, `OAI.SurjectiveTrivialInduction.iso`, `OAI.TwistedBrin.Basis.Matching.GroundFaces`, `OAI.TwistedBrin.Oligomorphic`, `OAI.TwistedBrin.Pattern`, `OAI.TwistedBrin.Pattern.Leaves`, `OAI.TwistedBrin.Pattern.bounded`, `OAI.TwistedBrin.Pattern.coordinates`, `OAI.TwistedBrin.Pattern.depth`, `OAI.TwistedBrin.Pattern.graft`, `OAI.TwistedBrin.Pattern.graftLeaves`, `OAI.TwistedBrin.Pattern.nodes`, `OAI.TwistedBrin.Pattern.rectangular`, `OAI.TwistedBrin.Pattern.relabel`, `OAI.TwistedBrin.Pattern.relabelLeaves`, `OAI.TwistedBrin.Pattern.shuffle`, `OAI.TwistedBrin.Pattern.uniform` and 5 more.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: `FiniteCompiler_TapeFolding`, `FiniteType_NonunitalCompression`, `FiniteType_OrderChains`, `FiniteType_OrderListChainsBased`, `FiniteType_ProductGroupHomology`, `FiniteType_SourceCorner`, `FiniteType_StageGeometryProperties`, `FiniteType_StandardHomology`, `FiniteType_SteinbergFinitePresentation`, `FiniteType_SteinbergWords`, `FiniteType_SurjectiveTrivialInduction`, `FiniteType_TwistedBrinBasis`, `FiniteType_TwistedBrinBasisFirstCut`, `FiniteType_TwistedBrinBasisGroundMatching`, `FiniteType_TwistedBrinBasisTranslateEquiv`, `FiniteType_TwistedBrinGermBrick`, `FiniteType_TwistedBrinPattern`, `FiniteType_TwistedBrinPrefix`, `SimpleOvergroups_EnlargementCore`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ66So015`.
-- source:
--   OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 250; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/ComparatorChallenges/SimpleOvergroups.lean; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit 1581d4c

import Mathlib

section
-- module Solutions.OAIQ066_SO.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
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
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteCompiler_TapeFolding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Safe tapes, literal folding, and uniform code-machine realization.
-/

namespace FiniteAlgebraicEnvelopes.MachineRealization.UniformCode
open Turing.ToPartrec

theorem eval_comp (f g : Code) (v : List ℕ) :
    (Code.comp f g).eval v = (g.eval v).bind (fun w => f.eval w) := rfl

attribute [local simp] eval_comp

open Encodable

end FiniteAlgebraicEnvelopes.MachineRealization.UniformCode

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_StandardHomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory CategoryTheory.Limits
open _root_.CategoryTheory
open _root_.CategoryTheory MonoidalCategory _root_.Representation TensorProduct
namespace StandardHomology
variable {R G : Type} [CommRing R] [Group G]

def coefficientMap (P : ChainComplex (Rep R G) ℕ) {A B : Rep R G} (α : A ⟶ B) :
    P.coinvariantsTensorObj A ⟶ P.coinvariantsTensorObj B :=
  (NatTrans.mapHomologicalComplex ((Rep.coinvariantsTensor R G).map α) _).app P

def chainsIso (A : Rep R G) : groupHomology.inhomogeneousChains A ≅
    (Rep.standardComplex R G).coinvariantsTensorObj A := by
  classical
  exact groupHomology.inhomogeneousChainsIso A ≪≫
    (((Rep.coinvariantsTensor R G).obj A).mapHomologicalComplex _).mapIso
      (Rep.barComplex.isoStandardComplex R G)

def homologyIso (A : Rep R G) (n : ℕ) : groupHomology A n ≅
    ((Rep.standardComplex R G).coinvariantsTensorObj A).homology n :=
  (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) n).mapIso
    (chainsIso A)

end StandardHomology

open _root_.CategoryTheory
namespace groupHomology
open scoped _root_.groupHomology
variable (R G : Type) [CommRing R] [Group G]

instance chainsFunctor_additive : (_root_.groupHomology.chainsFunctor R G).Additive where
  map_add := by
    intro A B α β
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext
    intro s a
    change (_root_.groupHomology.chainsMap (MonoidHom.id G) (α+β)).f n (Finsupp.single s a) =
      (_root_.groupHomology.chainsMap (MonoidHom.id G) α).f n (Finsupp.single s a) +
      (_root_.groupHomology.chainsMap (MonoidHom.id G) β).f n (Finsupp.single s a)
    exact (_root_.groupHomology.chainsMap_f_single (MonoidHom.id G) (α+β) n s a).trans
      ((Finsupp.single_add _ _ _).trans
        (congrArg₂ (· + ·)
          (_root_.groupHomology.chainsMap_f_single (MonoidHom.id G) α n s a)
          (_root_.groupHomology.chainsMap_f_single (MonoidHom.id G) β n s a)).symm)

instance functor_additive (n : ℕ) : (_root_.groupHomology.functor R G n).Additive := by
  change (_root_.groupHomology.chainsFunctor R G ⋙
    HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) n).Additive
  infer_instance

end groupHomology

open _root_.CategoryTheory

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_NonunitalCompression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise
open scoped commutatorElement

namespace Steinberg

variable {n m R : Type*} [Ring R] [Fintype n] [DecidableEq n]

def matrixBlock {p : Type*} [Fintype p] [DecidableEq p] :
    (Matrix n n R)ˣ →* (Matrix (n ⊕ p) (n ⊕ p) R)ˣ where
  toFun A := {
    val := Matrix.fromBlocks A.val 0 0 1
    inv := Matrix.fromBlocks A.inv 0 0 1
    val_inv := by rw [Matrix.fromBlocks_multiply]; simp [Matrix.fromBlocks_one]
    inv_val := by rw [Matrix.fromBlocks_multiply]; simp [Matrix.fromBlocks_one] }
  map_one' := Units.ext (by simp [Matrix.fromBlocks_one])
  map_mul' A B := by
    apply Units.ext
    change Matrix.fromBlocks (A * B).val 0 0 1 =
      Matrix.fromBlocks A.val 0 0 1 * Matrix.fromBlocks B.val 0 0 1
    rw [Matrix.fromBlocks_multiply]
    simp

end Steinberg

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SteinbergWords
attribute [-instance] _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise
open scoped commutatorElement
namespace SteinbergWords
variable {H : Type*} [Group H]

lemma interchange (a b c : H) (hac : Commute a c)
    (huv : Commute ⁅a,b⁆ ⁅b,c⁆) (hvc : Commute ⁅b,c⁆ c) :
    ⁅⁅a,b⁆,c⁆=⁅a,⁅b,c⁆⁆ := by
  have h1 : a*b*c=⁅a,b⁆*⁅b,c⁆*c*b*a := by
    calc
      a*b*c = ⁅a,b⁆*b*a*c := by simp [commutatorElement_def,mul_assoc]
      _ = ⁅a,b⁆*b*c*a := by rw [mul_assoc (⁅a,b⁆*b) a c,hac.eq]; group
      _ = ⁅a,b⁆*⁅b,c⁆*c*b*a := by simp [commutatorElement_def,mul_assoc]
  have h2 : a*b*c=⁅a,⁅b,c⁆⁆*⁅b,c⁆*c*⁅a,b⁆*b*a := by
    calc
      a*b*c = a*⁅b,c⁆*c*b := by simp [commutatorElement_def,mul_assoc]
      _ = ⁅a,⁅b,c⁆⁆*⁅b,c⁆*a*c*b := by simp [commutatorElement_def,mul_assoc]
      _ = ⁅a,⁅b,c⁆⁆*⁅b,c⁆*c*a*b := by rw [mul_assoc (⁅a,⁅b,c⁆⁆*⁅b,c⁆) a c,hac.eq]; group
      _ = ⁅a,⁅b,c⁆⁆*⁅b,c⁆*c*⁅a,b⁆*b*a := by simp [commutatorElement_def,mul_assoc]
  have he : ⁅a,b⁆*⁅b,c⁆*c=⁅a,⁅b,c⁆⁆*⁅b,c⁆*c*⁅a,b⁆ :=
    mul_right_cancel (mul_right_cancel (h1.symm.trans h2))
  have hv : Commute ⁅b,c⁆ ⁅⁅a,b⁆,c⁆ :=
    ((huv.symm.mul_right hvc).mul_right huv.symm.inv_right).mul_right hvc.inv_right
  apply mul_right_cancel (b:=⁅b,c⁆*c*⁅a,b⁆)
  calc
    ⁅⁅a,b⁆,c⁆*(⁅b,c⁆*c*⁅a,b⁆) = ⁅b,c⁆*(⁅⁅a,b⁆,c⁆*c*⁅a,b⁆) := by
      simp only [← mul_assoc]
      rw [hv.symm.eq]
    _ = ⁅b,c⁆*(⁅a,b⁆*c) := by simp [commutatorElement_def,mul_assoc]
    _ = ⁅a,b⁆*⁅b,c⁆*c := by rw [← mul_assoc,huv.symm.eq]
    _ = ⁅a,⁅b,c⁆⁆*(⁅b,c⁆*c*⁅a,b⁆) := by simpa only [mul_assoc] using he

variable {n α : Type*}

structure Initial where
  gen : ∀ i j : n, i≠j → Option α → H
  away : ∀ i j k l hij hkl, i≠l → j≠k → ∀ a b,
    Commute (gen i j hij a) (gen k l hkl b)
  chain_left : ∀ i j k hij hjk hik a,
    ⁅gen i j hij none,gen j k hjk a⁆=gen i k hik a
  chain_right : ∀ i j k hij hjk hik a,
    ⁅gen i j hij a,gen j k hjk none⁆=gen i k hik a

variable (outside : ∀ i j k l : n, ∃ p, p≠i ∧ p≠j ∧ p≠k ∧ p≠l)

def middle (i j : n) : n := (outside i j i j).choose
lemma middle_left (i j : n) : i≠middle outside i j :=
  (outside i j i j).choose_spec.1.symm
lemma middle_right (i j : n) : middle outside i j≠j :=
  (outside i j i j).choose_spec.2.1

variable (D : Initial (n:=n) (α:=α) (H:=H))

def word (i j : n) (hij : i≠j) (w : List α) : H :=
  match w with
  | [] => D.gen i j hij none
  | [a] => D.gen i j hij (some a)
  | a::b::t => ⁅D.gen i (middle outside i j) (middle_left outside i j) (some a),
      word (middle outside i j) j (middle_right outside i j) (b::t)⁆

@[simp] lemma word_nil (i j : n) (hij) : word outside D i j hij []=D.gen i j hij none := by
  rw [word]
@[simp] lemma word_singleton (i j : n) (hij) (a : α) :
    word outside D i j hij [a]=D.gen i j hij (some a) := by rw [word]
lemma word_cons_cons (i j : n) (hij) (a b : α) (t : List α) :
    word outside D i j hij (a::b::t)=
      ⁅word outside D i (middle outside i j) (middle_left outside i j) [a],
        word outside D (middle outside i j) j (middle_right outside i j) (b::t)⁆ := by
  rw [word_singleton]
  rw [word]

def Away (m : ℕ) : Prop := ∀ (u v : List α), u.length ≤ m → v.length ≤ m →
  ∀ i j k l hij hkl, i≠l → j≠k →
    Commute (word outside D i j hij u) (word outside D k l hkl v)

def Chain (m : ℕ) : Prop := ∀ (u v : List α), u.length+v.length ≤ m →
  ∀ i j k hij hjk hik,
    ⁅word outside D i j hij u,word outside D j k hjk v⁆=
      word outside D i k hik (u++v)

lemma base : Away outside D 1 ∧ Chain outside D 1 := by
  constructor
  · intro u v hu hv i j k l hij hkl hil hjk
    cases u with
    | nil =>
      cases v with
      | nil => exact D.away i j k l hij hkl hil hjk _ _
      | cons b s =>
        have hs : s=[] := List.eq_nil_of_length_eq_zero (by simpa using hv)
        subst s; exact D.away i j k l hij hkl hil hjk _ _
    | cons a t =>
      have ht : t=[] := List.eq_nil_of_length_eq_zero (by simpa using hu)
      subst t
      cases v with
      | nil => exact D.away i j k l hij hkl hil hjk _ _
      | cons b s =>
        have hs : s=[] := List.eq_nil_of_length_eq_zero (by simpa using hv)
        subst s; exact D.away i j k l hij hkl hil hjk _ _
  · intro u v huv i j k hij hjk hik
    cases u with
    | nil =>
      cases v with
      | nil => exact D.chain_left i j k hij hjk hik none
      | cons b s =>
        have hs : s=[] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons,List.length_nil] at huv; omega)
        subst s; exact D.chain_left i j k hij hjk hik (some b)
    | cons a t =>
      have ht : t=[] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons] at huv; omega)
      have hv : v=[] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons] at huv; omega)
      subst t v; exact D.chain_right i j k hij hjk hik (some a)

lemma split_head {m : ℕ} (hm : 1 ≤ m) (ha : Away outside D m) (hc : Chain outside D m)
    (a : α) (t : List α) (ht : t.length ≤ m)
    (i j k : n) (hij : i≠j) (hik : i≠k) (hkj : k≠j) :
    word outside D i j hij (a::t)=
      ⁅word outside D i k hik [a],word outside D k j hkj t⁆ := by
  cases t with
  | nil => exact (hc [a] [] (by simpa using hm) i k j hik hkj hij).symm
  | cons b t =>
    rw [word_cons_cons]
    let p := middle outside i j
    have hip : i≠p := middle_left outside i j
    have hpj : p≠j := middle_right outside i j
    by_cases hkp : k=p
    · subst k; rfl
    have hleft := hc [a] [] (by simpa using hm) i k p hik hkp hip
    have hright := hc [] (b::t) (by simpa using ht) k p j hkp hpj hkj
    simp only [List.append_nil,List.nil_append] at hleft hright
    have hi := interchange (word outside D i k hik [a]) (word outside D k p hkp [])
      (word outside D p j hpj (b::t))
      (ha [a] (b::t) (by simpa using hm) ht i k p j hik hpj hij hkp)
      (by rw [hleft,hright]; exact ha [a] (b::t) (by simpa using hm) ht i p k j hip hkj hij (Ne.symm hkp))
      (by rw [hright]; exact ha (b::t) (b::t) ht ht k j p j hkj hpj hkj hpj.symm)
    simpa only [hleft,hright] using hi

lemma commute_bracket_left {a b c : H} (hac : Commute a c) (hbc : Commute b c) :
    Commute ⁅a,b⁆ c :=
  ((hac.mul_left hbc).mul_left hac.inv_left).mul_left hbc.inv_left

lemma away_step {m : ℕ} (hm : 1 ≤ m) (ha : Away outside D m) (hc : Chain outside D m) :
    Away outside D (m+1) := by
  have hn : ∀ (u v : List α), u.length ≤ m+1 → v.length ≤ m →
      ∀ i j k l hij hkl, i≠l → j≠k →
        Commute (word outside D i j hij u) (word outside D k l hkl v) := by
    intro u v hu hv i j k l hij hkl hil hjk
    by_cases hu' : u.length ≤ m
    · exact ha u v hu' hv i j k l hij hkl hil hjk
    cases u with
    | nil => simp at hu'
    | cons a t =>
      have ht : t.length ≤ m := by simp only [List.length_cons] at hu; omega
      obtain ⟨p,hpi,hpj,hpk,hpl⟩ := outside i j k l
      rw [split_head outside D hm ha hc a t ht i j p hij hpi.symm hpj]
      apply commute_bracket_left
      · exact ha [a] v (by simpa using hm) hv i p k l hpi.symm hkl hil hpk
      · exact ha t v ht hv p j k l hpj hkl hpl hjk
  intro u v hu hv i j k l hij hkl hil hjk
  by_cases hv' : v.length ≤ m
  · exact hn u v hu hv' i j k l hij hkl hil hjk
  cases v with
  | nil => simp at hv'
  | cons b t =>
    have ht : t.length ≤ m := by simp only [List.length_cons] at hv; omega
    obtain ⟨p,hpk,hpl,hpi,hpj⟩ := outside k l i j
    rw [split_head outside D hm ha hc b t ht k l p hkl hpk.symm hpl]
    exact (commute_bracket_left
      (hn u [b] hu (by simpa using hm) i j k p hij hpk.symm hpi.symm hjk).symm
      (hn u t hu ht i j p l hij hpl hil hpj.symm).symm).symm

lemma chain_step {m : ℕ} (hm : 1 ≤ m) (ha : Away outside D m) (hc : Chain outside D m)
    (han : Away outside D (m+1)) : Chain outside D (m+1) := by
  intro u v huv i j k hij hjk hik
  by_cases ho : u.length+v.length ≤ m
  · exact hc u v ho i j k hij hjk hik
  cases u with
  | nil =>
    cases v with
    | nil => simp at ho
    | cons a t =>
      have ht : t.length ≤ m := by simp only [List.length_nil,List.length_cons] at huv; omega
      obtain ⟨p,hpi,hpj,hpk,_⟩ := outside i j k k
      have hleft := hc [] [a] (by simpa using hm) i j p hij hpj.symm hpi.symm
      simp only [List.nil_append] at hleft
      have hs := split_head outside D hm ha hc a t ht j k p hjk hpj.symm hpk
      have hi := interchange (word outside D i j hij [])
        (word outside D j p hpj.symm [a]) (word outside D p k hpk t)
        (han [] t (by simp) (by omega) i j p k hij hpk hik hpj.symm)
        (by
          rw [hleft,← hs]
          exact han [a] (a::t) (by simp only [List.length_singleton]; omega)
            (by simpa using huv) i p j k hpi.symm hjk hik hpj)
        (by
          rw [← hs]
          exact han (a::t) t (by simpa using huv) (by omega) j k p k hjk hpk hjk hpk.symm)
      simp only [List.nil_append]
      rw [hs,← hi,hleft]
      exact (split_head outside D hm ha hc a t ht i k p hik hpi.symm hpk).symm
  | cons a t =>
    have ht : t.length ≤ m := by simp only [List.length_cons] at huv; omega
    have htv : t.length+v.length ≤ m := by simp only [List.length_cons] at huv; omega
    obtain ⟨p,hpi,hpj,hpk,_⟩ := outside i j k k
    have hs := split_head outside D hm ha hc a t ht i j p hij hpi.symm hpj
    have hr := hc t v htv p j k hpj hjk hpk
    have hi := interchange (word outside D i p hpi.symm [a])
      (word outside D p j hpj t) (word outside D j k hjk v)
      (han [a] v (by simp only [List.length_singleton]; omega) (by simp only [List.length_cons] at huv; omega)
        i p j k hpi.symm hjk hik hpj)
      (by
        rw [← hs,hr]
        exact han (a::t) (t++v) (by simp only [List.length_cons] at *; omega)
          (by simp only [List.length_append]; omega) i j p k hij hpk hik hpj.symm)
      (by
        rw [hr]
        exact han (t++v) v (by simp only [List.length_append]; omega)
          (by simp only [List.length_cons] at huv; omega) p k j k hpk hjk hpk hjk.symm)
    rw [hs,hi,hr]
    exact (split_head outside D hm ha hc a (t++v) (by simpa only [List.length_append] using htv)
      i k p hik hpi.symm hpk).symm

lemma laws (m : ℕ) : Away outside D (m+1) ∧ Chain outside D (m+1) := by
  induction m with
  | zero => exact base outside D
  | succ m ih =>
    have ha := away_step outside D (by omega : 1 ≤ m+1) ih.1 ih.2
    exact ⟨ha,chain_step outside D (by omega) ih.1 ih.2 ha⟩

theorem word_commute (u v : List α) (i j k l : n) (hij : i≠j) (hkl : k≠l)
    (hil : i≠l) (hjk : j≠k) :
    Commute (word outside D i j hij u) (word outside D k l hkl v) :=
  (laws outside D (u.length+v.length)).1 u v (by omega) (by omega) i j k l hij hkl hil hjk

theorem word_chain (u v : List α) (i j k : n) (hij : i≠j) (hjk : j≠k) (hik : i≠k) :
    ⁅word outside D i j hij u,word outside D j k hjk v⁆=word outside D i k hik (u++v) :=
  (laws outside D (u.length+v.length)).2 u v (by omega) i j k hij hjk hik

def rootSubgroup (i j : n) (hij : i≠j) : Subgroup H :=
  Subgroup.closure (Set.range (word outside D i j hij))

instance rootSubgroupCommutative (i j : n) (hij : i≠j) :
    IsMulCommutative (rootSubgroup outside D i j hij) := by
  apply Subgroup.isMulCommutative_closure
  rintro _ ⟨u,rfl⟩ _ ⟨v,rfl⟩
  exact word_commute outside D u v i j i j hij hij hij hij.symm

open scoped IsMulCommutative

def polynomialAdd (i j : n) (hij : i≠j) : FreeAbelianGroup (FreeMonoid α) →+ Additive H :=
  (rootSubgroup outside D i j hij).subtype.toAdditive.comp
    (FreeAbelianGroup.lift (fun w : FreeMonoid α =>
      Additive.ofMul (⟨word outside D i j hij w,Subgroup.subset_closure ⟨w,rfl⟩⟩ :
        rootSubgroup outside D i j hij)))

def polynomial (i j : n) (hij : i≠j) (a : FreeAbelianGroup (FreeMonoid α)) : H :=
  Additive.toMul (polynomialAdd outside D i j hij a)

@[simp] lemma polynomial_of (i j : n) (hij : i≠j) (w : FreeMonoid α) :
    polynomial outside D i j hij (FreeAbelianGroup.of w)=word outside D i j hij w := by
  simp [polynomial,polynomialAdd]
@[simp] lemma polynomial_zero (i j : n) (hij : i≠j) :
    polynomial outside D i j hij 0=1 := by simp [polynomial]
lemma polynomial_add (i j : n) (hij : i≠j) (a b : FreeAbelianGroup (FreeMonoid α)) :
    polynomial outside D i j hij (a+b)=polynomial outside D i j hij a*polynomial outside D i j hij b := by
  simp [polynomial]
lemma polynomial_neg (i j : n) (hij : i≠j) (a : FreeAbelianGroup (FreeMonoid α)) :
    polynomial outside D i j hij (-a)=(polynomial outside D i j hij a)⁻¹ := by simp [polynomial]

lemma polynomial_commute (i j k l : n) (hij : i≠j) (hkl : k≠l) (hil : i≠l) (hjk : j≠k)
    (a b : FreeAbelianGroup (FreeMonoid α)) :
    Commute (polynomial outside D i j hij a) (polynomial outside D k l hkl b) := by
  induction a using FreeAbelianGroup.induction_on with
  | zero => simp
  | of u =>
    induction b using FreeAbelianGroup.induction_on with
    | zero => simp
    | of v => simpa only [polynomial_of] using word_commute outside D u v i j k l hij hkl hil hjk
    | neg b hb => simpa only [polynomial_neg] using hb.inv_right
    | add b c hb hc => simpa only [polynomial_add] using hb.mul_right hc
  | neg a ha => simpa only [polynomial_neg] using ha.inv_left
  | add a c ha hc => simpa only [polynomial_add] using ha.mul_left hc

lemma bracket_inv_left (a b : H) (h : Commute a ⁅a,b⁆) : ⁅a⁻¹,b⁆=⁅a,b⁆⁻¹ := by
  rw [commutatorElement_inv_left,← commutatorElement_inv,h.inv_left.inv_right.eq]
  simp only [mul_assoc,inv_mul_cancel,mul_one]

lemma bracket_inv_right (a b : H) (h : Commute b ⁅a,b⁆) : ⁅a,b⁻¹⁆=⁅a,b⁆⁻¹ := by
  rw [commutatorElement_inv_right,← commutatorElement_inv,h.inv_left.inv_right.eq]
  simp only [mul_assoc,inv_mul_cancel,mul_one]

lemma bracket_mul_left (a c b : H) (h : Commute a ⁅c,b⁆) (hq : Commute ⁅a,b⁆ ⁅c,b⁆) :
    ⁅a*c,b⁆=⁅a,b⁆*⁅c,b⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul,h.eq]
  simpa only [mul_assoc,mul_inv_cancel,mul_one] using hq.symm.eq

lemma bracket_mul_right (a b c : H) (h : Commute b ⁅a,c⁆) :
    ⁅a,b*c⁆=⁅a,b⁆*⁅a,c⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj,mul_assoc ⁅a,b⁆ b ⁅a,c⁆,h.eq]
  group

theorem polynomial_chain (i j k : n) (hij : i≠j) (hjk : j≠k) (hik : i≠k)
    (a b : FreeAbelianGroup (FreeMonoid α)) :
    ⁅polynomial outside D i j hij a,polynomial outside D j k hjk b⁆=
      polynomial outside D i k hik (a*b) := by
  induction a using FreeAbelianGroup.induction_on with
  | zero => simp
  | of u =>
    induction b using FreeAbelianGroup.induction_on with
    | zero => simp
    | of v =>
      rw [FreeAbelianGroup.of_mul_of,polynomial_of,polynomial_of,polynomial_of]
      exact word_chain outside D u v i j k hij hjk hik
    | neg v hv =>
      rw [polynomial_neg,mul_neg,polynomial_neg,bracket_inv_right _ _ (by
        rw [hv]
        exact polynomial_commute outside D j k i k hjk hik hjk hik.symm _ _),hv]
    | add b c hb hc =>
      rw [polynomial_add,mul_add,polynomial_add,bracket_mul_right _ _ _ (by
        rw [hc]
        exact polynomial_commute outside D j k i k hjk hik hjk hik.symm _ _),hb,hc]
  | neg u hu =>
    rw [polynomial_neg,neg_mul,polynomial_neg,bracket_inv_left _ _ (by
      rw [hu]
      exact polynomial_commute outside D i j i k hij hik hik hij.symm _ _),hu]
  | add a c ha hc =>
    rw [polynomial_add,add_mul,polynomial_add,bracket_mul_left _ _ _ (by
      rw [hc]
      exact polynomial_commute outside D i j i k hij hik hik hij.symm _ _)
      (by rw [ha,hc]; exact polynomial_commute outside D i k i k hik hik hik hik.symm _ _),ha,hc]

end SteinbergWords

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SteinbergFinitePresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise
section
open scoped commutatorElement
namespace SteinbergFinitePresentation
open scoped commutatorElement
variable (n α : Type*)

abbrev Triple := {t : n×n×n // t.1≠t.2.1 ∧ t.2.1≠t.2.2 ∧ t.1≠t.2.2}
abbrev Quad := {t : n×n×n×n // t.1≠t.2.1 ∧ t.2.2.1≠t.2.2.2 ∧
  t.1≠t.2.2.2 ∧ t.2.1≠t.2.2.1}
abbrev Index := (Quad n × Option α × Option α) ⊕ (Bool × Triple n × Option α)

abbrev Coeff := FreeAbelianGroup (FreeMonoid α)
def coefficient : Option α → Coeff α
  | none => 1
  | some a => FreeAbelianGroup.of (FreeMonoid.of a)

end SteinbergFinitePresentation
end

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SourceCorner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise
namespace SourceCorner
variable {R : Type} [Ring R] {e : R} (he : IsIdempotentElem e)
                                                                          
def val : he.Corner →ₙ+* R where
  toFun x := x.val
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

end SourceCorner

end

open _root_.CategoryTheory CategoryTheory.Limits

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SurjectiveTrivialInduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory CategoryTheory.Limits _root_.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory CategoryTheory.Limits
namespace SurjectiveTrivialInduction
open _root_.CategoryTheory _root_.Representation
attribute [-instance] AddCommGroup.toIntModule
variable {G H : Type} [Group G] [Group H] (φ : G →* H) (hs : Function.Surjective φ)

include hs in
lemma mk_eq (h : H) (a : ℤ) :
    IndV.mk φ (Rep.trivial ℤ G ℤ).ρ h a = IndV.mk φ (Rep.trivial ℤ G ℤ).ρ 1 a := by
  obtain ⟨g,rfl⟩ := hs h
  have he := Coinvariants.mk_tmul_inv ((Representation.leftRegular ℤ H).comp φ)
    (Rep.trivial ℤ G ℤ).ρ (MonoidAlgebra.single (1 : H) (1 : ℤ)) a g
  simpa using he.symm

def forward : Rep.ind φ (Rep.trivial ℤ G ℤ) ⟶ Rep.trivial ℤ H ℤ :=
  (Rep.indResHomEquiv φ _ _).symm (Rep.ofHom ⟨LinearMap.id,fun _ => rfl⟩)
lemma forward_mk (h : H) (a : ℤ) :
    forward φ (IndV.mk φ (Rep.trivial ℤ G ℤ).ρ h a) = a := by
  simp [forward,Rep.indResHomEquiv]

def backward : Rep.trivial ℤ H ℤ ⟶ Rep.ind φ (Rep.trivial ℤ G ℤ) :=
  Rep.ofHom ⟨IndV.mk φ (Rep.trivial ℤ G ℤ).ρ 1, by
    intro h
    apply DFunLike.ext
    intro a
    change IndV.mk φ (Rep.trivial ℤ G ℤ).ρ 1 a =
      (Representation.ind φ (Rep.trivial ℤ G ℤ).ρ) h (IndV.mk φ (Rep.trivial ℤ G ℤ).ρ 1 a)
    rw [Representation.ind_mk]
    exact (mk_eq φ hs _ _).symm⟩

def iso : Rep.ind φ (Rep.trivial ℤ G ℤ) ≅ Rep.trivial ℤ H ℤ where
  hom := forward φ
  inv := backward φ hs
  hom_inv_id := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply IndV.hom_ext
    intro h
    apply DFunLike.ext
    intro a
    change IndV.mk φ (Rep.trivial ℤ G ℤ).ρ 1
      (forward φ (IndV.mk φ (Rep.trivial ℤ G ℤ).ρ h a)) = IndV.mk φ (Rep.trivial ℤ G ℤ).ρ h a
    rw [forward_mk]
    exact (mk_eq φ hs h a).symm
  inv_hom_id := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply DFunLike.ext
    intro a
    exact forward_mk φ 1 a
end SurjectiveTrivialInduction

open _root_.CategoryTheory CategoryTheory.Limits
namespace ProductGroupHomology
section
attribute [-instance] AddCommGroup.toIntModule

open scoped MonoidalCategory
end

open _root_.CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
attribute [-instance] AddCommGroup.toIntModule
end ProductGroupHomology

attribute [instance] AddCommGroup.toIntModule

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_ProductGroupHomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory CategoryTheory.Limits _root_.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
namespace ProductGroupHomology
open _root_.CategoryTheory CategoryTheory.Limits
attribute [-instance] AddCommGroup.toIntModule
end ProductGroupHomology

open Set Function
open scoped Pointwise

universe u v
namespace TwistedBrin

structure Prefix (S : Type u) where
  word : S → List Bool
  finite_support : {s | word s ≠ []}.Finite

namespace Prefix
variable {S : Type u}
instance instCoeFunForallListBool : CoeFun (Prefix S) (fun _ => S → List Bool) := ⟨Prefix.word⟩
@[ext] theorem ext {p q : Prefix S} (h : ∀ s, p s = q s) : p = q := by
  cases p; cases q; simp_all only [mk.injEq]; exact funext h

def empty : Prefix S := ⟨fun _ => [], by simp⟩
@[simp] lemma empty_apply (s : S) : (empty : Prefix S) s = [] := rfl

def append (p q : Prefix S) : Prefix S where
  word s := p s ++ q s
  finite_support := (p.finite_support.union q.finite_support).subset (by
    intro s hs
    simp only [mem_ofPred_eq, mem_union] at *
    by_contra h
    push Not at h
    simp [h.1,h.2] at hs)
@[simp] lemma append_apply (p q : Prefix S) (s : S) : append p q s = p s ++ q s := rfl
@[simp] lemma empty_append (p : Prefix S) : append empty p = p := by ext; simp
@[simp] lemma append_empty (p : Prefix S) : append p empty = p := by ext; simp
lemma append_assoc (p q r : Prefix S) : append (append p q) r = append p (append q r) := by
  ext; simp [List.append_assoc]

end Prefix

end TwistedBrin

namespace TwistedBrin
section
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

def Oligomorphic : Prop :=
  ∀ n : ℕ, ∃ R : Finset (Finset S), ∀ F : Finset S, F.card = n →
    ∃ (E : Finset S), E ∈ R ∧ ∃ a : A, F.map (ρ a).toEmbedding = E

end

end TwistedBrin

namespace TwistedBrin.Prefix
variable {S : Type u}

noncomputable def Grid (b : S →₀ ℕ) := (s : b.support) → Fin (b s) → Bool
noncomputable instance instFintypeGrid (b : S →₀ ℕ) : Fintype (Grid b) := by
  classical
  unfold Grid
  infer_instance

end TwistedBrin.Prefix

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_OrderListChainsBased
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory CategoryTheory.Limits _root_.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise

namespace SteinChains
variable (V : Type*)

structure Complex where
  faces : Set (Finset V)
  down : ∀ {F E}, F ∈ faces → E ⊆ F → E ∈ faces

def boundaryComplex (T : Finset V) : Complex V where
  faces := {F | F ⊆ T ∧ F.card < T.card}
  down := fun h h' => ⟨h'.trans h.1,lt_of_le_of_lt (Finset.card_le_card h') h.2⟩

end SteinChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_OrderChains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory CategoryTheory.Limits _root_.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise

namespace SteinChains
variable (V : Type*) [Fintype V]
                                                                      
def ProperFace := {F : Finset V // F ≠ ∅ ∧ F ≠ Finset.univ}
instance instPartialOrderProperFace : PartialOrder (ProperFace V) := inferInstanceAs
  (PartialOrder {F : Finset V // F ≠ ∅ ∧ F ≠ Finset.univ})
end SteinChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrinBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory CategoryTheory.Limits _root_.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
universe u v

namespace TwistedBrin

inductive Pattern (S : Type u)
  | leaf
  | split (s : S) (left right : Pattern S)

namespace Pattern
variable {S : Type u}

def Leaves : Pattern S → Type
  | .leaf => Unit
  | .split _ P Q => Leaves P ⊕ Leaves Q

instance leavesFintype : (P : Pattern S) → Fintype (Leaves P)
  | .leaf => inferInstanceAs (Fintype Unit)
  | .split _ P Q => by
    letI := leavesFintype P
    letI := leavesFintype Q
    exact inferInstanceAs (Fintype (Leaves P ⊕ Leaves Q))

end Pattern
end TwistedBrin

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrinPrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory CategoryTheory.Limits _root_.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
universe u v

namespace TwistedBrin.Pattern
variable {S : Type u}

def relabel (σ : Equiv.Perm S) : Pattern S → Pattern S
  | .leaf => .leaf
  | .split s P Q => .split (σ s) (relabel σ P) (relabel σ Q)

def relabelLeaves (σ : Equiv.Perm S) : (P : Pattern S) → Leaves P ≃ Leaves (relabel σ P)
  | .leaf => Equiv.refl _
  | .split _ P Q => Equiv.sumCongr (relabelLeaves σ P) (relabelLeaves σ Q)

def graft : (P : Pattern S) → (Leaves P → Pattern S) → Pattern S
  | .leaf, Q => Q ()
  | .split s P R, Q => .split s (graft P (fun i => Q (.inl i)))
      (graft R (fun i => Q (.inr i)))

def graftLeaves : (P : Pattern S) → (Q : Leaves P → Pattern S) →
    (Σ i : Leaves P, Leaves (Q i)) ≃ Leaves (graft P Q)
  | .leaf, Q => {
      toFun := fun i => by rcases i with ⟨⟨⟩,i⟩; exact i
      invFun := fun i => ⟨(),i⟩
      left_inv := by rintro ⟨⟨⟩,i⟩; rfl
      right_inv := fun _ => rfl }
  | .split _ P R, Q => {
      toFun := fun i => match i with
        | ⟨.inl i,j⟩ => .inl (graftLeaves P (fun i => Q (.inl i)) ⟨i,j⟩)
        | ⟨.inr i,j⟩ => .inr (graftLeaves R (fun i => Q (.inr i)) ⟨i,j⟩)
      invFun := fun i => match i with
        | .inl j => let k := (graftLeaves P (fun i => Q (.inl i))).symm j; ⟨.inl k.1,k.2⟩
        | .inr j => let k := (graftLeaves R (fun i => Q (.inr i))).symm j; ⟨.inr k.1,k.2⟩
      left_inv := by
        rintro ⟨i,j⟩
        cases i with
        | inl i =>
          exact congrArg (fun k : Σ i : Leaves P, Leaves (Q (.inl i)) =>
            (⟨Sum.inl k.1,k.2⟩ : Σ i : Leaves (.split _ P R), Leaves (Q i)))
            ((graftLeaves P (fun i => Q (.inl i))).symm_apply_apply ⟨i,j⟩)
        | inr i =>
          exact congrArg (fun k : Σ i : Leaves R, Leaves (Q (.inr i)) =>
            (⟨Sum.inr k.1,k.2⟩ : Σ i : Leaves (.split _ P R), Leaves (Q i)))
            ((graftLeaves R (fun i => Q (.inr i))).symm_apply_apply ⟨i,j⟩)
      right_inv := by
        intro i
        cases i with
        | inl i =>
          exact congrArg Sum.inl ((graftLeaves P (fun i => Q (.inl i))).apply_symm_apply i)
        | inr i =>
          exact congrArg Sum.inr ((graftLeaves R (fun i => Q (.inr i))).apply_symm_apply i) }

end TwistedBrin.Pattern

namespace TwistedBrin.Pattern
variable {S : Type u}

def uniform : List S → Pattern S
  | [] => .leaf
  | s :: L => .split s (uniform L) (uniform L)

noncomputable def rectangular (b : S →₀ ℕ) : Pattern S :=
  uniform (Finsupp.toMultiset b).toList

end TwistedBrin.Pattern

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrinBasisTranslateEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory CategoryTheory.Limits _root_.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
universe u v

namespace TwistedBrin.Pattern
variable {S : Type u}

@[simp] lemma graft_leaf (P : Pattern S) : graft P (fun _ => leaf) = P := by
  induction P with
  | leaf => rfl
  | split s P Q ihP ihQ => simp only [graft,ihP,ihQ]

end TwistedBrin.Pattern

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrinPattern
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory CategoryTheory.Limits _root_.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
universe u v

namespace TwistedBrin.Pattern
variable {S : Type u}

def nodes : Pattern S → ℕ
  | .leaf => 0
  | .split _ P Q => nodes P + nodes Q + 1

def depth : Pattern S → ℕ
  | .leaf => 0
  | .split _ P Q => max (depth P) (depth Q) + 1

noncomputable def coordinates : Pattern S → Finset S
  | .leaf => ∅
  | .split s P Q => by classical exact Insert.insert s (coordinates P ∪ coordinates Q)

@[simp] lemma depth_relabel (σ : Equiv.Perm S) (P : Pattern S) :
    depth (relabel σ P) = depth P := by
  induction P with
  | leaf => rfl
  | split s P Q ihP ihQ => simp [relabel,depth,ihP,ihQ]

noncomputable def bounded (U : Finset S) : ℕ → Finset (Pattern S)
  | 0 => {.leaf}
  | n+1 => by
    classical
    exact Insert.insert .leaf (U.biUnion (fun s => (bounded U n).biUnion (fun P =>
      (bounded U n).image (fun Q => .split s P Q))))

end TwistedBrin.Pattern

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrinGermBrick
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory CategoryTheory.Limits _root_.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
universe u v

namespace TwistedBrin
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

def pointwiseStabilizer (F : Finset S) : Subgroup A where
  carrier := {a | ∀ s ∈ F, ρ a s = s}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb s hs
    simp only [map_mul,Equiv.Perm.mul_apply,hb s hs,ha s hs]
  inv_mem' := by
    intro a ha s hs
    rw [map_inv]
    exact (ρ a).symm_apply_eq.mpr (ha s hs).symm

end TwistedBrin

namespace TwistedBrin.Pattern
variable {S : Type u}

def shuffle {α β γ δ : Type*} : ((α ⊕ γ) ⊕ (β ⊕ δ)) ≃ ((α ⊕ β) ⊕ (γ ⊕ δ)) where
  toFun
    | .inl (.inl a) => .inl (.inl a)
    | .inl (.inr c) => .inr (.inl c)
    | .inr (.inl b) => .inl (.inr b)
    | .inr (.inr d) => .inr (.inr d)
  invFun
    | .inl (.inl a) => .inl (.inl a)
    | .inl (.inr b) => .inr (.inl b)
    | .inr (.inl c) => .inl (.inr c)
    | .inr (.inr d) => .inr (.inr d)
  left_inv := by rintro ((a|c)|(b|d)) <;> rfl
  right_inv := by rintro ((a|b)|(c|d)) <;> rfl

end TwistedBrin.Pattern

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrinBasisFirstCut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory CategoryTheory.Limits _root_.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
universe u v

namespace TwistedBrin.OrderNerve

open _root_.CategoryTheory
universe w
variable {α β : Type u} [Preorder α] [Preorder β]

@[simp] lemma nerveMap_order_id : nerveMap (OrderHom.id : α →o α).toFunctor = 𝟙 _ := rfl
@[simp] lemma nerveMap_order_comp {γ : Type u} [Preorder γ]
    (f : α →o β) (g : β →o γ) :
    nerveMap (g.comp f).toFunctor = nerveMap f.toFunctor ≫ nerveMap g.toFunctor := rfl

end TwistedBrin.OrderNerve

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrinBasisGroundMatching
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory CategoryTheory.Limits _root_.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
universe u v
namespace TwistedBrin.Basis

universe w
variable {A : Type v} [Group A] {S : Type u} {ρ : A →* Equiv.Perm S}

namespace Matching
variable {I : Type w}
  [Fintype I]

abbrev GroundFaces := {N : OrderDual (Finset I) // N.Nonempty}

end Matching
end TwistedBrin.Basis

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_StageGeometryProperties
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace StageGeometry
variable {R Y W G : Type} [Ring R] [Nontrivial R] [Group W] [MulAction W Y]
  [Group G]
local instance instDecidableEq_solutions_1 : DecidableEq Y := Classical.decEq _
end StageGeometry

end
end

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_EnlargementCore
attribute [-instance] _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SourceEnlargement

variable {D V Z : Type*} [Ring D] [Group V] [MulAction V Z]

lemma complement_product (E P : D) (hEP : E * P = 0) :
    (1 - E) * (1 - P) = 1 - (E + P) := by
  calc
    (1 - E) * (1 - P) = 1 - (E + P) + E * P := by noncomm_ring
    _ = 1 - (E + P) := by rw [hEP, add_zero]

end SourceEnlargement
end

end OAI
end


