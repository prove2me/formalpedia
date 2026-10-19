-- Prove2me | Definitions.Def_OAIQWUFI004
-- name    : OAIQWUFI004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T19:47:50.981738+00:00
-- url     : https://prove2.me/theorems/97633c3a-4e36-4f9c-8667-851120cf9e4c
-- title:
--   OpenAI universal F∞ group split: definitions bundle 5 of 9
-- statement:
--   Definitions bundle 5 of 9 of the split of OpenAI's proof that a single group of type $F_\infty$ contains every finitely presented group (OpenAI, *A universal group of type F∞*, OpenAI Math Release, September 23, 2026, result family 250, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0). It holds OpenAI's Lean definitions, structures and instances from the modules listed below, ported to Lean 4.33.1 and Mathlib 0df444a. It also holds the lemmas those definitions use in their bodies.
--
--   Many of OpenAI's definitions in this development are built from proofs. They choose witnesses of existence theorems with `Classical.choose` (Brown's construction chooses each next attachment, and the Milnor ghost maps are chosen from `uniform_diagram_sphere_ghost`, which rests on cellular approximation), so the bundle has to contain those proofs and the lemmas behind them. Among them is cellular approximation, here under the name `Cellular.exists_cellular_approximation_bundle`; the same theorem is published as the statement `OAI.UniversalFInfinity.Cellular.exists_cellular_approximation`. The bundle also contains a few lemmas that newer Lean and Mathlib versions provide (such as `ite_eq_left`), defined for compatibility.
--
--   It imports bundles 1–4 of this split (`OAIQWUFI000`–`OAIQWUFI003`).
--
--   Modules: `AscendingTorus.lean`, `Attachments.lean`, `Benign.lean`, `BrownConstruction.lean`, `Cayley.lean`, `CellRetractions.lean`, `CellularApproximation.lean`, `CellularAttachment.lean`, `CellularChains.lean`, `CellularFillings.lean`, `CellularLifting.lean`, `CentralHNN.lean`, `CompactCells.lean`, `ControlledCells.lean`, `ControlledHomotopies.lean`, `CoveringAttachments.lean`, `FiniteHNN.lean`, `GeneralPosition.lean`, `GraphActions.lean`, `GraphBundles.lean`, `HigmanEmbedding.lean`, `HomotopyProducts.lean`, `MarkerMachine.lean`, `Markers.lean`, `Milnor.lean`, `MilnorControl.lean`, `PathExtensions.lean`, `RopeTrick.lean`, `SimplexDisk.lean`, `Simplicial.lean`, `StackMachines.lean`, `StackPrograms.lean`, `TopologicalTowers.lean`, `TuringMachines.lean`, `UniversalPresentation.lean`, `UniverseTransport.lean`.
--
--   The theorems the definitions do not need are proved in the solutions of this split. The split exists because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, A universal group of type F∞, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 250; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-universal-group-of-type-F-infinity-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory/UniversalGroup at commit adc7f12

import Mathlib
import Definitions.Def_OAIQWUFI000
import Definitions.Def_OAIQWUFI001
import Definitions.Def_OAIQWUFI002
import Definitions.Def_OAIQWUFI003

section
-- module Solutions.OAIQW_UniversalFInfinity.Compat
/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    (if hp : p then a hp else b hp) = b h := dif_neg h
end OAICompat434
end

section
-- module Solutions.OAIQW_UniversalFInfinity.CentralHNN
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section UniversalFinitelyPresentedProof
universe u v w x

namespace Higman
open HNNExtension

namespace CentralExtension
variable {G : Type u} [Group G] {K : Type v} [Group K]
variable {A : Subgroup G} {B : Subgroup K}

def map (i : G →* K) (hi : A ≤ B.comap i) :
    CentralExtension G A →* CentralExtension K B :=
  HNNExtension.lift (HNNExtension.of.comp i) HNNExtension.t (by
    intro a
    exact HNNExtension.t_mul_of (φ := MulEquiv.refl B) ⟨i a, hi a.2⟩)

@[simp] theorem map_of (i : G →* K) (hi : A ≤ B.comap i) (g : G) :
    map i hi (HNNExtension.of g) = HNNExtension.of (i g) := by
  exact HNNExtension.lift_of _ _ _ g

@[simp] theorem map_t (i : G →* K) (hi : A ≤ B.comap i) :
    map i hi HNNExtension.t = HNNExtension.t := by
  exact HNNExtension.lift_t _ _ _

def mapWord (i : G →* K) (hi : B.comap i = A)
    (r : NormalWord.ReducedWord G A A) : NormalWord.ReducedWord K B B where
  head := i r.head
  toList := r.toList.map (fun p ↦ (p.1, i p.2))
  chain := by
    apply (List.isChain_map _).mpr
    apply r.chain.imp
    intro a b hab hmem
    apply hab
    have hm : i a.2 ∈ B := by
      simpa [HNNExtension.toSubgroup] using hmem
    have : a.2 ∈ B.comap i := hm
    simpa [hi, HNNExtension.toSubgroup] using this

@[simp] theorem mapWord_prod (i : G →* K) (hi : B.comap i = A)
    (r : NormalWord.ReducedWord G A A) :
    (mapWord i hi r).prod (MulEquiv.refl B) =
      map i (le_of_eq hi.symm) (r.prod (MulEquiv.refl A)) := by
  simp [NormalWord.ReducedWord.prod, mapWord, map_list_prod, List.map_map, Function.comp_def]

theorem map_injective (i : G →* K) (hinj : Function.Injective i)
    (hi : B.comap i = A) : Function.Injective (map i (le_of_eq hi.symm)) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm _ bot_le
  intro g hg
  obtain ⟨d⟩ := NormalWord.TransversalPair.nonempty G A A
  let r := (NormalWord.equiv (MulEquiv.refl A) d g)
  have hr : r.prod (MulEquiv.refl A) = g :=
    (NormalWord.equiv (MulEquiv.refl A) d).symm_apply_apply g
  have hm : (mapWord i hi r.toReducedWord).prod (MulEquiv.refl B) = 1 := by
    rw [mapWord_prod]
    change map i (le_of_eq hi.symm) (r.prod (MulEquiv.refl A)) = 1
    rw [hr]
    exact hg
  have hn := HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range
    (MulEquiv.refl B) (mapWord i hi r.toReducedWord)
    (by rw [hm]; exact Subgroup.one_mem _)
  have hnil : r.toList = [] := by simpa [mapWord] using hn
  have hhead : i r.head = 1 := by
    apply HNNExtension.of_injective (φ := MulEquiv.refl B)
    simpa [mapWord, NormalWord.ReducedWord.prod, hnil] using hm
  have hhead' : r.head = 1 := hinj (by simpa using hhead)
  rw [Subgroup.mem_bot, ← hr]
  simp [NormalWord.ReducedWord.prod, hnil, hhead']

open Monoid Coprod Multiplicative

def relation (g : G) : G ∗ Multiplicative ℤ :=
  (inr (ofAdd 1) * inl g) * (inl g * inr (ofAdd 1))⁻¹

end CentralExtension
end Higman

namespace Higman.Double
open HNNExtension Multiplicative
variable {G : Type u} [Group G] {D : Type v} [Group D]
variable (A : Subgroup G)

abbrev Extension := HNNExtension G A A (MulEquiv.refl A)

def first : G →* Extension A := HNNExtension.of

def second : G →* Extension A :=
  (MulAut.conj HNNExtension.t).toMonoidHom.comp (first A)

def subgroup : Subgroup (Extension A) := (first A).range ⊔ (second A).range

def firstIn : G →* subgroup A :=
  (first A).codRestrict (subgroup A) (fun g ↦ (le_sup_left : (first A).range ≤ subgroup A) ⟨g,rfl⟩)

def secondIn : G →* subgroup A :=
  (second A).codRestrict (subgroup A) (fun g ↦ (le_sup_right : (second A).range ≤ subgroup A) ⟨g,rfl⟩)

variable {A}

def lamp : D →* D ≀ᵣ Multiplicative ℤ where
  toFun d := ⟨fun n ↦ if n = 1 then d else 1, 1⟩
  map_one' := by ext <;> simp
  map_mul' a b := by
    ext n
    · by_cases hn : n = 1 <;> simp [hn]
    · simp

@[simp] theorem lamp_left (d : D) (n : Multiplicative ℤ) :
    (lamp d).left n = if n = 1 then d else 1 := rfl

@[simp] theorem lamp_right (d : D) : (lamp d).right = 1 := rfl

def coordinate (n : Multiplicative ℤ) :
    (RegularWreathProduct.rightHom : D ≀ᵣ Multiplicative ℤ →* Multiplicative ℤ).ker →* D where
  toFun x := x.1.left n
  map_one' := rfl
  map_mul' x y := by
    have hx : x.1.right = 1 := x.2
    simp [RegularWreathProduct.mul_left, hx]

def wreathMap (q : G →* D) (hq : A ≤ q.ker) :
    Extension A →* D ≀ᵣ Multiplicative ℤ :=
  HNNExtension.lift (lamp.comp q) (RegularWreathProduct.inl (ofAdd 1)) (by
    intro a
    have ha : q a = 1 := hq a.2
    simp [ha])

@[simp] theorem wreathMap_first (q : G →* D) (hq : A ≤ q.ker) (g : G) :
    wreathMap q hq (first A g) = lamp (q g) := by
  simp [wreathMap, first]

@[simp] theorem wreathMap_second (q : G →* D) (hq : A ≤ q.ker) (g : G) :
    wreathMap q hq (second A g) =
      RegularWreathProduct.inl (ofAdd 1) * lamp (q g) *
        (RegularWreathProduct.inl (ofAdd 1))⁻¹ := by
  simp [second, MulAut.conj_apply, wreathMap, first]

theorem subgroup_le_coordKer (q : G →* D) (hq : A ≤ q.ker) :
    subgroup A ≤ (RegularWreathProduct.rightHom.comp (wreathMap q hq)).ker := by
  apply sup_le
  · rintro _ ⟨g,rfl⟩
    change (wreathMap q hq (first A g)).right = 1
    simp
  · rintro _ ⟨g,rfl⟩
    change (wreathMap q hq (second A g)).right = 1
    simp

def read (q : G →* D) (hq : A ≤ q.ker) : subgroup A →* D :=
  (coordinate (ofAdd 1)).comp
    (((wreathMap q hq).comp (subgroup A).subtype).codRestrict _
      (fun x ↦ subgroup_le_coordKer q hq x.2))

@[simp] theorem read_first (q : G →* D) (hq : A ≤ q.ker) (g : G) :
    read q hq (firstIn A g) = 1 := by
  change (wreathMap q hq (first A g)).left (ofAdd 1) = 1
  rw [wreathMap_first, lamp_left]
  simp

@[simp] theorem read_second (q : G →* D) (hq : A ≤ q.ker) (g : G) :
    read q hq (secondIn A g) = q g := by
  change (wreathMap q hq (second A g)).left (ofAdd 1) = q g
  rw [wreathMap_second]
  simp

end Higman.Double

end UniversalFinitelyPresentedProof

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.RopeTrick
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v w x

namespace Higman
open Monoid Coprod

lemma commute_of_free_generators {ι : Type u} {κ : Type v}
    {G : Type w} {H : Type x} {K : Type*} [Group G] [Group H] [Group K]
    (p : FreeGroup ι →* G) (hp : Function.Surjective p)
    (q : FreeGroup κ →* H) (hq : Function.Surjective q)
    (f : G →* K) (g : H →* K)
    (hc : ∀ i j, Commute (f (p (FreeGroup.of i))) (g (q (FreeGroup.of j)))) :
    ∀ a b, Commute (f a) (g b) := by
  intro a b
  obtain ⟨a,rfl⟩ := hp a
  obtain ⟨b,rfl⟩ := hq b
  have hgen (i : ι) (b : FreeGroup κ) :
      Commute (f (p (FreeGroup.of i))) (g (q b)) := by
    induction b using FreeGroup.induction_on with
    | C1 => simp
    | of j => exact hc i j
    | inv_of b hb => simpa only [map_inv] using hb.inv_right
    | mul b c hb hc => simpa only [map_mul] using hb.mul_right hc
  induction a using FreeGroup.induction_on with
  | C1 => simp
  | of i => exact hgen i b
  | inv_of a ha => simpa only [map_inv] using ha.inv_left
  | mul a c ha hc => simpa only [map_mul] using ha.mul_left hc

theorem finitelyPresented_prod {G : Type u} {H : Type v} [Group G] [Group H]
    [Group.IsFinitelyPresented G] [Group.IsFinitelyPresented H] :
    Group.IsFinitelyPresented (G × H) := by
  classical
  obtain ⟨n,p,hp,_⟩ := Group.IsFinitelyPresented.out (G := G)
  obtain ⟨m,q,hq,_⟩ := Group.IsFinitelyPresented.out (G := H)
  let relation : Fin n × Fin m → G ∗ H := fun ij ↦
    (inl (p (FreeGroup.of ij.1)) * inr (q (FreeGroup.of ij.2))) *
      (inr (q (FreeGroup.of ij.2)) * inl (p (FreeGroup.of ij.1)))⁻¹
  let N := Subgroup.normalClosure (Set.range relation)
  let Q := (G ∗ H) ⧸ N
  let proj : G ∗ H →* Q := QuotientGroup.mk' N
  let f : G →* Q := proj.comp inl
  let g : H →* Q := proj.comp inr
  have hcomm : ∀ a b, Commute (f a) (g b) := by
    apply commute_of_free_generators p hp q hq
    intro i j
    have h : proj (relation (i,j)) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure ⟨(i,j),rfl⟩)
    exact mul_inv_eq_one.mp (by simpa only [f,g,MonoidHom.comp_apply,relation,map_mul,map_inv] using h)
  let π : G ∗ H →* G × H := Coprod.lift (MonoidHom.inl G H) (MonoidHom.inr G H)
  let s : G × H →* Q := MonoidHom.noncommCoprod f g hcomm
  have hs : s.comp π = proj := by
    apply Coprod.hom_ext <;> ext z <;> simp [s,π,f,g]
  have hker : π.ker = N := by
    apply le_antisymm
    · intro z hz
      apply (QuotientGroup.eq_one_iff _).mp
      change proj z = 1
      rw [← hs]
      change s (π z) = 1
      rw [show π z = 1 from hz,map_one]
    · apply Subgroup.normalClosure_le_normal
      rintro z ⟨⟨i,j⟩,rfl⟩
      change π (relation (i,j)) = 1
      simp [π,relation]
  apply Group.IsFinitelyPresented.of_surjective π
  · rintro ⟨a,b⟩
    exact ⟨inl a * inr b,by simp [π]⟩
  · exact ⟨Set.range relation,Set.finite_range _,hker.symm⟩

end Higman

namespace Higman.RopeTrick

section
open Monoid Coprod Multiplicative

section Container
variable {ι : Type u} {K : Type v} [Group K]

abbrev Raw := (K × FreeGroup ι) ∗ Multiplicative ℤ

def rawK : K →* Raw (ι := ι) (K := K) := Coprod.inl.comp (MonoidHom.inl K (FreeGroup ι))
def rawF : FreeGroup ι →* Raw (ι := ι) (K := K) := Coprod.inl.comp (MonoidHom.inr K (FreeGroup ι))
def rawT : Raw (ι := ι) (K := K) := Coprod.inr (ofAdd 1)

def relation (α β : FreeGroup ι →* K) : ι ⊕ ι → Raw (ι := ι) (K := K)
  | .inl j => (rawT * rawK (α (FreeGroup.of j))) *
      (rawK (α (FreeGroup.of j)) * rawT)⁻¹
  | .inr j => (rawT * rawK (β (FreeGroup.of j))) *
      (rawK (β (FreeGroup.of j)) * rawF (FreeGroup.of j) * rawT)⁻¹

abbrev relations (α β : FreeGroup ι →* K) := Subgroup.normalClosure (Set.range (relation α β))
abbrev Container (α β : FreeGroup ι →* K) := Raw (ι := ι) (K := K) ⧸ relations α β

def proj (α β : FreeGroup ι →* K) : Raw (ι := ι) (K := K) →* Container α β :=
  QuotientGroup.mk' (relations α β)
def kMap (α β : FreeGroup ι →* K) : K →* Container α β := (proj α β).comp rawK
def fMap (α β : FreeGroup ι →* K) : FreeGroup ι →* Container α β := (proj α β).comp rawF
def stable (α β : FreeGroup ι →* K) : Container α β := proj α β rawT

end Container

variable {A : Type u} {K : Type v} {G : Type w} [Group A] [Group K] [Group G]
variable (i : A →* K) (hi : Function.Injective i) (r : A →* G)

def left : A →* K × G := i.prod 1
def right : A →* K × G := i.prod r

include hi in
lemma left_injective : Function.Injective (left i (G := G)) := by
  intro a b h
  exact hi (congrArg Prod.fst h)
include hi in
lemma right_injective : Function.Injective (right i r) := by
  intro a b h
  exact hi (congrArg Prod.fst h)

noncomputable def associated : (left i (G := G)).range ≃* (right i r).range :=
  (MonoidHom.ofInjective (left_injective i hi)).symm.trans
    (MonoidHom.ofInjective (right_injective i hi r))

abbrev Model := HNNExtension (K × G) (left i (G := G)).range (right i r).range (associated i hi r)

lemma associated_left (a : A) : associated i hi r ⟨left i a,⟨a,rfl⟩⟩ =
    ⟨right i r a,⟨a,rfl⟩⟩ := by
  change (MonoidHom.ofInjective (right_injective i hi r))
    ((MonoidHom.ofInjective (left_injective i hi)).symm
      ((MonoidHom.ofInjective (left_injective i hi)) a)) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

lemma model_relation (a : A) :
    (HNNExtension.t : Model i hi r) * HNNExtension.of (i a,1) =
      HNNExtension.of (i a,r a) * HNNExtension.t := by
  have h := HNNExtension.t_mul_of (φ := associated i hi r) ⟨left i a,⟨a,rfl⟩⟩
  rw [associated_left] at h
  exact h

end

open Monoid Coprod Multiplicative
noncomputable section
variable {ι : Type u} {A : Type v} {K : Type w} {G : Type x}
variable [Group A] [Group K] [Group G]
variable (i : A →* K) (hi : Function.Injective i) (r : A →* G)
variable (q : FreeGroup ι →* G)

def evaluate : Raw (ι := ι) (K := K) →* Model i hi r :=
  Coprod.lift (HNNExtension.of.comp ((MonoidHom.id K).prodMap q))
    (zpowersHom _ HNNExtension.t)

@[simp] lemma evaluate_rawK (k : K) :
    evaluate i hi r q (rawK k) = HNNExtension.of (k,1) := by
  simp [evaluate,rawK]
@[simp] lemma evaluate_rawF (w : FreeGroup ι) :
    evaluate i hi r q (rawF w) = HNNExtension.of (1,q w) := by
  simp [evaluate,rawF]
@[simp] lemma evaluate_rawT :
    evaluate i hi r q rawT = HNNExtension.t := by
  simp [evaluate,rawT]

variable (p₀ p₁ : FreeGroup ι →* A)
variable (h₀ : ∀ w, r (p₀ w) = 1) (h₁ : ∀ w, r (p₁ w) = q w)

include h₀ h₁ in
lemma evaluate_relation (j : ι ⊕ ι) :
    evaluate i hi r q (relation (i.comp p₀) (i.comp p₁) j) = 1 := by
  cases j with
  | inl j =>
    simp only [relation,map_mul,map_inv,evaluate_rawK,evaluate_rawT]
    apply mul_inv_eq_one.mpr
    simpa only [MonoidHom.comp_apply,h₀] using model_relation i hi r (p₀ (FreeGroup.of j))
  | inr j =>
    simp only [relation,map_mul,map_inv,evaluate_rawK,evaluate_rawF,evaluate_rawT]
    apply mul_inv_eq_one.mpr
    rw [← map_mul]
    simpa only [MonoidHom.comp_apply,Prod.mk_mul_mk,mul_one,one_mul,h₁] using
      model_relation i hi r (p₁ (FreeGroup.of j))

def detect : Container (i.comp p₀) (i.comp p₁) →* Model i hi r :=
  QuotientGroup.lift _ (evaluate i hi r q) (by
    apply Subgroup.normalClosure_le_normal
    rintro z ⟨j,rfl⟩
    exact evaluate_relation i hi r q p₀ p₁ h₀ h₁ j)

@[simp] lemma detect_fMap (w : FreeGroup ι) :
    detect i hi r q p₀ p₁ h₀ h₁ (fMap (i.comp p₀) (i.comp p₁) w) =
      HNNExtension.of (1,q w) := by
  change evaluate i hi r q (rawF w) = _
  exact evaluate_rawF i hi r q w

end
end Higman.RopeTrick

namespace Higman
variable {G : Type u} [Group G]

namespace IsBenign
variable {A B : Subgroup G}

theorem comap {D : Type u} [Group D] [Group.IsFinitelyPresented D]
    (hA : IsBenign A) (f : D →* G) : IsBenign (A.comap f) := by
  obtain ⟨n,p,hp,_⟩ := Group.IsFinitelyPresented.out (G := D)
  have : Group.FG D := Group.fg_of_surjective hp
  obtain ⟨K,_,_,i,_,L,hL,hLi⟩ := hA
  refine ⟨D × K,inferInstance,finitelyPresented_prod,
    (MonoidHom.id D).prod (i.comp f),?_,(⊤ : Subgroup D).prod L,
    Group.FG.out.prod hL,?_⟩
  · intro x y h
    exact congrArg Prod.fst h
  · ext x
    change (x ∈ (⊤ : Subgroup D) ∧ i (f x) ∈ L) ↔ f x ∈ A
    simpa only [Subgroup.mem_top,true_and,Subgroup.mem_comap] using
      (show f x ∈ L.comap i ↔ f x ∈ A by rw [hLi])

end IsBenign

end Higman

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.Benign
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section UniversalFinitelyPresentedProof
universe u v w x

namespace Higman.CentralExtension
open Monoid Coprod Multiplicative
variable {G : Type u} [Group G] (A : Subgroup G)

abbrev rawProjection : G ∗ Multiplicative ℤ →* CentralExtension G A :=
  (HNNExtension.con G A A (MulEquiv.refl A)).mk'

end Higman.CentralExtension

namespace Higman.HNNTransport
open HNNExtension
variable {G : Type u} [Group G] {K : Type v} [Group K]
  {A B : Subgroup G} {C D : Subgroup K} (φ : A ≃* B) (ψ : C ≃* D)
  (i : G →* K) (hA : C.comap i = A) (hB : D.comap i = B)
  (hφ : ∀ a : A, i (φ a) = ψ ⟨i a,show i a ∈ C from hA.symm ▸ a.2⟩)

def map : HNNExtension G A B φ →* HNNExtension K C D ψ :=
  HNNExtension.lift (HNNExtension.of.comp i) HNNExtension.t (by
    intro a
    simpa only [MonoidHom.comp_apply,hφ a] using
      HNNExtension.t_mul_of (φ := ψ) ⟨i a,show i a ∈ C from hA.symm ▸ a.2⟩)

@[simp] theorem map_of (g : G) : map φ ψ i hA hφ (HNNExtension.of g) =
    HNNExtension.of (i g) := by simp [map]

@[simp] theorem map_t : map φ ψ i hA hφ HNNExtension.t = HNNExtension.t := by simp [map]

def mapWord (r : NormalWord.ReducedWord G A B) : NormalWord.ReducedWord K C D where
  head := i r.head
  toList := r.toList.map (fun p ↦ (p.1,i p.2))
  chain := by
    apply (List.isChain_map _).mpr
    apply r.chain.imp
    intro a b hab hmem
    apply hab
    rcases Int.units_eq_one_or a.1 with ha | ha
    · have hm : i a.2 ∈ C := by simpa [ha,HNNExtension.toSubgroup] using hmem
      have hm' : a.2 ∈ A := hA ▸ hm
      simpa [ha,HNNExtension.toSubgroup] using hm'
    · have hm : i a.2 ∈ D := by simpa [ha,HNNExtension.toSubgroup] using hmem
      have hm' : a.2 ∈ B := hB ▸ hm
      simpa [ha,HNNExtension.toSubgroup] using hm'

@[simp] theorem mapWord_prod (r : NormalWord.ReducedWord G A B) :
    (mapWord i hA hB r).prod ψ = map φ ψ i hA hφ (r.prod φ) := by
  simp [NormalWord.ReducedWord.prod,mapWord,map_list_prod,List.map_map,Function.comp_def]

include hB

theorem mem_base_of_map_mem_base (x : HNNExtension G A B φ)
    (hx : map φ ψ i hA hφ x ∈ (HNNExtension.of : K →* HNNExtension K C D ψ).range) :
    x ∈ (HNNExtension.of : G →* HNNExtension G A B φ).range := by
  obtain ⟨d⟩ := NormalWord.TransversalPair.nonempty G A B
  let r := NormalWord.equiv φ d x
  have hr : r.prod φ = x := (NormalWord.equiv φ d).symm_apply_apply x
  have hm : (mapWord i hA hB r.toReducedWord).prod ψ ∈ HNNExtension.of.range := by
    rw [mapWord_prod φ ψ i hA hB hφ]
    rw [hr]
    exact hx
  have hn := HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range ψ
    (mapWord i hA hB r.toReducedWord) hm
  have hnil : r.toList = [] := by simpa [mapWord] using hn
  refine ⟨r.head,?_⟩
  rw [← hr]
  simp [NormalWord.ReducedWord.prod,hnil]

theorem map_injective (hi : Function.Injective i) : Function.Injective (map φ ψ i hA hφ) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm _ bot_le
  intro x hx
  have hm : map φ ψ i hA hφ x ∈ HNNExtension.of.range := by
    change map φ ψ i hA hφ x = 1 at hx
    rw [hx]
    exact Subgroup.one_mem _
  obtain ⟨g,rfl⟩ := mem_base_of_map_mem_base φ ψ i hA hB hφ x hm
  change map φ ψ i hA hφ (HNNExtension.of g) = 1 at hx
  rw [map_of] at hx
  have hg : i g = 1 := HNNExtension.of_injective (φ := ψ) (hx.trans (map_one _).symm)
  have hg' : g = 1 := hi (hg.trans (map_one i).symm)
  rw [Subgroup.mem_bot,hg',map_one]

end Higman.HNNTransport

namespace Higman.HNNSubgroup
open HNNExtension
variable {G : Type u} [Group G] {A B : Subgroup G} (φ : A ≃* B)
  (S : Subgroup G) (hS : ∀ a : A, (φ a : G) ∈ S ↔ (a : G) ∈ S)

def restricted : A.comap S.subtype ≃* B.comap S.subtype where
  toFun a := ⟨⟨φ ⟨a,a.2⟩,(hS ⟨a,a.2⟩).mpr a.1.2⟩,(φ ⟨a,a.2⟩).2⟩
  invFun b := ⟨⟨φ.symm ⟨b,b.2⟩,(hS (φ.symm ⟨b,b.2⟩)).mp (by simp)⟩,
    (φ.symm ⟨b,b.2⟩).2⟩
  left_inv a := by apply Subtype.ext; apply Subtype.ext; exact congrArg (fun z : A ↦ (z : G)) (φ.symm_apply_apply ⟨a,a.2⟩)
  right_inv b := by apply Subtype.ext; apply Subtype.ext; exact congrArg (fun z : B ↦ (z : G)) (φ.apply_symm_apply ⟨b,b.2⟩)
  map_mul' a b := by apply Subtype.ext; apply Subtype.ext; exact congrArg (fun z : B ↦ (z : G)) (φ.map_mul ⟨a,a.2⟩ ⟨b,b.2⟩)

def inclusion : HNNExtension S (A.comap S.subtype) (B.comap S.subtype)
    (restricted φ S hS) →* HNNExtension G A B φ :=
  HNNTransport.map (restricted φ S hS) φ S.subtype rfl (fun _ ↦ rfl)

@[simp] theorem inclusion_of (s : S) :
    inclusion φ S hS (HNNExtension.of s) = HNNExtension.of (s : G) := by
  exact HNNTransport.map_of _ _ _ _ _ s

@[simp] theorem inclusion_t : inclusion φ S hS HNNExtension.t = HNNExtension.t := by
  exact HNNTransport.map_t _ _ _ _ _

end Higman.HNNSubgroup

end UniversalFinitelyPresentedProof

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.FiniteHNN
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v w x

namespace Higman.HNN
open Monoid Coprod Multiplicative
variable {G : Type u} [Group G] {A B : Subgroup G} (φ : A ≃* B)

def relation (a : A) : G ∗ Multiplicative ℤ :=
  (inr (ofAdd 1) * inl (a : G)) * (inl (φ a : G) * inr (ofAdd 1))⁻¹

end Higman.HNN

namespace Higman

structure PartialIso (G : Type u) [Group G] where
  source : Subgroup G
  target : Subgroup G
  equiv : source ≃* target

namespace PartialIso
variable {G : Type u} [Group G] {K : Type u} [Group K]

noncomputable def map (p : PartialIso G) (i : G →* K) (hi : Function.Injective i) :
    PartialIso K where
  source := p.source.map i
  target := p.target.map i
  equiv := ((p.source.equivMapOfInjective i hi).symm.trans p.equiv).trans
    (p.target.equivMapOfInjective i hi)

@[simp] theorem map_equiv (p : PartialIso G) (i : G →* K) (hi : Function.Injective i)
    (a : p.source) :
    ((p.map i hi).equiv (p.source.equivMapOfInjective i hi a) : K) = i (p.equiv a) := by
  change i (p.equiv ((p.source.equivMapOfInjective i hi).symm
    (p.source.equivMapOfInjective i hi a))) = i (p.equiv a)
  rw [MulEquiv.symm_apply_apply]

def Invariant (p : PartialIso G) (R : Subgroup G) : Prop :=
  ∀ a : p.source, (p.equiv a : G) ∈ R ↔ (a : G) ∈ R

end PartialIso
namespace Orbit
variable {G : Type u} [Group G]

def subgroup (ps : List (PartialIso G)) (S : Set G) : Subgroup G :=
  sInf {R | S ⊆ R ∧ ∀ p ∈ ps, p.Invariant R}

end Orbit
end Higman

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.Markers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section UniversalFinitelyPresentedProof
universe u v w x

namespace Higman.DecoratedMarker
open Monoid Coprod
variable {G : Type u} [Group G] {T : Type v} [Group T] {Q : Type w}

abbrev Kernel (G : Type u) [Group G] (T : Type v) (Q : Type w) :=
  G ∗ FreeGroup (T × Q)
abbrev Base (G : Type u) [Group G] (T : Type v) [Group T] (Q : Type w) :=
  (G × T) ∗ FreeGroup Q

def shift (t : T) : MulAut (Kernel G T Q) :=
  (MulEquiv.refl G).coprodCongr
    (FreeGroup.freeGroupCongr ((Equiv.mulLeft t).prodCongr (Equiv.refl Q)))

@[simp] theorem shift_inl (t : T) (g : G) : shift t (inl g : Kernel G T Q) = inl g := rfl
@[simp] theorem shift_inr_of (t s : T) (q : Q) :
    shift t (inr (FreeGroup.of (s,q)) : Kernel G T Q) = inr (FreeGroup.of (t*s,q)) := rfl

def shifts : T →* MulAut (Kernel G T Q) where
  toFun := shift
  map_one' := by
    apply MulEquiv.toMonoidHom_injective
    apply Coprod.hom_ext
    · apply MonoidHom.ext
      intro g
      simp
    · apply FreeGroup.ext_hom
      rintro ⟨s,q⟩
      simp
  map_mul' t s := by
    apply MulEquiv.toMonoidHom_injective
    apply Coprod.hom_ext
    · apply MonoidHom.ext
      intro g
      simp
    · apply FreeGroup.ext_hom
      rintro ⟨r,q⟩
      simp [mul_assoc]

abbrev ShiftGroup (G : Type u) [Group G] (T : Type v) [Group T] (Q : Type w) :=
  (Kernel G T Q) ⋊[shifts] T

def coefficient : G →* Base G T Q := inl.comp (MonoidHom.inl G T)
def translation : T →* Base G T Q := inl.comp (MonoidHom.inr G T)
def marker (t : T) (q : Q) : Base G T Q :=
  translation t * inr (FreeGroup.of q) * (translation t)⁻¹

def inclusion : Kernel G T Q →* Base G T Q :=
  Coprod.lift coefficient (FreeGroup.lift (fun p ↦ marker p.1 p.2))

@[simp] theorem inclusion_inl (g : G) : inclusion (inl g : Kernel G T Q) = coefficient g := by
  simp [inclusion]
@[simp] theorem inclusion_inr_of (t : T) (q : Q) :
    inclusion (inr (FreeGroup.of (t,q)) : Kernel G T Q) = marker t q := by
  simp [inclusion]

lemma commute_coefficient_translation (g : G) (t : T) :
    Commute (coefficient g : Base G T Q) (translation t) :=
  (MonoidHom.commute_inl_inr g t).map inl

lemma test_commute (g : G) (t : T) :
    Commute (SemidirectProduct.inl (inl g) : ShiftGroup G T Q)
      (SemidirectProduct.inr t) := by
  apply SemidirectProduct.ext
  · change inl g * shifts (1 : T) 1 = 1 * shifts t (inl g)
    simp only [map_one, mul_one, one_mul]
    rfl
  · change (1 : T) * t = t * 1
    simp

def test : Base G T Q →* ShiftGroup G T Q :=
  Coprod.lift
    ((SemidirectProduct.inl.comp inl).noncommCoprod SemidirectProduct.inr test_commute)
    (FreeGroup.lift (fun q ↦ SemidirectProduct.inl (inr (FreeGroup.of (1,q)))))

@[simp] theorem test_coefficient (g : G) : test (coefficient g : Base G T Q) =
    SemidirectProduct.inl (inl g) := by simp [test,coefficient]
@[simp] theorem test_translation (t : T) : test (translation t : Base G T Q) =
    SemidirectProduct.inr t := by simp [test,translation]
@[simp] theorem test_inr_of (q : Q) : test (inr (FreeGroup.of q) : Base G T Q) =
    SemidirectProduct.inl (inr (FreeGroup.of (1,q))) := by simp [test]
@[simp] theorem test_marker (t : T) (q : Q) : test (marker t q : Base G T Q) =
    SemidirectProduct.inl (inr (FreeGroup.of (t,q))) := by
  simp only [marker,map_mul,map_inv,test_translation,test_inr_of]
  rw [← map_inv,← SemidirectProduct.inl_aut]
  change SemidirectProduct.inl (inr (FreeGroup.of (t * 1, q))) = _
  rw [mul_one]

@[simp] theorem test_comp : (test (G := G) (T := T) (Q := Q)).comp inclusion =
    SemidirectProduct.inl := by
  apply Coprod.hom_ext
  · apply MonoidHom.ext
    intro g
    simp
  · apply FreeGroup.ext_hom
    rintro ⟨t,q⟩
    simp

lemma inclusion_shift (t : T) :
    (inclusion (G := G) (Q := Q)).comp (shifts t).toMonoidHom =
      (MulAut.conj (translation t)).toMonoidHom.comp inclusion := by
  apply Coprod.hom_ext
  · apply MonoidHom.ext
    intro g
    simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,shifts,MonoidHom.coe_mk,
      OneHom.coe_mk,shift_inl,inclusion_inl,MulAut.conj_apply]
    rw [← (commute_coefficient_translation g t).eq,mul_inv_cancel_right]
  · apply FreeGroup.ext_hom
    rintro ⟨s,q⟩
    simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,shifts,MonoidHom.coe_mk,
      OneHom.coe_mk,shift_inr_of,inclusion_inr_of,MulAut.conj_apply,marker,map_mul,map_inv]
    group

def inverse : ShiftGroup G T Q →* Base G T Q :=
  SemidirectProduct.lift inclusion translation inclusion_shift

@[simp] theorem inverse_inl (x : Kernel G T Q) :
    inverse (SemidirectProduct.inl x) = inclusion x := by simp [inverse]
@[simp] theorem inverse_inr (t : T) :
    inverse (SemidirectProduct.inr t : ShiftGroup G T Q) = translation t := by simp [inverse]

@[simp] theorem inverse_comp_test : (inverse (G := G) (T := T) (Q := Q)).comp test =
    MonoidHom.id _ := by
  apply Coprod.hom_ext
  · apply MonoidHom.ext
    rintro ⟨g,t⟩
    have he : (inl (g,t) : Base G T Q) = coefficient g * translation t := by
      rw [coefficient,translation,MonoidHom.comp_apply,MonoidHom.comp_apply,← map_mul]
      simp
    change inverse (test (inl (g,t))) = inl (g,t)
    rw [he]
    simp
  · apply FreeGroup.ext_hom
    intro q
    simp only [MonoidHom.comp_apply,MonoidHom.id_apply,test_inr_of,inverse_inl,
      inclusion_inr_of,marker,map_one,one_mul,inv_one,mul_one]

@[simp] theorem test_comp_inverse : (test (G := G) (T := T) (Q := Q)).comp inverse =
    MonoidHom.id _ := by
  apply SemidirectProduct.hom_ext
  · apply MonoidHom.ext
    intro x
    simp only [MonoidHom.comp_apply,inverse_inl,MonoidHom.id_apply]
    exact DFunLike.congr_fun test_comp x
  · apply MonoidHom.ext
    intro t
    simp

def decomposition : Base G T Q ≃* ShiftGroup G T Q :=
  MonoidHom.toMulEquiv test inverse inverse_comp_test test_comp_inverse

end Higman.DecoratedMarker

namespace Higman.DecoratedFreeBasis
open Monoid Coprod
variable {G : Type*} [Group G] {X : Type*}

def inclusion (w : X → G) : FreeGroup X →* G ∗ FreeGroup X :=
  FreeGroup.lift (fun x ↦ inl (w x) * inr (FreeGroup.of x))

@[simp] theorem inclusion_of (w : X → G) (x : X) :
    inclusion w (FreeGroup.of x) = inl (w x) * inr (FreeGroup.of x) := by
  simp [inclusion]

@[simp] theorem projection_comp (w : X → G) :
    (Coprod.snd : G ∗ FreeGroup X →* FreeGroup X).comp (inclusion w) = MonoidHom.id _ := by
  apply FreeGroup.ext_hom
  intro x
  simp

def twist (w : X → G) : MulAut (G ∗ FreeGroup X) :=
  MonoidHom.toMulEquiv
    (Coprod.lift inl (inclusion w))
    (Coprod.lift inl (inclusion (fun x ↦ (w x)⁻¹)))
    (by
      apply Coprod.hom_ext
      · apply MonoidHom.ext
        intro g
        simp
      · apply FreeGroup.ext_hom
        intro x
        simp)
    (by
      apply Coprod.hom_ext
      · apply MonoidHom.ext
        intro g
        simp
      · apply FreeGroup.ext_hom
        intro x
        simp)

@[simp] theorem twist_inl (w : X → G) (g : G) : twist w (inl g) = inl g := by
  simp [twist]
@[simp] theorem twist_inr_of (w : X → G) (x : X) : twist w (inr (FreeGroup.of x)) =
    inl (w x) * inr (FreeGroup.of x) := by simp [twist]

end Higman.DecoratedFreeBasis

namespace Higman.MarkerEmbedding
open Monoid Coprod DecoratedMarker
variable {G : Type u} [Group G] {D : Type v} [Group D]
    {T : Type w} [Group T] {P Q : Type*}

def index (f : D →* T) (o : P → T) (q : P → Q) (x : D × P) : T × Q :=
  (f x.1 * o x.2,q x.2)

def kernelMap (f : D →* T) (o : P → T) (q : P → Q) (w : P → G) :
    Kernel G D P →* Kernel G T Q :=
  Coprod.lift inl (FreeGroup.lift (fun x : D × P ↦
    inl (w x.2) * inr (FreeGroup.of (index f o q x))))

@[simp] theorem kernelMap_inl (f : D →* T) (o : P → T) (q : P → Q) (w : P → G) (g : G) :
    kernelMap f o q w (inl g) = inl g := by simp [kernelMap]
@[simp] theorem kernelMap_inr_of (f : D →* T) (o : P → T) (q : P → Q) (w : P → G) (x : D × P) :
    kernelMap f o q w (inr (FreeGroup.of x)) =
      inl (w x.2) * inr (FreeGroup.of (index f o q x)) := by simp [kernelMap]

lemma kernelMap_shift (f : D →* T) (o : P → T) (q : P → Q) (w : P → G) (d : D) :
    (kernelMap f o q w).comp (shifts d).toMonoidHom =
      (shifts (f d)).toMonoidHom.comp (kernelMap f o q w) := by
  apply Coprod.hom_ext
  · apply MonoidHom.ext
    intro g
    simp [shifts]
  · apply FreeGroup.ext_hom
    rintro ⟨e,p⟩
    simp [shifts,index,mul_assoc]

def embedding (f : D →* T) (o : P → T) (q : P → Q) (w : P → G) :
    Base G D P →* Base G T Q :=
  inverse.comp ((SemidirectProduct.map (kernelMap f o q w) f
    (kernelMap_shift f o q w)).comp test)

@[simp] theorem embedding_coefficient (f : D →* T) (o : P → T) (q : P → Q) (w : P → G)
    (g : G) : embedding f o q w (coefficient g) = coefficient g := by
  simp [embedding]
@[simp] theorem embedding_translation (f : D →* T) (o : P → T) (q : P → Q) (w : P → G)
    (d : D) : embedding f o q w (translation d) = translation (f d) := by
  simp [embedding]
@[simp] theorem embedding_inr_of (f : D →* T) (o : P → T) (q : P → Q) (w : P → G)
    (p : P) : embedding f o q w (inr (FreeGroup.of p)) = coefficient (w p) * marker (o p) (q p) := by
  simp [embedding,index]
@[simp] theorem embedding_marker (f : D →* T) (o : P → T) (q : P → Q) (w : P → G)
    (d : D) (p : P) : embedding f o q w (marker d p) =
      coefficient (w p) * marker (f d * o p) (q p) := by
  simp only [embedding,MonoidHom.comp_apply,test_marker,SemidirectProduct.map_inl,
    kernelMap_inr_of,inverse_inl,map_mul,inclusion_inl,inclusion_inr_of,index]

theorem kernelMap_injective [Nonempty P] (f : D →* T) (o : P → T) (q : P → Q)
    (w : P → G) (hi : Function.Injective (index f o q)) :
    Function.Injective (kernelMap f o q w) := by
  classical
  let r := Function.invFun (index f o q)
  have hr : Function.LeftInverse r (index f o q) := Function.leftInverse_invFun hi
  let k := Coprod.map (MonoidHom.id G) (FreeGroup.map (index f o q))
  have hk : Function.Injective k := by
    let l := Coprod.map (MonoidHom.id G) (FreeGroup.map r)
    have he : l.comp k = MonoidHom.id _ := by
      apply Coprod.hom_ext
      · apply MonoidHom.ext
        intro g
        simp [l,k]
      · apply FreeGroup.ext_hom
        intro x
        simp [l,k,hr x]
    apply Function.Injective.of_comp (f := l)
    rw [← MonoidHom.coe_comp,he]
    exact Function.injective_id
  have he : kernelMap f o q w = k.comp (DecoratedFreeBasis.twist (w ∘ Prod.snd)).toMonoidHom := by
    apply Coprod.hom_ext
    · apply MonoidHom.ext
      intro g
      simp [k]
    · apply FreeGroup.ext_hom
      intro x
      simp [k]
  rw [he]
  exact hk.comp (DecoratedFreeBasis.twist (w ∘ Prod.snd)).injective

theorem embedding_injective [Nonempty P] (f : D →* T) (hf : Function.Injective f)
    (o : P → T) (q : P → Q) (w : P → G) (hi : Function.Injective (index f o q)) :
    Function.Injective (embedding f o q w) := by
  have hk := kernelMap_injective f o q w hi
  have hm : Function.Injective (SemidirectProduct.map (kernelMap f o q w) f
      (kernelMap_shift f o q w)) := by
    intro x y he
    apply SemidirectProduct.ext
    · exact hk (congrArg SemidirectProduct.left he)
    · exact hf (congrArg SemidirectProduct.right he)
  exact (decomposition (G := G) (T := T) (Q := Q)).symm.injective.comp
    (hm.comp (decomposition (G := G) (T := D) (Q := P)).injective)

theorem index_injective (f : D →* T) (hf : Function.Injective f) (o : P → T)
    (q : P → Q) (hq : Function.Injective q) : Function.Injective (index f o q) := by
  rintro ⟨d,p⟩ ⟨e,r⟩ he
  obtain rfl : p = r := hq (congrArg Prod.snd he)
  have hd : f d * o p = f e * o p := congrArg Prod.fst he
  exact Prod.ext (hf (mul_right_cancel hd)) rfl

end Higman.MarkerEmbedding

end UniversalFinitelyPresentedProof

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.MarkerMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v w x

namespace Higman.FreeBasis

section
variable {X : Type*}

noncomputable def erase (S : Set X) : FreeGroup X →* FreeGroup X := by
  classical
  exact FreeGroup.lift (fun x ↦ if x ∈ S then FreeGroup.of x else 1)

open Classical in
@[simp] theorem erase_of (S : Set X) (x : X) : erase S (FreeGroup.of x) =
    if x ∈ S then FreeGroup.of x else 1 := by
  classical
  simp [erase]

abbrev span (S : Set X) : Subgroup (FreeGroup X) := Subgroup.closure (FreeGroup.of '' S)

end

end Higman.FreeBasis

namespace Higman.MarkerEmbedding

section
open Monoid Coprod DecoratedMarker
variable {G : Type u} [Group G] {D : Type v} [Group D]
    {T : Type w} [Group T] {P Q : Type*}

@[simp] theorem test_embedding (f : D →* T) (o : P → T) (q : P → Q)
    (w : P → G) (x : Base G D P) :
    test (embedding f o q w x) =
      SemidirectProduct.map (kernelMap f o q w) f (kernelMap_shift f o q w) (test x) := by
  change (test.comp inverse) _ = _
  rw [test_comp_inverse]
  rfl

@[simp] theorem embedding_inclusion (f : D →* T) (o : P → T) (q : P → Q)
    (w : P → G) (x : Kernel G D P) :
    embedding f o q w (inclusion x) = inclusion (kernelMap f o q w x) := by
  simp only [embedding,MonoidHom.comp_apply]
  rw [← MonoidHom.comp_apply (test : Base G D P →* _),test_comp]
  simp

def decoratedSubgroup (v : T × Q → G) (V : Set (T × Q)) : Subgroup (Base G T Q) :=
  (FreeBasis.span V).map (inclusion.comp (DecoratedFreeBasis.inclusion v))

end

open DecoratedMarker
variable {G : Type u} [Group G] {T : Type v} [Group T] {Q : Type w}
  {D : Type*} [Group D] {P : Type*}

def pullDecoration (f : D →* T) (o : P → T) (q : P → Q) (w : P → G)
    (v : T × Q → G) (x : D × P) : G := v (index f o q x) * (w x.2)⁻¹

@[simp] lemma embedding_decorated (f : D →* T) (o : P → T) (q : P → Q) (w : P → G)
    (v : T × Q → G) (x : D × P) :
    embedding f o q w (coefficient (pullDecoration f o q w v x) * marker x.1 x.2) =
      coefficient (v (index f o q x)) * marker (index f o q x).1 (index f o q x).2 := by
  rw [map_mul,embedding_coefficient,embedding_marker,← mul_assoc,← map_mul]
  simp [pullDecoration,index]

end Higman.MarkerEmbedding

namespace Higman.PartialIso
variable {H : Type u} [Group H] {G : Type u} [Group G]

noncomputable def ofEmbeddings (i j : H →* G) (hi : Function.Injective i)
    (hj : Function.Injective j) : PartialIso G where
  source := i.range
  target := j.range
  equiv := (MonoidHom.ofInjective hi).symm.trans (MonoidHom.ofInjective hj)

@[simp] theorem ofEmbeddings_apply (i j : H →* G) (hi : Function.Injective i)
    (hj : Function.Injective j) (x : H) :
    ((ofEmbeddings i j hi hj).equiv (MonoidHom.ofInjective hi x) : G) = j x := by
  change j ((MonoidHom.ofInjective hi).symm ((MonoidHom.ofInjective hi) x)) = j x
  rw [MulEquiv.symm_apply_apply]

end Higman.PartialIso
namespace Higman.MarkerMachine
open DecoratedMarker MarkerEmbedding

structure Edge (G T : Type u) [Group G] [Group T] (Q : Type u) where
  Domain : Type u
  [domainGroup : Group Domain]
  inputLinear : Domain →* T
  outputLinear : Domain →* T
  input_injective : Function.Injective inputLinear
  output_injective : Function.Injective outputLinear
  inputOffset : T
  outputOffset : T
  inputState : Q
  outputState : Q
  weight : G

attribute [instance] Edge.domainGroup
variable {G T Q : Type u} [Group G] [Group T]

namespace Edge
variable (e : Edge G T Q)

def input (d : e.Domain) : T × Q := (e.inputLinear d * e.inputOffset,e.inputState)
def output (d : e.Domain) : T × Q := (e.outputLinear d * e.outputOffset,e.outputState)

def inputMap : Base G e.Domain Unit →* Base G T Q :=
  embedding e.inputLinear (fun _ ↦ e.inputOffset) (fun _ ↦ e.inputState) (fun _ ↦ 1)
def outputMap : Base G e.Domain Unit →* Base G T Q :=
  embedding e.outputLinear (fun _ ↦ e.outputOffset) (fun _ ↦ e.outputState) (fun _ ↦ e.weight)

lemma input_index_injective : Function.Injective
    (index e.inputLinear (fun _ : Unit ↦ e.inputOffset) (fun _ ↦ e.inputState)) :=
  index_injective e.inputLinear e.input_injective _ _ (Function.injective_of_subsingleton _)
lemma output_index_injective : Function.Injective
    (index e.outputLinear (fun _ : Unit ↦ e.outputOffset) (fun _ ↦ e.outputState)) :=
  index_injective e.outputLinear e.output_injective _ _ (Function.injective_of_subsingleton _)

lemma inputMap_injective : Function.Injective e.inputMap :=
  embedding_injective e.inputLinear e.input_injective _ _ _ e.input_index_injective
lemma outputMap_injective : Function.Injective e.outputMap :=
  embedding_injective e.outputLinear e.output_injective _ _ _ e.output_index_injective

noncomputable def partialIso : PartialIso (Base G T Q) :=
  PartialIso.ofEmbeddings e.inputMap e.outputMap e.inputMap_injective e.outputMap_injective

end Edge
end Higman.MarkerMachine

namespace Higman.MarkerMachine
open DecoratedMarker MarkerEmbedding
variable {G T Q : Type u} [Group G] [Group T]

inductive Reach (es : List (Edge G T Q)) (seed : T × Q) : T × Q → Prop
  | start : Reach es seed seed
  | forward (e : Edge G T Q) (he : e ∈ es) (d : e.Domain) :
      Reach es seed (e.input d) → Reach es seed (e.output d)
  | backward (e : Edge G T Q) (he : e ∈ es) (d : e.Domain) :
      Reach es seed (e.output d) → Reach es seed (e.input d)

def word (v : T × Q → G) (c : T × Q) : Base G T Q :=
  coefficient (v c) * marker c.1 c.2

end Higman.MarkerMachine

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.StackMachines
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v w x

namespace Higman.IntegerStack
variable {E : Type*}

def code (b : ℤ) (d : E → ℤ) : List E → ℤ
  | [] => 1
  | e :: s => b * code b d s + d e

@[simp] theorem code_nil (b : ℤ) (d : E → ℤ) : code b d [] = 1 := rfl
@[simp] theorem code_cons (b : ℤ) (d : E → ℤ) (e : E) (s : List E) :
    code b d (e :: s) = b * code b d s + d e := rfl

end Higman.IntegerStack

namespace Higman.HistoryMachine
variable {E : Type*} {C : Type*} {D : E → Type*}

inductive Run (input output : (e : E) → D e → C) (initial : C) : List E → C → Prop
  | start : Run input output initial [] initial
  | step {s : List E} (e : E) (z : D e) :
      Run input output initial s (input e z) → Run input output initial (e :: s) (output e z)

variable (input output : (e : E) → D e → C) (initial : C)

@[simp] theorem run_nil (c : C) : Run input output initial [] c ↔ c = initial := by
  constructor
  · intro h
    cases h
    rfl
  · rintro rfl
    exact Run.start

@[simp] theorem run_cons (e : E) (s : List E) (c : C) :
    Run input output initial (e :: s) c ↔
      ∃ z : D e, c = output e z ∧ Run input output initial s (input e z) := by
  constructor
  · intro h
    cases h with
    | step e z h => exact ⟨z,rfl,h⟩
  · rintro ⟨z,rfl,h⟩
    exact Run.step e z h

def Reach (b : ℤ) (digit : E → ℤ) (c : C) (history : ℤ) : Prop :=
  ∃ s, Run input output initial s c ∧ history = IntegerStack.code b digit s

variable (b : ℤ) (digit : E → ℤ) (hb : 2 ≤ b)
  (hd : ∀ e, 2 ≤ digit e ∧ digit e < b) (hinj : Function.Injective digit)

variable {G : Type*} [Group G]

def value (weight : E → G) : List E → G
  | [] => 1
  | e :: s => value weight s * weight e

noncomputable def decoration (weight : E → G) (h : ℤ) : G := by
  classical
  exact if hh : ∃ s, h = IntegerStack.code b digit s then value weight hh.choose else 1

end Higman.HistoryMachine

namespace Higman.RecordedMachine

section
open MarkerMachine
abbrev Counter := Multiplicative ℤ

def scale (b : ℤ) : Counter →* Counter where
  toFun x := Multiplicative.ofAdd (b * x.toAdd)
  map_one' := by simp
  map_mul' x y := by simp [mul_add]

lemma scale_injective (b : ℤ) (hb : b ≠ 0) : Function.Injective (scale b) := by
  intro x y h
  change x.toAdd = y.toAdd
  exact mul_left_cancel₀ hb (congrArg Multiplicative.toAdd h)

variable {G T Q : Type u} [Group G]

def augment (c : T × Q) (h : ℤ) : (T × Counter) × Q := ((c.1,Multiplicative.ofAdd h),c.2)
def forget (c : (T × Counter) × Q) : T × Q := (c.1.1,c.2)
def history (c : (T × Counter) × Q) : ℤ := c.1.2.toAdd

@[simp] lemma forget_augment (c : T × Q) (h : ℤ) : forget (augment c h) = c := rfl
@[simp] lemma history_augment (c : T × Q) (h : ℤ) : history (augment c h) = h := rfl
@[simp] lemma augment_forget (c : (T × Counter) × Q) : augment (forget c) (history c) = c := rfl

variable [Group T]

def edge (e : Edge G T Q) (b digit : ℤ) (hb : b ≠ 0) : Edge G (T × Counter) Q where
  Domain := e.Domain × Counter
  inputLinear := e.inputLinear.prodMap (MonoidHom.id Counter)
  outputLinear := e.outputLinear.prodMap (scale b)
  input_injective := by
    intro x y h
    exact Prod.ext (e.input_injective (congrArg Prod.fst h)) (congrArg (fun p : T × Counter ↦ p.2) h)
  output_injective := by
    intro x y h
    exact Prod.ext (e.output_injective (congrArg Prod.fst h))
      (scale_injective b hb (congrArg Prod.snd h))
  inputOffset := (e.inputOffset,1)
  outputOffset := (e.outputOffset,Multiplicative.ofAdd digit)
  inputState := e.inputState
  outputState := e.outputState
  weight := e.weight

@[simp] lemma edge_input (e : Edge G T Q) (b digit : ℤ) (hb : b ≠ 0) (d : e.Domain) (h : Counter) :
    (edge e b digit hb).input (d,h) = augment (e.input d) h.toAdd := by
  change ((e.inputLinear d, h) * (e.inputOffset, 1), e.inputState) = _
  simp only [Prod.mul_def, mul_one]
  rfl
@[simp] lemma edge_output (e : Edge G T Q) (b digit : ℤ) (hb : b ≠ 0) (d : e.Domain) (h : Counter) :
    (edge e b digit hb).output (d,h) =
      augment (e.output d) (b * h.toAdd + digit) := rfl

variable {E : Type u} [Fintype E] (edges : E → Edge G T Q)
  (b : ℤ) (digit : E → ℤ) (hb : 2 ≤ b)

noncomputable def edgeList : List (Edge G (T × Counter) Q) :=
  Finset.univ.toList.map (fun e ↦ edge (edges e) b (digit e) (by omega))

variable (seed : T × Q)

def Forward (c : (T × Counter) × Q) : Prop :=
  HistoryMachine.Reach (fun e ↦ (edges e).input) (fun e ↦ (edges e).output) seed b digit
    (forget c) (history c)

variable (hd : ∀ e, 2 ≤ digit e ∧ digit e < b) (hinj : Function.Injective digit)

lemma output_injective (e : Edge G T Q) : Function.Injective e.output := by
  intro x y h
  exact e.output_injective (mul_right_cancel (congrArg Prod.fst h))

end

open MarkerMachine DecoratedMarker MarkerEmbedding
variable {G T Q E : Type u} [Group G] [Group T] [Fintype E]
  (edges : E → Edge G T Q) (b : ℤ) (digit : E → ℤ) (hb : 2 ≤ b)
  (seed : T × Q) (hd : ∀ e, 2 ≤ digit e ∧ digit e < b) (hinj : Function.Injective digit)

noncomputable def decoration (c : (T × Counter) × Q) : G :=
  HistoryMachine.decoration b digit (fun e ↦ (edges e).weight) (history c)

end Higman.RecordedMachine

namespace Higman.MarkerEmbedding
open Monoid Coprod DecoratedMarker
variable {G T : Type u} {Q : Type*} [Group G] [Group T]

def coefficientProjection : Base G T Q →* G := Coprod.lift (MonoidHom.fst G T) 1

@[simp] lemma projection_coefficient (g : G) :
    coefficientProjection (coefficient g : Base G T Q) = g := by
  simp [coefficientProjection,coefficient]
@[simp] lemma projection_translation (t : T) :
    coefficientProjection (translation t : Base G T Q) = 1 := by
  simp [coefficientProjection,translation]
@[simp] lemma projection_marker (t : T) (q : Q) :
    coefficientProjection (marker t q : Base G T Q) = 1 := by
  simp [coefficientProjection,marker,translation]

end Higman.MarkerEmbedding

namespace Higman.RecordedMachine
open MarkerMachine
variable {G T Q E : Type u} [Group G] [Group T]
  (edges : E → Edge G T Q) (seed : T × Q) (halt : Q)

def acceptedOutputs : Set G :=
  {g | ∃ s c, HistoryMachine.Run (fun e ↦ (edges e).input) (fun e ↦ (edges e).output)
    seed s c ∧ c.2 = halt ∧ g = HistoryMachine.value (fun e ↦ (edges e).weight) s}

end Higman.RecordedMachine

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.StackPrograms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v w x

namespace Higman.AffineStack

section
open MarkerMachine
abbrev Counter := Multiplicative ℤ

def scale (b : ℤ) : Counter →* Counter where
  toFun h := Multiplicative.ofAdd (b * h.toAdd)
  map_one' := by change Multiplicative.ofAdd (b*0) = Multiplicative.ofAdd 0; simp
  map_mul' x y := by
    change Multiplicative.ofAdd (b*(x.toAdd+y.toAdd)) = Multiplicative.ofAdd (b*x.toAdd+b*y.toAdd)
    rw [mul_add]

lemma scale_injective (b : ℤ) (hb : b ≠ 0) : Function.Injective (scale b) := by
  intro x y h
  apply Multiplicative.toAdd.injective
  exact mul_left_cancel₀ hb (congrArg Multiplicative.toAdd h)

inductive Op (Γ : Type)
  | push (a : Γ) | pop (a : Γ) | peek (a : Γ) | empty | idle

variable {Γ G Q : Type} [Group G]

def Op.Rel : Op Γ → List Γ → List Γ → Prop
  | .push a, s, t => t = a :: s
  | .pop a, s, t => s = a :: t
  | .peek a, s, t => s = t ∧ ∃ r, s = a :: r
  | .empty, s, t => s = [] ∧ t = []
  | .idle, s, t => s = t

def localEdge (b : ℤ) (digit : Γ → ℤ) (hb : b ≠ 0) (p q : Q) (w : G) :
    Op Γ → Edge G Counter Q
  | .push a => ⟨Counter, MonoidHom.id _, scale b, Function.injective_id,
      scale_injective b hb, 1, Multiplicative.ofAdd (digit a),p,q,w⟩
  | .pop a => ⟨Counter, scale b, MonoidHom.id _, scale_injective b hb,
      Function.injective_id, Multiplicative.ofAdd (digit a),1,p,q,w⟩
  | .peek a => ⟨Counter, scale b, scale b, scale_injective b hb,
      scale_injective b hb, Multiplicative.ofAdd (digit a),Multiplicative.ofAdd (digit a),p,q,w⟩
  | .empty => ⟨PUnit,1,1,Function.injective_of_subsingleton _,Function.injective_of_subsingleton _,
      Multiplicative.ofAdd 1,Multiplicative.ofAdd 1,p,q,w⟩
  | .idle => ⟨Counter, MonoidHom.id _,MonoidHom.id _,Function.injective_id,
      Function.injective_id,1,1,p,q,w⟩

instance localEdge_finitelyPresented (b : ℤ) (digit : Γ → ℤ) (hb : b ≠ 0) (p q : Q) (w : G)
    (o : Op Γ) : Group.IsFinitelyPresented (localEdge b digit hb p q w o).Domain := by
  cases o with
  | empty => exact inferInstanceAs (Group.IsFinitelyPresented PUnit)
  | push a | pop a | peek a | idle => exact inferInstanceAs (Group.IsFinitelyPresented Counter)

variable (b : ℤ) (digit : Γ → ℤ) (hb : 2 ≤ b)
  (hd : ∀ a, 2 ≤ digit a ∧ digit a < b) (hi : Function.Injective digit)

def encode (s : List Γ) : Counter := Multiplicative.ofAdd (IntegerStack.code b digit s)

end

section
open MarkerMachine
variable {K Γ G Q : Type} [DecidableEq K] [Group G]

abbrev Stores (K : Type) := K → Counter
abbrev Rest (k : K) := {j : K // j ≠ k} → Counter

def insertLinear {A : Type} [Group A] (k : K) (f : A →* Counter) :
    A × Rest k →* Stores K where
  toFun x j := if h : j = k then f x.1 else x.2 ⟨j,h⟩
  map_one' := by ext j; dsimp; split_ifs <;> simp
  map_mul' x y := by ext j; dsimp; split_ifs <;> simp

@[simp] lemma insertLinear_apply {A : Type} [Group A] (k : K) (f : A →* Counter)
    (x : A × Rest k) (j : K) : insertLinear k f x j =
      if h : j = k then f x.1 else x.2 ⟨j,h⟩ := rfl

lemma insertLinear_injective {A : Type} [Group A] (k : K) (f : A →* Counter)
    (hf : Function.Injective f) : Function.Injective (insertLinear k f) := by
  intro x y h
  apply Prod.ext
  · apply hf
    simpa [insertLinear] using congrFun h k
  · funext j
    simpa [insertLinear,j.property] using congrFun h j.val

def insertOffset (k : K) (a : Counter) : Stores K := fun j ↦ if j = k then a else 1

def liftEdge (k : K) (e : Edge G Counter Q) : Edge G (Stores K) Q where
  Domain := e.Domain × Rest k
  inputLinear := insertLinear k e.inputLinear
  outputLinear := insertLinear k e.outputLinear
  input_injective := insertLinear_injective k e.inputLinear e.input_injective
  output_injective := insertLinear_injective k e.outputLinear e.output_injective
  inputOffset := insertOffset k e.inputOffset
  outputOffset := insertOffset k e.outputOffset
  inputState := e.inputState
  outputState := e.outputState
  weight := e.weight

inductive Action (K Γ : Type)
  | onStack (k : K) (o : Op Γ) | idle

def Action.Rel : Action K Γ → (K → List Γ) → (K → List Γ) → Prop
  | .onStack k o, S, T => ∃ t, o.Rel (S k) t ∧ T = Function.update S k t
  | .idle, S, T => T = S

variable (b : ℤ) (digit : Γ → ℤ) (hb : 2 ≤ b)
  (hd : ∀ a, 2 ≤ digit a ∧ digit a < b) (hi : Function.Injective digit)

def encodeStores (S : K → List Γ) : Stores K := fun k ↦ encode b digit (S k)

def actionEdge (p q : Q) (w : G) : Action K Γ → Edge G (Stores K) Q
  | .onStack k o => liftEdge k (localEdge b digit (by omega) p q w o)
  | .idle => ⟨Stores K,MonoidHom.id _,MonoidHom.id _,Function.injective_id,
      Function.injective_id,1,1,p,q,w⟩

end

open MarkerMachine
variable {K Γ G Q : Type} [DecidableEq K] [Group G]
  (b : ℤ) (digit : Γ → ℤ) (hb : 2 ≤ b)

@[simp] lemma actionEdge_inputState (p q : Q) (w : G) (a : Action K Γ) :
    (actionEdge b digit hb p q w a).inputState = p := by
  cases a with
  | onStack k o => cases o <;> rfl
  | idle => rfl

@[simp] lemma actionEdge_outputState (p q : Q) (w : G) (a : Action K Γ) :
    (actionEdge b digit hb p q w a).outputState = q := by
  cases a with
  | onStack k o => cases o <;> rfl
  | idle => rfl

@[simp] lemma actionEdge_weight (p q : Q) (w : G) (a : Action K Γ) :
    (actionEdge b digit hb p q w a).weight = w := by
  cases a with
  | onStack k o => cases o <;> rfl
  | idle => rfl

end Higman.AffineStack

namespace Higman.StackProgram

section
open AffineStack MarkerMachine
variable {K Γ G Q E : Type} [DecidableEq K] [Group G]

structure Instruction (K Γ G Q : Type) where
  source : Q
  target : Q
  action : Action K Γ
  weight : G

def Instruction.edge (b : ℤ) (digit : Γ → ℤ) (hb : 2 ≤ b) (i : Instruction K Γ G Q) :
    Edge G (Stores K) Q := actionEdge b digit hb i.source i.target i.weight i.action

inductive Run (prog : E → Instruction K Γ G Q) (seed : (K → List Γ) × Q) :
    List E → ((K → List Γ) × Q) → Prop
  | start : Run prog seed [] seed
  | step {s : List E} (e : E) (S T : K → List Γ) (h : (prog e).action.Rel S T) :
      Run prog seed s (S,(prog e).source) → Run prog seed (e::s) (T,(prog e).target)

variable (prog : E → Instruction K Γ G Q) (seed : (K → List Γ) × Q)
  (b : ℤ) (digit : Γ → ℤ) (hb : 2 ≤ b)
  (hd : ∀ a, 2 ≤ digit a ∧ digit a < b) (hi : Function.Injective digit)

def outputs (halt : Q) : Set G :=
  {g | ∃ s S, Run prog seed s (S,halt) ∧ g = HistoryMachine.value (fun e ↦ (prog e).weight) s}

end

open AffineStack MarkerMachine

end Higman.StackProgram

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.TuringMachines
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section UniversalFinitelyPresentedProof
universe u v w x

namespace Higman.MicroTM2
open Turing Function Relation
variable {K Γ Λ σ : Type} [DecidableEq K]
abbrev Stmt (K Γ Λ σ : Type) := TM2.Stmt (fun _ : K ↦ Γ) Λ σ
abbrev Cfg (K Γ Λ σ : Type) := (K → List Γ) × (Option (Stmt K Γ Λ σ) × σ)

variable (M : Λ → Stmt K Γ Λ σ)

def step : Cfg K Γ Λ σ → Option (Cfg K Γ Λ σ)
  | (_,none,_) => none
  | (S,some q,v) => some <| match q with
    | .push k f r => (update S k (f v :: S k),some r,v)
    | .peek k f r => (S,some r,f v (S k).head?)
    | .pop k f r => (update S k (S k).tail,some r,f v (S k).head?)
    | .load f r => (S,some r,f v)
    | .branch f r t => (S,some (if f v then r else t),v)
    | .goto f => (S,some (M (f v)),v)
    | .halt => (S,none,v)

def translate (c : TM2.Cfg (fun _ : K ↦ Γ) Λ σ) : Cfg K Γ Λ σ :=
  (c.stk,Option.map M c.l,c.var)

def project : Cfg K Γ Λ σ → TM2.Cfg (fun _ : K ↦ Γ) Λ σ
  | (S,none,v) => ⟨none,v,S⟩
  | (S,some q,v) => TM2.stepAux q v S

end Higman.MicroTM2

namespace Higman.TM2StackCompiler
open Turing Function AffineStack StackProgram MicroTM2 Relation
variable {K Γ Λ σ G : Type} [DecidableEq K] [Group G]

def readOp (pop : Bool) : Option Γ → Op Γ
  | none => .empty
  | some a => if pop then .pop a else .peek a

def rawAction (q : Stmt K Γ Λ σ) (v : σ) (a : Option Γ) : Action K Γ :=
  match q with
  | .push k f _ => .onStack k (.push (f v))
  | .peek k _ _ => .onStack k (readOp false a)
  | .pop k _ _ => .onStack k (readOp true a)
  | _ => .idle

def rawTarget (M : Λ → Stmt K Γ Λ σ) (q : Stmt K Γ Λ σ) (v : σ) (a : Option Γ) :
    Option (Stmt K Γ Λ σ) × σ :=
  match q with
  | .push _ _ r => (some r,v)
  | .peek _ f r => (some r,f v a)
  | .pop _ f r => (some r,f v a)
  | .load f r => (some r,f v)
  | .branch f r t => (some (if f v then r else t),v)
  | .goto f => (some (M (f v)),v)
  | .halt => (none,v)

variable (M : Λ → Stmt K Γ Λ σ)

variable (L : Finset Λ) (hL : ∀ l ∈ L, TM2.SupportsStmt L (M l))

include hL in
omit [DecidableEq K] in
lemma target_mem (q : Stmt K Γ Λ σ) (hq : some q ∈ TM2.stmts M L) (v : σ) (a : Option Γ) :
    (rawTarget M q v a).1 ∈ TM2.stmts M L := by
  classical
  have hs : TM2.SupportsStmt L q := by
    obtain ⟨l,hl,hh⟩ := Finset.mem_biUnion.mp (Finset.some_mem_insertNone.mp hq)
    exact TM2.stmts₁_supportsStmt_mono hh (hL l hl)
  cases q with
  | push k f r | peek k f r | pop k f r | load f r =>
    exact TM2.stmts_trans (by simp [TM2.stmts₁,TM2.stmts₁_self]) hq
  | branch f r t =>
    dsimp [rawTarget]
    split_ifs
    · exact TM2.stmts_trans (by simp [TM2.stmts₁,TM2.stmts₁_self]) hq
    · exact TM2.stmts_trans (by simp [TM2.stmts₁,TM2.stmts₁_self]) hq
  | goto f =>
    apply Finset.some_mem_insertNone.mpr
    apply Finset.mem_biUnion.mpr
    exact ⟨f v,hs v,TM2.stmts₁_self⟩
  | halt => exact Finset.none_mem_insertNone

abbrev State := {q : Option (Stmt K Γ Λ σ) // q ∈ TM2.stmts M L} × σ
abbrev Edge := {q : Stmt K Γ Λ σ // some q ∈ TM2.stmts M L} × σ × Option Γ

noncomputable instance instFintypeState [Fintype σ] : Fintype (State M L) := inferInstance
noncomputable instance instFintypeEdge [Fintype σ] [Fintype Γ] : Fintype (Edge M L) := by
  classical
  have : Fintype {q : Stmt K Γ Λ σ // some q ∈ TM2.stmts M L} :=
    Fintype.ofInjective (fun q ↦ (⟨some q.val,q.property⟩ :
      {q : Option (Stmt K Γ Λ σ) // q ∈ TM2.stmts M L})) (by
        intro q r h; exact Subtype.ext (Option.some.inj (congrArg Subtype.val h)))
  exact inferInstance

noncomputable def compile (e : Edge M L) : Instruction K Γ G (State M L) where
  source := (⟨some e.1.val,e.1.property⟩,e.2.1)
  target := (⟨(rawTarget M e.1.val e.2.1 e.2.2).1,target_mem M L hL _ e.1.property _ _⟩,
    (rawTarget M e.1.val e.2.1 e.2.2).2)
  action := rawAction e.1.val e.2.1 e.2.2
  weight := 1

def forget (c : (K → List Γ) × State M L) : Cfg K Γ Λ σ :=
  (c.1,c.2.1.val,c.2.2)

omit [DecidableEq K] in
@[simp] lemma weights_one (s : List (Edge M L)) :
    HistoryMachine.value (fun e ↦ (compile (G := G) M L hL e).weight) s = 1 := by
  induction s with
  | nil => rfl
  | cons e s ih => simpa only [HistoryMachine.value,compile,mul_one] using ih

end Higman.TM2StackCompiler

end UniversalFinitelyPresentedProof

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.HigmanEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v w x

namespace Higman.WordBinary
open Turing.PartrecToTM2
abbrev Letter := Bool × Bool × Bool

def push (a : Letter) (n : ℕ) : ℕ := Nat.bit a.1 (Nat.bit a.2.1 (Nat.bit a.2.2 n))
def code : List Letter → ℕ
  | [] => 1
  | a::w => push a (code w)

def symbol (b : Bool) : Γ' := if b then .bit1 else .bit0

def spelling : List Letter → List Γ'
  | [] => [.bit1]
  | a::w => symbol a.1 :: symbol a.2.1 :: symbol a.2.2 :: spelling w

end Higman.WordBinary

namespace Higman.RangeRecognizer
open Turing ToPartrec PartrecToTM2

def search (r : ℕ → ℕ) (n : ℕ) : Part ℕ :=
  Nat.rfind (fun k ↦ Part.some (decide (r k = n)))

end Higman.RangeRecognizer

noncomputable section
namespace Higman.RecognizingStack
open Turing ToPartrec PartrecToTM2 WordBinary AffineStack StackProgram Function Relation
variable {G : Type} [Group G]

instance instFintypeK'_solutions : Fintype K' := ⟨{.main,.rev,.aux,.stack},by intro k; cases k <;> simp⟩

abbrev MState (c : Code) := TM2StackCompiler.State tr (support c)
abbrev MEdge (c : Code) := TM2StackCompiler.Edge tr (support c)
local instance instFintypeMEdge (c : Code) : Fintype (MEdge c) := by
  exact TM2StackCompiler.instFintypeEdge (K := K') (Γ := Γ') (σ := Option Γ')
    tr (support c)
def mprog (c : Code) : MEdge c → Instruction K' Γ' G (MState c) :=
  TM2StackCompiler.compile tr (support c) (tr_supports c Cont'.halt).2

inductive State (c : Code)
  | ready | first (a : Letter) | second (a : Letter) | machine (q : MState c) | done
  deriving Fintype
inductive Edge (c : Code)
  | first (a : Letter) | second (a : Letter) | third (a : Letter) | enter
  | machine (e : MEdge c) | exit (v : Option Γ')
  deriving Fintype

def initialState (c : Code) : MState c := by
  classical
  exact (⟨some (tr (trNormal c Cont'.halt)),by
    apply Finset.some_mem_insertNone.mpr
    apply Finset.mem_biUnion.mpr
    exact ⟨trNormal c Cont'.halt,(tr_supports c Cont'.halt).1,TM2.stmts₁_self⟩⟩,none)

def finalState (c : Code) (v : Option Γ') : MState c :=
  (⟨none,Finset.none_mem_insertNone⟩,v)

def prog (c : Code) (weight : Letter → G) : Edge c → Instruction K' Γ' G (State c)
  | .first a => ⟨.ready,.first a,.onStack .main (.push (symbol a.2.2)),1⟩
  | .second a => ⟨.first a,.second a,.onStack .main (.push (symbol a.2.1)),1⟩
  | .third a => ⟨.second a,.ready,.onStack .main (.push (symbol a.1)),weight a⟩
  | .enter => ⟨.ready,.machine (initialState c),.idle,1⟩
  | .machine e => ⟨.machine (mprog (G := G) c e).source,.machine (mprog (G := G) c e).target,
      (mprog (G := G) c e).action,1⟩
  | .exit v => ⟨.machine (finalState c v),.done,.idle,1⟩

def store (s : List Γ') : K' → List Γ' := K'.elim s [] [] []
def encoded (w : List Letter) := spelling w ++ [.cons]
def seed (c : Code) : (K' → List Γ') × State c := (store (encoded []),.ready)

def Correct (c : Code) (weight : Letter → G) (g : G) : ((K' → List Γ') × State c) → Prop
  | (S,.ready) => ∃ w, S = store (encoded w) ∧ g = HistoryMachine.value weight w
  | (S,.first a) => ∃ w, S = store (symbol a.2.2 :: encoded w) ∧ g = HistoryMachine.value weight w
  | (S,.second a) => ∃ w, S = store (symbol a.2.1 :: symbol a.2.2 :: encoded w) ∧
      g = HistoryMachine.value weight w
  | (S,.machine q) => ∃ w, g = HistoryMachine.value weight w ∧
      StateTransition.Reaches (MicroTM2.step tr) (MicroTM2.translate tr (init c [code w]))
        (TM2StackCompiler.forget tr (support c) (S,q))
  | (_,.done) => ∃ w, g = HistoryMachine.value weight w ∧ (c.eval [code w]).Dom

end Higman.RecognizingStack

namespace Higman.NormalWords

section
open WordBinary

def encodeLetter : Alphabet × Bool → Letter
  | (.inl a,b) => (false,a,b)
  | (.inr _,b) => (true,false,b)

def generator (a : Letter) : Alphabet := if a.1 then .inr () else .inl a.2.1
def weight (a : Letter) : FreeGroup Alphabet :=
  if a.2.2 then FreeGroup.of (generator a) else (FreeGroup.of (generator a))⁻¹

def encodeWord (w : Raw) : List Letter := w.reverse.map encodeLetter

def conjugator (n : ℕ) : Raw := (Encodable.decode (α := Raw) n).getD []
def conjugated (r : ℕ → Raw) (n : ℕ) : Raw :=
  conjugator n.unpair.1 ++ r n.unpair.2 ++ FreeGroup.invRev (conjugator n.unpair.1)

def enumerate (r : ℕ → Raw) (n : ℕ) : List Letter := encodeWord (conjugated r n)

end

end Higman.NormalWords

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.UniversalPresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section UniversalFinitelyPresentedProof
universe u v w x
noncomputable section

namespace UniversalFInfinity.FreeConjugates

def shift (n : ℤ) : MulAut (FreeGroup ℤ) :=
  FreeGroup.freeGroupCongr (Equiv.addLeft n)

@[simp] lemma shift_of (n k : ℤ) : shift n (FreeGroup.of k) = FreeGroup.of (n+k) := rfl

def shifts : Multiplicative ℤ →* MulAut (FreeGroup ℤ) where
  toFun n := shift n.toAdd
  map_one' := by
    apply MulEquiv.toMonoidHom_injective
    ext k
    simp [shift]
  map_mul' n m := by
    apply MulEquiv.toMonoidHom_injective
    ext k
    simp [shift, add_assoc]

abbrev ShiftGroup := (FreeGroup ℤ) ⋊[shifts] (Multiplicative ℤ)
abbrev Two := FreeGroup Bool
def a : Two := FreeGroup.of false
def p : Two := FreeGroup.of true
def word (i : ℕ) : Two := a ^ i * p * (a ^ i)⁻¹

def test : Two →* ShiftGroup :=
  FreeGroup.lift (fun b => if b then SemidirectProduct.inl (FreeGroup.of 0)
    else SemidirectProduct.inr (Multiplicative.ofAdd 1))

@[simp] lemma test_a : test a = SemidirectProduct.inr (Multiplicative.ofAdd 1) := by
  simp [test,a]
@[simp] lemma test_p : test p = SemidirectProduct.inl (FreeGroup.of 0) := by
  simp [test,p]

lemma test_word (i : ℕ) : test (word i) =
    SemidirectProduct.inl (FreeGroup.of (i : ℤ)) := by
  simp only [word,map_mul,map_pow,map_inv,test_a,test_p]
  rw [← map_pow,← map_inv,← SemidirectProduct.inl_aut]
  congr 1
  change shift ((Multiplicative.ofAdd (1 : ℤ)) ^ i).toAdd (FreeGroup.of 0) = _
  simp

def inclusion : FreeGroup ℕ →* Two := FreeGroup.lift word

lemma test_comp : test.comp inclusion =
    (SemidirectProduct.inl : FreeGroup ℤ →* ShiftGroup).comp (FreeGroup.map Int.ofNat) := by
  apply FreeGroup.ext_hom
  intro i
  simpa only [MonoidHom.comp_apply, inclusion, FreeGroup.lift_apply_of, FreeGroup.map.of]
    using (test_word i).trans (congrArg SemidirectProduct.inl
      (congrArg FreeGroup.of (show (i : ℤ) = Int.ofNat i from rfl)))

lemma inclusion_injective : Function.Injective inclusion := by
  apply Function.Injective.of_comp (f := test)
  rw [← MonoidHom.coe_comp,test_comp]
  exact SemidirectProduct.inl_injective.comp (FreeGroup.map_injective Int.ofNat_injective)

end UniversalFInfinity.FreeConjugates

namespace UniversalFInfinity.CountableOvergroup
open Monoid
variable {C : Type u} [Group C] (c : ℕ → C)

abbrev Base := Coprod C FreeConjugates.Two

def left : FreeGroup ℕ →* Base (C := C) :=
  Coprod.inr.comp FreeConjugates.inclusion

def right : FreeGroup ℕ →* Base (C := C) :=
  FreeGroup.lift (fun i => Coprod.inl (c i) * Coprod.inr (FreeConjugates.word i))

@[simp] lemma left_of (i : ℕ) : left (C := C) (FreeGroup.of i) =
    Coprod.inr (FreeConjugates.word i) := by
  simp only [left,MonoidHom.comp_apply,FreeConjugates.inclusion,FreeGroup.lift_apply_of]

@[simp] lemma right_of (i : ℕ) : right c (FreeGroup.of i) =
    Coprod.inl (c i) * Coprod.inr (FreeConjugates.word i) := by
  simp only [right,FreeGroup.lift_apply_of]

def projection : Base (C := C) →* FreeConjugates.Two :=
  Coprod.lift 1 (MonoidHom.id _)

lemma left_injective : Function.Injective (left (C := C)) :=
  Coprod.inr_injective.comp FreeConjugates.inclusion_injective

lemma projection_right : (projection (C := C)).comp (right c) = FreeConjugates.inclusion := by
  apply FreeGroup.ext_hom
  intro i
  simp [projection,right,FreeConjugates.inclusion]

lemma right_injective : Function.Injective (right c) := by
  apply Function.Injective.of_comp (f := projection)
  rw [← MonoidHom.coe_comp,projection_right]
  exact FreeConjugates.inclusion_injective

noncomputable def associated : (left (C := C)).range ≃* (right c).range :=
  (MonoidHom.ofInjective (left_injective (C := C))).symm.trans
    (MonoidHom.ofInjective (right_injective c))

abbrev Overgroup := HNNExtension (Base (C := C)) (left (C := C)).range (right c).range
  (associated c)

noncomputable def t : Overgroup c := HNNExtension.t

end UniversalFInfinity.CountableOvergroup

end
end UniversalFinitelyPresentedProof

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.SimplexDisk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Metric Topology BigOperators
namespace UniversalFInfinity.SimplexDisk
noncomputable section

def Truncated (n : ℕ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1}
def Positive (n : ℕ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 < x i) ∧ ∑ i, x i < 1}
def sumCLM (n : ℕ) : (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ i, ContinuousLinearMap.proj i
@[simp] lemma sumCLM_apply (n : ℕ) (x : Fin n → ℝ) : sumCLM n x = ∑ i, x i := by
  simp [sumCLM]

lemma truncated_closed (n : ℕ) : IsClosed (Truncated n) := by
  have h : Truncated n = (⋂ i, {x | (0:ℝ) ≤ x i}) ∩ {x | ∑ i, x i ≤ 1} := by
    ext x; simp [Truncated]
  rw [h]
  exact (isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)).inter
    (isClosed_le (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const)

lemma positive_open (n : ℕ) : IsOpen (Positive n) := by
  have h : Positive n = (⋂ i, {x | (0:ℝ) < x i}) ∩ {x | ∑ i, x i < 1} := by
    ext x; simp [Positive]
  rw [h]
  exact (isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)).inter
    (isOpen_lt (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const)

lemma interior_truncated (n : ℕ) : interior (Truncated n) = Positive n := by
  apply Subset.antisymm
  · intro x hx
    have hc : ∀ i, 0 < x i := by
      intro i
      have hh := interior_mono (show Truncated n ⊆ (Function.eval i) ⁻¹' Ici (0:ℝ) from fun _ h => h.1 i) hx
      rw [← (isOpenMap_eval i).preimage_interior_eq_interior_preimage (continuous_apply i),interior_Ici] at hh
      exact hh
    refine ⟨hc,?_⟩
    cases n with
    | zero => simp
    | succ n =>
      have hs : Function.Surjective (sumCLM (n+1)) := by
        intro r
        refine ⟨Pi.single 0 r,?_⟩
        simp
      have hh := interior_mono (show Truncated (n+1) ⊆ (sumCLM (n+1)) ⁻¹' Iic (1:ℝ) from fun _ h => by simpa using h.2) hx
      rw [← ((sumCLM (n+1)).isOpenMap hs).preimage_interior_eq_interior_preimage (sumCLM (n+1)).continuous,interior_Iic] at hh
      simpa only [mem_preimage,mem_Iio,sumCLM_apply] using hh
  · apply (positive_open n).subset_interior_iff.mpr
    exact fun _ h => ⟨fun i => (h.1 i).le,h.2.le⟩

lemma truncated_convex (n : ℕ) : Convex ℝ (Truncated n) := by
  have h : Truncated n = (⋂ i, ((LinearMap.proj i : (Fin n → ℝ) →ₗ[ℝ] ℝ) ⁻¹' Ici 0)) ∩
      (sumCLM n) ⁻¹' Iic 1 := by ext x; simp [Truncated]
  rw [h]
  exact (convex_iInter fun i => (convex_Ici (0:ℝ)).linear_preimage (LinearMap.proj i)).inter
    ((convex_Iic (1:ℝ)).linear_preimage (sumCLM n).toLinearMap)

lemma truncated_bounded (n : ℕ) : Bornology.IsBounded (Truncated n) := by
  apply (isBounded_Icc (a := (0 : Fin n → ℝ)) (b := 1)).subset
  intro x hx
  refine ⟨hx.1,fun i => ?_⟩
  exact (Finset.single_le_sum (fun j _ => hx.1 j) (Finset.mem_univ i)).trans hx.2

lemma positive_nonempty (n : ℕ) : (Positive n).Nonempty := by
  refine ⟨fun _ => 1 / (n+1 : ℝ),fun _ => by positivity,?_⟩
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hn : (0:ℝ) < n+1 := by positivity
  rw [mul_one_div,div_lt_one hn]
  linarith

noncomputable def ambient (n : ℕ) : (Fin n → ℝ) ≃ₜ (Fin n → ℝ) :=
  Classical.choose (exists_homeomorph_image_interior_closure_frontier_eq_unitBall
    (truncated_convex n) (by rw [interior_truncated]; exact positive_nonempty n) (truncated_bounded n))

lemma ambient_positive (n : ℕ) : ambient n '' Positive n = ball 0 1 := by
  simpa only [ambient,interior_truncated] using
    (Classical.choose_spec (exists_homeomorph_image_interior_closure_frontier_eq_unitBall
      (truncated_convex n) (by rw [interior_truncated]; exact positive_nonempty n) (truncated_bounded n))).1
lemma ambient_truncated (n : ℕ) : ambient n '' Truncated n = closedBall 0 1 := by
  simpa only [ambient,(truncated_closed n).closure_eq] using
    (Classical.choose_spec (exists_homeomorph_image_interior_closure_frontier_eq_unitBall
      (truncated_convex n) (by rw [interior_truncated]; exact positive_nonempty n) (truncated_bounded n))).2.1

noncomputable def truncatedDisk (n : ℕ) : Truncated n ≃ₜ closedBall (0 : Fin n → ℝ) 1 :=
  ((ambient n).image (Truncated n)).trans (Homeomorph.setCongr (ambient_truncated n))

noncomputable def simplexTruncated (n : ℕ) : SimplexDisk.Simplex (Fin (n+1)) ≃ₜ Truncated n where
  toFun x := ⟨fun i => x.1 i.succ,fun i => x.2.1 _,by
    have h := x.2.2
    rw [Fin.sum_univ_succ] at h
    linarith [x.2.1 0]⟩
  invFun x := ⟨Fin.cons (1 - ∑ i, x.1 i) x.1,by
    constructor
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact sub_nonneg.mpr x.2.2
      · exact x.2.1 j
    · simp [Fin.sum_univ_succ]⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun j => rfl) i
    have h := x.2.2
    rw [Fin.sum_univ_succ] at h
    change 1 - ∑ i : Fin n, x.1 i.succ = x.1 0
    linarith
  right_inv x := by rfl
  continuous_toFun := (continuous_pi fun i => (continuous_apply i.succ).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact continuous_const.sub (continuous_finsetSum _ fun j _ => (continuous_apply j).comp continuous_subtype_val)
    · exact (continuous_apply j).comp continuous_subtype_val

noncomputable def simplexDisk (n : ℕ) : SimplexDisk.Simplex (Fin (n+1)) ≃ₜ closedBall (0 : Fin n → ℝ) 1 :=
  (simplexTruncated n).trans (truncatedDisk n)

noncomputable def reindex {A B : Type*} [Fintype A] [Fintype B] (e : A ≃ B) :
    SimplexDisk.Simplex A ≃ₜ SimplexDisk.Simplex B where
  toFun x := ⟨fun b => x.1 (e.symm b),fun b => x.2.1 _,(e.symm.sum_comp x.1).trans x.2.2⟩
  invFun x := ⟨fun a => x.1 (e a),fun a => x.2.1 _,(e.sum_comp x.1).trans x.2.2⟩
  left_inv x := by ext a; simp
  right_inv x := by ext b; simp
  continuous_toFun := (continuous_pi fun b => ((continuous_apply (e.symm b)).comp continuous_subtype_val : Continuous (fun x : SimplexDisk.Simplex A => x.1 (e.symm b)))).subtype_mk _
  continuous_invFun := (continuous_pi fun a => ((continuous_apply (e a)).comp continuous_subtype_val : Continuous (fun x : SimplexDisk.Simplex B => x.1 (e a)))).subtype_mk _

lemma reindex_positive {A B : Type*} [Fintype A] [Fintype B] (e : A ≃ B) (x : SimplexDisk.Simplex A) :
    (∀ b, 0 < (reindex e x).1 b) ↔ ∀ a, 0 < x.1 a := by
  constructor
  · intro h a
    change ∀ b, 0 < x.1 (e.symm b) at h
    simpa only [e.symm_apply_apply] using h (e a)
  · intro h b
    change 0 < x.1 (e.symm b)
    exact h _

end
end UniversalFInfinity.SimplexDisk

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.Simplicial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Topology BigOperators

namespace UniversalFInfinity.Simplicial

section
universe u v
variable {V : Type u} (K : PreAbstractSimplicialComplex V)

lemma face_nonempty (s : Face K) : s.1.Nonempty := (K.isRelLowerSet_faces s.2).1

lemma faceMap_injective (s : Face K) : Function.Injective (faceMap K s) := by
  intro x y h
  apply Subtype.ext
  funext v
  have hh := congrArg (fun p : Space K => p.1 v) h
  exact (weight_apply _ _ _).symm.trans (hh.trans (weight_apply _ _ _))

noncomputable def coordinates (s : Finset V) (x : Space K) (h : x.1.support ⊆ s) : SimplexDisk.Simplex s := by
  refine ⟨fun v => x.1 v,fun v => x.2.1 _,?_⟩
  rw [Finset.sum_coe_sort]
  exact (x.1.sum_of_support_subset h _ (fun _ _ => rfl)).symm.trans x.2.2.1

lemma faceMap_coordinates (s : Face K) (x : Space K) (h : x.1.support ⊆ s.1) :
    faceMap K s (coordinates K s.1 x h) = x := by
  classical
  apply Subtype.ext
  ext v
  by_cases hv : v ∈ s.1
  · exact weight_apply _ _ ⟨v,hv⟩
  · change weight s.1 _ v = x.1 v
    rw [weight_apply_not _ _ hv,Finsupp.notMem_support_iff.mp (fun hh => hv (h hh))]

lemma range_faceMap (s : Face K) : Set.range (faceMap K s) = {x | x.1.support ⊆ s.1} := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    exact weight_support_subset _ _
  · intro h
    exact ⟨coordinates K s.1 x h,faceMap_coordinates K s x h⟩

lemma support_eq_iff (s : Face K) (x : SimplexDisk.Simplex s.1) :
    (faceMap K s x).1.support = s.1 ↔ ∀ v, 0 < x.1 v := by
  classical
  constructor
  · intro he v
    have hn : weight s.1 x v ≠ 0 := by
      apply Finsupp.mem_support_iff.mp
      change v.1 ∈ (faceMap K s x).1.support
      rw [he]
      exact v.2
    rw [weight_apply] at hn
    exact lt_of_le_of_ne (x.2.1 v) (Ne.symm hn)
  · intro hp
    apply Finset.Subset.antisymm (weight_support_subset _ _)
    intro v hv
    apply Finsupp.mem_support_iff.mpr
    rw [weight_apply _ _ ⟨v,hv⟩]
    exact ne_of_gt (hp ⟨v,hv⟩)

end

open Set Metric Topology BigOperators
open scoped Classical
universe u
end UniversalFInfinity.Simplicial

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.Milnor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Topology BigOperators

namespace UniversalFInfinity.Simplicial
open Set Metric Topology BigOperators
universe u
variable {V : Type u} (K : PreAbstractSimplicialComplex V)

abbrev Cell (n : ℕ) := {s : Face K // s.1.card = n+1}

def cellOfFace (s : Face K) : Cell K (s.1.card-1) :=
  ⟨s,by have := Finset.card_pos.mpr (face_nonempty K s); omega⟩

def cellEquiv {n : ℕ} (s : Cell K n) : s.1.1 ≃ Fin (n+1) :=
  Fintype.equivFinOfCardEq (by simpa only [Fintype.card_coe] using s.2)

def faceDisk {n : ℕ} (s : Cell K n) : SimplexDisk.Simplex s.1.1 ≃ₜ closedBall (0 : Fin n → ℝ) 1 :=
  (SimplexDisk.reindex (cellEquiv K s)).trans (SimplexDisk.simplexDisk n)

def diskMap {n : ℕ} (s : Cell K n) : C(closedBall (0 : Fin n → ℝ) 1, Space K) :=
  ⟨(faceMap K s.1) ∘ (faceDisk K s).symm,(continuous_faceMap K s.1).comp (faceDisk K s).symm.continuous⟩

lemma diskMap_injective {n : ℕ} (s : Cell K n) : Function.Injective (diskMap K s) :=
  (faceMap_injective K s.1).comp (faceDisk K s).symm.injective

lemma diskMap_range {n : ℕ} (s : Cell K n) : Set.range (diskMap K s) = Set.range (faceMap K s.1) :=
  (faceDisk K s).symm.surjective.range_comp (faceMap K s.1)

def characteristic {n : ℕ} (s : Cell K n) (x : Fin n → ℝ) : Space K := by
  classical
  exact if hx : x ∈ closedBall 0 1 then diskMap K s ⟨x,hx⟩ else diskMap K s ⟨0,by simp⟩

lemma characteristic_disk {n : ℕ} (s : Cell K n) (x : closedBall (0 : Fin n → ℝ) 1) :
    characteristic K s x.1 = diskMap K s x := by simp only [characteristic,dite_eq_left x.2]

end UniversalFInfinity.Simplicial

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.CompactCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Topology BigOperators

open Set Metric Topology
namespace UniversalFInfinity.Cellular
universe u
variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable {C : Set X} [CWComplex C]

omit [T2Space X] in

lemma closedCell_subset_finite_openCells (n : ℕ) (i : RelCWComplex.cell C n) :
    ∃ I : Finset (Σ m, RelCWComplex.cell C m),
      CWComplex.closedCell n i ⊆ ⋃ p ∈ I, CWComplex.openCell p.1 p.2 := by
  classical
  obtain ⟨J,hJ⟩ := CWComplex.cellFrontier_subset_finite_openCell n i
  refine ⟨insert ⟨n,i⟩ ((Finset.range n).sigma J),?_⟩
  intro x hx
  rw [← CWComplex.cellFrontier_union_openCell_eq_closedCell] at hx
  rcases hx with hx | hx
  swap
  · exact Set.mem_iUnion.mpr ⟨⟨n,i⟩,Set.mem_iUnion.mpr ⟨Finset.mem_insert_self _ _,hx⟩⟩
  · have hxx := hJ hx
    simp only [Set.mem_iUnion] at hxx
    obtain ⟨m,hm,j,hj,hx⟩ := hxx
    exact Set.mem_iUnion.mpr ⟨⟨m,j⟩,Set.mem_iUnion.mpr
      ⟨Finset.mem_insert_of_mem (by simp only [Finset.mem_sigma,Finset.mem_range]; exact ⟨hm,hj⟩),hx⟩⟩

lemma cellSelection_closed {I : Type u} (c : I → Σ n, RelCWComplex.cell C n)
    (hc : Function.Injective c) (x : I → X)
    (hx : ∀ i, x i ∈ CWComplex.openCell (c i).1 (c i).2) (S : Set X)
    (hS : S ⊆ Set.range x) : IsClosed S := by
  apply (CWComplex.closed C S ?_).mpr
  · intro n j
    obtain ⟨J,hJ⟩ := closedCell_subset_finite_openCells n j
    have hfinite : (S ∩ CWComplex.closedCell n j).Finite := by
      have hcpre : (c ⁻¹' (J : Set (Σ n, RelCWComplex.cell C n))).Finite :=
        J.finite_toSet.preimage hc.injOn
      apply (hcpre.image x).subset
      rintro y ⟨hyS,hycell⟩
      obtain ⟨i,rfl⟩ := hS hyS
      have hxx := hJ hycell
      simp only [Set.mem_iUnion] at hxx
      obtain ⟨p,hpJ,hxp⟩ := hxx
      have heq : c i = p := by
        by_contra hne
        exact (CWComplex.disjoint_openCell_of_ne hne).notMem_of_mem_left (hx i) hxp
      exact ⟨i,by change c i ∈ J; rw [heq]; exact hpJ,rfl⟩
    exact hfinite.isClosed
  · rintro y hy
    obtain ⟨i,rfl⟩ := hS hy
    exact CWComplex.openCell_subset_complex (c i).1 (c i).2 (hx i)

theorem compact_finitely_many_cells {K : Set X} (hK : IsCompact K) :
    {p : Σ n, RelCWComplex.cell C n | (K ∩ CWComplex.openCell p.1 p.2).Nonempty}.Finite := by
  classical
  let I := {p : Σ n, RelCWComplex.cell C n | (K ∩ CWComplex.openCell p.1 p.2).Nonempty}
  let x : I → X := fun i => i.2.choose
  have hx (i : I) : x i ∈ CWComplex.openCell i.1.1 i.1.2 := i.2.choose_spec.2
  have hxK (i : I) : x i ∈ K := i.2.choose_spec.1
  have hinj : Function.Injective x := by
    intro i j hij
    apply Subtype.ext
    by_contra hne
    exact (CWComplex.disjoint_openCell_of_ne hne).notMem_of_mem_left (hx i) (hij ▸ hx j)
  have hall : ∀ S ⊆ Set.range x, IsClosed S :=
    cellSelection_closed (C := C) Subtype.val Subtype.val_injective x hx
  have hcompact : IsCompact (Set.range x) :=
    hK.of_isClosed_subset (hall _ subset_rfl) (Set.range_subset_iff.mpr hxK)
  have hdiscrete : IsDiscrete (Set.range x) := by
    apply isDiscrete_iff_forall_mem_exists_isClosed.mpr
    intro S hS
    exact ⟨S,hall S hS,Set.inter_eq_left.mpr hS⟩
  have hrange := hcompact.finite hdiscrete
  have : Finite I := (Set.finite_range_iff hinj).mp hrange
  exact Set.toFinite I

theorem compact_bounded_skeleton {K : Set X} (hK : IsCompact K) (hKC : K ⊆ C) :
    ∃ n : ℕ, K ⊆ CWComplex.skeletonLT C n := by
  classical
  let S := {p : Σ n, RelCWComplex.cell C n | (K ∩ CWComplex.openCell p.1 p.2).Nonempty}
  have hS : S.Finite := compact_finitely_many_cells hK
  let I := hS.toFinset
  refine ⟨I.sup (fun p => p.1+1),?_⟩
  intro x hx
  have hxC := hKC hx
  rw [← CWComplex.iUnion_openCell_eq_complex (C := C)] at hxC
  simp only [Set.mem_iUnion] at hxC
  obtain ⟨m,j,hj⟩ := hxC
  have hmem : (⟨m,j⟩ : Σ n, RelCWComplex.cell C n) ∈ I := by
    exact hS.mem_toFinset.mpr ⟨x,hx,hj⟩
  have hm : m+1 ≤ I.sup (fun p => p.1+1) := Finset.le_sup (f := fun p => p.1+1) hmem
  apply CWComplex.skeletonLT_mono (C := C)
    (m := (m : ℕ∞)+1) (n := ((I.sup (fun p => p.1+1) : ℕ) : ℕ∞)) (by exact_mod_cast hm)
  exact CWComplex.closedCell_subset_skeletonLT m j (CWComplex.openCell_subset_closedCell m j hj)

theorem compactMap_bounded_skeleton {A : Type*} [TopologicalSpace A] [CompactSpace A]
    (f : C(A,X)) (hf : ∀ a, f a ∈ C) :
    ∃ n : ℕ, ∀ a, f a ∈ CWComplex.skeletonLT C n := by
  obtain ⟨n,hn⟩ := compact_bounded_skeleton (C := C) (isCompact_range f.continuous)
    (Set.range_subset_iff.mpr hf)
  exact ⟨n,fun a => hn (Set.mem_range_self a)⟩

end UniversalFInfinity.Cellular

open Set Metric Topology
namespace UniversalFInfinity.SphereTopology
abbrev Disk (n : ℕ) := closedBall (0 : Fin n → ℝ) 1
abbrev Sphere (n : ℕ) := sphere (0 : Fin n → ℝ) 1

def boundary (n : ℕ) : C(Sphere n,Disk n) :=
  ⟨fun x => ⟨x.1,sphere_subset_closedBall x.2⟩,continuous_subtype_val.subtype_mk _⟩

lemma sphere_norm {n : ℕ} (x : Sphere n) : ‖x.1‖ = 1 := by
  simpa only [mem_sphere,dist_zero_right] using x.2
lemma disk_norm {n : ℕ} (x : Disk n) : ‖x.1‖ ≤ 1 := by
  simpa only [mem_closedBall,dist_zero_right] using x.2

def cone (n : ℕ) : C(unitInterval × Sphere n,Disk n) := by
  have hm (p : unitInterval × Sphere n) : (p.1:ℝ) • p.2.1 ∈ closedBall (0 : Fin n → ℝ) 1 := by
    simp only [mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_nonneg p.1.2.1,sphere_norm,mul_one]
    exact p.1.2.2
  exact ⟨fun p => ⟨(p.1:ℝ) • p.2.1,hm p⟩,
    ((continuous_subtype_val.comp continuous_fst).smul
      (continuous_subtype_val.comp continuous_snd)).subtype_mk hm⟩

lemma cone_norm {n : ℕ} (p : unitInterval × Sphere n) : ‖(cone n p).1‖ = (p.1:ℝ) := by
  simp only [cone,ContinuousMap.coe_mk,norm_smul,Real.norm_eq_abs,abs_of_nonneg p.1.2.1,sphere_norm,mul_one]

lemma cone_surjective (n : ℕ) [Nonempty (Sphere n)] : Function.Surjective (cone n) := by
  intro x
  by_cases hx : x.1 = 0
  · obtain ⟨s⟩ := ‹Nonempty (Sphere n)›
    refine ⟨(0,s),Subtype.ext ?_⟩
    simp only [cone,ContinuousMap.coe_mk,Set.Icc.coe_zero,zero_smul,hx]
  · let s : Sphere n := ⟨‖x.1‖⁻¹ • x.1,by
      simp only [mem_sphere,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_inv,abs_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]⟩
    refine ⟨(⟨‖x.1‖,norm_nonneg _,disk_norm x⟩,s),Subtype.ext ?_⟩
    change ‖x.1‖ • (‖x.1‖⁻¹ • x.1) = x.1
    rw [smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx),one_smul]

lemma cone_quotient (n : ℕ) [Nonempty (Sphere n)] : IsQuotientMap (cone n) :=
  IsQuotientMap.of_surjective_continuous (cone_surjective n) (cone n).continuous

variable {Y : Type*} [TopologicalSpace Y] {n : ℕ}

def Extends (f : C(Sphere n,Y)) : Prop := ∃ F : C(Disk n,Y), F.comp (boundary n) = f

lemma extends_of_nullhomotopic [Nonempty (Sphere n)] {y : Y} {f : C(Sphere n,Y)}
    (H : (ContinuousMap.const (Sphere n) y).Homotopy f) : Extends f := by
  have hf : Function.FactorsThrough H.toContinuousMap (cone n) := by
    intro p q hpq
    have ht : p.1 = q.1 := Subtype.ext ((cone_norm p).symm.trans ((congrArg (fun z : Disk n => ‖z.1‖) hpq).trans (cone_norm q)))
    by_cases hzero : (p.1:ℝ) = 0
    · have hp : p.1 = 0 := Subtype.ext hzero
      have hq : q.1 = 0 := ht.symm.trans hp
      change H (p.1,p.2) = H (q.1,q.2)
      rw [hp,hq,H.apply_zero,H.apply_zero]
      rfl
    · have hs : p.2 = q.2 := by
        apply Subtype.ext
        have heq := congrArg (fun z : Disk n => z.1) hpq
        change (p.1:ℝ) • p.2.1 = (q.1:ℝ) • q.2.1 at heq
        rw [← ht] at heq
        exact (smul_right_injective _ hzero) heq
      exact congrArg H.toContinuousMap (Prod.ext ht hs)
  let F : C(Disk n,Y) := (cone_quotient n).lift H.toContinuousMap hf
  refine ⟨F,?_⟩
  ext s
  have hh := ContinuousMap.congr_fun ((cone_quotient n).lift_comp H.toContinuousMap hf) (1,s)
  have hcone : cone n (1,s) = boundary n s := by apply Subtype.ext; simp [cone,boundary]
  simpa only [ContinuousMap.comp_apply,hcone,ContinuousMap.Homotopy.coe_toContinuousMap,
    ContinuousMap.Homotopy.apply_one] using hh

lemma nullhomotopic_of_extends {f : C(Sphere n,Y)} (hf : Extends f) :
    ∃ y : Y, Nonempty ((ContinuousMap.const (Sphere n) y).Homotopy f) := by
  obtain ⟨F,hF⟩ := hf
  let z : Disk n := ⟨0,by simp⟩
  refine ⟨F z,⟨{
    toFun := fun p => F (cone n p)
    continuous_toFun := F.continuous.comp (cone n).continuous
    map_zero_left := ?_
    map_one_left := ?_ }⟩⟩
  · intro s
    exact congrArg F (Subtype.ext (by simp [cone,z]))
  · intro s
    have hs : cone n (1,s) = boundary n s := by apply Subtype.ext; simp [cone,boundary]
    rw [hs]
    exact ContinuousMap.congr_fun hF s

lemma extends_of_homotopy [Nonempty (Sphere n)] {f g : C(Sphere n,Y)}
    (H : f.Homotopy g) (hg : Extends g) : Extends f := by
  obtain ⟨y,⟨J⟩⟩ := nullhomotopic_of_extends hg
  exact extends_of_nullhomotopic (J.trans H.symm)

lemma sphere_nonempty (n : ℕ) : Nonempty (Sphere (n+1)) :=
  (NormedSpace.sphere_nonempty.mpr (by norm_num : (0:ℝ) ≤ 1)).coe_sort

end UniversalFInfinity.SphereTopology

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.CellularLifting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Metric Topology BigOperators
open Set Metric Topology


namespace UniversalFInfinity.Cellular
universe u v w

lemma continuous_boundary (n : ℕ) : Continuous (boundary n) :=
  continuous_subtype_val.subtype_mk _

variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable {C : Set X} [CWComplex C]

def characteristic (n : ℕ) (i : RelCWComplex.cell C n) : C(Disk n, X) :=
  ⟨fun x => RelCWComplex.map n i x.1, (RelCWComplex.continuousOn n i).domRestrict⟩

lemma skeleton_mono {m n : ℕ} (h : m ≤ n) :
    Skeleton C m ⊆ Skeleton C n :=
  CWComplex.skeletonLT_mono (by exact_mod_cast h)

lemma sphere_mem_skeleton (n : ℕ) (i : RelCWComplex.cell C n) (x : Sphere n) :
    characteristic n i (boundary n x) ∈ Skeleton C n :=
  CWComplex.cellFrontier_subset_skeletonLT n i ⟨x.1,x.2,rfl⟩

lemma characteristic_mem_skeleton {m n : ℕ} (h : m < n)
    (i : RelCWComplex.cell C m) (x : Disk m) :
    characteristic m i x ∈ Skeleton C n := by
  apply skeleton_mono (Nat.succ_le_of_lt h)
  exact CWComplex.closedCell_subset_skeletonLT m i ⟨x.1,x.2,rfl⟩

lemma openCell_not_skeleton (n : ℕ) (i : RelCWComplex.cell C n) {x : X}
    (hx : x ∈ CWComplex.openCell n i) : x ∉ Skeleton C n :=
  (CWComplex.disjoint_skeletonLT_openCell (C := C) (j := i) le_rfl).notMem_of_mem_right hx

noncomputable section

lemma disk_coord {n : ℕ} (x : Disk n) (i : Fin n) : |x.1 i| ≤ 1 := by
  exact (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).mp
    (mem_closedBall_zero_iff.mp x.2) i

lemma disk_mem {n : ℕ} {x : Fin n → ℝ} (h : ∀ i, |x i| ≤ 1) :
    x ∈ closedBall 0 1 := by
  exact mem_closedBall_zero_iff.mpr
    ((pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).mpr h)

def diskCons {n : ℕ} (x : Disk n) (t : unitInterval) : Disk (n+1) :=
  ⟨Fin.cons (2*t.1-1) x.1, disk_mem (by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero,abs_le]
      constructor <;> linarith [t.2.1,t.2.2]
    · exact disk_coord x j)⟩

lemma continuous_diskCons {n : ℕ} :
    Continuous (fun q : Disk n × unitInterval => diskCons q.1 q.2) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · change Continuous (fun q : Disk n × unitInterval => 2*q.2.1-1)
    fun_prop
  · change Continuous (fun q : Disk n × unitInterval => q.1.1 j)
    exact (continuous_apply j).comp (continuous_subtype_val.comp continuous_fst)

def diskTail {n : ℕ} (x : Disk (n+1)) : Disk n :=
  ⟨Fin.tail x.1,disk_mem (fun i => disk_coord x i.succ)⟩

lemma continuous_diskTail {n : ℕ} : Continuous (@diskTail n) := by
  apply Continuous.subtype_mk
  exact continuous_pi (fun i => (continuous_apply i.succ).comp continuous_subtype_val)

def diskTime {n : ℕ} (x : Disk (n+1)) : unitInterval :=
  ⟨(x.1 0+1)/2,by have h := (abs_le.mp (disk_coord x 0)); constructor <;> linarith⟩

lemma continuous_diskTime {n : ℕ} : Continuous (@diskTime n) := by
  exact (((continuous_apply 0).comp continuous_subtype_val).add continuous_const).div_const 2 |>.subtype_mk _

@[simp] lemma diskTail_cons {n : ℕ} (x : Disk n) (t : unitInterval) :
    diskTail (diskCons x t) = x := by
  apply Subtype.ext
  simp only [diskTail,diskCons,Fin.tail_cons]

@[simp] lemma diskTime_cons {n : ℕ} (x : Disk n) (t : unitInterval) :
    diskTime (diskCons x t) = t := by
  apply Subtype.ext
  simp only [diskTime,diskCons,Fin.cons_zero]
  ring

lemma sphere_iff_coord {n : ℕ} (x : Disk n) :
    x.1 ∈ sphere 0 1 ↔ ∃ i, |x.1 i| = 1 := by
  rw [sphere_pi (0 : Fin n → ℝ) (Or.inl (by norm_num))]
  simp only [Set.mem_inter_iff,Set.mem_iUnion,Set.mem_preimage,Function.eval,
    Pi.zero_apply,mem_sphere_zero_iff_norm,Real.norm_eq_abs,and_iff_left x.2]

lemma cons_mem_sphere_of_boundary {n : ℕ} (x : Sphere n) (t : unitInterval) :
    (diskCons (boundary n x) t).1 ∈ sphere 0 1 := by
  obtain ⟨i,hi⟩ := (sphere_iff_coord (boundary n x)).mp x.2
  exact (sphere_iff_coord _).mpr ⟨i.succ,hi⟩

lemma cons_zero_mem_sphere {n : ℕ} (x : Disk n) :
    (diskCons x 0).1 ∈ sphere 0 1 := by
  apply (sphere_iff_coord _).mpr
  exact ⟨0,by norm_num [diskCons]⟩

lemma cons_one_mem_sphere {n : ℕ} (x : Disk n) :
    (diskCons x 1).1 ∈ sphere 0 1 := by
  apply (sphere_iff_coord _).mpr
  exact ⟨0,by norm_num [diskCons]⟩

lemma sphere_split {n : ℕ} (x : Sphere (n+1)) :
    x.1 0 = -1 ∨ x.1 0 = 1 ∨ (diskTail (boundary (n+1) x)).1 ∈ sphere 0 1 := by
  obtain ⟨i,hi⟩ := (sphere_iff_coord (boundary (n+1) x)).mp x.2
  refine Fin.cases ?_ (fun i hi => ?_) i hi
  · intro h
    rcases abs_eq (by norm_num : (0:ℝ) ≤ 1) |>.mp h with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
  · exact Or.inr (Or.inr ((sphere_iff_coord _).mpr ⟨i,hi⟩))

lemma continuous_liftCover {A : Type u} {Y : Type v} {ι : Type w}
    [TopologicalSpace A] [TopologicalSpace Y] [Finite ι]
    (S : ι → Set A) (f : ∀ i, C(S i,Y))
    (hcompat : ∀ i j x (hi : x ∈ S i) (hj : x ∈ S j), f i ⟨x,hi⟩ = f j ⟨x,hj⟩)
    (hcover : ⋃ i, S i = Set.univ) (hclosed : ∀ i, IsClosed (S i)) :
    Continuous (Set.liftCover S (fun i => f i) hcompat hcover) := by
  rw [continuous_iff_isClosed]
  intro D hD
  rw [Set.preimage_liftCover]
  exact isClosed_iUnion_of_finite fun i => (hclosed i).isClosedMap_subtype_val _ (hD.preimage (f i).continuous)

def cylinderFace (n : ℕ) : Option Bool → Set (Sphere (n+1))
  | none => {x | (diskTail (boundary (n+1) x)).1 ∈ sphere 0 1}
  | some false => {x | x.1 0 = -1}
  | some true => {x | x.1 0 = 1}

lemma cylinderFace_closed (n : ℕ) (i : Option Bool) : IsClosed (cylinderFace n i) := by
  cases i with
  | none =>
    exact isClosed_sphere.preimage
      (continuous_subtype_val.comp (continuous_diskTail.comp (continuous_boundary (n+1))))
  | some b =>
    cases b <;>
      exact isClosed_eq ((continuous_apply 0).comp continuous_subtype_val) continuous_const

lemma cylinderFace_cover (n : ℕ) : ⋃ i, cylinderFace n i = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  rcases sphere_split x with h | h | h
  · exact Set.mem_iUnion.mpr ⟨some false,h⟩
  · exact Set.mem_iUnion.mpr ⟨some true,h⟩
  · exact Set.mem_iUnion.mpr ⟨none,h⟩

variable {Y : Type u} [TopologicalSpace Y]

def pathEndpoint : C(C(unitInterval,Y), Y × Y) :=
  ⟨fun q => (q 0,q 1), (continuous_eval_const 0).prodMk (continuous_eval_const 1)⟩

section CylinderMap
variable {n : ℕ} (a : C(Sphere n,C(unitInterval,Y))) (b : C(Disk n,Y × Y))

def faceTail (i : Option Bool) : C(cylinderFace n i,Disk n) :=
  ⟨fun x => diskTail (boundary (n+1) x.1),
    continuous_diskTail.comp ((continuous_boundary (n+1)).comp continuous_subtype_val)⟩

def faceSphere : C(cylinderFace n none,Sphere n) :=
  ⟨fun x => ⟨(faceTail none x).1,x.2⟩, (continuous_subtype_val.comp (faceTail none).continuous).subtype_mk _⟩

def faceTime (i : Option Bool) : C(cylinderFace n i,unitInterval) :=
  ⟨fun x => diskTime (boundary (n+1) x.1),
    continuous_diskTime.comp ((continuous_boundary (n+1)).comp continuous_subtype_val)⟩

def faceMap : ∀ i : Option Bool, C(cylinderFace n i,Y)
  | none => ⟨fun x => a (faceSphere x) (faceTime none x),
      continuous_eval.comp ((a.continuous.comp faceSphere.continuous).prodMk (faceTime none).continuous)⟩
  | some false => ⟨fun x => (b (faceTail (some false) x)).1,
      continuous_fst.comp (b.continuous.comp (faceTail (some false)).continuous)⟩
  | some true => ⟨fun x => (b (faceTail (some true) x)).2,
      continuous_snd.comp (b.continuous.comp (faceTail (some true)).continuous)⟩

lemma faceTime_eq_zero (x : Sphere (n+1)) (h : x.1 0 = -1) :
    diskTime (boundary (n+1) x) = 0 := by
  apply Subtype.ext
  change (x.1 0+1)/2 = 0
  rw [h]
  norm_num

lemma faceTime_eq_one (x : Sphere (n+1)) (h : x.1 0 = 1) :
    diskTime (boundary (n+1) x) = 1 := by
  apply Subtype.ext
  change (x.1 0+1)/2 = 1
  rw [h]
  norm_num

variable (h : ∀ x, pathEndpoint (a x) = b (boundary n x))

include h in
lemma faceMap_compat (i j : Option Bool) (x : Sphere (n+1))
    (hi : x ∈ cylinderFace n i) (hj : x ∈ cylinderFace n j) :
    faceMap a b i ⟨x,hi⟩ = faceMap a b j ⟨x,hj⟩ := by
  have left (hs : x ∈ cylinderFace n none) (h0 : x.1 0 = -1) :
      faceMap a b none ⟨x,hs⟩ = (b (diskTail (boundary (n+1) x))).1 := by
    change a (faceSphere ⟨x,hs⟩) (diskTime (boundary (n+1) x)) = _
    rw [faceTime_eq_zero x h0]
    exact congrArg Prod.fst (h (faceSphere ⟨x,hs⟩))
  have right (hs : x ∈ cylinderFace n none) (h1 : x.1 0 = 1) :
      faceMap a b none ⟨x,hs⟩ = (b (diskTail (boundary (n+1) x))).2 := by
    change a (faceSphere ⟨x,hs⟩) (diskTime (boundary (n+1) x)) = _
    rw [faceTime_eq_one x h1]
    exact congrArg Prod.snd (h (faceSphere ⟨x,hs⟩))
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some c => cases c; exact left hi hj; exact right hi hj
  | some c =>
    cases c
    · cases j with
      | none => exact (left hj hi).symm
      | some d =>
        cases d
        · rfl
        · have := hi.symm.trans hj; norm_num at this
    · cases j with
      | none => exact (right hj hi).symm
      | some d =>
        cases d
        · have := hi.symm.trans hj; norm_num at this
        · rfl

def cylinderBoundaryMap : C(Sphere (n+1),Y) :=
  ⟨Set.liftCover (cylinderFace n) (fun i => faceMap a b i)
    (faceMap_compat a b h) (cylinderFace_cover n),
    continuous_liftCover _ _ _ _ (cylinderFace_closed n)⟩

lemma cylinderBoundaryMap_face (i : Option Bool) (x : cylinderFace n i) :
    cylinderBoundaryMap a b h x.1 = faceMap a b i x :=
  by
    apply Set.liftCover_coe (S := cylinderFace n) (f := fun i => faceMap a b i)
      (hf := faceMap_compat a b h) (hS := cylinderFace_cover n)

end CylinderMap

end
end UniversalFInfinity.Cellular

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.MilnorControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology

namespace UniversalFInfinity.Milnor

section
open Set Metric Topology BigOperators UniversalFInfinity.Simplicial
open scoped Classical
universe u v
variable {G : Type u} [Group G]

attribute [local instance] OAI.UniversalFInfinity.Milnor.instDecidableEqProdNat_solutions_1
lemma translate_one (s : Finset (ℕ × G)) : translate 1 s = s := by
  simp only [translate,one_mul,Prod.mk.eta,Finset.image_id']

lemma orbitSpan_le (S : Finset (Finset (ℕ × G))) : orbitSpan S ≤ complex G := fun _ h => h.1
lemma orbitSpan_contains (S : Finset (Finset (ℕ × G))) {t : Finset (ℕ × G)}
    (ht : t ∈ complex G) (h : ∃ s ∈ S, t ⊆ s) : t ∈ orbitSpan S := by
  obtain ⟨s,hs,hts⟩ := h
  exact ⟨ht,1,s,hs,by rwa [translate_one]⟩

end
open Set Metric Topology BigOperators UniversalFInfinity.Simplicial
open scoped Classical unitInterval
universe u v
end UniversalFInfinity.Milnor

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.HomotopyProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology

namespace UniversalFInfinity.Milnor

open Set Metric Topology BigOperators UniversalFInfinity.Simplicial
open scoped Classical
universe u v
variable (G : Type u) [Group G]

local instance (priority := 2000) instDecidableEqProdNat_solutions_6_ra4305b_1 (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)
abbrev Stage (S : Shapes G) := Simplicial.Space (stage G S)

def stageFull (S : Shapes G) : C(Stage G S,Space G) :=
  ⟨inclusion _ _ (fun _ h => orbitSpan_le _ h),continuous_inclusion _ _ _⟩

variable {X : Type v} [TopologicalSpace X] [MulAction G X]

def CompactFundamentalSet : Prop :=
  ∃ K : Set X, IsCompact K ∧ ∀ x : X, ∃ g : G, ∃ y ∈ K, x = g • y

end UniversalFInfinity.Milnor

open Set Metric Topology

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.Attachments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Metric Topology BigOperators
open Set Metric Topology

namespace UniversalFInfinity.Attachment
noncomputable section
universe u v w
abbrev Disk (n : ℕ) := closedBall (0 : Fin n → ℝ) 1
abbrev Sphere (n : ℕ) := sphere (0 : Fin n → ℝ) 1
abbrev OpenDisk (n : ℕ) := ball (0 : Fin n → ℝ) 1

def boundary (n : ℕ) : Sphere n → Disk n :=
  fun x => ⟨x.1, sphere_subset_closedBall x.2⟩
def interior (n : ℕ) : OpenDisk n → Disk n :=
  fun x => ⟨x.1, ball_subset_closedBall x.2⟩
lemma continuous_boundary (n : ℕ) : Continuous (boundary n) :=
  continuous_subtype_val.subtype_mk _
lemma continuous_interior (n : ℕ) : Continuous (interior n) :=
  continuous_subtype_val.subtype_mk _
lemma boundary_closedEmbedding (n : ℕ) : IsClosedEmbedding (boundary n) :=
  (continuous_boundary n).isClosedEmbedding (fun _ _ h => Subtype.ext (congrArg (fun z : Disk n => z.1) h))

variable {X : Type u} [TopologicalSpace X] {ι : Type v} {n : ℕ}
variable (a : ι → C(Sphere n,X))

def Space (_a : ι → C(Sphere n,X)) := X ⊕ (Σ _ : ι, OpenDisk n)

noncomputable def quotient : (X ⊕ (Σ _ : ι, Disk n)) → Space a := by
  classical
  intro z
  cases z with
  | inl x => exact Sum.inl x
  | inr p =>
    exact if h : p.2.1 ∈ ball (0 : Fin n → ℝ) 1 then Sum.inr ⟨p.1,⟨p.2.1,h⟩⟩
    else Sum.inl (a p.1 ⟨p.2.1,by
      have hd := p.2.2
      simp only [mem_closedBall,mem_ball,mem_sphere] at *
      exact le_antisymm hd (le_of_not_gt h)⟩)

instance instTopologicalSpaceSpace : TopologicalSpace (Space a) := TopologicalSpace.coinduced (quotient a) inferInstance

@[simp] lemma quotient_inl (x : X) : quotient a (Sum.inl x) = Sum.inl x := rfl

@[simp] lemma quotient_interior (i : ι) (x : OpenDisk n) :
    quotient a (Sum.inr ⟨i,interior n x⟩) = Sum.inr ⟨i,x⟩ := by
  classical
  exact dite_eq_left x.2

@[simp] lemma quotient_boundary (i : ι) (x : Sphere n) :
    quotient a (Sum.inr ⟨i,boundary n x⟩) = Sum.inl (a i x) := by
  classical
  have hx : x.1 ∉ ball (0 : Fin n → ℝ) 1 := by
    simpa only [mem_ball,mem_sphere,x.2,lt_self_iff_false,not_false_eq_true] using
      (sphere_disjoint_ball.notMem_of_mem_left x.2)
  exact dite_eq_right hx

lemma quotient_surjective : Function.Surjective (quotient a) := by
  intro z
  cases z with
  | inl x => exact ⟨Sum.inl x,rfl⟩
  | inr p => exact ⟨Sum.inr ⟨p.1,interior n p.2⟩,quotient_interior a p.1 p.2⟩

lemma continuous_quotient : Continuous (quotient a) := continuous_coinduced_rng

def base : X → Space a := Sum.inl
noncomputable def cell (i : ι) : C(Disk n,Space a) :=
  ⟨fun x => quotient a (Sum.inr ⟨i,x⟩),
    (continuous_quotient a).comp (continuous_inr.comp continuous_sigmaMk)⟩
lemma continuous_base : Continuous (base a) :=
  (continuous_quotient a).comp continuous_inl

@[simp] lemma cell_boundary (i : ι) (x : Sphere n) :
    cell a i (boundary n x) = base a (a i x) := quotient_boundary a i x
@[simp] lemma cell_interior (i : ι) (x : OpenDisk n) :
    cell a i (interior n x) = Sum.inr ⟨i,x⟩ := quotient_interior a i x

lemma continuous_iff {Y : Type w} [TopologicalSpace Y] (f : Space a → Y) :
    Continuous f ↔ Continuous (f ∘ base a) ∧ ∀ i, Continuous (f ∘ cell a i) := by
  change Continuous[TopologicalSpace.coinduced (quotient a) inferInstance,_] f ↔ _
  rw [continuous_coinduced_dom,continuous_sum_dom,continuous_sigma_iff]
  rfl

lemma isClosed_iff (S : Set (Space a)) :
    IsClosed S ↔ IsClosed (base a ⁻¹' S) ∧ ∀ i, IsClosed (cell a i ⁻¹' S) := by
  change @IsClosed _ (TopologicalSpace.coinduced (quotient a) inferInstance) S ↔ _
  rw [isClosed_coinduced,isClosed_sum_iff,isClosed_sigma_iff]
  rfl

lemma cell_preimage_base_image (i : ι) (S : Set X) :
    cell a i ⁻¹' (base a '' S) = boundary n '' ((a i) ⁻¹' S) := by
  classical
  ext d
  by_cases h : d.1 ∈ ball (0 : Fin n → ℝ) 1
  · have hd : d = interior n ⟨d.1,h⟩ := rfl
    rw [hd]
    simp only [Set.mem_preimage,cell_interior,base,Set.mem_image]
    constructor
    · rintro ⟨x,_,hx⟩; cases hx
    · rintro ⟨x,_,hx⟩
      have heq := congrArg (fun d : Disk n => d.1) hx
      have hh : x.1 ∈ ball (0 : Fin n → ℝ) 1 := heq ▸ h
      exact False.elim ((sphere_disjoint_ball.notMem_of_mem_left x.2) hh)
  · let x : Sphere n := ⟨d.1,by
      have hd := d.2
      simp only [mem_closedBall,mem_ball,mem_sphere] at *
      exact le_antisymm hd (le_of_not_gt h)⟩
    have hd : d = boundary n x := rfl
    rw [hd]
    simp only [Set.mem_preimage,cell_boundary,Set.mem_image]
    constructor
    · rintro ⟨y,hy,hyx⟩
      have heq : y = a i x := Sum.inl_injective hyx
      exact ⟨x,heq ▸ hy,rfl⟩
    · rintro ⟨y,hy,hyx⟩
      have heq : y = x := Subtype.ext (congrArg (fun d : Disk n => d.1) hyx)
      subst y
      exact ⟨a i x,hy,rfl⟩

lemma base_isClosedMap : IsClosedMap (base a) := by
  intro S hS
  rw [isClosed_iff]
  constructor
  · have heq : base a ⁻¹' (base a '' S) = S :=
      Set.preimage_image_eq S Sum.inl_injective
    exact heq.symm ▸ hS
  · intro i
    rw [cell_preimage_base_image]
    exact (boundary_closedEmbedding n).isClosedMap _ (hS.preimage (a i).continuous)

lemma base_closedEmbedding : IsClosedEmbedding (base a) :=
  IsClosedEmbedding.of_continuous_injective_isClosedMap
    (continuous_base a) Sum.inl_injective (base_isClosedMap a)

noncomputable def lift {Y : Type w} [TopologicalSpace Y] (f : C(X,Y))
    (g : ι → C(Disk n,Y)) (h : ∀ i x, g i (boundary n x) = f (a i x)) : C(Space a,Y) := by
  classical
  let F : Space a → Y := Sum.elim f (fun p => g p.1 (interior n p.2))
  have hcell (i : ι) : F ∘ cell a i = g i := by
    funext d
    by_cases hd : d.1 ∈ ball (0 : Fin n → ℝ) 1
    · have heq : d = interior n ⟨d.1,hd⟩ := rfl
      rw [heq,Function.comp_apply,cell_interior]
      rfl
    · let x : Sphere n := ⟨d.1,by
        have hm := d.2
        simp only [mem_closedBall,mem_ball,mem_sphere] at *
        exact le_antisymm hm (le_of_not_gt hd)⟩
      have heq : d = boundary n x := rfl
      rw [heq,Function.comp_apply,cell_boundary]
      exact (h i x).symm
  exact ⟨F,(continuous_iff a F).mpr ⟨f.continuous,fun i => by rw [hcell]; exact (g i).continuous⟩⟩

@[simp] lemma lift_base {Y : Type w} [TopologicalSpace Y] (f : C(X,Y))
    (g : ι → C(Disk n,Y)) (h : ∀ i x, g i (boundary n x) = f (a i x)) (x : X) :
    lift a f g h (base a x) = f x := rfl

@[simp] lemma lift_cell {Y : Type w} [TopologicalSpace Y] (f : C(X,Y))
    (g : ι → C(Disk n,Y)) (h : ∀ i x, g i (boundary n x) = f (a i x))
    (i : ι) (d : Disk n) : lift a f g h (cell a i d) = g i d := by
  classical
  by_cases hd : d.1 ∈ ball (0 : Fin n → ℝ) 1
  · have heq : d = interior n ⟨d.1,hd⟩ := rfl
    rw [heq,cell_interior]
    rfl
  · let x : Sphere n := ⟨d.1,by
      have hm := d.2
      simp only [mem_closedBall,mem_ball,mem_sphere] at *
      exact le_antisymm hm (le_of_not_gt hd)⟩
    have heq : d = boundary n x := rfl
    rw [heq,cell_boundary,lift_base,h]

lemma interior_openEmbedding (n : ℕ) : IsOpenEmbedding (interior n) :=
  .inclusion ball_subset_closedBall (isOpen_ball.preimage continuous_subtype_val)

def openCell (i : ι) : OpenDisk n → Space a := fun x => Sum.inr ⟨i,x⟩

lemma openCell_eq (i : ι) : openCell a i = cell a i ∘ interior n := by
  funext x
  exact (cell_interior a i x).symm

lemma quotient_preimage_openCell_image (i : ι) (S : Set (OpenDisk n)) :
    quotient a ⁻¹' (openCell a i '' S) =
      Sum.inr '' (Sigma.mk i '' (interior n '' S)) := by
  classical
  ext q
  cases q with
  | inl x =>
    simp only [Set.mem_preimage,quotient_inl,Set.mem_image]
    constructor
    · rintro ⟨y,_,hy⟩; cases hy
    · rintro ⟨y,_,hy⟩; cases hy
  | inr p =>
    by_cases hp : p.2.1 ∈ ball (0 : Fin n → ℝ) 1
    · have heq : p.2 = interior n ⟨p.2.1,hp⟩ := rfl
      change (∃ x ∈ S, openCell a i x = quotient a (Sum.inr ⟨p.1,p.2⟩)) ↔ _
      rw [heq,quotient_interior]
      constructor
      · rintro ⟨x,hx,he⟩
        have hh : (⟨i,x⟩ : Σ _ : ι, OpenDisk n) = ⟨p.1,⟨p.2.1,hp⟩⟩ := Sum.inr_injective he
        have hh' : (⟨i,interior n x⟩ : Σ _ : ι, Disk n) = ⟨p.1,p.2⟩ :=
          congrArg (fun p : Σ _ : ι, OpenDisk n => (⟨p.1,interior n p.2⟩ : Σ _ : ι, Disk n)) hh
        exact ⟨⟨i,interior n x⟩,⟨interior n x,⟨x,hx,rfl⟩,rfl⟩,congrArg Sum.inr hh'⟩
      · rintro ⟨y,⟨d,⟨x,hx,hxd⟩,hdy⟩,hy⟩
        subst d; subst y
        have hh := Sum.inr_injective hy
        have hi : i = p.1 := congrArg Sigma.fst hh
        subst i
        have hh' : interior n x = interior n ⟨p.2.1,hp⟩ := eq_of_heq (Sigma.mk.inj_iff.mp hh).2
        have he : x = ⟨p.2.1,hp⟩ := (interior_openEmbedding n).injective hh'
        exact ⟨x,hx,by subst x; rfl⟩
    · let x : Sphere n := ⟨p.2.1,by
        have hm := p.2.2
        simp only [mem_closedBall,mem_ball,mem_sphere] at *
        exact le_antisymm hm (le_of_not_gt hp)⟩
      have heq : p.2 = boundary n x := rfl
      change (∃ y ∈ S, openCell a i y = quotient a (Sum.inr ⟨p.1,p.2⟩)) ↔ _
      rw [heq,quotient_boundary]
      constructor
      · rintro ⟨y,_,hy⟩; cases hy
      · rintro ⟨y,⟨d,⟨z,_,hzd⟩,hdy⟩,hy⟩
        subst d; subst y
        have hh := Sum.inr_injective hy
        have hi : i = p.1 := congrArg Sigma.fst hh
        subst i
        have hh' : interior n z = boundary n x := eq_of_heq (Sigma.mk.inj_iff.mp hh).2
        have hh'' := congrArg (fun d : Disk n => d.1) hh'
        exact False.elim (hp (hh'' ▸ z.2))

lemma openCell_openEmbedding (i : ι) : IsOpenEmbedding (openCell a i) := by
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap
  · rw [openCell_eq]
    exact (cell a i).continuous.comp (continuous_interior n)
  · intro x y h
    exact eq_of_heq (Sigma.mk.inj_iff.mp (Sum.inr_injective h)).2
  · intro S hS
    change @IsOpen _ (TopologicalSpace.coinduced (quotient a) inferInstance) _
    rw [isOpen_coinduced,quotient_preimage_openCell_image]
    exact isOpenMap_inr _ (isOpenMap_sigmaMk _ ((interior_openEmbedding n).isOpenMap S hS))

lemma exists_real_extension (f : C(X,ℝ)) :
    ∃ F : C(Space a,ℝ), ∀ x, F (base a x) = f x := by
  classical
  have hi (i : ι) : ∃ g : C(Disk n,ℝ), ∀ x, g (boundary n x) = f (a i x) := by
    obtain ⟨g,hg⟩ := (f.comp (a i)).exists_extension' (boundary_closedEmbedding n)
    exact ⟨g,fun x => congrFun hg x⟩
  choose g hg using hi
  exact ⟨lift a f g hg,fun x => lift_base a f g hg x⟩

def RealSeparated (Y : Type*) [TopologicalSpace Y] : Prop :=
  ∀ x y : Y, x ≠ y → ∃ f : C(Y,ℝ), f x ≠ f y

lemma RealSeparated.t2Space {Y : Type*} [TopologicalSpace Y] (h : RealSeparated Y) :
    T2Space Y := by
  constructor
  intro x y hxy
  obtain ⟨f,hf⟩ := h x y hxy
  exact separated_by_continuous f.continuous hf

lemma realSeparated_of_tychonoff {Y : Type*} [TopologicalSpace Y]
    [T1Space Y] [CompletelyRegularSpace Y] : RealSeparated Y := by
  intro x y hxy
  obtain ⟨f,hf,hfx,hfy⟩ := CompletelyRegularSpace.completely_regular x {y} isClosed_singleton
    (by simpa only [Set.mem_singleton_iff] using hxy)
  refine ⟨⟨fun q => (f q : ℝ),continuous_subtype_val.comp hf⟩,?_⟩
  change (f x : ℝ) ≠ (f y : ℝ)
  rw [hfx,hfy (Set.mem_singleton y)]
  norm_num

lemma exists_interior_separator [T1Space X] (i : ι) (x : OpenDisk n) (z : Space a)
    (hxz : openCell a i x ≠ z) :
    ∃ F : C(Space a,ℝ), F (openCell a i x) = 1 ∧ F z = 0 := by
  classical
  let K : Set (Disk n) := Set.range (boundary n) ∪ cell a i ⁻¹' {z}
  have hKc : IsClosed K := by

    have hz : IsClosed (cell a i ⁻¹' {z}) := by
      cases z with
      | inl y =>
        have heq : ({base a y} : Set (Space a)) = base a '' {y} :=
          Set.image_singleton.symm
        change IsClosed (cell a i ⁻¹' {base a y})
        rw [heq,cell_preimage_base_image]

        exact (boundary_closedEmbedding n).isClosedMap _
          (isClosed_singleton.preimage (a i).continuous)
      | inr p =>
        have heq : ({openCell a p.1 p.2} : Set (Space a)) = openCell a p.1 '' {p.2} :=
          Set.image_singleton.symm
        have hpre := quotient_preimage_openCell_image a p.1 ({p.2} : Set (OpenDisk n))
        have hclosed : IsClosed (quotient a ⁻¹' {Sum.inr p}) := by
          change IsClosed (quotient a ⁻¹' {openCell a p.1 p.2})
          rw [heq,hpre]
          exact isClosedMap_inr _ (isClosedMap_sigmaMk _
            ((isCompact_singleton.image (continuous_interior n)).isClosed))
        exact hclosed.preimage (continuous_inr.comp continuous_sigmaMk)
    exact (boundary_closedEmbedding n).isClosed_range.union hz
  have hxK : interior n x ∉ K := by
    rintro (hx | hx)
    · obtain ⟨s,hs⟩ := hx
      have heq := congrArg (fun d : Disk n => d.1) hs
      exact sphere_disjoint_ball.notMem_of_mem_left s.2 (heq ▸ x.2)
    · change cell a i (interior n x) = z at hx
      exact hxz ((cell_interior a i x).symm.trans hx)
  obtain ⟨f,hf0,hf1,_⟩ := exists_continuous_zero_one_of_isClosed hKc
    (isClosed_singleton (x := interior n x)) (Set.disjoint_singleton_right.mpr hxK)
  let g : ι → C(Disk n,ℝ) := fun j => if j = i then f else ContinuousMap.const _ 0
  have hgb (j : ι) (s : Sphere n) : g j (boundary n s) = (0 : ℝ) := by
    dsimp [g]
    split_ifs with hji
    · exact hf0 (Set.mem_union_left _ (Set.mem_range_self s))
    · rfl
  let F : C(Space a,ℝ) := lift a (ContinuousMap.const _ 0) g hgb
  have hFcell (j : ι) (d : Disk n) : F (cell a j d) = g j d := lift_cell a _ _ _ j d
  refine ⟨F,?_,?_⟩
  · change F (Sum.inr ⟨i,x⟩) = 1
    rw [← cell_interior a i x,hFcell]
    simpa only [g,ite_eq_left rfl,Pi.one_apply] using hf1 (Set.mem_singleton _)
  · cases z with
    | inl y => exact lift_base a _ _ _ y
    | inr p =>
      rw [← cell_interior a p.1 p.2,hFcell]
      by_cases hpi : p.1 = i
      · have hm : interior n p.2 ∈ K := by
          right
          change cell a i (interior n p.2) = Sum.inr p
          rw [cell_interior]
          cases p with
          | mk j y => cases hpi; rfl
        simpa only [g,ite_eq_left hpi,Pi.zero_apply] using hf0 hm
      · simp only [g,ite_eq_right hpi,ContinuousMap.const_apply]

lemma realSeparated (hX : RealSeparated X) : RealSeparated (Space a) := by
  classical
  let : T2Space X := hX.t2Space
  intro x y hxy
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      have hne : x ≠ y := fun heq => hxy (congrArg Sum.inl heq)
      obtain ⟨f,hf⟩ := hX x y hne
      obtain ⟨F,hF⟩ := exists_real_extension a f
      refine ⟨F,?_⟩
      change F (base a x) ≠ F (base a y)
      rwa [hF,hF]
    | inr p =>
      obtain ⟨F,hF1,hF0⟩ := exists_interior_separator a p.1 p.2 (Sum.inl x)
        (by exact fun h => hxy h.symm)
      refine ⟨F,?_⟩
      change F (Sum.inl x) ≠ F (openCell a p.1 p.2)
      rw [hF0,hF1]
      norm_num
  | inr p =>
    obtain ⟨F,hF1,hF0⟩ := exists_interior_separator a p.1 p.2 y hxy
    refine ⟨F,?_⟩
    change F (openCell a p.1 p.2) ≠ F y
    rw [hF1,hF0]
    norm_num

lemma t2Space (hX : RealSeparated X) : T2Space (Space a) := (realSeparated a hX).t2Space

section Characteristic
variable [Nonempty X]

def characteristic (i : ι) (x : Fin n → ℝ) : Space a := by
  classical
  exact if hx : x ∈ closedBall 0 1 then cell a i ⟨x,hx⟩ else base a (Classical.choice ‹Nonempty X›)

lemma characteristic_disk (i : ι) (d : Disk n) :
    characteristic a i d.1 = cell a i d := by
  simp only [characteristic,dite_eq_left d.2]

lemma characteristic_open (i : ι) (x : OpenDisk n) :
    characteristic a i x.1 = openCell a i x := by
  exact (characteristic_disk a i (interior n x)).trans (cell_interior a i x)

lemma characteristic_bijOn (i : ι) :
    Set.BijOn (characteristic a i) (ball 0 1) (Set.range (openCell a i)) := by
  constructor
  · intro x hx
    exact ⟨⟨x,hx⟩,(characteristic_open a i ⟨x,hx⟩).symm⟩
  constructor
  · intro x hx y hy hxy
    have hxy' : openCell a i ⟨x,hx⟩ = openCell a i ⟨y,hy⟩ := by
      rwa [characteristic_open a i ⟨x,hx⟩,characteristic_open a i ⟨y,hy⟩] at hxy
    exact congrArg Subtype.val ((openCell_openEmbedding a i).injective hxy')
  · rintro z ⟨x,rfl⟩
    exact ⟨x.1,x.2,characteristic_open a i x⟩

def characteristicPE (i : ι) : PartialEquiv (Fin n → ℝ) (Space a) :=
  (characteristic_bijOn a i).toPartialEquiv _ _ _

lemma characteristicPE_continuousOn (i : ι) :
    ContinuousOn (characteristicPE a i) (closedBall 0 1) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have heq : (closedBall (0:Fin n→ℝ) 1).domRestrict (characteristicPE a i) = cell a i := by
    funext x
    exact characteristic_disk a i x
  rw [heq]
  exact (cell a i).continuous

lemma characteristicPE_continuousOn_symm (i : ι) :
    ContinuousOn (characteristicPE a i).symm (characteristicPE a i).target := by
  let e := characteristicPE a i
  have he : IsEmbedding (e.source.domRestrict e) := by
    have heq : e.source.domRestrict e = openCell a i := by
      funext x
      exact characteristic_open a i x
    rw [heq]
    exact (openCell_openEmbedding a i).isEmbedding
  let H : e.source ≃ₜ e.target := e.toEquiv.toHomeomorphOfIsInducing
    (he.isInducing.codRestrict (fun x => e.map_source x.2))
  rw [continuousOn_iff_continuous_domRestrict]
  exact continuous_subtype_val.comp H.symm.continuous

lemma characteristicPE_image_ball (i : ι) :
    characteristicPE a i '' ball 0 1 = Set.range (openCell a i) :=
  (characteristic_bijOn a i).image_eq

lemma characteristicPE_image_closedBall (i : ι) :
    characteristicPE a i '' closedBall 0 1 = Set.range (cell a i) := by
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨⟨x,hx⟩,(characteristic_disk a i ⟨x,hx⟩).symm⟩
  · rintro ⟨x,rfl⟩
    exact ⟨x.1,x.2,characteristic_disk a i x⟩

abbrev CellIndex (m n : ℕ) (ι : Type v) := ULift.{u} (PLift (m = n) × ι)

def cellMap (m : ℕ) (i : CellIndex.{u,v} m n ι) :
    PartialEquiv (Fin m → ℝ) (Space a) := by
  obtain ⟨⟨⟨hm⟩,i⟩⟩ := i
  subst m
  exact characteristicPE a i

@[instance_reducible]
def relCWComplex : RelCWComplex (Set.univ : Set (Space a)) (Set.range (base a)) where
  cell m := CellIndex.{u,v} m n ι
  map := cellMap a
  source_eq := by
    rintro m ⟨⟨⟨hm⟩,i⟩⟩
    subst m
    rfl
  continuousOn := by
    rintro m ⟨⟨⟨hm⟩,i⟩⟩
    subst m
    exact characteristicPE_continuousOn a i
  continuousOn_symm := by
    rintro m ⟨⟨⟨hm⟩,i⟩⟩
    subst m
    exact characteristicPE_continuousOn_symm a i
  pairwiseDisjoint' := by
    rintro ⟨m,⟨⟨⟨hm⟩,i⟩⟩⟩ _ ⟨k,⟨⟨⟨hk⟩,j⟩⟩⟩ _ hne
    subst m; subst k
    change Disjoint (characteristicPE a i '' ball 0 1) (characteristicPE a j '' ball 0 1)
    rw [characteristicPE_image_ball,characteristicPE_image_ball]
    apply Set.disjoint_left.mpr
    rintro z ⟨x,rfl⟩ ⟨y,h⟩
    have hij : j = i := congrArg Sigma.fst (Sum.inr_injective h)
    subst j
    exact hne rfl
  disjointBase' := by
    rintro m ⟨⟨⟨hm⟩,i⟩⟩
    subst m
    change Disjoint (characteristicPE a i '' ball 0 1) _
    rw [characteristicPE_image_ball]
    apply Set.disjoint_left.mpr
    rintro z ⟨x,rfl⟩ ⟨y,h⟩
    cases h
  mapsTo := by
    rintro m ⟨⟨⟨hm⟩,i⟩⟩
    subst m
    refine ⟨fun _ => ∅,?_⟩
    intro x hx
    left
    refine ⟨a i ⟨x,hx⟩,?_⟩
    change base a (a i ⟨x,hx⟩) = characteristic a i x
    exact (cell_boundary a i ⟨x,hx⟩).symm.trans
      (characteristic_disk a i (boundary n ⟨x,hx⟩)).symm
  closed' := by
    intro A _ hA
    apply (isClosed_iff a A).mpr
    constructor
    · have h := hA.2.preimage (continuous_base a)
      convert h using 1
      ext x
      simp only [Set.mem_preimage,Set.mem_inter_iff,Set.mem_range_self,and_true]
    · intro i
      have h := (hA.1 n ⟨⟨⟨rfl⟩,i⟩⟩).preimage (cell a i).continuous
      change IsClosed ((cell a i) ⁻¹' (A ∩ characteristicPE a i '' closedBall 0 1)) at h
      rw [characteristicPE_image_closedBall] at h
      convert h using 1
      ext x
      simp only [Set.mem_preimage,Set.mem_inter_iff,Set.mem_range_self,and_true]
  isClosedBase := (base_closedEmbedding a).isClosed_range
  union' := by
    apply Set.eq_univ_of_forall
    intro z
    cases z with
    | inl x => exact Or.inl ⟨x,rfl⟩
    | inr p =>
      right
      refine Set.mem_iUnion.mpr ⟨n,Set.mem_iUnion.mpr ⟨⟨⟨⟨rfl⟩,p.1⟩⟩,?_⟩⟩
      change Sum.inr p ∈ characteristicPE a p.1 '' closedBall 0 1
      rw [characteristicPE_image_closedBall]
      exact ⟨interior n p.2,cell_interior a p.1 p.2⟩

end Characteristic

end
end UniversalFInfinity.Attachment

open Set Metric Topology

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.CellularAttachment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology

namespace UniversalFInfinity.Cellular
universe u
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] [Nonempty X]
variable {C : Set X} [CWComplex C] {f : X → Y} (hf : IsClosedEmbedding f)

def transportedMap (n : ℕ) (i : RelCWComplex.cell C n) : PartialEquiv (Fin n → ℝ) Y :=
  (RelCWComplex.map n i).trans (hf.isEmbedding.toPartialHomeomorph f).toPartialEquiv

@[simp] lemma transportedMap_apply (n : ℕ) (i : RelCWComplex.cell C n) (x : Fin n → ℝ) :
    transportedMap hf n i x = f (RelCWComplex.map n i x) := rfl

lemma transportedMap_source (n : ℕ) (i : RelCWComplex.cell C n) :
    (transportedMap hf n i).source = ball 0 1 := by
  simp only [transportedMap,PartialEquiv.trans_source,
    IsEmbedding.toPartialHomeomorph_source,Set.preimage_univ,Set.inter_univ,
    RelCWComplex.source_eq]

lemma transportedMap_image (n : ℕ) (i : RelCWComplex.cell C n) (S : Set (Fin n → ℝ)) :
    transportedMap hf n i '' S = f '' (RelCWComplex.map n i '' S) :=
  Set.image_comp f (RelCWComplex.map n i) S

lemma transportedMap_continuousOn (n : ℕ) (i : RelCWComplex.cell C n) :
    ContinuousOn (transportedMap hf n i) (closedBall 0 1) :=
  hf.continuous.comp_continuousOn (RelCWComplex.continuousOn n i)

lemma transportedMap_continuousOn_symm (n : ℕ) (i : RelCWComplex.cell C n) :
    ContinuousOn (transportedMap hf n i).symm (transportedMap hf n i).target := by
  let e := hf.isEmbedding.toPartialHomeomorph f
  change ContinuousOn (fun y => (RelCWComplex.map n i).symm (e.symm y))
    (e.target ∩ e.symm ⁻¹' (RelCWComplex.map n i).target)
  exact (RelCWComplex.continuousOn_symm n i).comp
    (e.continuousOn_symm.mono Set.inter_subset_left) (fun _ h => h.2)

end UniversalFInfinity.Cellular

open Set Metric Topology
namespace UniversalFInfinity.Attachment

section
open Set Metric Topology
universe z
variable {X : Type z} [TopologicalSpace X] [T2Space X] [Nonempty X]
variable [CWComplex (Set.univ : Set X)] {ι : Type z} {n : ℕ}
variable (a : ι → C(Sphere n,X))

abbrev OldCell (m : ℕ) := RelCWComplex.cell (Set.univ : Set X) m

omit [Nonempty X] in
lemma attaching_finite_frontier
    (hdim : ∀ m (_ : OldCell (X := X) m), m < n) (i : ι) :
    ∃ I : ∀ m, Finset (OldCell (X := X) m),
      ∀ x, a i x ∈ ⋃ m < n, ⋃ j ∈ I m, CWComplex.closedCell m j := by
  classical
  let S := {p : Σ m, OldCell (X := X) m |
    (Set.range (a i) ∩ CWComplex.openCell p.1 p.2).Nonempty}
  have hS : S.Finite := Cellular.compact_finitely_many_cells (C := (Set.univ : Set X))
    (isCompact_range (a i).continuous)
  have hSm (m : ℕ) : ((Sigma.mk m) ⁻¹' S).Finite :=
    hS.preimage (Set.injOn_of_injective (fun _ _ h => eq_of_heq (Sigma.mk.inj_iff.mp h).2))
  refine ⟨fun m => (hSm m).toFinset,?_⟩
  intro x
  have hx : a i x ∈ (Set.univ : Set X) := Set.mem_univ _
  rw [← CWComplex.iUnion_openCell_eq_complex (C := (Set.univ : Set X))] at hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨m,j,hx⟩ := hx
  exact Set.mem_iUnion.mpr ⟨m,Set.mem_iUnion.mpr ⟨hdim m j,Set.mem_iUnion.mpr
    ⟨j,Set.mem_iUnion.mpr ⟨(hSm m).mem_toFinset.mpr ⟨a i x,⟨x,rfl⟩,hx⟩,
      CWComplex.openCell_subset_closedCell m j hx⟩⟩⟩⟩

abbrev LayerCell (m : ℕ) := OldCell (X := X) m ⊕ CellIndex.{z,z} m n ι

def layerMap (m : ℕ) : LayerCell (X := X) (ι := ι) (n := n) m →
    PartialEquiv (Fin m → ℝ) (Space a)
  | Sum.inl i => Cellular.transportedMap (C := Set.univ) (base_closedEmbedding a) m i
  | Sum.inr i => cellMap a m i

omit [T2Space X] in
lemma layerMap_old_image (m : ℕ) (i : OldCell (X := X) m) (S : Set (Fin m → ℝ)) :
    layerMap a m (Sum.inl i) '' S = base a '' (RelCWComplex.map m i '' S) :=
  Cellular.transportedMap_image (base_closedEmbedding a) m i S

omit [T2Space X] in
lemma layerMap_new (i : ι) :
    layerMap a n (Sum.inr ⟨⟨⟨rfl⟩,i⟩⟩) = characteristicPE a i := rfl

@[instance_reducible]
def layerCW (hdim : ∀ m (_ : OldCell (X := X) m), m < n) :
    CWComplex (Set.univ : Set (Space a)) where
  cell := LayerCell (X := X) (ι := ι) (n := n)
  map := layerMap a
  source_eq := by
    intro m i
    cases i with
    | inl i => exact Cellular.transportedMap_source (base_closedEmbedding a) m i
    | inr i => exact (relCWComplex a).source_eq m i
  continuousOn := by
    intro m i
    cases i with
    | inl i => exact Cellular.transportedMap_continuousOn (base_closedEmbedding a) m i
    | inr i => exact (relCWComplex a).continuousOn m i
  continuousOn_symm := by
    intro m i
    cases i with
    | inl i => exact Cellular.transportedMap_continuousOn_symm (base_closedEmbedding a) m i
    | inr i => exact (relCWComplex a).continuousOn_symm m i
  pairwiseDisjoint' := by
    rintro ⟨m,i⟩ _ ⟨k,j⟩ _ hne
    change Disjoint (layerMap a m i '' ball 0 1) (layerMap a k j '' ball 0 1)
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        rw [layerMap_old_image,layerMap_old_image]
        apply (CWComplex.disjoint_openCell_of_ne ?_).image (base_closedEmbedding a).injective.injOn (Set.subset_univ _) (Set.subset_univ _)
        intro h
        cases h
        exact hne rfl
      | inr j =>
        obtain ⟨⟨⟨hk⟩,j⟩⟩ := j
        subst k
        rw [layerMap_old_image,layerMap_new,characteristicPE_image_ball]
        apply Set.disjoint_left.mpr
        rintro z ⟨x,_,rfl⟩ ⟨y,h⟩
        cases h
    | inr i =>
      obtain ⟨⟨⟨hm⟩,i⟩⟩ := i
      subst m
      cases j with
      | inl j =>
        rw [layerMap_new,characteristicPE_image_ball,layerMap_old_image]
        apply Set.disjoint_left.mpr
        rintro z ⟨x,rfl⟩ ⟨y,_,h⟩
        cases h
      | inr j =>
        obtain ⟨⟨⟨hk⟩,j⟩⟩ := j
        subst k
        rw [layerMap_new,layerMap_new,characteristicPE_image_ball,characteristicPE_image_ball]
        apply Set.disjoint_left.mpr
        rintro z ⟨x,rfl⟩ ⟨y,h⟩
        have hij : j = i := congrArg Sigma.fst (Sum.inr_injective h)
        subst j
        exact hne rfl
  mapsTo' := by
    classical
    intro m c
    cases c with
    | inl i =>
      obtain ⟨I,hI⟩ := CWComplex.cellFrontier_subset_finite_closedCell m i
      refine ⟨fun k => (I k).image Sum.inl,?_⟩
      intro x hx
      have hh := hI (show RelCWComplex.map m i x ∈ CWComplex.cellFrontier m i from ⟨x,hx,rfl⟩)
      simp only [Set.mem_iUnion] at hh
      obtain ⟨k,hkm,j,hj,hx⟩ := hh
      refine Set.mem_iUnion.mpr ⟨k,Set.mem_iUnion.mpr ⟨hkm,Set.mem_iUnion.mpr
        ⟨Sum.inl j,Set.mem_iUnion.mpr ⟨Finset.mem_image.mpr ⟨j,hj,rfl⟩,?_⟩⟩⟩⟩
      rw [layerMap_old_image]
      exact ⟨_,hx,rfl⟩
    | inr i =>
      obtain ⟨⟨⟨hm⟩,i⟩⟩ := i
      subst m
      obtain ⟨I,hI⟩ := attaching_finite_frontier a hdim i
      refine ⟨fun k => (I k).image Sum.inl,?_⟩
      intro x hx
      have hh := hI ⟨x,hx⟩
      simp only [Set.mem_iUnion] at hh
      obtain ⟨k,hkn,j,hj,hx'⟩ := hh
      refine Set.mem_iUnion.mpr ⟨k,Set.mem_iUnion.mpr ⟨hkn,Set.mem_iUnion.mpr
        ⟨Sum.inl j,Set.mem_iUnion.mpr ⟨Finset.mem_image.mpr ⟨j,hj,rfl⟩,?_⟩⟩⟩⟩
      rw [layerMap_old_image]
      refine ⟨a i ⟨x,hx⟩,hx',?_⟩
      change base a (a i ⟨x,hx⟩) = characteristic a i x
      exact (cell_boundary a i ⟨x,hx⟩).symm.trans
        (characteristic_disk a i (boundary n ⟨x,hx⟩)).symm
  closed' := by
    intro A _ hA
    apply (isClosed_iff a A).mpr
    constructor
    · apply (CWComplex.closed Set.univ (base a ⁻¹' A) (Set.subset_univ _)).mpr
      intro m i
      have h := (hA m (Sum.inl i)).preimage (continuous_base a)
      rw [layerMap_old_image,Set.preimage_inter,
        Set.preimage_image_eq _ (base_closedEmbedding a).injective] at h
      exact h
    · intro i
      have h := (hA n (Sum.inr ⟨⟨⟨rfl⟩,i⟩⟩)).preimage (cell a i).continuous
      rw [layerMap_new,characteristicPE_image_closedBall,Set.preimage_inter] at h
      simpa only [Set.preimage_range,Set.inter_univ] using h
  union' := by
    apply Set.eq_univ_of_forall
    intro z
    cases z with
    | inl x =>
      have hx : x ∈ (Set.univ : Set X) := Set.mem_univ _
      rw [← CWComplex.union (C := (Set.univ : Set X))] at hx
      simp only [Set.mem_iUnion] at hx
      obtain ⟨m,i,hx⟩ := hx
      refine Set.mem_iUnion.mpr ⟨m,Set.mem_iUnion.mpr ⟨Sum.inl i,?_⟩⟩
      rw [layerMap_old_image]
      exact ⟨x,hx,rfl⟩
    | inr p =>
      refine Set.mem_iUnion.mpr ⟨n,Set.mem_iUnion.mpr ⟨Sum.inr ⟨⟨⟨rfl⟩,p.1⟩⟩,?_⟩⟩
      rw [layerMap_new,characteristicPE_image_closedBall]
      exact ⟨interior n p.2,cell_interior a p.1 p.2⟩

lemma layerCW_dimensions (hdim : ∀ m (_ : OldCell (X := X) m), m < n)
    (m : ℕ) (i : (layerCW a hdim).cell m) : m < n+1 := by
  cases i with
  | inl i => exact (hdim m i).trans (Nat.lt_succ_self n)
  | inr i =>
    obtain ⟨⟨⟨hm⟩,i⟩⟩ := i
    subst m
    exact Nat.lt_succ_self n

lemma layerCW_finite_cells [Finite ι]
    (hfin : ∀ m, Finite (OldCell (X := X) m))
    (hdim : ∀ m (_ : OldCell (X := X) m), m < n) (m : ℕ) :
    Finite ((layerCW a hdim).cell m) := by
  let := hfin m
  change Finite (LayerCell (X := X) (ι := ι) (n := n) m)
  infer_instance

end

section
open Set Metric Topology
universe u v w z
variable {X : Type u} [TopologicalSpace X] {ι : Type v} {n : ℕ}
variable (a : ι → C(Sphere n,X))
variable {G : Type w} [Group G] [MulAction G X] [MulAction G ι]

instance spaceMulAction : MulAction G (Space a) where
  smul g := Sum.elim (fun x => Sum.inl (g • x)) (fun p => Sum.inr ⟨g • p.1,p.2⟩)
  one_smul := by
    intro x
    cases x with
    | inl x => change Sum.inl ((1 : G) • x) = Sum.inl x; rw [one_smul]
    | inr p => change Sum.inr ⟨(1 : G) • p.1,p.2⟩ = Sum.inr p; rw [one_smul]
  mul_smul := by
    intro g h x
    cases x with
    | inl x => change Sum.inl ((g * h) • x) = Sum.inl (g • h • x); rw [mul_smul]
    | inr p => change (Sum.inr ⟨(g * h) • p.1,p.2⟩ : Space a) = Sum.inr ⟨g • h • p.1,p.2⟩; rw [mul_smul]

@[simp] lemma smul_base (g : G) (x : X) : g • base a x = base a (g • x) := rfl
@[simp] lemma smul_openCell (g : G) (i : ι) (x : OpenDisk n) :
    g • openCell a i x = openCell a (g • i) x := rfl

variable (ha : ∀ (g : G) i x, a (g • i) x = g • a i x)
include ha
lemma smul_cell (g : G) (i : ι) (d : Disk n) :
    g • cell a i d = cell a (g • i) d := by
  classical
  by_cases hd : d.1 ∈ ball (0 : Fin n → ℝ) 1
  · have heq : d = interior n ⟨d.1,hd⟩ := rfl
    rw [heq,cell_interior,cell_interior]
    rfl
  · let x : Sphere n := ⟨d.1,by
      have hm := d.2
      simp only [mem_closedBall,mem_ball,mem_sphere] at *
      exact le_antisymm hm (le_of_not_gt hd)⟩
    have heq : d = boundary n x := rfl
    rw [heq,cell_boundary,cell_boundary,smul_base,ha]

lemma continuousConstSMul [ContinuousConstSMul G X] : ContinuousConstSMul G (Space a) where
  continuous_const_smul g := (continuous_iff a _).mpr ⟨
    (continuous_base a).comp (continuous_const_smul g),fun i => by
      have heq : (g • ·) ∘ cell a i = cell a (g • i) := funext (smul_cell a ha g i)
      rw [heq]
      exact (cell a (g • i)).continuous⟩

omit ha in
lemma isOpen_iff (S : Set (Space a)) :
    IsOpen S ↔ IsOpen (base a ⁻¹' S) ∧ ∀ i, IsOpen (cell a i ⁻¹' S) := by
  change @IsOpen _ (TopologicalSpace.coinduced (quotient a) inferInstance) S ↔ _
  rw [isOpen_coinduced,isOpen_sum_iff,isOpen_sigma_iff]
  rfl

end

section
open Set Metric Topology
universe u v w
abbrev Collar (n : ℕ) := {d : Disk n | (1 / 2 : ℝ) < ‖d.1‖}

def collarInclusion (n : ℕ) : Collar n → Disk n := Subtype.val

def radial (n : ℕ) : Collar n → Sphere n := fun d =>
  ⟨‖d.1.1‖⁻¹ • d.1.1,by
    have hn : ‖d.1.1‖ ≠ 0 := ne_of_gt (lt_trans (by norm_num) d.2)
    rw [mem_sphere,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_inv,abs_norm,
      inv_mul_cancel₀ hn]⟩

lemma continuous_radial (n : ℕ) : Continuous (radial n) := by
  apply Continuous.subtype_mk
  have hn : ∀ d : Collar n, ‖d.1.1‖ ≠ 0 := fun d => ne_of_gt (lt_trans (by norm_num) d.2)
  exact ((continuous_subtype_val.comp continuous_subtype_val).norm.inv₀ hn).smul
    (continuous_subtype_val.comp continuous_subtype_val)

lemma collar_openEmbedding (n : ℕ) : IsOpenEmbedding (collarInclusion n) :=
  (isOpen_lt continuous_const continuous_subtype_val.norm).isOpenEmbedding_subtypeVal

lemma radial_boundary (n : ℕ) (x : Sphere n) (h : (1/2:ℝ) < ‖(boundary n x).1‖) :
    radial n ⟨boundary n x,h⟩ = x := by
  apply Subtype.ext
  have hx : ‖x.1‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using x.2
  simp only [radial,boundary,hx,inv_one,one_smul]

variable {X : Type u} [TopologicalSpace X] {ι : Type v} {n : ℕ}
variable (a : ι → C(Sphere n,X))

def thickening (U : Set X) : Set (Space a) := fun z =>
  match z with
  | Sum.inl x => x ∈ U
  | Sum.inr p => ∃ h : (1/2:ℝ) < ‖p.2.1‖,
      a p.1 (radial n ⟨interior n p.2,h⟩) ∈ U

@[simp] lemma base_mem_thickening (U : Set X) (x : X) :
    base a x ∈ thickening a U ↔ x ∈ U := Iff.rfl

lemma cell_preimage_thickening (U : Set X) (i : ι) :
    cell a i ⁻¹' thickening a U =
      collarInclusion n '' ((a i ∘ radial n) ⁻¹' U) := by
  classical
  ext d
  by_cases hd : d.1 ∈ ball (0 : Fin n → ℝ) 1
  · have heq : d = interior n ⟨d.1,hd⟩ := rfl
    rw [heq]
    simp only [Set.mem_preimage,cell_interior,Set.mem_image]
    constructor
    · rintro ⟨h,hh⟩
      exact ⟨⟨d,h⟩,hh,rfl⟩
    · rintro ⟨y,hy,he⟩
      have heq' : y.1 = d := he
      subst d
      exact ⟨y.2,hy⟩
  · let x : Sphere n := ⟨d.1,by
      have hm := d.2
      simp only [mem_closedBall,mem_ball,mem_sphere] at *
      exact le_antisymm hm (le_of_not_gt hd)⟩
    have heq : d = boundary n x := rfl
    have hx : ‖x.1‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using x.2
    have hhalf : (1/2:ℝ) < ‖(boundary n x).1‖ := by change (1/2:ℝ) < ‖x.1‖; rw [hx]; norm_num
    rw [heq]
    simp only [Set.mem_preimage,cell_boundary,base_mem_thickening,Set.mem_image]
    constructor
    · intro h
      exact ⟨⟨boundary n x,hhalf⟩,by simpa only [Function.comp_apply,radial_boundary] using h,rfl⟩
    · rintro ⟨y,hy,he⟩
      have heq' : y = ⟨boundary n x,hhalf⟩ := Subtype.ext he
      simpa only [heq',Function.comp_apply,radial_boundary] using hy

lemma thickening_isOpen {U : Set X} (hU : IsOpen U) : IsOpen (thickening a U) := by
  rw [isOpen_iff]
  refine ⟨hU,fun i => ?_⟩
  rw [cell_preimage_thickening]
  exact (collar_openEmbedding n).isOpenMap _
    (hU.preimage ((a i).continuous.comp (continuous_radial n)))

variable {G : Type w} [Group G] [MulAction G X] [MulAction G ι]
variable (ha : ∀ (g : G) i x, a (g • i) x = g • a i x)
include ha
lemma thickening_disjoint {U : Set X}
    (hU : ∀ g : G, ((g • ·) '' U ∩ U).Nonempty → g = 1) :
    ∀ g : G, ((g • ·) '' thickening a U ∩ thickening a U).Nonempty → g = 1 := by
  intro g h
  obtain ⟨_,⟨z,hz,rfl⟩,hgz⟩ := h
  cases z with
  | inl x => exact hU g ⟨g • x,⟨x,hz,rfl⟩,hgz⟩
  | inr p =>
    obtain ⟨hhalf,hz⟩ := hz
    obtain ⟨_,hgz⟩ := hgz
    change a (g • p.1) (radial n ⟨interior n p.2,hhalf⟩) ∈ U at hgz
    rw [ha] at hgz
    exact hU g ⟨g • a p.1 (radial n ⟨interior n p.2,hhalf⟩),⟨_,hz,rfl⟩,hgz⟩

lemma exists_disjoint_nhds [IsCancelSMul G ι]
    (hX : ∀ x : X, ∃ U ∈ 𝓝 x, ∀ g : G, ((g • ·) '' U ∩ U).Nonempty → g = 1) :
    ∀ z : Space a, ∃ U ∈ 𝓝 z, ∀ g : G, ((g • ·) '' U ∩ U).Nonempty → g = 1 := by
  intro z
  cases z with
  | inl x =>
    obtain ⟨U,hUx,hU⟩ := hX x
    obtain ⟨V,hVU,hV,hxV⟩ := mem_nhds_iff.mp hUx
    refine ⟨thickening a V,(thickening_isOpen a hV).mem_nhds hxV,
      thickening_disjoint a ha (fun g hg => hU g ?_)⟩
    exact hg.mono (Set.inter_subset_inter (Set.image_mono hVU) hVU)
  | inr p =>
    refine ⟨Set.range (openCell a p.1),(openCell_openEmbedding a p.1).isOpen_range.mem_nhds
      (Set.mem_range_self p.2),?_⟩
    intro g hg
    obtain ⟨_,⟨_,⟨x,rfl⟩,rfl⟩,⟨y,hy⟩⟩ := hg
    have hi : p.1 = g • p.1 := congrArg Sigma.fst (Sum.inr_injective hy)
    apply IsCancelSMul.right_cancel g 1 p.1
    simpa only [one_smul] using hi.symm

end

section
open Set Metric Topology
universe u v w z
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable {ι : Type w} {κ : Type z} {n : ℕ}
variable (a : ι → C(Sphere n,X)) (b : κ → C(Sphere n,Y))

def map (p : C(X,Y)) (σ : ι → κ) (h : ∀ i x, p (a i x) = b (σ i) x) :
    C(Space a,Space b) :=
  lift a ⟨base b ∘ p,(continuous_base b).comp p.continuous⟩
    (fun i => cell b (σ i)) (fun i x => by simp only [cell_boundary,ContinuousMap.coe_mk,Function.comp_apply,h])

@[simp] lemma map_base (p : C(X,Y)) (σ : ι → κ)
    (h : ∀ i x, p (a i x) = b (σ i) x) (x : X) :
    map a b p σ h (base a x) = base b (p x) := rfl

@[simp] lemma map_cell (p : C(X,Y)) (σ : ι → κ)
    (h : ∀ i x, p (a i x) = b (σ i) x) (i : ι) (d : Disk n) :
    map a b p σ h (cell a i d) = cell b (σ i) d := lift_cell a _ _ _ i d

@[simp] lemma map_openCell (p : C(X,Y)) (σ : ι → κ)
    (h : ∀ i x, p (a i x) = b (σ i) x) (i : ι) (d : OpenDisk n) :
    map a b p σ h (openCell a i d) = openCell b (σ i) d := by
  change map a b p σ h (Sum.inr ⟨i,d⟩) = Sum.inr ⟨σ i,d⟩
  rw [← cell_interior a i d,map_cell,cell_interior]

lemma map_surjective (p : C(X,Y)) (σ : ι → κ)
    (h : ∀ i x, p (a i x) = b (σ i) x)
    (hp : Function.Surjective p) (hσ : Function.Surjective σ) :
    Function.Surjective (map a b p σ h) := by
  intro z
  cases z with
  | inl y =>
    obtain ⟨x,rfl⟩ := hp y
    exact ⟨base a x,rfl⟩
  | inr q =>
    obtain ⟨i,hi⟩ := hσ q.1
    exact ⟨openCell a i q.2,by rw [map_openCell,hi]; rfl⟩

lemma map_isQuotientMap (p : C(X,Y)) (σ : ι → κ)
    (h : ∀ i x, p (a i x) = b (σ i) x)
    (hp : IsQuotientMap p) (hσ : Function.Surjective σ) :
    IsQuotientMap (map a b p σ h) := by
  refine ⟨?_,map_surjective a b p σ h hp.surjective hσ⟩
  rw [isCoinducing_iff]
  intro U
  constructor
  · intro hU
    rw [isOpen_iff] at hU ⊢
    constructor
    · apply hp.isOpen_preimage.mp
      exact hU.1
    · intro j
      obtain ⟨i,rfl⟩ := hσ j
      convert hU.2 i using 1
      ext d
      simp only [Set.mem_preimage,map_cell]
  · exact fun hU => hU.preimage (map a b p σ h).continuous

end

open Set Metric Topology
universe u v w z

def FreeIndex (G : Type u) (ι : Type v) := G × ι

instance instMulActionFreeIndex {G : Type u} [Group G] {ι : Type v} : MulAction G (FreeIndex G ι) where
  smul g p := (g * p.1,p.2)
  one_smul p := by change ((1:G)*p.1,p.2)=p; simp only [one_mul]; rfl
  mul_smul g h p := by change ((g*h)*p.1,p.2)=(g*(h*p.1),p.2); rw [mul_assoc]

instance instIsCancelSMulFreeIndex {G : Type u} [Group G] {ι : Type v} : IsCancelSMul G (FreeIndex G ι) where
  right_cancel' _ _ _ he := mul_right_cancel (congrArg (fun p : FreeIndex G ι => p.1) he)

variable {G : Type u} [Group G]
variable {E : Type v} [TopologicalSpace E] [MulAction G E] [ContinuousConstSMul G E]
variable {X : Type w} [TopologicalSpace X] {ι : Type z} {n : ℕ}
variable (a : ι → C(Sphere n,E))

def equivariantFamily : FreeIndex G ι → C(Sphere n,E) :=
  fun i => ⟨fun x => i.1 • a i.2 x,(continuous_const_smul i.1).comp (a i.2).continuous⟩

lemma equivariantFamily_smul (g : G) (i : FreeIndex G ι) (x : Sphere n) :
    equivariantFamily (G := G) a (g • i) x = g • equivariantFamily a i x := mul_smul g i.1 _

instance equivariantAttachmentContinuousAction :
    ContinuousConstSMul G (Space (equivariantFamily (G := G) a)) :=
  continuousConstSMul _ (equivariantFamily_smul a)

variable (p : C(E,X)) (hp : IsQuotientCoveringMap p G)
variable (b : ι → C(Sphere n,X)) (h : ∀ i x, p (a i x) = b i x)

include hp h in
lemma equivariantFamily_over (i : FreeIndex G ι) (x : Sphere n) :
    p (equivariantFamily (G := G) a i x) = b i.2 x :=
  (hp.map_smul i.1).trans (h i.2 x)

def coverMap : C(Space (equivariantFamily (G := G) a),Space b) :=
  map _ b p Prod.snd (equivariantFamily_over a p hp b h)

lemma coverMap_isQuotient : IsQuotientMap (coverMap a p hp b h) :=
  map_isQuotientMap _ b p Prod.snd _ hp.toIsQuotientMap (fun i => ⟨(1,i),rfl⟩)

lemma coverMap_fibers {e₁ e₂ : Space (equivariantFamily (G := G) a)} :
    coverMap a p hp b h e₁ = coverMap a p hp b h e₂ ↔ e₁ ∈ MulAction.orbit G e₂ := by
  classical
  cases e₁ with
  | inl x =>
    cases e₂ with
    | inl y =>
      change Sum.inl (p x) = Sum.inl (p y) ↔ _
      rw [Sum.inl.injEq,hp.apply_eq_iff_mem_orbit]
      constructor
      · rintro ⟨g,hg⟩; exact ⟨g,congrArg Sum.inl hg⟩
      · rintro ⟨g,hg⟩; exact ⟨g,Sum.inl_injective hg⟩
    | inr q =>
      constructor
      · intro hh
        change base b (p x) =
          map _ b p (fun index : FreeIndex G ι => index.2) _ (openCell _ q.1 q.2) at hh
        rw [map_openCell] at hh
        cases hh
      · rintro ⟨g,hg⟩; cases hg
  | inr q =>
    cases e₂ with
    | inl y =>
      constructor
      · intro hh
        change map _ b p (fun index : FreeIndex G ι => index.2) _
          (openCell _ q.1 q.2) = base b (p y) at hh
        rw [map_openCell] at hh
        cases hh
      · rintro ⟨g,hg⟩; cases hg
    | inr r =>
      change map _ b p (fun index : FreeIndex G ι => index.2) _ (openCell _ q.1 q.2) =
        map _ b p (fun index : FreeIndex G ι => index.2) _ (openCell _ r.1 r.2) ↔ _
      rw [map_openCell,map_openCell]
      constructor
      · intro hh
        have hi : q.1.2 = r.1.2 := congrArg Sigma.fst (Sum.inr_injective hh)
        have hd : q.2 = r.2 := congrArg (fun p : Σ _ : ι, OpenDisk n => p.2) (Sum.inr_injective hh)
        refine ⟨q.1.1 * r.1.1⁻¹,?_⟩
        change Sum.inr ⟨((q.1.1 * r.1.1⁻¹) * r.1.1,r.1.2),r.2⟩ = Sum.inr q
        simp only [inv_mul_cancel_right,← hi,← hd]
        rfl
      · rintro ⟨g,hg⟩
        change (Sum.inr ⟨g • r.1,r.2⟩ : Space (equivariantFamily (G := G) a)) = Sum.inr q at hg
        have hi : (g • r.1) = q.1 := congrArg Sigma.fst (Sum.inr_injective hg)
        have htuple : (⟨g • r.1,r.2⟩ : Σ _ : FreeIndex G ι, OpenDisk n) = q := Sum.inr_injective hg
        have hd' := congrArg (fun p : Σ _ : FreeIndex G ι, OpenDisk n => p.2) htuple
        have hd : r.2 = q.2 := hd'
        have his' := congrArg (fun p : FreeIndex G ι => p.2) hi
        have his : r.1.2 = q.1.2 := his'
        change (Sum.inr ⟨q.1.2,q.2⟩ : Space b) = Sum.inr ⟨r.1.2,r.2⟩
        rw [his,hd]

lemma coverMap_isQuotientCovering : IsQuotientCoveringMap (coverMap a p hp b h) G where
  __ := coverMap_isQuotient a p hp b h
  __ := equivariantAttachmentContinuousAction a
  apply_eq_iff_mem_orbit := coverMap_fibers a p hp b h
  disjoint := exists_disjoint_nhds _ (equivariantFamily_smul a) hp.disjoint

end UniversalFInfinity.Attachment

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.Cayley
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology

namespace UniversalFInfinity.Cayley
open Set Metric Topology Attachment
universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable {S : Type u} (s : S → G)

instance disk_pathConnected (n : ℕ) : PathConnectedSpace (Disk n) :=
  isPathConnected_iff_pathConnectedSpace.mp ((convex_closedBall (0 : Fin n → ℝ) 1).isPathConnected ⟨0,mem_closedBall_self (by norm_num)⟩)

end UniversalFInfinity.Cayley

open Set Metric Topology

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.PathExtensions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology

namespace UniversalFInfinity.PathExtension

section
open Path.Homotopic
universe u v
variable {X : Type u} [TopologicalSpace X]

namespace Q
variable {x y z : X}

structure Equal {x' y' : X} (p : Path.Homotopic.Quotient x y)
    (q : Path.Homotopic.Quotient x' y') : Prop where
  source : x = x'
  target : y = y'
  path : HEq p q

namespace Equal
lemma refl (p : Path.Homotopic.Quotient x y) : Equal p p := ⟨rfl,rfl,HEq.rfl⟩
lemma symm {x' y' : X} {p : Path.Homotopic.Quotient x y}
    {q : Path.Homotopic.Quotient x' y'} (h : Equal p q) : Equal q p :=
  ⟨h.source.symm,h.target.symm,h.path.symm⟩
lemma trans {x' y' x'' y'' : X} {p : Path.Homotopic.Quotient x y}
    {q : Path.Homotopic.Quotient x' y'} {r : Path.Homotopic.Quotient x'' y''}
    (h : Equal p q) (k : Equal q r) : Equal p r :=
  ⟨h.source.trans k.source,h.target.trans k.target,h.path.trans k.path⟩
lemma comp {x' y' z' : X} {p : Path.Homotopic.Quotient x y}
    {q : Path.Homotopic.Quotient y z} {p' : Path.Homotopic.Quotient x' y'}
    {q' : Path.Homotopic.Quotient y' z'} (hp : Equal p p') (hq : Equal q q') :
    Equal (p.trans q) (p'.trans q') := by
  rcases hp with ⟨hx,hy,hp⟩
  rcases hq with ⟨_,hz,hq⟩
  subst x'; subst y'; subst z'
  cases eq_of_heq hp; cases eq_of_heq hq
  exact .refl _
end Equal

end Q

variable {G : Type v} [Group G] [MulAction G X] [ContinuousConstSMul G X]

variable (G) (x₀ : X)
abbrev Extension := Σ g : G, Path.Homotopic.Quotient x₀ (g • x₀)
variable {G x₀}

omit [ContinuousConstSMul G X] in
@[ext] lemma ext {a b : Extension G x₀} (hg : a.1 = b.1) (hp : HEq a.2 b.2) : a = b :=
  Sigma.ext hg hp

end
open Path.Homotopic
universe u v w
end UniversalFInfinity.PathExtension
namespace UniversalFInfinity.Attachment
open Set Metric Topology
universe u v w z
variable {G : Type u} [Group G]
variable {X : Type v} [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]
variable {Y : Type w} [TopologicalSpace Y] [MulAction G Y] [ContinuousConstSMul G Y]
variable {ι : Type z} {n : ℕ} (a : ι → C(Sphere n,X))

lemma exists_equivariant_extension (f : C(X,Y))
    (hf : ∀ (g : G) x, f (g • x) = g • f x) (hY : Cellular.SphereFillable Y) :
    ∃ F : C(Space (equivariantFamily (G := G) a),Y),
      (∀ x, F (base _ x) = f x) ∧ (∀ (g : G) x, F (g • x) = g • F x) := by
  choose e he using fun i => hY n (f.comp (a i))
  let b : FreeIndex G ι → C(Disk n,Y) := fun i =>
    ⟨fun d => i.1 • e i.2 d,(continuous_const_smul i.1).comp (e i.2).continuous⟩
  have hb (i : FreeIndex G ι) (x : Sphere n) :
      b i (boundary n x) = f (equivariantFamily a i x) := by
    change i.1 • e i.2 (Cellular.boundary n x) = f (i.1 • a i.2 x)
    rw [he,hf]
    rfl
  refine ⟨lift _ f b hb,fun _ => rfl,?_⟩
  intro g x
  cases x with
  | inl x => exact hf g x
  | inr p => exact (mul_smul g p.1.1 (e p.1.2 (interior n p.2)))

lemma compactFundamentalSet [Finite ι] (hX : Milnor.CompactFundamentalSet G (X := X)) :
    Milnor.CompactFundamentalSet G (X := Space (equivariantFamily (G := G) a)) := by
  let b := equivariantFamily (G := G) a
  obtain ⟨K,hK,hcov⟩ := hX
  let L : Set (Space b) := (base b '' K) ∪ ⋃ i : ι, Set.range (cell b ((1:G),i))
  refine ⟨L,(hK.image (continuous_base b)).union (isCompact_iUnion (fun i =>
    isCompact_range (cell b ((1:G),i)).continuous)),?_⟩
  intro x
  cases x with
  | inl x =>
    obtain ⟨g,y,hy,rfl⟩ := hcov x
    exact ⟨g,base b y,Or.inl ⟨y,hy,rfl⟩,rfl⟩
  | inr p =>
    refine ⟨p.1.1,cell b ((1:G),p.1.2) (interior n p.2),?_,?_⟩
    · exact Or.inr (Set.mem_iUnion.mpr ⟨p.1.2,Set.mem_range_self _⟩)
    · refine Eq.trans ?_ (congrArg (fun point : Space b => p.1.1 • point)
        (cell_interior b (1,p.1.2) p.2)).symm
      exact congrArg (fun first : G => openCell b (first,p.1.2) p.2)
        (mul_one p.1.1).symm
end UniversalFInfinity.Attachment

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.CoveringAttachments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology

namespace UniversalFInfinity.Attachment
open Set Metric Topology
variable {X : Type*} [TopologicalSpace X] {ι : Type*} {n : ℕ}
variable (a : ι → C(Sphere n,X))

def cellCenter (i : ι) : Space a := openCell a i ⟨0,by simp⟩
def punctured : Set (Space a) := (Set.range (cellCenter a))ᶜ

def rawCoordinate : Space a → (Fin n → ℝ)
  | Sum.inl _ => 0 | Sum.inr p => p.2.1

lemma base_mem_punctured (x : X) : base a x ∈ punctured a := by
  rintro ⟨i,h⟩
  cases h

lemma cell_mem_punctured (i : ι) (d : Disk n) : cell a i d ∈ punctured a ↔ d.1 ≠ 0 := by
  classical
  constructor
  · intro hd hzero
    apply hd
    refine ⟨i,?_⟩
    have heq : d = interior n ⟨0,by simp⟩ := Subtype.ext hzero
    rw [heq,cell_interior]
    rfl
  · intro hzero
    rintro ⟨j,hj⟩
    by_cases h : d.1 ∈ ball (0 : Fin n → ℝ) 1
    · have heq : d = interior n ⟨d.1,h⟩ := rfl
      rw [heq,cell_interior] at hj
      exact hzero (congrArg (rawCoordinate a) hj).symm
    · let s : Sphere n := ⟨d.1,by
        have hd := d.2
        simp only [mem_sphere,mem_ball,mem_closedBall] at *
        exact le_antisymm hd (le_of_not_gt h)⟩
      have heq : d = boundary n s := rfl
      rw [heq,cell_boundary] at hj
      cases hj

lemma punctured_open : IsOpen (punctured a) := by
  change IsOpen (Set.range (cellCenter a))ᶜ
  rw [isOpen_compl_iff]
  rw [isClosed_iff]
  constructor
  · have h : base a ⁻¹' Set.range (cellCenter a) = ∅ := by
      ext x
      simp only [mem_preimage,mem_empty_iff_false,iff_false]
      exact base_mem_punctured a x
    rw [h]
    exact isClosed_empty
  · intro i
    have h : cell a i ⁻¹' Set.range (cellCenter a) = {d : Disk n | d.1 = 0} := by
      ext d
      exact not_iff_not.mp (cell_mem_punctured a i d)
    rw [h]
    exact isClosed_eq continuous_subtype_val continuous_const

lemma continuous_punctured {Y : Type*} [TopologicalSpace Y] (F : punctured a → Y)
    (hb : Continuous (fun x : X => F ⟨base a x,base_mem_punctured a x⟩))
    (hc : ∀ i, Continuous (fun d : {d : Disk n // d.1 ≠ 0} =>
      F ⟨cell a i d.1,(cell_mem_punctured a i d.1).mpr d.2⟩)) : Continuous F := by
  let q := quotient a
  have hq : IsQuotientMap q := ⟨⟨rfl⟩,quotient_surjective a⟩
  have hp := hq.restrictPreimage_isOpen (punctured_open a)
  apply hp.continuous_iff.mpr
  apply continuous_iff_continuousAt.mpr
  rintro ⟨z,hz⟩
  cases z with
  | inl x =>
    let e : X → q ⁻¹' punctured a := fun x => ⟨Sum.inl x,base_mem_punctured a x⟩
    have he : IsOpenEmbedding e := by
      have hi : IsOpenEmbedding (Sum.inl : X → X ⊕ (Σ _ : ι, Disk n)) := .inl
      exact ⟨hi.isEmbedding.codRestrict (q ⁻¹' punctured a) (fun x => base_mem_punctured a x),by
        have hr : Set.range e = Subtype.val ⁻¹' Set.range Sum.inl := by
          ext z
          simp only [mem_range,mem_preimage,e]
          constructor
          · rintro ⟨x,rfl⟩; exact ⟨x,rfl⟩
          · rintro ⟨x,hx⟩; exact ⟨x,Subtype.ext hx⟩
        rw [hr]
        exact hi.isOpen_range.preimage continuous_subtype_val⟩
    exact (he.continuousAt_iff (g := F ∘ (punctured a).restrictPreimage q)).mp (hb.continuousAt (x := x))
  | inr p =>
    rcases p with ⟨i,d⟩
    have hd : d.1 ≠ 0 := (cell_mem_punctured a i d).mp hz
    let e : {d : Disk n // d.1 ≠ 0} → q ⁻¹' punctured a :=
      fun d => ⟨Sum.inr ⟨i,d.1⟩,(cell_mem_punctured a i d.1).mpr d.2⟩
    have he : IsOpenEmbedding e := by
      have hi : IsOpenEmbedding (fun d : Disk n => (Sum.inr ⟨i,d⟩ : X ⊕ (Σ _ : ι, Disk n))) :=
        IsOpenEmbedding.inr.comp IsOpenEmbedding.sigmaMk
      exact hi.restrict (fun d hd => (cell_mem_punctured a i d).mpr hd)
        (isClosed_eq continuous_subtype_val continuous_const).isOpen_compl
    have hc' : ContinuousAt ((F ∘ (punctured a).restrictPreimage q) ∘ e) ⟨d,hd⟩ := by
      change ContinuousAt (fun d : {d : Disk n // d.1 ≠ 0} =>
        F ⟨cell a i d.1,(cell_mem_punctured a i d.1).mpr d.2⟩) ⟨d,hd⟩
      exact (hc i).continuousAt
    have result := (he.continuousAt_iff (g := F ∘ (punctured a).restrictPreimage q)).mp hc'
    exact result

abbrev PuncturedDisk (n : ℕ) := {d : Disk n // d.1 ≠ 0}

def puncturedBoundary (x : Sphere n) : PuncturedDisk n :=
  ⟨boundary n x,by
    intro h
    change x.1 = 0 at h
    have hx := x.2
    simp only [mem_sphere,dist_zero_right] at hx
    rw [h,norm_zero] at hx
    norm_num at hx⟩

def puncturedCell (i : ι) (d : PuncturedDisk n) : punctured a :=
  ⟨cell a i d.1,(cell_mem_punctured a i d.1).mpr d.2⟩

def puncturedBase (x : X) : punctured a := ⟨base a x,base_mem_punctured a x⟩

lemma puncturedCell_boundary (i : ι) (x : Sphere n) :
    puncturedCell a i (puncturedBoundary x) = puncturedBase a (a i x) :=
  Subtype.ext (cell_boundary a i x)

noncomputable def puncturedLift {Y : Type*} [TopologicalSpace Y] (f : C(X,Y))
    (g : ι → C(PuncturedDisk n,Y))
    (h : ∀ i x, g i (puncturedBoundary x) = f (a i x)) : C(punctured a,Y) := by
  classical
  let F : punctured a → Y := fun z => match heq : z.1 with
    | Sum.inl x => f x
    | Sum.inr p => g p.1 ⟨interior n p.2,by
        exact (cell_mem_punctured a p.1 (interior n p.2)).mp
          (by simpa only [cell_interior,← heq] using z.2)⟩
  have hcell (i : ι) : F ∘ puncturedCell a i = g i := by
    funext d
    by_cases hd : d.1.1 ∈ ball (0 : Fin n → ℝ) 1
    · have heq : d.1 = interior n ⟨d.1.1,hd⟩ := rfl
      change F ⟨cell a i d.1,_⟩ = g i d
      have hc : cell a i d.1 = Sum.inr ⟨i,⟨d.1.1,hd⟩⟩ := (congrArg (cell a i) heq).trans (cell_interior a i ⟨d.1.1,hd⟩)
      simp only [hc,F]
      exact congrArg (g i) (Subtype.ext (Subtype.ext rfl))
    · let x : Sphere n := ⟨d.1.1,by
        have hm := d.1.2
        simp only [mem_closedBall,mem_ball,mem_sphere] at *
        exact le_antisymm hm (le_of_not_gt hd)⟩
      have heq : d.1 = boundary n x := rfl
      change F ⟨cell a i d.1,_⟩ = g i d
      have hc : cell a i d.1 = base a (a i x) := (congrArg (cell a i) heq).trans (cell_boundary a i x)
      simp only [hc,base,F]
      exact (h i x).symm.trans (congrArg (g i) (Subtype.ext (Subtype.ext rfl)))
  exact ⟨F,continuous_punctured a F f.continuous (fun i => by
    change Continuous (F ∘ puncturedCell a i)
    rw [hcell]
    exact (g i).continuous)⟩

@[simp] lemma puncturedLift_base {Y : Type*} [TopologicalSpace Y] (f : C(X,Y))
    (g : ι → C(PuncturedDisk n,Y))
    (h : ∀ i x, g i (puncturedBoundary x) = f (a i x)) (x : X) :
    puncturedLift a f g h (puncturedBase a x) = f x := rfl

@[simp] lemma puncturedLift_cell {Y : Type*} [TopologicalSpace Y] (f : C(X,Y))
    (g : ι → C(PuncturedDisk n,Y))
    (h : ∀ i x, g i (puncturedBoundary x) = f (a i x))
    (i : ι) (d : PuncturedDisk n) :
    puncturedLift a f g h (puncturedCell a i d) = g i d := by
  classical
  by_cases hd : d.1.1 ∈ ball (0 : Fin n → ℝ) 1
  · have heq : d.1 = interior n ⟨d.1.1,hd⟩ := rfl
    change puncturedLift a f g h ⟨cell a i d.1,_⟩ = _
    have hc : cell a i d.1 = Sum.inr ⟨i,⟨d.1.1,hd⟩⟩ := (congrArg (cell a i) heq).trans (cell_interior a i ⟨d.1.1,hd⟩)
    simp only [hc,puncturedLift,ContinuousMap.coe_mk]
    exact congrArg (g i) (Subtype.ext (Subtype.ext rfl))
  · let x : Sphere n := ⟨d.1.1,by
      have hm := d.1.2
      simp only [mem_closedBall,mem_ball,mem_sphere] at *
      exact le_antisymm hm (le_of_not_gt hd)⟩
    have hd : d = puncturedBoundary x := rfl
    rw [hd,puncturedCell_boundary,puncturedLift_base,h]

lemma punctured_surjective (z : punctured a) :
    (∃ x, z = puncturedBase a x) ∨ ∃ i d, z = puncturedCell a i d := by
  cases heq : z.1 with
  | inl x => exact Or.inl ⟨x,Subtype.ext heq⟩
  | inr p =>
    have hd : p.2.1 ≠ 0 := (cell_mem_punctured a p.1 (interior n p.2)).mp
      (by simpa only [cell_interior,← heq] using z.2)
    exact Or.inr ⟨p.1,⟨interior n p.2,hd⟩,Subtype.ext (heq.trans (cell_interior a p.1 p.2).symm)⟩

def radialSphere : C(PuncturedDisk n,Sphere n) := by
  have hm (d : PuncturedDisk n) : ‖d.1.1‖⁻¹ • d.1.1 ∈ sphere (0 : Fin n → ℝ) 1 := by
    simp only [mem_sphere,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_inv,
      abs_norm,inv_mul_cancel₀ (norm_ne_zero_iff.mpr d.2)]
  refine ⟨fun d => ⟨‖d.1.1‖⁻¹ • d.1.1,hm d⟩,?_⟩
  exact (((continuous_subtype_val.comp continuous_subtype_val).norm.inv₀
    (fun d : PuncturedDisk n => norm_ne_zero_iff.mpr d.2)).smul
      (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk hm

@[simp] lemma radialSphere_boundary (x : Sphere n) : radialSphere (puncturedBoundary x) = x := by
  apply Subtype.ext
  have hx : ‖x.1‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using x.2
  change ‖x.1‖⁻¹ • x.1 = x.1
  rw [hx,inv_one,one_smul]

def radialDisk : C(unitInterval × PuncturedDisk n,Disk n) := by
  let f (p : unitInterval × PuncturedDisk n) :=
    (1-(p.1:ℝ)) • p.2.1.1 + (p.1:ℝ) • (radialSphere p.2).1
  have hm (p : unitInterval × PuncturedDisk n) : f p ∈ closedBall (0 : Fin n → ℝ) 1 :=
    (convex_closedBall (0 : Fin n → ℝ) 1) p.2.1.2
      (sphere_subset_closedBall (radialSphere p.2).2)
      (sub_nonneg.mpr p.1.2.2) p.1.2.1 (by ring)
  have hc : Continuous f :=
    ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
      (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd))).add
      ((continuous_subtype_val.comp continuous_fst).smul
        (continuous_subtype_val.comp (radialSphere.continuous.comp continuous_snd)))
  exact ⟨fun p => ⟨f p,hm p⟩,hc.subtype_mk hm⟩

@[simp] lemma radialDisk_zero (d : PuncturedDisk n) : radialDisk (0,d) = d.1 := by
  apply Subtype.ext
  simp [radialDisk]
@[simp] lemma radialDisk_one (d : PuncturedDisk n) : radialDisk (1,d) = boundary n (radialSphere d) := by
  apply Subtype.ext
  simp [radialDisk,boundary]
@[simp] lemma radialDisk_boundary (t : unitInterval) (x : Sphere n) :
    radialDisk (t,puncturedBoundary x) = boundary n x := by
  apply Subtype.ext
  simp only [radialDisk,ContinuousMap.coe_mk,radialSphere_boundary]
  change (1-(t:ℝ)) • x.1 + (t:ℝ) • x.1 = x.1
  rw [← add_smul,sub_add_cancel,one_smul]

def radialRetraction : C(punctured a,X) :=
  puncturedLift a (.id X) (fun i => (a i).comp radialSphere)
    (fun i x => by simp only [ContinuousMap.comp_apply,radialSphere_boundary,ContinuousMap.id_apply])

@[simp] lemma radialRetraction_base (x : X) : radialRetraction a (puncturedBase a x) = x := rfl
@[simp] lemma radialRetraction_cell (i : ι) (d : PuncturedDisk n) :
    radialRetraction a (puncturedCell a i d) = a i (radialSphere d) := by
  exact puncturedLift_cell _ _ _ _ _ _

def radialPaths : C(punctured a,C(unitInterval,Space a)) := by
  let f : C(X × unitInterval,Space a) := ⟨fun p => base a p.1,(continuous_base a).comp continuous_fst⟩
  let g (i : ι) : C(PuncturedDisk n × unitInterval,Space a) :=
    (cell a i).comp (radialDisk.comp ⟨Prod.swap,continuous_swap⟩)
  have h (i : ι) (x : Sphere n) : (g i).curry (puncturedBoundary x) = f.curry (a i x) := by
    ext t
    change cell a i (radialDisk (t,puncturedBoundary x)) = base a (a i x)
    rw [radialDisk_boundary,cell_boundary]
  exact puncturedLift a f.curry (fun i => (g i).curry) h

@[simp] lemma radialPaths_base (x : X) (t : unitInterval) :
    radialPaths a (puncturedBase a x) t = base a x := rfl
@[simp] lemma radialPaths_cell (i : ι) (d : PuncturedDisk n) (t : unitInterval) :
    radialPaths a (puncturedCell a i d) t = cell a i (radialDisk (t,d)) := by
  unfold radialPaths
  rw [puncturedLift_cell]
  rfl

def puncturedInclusion : C(punctured a,Space a) := ⟨Subtype.val,continuous_subtype_val⟩
def radialEnd : C(punctured a,Space a) := (⟨base a,continuous_base a⟩ : C(X,Space a)).comp (radialRetraction a)

def radialHomotopy : (puncturedInclusion a).Homotopy (radialEnd a) where
  toFun p := radialPaths a p.2 p.1
  continuous_toFun := (radialPaths a).uncurry.continuous.comp continuous_swap
  map_zero_left z := by
    rcases punctured_surjective a z with ⟨x,rfl⟩ | ⟨i,d,rfl⟩
    · rfl
    · rw [radialPaths_cell,radialDisk_zero]
      rfl
  map_one_left z := by
    rcases punctured_surjective a z with ⟨x,rfl⟩ | ⟨i,d,rfl⟩
    · rfl
    · rw [radialPaths_cell,radialDisk_one,cell_boundary]
      change base a (a i (radialSphere d)) = base a (radialRetraction a (puncturedCell a i d))
      rw [radialRetraction_cell]

@[simp] lemma radialHomotopy_base (x : X) (t : unitInterval) :
    radialHomotopy a (t,puncturedBase a x) = base a x := rfl

lemma cell_eq_openCell_iff (i j : ι) (d : Disk n) (x : OpenDisk n) :
    cell a i d = openCell a j x ↔ i = j ∧ d.1 = x.1 := by
  classical
  constructor
  · intro h
    by_cases hd : d.1 ∈ ball (0 : Fin n → ℝ) 1
    · have hi : cell a i d = Sum.inr ⟨i,⟨d.1,hd⟩⟩ :=
        cell_interior a i ⟨d.1,hd⟩
      rw [hi] at h
      have hh : (⟨i,⟨d.1,hd⟩⟩ : Σ _ : ι, OpenDisk n) = ⟨j,x⟩ := Sum.inr_injective h
      exact ⟨congrArg Sigma.fst hh,congrArg (fun p : Σ _ : ι, OpenDisk n => p.2.1) hh⟩
    · let s : Sphere n := ⟨d.1,by
        have hm := d.2
        simp only [mem_sphere,mem_ball,mem_closedBall] at *
        exact le_antisymm hm (le_of_not_gt hd)⟩
      have hi : cell a i d = base a (a i s) := cell_boundary a i s
      rw [hi] at h
      cases h
  · rintro ⟨rfl,h⟩
    have hd : d = interior n x := Subtype.ext h
    rw [hd,cell_interior]
    rfl

lemma openCell_disjoint (i j : ι) (hij : i ≠ j) :
    Disjoint (Set.range (openCell a i)) (Set.range (openCell a j)) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨x,rfl⟩ ⟨y,h⟩
  exact hij (congrArg Sigma.fst (Sum.inr_injective h)).symm

lemma openCell_selection_closed {I : Type*} (c : I → ι) (hc : Function.Injective c)
    (x : I → OpenDisk n) (S : Set (Space a))
    (hS : S ⊆ Set.range (fun i => openCell a (c i) (x i))) : IsClosed S := by
  rw [isClosed_iff]
  constructor
  · have h : base a ⁻¹' S = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro y hy
      obtain ⟨i,hi⟩ := hS hy
      cases hi
    rw [h]
    exact isClosed_empty
  · intro j
    suffices (cell a j ⁻¹' S).Subsingleton from this.finite.isClosed
    intro d hd e he
    obtain ⟨i,hi⟩ := hS hd
    obtain ⟨k,hk⟩ := hS he
    have hdi := (cell_eq_openCell_iff a j (c i) d (x i)).mp hi.symm
    have hek := (cell_eq_openCell_iff a j (c k) e (x k)).mp hk.symm
    have hik : i = k := hc (hdi.1.symm.trans hek.1)
    subst k
    exact Subtype.ext (hdi.2.trans hek.2.symm)

lemma compact_finitely_many_openCells {K : Set (Space a)} (hK : IsCompact K) :
    {i : ι | (K ∩ Set.range (openCell a i)).Nonempty}.Finite := by
  classical
  let I := {i : ι | (K ∩ Set.range (openCell a i)).Nonempty}
  have hchoice (i : I) : ∃ x : OpenDisk n, openCell a i.1 x ∈ K := by
    obtain ⟨z,hz,⟨x,hx⟩⟩ := i.2
    exact ⟨x,hx ▸ hz⟩
  choose x hx using hchoice
  let y : I → Space a := fun i => openCell a i.1 (x i)
  have hyinj : Function.Injective y := by
    intro i j h
    apply Subtype.ext
    exact congrArg Sigma.fst (Sum.inr_injective h)
  have hclosed : ∀ S ⊆ Set.range y, IsClosed S :=
    openCell_selection_closed a Subtype.val Subtype.val_injective x
  have hcompact : IsCompact (Set.range y) := hK.of_isClosed_subset
    (hclosed _ subset_rfl) (Set.range_subset_iff.mpr hx)
  have hdisc : IsDiscrete (Set.range y) := by
    apply isDiscrete_iff_forall_mem_exists_isClosed.mpr
    intro S hS
    exact ⟨S,hclosed S hS,Set.inter_eq_left.mpr hS⟩
  have hrange := hcompact.finite hdisc
  have : Finite I := (Set.finite_range_iff hyinj).mp hrange
  exact Set.toFinite I

end UniversalFInfinity.Attachment

open Set Topology
namespace UniversalFInfinity.Cellular
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def patchFun (A : Set X) (f : C(X,Y)) (g : C(A,Y)) (x : X) : Y := by
  classical
  exact if hx : x ∈ A then g ⟨x,hx⟩ else f x

lemma patchFun_on (A : Set X) (f : C(X,Y)) (g : C(A,Y)) (x : A) :
    patchFun A f g x = g x := by simp only [patchFun,dite_eq_left x.2]

lemma patchFun_off (A : Set X) (f : C(X,Y)) (g : C(A,Y)) {x : X} (hx : x ∉ A) :
    patchFun A f g x = f x := by simp only [patchFun,dite_eq_right hx]

lemma continuous_patchFun {A : Set X} (hA : IsClosed A) (f : C(X,Y)) (g : C(A,Y))
    (hboundary : ∀ (x : A), (x:X) ∈ frontier A → g x = f x) :
    Continuous (patchFun A f g) := by
  classical
  have hOn : ContinuousOn (patchFun A f g) A := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : A.domRestrict (patchFun A f g) = g := funext (patchFun_on A f g)
    rw [heq]
    exact g.continuous
  have h := continuous_if (p := fun x => x ∈ A) (f := patchFun A f g) (g := f)
    (fun x hx => by
      have hxa : x ∈ A := hA.closure_eq ▸ hx.1
      exact (patchFun_on A f g ⟨x,hxa⟩).trans (hboundary ⟨x,hxa⟩ hx))
    (by simpa only [Set.ofPred_mem_eq,hA.closure_eq] using hOn) f.continuous.continuousOn
  convert h using 1
  ext x
  by_cases hx : x ∈ A
  · simp only [ite_eq_left hx]
  · simp only [ite_eq_right hx,patchFun_off A f g hx]

def patch {A : Set X} (hA : IsClosed A) (f : C(X,Y)) (g : C(A,Y))
    (hboundary : ∀ (x : A), (x:X) ∈ frontier A → g x = f x) : C(X,Y) :=
  ⟨patchFun A f g,continuous_patchFun hA f g hboundary⟩

lemma patch_on {A : Set X} (hA : IsClosed A) (f : C(X,Y)) (g : C(A,Y))
    (hboundary : ∀ (x : A), (x:X) ∈ frontier A → g x = f x) (x : A) :
    patch hA f g hboundary x = g x := patchFun_on A f g x

lemma patch_off {A : Set X} (hA : IsClosed A) (f : C(X,Y)) (g : C(A,Y))
    (hboundary : ∀ (x : A), (x:X) ∈ frontier A → g x = f x) {x : X} (hx : x ∉ A) :
    patch hA f g hboundary x = f x := patchFun_off A f g hx

def patchHomotopy {A : Set X} (hA : IsClosed A) (f : C(X,Y)) (g : C(A,Y))
    (H : (f.restrict A).Homotopy g)
    (hboundary : ∀ (t : unitInterval) (x : A), (x:X) ∈ frontier A → H (t,x) = f x) :
    f.Homotopy (patch hA f g (fun x hx => by simpa using hboundary 1 x hx)) := by
  let B : Set (unitInterval × X) := Prod.snd ⁻¹' A
  let H' : C(B,Y) := ⟨fun z => H (z.1.1,⟨z.1.2,z.2⟩),
    H.continuous.comp ((continuous_fst.comp continuous_subtype_val).prodMk
      ((continuous_snd.comp continuous_subtype_val).subtype_mk _))⟩
  let hB : IsClosed B := hA.preimage continuous_snd
  let F : C(unitInterval × X,Y) := f.comp ⟨Prod.snd,continuous_snd⟩
  have hb : ∀ z : B, (z : unitInterval × X) ∈ frontier B → H' z = F z := by
    intro z hz
    exact hboundary z.1.1 ⟨z.1.2,z.2⟩ (continuous_snd.frontier_preimage_subset A hz)
  refine ⟨patch hB F H' hb,?_,?_⟩
  · intro x
    change patch hB F H' hb (0,x) = f x
    by_cases hx : x ∈ A
    · rw [patch_on hB F H' hb ⟨(0,x),hx⟩]
      exact H.apply_zero ⟨x,hx⟩
    · exact patch_off hB F H' hb (x := (_,x)) hx
  · intro x
    change patch hB F H' hb (1,x) = patch hA f g _ x
    by_cases hx : x ∈ A
    · rw [patch_on hB F H' hb ⟨(1,x),hx⟩,patch_on hA f g _ ⟨x,hx⟩]
      exact H.apply_one ⟨x,hx⟩
    · rw [patch_off hB F H' hb (x := (_,x)) hx,patch_off hA f g _ hx]
      rfl

end UniversalFInfinity.Cellular

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.CellRetractions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology

open Set Metric Topology
open scoped NNReal
namespace UniversalFInfinity.GeneralPosition

section
variable {K : Type*} [MetricSpace K] [CompactSpace K]

lemma lipschitz_mul {f g : C(K,ℝ)} {L M : ℝ≥0}
    (hf : LipschitzWith L f) (hg : LipschitzWith M g) :
    LipschitzWith (‖f‖₊ * M + ‖g‖₊ * L) (f * g) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [ContinuousMap.mul_apply,NNReal.coe_add,NNReal.coe_mul,coe_nnnorm]
  calc
    dist (f x * g x) (f y * g y)
        = ‖f x * (g x-g y) + g y * (f x-f y)‖ := by
          rw [dist_eq_norm]; congr 1; ring
    _ ≤ ‖f x * (g x-g y)‖ + ‖g y * (f x-f y)‖ := norm_add_le _ _
    _ = ‖f x‖ * dist (g x) (g y) + ‖g y‖ * dist (f x) (f y) := by
      rw [norm_mul,norm_mul,dist_eq_norm,dist_eq_norm]
    _ ≤ ‖f‖ * ((M:ℝ) * dist x y) + ‖g‖ * ((L:ℝ) * dist x y) := by
      gcongr
      · exact f.norm_coe_le_norm x
      · exact hg.dist_le_mul x y
      · exact g.norm_coe_le_norm y
      · exact hf.dist_le_mul x y
    _ = (‖f‖ * M + ‖g‖ * L) * dist x y := by ring

def lipschitzAlgebra : Subalgebra ℝ C(K,ℝ) where
  carrier := {f | ∃ L, LipschitzWith L f}
  zero_mem' := ⟨0,LipschitzWith.const 0⟩
  one_mem' := ⟨0,LipschitzWith.const 1⟩
  add_mem' := by rintro f g ⟨L,hL⟩ ⟨M,hM⟩; exact ⟨L+M,hL.add hM⟩
  mul_mem' := by rintro f g ⟨L,hL⟩ ⟨M,hM⟩; exact ⟨_,lipschitz_mul hL hM⟩
  algebraMap_mem' r := ⟨0,LipschitzWith.const r⟩

lemma lipschitzAlgebra_separates : (lipschitzAlgebra (K := K)).SeparatesPoints := by
  intro x y hxy
  refine ⟨fun z => dist z y,⟨⟨fun z => dist z y,continuous_id.dist continuous_const⟩,
    ⟨1,LipschitzWith.dist_left y⟩,rfl⟩,?_⟩
  simpa using hxy

lemma exists_lipschitz_approximation (f : C(K,ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : C(K,ℝ), (∃ L, LipschitzWith L g) ∧ ∀ x, ‖g x-f x‖ < ε := by
  obtain ⟨g,hg⟩ := ContinuousMap.exists_mem_subalgebra_near_continuous_of_separatesPoints
    lipschitzAlgebra lipschitzAlgebra_separates f f.continuous ε hε
  exact ⟨g,g.2,hg⟩

end

section
open Set Metric Topology
open scoped NNReal ENNReal
variable {K : Type*} [MetricSpace K] [CompactSpace K]

lemma exists_lipschitz_vector_approximation {n : ℕ} (f : C(K,Fin n → ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : C(K,Fin n → ℝ), (∃ L, LipschitzWith L g) ∧ ∀ x, ‖g x-f x‖ < ε := by
  classical
  have hex : ∀ i : Fin n, ∃ g : C(K,ℝ), (∃ L, LipschitzWith L g) ∧
      ∀ x, ‖g x-f x i‖ < ε := fun i =>
    exists_lipschitz_approximation ⟨fun x => f x i,(continuous_apply i).comp f.continuous⟩ hε
  choose g hg he using hex
  choose L hL using hg
  let H : C(K,Fin n → ℝ) := ⟨fun x i => g i x,continuous_pi (fun i => (g i).continuous)⟩
  refine ⟨H,⟨Finset.univ.sup L,?_⟩,?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_pi_le_iff (mul_nonneg (NNReal.coe_nonneg _) dist_nonneg)]
    intro i
    exact (hL i).dist_le_mul x y |>.trans (mul_le_mul_of_nonneg_right
      (by exact_mod_cast Finset.le_sup (f := L) (Finset.mem_univ i)) dist_nonneg)
  · intro x
    exact (pi_norm_lt_iff hε).mpr (fun i => he i x)

omit [CompactSpace K] in

lemma exists_missing_point {n : ℕ} {g : K → Fin n → ℝ} {L : ℝ≥0}
    (hg : LipschitzWith L g) (hdim : dimH (Set.univ : Set K) < n)
    (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r) :
    ∃ a ∈ Metric.ball c r, a ∉ Set.range g := by
  by_contra! h
  have hle : dimH (Metric.ball c r) ≤ dimH (Set.range g) := dimH_mono h
  rw [Real.dimH_ball_pi_fin _ hr] at hle
  exact (not_le_of_gt hdim) (hle.trans hg.dimH_range_le)

lemma exists_nonzero_approximation {n : ℕ} (f : C(K,Fin n → ℝ))
    (hdim : dimH (Set.univ : Set K) < n) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : C(K,Fin n → ℝ), (∀ x, g x ≠ 0) ∧ ∀ x, ‖g x-f x‖ < ε := by
  obtain ⟨h,⟨L,hL⟩,hh⟩ := exists_lipschitz_vector_approximation f (half_pos hε)
  obtain ⟨a,ha,ha'⟩ := exists_missing_point hL hdim 0 (half_pos hε)
  refine ⟨h - ContinuousMap.const K a,?_,?_⟩
  · intro x hx
    apply ha'
    exact ⟨x,sub_eq_zero.mp hx⟩
  · intro x
    have ha : ‖a‖ < ε/2 := by simpa only [Metric.mem_ball,dist_zero_right] using ha
    change ‖(h x-a)-f x‖ < ε
    have hhx := hh x
    calc
      ‖(h x-a)-f x‖ = ‖(h x-f x)-a‖ := by congr 1; abel
      _ ≤ ‖h x-f x‖+‖a‖ := norm_sub_le _ _
      _ < ε := by linarith

end

open Set Metric Topology
open scoped NNReal ENNReal
variable {K : Type*} [MetricSpace K] [CompactSpace K]

def cutoff (δ r : ℝ) : ℝ := min 1 (max 0 (2-r/δ))
lemma cutoff_nonneg (δ r : ℝ) : 0 ≤ cutoff δ r := le_min (by norm_num) (le_max_left _ _)
lemma cutoff_le_one (δ r : ℝ) : cutoff δ r ≤ 1 := min_le_left _ _
lemma cutoff_small {δ r : ℝ} (hδ : 0 < δ) (hr : r ≤ δ) : cutoff δ r = 1 := by
  apply min_eq_left
  apply le_max_of_le_right
  have : r/δ ≤ 1 := (div_le_one hδ).mpr hr
  linarith
lemma cutoff_large {δ r : ℝ} (hδ : 0 < δ) (hr : 2*δ ≤ r) : cutoff δ r = 0 := by
  have : 2 ≤ r/δ := (le_div_iff₀ hδ).mpr hr
  simp only [cutoff,max_eq_left (by linarith : 2-r/δ ≤ 0),min_eq_right (by norm_num : (0:ℝ)≤1)]
lemma continuous_cutoff (δ : ℝ) : Continuous (cutoff δ) :=
  continuous_const.min (continuous_const.max (continuous_const.sub (continuous_id.div_const δ)))

lemma exists_relative_nonzero_approximation {n : ℕ} (f : C(K,Fin n → ℝ))
    (hdim : dimH (Set.univ : Set K) < n) {δ : ℝ} (hδ : 0 < δ) :
    ∃ g : C(K,Fin n → ℝ), (∀ x, g x ≠ 0) ∧
      (∀ x, 2*δ ≤ ‖f x‖ → g x = f x) ∧ ∀ x, ‖g x-f x‖ < δ/2 := by
  obtain ⟨h,hne,hh⟩ := exists_nonzero_approximation f hdim (half_pos hδ)
  let g : C(K,Fin n → ℝ) := ⟨fun x => f x + cutoff δ ‖f x‖ • (h x-f x),
    f.continuous.add (((continuous_cutoff δ).comp f.continuous.norm).smul
      (h.continuous.sub f.continuous))⟩
  have hdist (x : K) : ‖g x-f x‖ < δ/2 := by
    change ‖(f x+cutoff δ ‖f x‖ • (h x-f x))-f x‖ < δ/2
    rw [add_sub_cancel_left,norm_smul,Real.norm_of_nonneg (cutoff_nonneg _ _)]
    exact (mul_le_of_le_one_left (norm_nonneg _) (cutoff_le_one _ _)).trans_lt (hh x)
  refine ⟨g,?_,?_,hdist⟩
  · intro x hx
    by_cases hnorm : ‖f x‖ ≤ δ
    · have hg : g x = h x := by
        change f x+cutoff δ ‖f x‖ • (h x-f x)=h x
        rw [cutoff_small hδ hnorm,one_smul,add_sub_cancel]
      exact hne x (hg.symm.trans hx)
    · have hd := hdist x
      rw [hx,zero_sub,norm_neg] at hd
      linarith
  · intro x hx
    change f x+cutoff δ ‖f x‖ • (h x-f x)=f x
    rw [cutoff_large hδ hx,zero_smul,add_zero]

omit [MetricSpace K] [CompactSpace K] in

lemma relative_interpolation_bound {n : ℕ} {f g : K → Fin n → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hfix : ∀ x, 2*δ ≤ ‖f x‖ → g x = f x)
    (hdist : ∀ x, ‖g x-f x‖ < δ/2)
    (x : K) (hx : ‖f x‖ ≤ 4*δ) (t : unitInterval) :
    ‖f x+(t:ℝ) • (g x-f x)‖ ≤ 4*δ := by
  by_cases hc : 2*δ ≤ ‖f x‖
  · rw [hfix x hc,sub_self,smul_zero,add_zero]
    exact hx
  · have ht : ‖(t:ℝ) • (g x-f x)‖ ≤ ‖g x-f x‖ := by
      rw [norm_smul,Real.norm_of_nonneg t.2.1]
      exact mul_le_of_le_one_left (norm_nonneg _) t.2.2
    have hsum := norm_add_le (f x) ((t:ℝ) • (g x-f x))
    have hd := hdist x
    linarith

end UniversalFInfinity.GeneralPosition

namespace UniversalFInfinity.Cellular

section
open Set Metric Topology
open scoped ENNReal NNReal
variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] {n : ℕ}

abbrev ChartDisk (n : ℕ) := Metric.ball (0 : Fin n → ℝ) 1
abbrev ChartCore (n : ℕ) := Metric.closedBall (0 : Fin n → ℝ) (1/2)

def chartCoreInclusion (n : ℕ) : C(ChartCore n,ChartDisk n) :=
  ⟨fun x => ⟨x.1, (mem_closedBall.mp x.2).trans_lt (by norm_num)⟩,
    continuous_subtype_val.subtype_mk _⟩

def chartCore (e : C(ChartDisk n,Y)) : C(ChartCore n,Y) := e.comp (chartCoreInclusion n)

lemma chartCore_closedEmbedding (e : C(ChartDisk n,Y)) (he : IsOpenEmbedding e) :
    IsClosedEmbedding (chartCore e) := by
  apply (chartCore e).continuous.isClosedEmbedding
  intro x y h
  apply Subtype.ext
  exact congrArg (fun z : ChartDisk n => z.1) (he.injective h)

variable {K : Type*} [MetricSpace K]

def chartDomain (e : C(ChartDisk n,Y)) (f : C(K,Y)) : Set K := f ⁻¹' Set.range (chartCore e)

lemma chartDomain_closed (e : C(ChartDisk n,Y)) (he : IsOpenEmbedding e) (f : C(K,Y)) :
    IsClosed (chartDomain e f) := (chartCore_closedEmbedding e he).isClosed_range.preimage f.continuous

def coreCoordinate (e : C(ChartDisk n,Y)) (he : IsOpenEmbedding e) (f : C(K,Y)) :
    C(chartDomain e f,ChartCore n) :=
  ⟨fun x => (chartCore_closedEmbedding e he).toIsEmbedding.toHomeomorph.symm ⟨f x,x.2⟩,
    (chartCore_closedEmbedding e he).toIsEmbedding.toHomeomorph.symm.continuous.comp
      ((f.continuous.comp continuous_subtype_val).subtype_mk _)⟩

lemma coreCoordinate_fac (e : C(ChartDisk n,Y)) (he : IsOpenEmbedding e) (f : C(K,Y))
    (x : chartDomain e f) : chartCore e (coreCoordinate e he f x) = f x :=
  congrArg Subtype.val ((chartCore_closedEmbedding e he).toIsEmbedding.toHomeomorph.apply_symm_apply _)

lemma coreCoordinate_frontier (e : C(ChartDisk n,Y)) (he : IsOpenEmbedding e) (f : C(K,Y))
    (x : chartDomain e f) (hx : (x:K) ∈ frontier (chartDomain e f)) :
    ‖(coreCoordinate e he f x : Fin n → ℝ)‖ = 1/2 := by
  apply le_antisymm
  · simpa only [mem_closedBall,dist_zero_right] using (coreCoordinate e he f x).2
  · by_contra! h
    let U : Set (ChartDisk n) := {z | ‖(z : Fin n → ℝ)‖ < 1/2}
    have hU : IsOpen U := isOpen_lt (continuous_subtype_val.norm) continuous_const
    have hsub : f ⁻¹' (e '' U) ⊆ chartDomain e f := by
      intro y hy
      obtain ⟨z,hz,hzy⟩ := hy
      exact ⟨⟨z.1,by simpa only [mem_closedBall,dist_zero_right] using le_of_lt hz⟩,hzy⟩
    have hxU : (x:K) ∈ f ⁻¹' (e '' U) := by
      refine ⟨chartCoreInclusion n (coreCoordinate e he f x),h,?_⟩
      exact coreCoordinate_fac e he f x
    exact hx.2 (mem_interior.mpr ⟨f ⁻¹' (e '' U),hsub,
      (he.isOpenMap U hU).preimage f.continuous,hxU⟩)

omit [T2Space Y] in
lemma chartDomain_dimH_le (e : C(ChartDisk n,Y)) (f : C(K,Y)) :
    dimH (Set.univ : Set (chartDomain e f)) ≤ dimH (Set.univ : Set K) := by
  rw [← isometry_subtype_coe.dimH_image]
  exact dimH_mono (Set.subset_univ _)

end

section
open Set Metric Topology
open scoped ENNReal NNReal
variable {Y : Type*} [TopologicalSpace Y] {n : ℕ}
variable {K : Type*} [MetricSpace K]

def chartCenter (e : C(ChartDisk n,Y)) : Y := e ⟨0,by simp⟩

lemma exists_chart_avoidance [T2Space Y] [CompactSpace K] (e : C(ChartDisk n,Y)) (he : IsOpenEmbedding e) (f : C(K,Y))
    (hdim : dimH (Set.univ : Set K) < n) :
    ∃ (g : C(K,Y)) (H : f.Homotopy g),
      (∀ x, g x ≠ chartCenter e) ∧
      (∀ (t : unitInterval) (x : K), f x ∉ Set.range e → H (t,x) = f x) ∧
      (∀ (t : unitInterval) (x : K), H (t,x) = f x ∨ H (t,x) ∈ Set.range e) := by
  let A := chartDomain e f
  have hA : IsClosed A := chartDomain_closed e he f
  let : CompactSpace A := isCompact_iff_compactSpace.mp hA.isCompact
  let u : C(A,Fin n → ℝ) := ⟨fun x => (coreCoordinate e he f x).1,
    continuous_subtype_val.comp (coreCoordinate e he f).continuous⟩
  obtain ⟨v,hv0,hvfix,hvdist⟩ := GeneralPosition.exists_relative_nonzero_approximation u
    ((chartDomain_dimH_le e f).trans_lt hdim) (δ := 1/8) (by norm_num)
  have hi (t : unitInterval) (x : A) : ‖u x+(t:ℝ) • (v x-u x)‖ ≤ 1/2 := by
    have hu : ‖u x‖ ≤ 4*(1/8:ℝ) := by
      simpa only [u,ContinuousMap.coe_mk,show (4:ℝ)*(1/8)=1/2 by norm_num,mem_closedBall,dist_zero_right]
        using (coreCoordinate e he f x).2
    simpa only [show (4:ℝ)*(1/8)=1/2 by norm_num] using
      GeneralPosition.relative_interpolation_bound (by norm_num : (0:ℝ)<1/8)
        hvfix hvdist x hu t
  have hvc (x : A) : v x ∈ ChartCore n := by
    have h := hi 1 x
    simpa only [Set.Icc.coe_one,one_smul,add_sub_cancel,mem_closedBall,dist_zero_right] using h
  let vcore : C(A,ChartCore n) := ⟨fun x => ⟨v x,hvc x⟩,
    v.continuous.subtype_mk hvc⟩
  let gA : C(A,Y) := (chartCore e).comp vcore
  let HA : (f.restrict A).Homotopy gA :=
    { toFun := fun tx => chartCore e ⟨u tx.2+(tx.1:ℝ) • (v tx.2-u tx.2),by
        simpa only [mem_closedBall,dist_zero_right] using hi tx.1 tx.2⟩
      continuous_toFun := (chartCore e).continuous.comp
        (((u.continuous.comp continuous_snd).add
          ((continuous_subtype_val.comp continuous_fst).smul
            ((v.continuous.comp continuous_snd).sub (u.continuous.comp continuous_snd)))).subtype_mk
            (fun tx => by
              simpa only [ChartCore,mem_closedBall,dist_zero_right,Pi.add_apply,
                Pi.smul_apply',Pi.sub_apply,Function.comp_apply] using hi tx.1 tx.2))
      map_zero_left := fun x => by
        simp only [Set.Icc.coe_zero,zero_smul,add_zero]
        exact coreCoordinate_fac e he f x
      map_one_left := fun x => by
        simp only [Set.Icc.coe_one,one_smul,add_sub_cancel]
        rfl }
  have hboundary (t : unitInterval) (x : A) (hx : (x:K) ∈ frontier A) :
      HA (t,x) = f x := by
    have hfix : v x = u x := hvfix x (by
      change 2*(1/8:ℝ) ≤ ‖(coreCoordinate e he f x).1‖
      rw [coreCoordinate_frontier e he f x hx]
      norm_num)
    change chartCore e ⟨u x+(t:ℝ) • (v x-u x),_⟩ = f x
    simp only [hfix,sub_self,smul_zero,add_zero]
    exact coreCoordinate_fac e he f x
  let hg : ∀ x : A, (x:K) ∈ frontier A → gA x = f x :=
    fun x hx => by simpa using hboundary 1 x hx
  let g := patch hA f gA hg
  let H : f.Homotopy g := patchHomotopy hA f gA HA hboundary
  have hOn (t : unitInterval) (x : A) : H (t,(x:K)) = HA (t,x) := by
    change patchFun (Prod.snd ⁻¹' A) _ _ (t,(x:K)) = _
    rw [patchFun,dite_eq_left (show (t,(x:K)) ∈ Prod.snd ⁻¹' A from x.2)]
    rfl
  have hOff (t : unitInterval) (x : K) (hx : x ∉ A) : H (t,x) = f x := by
    change patchFun (Prod.snd ⁻¹' A) _ _ (t,x) = _
    rw [patchFun,dite_eq_right (show (t,x) ∉ Prod.snd ⁻¹' A from hx)]
    rfl
  refine ⟨g,H,?_,?_,?_⟩
  · intro x hzero
    by_cases hx : x ∈ A
    · have hv : chartCore e (vcore ⟨x,hx⟩) = chartCenter e := by
        exact (patch_on hA f gA hg ⟨x,hx⟩).symm.trans hzero
      have hu := congrArg (fun z : ChartDisk n => z.1) (he.injective hv)
      exact hv0 ⟨x,hx⟩ hu
    · have hfx : f x = chartCenter e := (patch_off hA f gA hg hx).symm.trans hzero
      apply hx
      exact ⟨⟨0,by simp⟩,hfx.symm⟩
  · intro t x hx
    apply hOff
    rintro ⟨z,hz⟩
    exact hx ⟨chartCoreInclusion n z,hz⟩
  · intro t x
    by_cases hx : x ∈ A
    · right
      rw [hOn t ⟨x,hx⟩]
      exact ⟨_,rfl⟩
    · exact Or.inl (hOff t x hx)

end

open Set Metric Topology
open scoped ENNReal NNReal
section
variable {Y : Type*} [TopologicalSpace Y] {K : Type*} [TopologicalSpace K]

lemma homotopy_trans_pointwise {f g h : C(K,Y)} (H : f.Homotopy g) (J : g.Homotopy h)
    (P : K → Y → Prop) (hH : ∀ t x, P x (H (t,x))) (hJ : ∀ t x, P x (J (t,x))) :
    ∀ t x, P x (H.trans J (t,x)) := by
  intro t x
  rw [ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact hH _ x
  · exact hJ _ x

end
variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] {n : ℕ}
variable {K : Type*} [MetricSpace K] [CompactSpace K] {ι : Type*}
variable (e : ι → C(ChartDisk n,Y)) (he : ∀ i, IsOpenEmbedding (e i))
variable (hd : Pairwise (fun i j => Disjoint (Set.range (e i)) (Set.range (e j))))

omit [T2Space Y] in
lemma chartCenter_mem_range (i : ι) : chartCenter (e i) ∈ Set.range (e i) := ⟨_,rfl⟩

include he hd in
lemma exists_finite_chart_avoidance (f : C(K,Y)) (hdim : dimH (Set.univ : Set K) < n)
    (S : Finset ι) :
    ∃ (g : C(K,Y)) (H : f.Homotopy g),
      (∀ i ∈ S, ∀ x, g x ≠ chartCenter (e i)) ∧
      (∀ t x, H (t,x) = f x ∨ ∃ i ∈ S, H (t,x) ∈ Set.range (e i)) ∧
      (∀ t x, (∀ i ∈ S, f x ∉ Set.range (e i)) → H (t,x) = f x) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    exact ⟨f,.refl f,by simp,(fun _ _ => Or.inl rfl),fun _ _ _ => rfl⟩
  | @insert a S ha ih =>
    obtain ⟨g,H,hg,hH,hstat⟩ := ih
    obtain ⟨g',J,hg',hJstat,hJ⟩ := exists_chart_avoidance (e a) (he a) g hdim
    refine ⟨g',H.trans J,?_,?_,?_⟩
    · intro i hi x
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact hg' x
      · intro hzero
        rcases hJ 1 x with hj | hj
        · have hh : g' x = g x := by simpa using hj
          exact hg i hi x (hh.symm.trans hzero)
        · have hj : g' x ∈ Set.range (e a) := by simpa using hj
          rw [hzero] at hj
          exact (hd (by intro heq; subst i; exact ha hi)).notMem_of_mem_left hj
            (chartCenter_mem_range e i)
    · apply homotopy_trans_pointwise H J
        (fun x y => y = f x ∨ ∃ i ∈ insert a S, y ∈ Set.range (e i))
      · intro t x
        rcases hH t x with h | ⟨i,hi,h⟩
        · exact Or.inl h
        · exact Or.inr ⟨i,Finset.mem_insert_of_mem hi,h⟩
      · intro t x
        rcases hJ t x with h | h
        · rw [h]
          have hh : g x = f x ∨ ∃ i ∈ S, g x ∈ Set.range (e i) := by simpa using hH 1 x
          rcases hh with h | ⟨i,hi,h⟩
          · exact Or.inl h
          · exact Or.inr ⟨i,Finset.mem_insert_of_mem hi,h⟩
        · exact Or.inr ⟨a,Finset.mem_insert_self _ _,h⟩
    · intro t x hx
      have hfixed : ∀ t, H (t,x) = f x := fun t =>
        hstat t x (fun i hi => hx i (Finset.mem_insert_of_mem hi))
      have hgx : g x = f x := by simpa using hfixed 1
      have hjfixed : ∀ t, J (t,x) = f x := fun t =>
        (hJstat t x (by rw [hgx]; exact hx a (Finset.mem_insert_self _ _))).trans hgx
      rw [ContinuousMap.Homotopy.trans_apply]
      split_ifs
      · exact hfixed _
      · exact hjfixed _

include he hd in
lemma exists_all_chart_avoidance (f : C(K,Y)) (hdim : dimH (Set.univ : Set K) < n)
    (S : Finset ι) (hs : ∀ i, i ∉ S → ∀ x, f x ∉ Set.range (e i)) :
    ∃ (g : C(K,Y)) (H : f.Homotopy g),
      (∀ i x, g x ≠ chartCenter (e i)) ∧
      (∀ t x, (∀ i, f x ∉ Set.range (e i)) → H (t,x) = f x) := by
  classical
  obtain ⟨g,H,hg,hH,hstat⟩ := exists_finite_chart_avoidance e he hd f hdim S
  refine ⟨g,H,?_,?_⟩
  · intro i x
    by_cases hi : i ∈ S
    · exact hg i hi x
    · intro hzero
      have hh : g x = f x ∨ ∃ j ∈ S, g x ∈ Set.range (e j) := by simpa using hH 1 x
      rcases hh with h | ⟨j,hj,h⟩
      · apply hs i hi x
        rw [← h,hzero]
        exact chartCenter_mem_range e i
      · rw [hzero] at h
        exact (hd (by intro heq; subst j; exact hi hj)).notMem_of_mem_left h
          (chartCenter_mem_range e i)
  · intro t x hx
    exact hstat t x (fun i _ => hx i)

end UniversalFInfinity.Cellular

namespace UniversalFInfinity.Attachment
open Set Metric Topology
variable {X : Type*} [TopologicalSpace X] {ι : Type*} {n : ℕ}
variable (a : ι → C(Sphere n,X)) [T2Space (Space a)]
variable {K : Type*} [MetricSpace K] [CompactSpace K]

def chart (i : ι) : C(Cellular.ChartDisk n,Space a) :=
  ⟨openCell a i,(openCell_openEmbedding a i).continuous⟩

lemma exists_deformation_into_base (f : C(K,Space a))
    (hdim : dimH (Set.univ : Set K) < n) :
    ∃ (g : C(K,X)) (H : f.Homotopy ((⟨base a,continuous_base a⟩ : C(X,Space a)).comp g)),
      ∀ t x, f x ∈ Set.range (base a) → H (t,x) = f x := by
  classical
  let I := {i : ι | (Set.range f ∩ Set.range (openCell a i)).Nonempty}
  have hI : I.Finite := compact_finitely_many_openCells a (isCompact_range f.continuous)
  have hs : ∀ i, i ∉ hI.toFinset → ∀ x, f x ∉ Set.range (chart a i) := by
    intro i hi x hx
    apply hi
    rw [Set.Finite.mem_toFinset]
    exact ⟨f x,Set.mem_range_self x,hx⟩
  obtain ⟨g,H,hg,hstat⟩ := Cellular.exists_all_chart_avoidance (chart a)
    (fun i => openCell_openEmbedding a i) (fun i j hij => openCell_disjoint a i j hij)
    f hdim hI.toFinset hs
  have hgp (x : K) : g x ∈ punctured a := by
    rintro ⟨i,hi⟩
    exact hg i x hi.symm
  let gp : C(K,punctured a) := ⟨fun x => ⟨g x,hgp x⟩,g.continuous.subtype_mk hgp⟩
  let J := (radialHomotopy a).compContinuousMap gp
  have hJ0 : (puncturedInclusion a).comp gp = g := rfl
  let J' : g.Homotopy ((radialEnd a).comp gp) := hJ0 ▸ J
  refine ⟨(radialRetraction a).comp gp,H.trans J',?_⟩
  intro t x hx
  obtain ⟨y,hy⟩ := hx
  have hfixed (s : unitInterval) : H (s,x) = f x := by
    apply hstat s x
    intro i
    rintro ⟨d,hd⟩
    rw [← hy] at hd
    cases hd
  have hgx : g x = base a y := by simpa only [ContinuousMap.Homotopy.apply_one,← hy] using hfixed 1
  have hgp' : gp x = puncturedBase a y := Subtype.ext hgx
  have hjfixed (s : unitInterval) : J' (s,x) = f x := by
    change radialHomotopy a (s,gp x) = f x
    rw [hgp',radialHomotopy_base,hy]
  change (H.trans J') (t,x) = f x
  rw [ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact hfixed _
  · exact hjfixed _

end UniversalFInfinity.Attachment

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.GeneralPosition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal

open Set Metric Topology
open scoped NNReal ENNReal
namespace UniversalFInfinity.GeneralPosition

lemma lipschitz_insertNth {n : ℕ} (i : Fin (n+1)) (c : ℝ) :
    LipschitzWith 1 (Fin.insertNth (α := fun _ : Fin (n+1) => ℝ) i c : (Fin n → ℝ) → (Fin (n+1) → ℝ)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one,one_mul]
  rw [dist_pi_le_iff dist_nonneg]
  intro j
  refine Fin.succAboveCases i ?_ (fun k => ?_) j
  · simp only [Fin.insertNth_apply_same,dist_self,dist_nonneg]
  · simp only [Fin.insertNth_apply_succAbove]
    exact dist_le_pi_dist x y k

lemma sphere_subset_faces (n : ℕ) :
    Metric.sphere (0 : Fin (n+1) → ℝ) 1 ⊆
      ⋃ i : Fin (n+1), ⋃ c ∈ ({1,-1}:Set ℝ), Set.range (Fin.insertNth (α := fun _ : Fin (n+1) => ℝ) i c : (Fin n → ℝ) → _) := by
  intro x hx
  have hxnorm : ‖x‖ = 1 := by simpa only [Metric.mem_sphere,dist_zero_right] using hx
  have hi : ∃ i, 1 ≤ ‖x i‖ := by
    by_contra! hh
    have := (pi_norm_lt_iff (by norm_num : (0:ℝ)<1)).mpr hh
    linarith
  obtain ⟨i,hi⟩ := hi
  have heq : |x i| = 1 := le_antisymm ((norm_le_pi_norm x i).trans_eq hxnorm) hi
  have hc : x i ∈ ({1,-1}:Set ℝ) := by
    rcases abs_eq (by norm_num : (0:ℝ)≤1) |>.mp heq with h | h <;> simp [h]
  refine Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr ⟨x i,Set.mem_iUnion.mpr ⟨hc,?_⟩⟩⟩
  exact ⟨fun j => x (i.succAbove j),Fin.insertNth_self_removeNth _ _⟩

lemma dimH_cube_boundary_le (n : ℕ) :
    dimH (Metric.sphere (0 : Fin (n+1) → ℝ) 1) ≤ n := by
  apply (dimH_mono (sphere_subset_faces n)).trans
  rw [dimH_iUnion]
  apply iSup_le
  intro i
  rw [dimH_bUnion (Set.toFinite ({1,-1}:Set ℝ)).countable]
  apply iSup_le
  intro c
  apply iSup_le
  intro _
  exact (lipschitz_insertNth i c).dimH_range_le.trans_eq (Real.dimH_univ_pi_fin n)

lemma dimH_cube_boundary_subtype_le (n : ℕ) :
    dimH (Set.univ : Set (Metric.sphere (0 : Fin (n+1) → ℝ) 1)) ≤ n := by
  rw [← isometry_subtype_coe.dimH_image]
  simpa only [Subtype.range_coe_subtype,Set.image_univ,Set.ofPred_mem_eq] using dimH_cube_boundary_le n

end UniversalFInfinity.GeneralPosition

namespace UniversalFInfinity.Attachment

section
open Set Metric Topology
variable {X : Type*} [TopologicalSpace X] {ι : Type*} {n : ℕ}
variable (a : ι → C(Sphere n,X)) [T2Space (Space a)]

lemma dimH_disk_subtype_le (m : ℕ) : dimH (Set.univ : Set (Disk m)) ≤ m := by
  rw [← isometry_subtype_coe.dimH_image]
  have hm := dimH_mono (Set.subset_univ (closedBall (0 : Fin m → ℝ) 1))
  simpa only [Set.image_univ,Subtype.range_coe_subtype,Set.ofPred_mem_eq,Real.dimH_univ_pi_fin] using hm

end
open Set Metric Topology
variable {X : Type*} [TopologicalSpace X] [PathConnectedSpace X]
variable {ι : Type*} {n : ℕ} (a : ι → C(Sphere n,X)) [Nonempty (Sphere n)]
lemma pathConnectedSpace : PathConnectedSpace (Space a) := by
  let x₀ : X := Classical.choice inferInstance
  let s₀ : Sphere n := Classical.choice inferInstance
  have hj : ∀ z : Space a, Joined (base a x₀) z := by
    intro z
    cases z with
    | inl x => exact (PathConnectedSpace.joined x₀ x).map (continuous_base a)
    | inr p =>
      have h : Joined (boundary n s₀) (interior n p.2) := PathConnectedSpace.joined _ _
      have hh := h.map (cell a p.1).continuous
      rw [cell_interior,cell_boundary] at hh
      exact ((PathConnectedSpace.joined x₀ (a p.1 s₀)).map (continuous_base a)).trans hh
  exact ⟨⟨base a x₀⟩,fun x y => (hj x).symm.trans (hj y)⟩
end UniversalFInfinity.Attachment

open Set Metric Topology
namespace UniversalFInfinity.Cellular
universe u
variable {G : Type u} [Group G] {X : Type u} [TopologicalSpace X]
  [MulAction G X] [ContinuousConstSMul G X]
variable [CWComplex (univ : Set X)] {ι : ℕ → Type u}
variable (σ : ∀ n, (G × ι n) ≃ RelCWComplex.cell (univ : Set X) n)

def actionChart (n : ℕ) (i : G × ι n) : PartialEquiv (Fin n → ℝ) X :=
  (RelCWComplex.map n (σ n (1,i.2))).trans (Homeomorph.smul i.1).toEquiv.toPartialEquiv

lemma actionChart_image (n : ℕ) (i : G × ι n) (A : Set (Fin n → ℝ)) :
    actionChart σ n i '' A = (fun x : X => i.1 • x) '' (RelCWComplex.map n (σ n (1,i.2)) '' A) :=
  Set.image_comp (fun x : X => i.1 • x) (RelCWComplex.map n (σ n (1,i.2))) A

lemma actionChart_source (n : ℕ) (i : G × ι n) :
    (actionChart σ n i).source = ball 0 1 := by
  simp [actionChart,PartialEquiv.trans_source,RelCWComplex.source_eq]

lemma actionChart_continuousOn (n : ℕ) (i : G × ι n) :
    ContinuousOn (actionChart σ n i) (closedBall 0 1) :=
  (continuous_const_smul i.1).comp_continuousOn (RelCWComplex.continuousOn _ _)

lemma actionChart_continuousOn_symm (n : ℕ) (i : G × ι n) :
    ContinuousOn (actionChart σ n i).symm (actionChart σ n i).target := by
  change ContinuousOn (fun y => (RelCWComplex.map n (σ n (1,i.2))).symm (i.1⁻¹ • y))
    (univ ∩ (fun y : X => i.1⁻¹ • y) ⁻¹' (RelCWComplex.map n (σ n (1,i.2))).target)
  exact (RelCWComplex.continuousOn_symm _ _).comp (continuous_const_smul _).continuousOn
    (fun _ h => h.2)

variable
  (ho : ∀ n (g : G) (i : ι n),
    (fun x : X => g • x) '' RelCWComplex.openCell n (σ n (1,i)) = RelCWComplex.openCell n (σ n (g,i)))
  (hc : ∀ n (g : G) (i : ι n),
    (fun x : X => g • x) '' RelCWComplex.closedCell n (σ n (1,i)) = RelCWComplex.closedCell n (σ n (g,i)))

include ho in
lemma actionChart_open (n : ℕ) (i : G × ι n) :
    actionChart σ n i '' ball 0 1 = RelCWComplex.openCell n (σ n i) := by
  rw [actionChart_image]
  exact ho n i.1 i.2

include hc in
lemma actionChart_closed (n : ℕ) (i : G × ι n) :
    actionChart σ n i '' closedBall 0 1 = RelCWComplex.closedCell n (σ n i) := by
  rw [actionChart_image]
  exact hc n i.1 i.2

omit [ContinuousConstSMul G X] in
include hc in
lemma closedCell_smul (n : ℕ) (g h : G) (i : ι n) :
    (fun x : X => g • x) '' RelCWComplex.closedCell n (σ n (h,i)) =
      RelCWComplex.closedCell n (σ n (g*h,i)) := by
  rw [←hc n h i,←Set.image_comp]
  simpa only [Function.comp_def,mul_smul] using hc n (g*h) i

variable [T2Space X]

@[instance_reducible]
def actionCW : CWComplex (univ : Set X) where
  cell n := G × ι n
  map := actionChart σ
  source_eq := actionChart_source σ
  continuousOn := actionChart_continuousOn σ
  continuousOn_symm := actionChart_continuousOn_symm σ
  pairwiseDisjoint' := by
    intro p _ q _ hpq
    change Disjoint (actionChart σ p.1 p.2 '' ball 0 1) (actionChart σ q.1 q.2 '' ball 0 1)
    rw [actionChart_open σ ho,actionChart_open σ ho]
    apply CWComplex.disjoint_openCell_of_ne
    intro he
    apply hpq
    cases p with | mk n i =>
      cases q with | mk m j =>
        have hnm : n = m := congrArg Sigma.fst he
        subst m
        have hij : σ n i = σ n j := (Sigma.mk.inj he).2 |> eq_of_heq
        exact congrArg (Sigma.mk n) ((σ n).injective hij)
  mapsTo' := by
    classical
    intro n i
    obtain ⟨I,hI⟩ := CWComplex.cellFrontier_subset_finite_closedCell n (σ n (1,i.2))
    let f (m : ℕ) (j : RelCWComplex.cell (univ : Set X) m) : G × ι m :=
      (i.1 * ((σ m).symm j).1,((σ m).symm j).2)
    refine ⟨fun m => (I m).image (f m),?_⟩
    intro x hx
    have h := hI (show RelCWComplex.map n (σ n (1,i.2)) x ∈ RelCWComplex.cellFrontier n (σ n (1,i.2)) from ⟨x,hx,rfl⟩)
    simp only [Set.mem_iUnion] at h
    obtain ⟨m,hm,j,hj,hxj⟩ := h
    refine Set.mem_iUnion.mpr ⟨m,Set.mem_iUnion.mpr ⟨hm,Set.mem_iUnion.mpr
      ⟨f m j,Set.mem_iUnion.mpr ⟨Finset.mem_image.mpr ⟨j,hj,rfl⟩,?_⟩⟩⟩⟩
    rw [actionChart_closed σ hc]
    change i.1 • RelCWComplex.map n (σ n (1,i.2)) x ∈ RelCWComplex.closedCell m
      (σ m (i.1 * ((σ m).symm j).1,((σ m).symm j).2))
    rw [←closedCell_smul σ hc]
    refine ⟨_,?_,rfl⟩
    simpa only [Prod.eta,Equiv.apply_symm_apply] using hxj
  closed' := by
    intro A hA hclosed
    apply (CWComplex.closed (univ : Set X) A hA).mpr
    intro n j
    obtain ⟨i,rfl⟩ := (σ n).surjective j
    simpa only [actionChart_closed σ hc] using hclosed n i
  union' := by
    simp only [actionChart_closed σ hc]
    have he (n : ℕ) : (⋃ j : G × ι n, RelCWComplex.closedCell n (σ n j)) =
        ⋃ j : RelCWComplex.cell (univ : Set X) n, RelCWComplex.closedCell n j := by
      ext x
      simp only [mem_iUnion]
      constructor
      · rintro ⟨j,hj⟩; exact ⟨σ n j,hj⟩
      · rintro ⟨j,hj⟩; exact ⟨(σ n).symm j,by simpa only [Equiv.apply_symm_apply] using hj⟩
    simp_rw [he]
    exact CWComplex.union

end UniversalFInfinity.Cellular

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.CellularApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal
open Set Metric Topology
open scoped NNReal ENNReal
open Set Metric Topology

namespace UniversalFInfinity.Cellular

section
open Set Metric Topology
universe u
variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable {C : Set X} [CWComplex C]

def skeletonBoundary (n : ℕ) (i : RelCWComplex.cell C n) :
    C(Attachment.Sphere n,Skeleton C n) :=
  ⟨fun x => ⟨characteristic n i (boundary n x),sphere_mem_skeleton n i x⟩,
    ((characteristic n i).continuous.comp (continuous_boundary n)).subtype_mk _⟩

def skeletonBase (n : ℕ) : C(Skeleton C n,Skeleton C (n+1)) :=
  ⟨fun x => ⟨x.1,skeleton_mono (Nat.le_succ n) x.2⟩,continuous_subtype_val.subtype_mk _⟩

def skeletonCell (n : ℕ) (i : RelCWComplex.cell C n) :
    C(Attachment.Disk n,Skeleton C (n+1)) :=
  ⟨fun x => ⟨characteristic n i x,characteristic_mem_skeleton (Nat.lt_succ_self n) i x⟩,
    (characteristic n i).continuous.subtype_mk _⟩

def skeletonAssembly (n : ℕ) : C(Attachment.Space (skeletonBoundary (C := C) n),Skeleton C (n+1)) :=
  Attachment.lift _ (skeletonBase n) (skeletonCell n) (fun _ _ => rfl)

lemma skeletonAssembly_base (n : ℕ) (x : Skeleton C n) :
    skeletonAssembly n (Attachment.base _ x) = skeletonBase n x :=
  Attachment.lift_base _ _ _ _ x

lemma skeletonAssembly_cell (n : ℕ) (i : RelCWComplex.cell C n) (x : Disk n) :
    skeletonAssembly n (Attachment.cell _ i x) = skeletonCell n i x :=
  Attachment.lift_cell _ _ _ _ i x

lemma skeletonAssembly_interior (n : ℕ) (i : RelCWComplex.cell C n) (x : Attachment.OpenDisk n) :
    skeletonAssembly n (Sum.inr ⟨i,x⟩) = skeletonCell n i (Attachment.interior n x) := by
  rw [← Attachment.cell_interior (skeletonBoundary n) i x,skeletonAssembly_cell]

lemma skeletonAssembly_injective (n : ℕ) : Function.Injective (skeletonAssembly (C := C) n) := by
  intro a b hab
  rcases a with a|⟨i,a⟩ <;> rcases b with b|⟨j,b⟩
  · change skeletonAssembly n (Attachment.base _ a) = skeletonAssembly n (Attachment.base _ b) at hab
    rw [skeletonAssembly_base,skeletonAssembly_base] at hab
    exact congrArg Sum.inl (Subtype.ext (congrArg (fun z : Skeleton C (n+1) => z.1) hab))
  · have hh := congrArg Subtype.val hab
    rw [← show Attachment.base (skeletonBoundary n) a = Sum.inl a from rfl,
      skeletonAssembly_base,skeletonAssembly_interior] at hh
    have hm : a.1 ∈ CWComplex.openCell n j := ⟨b.1,b.2,hh.symm⟩
    exact False.elim (openCell_not_skeleton n j hm a.2)
  · have hh := congrArg Subtype.val hab
    rw [skeletonAssembly_interior,
      ← show Attachment.base (skeletonBoundary n) b = Sum.inl b from rfl,
      skeletonAssembly_base] at hh
    have hm : b.1 ∈ CWComplex.openCell n i := ⟨a.1,a.2,hh⟩
    exact False.elim (openCell_not_skeleton n i hm b.2)
  · have hh := congrArg Subtype.val hab
    rw [skeletonAssembly_interior,skeletonAssembly_interior] at hh
    have hij : i = j := by
      by_contra hne
      have hd := CWComplex.disjoint_openCell_of_ne (C := C) (i := i) (j := j)
        (fun h => hne (sigma_mk_injective h))
      exact Set.disjoint_left.mp hd ⟨a.1,a.2,rfl⟩ ⟨b.1,b.2,hh.symm⟩
    subst j
    have he : a = b := Subtype.ext ((RelCWComplex.map n i).injOn
      (by simpa only [RelCWComplex.source_eq] using a.2)
      (by simpa only [RelCWComplex.source_eq] using b.2) hh)
    subst b; rfl

lemma skeletonAssembly_surjective (n : ℕ) : Function.Surjective (skeletonAssembly (C := C) n) := by
  intro x
  have hx := x.2
  have heq : Skeleton C (n+1) = Skeleton C n ∪
      ⋃ i : RelCWComplex.cell C n,CWComplex.closedCell n i := by
    simpa only [Skeleton,Nat.cast_add,Nat.cast_one] using
      (CWComplex.skeletonLT_union_iUnion_closedCell_eq_skeletonLT_succ (C := C) n).symm
  have hx' := (congrArg (fun S : Set X => x.1 ∈ S) heq).mp hx
  rcases hx' with hx|hx
  · exact ⟨Attachment.base _ ⟨x.1,hx⟩,skeletonAssembly_base n _⟩
  · obtain ⟨i,y,hy,he⟩ := Set.mem_iUnion.mp hx
    refine ⟨Attachment.cell _ i ⟨y,hy⟩,?_⟩
    rw [skeletonAssembly_cell]
    exact Subtype.ext he

lemma skeletonAssembly_closed (n : ℕ) : IsClosedMap (skeletonAssembly (C := C) n) := by
  intro S hS
  let e : Attachment.Space (skeletonBoundary (C := C) n) → X :=
    fun x => (skeletonAssembly n x).1
  have hei : Function.Injective e := Subtype.val_injective.comp (skeletonAssembly_injective n)
  have hclosed : IsClosed (e '' S) := by
    apply (CWComplex.closed (Skeleton C (n+1)) _ ?_).mpr
    · intro m j
      have hm : m < n+1 := by
        have hh : (m : ℕ∞) < ((n+1 : ℕ) : ℕ∞) := by
          simpa only [RelCWComplex.skeletonLT_I,Set.mem_ofPred_eq] using j.2
        exact_mod_cast hh
      have hu : ∃ u : C(Disk m,Attachment.Space (skeletonBoundary (C := C) n)),
          ∀ x, e (u x) = characteristic m j.1 x := by
        rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hm|hm
        · refine ⟨⟨fun x => Attachment.base _
            ⟨characteristic m j.1 x,characteristic_mem_skeleton hm j.1 x⟩,
            (Attachment.continuous_base _).comp ((characteristic m j.1).continuous.subtype_mk _)⟩,?_⟩
          intro x; exact congrArg Subtype.val (skeletonAssembly_base n _)
        · subst m
          exact ⟨Attachment.cell _ j.1,fun x => congrArg Subtype.val (skeletonAssembly_cell n j.1 x)⟩
      obtain ⟨u,hu⟩ := hu
      have heq : (e '' S) ∩ CWComplex.closedCell m j =
          characteristic m j.1 '' (u ⁻¹' S) := by
        ext x
        constructor
        · rintro ⟨⟨y,hy,rfl⟩,z,hz,he⟩
          refine ⟨⟨z,hz⟩,?_,he⟩
          change u ⟨z,hz⟩ ∈ S
          have hh : u ⟨z,hz⟩ = y := hei ((hu _).trans he)
          rwa [hh]
        · rintro ⟨z,hz,rfl⟩
          exact ⟨⟨u z,hz,hu z⟩,z.1,z.2,rfl⟩
      rw [heq]
      exact ((hS.preimage u.continuous).isCompact.image (characteristic m j.1).continuous).isClosed
    · rintro x ⟨y,hy,rfl⟩
      exact (skeletonAssembly n y).2
  have h : IsClosed ((Subtype.val : Skeleton C (n+1) → X) ⁻¹' (e '' S)) :=
    hclosed.preimage continuous_subtype_val
  convert h using 1
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩; exact ⟨y,hy,rfl⟩
  · rintro ⟨y,hy,he⟩; exact ⟨y,hy,Subtype.ext he⟩

def skeletonHomeomorph (n : ℕ) :
    Attachment.Space (skeletonBoundary (C := C) n) ≃ₜ Skeleton C (n+1) :=
  (isHomeomorph_iff_continuous_isClosedMap_bijective.mpr
    ⟨(skeletonAssembly n).continuous,skeletonAssembly_closed n,
      skeletonAssembly_injective n,skeletonAssembly_surjective n⟩).homeomorph _
end

section
open Set Metric Topology
universe u
variable {G : Type u} [Group G] {X : Type u} [TopologicalSpace X] [T2Space X]
  [MulAction G X] [ContinuousConstSMul G X] [CWComplex (univ : Set X)]
variable {ι : ℕ → Type u}
variable (σ : ∀ n, (G × ι n) ≃ RelCWComplex.cell (univ : Set X) n)
variable (hσ : ∀ n (g h : G) (i : ι n) (x : Fin n → ℝ),
  RelCWComplex.map n (σ n (g*h,i)) x = g • RelCWComplex.map n (σ n (h,i)) x)

omit [ContinuousConstSMul G X] in
include hσ in
lemma skeleton_smul_mem (n : ℕ) (g : G) {x : X} (hx : x ∈ Skeleton (univ : Set X) n) :
    g • x ∈ Skeleton (univ : Set X) n := by
  obtain ⟨m,hm,j,y,hy,rfl⟩ := (CWComplex.mem_skeletonLT_iff (C := (univ : Set X))).mp hx
  let i := (σ m).symm j
  have hj : σ m i = j := (σ m).apply_symm_apply j
  apply (CWComplex.mem_skeletonLT_iff (C := (univ : Set X))).mpr
  refine ⟨m,hm,σ m (g*i.1,i.2),y,hy,?_⟩
  rw [hσ]
  exact congrArg (fun j => g • RelCWComplex.map m j y) hj

def skeletonTranslate (n : ℕ) (g : G) : C(Skeleton (univ : Set X) n,Skeleton (univ : Set X) n) :=
  ⟨fun x => ⟨g • x.1,skeleton_smul_mem σ hσ n g x.2⟩,
    ((continuous_const_smul g).comp continuous_subtype_val).subtype_mk _⟩

lemma skeletonTranslate_base (n : ℕ) (g : G) (x : Skeleton (univ : Set X) n) :
    skeletonTranslate σ hσ (n+1) g (skeletonBase n x) =
      skeletonBase n (skeletonTranslate σ hσ n g x) := rfl

lemma skeletonTranslate_cell (n : ℕ) (g h : G) (i : ι n) (x : Disk n) :
    skeletonTranslate σ hσ (n+1) g (skeletonCell n (σ n (h,i)) x) =
      skeletonCell n (σ n (g*h,i)) x := by
  apply Subtype.ext
  exact (hσ n g h i x.1).symm

end

section
open Set Metric Topology
universe u
variable {G : Type u} [Group G] {X : Type u} [TopologicalSpace X] [T2Space X]
  [MulAction G X] [ContinuousConstSMul G X] [CWComplex (univ : Set X)]
variable {ι : ℕ → Type u}
variable (σ : ∀ n, (G × ι n) ≃ RelCWComplex.cell (univ : Set X) n)
variable (hσ : ∀ n (g h : G) (i : ι n) (x : Fin n → ℝ),
  RelCWComplex.map n (σ n (g*h,i)) x = g • RelCWComplex.map n (σ n (h,i)) x)

variable {E B : Type u} [TopologicalSpace E] [TopologicalSpace B]
  [MulAction G E] [ContinuousConstSMul G E] [MulAction G B]

variable {Y : Type u} [TopologicalSpace Y] [MulAction G Y] [ContinuousConstSMul G Y]

omit [MulAction G X] [ContinuousConstSMul G X] in
def skeletonChart (n m : ℕ) (hm : m < n) (i : RelCWComplex.cell (univ : Set X) m) :
    C(Disk m,Skeleton (univ : Set X) n) :=
  ⟨fun z => ⟨characteristic m i z,characteristic_mem_skeleton hm i z⟩,
    (characteristic m i).continuous.subtype_mk _⟩

lemma skeleton_compact_representatives (n : ℕ) [∀ m,Finite (ι m)] :
    ∃ K : Set (Skeleton (univ : Set X) n), IsCompact K ∧
      ∀ x, ∃ g : G, ∃ y ∈ K, x = skeletonTranslate σ hσ n g y := by
  let K := ⋃ m : Fin n, ⋃ i : ι m, Set.range (skeletonChart n m m.2 (σ m (1,i)))
  have hK : IsCompact K := isCompact_iUnion fun m => isCompact_iUnion fun i =>
    isCompact_range (skeletonChart n m m.2 (σ m (1,i))).continuous
  refine ⟨K,hK,?_⟩
  intro x
  obtain ⟨m,hm,j,z,hz,hj⟩ := (CWComplex.mem_skeletonLT_iff (C := (univ : Set X))).mp x.2
  obtain ⟨⟨g,i⟩,rfl⟩ := (σ m).surjective j
  have hmn : m < n := by exact_mod_cast hm
  let y := skeletonChart n m hmn (σ m (1,i)) ⟨z,ball_subset_closedBall hz⟩
  refine ⟨g,y,Set.mem_iUnion.mpr ⟨⟨m,hmn⟩,Set.mem_iUnion.mpr ⟨i,Set.mem_range_self _⟩⟩,?_⟩
  apply Subtype.ext
  change x.1 = g • RelCWComplex.map m (σ m (1,i)) z
  rw [←hσ,mul_one]
  exact hj.symm
end

open Set Metric Topology
universe u v
variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable {C : Set X} [CWComplex C]
variable {K : Type v} [MetricSpace K] [CompactSpace K]

lemma deform_skeleton_succ (n : ℕ) (f : C(K,Skeleton C (n+1)))
    (hdim : dimH (Set.univ : Set K) < n) :
    ∃ (g : C(K,Skeleton C n))
      (H : f.Homotopy ((skeletonBase n).comp g)),
      ∀ t x, (f x).1 ∈ Skeleton C n → H (t,x) = f x := by
  let e := skeletonHomeomorph (C := C) n
  let : T2Space (Attachment.Space (skeletonBoundary (C := C) n)) := e.symm.t2Space
  let f' : C(K,Attachment.Space (skeletonBoundary (C := C) n)) := (⟨e.symm,e.symm.continuous⟩ : C(_, _)).comp f
  obtain ⟨g,H,hH⟩ := Attachment.exists_deformation_into_base (skeletonBoundary (C := C) n) f' hdim
  have h0 : (⟨e,e.continuous⟩ : C(_, _)).comp f' = f := by apply ContinuousMap.ext; intro x; exact e.apply_symm_apply (f x)
  have h1 : (⟨e,e.continuous⟩ : C(_, _)).comp
      ((⟨Attachment.base _,Attachment.continuous_base _⟩ : C(_, _)).comp g) =
      (skeletonBase n).comp g := by apply ContinuousMap.ext; intro x; exact skeletonAssembly_base n (g x)
  let J := (ContinuousMap.Homotopy.refl (⟨e,e.continuous⟩ : C(_, _))).comp H
  refine ⟨g,J.cast h0 h1,?_⟩
  intro t x hx
  change e (H (t,x)) = f x
  have hr : f' x ∈ Set.range (Attachment.base (skeletonBoundary (C := C) n)) := by
    refine ⟨⟨(f x).1,hx⟩,?_⟩
    apply e.injective
    change skeletonAssembly n (Attachment.base _ _) = e (e.symm (f x))
    rw [skeletonAssembly_base,e.apply_symm_apply]
    rfl
  rw [hH t x hr]
  exact e.apply_symm_apply (f x)

lemma deform_bounded_skeleton (d m : ℕ) (f : C(K,Skeleton C m))
    (hdim : dimH (Set.univ : Set K) < d) :
    ∃ (g : C(K,Skeleton C d))
      (H : ((skeletonInclusion m).comp f).Homotopy ((skeletonInclusion d).comp g)),
      ∀ t x, (f x).1 ∈ Skeleton C d → H (t,x) = (f x).1 := by
  induction m with
  | zero =>
    let g : C(K,Skeleton C d) := ⟨fun x => ⟨(f x).1,skeleton_mono (Nat.zero_le d) (f x).2⟩,
      f.continuous.subtype_val.subtype_mk _⟩
    exact ⟨g,.refl _,fun _ _ _ => rfl⟩
  | succ m ih =>
    by_cases hmd : m+1 ≤ d
    · let g : C(K,Skeleton C d) := ⟨fun x => ⟨(f x).1,skeleton_mono hmd (f x).2⟩,
        f.continuous.subtype_val.subtype_mk _⟩
      exact ⟨g,.refl _,fun _ _ _ => rfl⟩
    · have hdm : d ≤ m := by omega
      obtain ⟨g,H,hH⟩ := deform_skeleton_succ m f (hdim.trans_le (by exact_mod_cast hdm))
      obtain ⟨g',J,hJ⟩ := ih g
      let H' : ((skeletonInclusion (C := C) (m+1)).comp f).Homotopy
          ((skeletonInclusion m).comp g) :=
        (ContinuousMap.Homotopy.refl (skeletonInclusion (C := C) (m+1))).comp H
      refine ⟨g',H'.trans J,?_⟩
      intro t x hx
      have hh (s : unitInterval) : H' (s,x) = (f x).1 := by
        exact congrArg Subtype.val (hH s x (skeleton_mono hdm hx))
      have hg : (g x).1 = (f x).1 := by
        have he := hh 1
        rw [ContinuousMap.Homotopy.apply_one] at he
        exact he
      have hj (s : unitInterval) : J (s,x) = (f x).1 := by
        rw [hJ s x (hg.symm ▸ hx),hg]
      rw [ContinuousMap.Homotopy.trans_apply]
      split_ifs
      · exact hh _
      · exact hj _

theorem exists_cellular_approximation_bundle (d : ℕ) (f : C(K,X)) (hf : ∀ x,f x ∈ C)
    (hdim : dimH (Set.univ : Set K) < d) :
    ∃ (g : C(K,Skeleton C d)) (H : f.Homotopy ((skeletonInclusion d).comp g)),
      ∀ t x, f x ∈ Skeleton C d → H (t,x) = f x := by
  obtain ⟨m,hm⟩ := compactMap_bounded_skeleton f hf
  let f' : C(K,Skeleton C m) := ⟨fun x => ⟨f x,hm x⟩,f.continuous.subtype_mk _⟩
  exact deform_bounded_skeleton d m f' hdim
end UniversalFInfinity.Cellular
namespace UniversalFInfinity.SphereTopology
open Set Metric Topology
universe u
variable {Y : Type u} [TopologicalSpace Y]
lemma fill_zero [Nonempty Y] (a : C(Cellular.Sphere 0,Y)) :
    ∃ e : C(Cellular.Disk 0,Y), ∀ x, e (Cellular.boundary 0 x) = a x := by
  refine ⟨.const _ (Classical.choice ‹Nonempty Y›),?_⟩
  intro x
  have hx := x.2
  have hz : x.1 = 0 := Subsingleton.elim _ _
  simp only [hz,mem_sphere,dist_self] at hx
  exact False.elim (zero_ne_one hx)
end UniversalFInfinity.SphereTopology

open scoped TensorProduct

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.ControlledHomotopies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal
open Set Metric Topology
open scoped NNReal ENNReal
open Set Metric Topology
open scoped TensorProduct

namespace UniversalFInfinity.Cellular
open Set Metric Topology
universe u v w
variable {Y : Type v} {Z : Type w} [TopologicalSpace Y] [TopologicalSpace Z]

variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable {C : Set X} [CWComplex C]

structure PartialHomotopy (f g : C(X,Y)) (n : ℕ) where
  val : X → C(unitInterval,Y)
  continuousOn : ContinuousOn val (Skeleton C n)
  zero : ∀ x ∈ Skeleton C n, val x 0 = f x
  one : ∀ x ∈ Skeleton C n, val x 1 = g x

end UniversalFInfinity.Cellular

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.GraphBundles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal
open Set Metric Topology
open scoped NNReal ENNReal
open Set Metric Topology
open scoped TensorProduct

namespace UniversalFInfinity.GraphBundle

section
open Set Topology
open scoped unitInterval
universe u v w z
variable {C : Type u}
variable {A : Type v} [TopologicalSpace A] {B : Type w} [TopologicalSpace B]
variable (τ : C → C) (L R : C → C(B,A))

abbrev Inner := Set.Ioo (0:ℝ) 1
abbrev Core := (C × A) ⊕ (C × (Inner × B))
def Space (_ : C → C) (_ _ : C → C(B,A)) := Core (C := C) (A := A) (B := B)
def vertex (c : C) (x : A) : Space τ L R := Sum.inl (c,x)
def interior (c : C) (s : Inner) (x : B) : Space τ L R := Sum.inr (c,(s,x))

def edge (c : C) (t : I) (x : B) : Space τ L R := by
  classical
  exact if h0 : t = 0 then vertex τ L R c (L c x) else
    if h1 : t = 1 then vertex τ L R (τ c) (R c x) else
      interior τ L R c ⟨t.1,lt_of_le_of_ne t.2.1 (fun h => h0 (Subtype.ext h.symm)),
        lt_of_le_of_ne t.2.2 (fun h => h1 (Subtype.ext h))⟩ x

lemma edge_inner (c : C) (s : Inner) (x : B) :
    edge τ L R c ⟨s.1,s.2.1.le,s.2.2.le⟩ x = interior τ L R c s x := by
  unfold edge
  split_ifs with h0 h1
  · exact False.elim (s.2.1.ne' (congrArg Subtype.val h0))
  · exact False.elim (s.2.2.ne (congrArg Subtype.val h1))
  · rfl

variable [TopologicalSpace C] [DiscreteTopology C]

abbrev Raw := (C × A) ⊕ (C × (I × B))
def quotient : Raw (C := C) (A := A) (B := B) → Space τ L R :=
  Sum.elim (fun z => vertex τ L R z.1 z.2) (fun z => edge τ L R z.1 z.2.1 z.2.2)
instance instTopologicalSpaceSpace : TopologicalSpace (Space τ L R) :=
  TopologicalSpace.coinduced (quotient τ L R) inferInstance

end

open Set Topology
open scoped unitInterval
universe u v w
variable {C : Type u} {A : Type v} [TopologicalSpace A] {B : Type w} [TopologicalSpace B]
variable (τ : C → C) (L R : C → C(B,A))

@[simp] lemma vertex_eq_vertex (c d : C) (x y : A) :
    vertex τ L R c x = vertex τ L R d y ↔ c = d ∧ x = y := by
  change (Sum.inl (c,x) : Core (C := C) (A := A) (B := B)) = Sum.inl (d,y) ↔ _
  simp only [Sum.inl.injEq,Prod.mk.injEq]
@[simp] lemma vertex_ne_interior (c d : C) (x : A) (s : Inner) (y : B) :
    vertex τ L R c x ≠ interior τ L R d s y := by
  intro h
  change (Sum.inl (c,x) : Core (C := C) (A := A) (B := B)) = Sum.inr (d,(s,y)) at h
  cases h
@[simp] lemma interior_ne_vertex (c d : C) (s : Inner) (x : B) (y : A) :
    interior τ L R c s x ≠ vertex τ L R d y :=
  (vertex_ne_interior τ L R d c y s x).symm
@[simp] lemma interior_eq_interior (c d : C) (s t : Inner) (x y : B) :
    interior τ L R c s x = interior τ L R d t y ↔ c = d ∧ s = t ∧ x = y := by
  change (Sum.inr (c,(s,x)) : Core (C := C) (A := A) (B := B)) = Sum.inr (d,(t,y)) ↔ _
  simp only [Sum.inr.injEq,Prod.mk.injEq]

end UniversalFInfinity.GraphBundle

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.GraphActions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal
open Set Metric Topology
open scoped NNReal ENNReal
open Set Metric Topology
open scoped TensorProduct

namespace UniversalFInfinity.GraphBundle

open Set Topology
open scoped unitInterval
universe u v w z
variable {C : Type u} [TopologicalSpace C] [DiscreteTopology C]
variable {A : Type v} [TopologicalSpace A] {B : Type w} [TopologicalSpace B]
variable (τ : C → C) (L R : C → C(B,A))
variable {Y : Type z} [TopologicalSpace Y]

omit [DiscreteTopology C] in
lemma hom_ext {f g : C(Space τ L R,Y)}
    (hv : ∀ c x,f (vertex τ L R c x) = g (vertex τ L R c x))
    (he : ∀ c (z : I × B),f (edge τ L R c z.1 z.2) = g (edge τ L R c z.1 z.2)) : f = g := by
  apply ContinuousMap.ext
  intro z
  change Core (C := C) (A := A) (B := B) at z
  cases z with
  | inl z => exact hv z.1 z.2
  | inr z =>
    have hh := he z.1 (⟨z.2.1.1,z.2.1.2.1.le,z.2.1.2.2.le⟩,z.2.2)
    rw [edge_inner] at hh
    exact hh

end UniversalFInfinity.GraphBundle

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.AscendingTorus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal
open Set Metric Topology
open scoped NNReal ENNReal
open Set Metric Topology
open scoped TensorProduct

namespace UniversalFInfinity.AscendingTorus

section

open Monoid Coprod Multiplicative
universe u v w
variable {U : Type u} [Group U]

abbrev Free (U : Type u) [Group U] := U ∗ Multiplicative ℤ

def letter : Free U := inr (ofAdd 1)

def relation (f : Monoid.End U) (x : U) : Free U :=
  (inl x * letter) * (letter * inl (f x))⁻¹

def relations (f : Monoid.End U) : Subgroup (Free U) :=
  Subgroup.normalClosure (Set.range (relation f))

instance instNormalFreeRelations (f : Monoid.End U) : (relations f).Normal := inferInstanceAs
  (Subgroup.normalClosure (Set.range (relation f))).Normal

def Torus (f : Monoid.End U) := Free U ⧸ relations f

instance instGroupTorus (f : Monoid.End U) : Group (Torus f) := by
  delta Torus
  infer_instance

instance groupOfHom (f : U →* U) : Group (Torus f) := instGroupTorus f

def of (f : Monoid.End U) : U →* Torus f :=
  (QuotientGroup.mk' (relations f)).comp inl

def stable (f : Monoid.End U) : Torus f :=
  QuotientGroup.mk' (relations f) letter

lemma of_mul_stable (f : Monoid.End U) (x : U) :
    of f x * stable f = stable f * of f (f x) := by
  apply mul_inv_eq_one.mp
  change QuotientGroup.mk' (relations f) (relation f x) = 1
  exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure ⟨x,rfl⟩)

lemma inverse_conjugate (f : Monoid.End U) (x : U) :
    (stable f)⁻¹ * of f x * stable f = of f (f x) := by
  rw [mul_assoc, of_mul_stable, inv_mul_cancel_left]

variable {V : Type v} [Group V]

def lift (f : Monoid.End U) (φ : U →* V) (t : V)
    (h : ∀ x, φ x * t = t * φ (f x)) : Torus f →* V :=
  QuotientGroup.lift (relations f) (Coprod.lift φ (zpowersHom V t)) (by
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨x,rfl⟩
    change Coprod.lift φ (zpowersHom V t) (relation f x) = 1
    simp only [relation, letter, map_mul, map_inv, Coprod.lift_apply_inl, Coprod.lift_apply_inr,
      zpowersHom_apply, toAdd_ofAdd, zpow_one]
    rw [h x, mul_inv_cancel])

@[simp] lemma lift_of (f : Monoid.End U) (φ : U →* V) (t : V)
    (h : ∀ x, φ x * t = t * φ (f x)) (x : U) :
    lift f φ t h (of f x) = φ x := by
  change Coprod.lift φ (zpowersHom V t) (inl x) = _
  simp

@[simp] lemma lift_stable (f : Monoid.End U) (φ : U →* V) (t : V)
    (h : ∀ x, φ x * t = t * φ (f x)) :
    lift f φ t h (stable f) = t := by
  change Coprod.lift φ (zpowersHom V t) (inr (ofAdd 1)) = _
  simp

@[ext] lemma hom_ext {f : Monoid.End U} {φ ψ : Torus f →* V}
    (ho : φ.comp (of f) = ψ.comp (of f)) (ht : φ (stable f) = ψ (stable f)) :
    φ = ψ := by
  apply (MonoidHom.cancel_right (QuotientGroup.mk'_surjective (relations f))).mp
  apply Coprod.hom_ext ho
  exact MonoidHom.ext_mint ht

theorem of_injective (f : Monoid.End U) (hf : Function.Injective f) :
    Function.Injective (of f) := by
  let e : (⊤ : Subgroup U) ≃* f.range :=
    (Subgroup.topEquiv).trans (MonoidHom.ofInjective hf)
  let H := HNNExtension U ⊤ f.range e
  let j : U →* H := HNNExtension.of
  let s : H := HNNExtension.t
  have hs (x : U) : j x * s⁻¹ = s⁻¹ * j (f x) := by
    exact HNNExtension.of_mul_inv_t (⟨x,Subgroup.mem_top x⟩ : (⊤ : Subgroup U))
  let Φ : Torus f →* H := lift f j s⁻¹ hs
  intro x y hxy
  apply HNNExtension.of_injective (A := ⊤) (B := f.range) (φ := e)
  exact (lift_of f j s⁻¹ hs x).symm.trans
    ((congrArg Φ hxy).trans (lift_of f j s⁻¹ hs y))

end

section
open Monoid Coprod Multiplicative
universe u
variable {U : Type u} [Group U]

lemma of_mul_stable_pow (f : Monoid.End U) (u : U) (n : ℕ) :
    of f u * stable f ^ n = stable f ^ n * of f ((f ^ n) u) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ← mul_assoc, ih, mul_assoc, of_mul_stable, ← mul_assoc, ← pow_succ]
    rw [pow_succ' f n]
    rfl

lemma inv_stable_pow_mul_of (f : Monoid.End U) (u : U) (n : ℕ) :
    (stable f ^ n)⁻¹ * of f u = of f ((f ^ n) u) * (stable f ^ n)⁻¹ := by
  apply mul_right_cancel (b := stable f ^ n)
  simp only [mul_assoc, inv_mul_cancel, mul_one]
  rw [of_mul_stable_pow, inv_mul_cancel_left]

def normalForms (f : Monoid.End U) : Subgroup (Torus f) where
  carrier := {x | ∃ (p q : ℕ) (u : U), x = stable f ^ p * of f u * (stable f ^ q)⁻¹}
  one_mem' := ⟨0,0,1,by simp⟩
  inv_mem' := by
    rintro x ⟨p,q,u,rfl⟩
    exact ⟨q,p,u⁻¹,by simp only [mul_inv_rev, inv_inv, map_inv, mul_assoc]⟩
  mul_mem' := by
    rintro x y ⟨p,q,u,rfl⟩ ⟨r,s,v,rfl⟩
    refine ⟨p+r,q+s,(f^r) u * (f^q) v,?_⟩
    have ht : (stable f ^ q)⁻¹ * stable f ^ r =
        stable f ^ r * (stable f ^ q)⁻¹ := (Commute.pow_pow (Commute.refl (stable f)) q r).inv_left.eq
    calc
      _ = stable f ^ p * (of f u * stable f ^ r) *
          ((stable f ^ q)⁻¹ * of f v) * (stable f ^ s)⁻¹ := by
            simp only [mul_assoc]
            rw [← mul_assoc ((stable f ^ q)⁻¹),ht]
            simp only [mul_assoc]
      _ = _ := by
        rw [of_mul_stable_pow,inv_stable_pow_mul_of,map_mul,pow_add,pow_add,mul_inv_rev]
        have ht' : (stable f ^ s)⁻¹ * (stable f ^ q)⁻¹ =
            (stable f ^ q)⁻¹ * (stable f ^ s)⁻¹ :=
          (Commute.pow_pow (Commute.refl (stable f)) s q).inv_left.inv_right.eq
        rw [ht']
        simp only [mul_assoc]

def height (f : Monoid.End U) : Torus f →* Multiplicative ℤ :=
  lift f 1 (ofAdd 1) (by intro u; simp)

@[simp] lemma height_of (f : Monoid.End U) (u : U) : height f (of f u) = 1 :=
  lift_of f 1 (ofAdd 1) _ u

@[simp] lemma height_stable (f : Monoid.End U) : height f (stable f) = ofAdd 1 :=
  lift_stable f 1 (ofAdd 1) _

end

section
open Monoid Multiplicative
universe u
variable {U : Type u} [Group U]

abbrev Coset (f : Monoid.End U) := Torus f ⧸ (of f).range

def coset (f : Monoid.End U) (x : Torus f) : Coset f := QuotientGroup.mk x

def next (f : Monoid.End U) : Coset f → Coset f :=
  Quotient.map' (fun x => x * stable f) (by
    intro x y h
    rw [QuotientGroup.leftRel_apply] at h ⊢
    obtain ⟨u,hu⟩ := h
    refine ⟨f u,?_⟩
    rw [mul_inv_rev,mul_assoc,← mul_assoc x⁻¹,← hu]
    exact (inverse_conjugate f u).symm)

@[simp] lemma next_coset (f : Monoid.End U) (x : Torus f) :
    next f (coset f x) = coset f (x * stable f) := rfl

def cosetHeight (f : Monoid.End U) : Coset f → ℤ :=
  Quotient.lift (fun x => toAdd (height f x)) (by
    intro x y h
    have h' : x⁻¹ * y ∈ (of f).range := QuotientGroup.leftRel_apply.mp h
    obtain ⟨u,hu⟩ := h'
    have hy : y = x * of f u := by rw [hu,mul_inv_cancel_left]
    rw [hy,map_mul,height_of,mul_one])

@[simp] lemma cosetHeight_coset (f : Monoid.End U) (x : Torus f) :
    cosetHeight f (coset f x) = toAdd (height f x) := rfl

noncomputable def origin (f : Monoid.End U) (c : Coset f) : Torus f := c.out

@[simp] lemma coset_origin (f : Monoid.End U) (c : Coset f) :
    coset f (origin f c) = c := Quotient.out_eq' c

lemma origin_next_mem (f : Monoid.End U) (c : Coset f) :
    (origin f (next f c))⁻¹ * (origin f c * stable f) ∈ (of f).range := by
  apply QuotientGroup.eq.mp
  change coset f (origin f (next f c)) = coset f (origin f c * stable f)
  rw [coset_origin,← next_coset,coset_origin]

noncomputable def cosetOffset (f : Monoid.End U) (c : Coset f) : U :=
  Classical.choose (origin_next_mem f c)

lemma origin_next (f : Monoid.End U) (c : Coset f) :
    origin f (next f c) * of f (cosetOffset f c) = origin f c * stable f := by
  change origin f (next f c) * of f (Classical.choose (origin_next_mem f c)) = _
  rw [Classical.choose_spec (origin_next_mem f c),mul_inv_cancel_left]

end

open Monoid Multiplicative
noncomputable section
universe u
variable {U : Type u} [Group U] (f : Monoid.End U)

lemma smul_coset (g x : Torus f) : g • coset f x = coset f (g*x) := rfl
lemma next_smul (g : Torus f) (c : Coset f) : next f (g • c) = g • next f c := by
  induction c using QuotientGroup.induction_on with
  | H x => change coset f ((g*x)*stable f) = coset f (g*(x*stable f)); rw [mul_assoc]

lemma origin_action_mem (g : Torus f) (c : Coset f) :
    (origin f (g • c))⁻¹ * (g * origin f c) ∈ (of f).range := by
  apply QuotientGroup.eq.mp
  change coset f (origin f (g • c)) = coset f (g * origin f c)
  rw [coset_origin,← smul_coset,coset_origin]

def actionOffset (g : Torus f) (c : Coset f) : U :=
  Classical.choose (origin_action_mem f g c)
lemma origin_action (g : Torus f) (c : Coset f) :
    origin f (g • c) * of f (actionOffset f g c) = g * origin f c := by
  rw [actionOffset,Classical.choose_spec (origin_action_mem f g c),mul_inv_cancel_left]

variable (hf : Function.Injective f)
include hf
lemma actionOffset_one (c : Coset f) : actionOffset f 1 c = 1 := by
  apply of_injective f hf
  have h := origin_action f 1 c
  rw [one_smul,one_mul] at h
  exact (mul_left_cancel (h.trans (mul_one _).symm)).trans (map_one _).symm
lemma actionOffset_mul (g h : Torus f) (c : Coset f) :
    actionOffset f (g*h) c = actionOffset f g (h • c) * actionOffset f h c := by
  apply of_injective f hf
  apply mul_left_cancel (a := origin f ((g*h) • c))
  rw [map_mul,origin_action,mul_smul,←mul_assoc,origin_action]
  rw [mul_assoc,mul_assoc,origin_action]
lemma actionOffset_next (g : Torus f) (c : Coset f) :
    actionOffset f g (next f c) * cosetOffset f c =
      cosetOffset f (g • c) * f (actionOffset f g c) := by
  apply of_injective f hf
  apply mul_left_cancel (a := origin f (next f (g • c)))
  calc
    origin f (next f (g • c)) * of f (actionOffset f g (next f c) * cosetOffset f c) =
        (origin f (g • next f c) * of f (actionOffset f g (next f c))) * of f (cosetOffset f c) := by rw [map_mul,←mul_assoc,next_smul]
    _ = g * (origin f (next f c) * of f (cosetOffset f c)) := by rw [origin_action,mul_assoc]
    _ = g * (origin f c * stable f) := by rw [origin_next]
    _ = (origin f (g • c) * of f (actionOffset f g c)) * stable f := by rw [origin_action,mul_assoc]
    _ = (origin f (g • c) * stable f) * of f (f (actionOffset f g c)) := by rw [mul_assoc,of_mul_stable,←mul_assoc]
    _ = (origin f (next f (g • c)) * of f (cosetOffset f (g • c))) * of f (f (actionOffset f g c)) := by rw [origin_next]
    _ = origin f (next f (g • c)) * of f (cosetOffset f (g • c) * f (actionOffset f g c)) := by rw [map_mul,mul_assoc]

end
end UniversalFInfinity.AscendingTorus

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.ControlledCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal
open Set Metric Topology
open scoped NNReal ENNReal
open Set Metric Topology
open scoped TensorProduct

namespace UniversalFInfinity.Cellular

section
open Set Metric Topology
open scoped unitInterval
universe u v w
variable {X : Type u} {Y : Type v} {Z : Type w}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

def postPath (q : C(Y,Z)) : C(C(I,Y),C(I,Z)) :=
  ⟨fun a => q.comp a,ContinuousMap.continuous_postcomp q⟩

end

open Set Metric Topology
open scoped unitInterval
universe u v
end UniversalFInfinity.Cellular

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.CellularChains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal
open Set Metric Topology
open scoped NNReal ENNReal
open Set Metric Topology
open scoped TensorProduct

namespace UniversalFInfinity.Cellular

section
open Set Metric Topology
universe u
variable {G : Type u} [Group G] {X : Type u} [TopologicalSpace X] [T2Space X]
  [MulAction G X] [ContinuousConstSMul G X] [CWComplex (univ : Set X)]
variable {ι : ℕ → Type u}
variable (σ : ∀ n, (G × ι n) ≃ RelCWComplex.cell (univ : Set X) n)
variable (hσ : ∀ n (g h : G) (i : ι n) (x : Fin n → ℝ),
  RelCWComplex.map n (σ n (g*h,i)) x = g • RelCWComplex.map n (σ n (h,i)) x)

variable {E : Type u} [TopologicalSpace E] [MulAction G E] [ContinuousConstSMul G E]

lemma exists_equivariant_skeleton_extension_cells (n : ℕ)
    (b : C(Skeleton (univ : Set X) n,E))
    (hb : ∀ (g : G) x, b (skeletonTranslate σ hσ n g x) = g • b x)
    (hfill : ∀ i : ι n, ∃ d : C(Disk n,E), ∀ x, d (boundary n x) = b (skeletonBoundary n (σ n (1,i)) x)) :
    ∃ e : C(Skeleton (univ : Set X) (n+1),E),
      (∀ x, e (skeletonBase n x) = b x) ∧
      ∀ (g : G) x, e (skeletonTranslate σ hσ (n+1) g x) = g • e x := by
  choose d hd using hfill
  let D (j : RelCWComplex.cell (univ : Set X) n) : C(Disk n,E) :=
    ⟨fun x => ((σ n).symm j).1 • d ((σ n).symm j).2 x,
      (continuous_const_smul _).comp (d _).continuous⟩
  have hD (j : RelCWComplex.cell (univ : Set X) n) (x : Sphere n) :
      D j (boundary n x) = b (skeletonBoundary n j x) := by
    obtain ⟨⟨g,i⟩,rfl⟩ := (σ n).surjective j
    change ((σ n).symm (σ n (g,i))).1 • d ((σ n).symm (σ n (g,i))).2 (boundary n x) = _
    rw [Equiv.symm_apply_apply,hd]
    change g • b (skeletonBoundary n (σ n (1,i)) x) = _
    rw [←hb]
    congr 1
    apply Subtype.ext
    exact (hσ n g 1 i x.1).symm.trans (by rw [mul_one]; rfl)
  let f := Attachment.lift (skeletonBoundary (C := (univ : Set X)) n) b D hD
  let e : C(Skeleton (univ : Set X) (n+1),E) := f.comp ⟨(skeletonHomeomorph n).symm,(skeletonHomeomorph n).symm.continuous⟩
  have he_base (x : Skeleton (univ : Set X) n) : e (skeletonBase n x) = b x := by
    change f ((skeletonHomeomorph n).symm (skeletonBase n x)) = _
    rw [←skeletonAssembly_base]
    change f ((skeletonHomeomorph n).symm ((skeletonHomeomorph n) (Attachment.base _ x))) = _
    rw [Homeomorph.symm_apply_apply]
    rfl
  have he_cell (j : RelCWComplex.cell (univ : Set X) n) (x : Disk n) :
      e (skeletonCell n j x) = D j x := by
    change f ((skeletonHomeomorph n).symm (skeletonCell n j x)) = _
    rw [←skeletonAssembly_cell]
    change f ((skeletonHomeomorph n).symm ((skeletonHomeomorph n) (Attachment.cell _ j x))) = _
    rw [Homeomorph.symm_apply_apply]
    exact Attachment.lift_cell _ _ _ _ _ _
  refine ⟨e,he_base,?_⟩
  intro g x
  obtain ⟨y,rfl⟩ := skeletonAssembly_surjective n x
  cases y with
  | inl x =>
    change e (skeletonTranslate σ hσ (n+1) g (skeletonBase n x)) = g • e (skeletonBase n x)
    rw [skeletonTranslate_base,he_base,he_base,hb]
  | inr p =>
    obtain ⟨⟨h,i⟩,hj⟩ := (σ n).surjective p.1
    have heq : skeletonAssembly n (Sum.inr p) = skeletonCell n p.1 (Attachment.interior n p.2) := by
      exact skeletonAssembly_interior n p.1 p.2
    rw [heq,←hj,skeletonTranslate_cell,he_cell,he_cell]
    change ((σ n).symm (σ n (g*h,i))).1 • d ((σ n).symm (σ n (g*h,i))).2 _ =
      g • (((σ n).symm (σ n (h,i))).1 • d ((σ n).symm (σ n (h,i))).2 _)
    simp only [Equiv.symm_apply_apply,mul_smul]
end

section
open Set Metric Topology
universe u
variable {G : Type u} [Group G] {X : Type u} [TopologicalSpace X] [T2Space X]
  [MulAction G X] [ContinuousConstSMul G X] [CWComplex (univ : Set X)]
variable {ι : ℕ → Type u}
variable (σ : ∀ n, (G × ι n) ≃ RelCWComplex.cell (univ : Set X) n)
variable (hσ : ∀ n (g h : G) (i : ι n) (x : Fin n → ℝ),
  RelCWComplex.map n (σ n (g*h,i)) x = g • RelCWComplex.map n (σ n (h,i)) x)
variable {E : Type u} [TopologicalSpace E] [MulAction G E] [ContinuousConstSMul G E]
variable (n : ℕ) (b : C(Skeleton (univ : Set X) n,E))
variable (hb : ∀ (g : G) x, b (skeletonTranslate σ hσ n g x) = g • b x)

def skeletonObstructions (i : ι n) : C(Sphere n,E) :=
  b.comp (skeletonBoundary n (σ n (1,i)))

end

section
open Set Metric Topology
universe u
variable {G : Type u} [Group G] {X : Type u} [TopologicalSpace X] [T2Space X]
  [MulAction G X] [ContinuousConstSMul G X] [CWComplex (univ : Set X)]
variable {ι : ℕ → Type u}
variable (σ : ∀ n, (G × ι n) ≃ RelCWComplex.cell (univ : Set X) n)
variable (hσ : ∀ n (g h : G) (i : ι n) (x : Fin n → ℝ),
  RelCWComplex.map n (σ n (g*h,i)) x = g • RelCWComplex.map n (σ n (h,i)) x)
variable {E B : Type u} [TopologicalSpace E] [TopologicalSpace B]
  [MulAction G E] [ContinuousConstSMul G E] [MulAction G B]

lemma exists_equivariant_skeleton_lift_cells (n : ℕ) (p : C(E,B))
    (hp : ∀ (g : G) e, p (g • e) = g • p e)
    (F : C(Skeleton (univ : Set X) (n+1),B))
    (hF : ∀ (g : G) x, F (skeletonTranslate σ hσ (n+1) g x) = g • F x)
    (b : C(Skeleton (univ : Set X) n,E))
    (hb : ∀ (g : G) x, b (skeletonTranslate σ hσ n g x) = g • b x)
    (hfill : ∀ i : ι n, ∃ d : C(Disk n,E),
      (∀ x,d (boundary n x) = b (skeletonBoundary n (σ n (1,i)) x)) ∧
      ∀ x,p (d x) = F (skeletonCell n (σ n (1,i)) x))
    (hbF : ∀ x, p (b x) = F (skeletonBase n x)) :
    ∃ e : C(Skeleton (univ : Set X) (n+1),E),
      (∀ x, e (skeletonBase n x) = b x) ∧ (∀ x, p (e x) = F x) ∧
      ∀ (g : G) x, e (skeletonTranslate σ hσ (n+1) g x) = g • e x := by
  choose d hd hf using hfill
  let D (j : RelCWComplex.cell (univ : Set X) n) : C(Disk n,E) :=
    ⟨fun x => ((σ n).symm j).1 • d ((σ n).symm j).2 x,
      (continuous_const_smul _).comp (d _).continuous⟩
  have hD (j : RelCWComplex.cell (univ : Set X) n) (x : Sphere n) :
      D j (boundary n x) = b (skeletonBoundary n j x) := by
    obtain ⟨⟨g,i⟩,rfl⟩ := (σ n).surjective j
    change ((σ n).symm (σ n (g,i))).1 • d ((σ n).symm (σ n (g,i))).2 (boundary n x) = _
    rw [Equiv.symm_apply_apply,hd]
    change g • b (skeletonBoundary n (σ n (1,i)) x) = _
    rw [←hb]
    congr 1
    apply Subtype.ext
    exact (hσ n g 1 i x.1).symm.trans (by rw [mul_one]; rfl)
  let f := Attachment.lift (skeletonBoundary (C := (univ : Set X)) n) b D hD
  let e : C(Skeleton (univ : Set X) (n+1),E) := f.comp ⟨(skeletonHomeomorph n).symm,(skeletonHomeomorph n).symm.continuous⟩
  have he_base (x : Skeleton (univ : Set X) n) : e (skeletonBase n x) = b x := by
    change f ((skeletonHomeomorph n).symm (skeletonBase n x)) = _
    rw [←skeletonAssembly_base]
    change f ((skeletonHomeomorph n).symm ((skeletonHomeomorph n) (Attachment.base _ x))) = _
    rw [Homeomorph.symm_apply_apply]
    rfl
  have he_cell (j : RelCWComplex.cell (univ : Set X) n) (x : Disk n) :
      e (skeletonCell n j x) = D j x := by
    change f ((skeletonHomeomorph n).symm (skeletonCell n j x)) = _
    rw [←skeletonAssembly_cell]
    change f ((skeletonHomeomorph n).symm ((skeletonHomeomorph n) (Attachment.cell _ j x))) = _
    rw [Homeomorph.symm_apply_apply]
    exact Attachment.lift_cell _ _ _ _ _ _
  have he (g : G) (x : Skeleton (univ : Set X) (n+1)) :
      e (skeletonTranslate σ hσ (n+1) g x) = g • e x := by
    obtain ⟨y,rfl⟩ := skeletonAssembly_surjective n x
    cases y with
    | inl x =>
      change e (skeletonTranslate σ hσ (n+1) g (skeletonBase n x)) = g • e (skeletonBase n x)
      rw [skeletonTranslate_base,he_base,he_base,hb]
    | inr q =>
      obtain ⟨⟨h,i⟩,hj⟩ := (σ n).surjective q.1
      have heq : skeletonAssembly n (Sum.inr q) = skeletonCell n q.1 (Attachment.interior n q.2) :=
        skeletonAssembly_interior n q.1 q.2
      rw [heq,←hj,skeletonTranslate_cell,he_cell,he_cell]
      change ((σ n).symm (σ n (g*h,i))).1 • d ((σ n).symm (σ n (g*h,i))).2 _ =
        g • (((σ n).symm (σ n (h,i))).1 • d ((σ n).symm (σ n (h,i))).2 _)
      simp only [Equiv.symm_apply_apply,mul_smul]
  refine ⟨e,he_base,?_,he⟩
  intro x
  obtain ⟨y,rfl⟩ := skeletonAssembly_surjective n x
  cases y with
  | inl x =>
    change p (e (skeletonBase n x)) = F (skeletonBase n x)
    rw [he_base,hbF]
  | inr q =>
    rw [skeletonAssembly_interior,he_cell]
    obtain ⟨⟨g,i⟩,hj⟩ := (σ n).surjective q.1
    rw [←hj]
    change p (((σ n).symm (σ n (g,i))).1 • d ((σ n).symm (σ n (g,i))).2 _) = _
    rw [Equiv.symm_apply_apply,hp,hf]
    change g • F (skeletonCell n (σ n (1,i)) _) = _
    rw [←hF,skeletonTranslate_cell,mul_one]
end

open Set Metric Topology
universe u v w
variable {Y : Type v} {Z : Type w} [TopologicalSpace Y] [TopologicalSpace Z]

lemma cylinder_filling_from_disk {n : ℕ} (q : C(Y,Z))
    (a : C(Sphere n,C(unitInterval,Y))) (b : C(Disk n,Y × Y))
    (h : ∀ x, pathEndpoint (a x) = b (boundary n x))
    (F : C(Disk (n+1),Z)) (hF : ∀ x,F (boundary (n+1) x) = q (cylinderBoundaryMap a b h x)) :
    ∃ e : C(Disk n,C(unitInterval,Z)),
      (∀ x t, e (boundary n x) t = q (a x t)) ∧
      ∀ x, pathEndpoint (e x) = (q (b x).1,q (b x).2) := by
  let e : C(Disk n,C(unitInterval,Z)) :=
    (F.comp ⟨fun p : Disk n × unitInterval => diskCons p.1 p.2,continuous_diskCons⟩).curry
  refine ⟨e,?_,?_⟩
  · intro x t
    let s : Sphere (n+1) := ⟨_,cons_mem_sphere_of_boundary x t⟩
    have hs : s ∈ cylinderFace n none := by
      change (diskTail (diskCons (boundary n x) t)).1 ∈ sphere 0 1
      rw [diskTail_cons]
      exact x.2
    change F (diskCons (boundary n x) t) = q (a x t)
    rw [show diskCons (boundary n x) t = boundary (n+1) s from rfl,hF,
      cylinderBoundaryMap_face a b h none ⟨s,hs⟩]
    change q (a (faceSphere ⟨s,hs⟩) (diskTime (diskCons (boundary n x) t))) = q (a x t)
    rw [diskTime_cons]
    congr 2
  · intro x
    apply Prod.ext
    · let s : Sphere (n+1) := ⟨_,cons_zero_mem_sphere x⟩
      have hs : s ∈ cylinderFace n (some false) := by
        change (diskCons x 0).1 0 = -1
        norm_num [diskCons]
      change F (diskCons x 0) = q (b x).1
      rw [show diskCons x 0 = boundary (n+1) s from rfl,hF,
        cylinderBoundaryMap_face a b h (some false) ⟨s,hs⟩]
      change q (b (diskTail (diskCons x 0))).1 = q (b x).1
      rw [diskTail_cons]
    · let s : Sphere (n+1) := ⟨_,cons_one_mem_sphere x⟩
      have hs : s ∈ cylinderFace n (some true) := by
        change (diskCons x 1).1 0 = 1
        norm_num [diskCons]
      change F (diskCons x 1) = q (b x).2
      rw [show diskCons x 1 = boundary (n+1) s from rfl,hF,
        cylinderBoundaryMap_face a b h (some true) ⟨s,hs⟩]
      change q (b (diskTail (diskCons x 1))).2 = q (b x).2
      rw [diskTail_cons]

end UniversalFInfinity.Cellular

namespace UniversalFInfinity.Attachment
open Cellular
universe u v
variable {G : Type u} [Group G] {E : Type v} [TopologicalSpace E]
variable [MulAction G E] [ContinuousConstSMul G E] {ι : Type v} {n : ℕ}
variable (a : ι → C(Sphere n,E))
lemma representative_filling (i : ι) :
    ∃ F : C(Disk n,Space (equivariantFamily (G := G) a)),
      ∀ x,F (boundary n x) = base _ (a i x) := by
  refine ⟨cell _ (show FreeIndex G ι from (1,i)),?_⟩
  intro x
  exact (cell_boundary _ _ x).trans (congrArg (base _) (one_smul G (a i x)))
end UniversalFInfinity.Attachment

namespace UniversalFInfinity.Cellular

section
open Set Metric Topology
open scoped unitInterval
universe u
variable {G : Type u} [Group G] {X : Type u} [TopologicalSpace X] [T2Space X]
  [MulAction G X] [ContinuousConstSMul G X] [CWComplex (univ : Set X)]
variable {ι : ℕ → Type u}
variable (κ : ∀ n, (G × ι n) ≃ RelCWComplex.cell (univ : Set X) n)
variable (hκ : ∀ n (g h : G) (i : ι n) (x : Fin n → ℝ),
  RelCWComplex.map n (κ n (g*h,i)) x = g • RelCWComplex.map n (κ n (h,i)) x)
variable {E : Type u} [TopologicalSpace E] [MulAction G E] [ContinuousConstSMul G E]
variable (n : ℕ) (a b : C(Skeleton (univ : Set X) (n+1),E))
variable (H : C(Skeleton (univ : Set X) n,C(I,E)))
variable (hH : ∀ x,pathEndpoint (H x) = (a (skeletonBase n x),b (skeletonBase n x)))

def homotopyObstructions (i : ι n) : C(Sphere (n+1),E) :=
  cylinderBoundaryMap (H.comp (skeletonBoundary n (κ n (1,i))))
    ((a.prodMk b).comp (skeletonCell n (κ n (1,i)))) (by
      intro x; exact hH (skeletonBoundary n (κ n (1,i)) x))

end

open Set Metric Topology
universe u
end UniversalFInfinity.Cellular

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.CellularFillings
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal
open Set Metric Topology
open scoped NNReal ENNReal
open Set Metric Topology
open scoped TensorProduct

namespace UniversalFInfinity.Cellular

section
open Set Metric Topology
universe u

def LowFillable (X : Type*) [TopologicalSpace X] (d : ℕ) : Prop :=
  ∀ n ≤ d, ∀ a : C(Sphere n,X), ∃ e : C(Disk n,X), ∀ x,e (boundary n x) = a x

end

section
open Set Metric Topology
universe u
variable {G : Type u} [Group G] {X Y : Type u}
  [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]
  [MulAction G X] [ContinuousConstSMul G X]
  [TopologicalSpace Y] [T2Space Y] [CWComplex (univ : Set Y)]
  [MulAction G Y] [ContinuousConstSMul G Y]
variable {ι κ : ℕ → Type u}
variable (α : ∀ n, (G × ι n) ≃ RelCWComplex.cell (univ : Set X) n)
  (hα : ∀ n (g h : G) (i : ι n) (x : Fin n → ℝ),
    RelCWComplex.map n (α n (g*h,i)) x = g • RelCWComplex.map n (α n (h,i)) x)
variable (β : ∀ n, (G × κ n) ≃ RelCWComplex.cell (univ : Set Y) n)
  (hβ : ∀ n (g h : G) (i : κ n) (x : Fin n → ℝ),
    RelCWComplex.map n (β n (g*h,i)) x = g • RelCWComplex.map n (β n (h,i)) x)
variable (n : ℕ) (q : C(Skeleton (univ : Set X) (n+1),Skeleton (univ : Set Y) (n+1)))
  (r : C(Skeleton (univ : Set Y) (n+1),X))
variable (H : C(Skeleton (univ : Set X) n,C(unitInterval,X)))
  (hH : ∀ x,pathEndpoint (H x) = ((skeletonBase n x).1,r (q (skeletonBase n x))))

def brownObstructions : κ (n+1) ⊕ ι n → C(Sphere (n+1),X) :=
  Sum.elim (skeletonObstructions β (n+1) r)
    (homotopyObstructions α n (skeletonInclusion (n+1)) (r.comp q) H hH)

abbrev BrownAttachment := Attachment.Space (Attachment.equivariantFamily (G := G)
  (brownObstructions α β n q r H hH))

def brownBase : C(X,BrownAttachment α β n q r H hH) :=
  ⟨Attachment.base _,Attachment.continuous_base _⟩

include hβ in
lemma brown_map_extension
    (hr : ∀ (g : G) x,r (skeletonTranslate β hβ (n+1) g x) = g • r x) :
    ∃ e : C(Skeleton (univ : Set Y) (n+2),BrownAttachment α β n q r H hH),
      (∀ x,e (skeletonBase (n+1) x) = brownBase α β n q r H hH (r x)) ∧
      ∀ (g : G) x,e (skeletonTranslate β hβ (n+2) g x) = g • e x := by
  apply exists_equivariant_skeleton_extension_cells β hβ (n+1)
    ((brownBase α β n q r H hH).comp r)
  · intro g x
    change Attachment.base _ (r (skeletonTranslate β hβ (n+1) g x)) = _
    rw [hr]; rfl
  · intro i
    obtain ⟨D,hD⟩ := Attachment.representative_filling (G := G)
      (brownObstructions α β n q r H hH) (Sum.inl i)
    exact ⟨D,hD⟩

include hα hβ in
lemma brown_homotopy_extension
    (hq : ∀ (g : G) x,q (skeletonTranslate α hα (n+1) g x) = skeletonTranslate β hβ (n+1) g (q x))
    (hr : ∀ (g : G) x,r (skeletonTranslate β hβ (n+1) g x) = g • r x)
    (hHe : ∀ (g : G) x,H (skeletonTranslate α hα n g x) = g • H x) :
    ∃ J : C(Skeleton (univ : Set X) (n+1),C(unitInterval,BrownAttachment α β n q r H hH)),
      (∀ x,pathEndpoint (J x) =
        (brownBase α β n q r H hH x.1,brownBase α β n q r H hH (r (q x)))) ∧
      ∀ (g : G) x,J (skeletonTranslate α hα (n+1) g x) = g • J x := by
  let b := brownBase α β n q r H hH
  let F := (b.comp (skeletonInclusion (n+1))).prodMk (b.comp (r.comp q))
  let L := (postPath b).comp H
  have hb (g : G) (x : X) : b (g • x) = g • b x := rfl
  have hF (g : G) x : F (skeletonTranslate α hα (n+1) g x) = g • F x := by
    apply Prod.ext
    · exact hb g x.1
    · change b (r (q (skeletonTranslate α hα (n+1) g x))) = g • b (r (q x))
      rw [hq,hr,hb]
  have hL (g : G) x : L (skeletonTranslate α hα n g x) = g • L x := by
    apply ContinuousMap.ext; intro t
    change b (H (skeletonTranslate α hα n g x) t) = g • b (H x t)
    rw [hHe]; rfl
  have hc (i : ι n) : ∃ e : C(Disk n,C(unitInterval,BrownAttachment α β n q r H hH)),
      (∀ x,e (boundary n x) = L (skeletonBoundary n (α n (1,i)) x)) ∧
      ∀ x,pathEndpoint (e x) = F (skeletonCell n (α n (1,i)) x) := by
    obtain ⟨D,hD⟩ := Attachment.representative_filling (G := G)
      (brownObstructions α β n q r H hH) (Sum.inr i)
    obtain ⟨e,he,hp⟩ := cylinder_filling_from_disk b
      (H.comp (skeletonBoundary n (α n (1,i))))
      (((skeletonInclusion (n+1)).prodMk (r.comp q)).comp (skeletonCell n (α n (1,i))))
      (fun x => hH (skeletonBoundary n (α n (1,i)) x)) D hD
    exact ⟨e,fun x => ContinuousMap.ext (he x),hp⟩
  have hL0 (x) : pathEndpoint (L x) = F (skeletonBase n x) :=
    Prod.ext (congrArg b (congrArg Prod.fst (hH x)))
      (congrArg b (congrArg Prod.snd (hH x)))
  obtain ⟨J,_,hJ,hJe⟩ := exists_equivariant_skeleton_lift_cells α hα n pathEndpoint
    (fun _ _ => rfl) F hF L hL hc hL0
  exact ⟨J,hJ,hJe⟩
end

open Set Metric Topology
universe u v w
variable {X : Type u} {Y : Type v} {W : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y] [CWComplex (univ : Set Y)]
  [TopologicalSpace W]

lemma fill_through_next_skeleton (d : ℕ) (q : C(X,Skeleton (univ : Set Y) d))
    (e : C(Skeleton (univ : Set Y) (d+1),W))
    (hq : ((skeletonInclusion d).comp q).Nullhomotopic)
    {m : ℕ} (hm : m ≤ d) [Nonempty (Sphere m)] (a : C(Sphere m,X)) :
    SphereTopology.Extends ((e.comp ((skeletonBase d).comp q)).comp a) := by
  obtain ⟨z,⟨H⟩⟩ := hq
  obtain ⟨F,hF⟩ := SphereTopology.extends_of_nullhomotopic (H.compContinuousMap a).symm
  obtain ⟨b,J,hstat⟩ := exists_cellular_approximation_bundle (d+1) F (fun _ => mem_univ _)
    ((Attachment.dimH_disk_subtype_le m).trans_lt (by exact_mod_cast Nat.lt_succ_of_le hm))
  refine ⟨e.comp b,?_⟩
  ext x
  apply congrArg e
  apply Subtype.ext
  have hFx : F (boundary m x) = (q (a x)).1 := ContinuousMap.congr_fun hF x
  have hx : F (boundary m x) ∈ Skeleton (univ : Set Y) (d+1) := by
    rw [hFx]
    exact (skeletonBase d (q (a x))).2
  have h := hstat 1 (boundary m x) hx
  exact (J.apply_one (boundary m x)).symm.trans h |>.trans hFx

lemma filling_after_skeletal_domination (d : ℕ)
    (q : C(X,Skeleton (univ : Set Y) d)) (e : C(Skeleton (univ : Set Y) (d+1),W))
    (hq : ((skeletonInclusion d).comp q).Nullhomotopic)
    (b : C(X,W)) (H : b.Homotopy (e.comp ((skeletonBase d).comp q)))
    {m : ℕ} (hm : m ≤ d) [Nonempty (Sphere m)] (a : C(Sphere m,X)) :
    SphereTopology.Extends (b.comp a) :=
  SphereTopology.extends_of_homotopy (H.compContinuousMap a)
    (fill_through_next_skeleton d q e hq hm a)
end UniversalFInfinity.Cellular

namespace UniversalFInfinity.Attachment
open Set Metric Topology Cellular
variable {G : Type*} [Group G] {X : Type*} [TopologicalSpace X]
  [MulAction G X] [ContinuousConstSMul G X] [Nonempty X]
variable {ι : Type*} {d : ℕ} (a : ι → C(Sphere d,X))
variable [T2Space (Space (equivariantFamily (G := G) a))]

lemma lowFillable_of_kills_old
    (hkill : ∀ m ≤ d, ∀ s : C(Sphere m,X),
      SphereTopology.Extends ((⟨base (equivariantFamily (G := G) a),continuous_base _⟩ :
        C(X,Space (equivariantFamily (G := G) a))).comp s)) :
    LowFillable (Space (equivariantFamily (G := G) a)) d := by
  intro m hm s
  cases m with
  | zero =>
    let : Nonempty (Space (equivariantFamily (G := G) a)) := ⟨base _ (Classical.choice ‹Nonempty X›)⟩
    exact SphereTopology.fill_zero s
  | succ m =>
    let := SphereTopology.sphere_nonempty m
    have hdim : dimH (Set.univ : Set (Sphere (m+1))) < d :=
      (GeneralPosition.dimH_cube_boundary_subtype_le m).trans_lt (by exact_mod_cast Nat.lt_of_succ_le hm)
    obtain ⟨s',H,_⟩ := exists_deformation_into_base (equivariantFamily (G := G) a) s hdim
    obtain ⟨F,hF⟩ := SphereTopology.extends_of_homotopy H (hkill (m+1) hm s')
    exact ⟨F,fun x => ContinuousMap.congr_fun hF x⟩
end UniversalFInfinity.Attachment

namespace UniversalFInfinity.Cellular

section
open Set Metric Topology
universe u
variable {G : Type u} [Group G] {X Y : Type u}
  [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]
  [MulAction G X] [ContinuousConstSMul G X]
  [TopologicalSpace Y] [T2Space Y] [CWComplex (univ : Set Y)]
  [MulAction G Y] [ContinuousConstSMul G Y]
variable {ι κ : ℕ → Type u}
variable (α : ∀ n, (G × ι n) ≃ RelCWComplex.cell (univ : Set X) n)
  (hα : ∀ n (g h : G) (i : ι n) (x : Fin n → ℝ),
    RelCWComplex.map n (α n (g*h,i)) x = g • RelCWComplex.map n (α n (h,i)) x)
variable (β : ∀ n, (G × κ n) ≃ RelCWComplex.cell (univ : Set Y) n)
  (hβ : ∀ n (g h : G) (i : κ n) (x : Fin n → ℝ),
    RelCWComplex.map n (β n (g*h,i)) x = g • RelCWComplex.map n (β n (h,i)) x)
variable (n : ℕ) (q : C(Skeleton (univ : Set X) (n+1),Skeleton (univ : Set Y) (n+1)))
  (r : C(Skeleton (univ : Set Y) (n+1),X))
variable (H : C(Skeleton (univ : Set X) n,C(unitInterval,X)))
  (hH : ∀ x,pathEndpoint (H x) = ((skeletonBase n x).1,r (q (skeletonBase n x))))

include hα hβ in
lemma brown_lowFillable [Nonempty X] [T2Space (BrownAttachment α β n q r H hH)]
    (hdim : Skeleton (univ : Set X) (n+1) = univ)
    (hqnull : ((skeletonInclusion (n+1)).comp q).Nullhomotopic)
    (hq : ∀ (g : G) x,q (skeletonTranslate α hα (n+1) g x) = skeletonTranslate β hβ (n+1) g (q x))
    (hr : ∀ (g : G) x,r (skeletonTranslate β hβ (n+1) g x) = g • r x)
    (hHe : ∀ (g : G) x,H (skeletonTranslate α hα n g x) = g • H x) :
    LowFillable (BrownAttachment α β n q r H hH) (n+1) := by
  obtain ⟨e,he,_⟩ := brown_map_extension α β hβ n q r H hH hr
  obtain ⟨J,hJ,_⟩ := brown_homotopy_extension α hα β hβ n q r H hH hq hr hHe
  let back : C(X,Skeleton (univ : Set X) (n+1)) :=
    ⟨fun x => ⟨x,by rw [hdim]; trivial⟩,continuous_id.subtype_mk (fun x => by rw [hdim]; trivial)⟩
  let q' := q.comp back
  let b := brownBase α β n q r H hH
  have hnull : ((skeletonInclusion (n+1)).comp q').Nullhomotopic := by
    obtain ⟨z,⟨K⟩⟩ := hqnull
    exact ⟨z,⟨K.compContinuousMap back⟩⟩
  let K : b.Homotopy (e.comp ((skeletonBase (n+1)).comp q')) :=
    { toFun := fun z => J (back z.2) z.1
      continuous_toFun := (J.continuous.comp (back.continuous.comp continuous_snd)).eval continuous_fst
      map_zero_left := fun x => congrArg Prod.fst (hJ (back x))
      map_one_left := fun x => (congrArg Prod.snd (hJ (back x))).trans (he (q (back x))).symm }
  apply Attachment.lowFillable_of_kills_old (G := G) (brownObstructions α β n q r H hH)
  intro m hm a
  cases m with
  | zero =>
    let : Nonempty (BrownAttachment α β n q r H hH) := ⟨b (Classical.choice ‹Nonempty X›)⟩
    obtain ⟨F,hF⟩ := SphereTopology.fill_zero (b.comp a)
    exact ⟨F,ContinuousMap.ext hF⟩
  | succ m =>
    let := SphereTopology.sphere_nonempty m
    exact filling_after_skeletal_domination (n+1) q' e hnull b K hm a
end

open Set Metric Topology
universe u
end UniversalFInfinity.Cellular

namespace UniversalFInfinity.Attachment
open Set Metric Topology Cellular
universe u
variable {G : Type u} [Group G] {X : Type u} [TopologicalSpace X] [T2Space X] [Nonempty X]
  [CWComplex (univ : Set X)] [MulAction G X] [ContinuousConstSMul G X]
variable {ι : ℕ → Type u} (α : ∀ m,(G × ι m) ≃ OldCell (X := X) m)
  (hα : ∀ m (g h : G) (i : ι m) (x : Fin m → ℝ),
    RelCWComplex.map m (α m (g*h,i)) x = g • RelCWComplex.map m (α m (h,i)) x)
variable {I : Type u} {n : ℕ} (a : I → C(Sphere n,X))

abbrev LayerOrbits (m : ℕ) := ι m ⊕ CellIndex.{u,u} m n I

def layerEquiv (m : ℕ) : (G × LayerOrbits (ι := ι) (I := I) (n := n) m) ≃
    LayerCell (X := X) (ι := FreeIndex G I) (n := n) m where
  toFun p := match p.2 with
    | Sum.inl i => Sum.inl (α m (p.1,i))
    | Sum.inr i => Sum.inr ⟨⟨i.down.1,(p.1,i.down.2)⟩⟩
  invFun p := match p with
    | Sum.inl i => (((α m).symm i).1,Sum.inl (((α m).symm i).2))
    | Sum.inr i => (i.down.2.1,Sum.inr ⟨⟨i.down.1,i.down.2.2⟩⟩)
  left_inv := by rintro ⟨g,i⟩; cases i <;> simp
  right_inv := by
    intro cell
    cases cell with
    | inl cell => simp
    | inr cell =>
      obtain ⟨⟨dimension,group,index⟩⟩ := cell
      rfl

omit [T2Space X] in
include hα in
lemma layerEquiv_map_disk (m : ℕ) (g h : G) (i : LayerOrbits (ι := ι) (I := I) (n := n) m)
    (x : Fin m → ℝ) (hx : x ∈ closedBall 0 1) :
    layerMap (equivariantFamily (G := G) a) m (layerEquiv α m (g*h,i)) x =
      g • layerMap (equivariantFamily (G := G) a) m (layerEquiv α m (h,i)) x := by
  cases i with
  | inl i =>
    change base _ (RelCWComplex.map m (α m (g*h,i)) x) = g • base _ (RelCWComplex.map m (α m (h,i)) x)
    rw [hα]; rfl
  | inr i =>
    obtain ⟨⟨⟨hm⟩,i⟩⟩ := i
    subst m
    change characteristic (equivariantFamily (G := G) a) (g*h,i) x =
      g • characteristic (equivariantFamily (G := G) a) (h,i) x
    exact (characteristic_disk _ (g*h,i) ⟨x,hx⟩).trans
      ((smul_cell _ (equivariantFamily_smul a) g (h,i) ⟨x,hx⟩).symm.trans
        (congrArg (g • ·) (characteristic_disk _ (h,i) ⟨x,hx⟩).symm))

variable (hdim : ∀ m (_ : OldCell (X := X) m),m < n)

omit [T2Space X] in
include hα in
lemma layerEquiv_image (m : ℕ) (g : G) (i : LayerOrbits (ι := ι) (I := I) (n := n) m)
    (A : Set (Fin m → ℝ)) (hA : A ⊆ closedBall 0 1) :
    (fun z => g • z) '' (layerMap (equivariantFamily (G := G) a) m (layerEquiv α m (1,i)) '' A) =
      layerMap (equivariantFamily (G := G) a) m (layerEquiv α m (g,i)) '' A := by
  rw [←Set.image_comp]
  apply Set.image_congr
  intro x hx
  have h := layerEquiv_map_disk α hα a m g 1 i x (hA hx)
  simpa only [mul_one,Function.comp_apply] using h.symm

variable [T2Space (Space (equivariantFamily (G := G) a))]

@[instance_reducible]
def equivariantLayerCW : CWComplex (univ : Set (Space (equivariantFamily (G := G) a))) := by
  let := layerCW (equivariantFamily (G := G) a) hdim
  exact actionCW (layerEquiv α)
    (fun m g i => layerEquiv_image α hα a m g i _ ball_subset_closedBall)
    (fun m g i => layerEquiv_image α hα a m g i _ subset_rfl)

lemma equivariantLayerCW_dims (m : ℕ) (i : (equivariantLayerCW α hα a hdim).cell m) : m < n+1 :=
  layerCW_dimensions (equivariantFamily (G := G) a) hdim m (layerEquiv α m i)

lemma equivariantLayerCW_smul (m : ℕ) (g h : G)
    (i : LayerOrbits (ι := ι) (I := I) (n := n) m) (x : Fin m → ℝ) :
    (equivariantLayerCW α hα a hdim).map m (g*h,i) x =
      g • (equivariantLayerCW α hα a hdim).map m (h,i) x := by
  change (g*h) • layerMap (equivariantFamily (G := G) a) m (layerEquiv α m (1,i)) x =
    g • (h • layerMap (equivariantFamily (G := G) a) m (layerEquiv α m (1,i)) x)
  exact mul_smul _ _ _

def layerOld (m : ℕ) (i : OldCell (X := X) m) :
    (equivariantLayerCW α hα a hdim).cell m :=
  (((α m).symm i).1,Sum.inl ((α m).symm i).2)

lemma layerOld_injective (m : ℕ) : Function.Injective (layerOld α hα a hdim m) := by
  intro i j h
  apply (α m).symm.injective
  have h1 := congrArg Prod.fst h
  have h2 := Sum.inl_injective (congrArg Prod.snd h)
  exact Prod.ext h1 h2

lemma layerOld_map (m : ℕ) (i : OldCell (X := X) m) (x : Fin m → ℝ) :
    (equivariantLayerCW α hα a hdim).map m (layerOld α hα a hdim m i) x =
      base (equivariantFamily (G := G) a) (RelCWComplex.map m i x) := by
  change ((α m).symm i).1 • base (equivariantFamily (G := G) a) (RelCWComplex.map m (α m (1,((α m).symm i).2)) x) = _
  change base (equivariantFamily (G := G) a) (((α m).symm i).1 • RelCWComplex.map m (α m (1,((α m).symm i).2)) x) = _
  rw [←hα,mul_one,Equiv.apply_symm_apply]

lemma layerOld_exhaustive (m : ℕ) (hm : m ≠ n)
    (i : (equivariantLayerCW α hα a hdim).cell m) :
    ∃ j,layerOld α hα a hdim m j = i := by
  obtain ⟨g,i⟩ := i
  cases i with
  | inl i => exact ⟨α m (g,i),by simp only [layerOld,Equiv.symm_apply_apply]⟩
  | inr i => exact (hm i.down.1.down).elim
end UniversalFInfinity.Attachment

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.TopologicalTowers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal
open Set Metric Topology
open scoped NNReal ENNReal
open Set Metric Topology
open scoped TensorProduct

namespace UniversalFInfinity.TopologicalTower
universe u v
variable (X : ℕ → Type u) [∀ n, TopologicalSpace (X n)]
variable (f : ∀ i j, i ≤ j → C(X i,X j)) [DirectedSystem X (f · · ·)]

abbrev Space := DirectLimit X f

end UniversalFInfinity.TopologicalTower

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.BrownConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal
open Set Metric Topology
open scoped NNReal ENNReal
open Set Metric Topology
open scoped TensorProduct

namespace UniversalFInfinity.Brown

section
open Set Metric Topology Cellular Attachment
universe u
variable (G : Type u) [Group G]

structure Stage (n : ℕ) where
  E : Type u
  B : Type u
  [topE : TopologicalSpace E]
  [topB : TopologicalSpace B]
  [nonemptyE : Nonempty E]
  [nonemptyB : Nonempty B]
  sepE : RealSeparated E
  sepB : RealSeparated B
  [cwE : CWComplex (univ : Set E)]
  [cwB : CWComplex (univ : Set B)]
  [action : MulAction G E]
  [continuousAction : ContinuousConstSMul G E]
  orbits : ℕ → Type u
  orbitFinite : ∀ m,Finite (orbits m)
  equiv : ∀ m,(G × orbits m) ≃ cwE.cell m
  equiv_map : ∀ m (g h : G) (i : orbits m) (x : Fin m → ℝ),
    cwE.map m (equiv m (g*h,i)) x = g • cwE.map m (equiv m (h,i)) x
  dimE : ∀ m (_ : cwE.cell m), m ≤ n
  dimB : ∀ m (_ : cwB.cell m), m ≤ n
  finiteB : ∀ m,Finite (cwB.cell m)
  fill : LowFillable E n
  p : C(E,B)
  covering : IsQuotientCoveringMap p G

attribute [instance] Stage.topE Stage.topB Stage.nonemptyE Stage.nonemptyB
  Stage.cwE Stage.cwB Stage.action Stage.continuousAction Stage.orbitFinite Stage.finiteB

instance instT2SpaceE {n : ℕ} (S : Stage G n) : T2Space S.E := S.sepE.t2Space

variable {G}

def ZeroOrbits : ℕ → Type u
  | 0 => PUnit
  | _+1 => PEmpty
end

open Set Metric Topology Cellular Attachment
universe u
end UniversalFInfinity.Brown

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.UniverseTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal
open Set Metric Topology
open scoped NNReal ENNReal
open Set Metric Topology
open scoped TensorProduct

open Set Metric Topology
namespace UniversalFInfinity.UniverseTransport

open Set Topology
universe u v
variable {G X E : Type u} [Group G] [TopologicalSpace X] [TopologicalSpace E]
  [MulAction G E] {p : E → X} (hp : IsQuotientCoveringMap p G)

def liftedCover : ULift.{v} E → ULift.{v} X := fun e => ⟨p e.down⟩
end UniversalFInfinity.UniverseTransport

end

end OAI
end


