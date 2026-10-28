-- Prove2me | Definitions.Def_OAIQ085D010
-- name    : OAIQ085D010
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T16:02:48.980709+00:00
-- url     : https://prove2.me/theorems/ccd9f8e8-14d8-44f8-bac0-91a9987e007b
-- title:
--   Definitions bundle OAIQ085D010 of the split of OpenAI, Constant-factor hardness of directed feedback vertex set (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DirectedFeedback.main`, carved from OpenAI's openai/math development (OpenAI, *Constant-factor hardness of directed feedback vertex set (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 296 declarations of OpenAI's Lean: 53 definitions, 3 inductive types or structures, 4 instances and 236 theorems. The definitions and types are `OAI.DFVSGames.Quadratic.nongenericFraction`, `OAI.DFVSGames.Reduction.ActualCanonical.Represents`, `OAI.DFVSGames.Reduction.ActualSource.NoiseEnumeration.ofFintype`, `OAI.DFVSGames.Soundness.ActualCanonicalPullback.outsideInsideEquiv`, `OAI.DFVSGames.Soundness.ActualCanonicalPullback.selectedFree`, `OAI.DFVSGames.Soundness.ActualPointAnswers.sourceTau`, `OAI.DFVSGames.Soundness.ConditionalIncidences.fillHidden`, `OAI.DFVSGames.Soundness.ConditionalIncidences.outsideRecord`, `OAI.DFVSGames.Soundness.IncidenceExtraction.LocalSimulation`, `OAI.DFVSGames.Soundness.IncidenceExtraction.LocalSimulation.induced`, `OAI.DFVSGames.Soundness.RepeatedGameBounds.Simulation.predicateGame`, `OAI.DFVSGames.Soundness.ZeroInformation.reconstructFirst`, `OAI.DFVSGames.Soundness.ZeroInformation.reconstructSecond`, `OAI.DirectedFeedback.BoundedExpr.Expr.subst`, `OAI.DirectedFeedback.BoundedExpr.LDef`, `OAI.DirectedFeedback.Construction.OutputArc`, `OAI.DirectedFeedback.Construction.bigAcceptance`, `OAI.DirectedFeedback.Construction.bigBudget`, `OAI.DirectedFeedback.Construction.bigFunction`, `OAI.DirectedFeedback.Construction.bigGood`, `OAI.DirectedFeedback.Construction.commonTransition`, `OAI.DirectedFeedback.Construction.failureEvent`, `OAI.DirectedFeedback.Construction.favorable`, `OAI.DirectedFeedback.Construction.prefixBit`, `OAI.DirectedFeedback.Construction.prefixTransition`, `OAI.DirectedFeedback.Construction.prefixValue`, `OAI.DirectedFeedback.Construction.rankOrder`, `OAI.DirectedFeedback.Construction.scaleDeletion`, `OAI.DirectedFeedback.Construction.smallAcceptance`, `OAI.DirectedFeedback.Construction.smallBudget`, `OAI.DirectedFeedback.Construction.smallFunction`, `OAI.DirectedFeedback.Construction.smallGood`, `OAI.DirectedFeedback.CookLevin.AddrDef`, `OAI.DirectedFeedback.CookLevin.CDef`, `OAI.DirectedFeedback.CookLevin.NPTableau.decodedPattern`, `OAI.DirectedFeedback.CookLevin.NPTableau.rawAccepts`, `OAI.DirectedFeedback.CookLevin.WDef`, `OAI.DirectedFeedback.Games.Game.Sound`, `OAI.DirectedFeedback.Games.listChoice`, `OAI.DirectedFeedback.Pivotal.acceptance` and 16 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `DirectedFeedback_Analysis_Deletion`, `DirectedFeedback_Analysis_NoiseEnumeration`, `DirectedFeedback_CookLevin_NPTableau`, `DirectedFeedback_Games_ActualCanonical`, `DirectedFeedback_Games_ConditionalIncidences`, `DirectedFeedback_Games_Harmonic`, `DirectedFeedback_Games_KernelCardinality`, `DirectedFeedback_Main`, `DirectedFeedback_Probability_RepeatedGameBounds`, `DirectedFeedback_RankGraph_AllGraph`, `DirectedFeedback_RankGraph_Bias`, `DirectedFeedback_RankGraph_CellCount`, `DirectedFeedback_RankGraph_FailureEvent`, `DirectedFeedback_RankGraph_LastBias`, `DirectedFeedback_RankGraph_OutputDef`, `DirectedFeedback_RankGraph_Point`, `DirectedFeedback_RankGraph_PrefixBit`, `DirectedFeedback_RankGraph_Rational`, `DirectedFeedback_RankGraph_RoundBoolean`, `DirectedFeedback_RankGraph_StackFinite`, `DirectedFeedback_RankGraph_SumBox`, `DirectedFeedback_RankGraph_UnweightedIntegrated`.
--
--   **Imports.** It imports the published bundle `Def_DirectedFeedback`; the bundles `OAIQ085D000`, `OAIQ085D001`, `OAIQ085D002`, `OAIQ085D003`, `OAIQ085D004` and `OAIQ085D005` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ085D016` and `OAIQ085D017`.
-- source:
--   OpenAI, Constant-factor hardness of directed feedback vertex set (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Constant-factor-hardness-of-directed-feedback-vertex-set-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Definitions.Def_DirectedFeedback
import Definitions.Def_OAIQ085D000
import Definitions.Def_OAIQ085D001
import Definitions.Def_OAIQ085D002
import Definitions.Def_OAIQ085D003
import Definitions.Def_OAIQ085D004
import Definitions.Def_OAIQ085D005

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_StackFinite
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype _root_.OAI.DFVSGames.Soundness.ConditionalIncidences.zeroBits _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain _root_.OAI.DirectedFeedback.RankPackets.shapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DirectedFeedback.BoundedExpr
open scoped BigOperators
namespace Expr

def subst {r s : Nat} (ρ : Fin r → Expr s) : Expr r → Expr s
  | .lit n => .lit n
  | .arg i => ρ i
  | .length => .length
  | .bit i => .bit (subst ρ i)
  | .add a b => .add (subst ρ a) (subst ρ b)
  | .mul a b => .mul (subst ρ a) (subst ρ b)
  | .sub a b => .sub (subst ρ a) (subst ρ b)
  | .zero a => .zero (subst ρ a)
  | .sum b e => .sum (subst ρ b) (subst (Fin.cons (.arg 0) (fun i => (ρ i).rename Fin.succ)) e)

theorem eval_subst {r s : Nat} (ρ : Fin r → Expr s) (e : Expr r) (x : List Bool) (a : Fin s → Nat) :
    (e.subst ρ).eval x a = e.eval x (fun i => (ρ i).eval x a) := by
  induction e generalizing s with
  | lit n => rfl
  | arg i => rfl
  | length => rfl
  | bit i ih => simp [subst,eval,ih]
  | add a b iha ihb => simp [subst,eval,iha,ihb]
  | mul a b iha ihb => simp [subst,eval,iha,ihb]
  | sub a b iha ihb => simp [subst,eval,iha,ihb]
  | zero a ih => simp [subst,eval,ih]
  | sum b e ihb ihe =>
    simp only [subst,eval,ihb,ihe]
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [eval]
    · simp [eval_rename,Function.comp_def]

end Expr

namespace Def
variable {r : Nat} {f g h : List Bool → (Fin r → Nat) → Nat}

theorem subst {s : Nat} (hf : Def f) (ρ : Fin r → List Bool → (Fin s → Nat) → Nat)
    (hρ : ∀ i, Def (ρ i)) : Def (fun x a => f x (fun i => ρ i x a)) := by
  classical
  choose terms hterms using hρ
  obtain ⟨e,he⟩ := hf
  refine ⟨e.subst terms,?_⟩
  intro x a
  rw [Expr.eval_subst]
  simpa only [hterms] using he x (fun i => ρ i x a)

theorem ite (ht : Def h) (hf : Def f) (hg : Def g) :
    Def (fun x a => if h x a = 0 then f x a else g x a) := by
  apply ((ht.zero.mul hf).add (ht.zero.zero.mul hg)).congr
  intro x a
  by_cases hh : h x a=0 <;> simp [hh]

theorem pow (hf : Def f) (n : Nat) : Def (fun x a => f x a ^ n) := by
  induction n with
  | zero => simpa using lit (r := r) 1
  | succ n ih => simpa only [pow_succ] using ih.mul hf

theorem poly (hf : Def f) (p : Polynomial Nat) : Def (fun x a => p.eval (f x a)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [Polynomial.eval_add] using hp.add hq
  | monomial k a => simpa only [Polynomial.eval_monomial] using (lit a).mul (hf.pow k)

theorem table (hf : Def f) (N : Nat) (t : Fin N → Nat) :
    Def (fun x a => if h : f x a < N then t ⟨f x a,h⟩ else 0) := by
  have hh := finset_sum Finset.univ (fun i : Fin N => fun x a => (if f x a=i.val then 1 else 0)*t i)
    (fun i _ => (hf.eq (lit i.val)).mul (lit (t i)))
  apply hh.congr
  intro x a
  by_cases h : f x a<N
  · rw [dite_eq_left h]
    rw [Finset.sum_eq_single (⟨f x a,h⟩ : Fin N)]
    · simp
    · intro b hb hne
      simp [show f x a ≠ b.val from fun he => hne (Fin.ext he.symm)]
    · simp
  · rw [dite_eq_right h]
    apply Finset.sum_eq_zero
    intro i hi
    simp [show f x a ≠ i.val by have := i.isLt; omega]

end Def
end DirectedFeedback.BoundedExpr


namespace DirectedFeedback.BoundedExpr
open scoped BigOperators
namespace Def
variable {r : Nat} {f g : List Bool → (Fin r → Nat) → Nat}

theorem div (hf : Def f) (hg : Def g) : Def (fun x a => f x a / g x a) := by
  have hf' := hf.rename Fin.succ
  have hg' := hg.rename Fin.succ
  have hi : Def (fun (_ : List Bool) (a : Fin (r+1) → Nat) => a 0) := arg 0
  have hlo := (hi.mul hg').le hf'
  have hhi := hf'.lt ((hi.add (lit 1)).mul hg')
  have hh := (hf.add (lit 1)).sum (hi.mul (hlo.mul hhi))
  apply hh.congr
  intro x a
  simp only [Function.comp_def,Fin.cons_zero,Fin.cons_succ]
  by_cases hg0 : g x a=0
  · simp [hg0]
  · have hgpos : 0<g x a := Nat.pos_of_ne_zero hg0
    have hquot : f x a / g x a < f x a+1 := Nat.lt_succ_of_le (Nat.div_le_self ..)
    rw [Finset.sum_eq_single (f x a/g x a)]
    · have h1 : f x a / g x a * g x a ≤ f x a := Nat.div_mul_le_self ..
      have h2 : f x a < (f x a/g x a+1)*g x a :=
        (Nat.div_lt_iff_lt_mul hgpos).mp (by omega)
      simp [h1,h2]
    · intro i hi hne
      by_cases h1 : i*g x a ≤ f x a
      · by_cases h2 : f x a < (i+1)*g x a
        · have hle := (Nat.le_div_iff_mul_le hgpos).mpr h1
          have hlt := (Nat.div_lt_iff_lt_mul hgpos).mpr h2
          omega
        · simp [h2]
      · simp [h1]
    · simp [hquot]

theorem mod (hf : Def f) (hg : Def g) : Def (fun x a => f x a % g x a) := by
  apply (hf.sub ((hf.div hg).mul hg)).congr
  intro x a
  exact (Nat.mod_eq_sub_div_mul ..).symm

theorem min (hf : Def f) (hg : Def g) : Def (fun x a => min (f x a) (g x a)) := by
  apply (hf.sub (hf.sub hg)).congr
  intro x a
  omega

theorem max (hf : Def f) (hg : Def g) : Def (fun x a => max (f x a) (g x a)) := by
  apply (hf.add (hg.sub hf)).congr
  intro x a
  omega

end Def
end DirectedFeedback.BoundedExpr


noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.BoundedExpr

namespace FDef
variable {r : Nat} {A B : Type} {f g : List Bool → (Fin r → Nat) → A}

theorem congr (hf : FDef f) (h : ∀ x a, f x a=g x a) : FDef g := by
  intro v
  apply (hf v).congr
  intro x a
  rw [h]

theorem const (v : A) : FDef (fun (_ : List Bool) (_ : Fin r → Nat) => v) := by
  intro w
  exact Def.lit (if v=w then 1 else 0)

theorem rename {s : Nat} (hf : FDef f) (ρ : Fin r → Fin s) : FDef (fun x a => f x (a ∘ ρ)) :=
  fun v => (hf v).rename ρ

theorem bind [Fintype A] (hf : FDef f)
    {g : A → List Bool → (Fin r → Nat) → B} (hg : ∀ v, FDef (g v)) :
    FDef (fun x a => g (f x a) x a) := by
  intro v
  have hh := Def.finset_sum Finset.univ
    (fun c : A => fun x a => (if f x a=c then 1 else 0)*(if g c x a=v then 1 else 0))
    (fun c _ => (hf c).mul (hg c v))
  apply hh.congr
  intro x a
  simp only [ite_mul, one_mul, zero_mul]
  simp

theorem map [Fintype A] (hf : FDef f) (t : A → B) : FDef (fun x a => t (f x a)) :=
  hf.bind (fun c => const (t c))

theorem toDef [Fintype A] (hf : FDef f) (t : A → Nat) : Def (fun x a => t (f x a)) := by
  have hh := Def.finset_sum Finset.univ
    (fun c : A => fun x a => (if f x a=c then 1 else 0)*t c)
    (fun c _ => (hf c).mul (Def.lit (t c)))
  apply hh.congr
  intro x a
  simp

theorem ite {h : List Bool → (Fin r → Nat) → Nat} (hh : Def h) (hf : FDef f) (hg : FDef g) :
    FDef (fun x a => if h x a=0 then f x a else g x a) := by
  intro v
  apply (hh.ite (hf v) (hg v)).congr
  intro x a
  split <;> simp_all

theorem bool {b : List Bool → (Fin r → Nat) → Bool}
    (h : Def (fun x a => if b x a then 1 else 0)) : FDef b := by
  intro v
  cases v with
  | true =>
    apply h.congr
    intro x a
    cases b x a <;> simp
  | false =>
    apply h.zero.congr
    intro x a
    cases b x a <;> simp

theorem decide {p : List Bool → (Fin r → Nat) → Prop}
    (h : Def (fun x a => if p x a then 1 else 0)) : FDef (fun x a => decide (p x a)) := by
  apply bool
  simpa

theorem ofNat {n : List Bool → (Fin r → Nat) → Nat} (hn : Def n) (N : Nat) (t : Fin N → A)
    (default : A) : FDef (fun x a => if h : n x a<N then t ⟨n x a,h⟩ else default) := by
  intro v
  have hh := (hn.lt (Def.lit N)).ite (Def.lit (if default=v then 1 else 0))
    (hn.table N (fun i => if t i=v then 1 else 0))
  apply hh.congr
  intro x a
  by_cases h : n x a<N <;> simp [h]

theorem pair [Fintype A] [Fintype B] (hf : FDef f)
    {g : List Bool → (Fin r → Nat) → B} (hg : FDef g) :
    FDef (fun x a => (f x a,g x a)) :=
  hf.bind (fun c => hg.map (Prod.mk c))

theorem pi {I : Type} [Fintype I] {F : I → Type} [∀ i, Fintype (F i)]
    {f : ∀ i, List Bool → (Fin r → Nat) → F i} (hf : ∀ i, FDef (f i)) :
    FDef (fun x a => fun i => f i x a) := by
  intro v
  have hsum := Def.finset_sum Finset.univ
    (fun i : I => fun x a => if f i x a = v i then 0 else 1)
    (fun i _ => (hf i (v i)).zero.congr (by intro x a; split <;> simp_all))
  apply hsum.zero.congr
  intro x a
  have he : (∑ i, if f i x a = v i then 0 else 1 : Nat)=0 ↔ (fun i => f i x a)=v := by
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)]
    simp only [Finset.mem_univ,true_implies,ite_eq_left_iff,one_ne_zero,imp_false,not_not]
    exact funext_iff.symm
  by_cases h : (fun i => f i x a)=v <;> simp_all

end FDef
end DirectedFeedback.BoundedExpr

end


noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.BoundedExpr

namespace PDef
variable {r : Nat} {p q : List Bool → (Fin r → Nat) → Prop}

theorem congr (hp : PDef p) (h : ∀ x a, p x a ↔ q x a) : PDef q :=
  Def.congr hp (fun x a => by simp only [h x a])

theorem const (p : Prop) : PDef (fun (_ : List Bool) (_ : Fin r → Nat) => p) :=
  Def.lit (if p then 1 else 0)

theorem and (hp : PDef p) (hq : PDef q) : PDef (fun x a => p x a ∧ q x a) := by
  apply Def.congr (Def.mul hp hq)
  intro x a
  by_cases h : p x a <;> by_cases h' : q x a <;> simp [h,h']

theorem or (hp : PDef p) (hq : PDef q) : PDef (fun x a => p x a ∨ q x a) := by
  exact (hp.not.and hq.not).not.congr (by intro x a; tauto)

theorem imp (hp : PDef p) (hq : PDef q) : PDef (fun x a => p x a → q x a) := by
  exact (hp.not.or hq).congr (by intro x a; tauto)

theorem all {I : Type} [Fintype I] {p : I → List Bool → (Fin r → Nat) → Prop}
    (hp : ∀ i, PDef (p i)) : PDef (fun x a => ∀ i, p i x a) := by
  have hh := (Def.finset_sum Finset.univ (fun i : I => fun x a => if ¬p i x a then 1 else 0)
    (fun i _ => Def.congr (hp i).not (by intro x a; by_cases h : p i x a <;> simp [h]))).zero
  apply hh.congr
  intro x a
  have he : (∑ i, if ¬p i x a then 1 else 0 : Nat)=0 ↔ ∀ i, p i x a := by
    simp
  by_cases h : ∀ i, p i x a <;> simp_all

theorem eq {A : Type} [Fintype A] {f g : List Bool → (Fin r → Nat) → A}
    (hf : FDef f) (hg : FDef g) : PDef (fun x a => f x a=g x a) :=
  (hf.pair hg).toDef (fun z => if z.1=z.2 then 1 else 0)

theorem nat_eq {f g : List Bool → (Fin r → Nat) → Nat} (hf : Def f) (hg : Def g) :
    PDef (fun x a => f x a=g x a) := Def.congr (hf.eq hg) (by intro x a; by_cases h : f x a=g x a <;> simp [h])

theorem le {f g : List Bool → (Fin r → Nat) → Nat} (hf : Def f) (hg : Def g) :
    PDef (fun x a => f x a≤g x a) := Def.congr (hf.le hg) (by intro x a; by_cases h : f x a≤g x a <;> simp [h])

theorem lt {f g : List Bool → (Fin r → Nat) → Nat} (hf : Def f) (hg : Def g) :
    PDef (fun x a => f x a<g x a) := Def.congr (hf.lt hg) (by intro x a; by_cases h : f x a<g x a <;> simp [h])

theorem decide (hp : PDef p) : FDef (fun x a => decide (p x a)) := FDef.decide hp

theorem ite {A : Type} {f g : List Bool → (Fin r → Nat) → A}
    (hp : PDef p) (hf : FDef f) (hg : FDef g) : FDef (fun x a => if p x a then f x a else g x a) := by
  apply (FDef.ite hp hg hf).congr
  intro x a
  by_cases h : p x a <;> simp [h]

theorem nite {f g : List Bool → (Fin r → Nat) → Nat}
    (hp : PDef p) (hf : Def f) (hg : Def g) : Def (fun x a => if p x a then f x a else g x a) := by
  apply (Def.ite hp hg hf).congr
  intro x a
  by_cases h : p x a <;> simp [h]

end PDef

namespace FDef
variable {r : Nat} {A : Type} [Fintype A]

theorem select {N : Nat} {f : Fin N → List Bool → (Fin r → Nat) → A}
    (hf : ∀ i, FDef (f i)) {n : List Bool → (Fin r → Nat) → Nat} (hn : Def n) (default : A) :
    FDef (fun x a => if h : n x a<N then f ⟨n x a,h⟩ x a else default) := by
  exact (FDef.pi hf).bind (fun table => hn |> fun hn => FDef.ofNat hn N table default)

end FDef
end DirectedFeedback.BoundedExpr

end


noncomputable section
open scoped Classical
namespace DirectedFeedback.DigitCodec
open BoundedExpr

theorem decode_def {r : Nat} {b n : List Bool → (Fin r → Nat) → Nat}
    (hb : Def b) (hn : Def n) (L : Nat) (i : Fin L) :
    Def (fun x a => decode (b x a) L (n x a) i) := by
  induction L generalizing n with
  | zero => exact i.elim0
  | succ L ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hn.mod hb
    · exact ih (hn.div hb) j

end DirectedFeedback.DigitCodec

end


noncomputable section
open scoped Classical
namespace DirectedFeedback.BoxCodec
open BoundedExpr
variable (Tag : Type) [Fintype Tag] [Nonempty Tag]
variable (b C L : Nat) (hb : 0<b)

theorem tag_equiv (a : Box Tag b C L) : tag Tag b C L (equiv Tag b C L hb a).val=a.1 := by
  have h := (equiv Tag b C L hb).left_inv a
  have he := congrArg Prod.fst h
  have hi : ((equiv Tag b C L hb a).val/(b^L*C))<Fintype.card Tag :=
    (finProdFinEquiv.symm (equiv Tag b C L hb a)).1.isLt
  rw [tag,dite_eq_left hi]
  exact he

theorem decode_tag (i : Fin (size Tag b C L)) :
    tag Tag b C L i.val=((equiv Tag b C L hb).symm i).1 := by
  simpa using tag_equiv Tag b C L hb ((equiv Tag b C L hb).symm i)

variable {b C L}
theorem tag_def {r : Nat} {b C i : List Bool → (Fin r → Nat) → Nat}
    (hb : Def b) (hC : Def C) (hi : Def i) (L : Nat) :
    FDef (fun x a => tag Tag (b x a) (C x a) L (i x a)) := by
  exact FDef.ofNat (hi.div ((hb.pow L).mul hC)) _ (Fintype.equivFin Tag).symm (Classical.choice inferInstance)
theorem digits_def {r : Nat} {b C i : List Bool → (Fin r → Nat) → Nat}
    (hb : Def b) (hC : Def C) (hi : Def i) (L : Nat) (j : Fin L) :
    Def (fun x a => digits (b x a) (C x a) L (i x a) j) :=
  DigitCodec.decode_def hb ((hi.mod ((hb.pow L).mul hC)).div hC) L j
theorem copy_def {r : Nat} {b C i : List Bool → (Fin r → Nat) → Nat}
    (hb : Def b) (hC : Def C) (hi : Def i) (L : Nat) :
    Def (fun x a => copy (b x a) (C x a) L (i x a)) :=
  (hi.mod ((hb.pow L).mul hC)).mod hC

end DirectedFeedback.BoxCodec

end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_SumBox
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain _root_.OAI.DirectedFeedback.RankPackets.shapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open scoped Classical
namespace DirectedFeedback.BoundedExpr
variable {r : Nat} {A B : Type} [Fintype A] [Fintype B]

structure LDef (l : List Bool → (Fin r → Nat) → List A) : Prop where
  length : Def (fun x a => (l x a).length)
  get : ∀ i, Def i → FDef (fun x a => (l x a)[i x a]?)

namespace LDef
variable {l m : List Bool → (Fin r → Nat) → List A}

omit [Fintype A] in
theorem const (l : List A) : LDef (fun (_ : List Bool) (_ : Fin r → Nat) => l) := by
  constructor
  · exact Def.lit l.length
  · intro i hi
    apply (FDef.ofNat hi l.length (fun j => some l[j.val]) none).congr
    intro x a
    by_cases h : i x a<l.length
    · simp [h]
    · simp [h]

theorem input : LDef (fun (x : List Bool) (_ : Fin r → Nat) => x) := by
  constructor
  · exact Def.length
  · intro i hi
    apply ((PDef.lt hi Def.length).ite ((FDef.bool hi.bit).map some) (FDef.const none)).congr
    intro x a
    by_cases h : i x a<x.length
    · simp [h]
    · simp [h]

omit [Fintype A] in
theorem replicate {n : List Bool → (Fin r → Nat) → Nat} (hn : Def n) (v : A) :
    LDef (fun x a => List.replicate (n x a) v) := by
  constructor
  · simpa only [List.length_replicate] using hn
  · intro i hi
    exact ((PDef.lt hi hn).ite (FDef.const (some v)) (FDef.const none)).congr
      (by intro x a; by_cases h : i x a<n x a <;> simp [h])

omit [Fintype A] in
theorem append (hl : LDef l) (hm : LDef m) : LDef (fun x a => l x a++m x a) := by
  constructor
  · simpa only [List.length_append] using hl.length.add hm.length
  · intro i hi
    apply ((PDef.lt hi hl.length).ite (hl.get i hi) (hm.get _ (hi.sub hl.length))).congr
    intro x a
    by_cases h : i x a < (l x a).length <;> simp [List.getElem?_append,h]

omit [Fintype B] in
theorem map (hl : LDef l) (f : A → B) : LDef (fun x a => (l x a).map f) := by
  constructor
  · simpa only [List.length_map] using hl.length
  · intro i hi
    exact ((hl.get i hi).map (Option.map f)).congr (by intro x a; simp)
end LDef
end DirectedFeedback.BoundedExpr

end


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Analysis_Deletion
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Reduction.ActualOrbit

open DFVSGames.Integration.BinaryLinear

universe u v

variable {Q : Type u} {T : Type v} {s d : Nat}

instance vertexNonempty [Nonempty Q] (can : Q → Ambient s d × T) :
    Nonempty (Vertex can) := Nonempty.map (vertex can) inferInstance

end DFVSGames.Reduction.ActualOrbit

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_KernelCardinality
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Gadget.StageQuotient.spaceFinite _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype _root_.OAI.DFVSGames.Soundness.ConditionalIncidences.zeroBits _root_.OAI.DFVSGames.Soundness.ConditionalSimulation.firstInputFintype _root_.OAI.DFVSGames.Soundness.ConditionalSimulation.secondInputFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder _root_.OAI.DirectedFeedback.RankGraph.instFiniteRank _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain _root_.OAI.DirectedFeedback.RankPackets.shapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Soundness.PartnerLinear

open PartnerProjection
open DFVSGames.Integration.BinaryLinear (F2 ofBit toBit scalar_cases ofBit_toBit
  toBit_ofBit )

variable {P : Type} (rhs active : P → Bool) (slot : P → Slot)

noncomputable instance partnerFintype [Fintype P] : Fintype (PartnerPoint rhs active) := by
  classical
  exact Fintype.ofEquiv (PartnerCoordinates active) (partnerEquiv rhs active).symm

noncomputable instance partnerFiniteDimensional [Fintype P] :
    FiniteDimensional F2 (PartnerPoint rhs active) :=
  (partnerLinearEquiv rhs active).symm.finiteDimensional

end DFVSGames.Soundness.PartnerLinear


namespace DFVSGames.Soundness.ZeroInformation

noncomputable def reconstructFirst {P R O N : Type} (positions : List P)
    (single hidden : P → Bool) (zeta0 : Bits R) (zeta1 zeta2 omega : P → Bits R)
    (name : O → Fin 3 → N) (insideOccurrences outsideOccurrences : P → O)
    (outsideNames : P → N) : FirstInput P R O :=
  firstInput positions single zeta0 zeta1 zeta2 omega
    (reconstructQuestion hidden insideOccurrences outsideOccurrences)
    (fun j => decodeIndex name (outsideOccurrences j) (outsideNames j))

def reconstructSecond {P R O N : Type} (positions : List P)
    (single hidden : P → Bool) (zeta0 : Bits R) (zeta1 zeta2 omega : P → Bits R)
    (outsideOccurrences : P → O) (insideNames outsideNames : P → N) : SecondInput P R O N :=
  secondInput positions single zeta0 zeta1 zeta2 omega outsideOccurrences
    (reconstructQuestion hidden insideNames outsideNames)

end DFVSGames.Soundness.ZeroInformation

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_ConditionalIncidences
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open scoped BigOperators

namespace DFVSGames.Soundness.ConditionalIncidences

noncomputable section

def outsideRecord {P O N : Type} (K : Finset P) (name : O → Fin 3 → N)
    (sample : Draw P O) : PositionOutside K → O × N :=
  fun j => incidence name (sample j.val)

end

end DFVSGames.Soundness.ConditionalIncidences
end

namespace DFVSGames.Soundness.IncidenceExtraction

structure LocalSimulation
    {InnerQA InnerQB InnerA InnerB OuterQA OuterQB OuterA OuterB : Type}
    (inner : Game InnerQA InnerQB InnerA InnerB)
    (outer : Game OuterQA OuterQB OuterA OuterB) where
  questionA : InnerQA → OuterQA
  questionB : InnerQB → OuterQB
  answerA : InnerQA → OuterA → InnerA
  answerB : InnerQB → OuterB → InnerB
  sound : ∀ qa qb a b,
    outer.accepts (questionA qa) (questionB qb) a b →
    inner.accepts qa qb (answerA qa a) (answerB qb b)

def LocalSimulation.induced
    {InnerQA InnerQB InnerA InnerB OuterQA OuterQB OuterA OuterB : Type}
    {inner : Game InnerQA InnerQB InnerA InnerB}
    {outer : Game OuterQA OuterQB OuterA OuterB}
    (r : LocalSimulation inner outer)
    (s : Strategies OuterQA OuterQB OuterA OuterB) :
    Strategies InnerQA InnerQB InnerA InnerB where
  first qa := r.answerA qa (s.first (r.questionA qa))
  second qb := r.answerB qb (s.second (r.questionB qb))

end DFVSGames.Soundness.IncidenceExtraction

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_ActualCanonical
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Reduction.ActualCanonical

open Integration.BinaryLinear ActualHomogeneous
open scoped BigOperators

universe u v w
variable {k : Nat}
variable {Name : Type u} {Id : Type v} {R : Type w}
variable [AddCommGroup R] [Module F2 R] [DecidableEq R]

def Represents (b : Fin k → F2) (z : R) (a : Fin k → Fin 3 → R)
    (X : E k →ₗ[F2] R) : Prop := ∀ x, ambientEval b z a x = X x

end DFVSGames.Reduction.ActualCanonical

namespace DFVSGames.Soundness.ActualCanonicalPullback

open scoped BigOperators
open PartnerProjection PartnerMapCoordinates
open ConditionalIncidences
open DFVSGames.Integration.BinaryLinear
open DFVSGames.Reduction

noncomputable section

variable {k : Nat} (rhsB : Fin k → Bool) (J : Finset (Fin k))
variable (R : Type) [AddCommGroup R] [Module F2 R]

def selectedFree (b : Fin k → F2) (slot : Fin k → Slot)
    (v : ActualHomogeneous.E k) (j : Fin k) : F2 :=
  match slot j with
  | .first => (v.2 j).1
  | .second => (v.2 j).2
  | .third => b j * v.1 + (v.2 j).1 + (v.2 j).2

def outsideInsideEquiv : (PositionOutside J ⊕ PositionInside J) ≃ Fin k where
  toFun j := Sum.elim Subtype.val Subtype.val j
  invFun j := if hj : j ∈ J then Sum.inr ⟨j,hj⟩ else Sum.inl ⟨j,hj⟩
  left_inv j := by
    cases j with
    | inl j => simp [j.property]
    | inr j => simp [j.property]
  right_inv j := by
    by_cases hj : j ∈ J <;> simp [hj]

end
end DFVSGames.Soundness.ActualCanonicalPullback

namespace DFVSGames.Soundness.ConditionalIncidences

noncomputable section

def fillHidden {P X : Type} [DecidableEq P] (K : Finset P)
    (fallback : P → X) (inside : PositionInside K → X) : P → X :=
  fun j => if hj : j ∈ K then inside ⟨j, hj⟩ else fallback j

end

end DFVSGames.Soundness.ConditionalIncidences

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Probability_RepeatedGameBounds
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Soundness.RepeatedGameBounds

open scoped BigOperators

noncomputable section

open Foundations.Games

namespace Simulation

variable {QA QB A B OA OB X Y : Type}
  [Fintype QA] [Fintype QB] [Fintype A] [Fintype B]
  [Fintype OA] [Fintype OB] [Fintype X] [Fintype Y]

def predicateGame (G : Game QA QB A B) : PredicateGame QA QB A B :=
  ⟨fun qa qb a b => G.accepts qa qb a b = true⟩

end Simulation

end
end DFVSGames.Soundness.RepeatedGameBounds

namespace DFVSGames.Soundness.ActualPointAnswers
open DFVSGames.Integration.BinaryLinear
open DFVSGames.Reduction
open PartnerProjection PartnerMapCoordinates RawPartnerTarget
open RepeatedGameBounds

noncomputable section
attribute [local instance] Classical.propDecidable

variable {k : Nat}

def sourceTau : ActualHomogeneous.E k →ₗ[F2] F2 := LinearMap.fst F2 F2 _

end
end DFVSGames.Soundness.ActualPointAnswers

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Analysis_NoiseEnumeration
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain _root_.OAI.DirectedFeedback.RankPackets.shapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Reduction.ActualSource

open scoped BigOperators

namespace NoiseEnumeration

variable {s d : Nat} {g : SplitGadget s d}

noncomputable def ofFintype (g : SplitGadget s d) : NoiseEnumeration g where
  indices := Finset.univ.toList
  nodup := Finset.nodup_toList _
  complete i := by simp

end NoiseEnumeration
end DFVSGames.Reduction.ActualSource

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_Harmonic
attribute [-instance] _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open DFVSGames.Gadget.Orientation

namespace DFVSGames.Quadratic

def nongenericFraction (F : Type*) [Field F] [Fintype F] [CharP F 2]
    [Algebra (ZMod 2) F] (r : ℕ) : ℚ :=
  (Nat.card {S : RankSpace (ZMod 2) (Fin 3 → F) r // ¬IsGeneric S.1} : ℚ) /
    Nat.card (RankSpace (ZMod 2) (Fin 3 → F) r)

end DFVSGames.Quadratic
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_CookLevin_NPTableau
attribute [-instance] _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace DirectedFeedback.CookLevin
open Turing
variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}

omit [DecidableEq K] in
theorem Window.words_ofCfg (S : ℕ) (c : TM2.Cfg Γ Λ σ)
    (hc : ∀ k, (c.stk k).length ≤ S) :
    (Window.ofCfg S c).words = WordCfg.ofCfg c := by
  unfold Window.words Window.ofCfg WordCfg.ofCfg
  congr 1
  funext k i
  by_cases hi : i < S
  · simp [wordsOfLists, hi]
  · simp only [dite_eq_right hi, wordsOfLists]
    exact (List.getElem?_eq_none ((hc k).trans (Nat.le_of_not_gt hi))).symm

end DirectedFeedback.CookLevin

end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_UnweightedIntegrated
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators

namespace DirectedFeedback.RankGraph
variable {U V X Y : Type} {T N L : ℕ}
variable (ord : Rank U V X Y T N → ℕ)
variable (ψ : Fin L → Fin N)

def Good (hL : 30 ≤ L) (d : Tuple U V T) : Prop :=
  ∀ E a c h, usable a c h → compareBit ord ψ d E a c h = referenceBit ord ψ hL d E

variable {ord ψ}

theorem twoLevel_arc (hψ : StrictMono ψ) (d : Tuple U V T)
    {E E' : Set (Domain U V X Y T d)} (hsub : E ⊆ E')
    {a a' h h' : Fin L} (haa : a < a') (hah : a < h') (hhh : h < h') :
    Arc (twoLevel ψ d E' a h) (twoLevel ψ d E a' h') := by
  classical
  refine ⟨d, _, _, rfl, rfl, ?_⟩
  intro lambda
  by_cases he : lambda ∈ E
  · simp only [he, hsub he, ↓reduceIte]
    exact hψ haa
  · by_cases he' : lambda ∈ E'
    · simp only [he, he', ↓reduceIte]
      exact hψ hah
    · simp only [he, he', ↓reduceIte]
      exact hψ hhh

theorem compareBit_mono_of_arc
    (hord : ∀ {a b}, Arc a b → ord a < ord b)
    {d : Tuple U V T} {E E' : Set (Domain U V X Y T d)}
    {a a' c h h' : Fin L}
    (ha : Arc (twoLevel ψ d E' a h) (twoLevel ψ d E a' h')) :
    compareBit ord ψ d E a' c h' ≤ compareBit ord ψ d E' a c h := by
  rw [Bool.le_iff_imp]
  simp only [compareBit, decide_eq_true_eq]
  exact fun hh => (hord ha).trans hh

theorem good_monotone (hL : 30 ≤ L) (hψ : StrictMono ψ)
    (hord : ∀ {a b}, Arc a b → ord a < ord b)
    (d : Tuple U V T) (hg : Good ord ψ hL d) :
    Monotone (referenceBit ord ψ hL d) := by
  intro E E' hsub
  have h1 := hg E' ⟨1, by omega⟩ ⟨14, by omega⟩ ⟨16, by omega⟩
    (by unfold usable; simp; omega)
  have h2 := hg E ⟨2, by omega⟩ ⟨14, by omega⟩ ⟨17, by omega⟩
    (by unfold usable; simp; omega)
  rw [← h1, ← h2]
  apply compareBit_mono_of_arc hord
  exact twoLevel_arc hψ d hsub (by simp) (by simp) (by simp)

theorem compare_prefix_big (t : ℕ) (ht : t < T) (s : Fin (t + 1) → U)
    (E : Set (Fin t → X)) (a c h : Fin L) :
    compareBit ord ψ (.inl ⟨⟨t, by omega⟩, Fin.init s⟩) E a c h =
      compareBit ord ψ (.inl ⟨⟨t + 1, by omega⟩, s⟩) (Fin.init ⁻¹' E) a c h := by
  unfold compareBit twoLevel
  rw [prefix_big t ht s]
  rfl

theorem compare_prefix_small (t : Fin T) (s : Fin t.val → U) (v : V)
    (E : Set (Fin t.val → X)) (a c h : Fin L) :
    compareBit ord ψ (.inl ⟨⟨t.val, by omega⟩, s⟩) E a c h =
      compareBit ord ψ (.inr ⟨t, s, v⟩) (Prod.fst ⁻¹' E) a c h := by
  unfold compareBit twoLevel
  rw [prefix_small t s v]
  rfl

theorem good_prefix_big (hL : 30 ≤ L) (t : ℕ) (ht : t < T)
    (s : Fin (t + 1) → U) (hg : Good ord ψ hL (.inl ⟨⟨t + 1, by omega⟩, s⟩)) :
    Good ord ψ hL (.inl ⟨⟨t, by omega⟩, Fin.init s⟩) := by
  intro E a c h hu
  unfold referenceBit
  rw [compare_prefix_big t ht s, compare_prefix_big t ht s]
  exact hg _ _ _ _ hu

end DirectedFeedback.RankGraph

namespace DirectedFeedback.RankGraph
variable {U V X Y : Type} {T N L k K : ℕ}
variable (ψ : Fin L → Fin N) (d : Tuple U V T)

variable {ψ d}

theorem wildcard_forcing (hL : L = 10 * K + 30) (hk : k ≤ K)
    (hψ : StrictMono ψ) (ord : Rank U V X Y T N → ℕ)
    (hg : Good ord ψ (by omega) d)
    (cell : Domain U V X Y T d → Fin k) (Z : Set (Domain U V X Y T d))
    (cut : ℕ) (hcut : cut ≤ k)
    (hpath : ∀ x y, belowWildcard d cell Z
        (fun j => ψ ⟨10 * j.val + 19, by have := j.isLt; omega⟩) x →
      aboveWildcard d cell Z
        (fun j => ψ ⟨10 * j.val + 19, by have := j.isLt; omega⟩) y →
      ord (vertex d x) < ord (vertex d y)) :
    ¬(referenceBit ord ψ (by omega) d ({lambda | (cell lambda).val < cut} \ Z) = false ∧
      referenceBit ord ψ (by omega) d
        (({lambda | (cell lambda).val < cut} \ Z) ∪ Z) = true) := by
  classical
  let E : Set (Domain U V X Y T d) := {lambda | (cell lambda).val < cut} \ Z
  let c : Fin L := ⟨10 * cut + 14, by omega⟩
  let lo : Fin L := ⟨1, by omega⟩
  let hi : Fin L := ⟨L - 2, by omega⟩
  let cm : Fin L := ⟨10 * cut + 12, by omega⟩
  let cp : Fin L := ⟨10 * cut + 16, by omega⟩
  let x : Domain U V X Y T d → Fin N := fun a => @ite (Fin N) (a ∈ E) (Classical.propDecidable _) (ψ lo) (ψ cp)
  let y : Domain U V X Y T d → Fin N := fun a => @ite (Fin N) (a ∈ E ∪ Z) (Classical.propDecidable _) (ψ cm) (ψ hi)
  have hx : belowWildcard d cell Z
      (fun j => ψ ⟨10 * j.val + 19, by have := j.isLt; omega⟩) x := by
    intro a ha
    by_cases hc : (cell a).val < cut
    · simp only [x, E, Set.mem_sdiff, Set.mem_ofPred_eq, hc, ha, not_false_eq_true,
        and_self, ↓reduceIte]
      apply hψ
      change 1 < 10 * (cell a).val + 19
      omega
    · simp only [x, E, Set.mem_sdiff, Set.mem_ofPred_eq, hc, false_and, ↓reduceIte]
      apply hψ
      change 10 * cut + 16 < 10 * (cell a).val + 19
      omega
  have hy : aboveWildcard d cell Z
      (fun j => ψ ⟨10 * j.val + 19, by have := j.isLt; omega⟩) y := by
    intro a ha
    by_cases hc : (cell a).val < cut
    · simp only [y, E, Set.mem_union, Set.mem_sdiff, Set.mem_ofPred_eq, hc, ha,
        not_false_eq_true, and_self, or_false, ↓reduceIte]
      apply hψ
      change 10 * (cell a).val + 19 < 10 * cut + 12
      omega
    · simp only [y, E, Set.mem_union, Set.mem_sdiff, Set.mem_ofPred_eq, hc, ha,
        false_and, or_self, ↓reduceIte]
      apply hψ
      change 10 * (cell a).val + 19 < L - 2
      have := (cell a).isLt
      omega
  have hu1 : usable lo c cp := by unfold usable; simp [lo, c, cp]; omega
  have hu2 : usable cm c hi := by unfold usable; simp [cm, c, hi]; omega
  intro hh
  have hb0 := (hg E lo c cp hu1).trans hh.1
  have hb1 := (hg (E ∪ Z) cm c hi hu2).trans hh.2
  have hn : ¬ord (vertex d x) < ord (marker (ψ c)) := by
    unfold compareBit at hb0
    have hh0 := of_decide_eq_false hb0
    simpa only [twoLevel, x] using hh0
  have hp : ord (vertex d y) < ord (marker (ψ c)) := by
    unfold compareBit at hb1
    have hh1 := of_decide_eq_true hb1
    simpa only [twoLevel, y] using hh1
  exact hn ((hpath x y hx hy).trans hp)

theorem comparison_forcing (hL : 30 ≤ L)
    (ord : Rank U V X Y T N → ℕ) (a b : Tuple U V T)
    (ha : Good ord ψ hL a) (hb : Good ord ψ hL b)
    (Ea : Set (Domain U V X Y T a)) (Eb : Set (Domain U V X Y T b))
    (hpath : ord (twoLevel ψ b Eb ⟨1, by omega⟩ ⟨16, by omega⟩) <
      ord (twoLevel ψ a Ea ⟨2, by omega⟩ ⟨17, by omega⟩)) :
    ¬(referenceBit ord ψ hL a Ea = true ∧ referenceBit ord ψ hL b Eb = false) := by
  intro hh
  have hh0 := (hb Eb ⟨1, by omega⟩ ⟨14, by omega⟩ ⟨16, by omega⟩
    (by unfold usable; simp; omega)).trans hh.2
  have hh1 := (ha Ea ⟨2, by omega⟩ ⟨14, by omega⟩ ⟨17, by omega⟩
    (by unfold usable; simp; omega)).trans hh.1
  simp only [compareBit, decide_eq_false_iff_not] at hh0
  simp only [compareBit, decide_eq_true_eq] at hh1
  exact hh0 (hpath.trans hh1)

end DirectedFeedback.RankGraph

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.TestGraph
open RankGraph
variable {U V X Y W C : Type} {T N : ℕ}

variable (wild : W → Wildcard (U := U) (V := V) (X := X) (Y := Y) (T := T) (N := N))
    (comp : C → Comparison (U := U) (V := V) (X := X) (Y := Y) (T := T) (N := N))

theorem wildcard_path (ord : Vertex U V X Y W C T N → ℕ)
    (retained : Vertex U V X Y W C T N → Prop)
    (hord : ∀ {a b}, retained a → retained b → Arc wild comp a b → ord a < ord b)
    (hrank : ∀ r, retained (.inl r)) (w : W) (hw : retained (.inr (.inl w)))
    (x y : Domain U V X Y T (wild w).tuple → Fin N)
    (hx : belowWildcard (wild w).tuple (wild w).cell (wild w).stars (wild w).level x)
    (hy : aboveWildcard (wild w).tuple (wild w).cell (wild w).stars (wild w).level y) :
    ord (.inl (vertex (wild w).tuple x)) < ord (.inl (vertex (wild w).tuple y)) :=
  (hord (hrank _) hw (.wild_in w x hx)).trans (hord hw (hrank _) (.wild_out w y hy))

theorem comparison_path (ord : Vertex U V X Y W C T N → ℕ)
    (retained : Vertex U V X Y W C T N → Prop)
    (hord : ∀ {a b}, retained a → retained b → Arc wild comp a b → ord a < ord b)
    (hrank : ∀ r, retained (.inl r)) (c : C) (hc : retained (.inr (.inr c))) :
    ord (.inl (comp c).source) < ord (.inl (comp c).target) :=
  (hord (hrank _) hc (.comp_in c)).trans (hord hc (hrank _) (.comp_out c))

end DirectedFeedback.TestGraph

noncomputable section
open scoped Classical
namespace DirectedFeedback.Prefix
variable {S X : Type*} {k : ℕ}

def Transition (g : Set S → Bool) (cell : S → Fin k) (r : Fin k) : Prop :=
  g (boundary cell r.val) = false ∧ g (boundary cell (r.val + 1)) = true

theorem boundary_mono (cell : S → Fin k) : Monotone (boundary cell) :=
  fun _ _ h _ ha => lt_of_lt_of_le ha h

theorem exists_transition (g : Set S → Bool) (cell : S → Fin k)
    (h0 : g ∅ = false) (h1 : g Set.univ = true) :
    ∃ r, Transition g cell r := by
  have he : ∃ r : ℕ, g (boundary cell r) = true := ⟨k, by simpa using h1⟩
  let n := Nat.find he
  have hn : g (boundary cell n) = true := Nat.find_spec he
  have hnk : n ≤ k := Nat.find_min' he (by simpa using h1)
  have hnpos : 0 < n := by
    by_contra hh
    have hn0 : n = 0 := by omega
    simp [hn0, h0] at hn
  refine ⟨⟨n - 1, by omega⟩, ?_, ?_⟩
  · have hh := Nat.find_min he (show n - 1 < n by omega)
    exact Bool.eq_false_iff.mpr hh
  · simpa only [Nat.sub_add_cancel hnpos] using hn

def transition (g : Set S → Bool) (cell : S → Fin k)
    (h0 : g ∅ = false) (h1 : g Set.univ = true) : Fin k :=
  Classical.choose (exists_transition g cell h0 h1)

theorem transition_spec (g : Set S → Bool) (cell : S → Fin k)
    (h0 : g ∅ = false) (h1 : g Set.univ = true) :
    Transition g cell (transition g cell h0 h1) :=
  Classical.choose_spec (exists_transition g cell h0 h1)

theorem conditionedSet_mono (cell : S → Fin k) (r : Fin k) :
    Monotone (conditionedSet (X := X) cell r) := by
  intro A B h a ha
  rcases ha with ha | ⟨ha, hb⟩
  · exact Or.inl ha
  · exact Or.inr ⟨ha, h hb⟩

theorem conditioned_properties (g : Set S → Bool) (g' : Set (S × X) → Bool)
    (hg' : Monotone g') (cell : S → Fin k) (r : Fin k) (hr : Transition g cell r)
    (hlift : ∀ E, g' (Prod.fst ⁻¹' E) = g E) :
    Monotone (fun R => g' (conditionedSet cell r R)) ∧
      g' (conditionedSet cell r ∅) = false ∧
      g' (conditionedSet cell r Set.univ) = true := by
  exact ⟨hg'.comp (conditionedSet_mono cell r), by simpa only [conditionedSet_empty, hlift] using hr.1,
    by simpa only [conditionedSet_univ, hlift] using hr.2⟩

theorem refined_even_boundary (cell : S → Fin k) (P : Set X) (r : ℕ) :
    boundary (refineCell cell P) (2 * r) = Prod.fst ⁻¹' boundary cell r := by
  classical
  ext a
  simp only [boundary, Set.mem_ofPred_eq, Set.mem_preimage, refineCell]
  split_ifs <;> omega

theorem refined_middle_boundary (cell : S → Fin k) (P : Set X) (r : Fin k) :
    boundary (refineCell cell P) (2 * r.val + 1) = conditionedSet cell r P := by
  classical
  ext a
  simp only [boundary, Set.mem_ofPred_eq, refineCell, conditionedSet, Fin.ext_iff]
  split_ifs
  all_goals simp_all
  all_goals omega

theorem transition_refines (g : Set S → Bool) (g' : Set (S × X) → Bool)
    (hg' : Monotone g') (cell : S → Fin k) (P : Set X)
    (hlift : ∀ E, g' (Prod.fst ⁻¹' E) = g E)
    {r : Fin k} {r' : Fin (2 * k)} (hr : Transition g cell r)
    (hr' : Transition g' (refineCell cell P) r') :
    r'.val / 2 = r.val := by
  have hlow : 2 * r.val ≤ r'.val := by
    by_contra hn
    have hh := hg' (boundary_mono (refineCell cell P)
      (show r'.val + 1 ≤ 2 * r.val by omega))
    rw [hr'.2, refined_even_boundary, hlift, hr.1] at hh
    contradiction
  have hhigh : r'.val < 2 * (r.val + 1) := by
    by_contra hn
    have hh := hg' (boundary_mono (refineCell cell P)
      (show 2 * (r.val + 1) ≤ r'.val by omega))
    rw [refined_even_boundary, hlift, hr.2, hr'.1] at hh
    contradiction
  omega

end DirectedFeedback.Prefix
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_CellCount
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype _root_.OAI.DFVSGames.Soundness.ConditionalIncidences.zeroBits _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.cellCountNeZero _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder _root_.OAI.DirectedFeedback.RankPackets.shapeFintype _root_.OAI.DirectedFeedback.RawFamily.eNonempty _root_.OAI.DirectedFeedback.RawFamily.wNonempty _root_.OAI.DirectedFeedback.StackDSL.Code.labelFintype
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
namespace DirectedFeedback.Prefix
variable {S X : Type*} {k : ℕ}

theorem transition_membership (g : Set S → Bool) (g' : Set (S × X) → Bool)
    (hg' : Monotone g') (cell : S → Fin k) (P : Set X)
    (hlift : ∀ E, g' (Prod.fst ⁻¹' E) = g E)
    {r : Fin k} {r' : Fin (2 * k)} (hr : Transition g cell r)
    (hr' : Transition g' (refineCell cell P) r')
    (a : S × X) (ha : refineCell cell P a = r') :
    decide (a.2 ∈ P) = g' (conditionedSet cell r P) := by
  classical
  have hdiv := transition_refines g g' hg' cell P hlift hr hr'
  have hav := congrArg Fin.val ha
  by_cases hp : a.2 ∈ P
  · have hex : r'.val = 2 * r.val := by
      simp only [refineCell, hp, ↓reduceIte, add_zero] at hav
      omega
    have hh := hr'.2
    rw [hex, refined_middle_boundary] at hh
    simpa only [hp, decide_true] using hh.symm
  · have hex : r'.val = 2 * r.val + 1 := by
      simp only [refineCell, hp, ↓reduceIte] at hav
      omega
    have hh := hr'.1
    rw [hex, refined_middle_boundary] at hh
    simpa only [hp, decide_false] using hh.symm

end DirectedFeedback.Prefix

noncomputable section
open scoped Classical
namespace DirectedFeedback.Prefix
variable {X : Type*}

def stepFunction (g : (t : ℕ) → Set (Fin t → X) → Bool) (t : ℕ)
    (E : Set ((Fin t → X) × X)) : Bool := g (t+1) (splitLast t ⁻¹' E)

theorem stepFunction_mono (g : (t : ℕ) → Set (Fin t → X) → Bool) (t : ℕ)
    (hg : Monotone (g (t+1))) : Monotone (stepFunction g t) := by
  intro E F hEF
  exact hg (Set.preimage_mono hEF)

theorem stepFunction_lift (g : (t : ℕ) → Set (Fin t → X) → Bool) (t : ℕ)
    (hlift : ∀ E, g (t+1) (Fin.init ⁻¹' E) = g t E) (E : Set (Fin t → X)) :
    stepFunction g t (Prod.fst ⁻¹' E) = g t E := hlift E

theorem step_transition (g : (t : ℕ) → Set (Fin t → X) → Bool) (t : ℕ)
    (P : ℕ → Set X) {r : Fin (cellCount (t+1))}
    (hr : Transition (g (t+1)) (prefixCell (t+1) P) r) :
    Transition (stepFunction g t) (refineCell (prefixCell t P) (P t)) r := hr

def conditionedValue (g : (t : ℕ) → Set (Fin t → X) → Bool) (P : ℕ → Set X)
    (r : (t : ℕ) → Fin (cellCount t)) (t : ℕ) (R : Set X) : Bool :=
  stepFunction g t (conditionedSet (prefixCell t P) (r t) R)

theorem selected_parent (g : (t : ℕ) → Set (Fin t → X) → Bool) (P : ℕ → Set X)
    (r : (t : ℕ) → Fin (cellCount t)) (t : ℕ)
    (hg : Monotone (g (t+1)))
    (hlift : ∀ E, g (t+1) (Fin.init ⁻¹' E) = g t E)
    (hr : Transition (g t) (prefixCell t P) (r t))
    (hr' : Transition (g (t+1)) (prefixCell (t+1) P) (r (t+1)))
    (a : Fin (t+1) → X) (ha : prefixCell (t+1) P a = r (t+1)) :
    prefixCell t P (Fin.init a) = r t := by
  have hd := transition_refines (g t) (stepFunction g t) (stepFunction_mono g t hg)
    (prefixCell t P) (P t) (stepFunction_lift g t hlift) hr (step_transition g t P hr')
  have hva := congrArg Fin.val ha
  apply Fin.ext
  dsimp only [prefixCell, refineCell] at hva
  split_ifs at hva <;> omega

theorem selected_last (g : (t : ℕ) → Set (Fin t → X) → Bool) (P : ℕ → Set X)
    (r : (t : ℕ) → Fin (cellCount t)) (t : ℕ)
    (hg : Monotone (g (t+1)))
    (hlift : ∀ E, g (t+1) (Fin.init ⁻¹' E) = g t E)
    (hr : Transition (g t) (prefixCell t P) (r t))
    (hr' : Transition (g (t+1)) (prefixCell (t+1) P) (r (t+1)))
    (a : Fin (t+1) → X) (ha : prefixCell (t+1) P a = r (t+1)) :
    decide (a (Fin.last t) ∈ P t) = conditionedValue g P r t (P t) :=
  transition_membership (g t) (stepFunction g t) (stepFunction_mono g t hg)
    (prefixCell t P) (P t) (stepFunction_lift g t hlift) hr (step_transition g t P hr')
    (Fin.init a, a (Fin.last t)) ha

theorem full_transition_membership (g : (t : ℕ) → Set (Fin t → X) → Bool)
    (P : ℕ → Set X) (r : (t : ℕ) → Fin (cellCount t)) (T : ℕ)
    (hg : ∀ t ≤ T, Monotone (g t))
    (hlift : ∀ t < T, ∀ E, g (t+1) (Fin.init ⁻¹' E) = g t E)
    (hr : ∀ t ≤ T, Transition (g t) (prefixCell t P) (r t))
    (a : Fin T → X) (ha : prefixCell T P a = r T) :
    ∀ j : Fin T, decide (a j ∈ P j.val) = conditionedValue g P r j.val (P j.val) := by
  induction T with
  | zero => intro j; exact Fin.elim0 j
  | succ T ih =>
    have ha' := selected_parent g P r T (hg _ (by omega)) (hlift _ (by omega))
      (hr _ (by omega)) (hr _ (by omega)) a ha
    have hp := ih (fun t ht => hg t (by omega)) (fun t ht => hlift t (by omega))
      (fun t ht => hr t (by omega)) (Fin.init a) ha'
    intro j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · exact selected_last g P r T (hg _ (by omega)) (hlift _ (by omega))
        (hr _ (by omega)) (hr _ (by omega)) a ha
    · exact hp i

end DirectedFeedback.Prefix

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Prefix
variable {S X : Type*} {k n : ℕ}

theorem ordered_boundary_sdiff (cell : S → Fin k) (order : X ≃ Fin n)
    (r : Fin k) (q : ℕ) (hq : q ≤ n) (j : X) :
    boundary (orderedCell cell order) (n*r.val+q) \ {a | a.2 = j} =
      {a | ((cell a.1).val < r.val ∧ a.2 ≠ j) ∨
        (cell a.1 = r ∧ a.2 ≠ j ∧ (order a.2).val < q)} := by
  ext a
  simp only [Set.mem_sdiff, boundary, orderedCell, Set.mem_ofPred_eq,
    block_prefix (order a.2).isLt hq, Fin.ext_iff]
  tauto

theorem single_label_crossing (cell : S → Fin k) (order : X ≃ Fin n)
    (r : Fin k) (q : ℕ) (hq : q ≤ n) (j : X)
    (g : Set (S × X) → Bool) (hg : Monotone g)
    (h0 : g (conditionedSet cell r {x | x ≠ j ∧ (order x).val < q}) = false)
    (h1 : g (conditionedSet cell r ({x | x ≠ j ∧ (order x).val < q} ∪ {j})) = true) :
    let E := boundary (orderedCell cell order) (n*r.val+q) \ {a | a.2 = j}
    g E = false ∧ g (E ∪ {a | a.2 = j}) = true := by
  dsimp only
  rw [ordered_boundary_sdiff cell order r q hq j]
  constructor
  · have h := hg (show {a : S × X | (cell a.1).val < r.val ∧ a.2 ≠ j ∨
        cell a.1 = r ∧ a.2 ≠ j ∧ (order a.2).val < q} ⊆
        conditionedSet cell r {x | x ≠ j ∧ (order x).val < q} by
        intro a ha
        rcases ha with ha | ha
        · exact Or.inl ha.1
        · exact Or.inr ⟨ha.1, ha.2⟩)
    rw [h0] at h
    exact le_antisymm h (by simp)
  · have h := hg (show conditionedSet cell r ({x | x ≠ j ∧ (order x).val < q} ∪ {j}) ⊆
        {a : S × X | (cell a.1).val < r.val ∧ a.2 ≠ j ∨
          cell a.1 = r ∧ a.2 ≠ j ∧ (order a.2).val < q} ∪ {a | a.2 = j} by
        intro a ha
        by_cases haj : a.2 = j
        · exact Or.inr haj
        · left
          rcases ha with ha | ⟨ha,hb⟩
          · exact Or.inl ⟨ha,haj⟩
          · exact Or.inr ⟨ha, hb.resolve_right (by simpa using haj)⟩)
    rw [h1] at h
    exact le_antisymm (by simp) h

end DirectedFeedback.Prefix

noncomputable section
open scoped BigOperators
namespace DirectedFeedback.SourceProbability

namespace FiniteDistribution

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

theorem probability_nonnegative (μ : FiniteDistribution Ω) (event : Ω → Bool) :
    0 ≤ μ.probability event := by
  apply Finset.sum_nonneg
  intro x _
  split
  · exact μ.nonnegative x
  · exact le_rfl

theorem probability_le_one (μ : FiniteDistribution Ω) (event : Ω → Bool) :
    μ.probability event ≤ 1 := by
  rw [← μ.normalized]
  apply Finset.sum_le_sum
  intro x _
  split
  · exact le_rfl
  · exact μ.nonnegative x

def transport (μ : FiniteDistribution Ω) (equiv : Ω ≃ Γ) : FiniteDistribution Γ where
  weight y := μ.weight (equiv.symm y)
  nonnegative y := μ.nonnegative (equiv.symm y)
  normalized := by rw [equiv.symm.sum_comp, μ.normalized]

end FiniteDistribution
namespace FiniteDistribution
variable {Ω Γ Q A : Type*} [Fintype Ω] [Fintype Γ] [Fintype Q] [Fintype A]

theorem expectation_comm (μ : FiniteDistribution Ω) (ν : FiniteDistribution Γ)
    (f : Ω → Γ → ℝ) :
    μ.expectation (fun x => ν.expectation (f x)) =
      ν.expectation (fun y => μ.expectation (fun x => f x y)) := by
  unfold expectation
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  exact mul_left_comm _ _ _

theorem iid_pushforward {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    (μ : FiniteDistribution Ω) (f : Ω → Γ) (n : Nat) :
    (μ.pushforward f).iid n =
      (μ.iid n).pushforward (fun answers i => f (answers i)) := by
  classical
  apply eq_of_weight_eq
  intro y
  simp only [iid, pushforward]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : (fun i => f (x i)) = y
  · have hp : ∀ i, f (x i) = y i := congrFun h
    simp [hp]
  · rw [ite_eq_right h]
    have hn : ¬ ∀ i, f (x i) = y i := fun hp => h (funext hp)
    obtain ⟨i, hi⟩ := not_forall.mp hn
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

end FiniteDistribution
end DirectedFeedback.SourceProbability

namespace DirectedFeedback.SourceProbability.FiniteDistribution
variable {I J : Type*} [Fintype I] [Fintype J]

theorem expectation_sum (μ : FiniteDistribution I) (f : J → I → ℝ) :
    μ.expectation (fun i => ∑ j, f j i) = ∑ j, μ.expectation (f j) := by
  simp_rw [expectation, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem expectation_pushforward (μ : FiniteDistribution I) (f : I → J) (h : J → ℝ) :
    (μ.pushforward f).expectation h = μ.expectation (fun a => h (f a)) := by
  classical
  simp only [expectation, pushforward, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp [ite_mul]

theorem table_pushforward {Q A B : Type*} [Fintype Q] [Fintype A] [Fintype B]
    [DecidableEq Q] (μ : Q → FiniteDistribution A) (f : Q → A → B) :
    (table μ).pushforward (fun x i => f i (x i)) =
      table (fun i => (μ i).pushforward (f i)) := by
  classical
  apply eq_of_weight_eq
  intro y
  simp only [table, pushforward]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : (fun i => f i (x i)) = y
  · have hp : ∀ i, f i (x i) = y i := congrFun h
    simp [hp]
  · rw [ite_eq_right h]
    symm
    obtain ⟨i, hi⟩ := not_forall.mp (show ¬ ∀ i, f i (x i) = y i from fun hp => h (funext hp))
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

end DirectedFeedback.SourceProbability.FiniteDistribution

noncomputable section
open scoped BigOperators
open DirectedFeedback.SourceProbability
namespace DirectedFeedback.Pivotal

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem law_relabel (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (σ : Equiv.Perm I) (f : (I → Bool) → ℝ) :
    (law p hp0 hp1).expectation (fun b => f (relabel σ b)) =
      (law p hp0 hp1).expectation f := by
  classical
  unfold FiniteDistribution.expectation
  symm
  apply Fintype.sum_equiv (relabel σ).symm
  intro b
  simp only [Equiv.apply_symm_apply]
  congr 1
  change (∏ i, (coin p hp0 hp1).weight (b i)) =
    ∏ i, (coin p hp0 hp1).weight (b (σ i))
  exact (Equiv.prod_comp σ (fun i => (coin p hp0 hp1).weight (b i))).symm

theorem sorted_chainPrefix (b : I → Bool) :
    ∃ σ : Equiv.Perm I, ∃ r ≤ Fintype.card I, b = relabel σ (chainPrefix I r) := by
  classical
  let s : Finset I := Finset.univ.filter (fun i => b i = true)
  have hcard : s.card ≤ Fintype.card I := Finset.card_le_univ _
  let first : Finset I := (Finset.univ : Finset (Fin s.card)).image
    (fun i => (Fintype.equivFin I).symm (Fin.castLE hcard i))
  have hfirst : first.card = s.card := by
    dsimp [first]
    rw [Finset.card_image_of_injective _
      (show Function.Injective (fun i : Fin s.card => (Fintype.equivFin I).symm (Fin.castLE hcard i)) from (Fintype.equivFin I).symm.injective.comp (Fin.castLE_injective hcard))]
    simp
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_map_finset_eq first s hfirst
  refine ⟨σ, s.card, hcard, ?_⟩
  ext i
  have hm : (σ.symm i ∈ first) ↔ (Fintype.equivFin I (σ.symm i)).val < s.card := by
    constructor
    · rintro hh
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hh
      rw [← hj]
      simp only [Equiv.apply_symm_apply]
      exact j.isLt
    · intro hi
      refine Finset.mem_image.mpr ⟨⟨_, hi⟩, Finset.mem_univ _, ?_⟩
      simp
  have hs : (i ∈ s) ↔ (σ.symm i ∈ first) := by
    rw [← hσ]
    simp
  apply Bool.eq_iff_iff.mpr
  simpa [s, relabel, chainPrefix] using hs.trans hm

omit [DecidableEq I] in
theorem probability_eq_expectation (μ : FiniteDistribution I) (event : I → Bool) :
    μ.probability event = μ.expectation (fun i => if event i then 1 else 0) := by
  unfold FiniteDistribution.probability FiniteDistribution.expectation
  apply Finset.sum_congr rfl
  intro i _
  cases h : event i <;> simp [h]

theorem bernoulli_le_chainBudget (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (event : (I → Bool) → Bool) :
    (law p hp0 hp1).probability event ≤ chainBudget event := by
  classical
  let U := FiniteDistribution.uniform (Equiv.Perm I)
  let f (b : I → Bool) : ℝ := if event b then 1 else 0
  have hf (b : I → Bool) : U.expectation (fun σ => f (relabel σ b)) ≤ chainBudget event := by
    obtain ⟨τ, r, hr, rfl⟩ := sorted_chainPrefix b
    calc
      _ ≤ U.expectation (fun σ => if chainHit event (τ.trans σ) then 1 else 0) := by
        apply FiniteDistribution.expectation_mono
        intro σ
        dsimp [f]
        by_cases hh : event (relabel (τ.trans σ) (chainPrefix I r)) = true
        · have hc : chainHit event (τ.trans σ) = true := by
            exact decide_eq_true ⟨r, hr, hh⟩
          simp [hh, hc]
        · simp [hh]
          split_ifs <;> norm_num
      _ = chainBudget event := by
        rw [show U = FiniteDistribution.uniform (Equiv.Perm I) from rfl,
          uniform_comp_right τ (fun σ => if chainHit event σ then 1 else 0)]
        exact (probability_eq_expectation _ _).symm
  rw [probability_eq_expectation]
  calc
    _ = U.expectation (fun σ => (law p hp0 hp1).expectation (fun b => f (relabel σ b))) := by
      simp_rw [law_relabel]
      rw [FiniteDistribution.expectation_const]
    _ = (law p hp0 hp1).expectation (fun b => U.expectation (fun σ => f (relabel σ b))) :=
      FiniteDistribution.expectation_comm _ _ _
    _ ≤ (law p hp0 hp1).expectation (fun _ => chainBudget event) :=
      FiniteDistribution.expectation_mono _ hf
    _ = chainBudget event := FiniteDistribution.expectation_const _ _

end DirectedFeedback.Pivotal

namespace DirectedFeedback.Pivotal
open DirectedFeedback.SourceProbability
open scoped BigOperators
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem sum_split (j : I) (H : (I → Bool) → ℝ) :
    (∑ x, H x) = ∑ x : {i : I // i ≠ j} → Bool,
      (H (insertBit j false x) + H (insertBit j true x)) := by
  rw [← Equiv.sum_comp (Equiv.funSplitAt j Bool).symm H]
  simp [Fintype.sum_prod_type, Finset.sum_add_distrib, insertBit, add_comm]

theorem prod_except (j : I) (g : I → ℝ) :
    (∏ i ∈ Finset.univ.erase j, g i) = ∏ i : {i : I // i ≠ j}, g i := by
  exact Finset.prod_subtype _ (by simp) g

def acceptance (f : (I → Bool) → Bool) (p : ℝ) : ℝ :=
  ∑ x, (∏ i, atom p (x i)) * bitValue (f x)

def discreteDerivative (f : (I → Bool) → Bool) (j : I)
    (x : {i : I // i ≠ j} → Bool) : ℝ :=
  bitValue (f (insertBit j true x)) - bitValue (f (insertBit j false x))

def totalInfluence (f : (I → Bool) → Bool) (p : ℝ) : ℝ :=
  ∑ j, ∑ x : {i : I // i ≠ j} → Bool,
    (∏ i, atom p (x i)) * discreteDerivative f j x

theorem acceptance_eq_probability (f : (I → Bool) → Bool)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    acceptance f p = (law p hp0 hp1).probability f := by
  rw [probability_eq_expectation]
  rfl

theorem russo (f : (I → Bool) → Bool) (p : ℝ) :
    HasDerivAt (acceptance f) (totalInfluence f p) p := by
  have h := HasDerivAt.fun_sum (u := (Finset.univ : Finset (I → Bool)))
    (fun x _ => (HasDerivAt.fun_finsetProd (u := (Finset.univ : Finset I))
      (fun i _ => atom_hasDerivAt (x i) p)).mul_const (bitValue (f x)))
  change HasDerivAt (acceptance f) _ p at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  simp only [totalInfluence, smul_eq_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [sum_split j]
  apply Finset.sum_congr rfl
  intro x _
  simp only [prod_except, insertBit_other, insertBit_self, Bool.false_eq_true,
    ↓reduceIte, discreteDerivative]
  ring

omit [Fintype I] in
theorem discreteDerivative_eq_indicator (f : (I → Bool) → Bool) (hf : Monotone f)
    (j : I) (x : {i : I // i ≠ j} → Bool) :
    discreteDerivative f j x = bitValue (pivotalEvent f j x) := by
  have hm : f (insertBit j false x) ≤ f (insertBit j true x) := by
    apply hf
    intro i
    by_cases hi : i = j
    · subst i; simp
    · simp [insertBit, hi]
  cases h0 : f (insertBit j false x) <;> cases h1 : f (insertBit j true x) <;>
    simp_all [discreteDerivative, bitValue, pivotalEvent, Bool.le_iff_imp]

theorem totalInfluence_eq_sum_probability (f : (I → Bool) → Bool) (hf : Monotone f)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    totalInfluence f p = ∑ j, (law p hp0 hp1).probability (pivotalEvent f j) := by
  unfold totalInfluence
  apply Finset.sum_congr rfl
  intro j _
  simp_rw [discreteDerivative_eq_indicator f hf]
  rw [probability_eq_expectation]
  rfl

theorem influence_le_budget (f : (I → Bool) → Bool) (hf : Monotone f)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    totalInfluence f p ≤ budget f := by
  rw [totalInfluence_eq_sum_probability f hf p hp0 hp1]
  exact Finset.sum_le_sum (fun j _ => bernoulli_le_chainBudget p hp0 hp1 _)

theorem influence_nonneg (f : (I → Bool) → Bool) (hf : Monotone f)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ totalInfluence f p := by
  rw [totalInfluence_eq_sum_probability f hf p hp0 hp1]
  exact Finset.sum_nonneg (fun j _ => FiniteDistribution.probability_nonnegative _ _)

theorem acceptance_zero (f : (I → Bool) → Bool) (h0 : f (fun _ => false) = false) :
    acceptance f 0 = 0 := by
  apply Finset.sum_eq_zero
  intro x _
  by_cases hx : x = fun _ => false
  · simp [hx, h0, bitValue]
  · have hh : ∃ i, x i = true := by
      by_contra hn
      apply hx
      funext i
      cases hi : x i
      · rfl
      · exact False.elim (hn ⟨i, hi⟩)
    obtain ⟨i, hi⟩ := hh
    have hz : (∏ i, atom 0 (x i)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [atom, hi])
    rw [hz, zero_mul]

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
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype _root_.OAI.DFVSGames.Reduction.ActualSource.sourceIndexNonempty _root_.OAI.DFVSGames.Soundness.ConditionalIncidences.zeroBits _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.CookLevin.NPTableau.codec_width_nonempty _root_.OAI.DirectedFeedback.RankPackets.shapeFintype _root_.OAI.DirectedFeedback.RawFamily.eNonempty _root_.OAI.DirectedFeedback.RawFamily.wNonempty _root_.OAI.DirectedFeedback.StackDSL.Code.labelFintype
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
namespace DirectedFeedback.Pivotal
open DirectedFeedback.SourceProbability
open scoped BigOperators
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem acceptance_le_mul_budget (f : (I → Bool) → Bool) (hf : Monotone f)
    (h0 : f (fun _ => false) = false) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (law p hp0 hp1).probability f ≤ p * budget f := by
  have hbound := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := acceptance f) (f' := totalInfluence f) (s := Set.Icc 0 p)
    (C := budget f)
    (fun q _ => (russo f q).hasDerivWithinAt)
    (fun q hq => by
      rw [Real.norm_eq_abs, abs_of_nonneg (influence_nonneg f hf q hq.1 (hq.2.trans hp1))]
      exact influence_le_budget f hf q hq.1 (hq.2.trans hp1))
    (convex_Icc (0 : ℝ) p) (show (0 : ℝ) ∈ Set.Icc 0 p from ⟨le_rfl, hp0⟩)
    (show p ∈ Set.Icc 0 p from ⟨hp0, le_rfl⟩)
  rw [acceptance_zero f h0, sub_zero, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg hp0, acceptance_eq_probability f p hp0 hp1,
    abs_of_nonneg (FiniteDistribution.probability_nonnegative _ _)] at hbound
  simpa [mul_comm] using hbound

end DirectedFeedback.Pivotal

namespace DirectedFeedback.SourceProbability.FiniteDistribution
open scoped BigOperators
variable {I J : Type*} [Fintype I] [Fintype J]

theorem probability_or_le_add (μ : FiniteDistribution I) (p q : I → Bool) :
    μ.probability (fun i => p i || q i) ≤ μ.probability p + μ.probability q := by
  unfold probability
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  cases hp : p i <;> cases hq : q i <;> simp [hp, hq, μ.nonnegative]

theorem indicator_difference (μ : FiniteDistribution I) (p q : I → Bool)
    (hpq : ∀ i, p i = true → q i = true) :
    μ.probability (fun i => decide (p i ≠ q i)) = μ.probability q - μ.probability p := by
  unfold probability
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases hp : p i <;> cases hq : q i <;> simp_all

theorem probability_disagree_triangle (μ : FiniteDistribution I) (p q r : I → Bool) :
    μ.probability (fun i => decide (p i ≠ r i)) ≤
      μ.probability (fun i => decide (p i ≠ q i)) +
      μ.probability (fun i => decide (q i ≠ r i)) := by
  calc
    _ ≤ μ.probability (fun i => decide (p i ≠ q i) || decide (q i ≠ r i)) := by
      apply probability_mono
      intro i hi
      simp only [decide_eq_true_eq, Bool.or_eq_true] at *
      by_cases h : p i = q i
      · exact Or.inr (fun hh => hi (h.trans hh))
      · exact Or.inl h
    _ ≤ _ := probability_or_le_add _ _ _

theorem probability_abs_sub_le_disagree (μ : FiniteDistribution I) (p q : I → Bool) :
    |μ.probability p - μ.probability q| ≤ μ.probability (fun i => decide (p i ≠ q i)) := by
  unfold probability
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |(if p i then μ.weight i else 0) - (if q i then μ.weight i else 0)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      cases hp : p i <;> cases hq : q i <;> simp [hp, hq, abs_of_nonneg (μ.nonnegative i)]

theorem pair_event_disagree (μ : FiniteDistribution I) (p p' q q' : I → Bool) :
    |μ.probability (fun i => p i && q i) - μ.probability (fun i => p' i && q' i)| ≤
      μ.probability (fun i => decide (p i ≠ p' i)) +
      μ.probability (fun i => decide (q i ≠ q' i)) := by
  apply (probability_abs_sub_le_disagree μ _ _).trans
  calc
    _ ≤ μ.probability (fun i => decide (p i ≠ p' i) || decide (q i ≠ q' i)) := by
      apply probability_mono
      intro i hi
      simp only [decide_eq_true_eq, Bool.or_eq_true] at *
      by_contra hn
      push Not at hn
      exact hi (by rw [hn.1, hn.2])
    _ ≤ _ := probability_or_le_add _ _ _

end DirectedFeedback.SourceProbability.FiniteDistribution

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.SourceProbability.FiniteDistribution
variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]

theorem expectation_transport (μ : FiniteDistribution I) (e : I ≃ J) (f : J → ℝ) :
    (μ.transport e).expectation f = μ.expectation (fun i => f (e i)) := by
  unfold expectation
  apply Fintype.sum_equiv e.symm
  intro j
  simp only [transport, Equiv.apply_symm_apply]

theorem uniform_transport [Nonempty I] [Nonempty J] (e : I ≃ J) :
    (uniform I).transport e = uniform J := by
  apply eq_of_weight_eq
  intro j
  simp only [transport, uniform, Fintype.card_congr e]

theorem uniform_product [Nonempty I] [Nonempty J] :
    (uniform I).product (uniform J) = uniform (I × J) := by
  apply eq_of_weight_eq
  intro x
  simp [product, uniform, Fintype.card_prod, Nat.cast_mul, mul_comm]

theorem probability_ge_atom (μ : FiniteDistribution I) (event : I → Bool) (a : I)
    (h : event a = true) : μ.weight a ≤ μ.probability event := by
  calc
    _ = (if event a then μ.weight a else 0) := by simp [h]
    _ ≤ _ := by
      unfold probability
      exact Finset.single_le_sum (f := fun i => if event i then μ.weight i else 0)
        (fun i _ => by cases event i <;> simp [μ.nonnegative]) (Finset.mem_univ a)

theorem probability_uniform [Nonempty I] (event : I → Bool) :
    (uniform I).probability event =
      ((Finset.univ.filter (fun i => event i = true)).card : ℝ) / Fintype.card I := by
  simp [probability, uniform, ← Finset.sum_filter, div_eq_mul_inv]

theorem expectation_table_pair {F : Type*} [Fintype F] [DecidableEq F]
    (α : I → FiniteDistribution J) (β : F → FiniteDistribution K)
    (i : I) (k : F) (f : J → K → ℝ) :
    (table α).expectation (fun x => (table β).expectation (fun y => f (x i) (y k))) =
      (α i).expectation (fun x => (β k).expectation (f x)) := by
  simp_rw [expectation_table_eval]
  exact expectation_table_eval α i (fun x => (β k).expectation (f x))

theorem markov_bound (μ : FiniteDistribution I) (B : I → ℝ) (hB : ∀ i, 0 ≤ B i)
    (c : ℝ) (hc : 0 < c) :
    μ.probability (fun i => decide (c < B i)) ≤ μ.expectation B / c := by
  apply (le_div_iff₀ hc).mpr
  rw [probability_eq_expect, ← expectation_mul_right]
  apply expectation_mono
  intro i
  by_cases hi : c < B i
  · simpa [hi] using hi.le
  · simpa [hi] using hB i

end DirectedFeedback.SourceProbability.FiniteDistribution

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Pivotal
open DirectedFeedback.SourceProbability FiniteDistribution
variable {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ}

def orderDecomposition (j : I) : (I ≃ Fin (n+1)) ≃ Fin (n+1) × ({i : I // i ≠ j} ≃ Fin n) where
  toFun e := (e j, deleteOrder j e)
  invFun q := insertOrder j q.1 q.2
  left_inv e := insert_delete_order j e
  right_inv q := by rcases q with ⟨r,e⟩; simp

theorem omittedHit_insert (j : I) (event : ({i : I // i ≠ j} → Bool) → Bool)
    (r : Fin (Fintype.card {i : I // i ≠ j} + 1))
    (e : {i : I // i ≠ j} ≃ Fin (Fintype.card {i : I // i ≠ j})) :
    omittedHit j event (insertOrder j r e) = orderHit event e := by
  apply Bool.eq_iff_iff.mpr
  simp only [omittedHit, orderHit, decide_eq_true_eq]
  constructor
  · rintro ⟨q,hq,he⟩
    refine ⟨if q ≤ r.val then q else q-1, by split_ifs <;> omega, ?_⟩
    convert he using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    funext x
    simp only [insertOrder_other, succAbove_cut_backward]
  · rintro ⟨q,hq,he⟩
    refine ⟨if q ≤ r.val then q else q+1, by split_ifs <;> omega, ?_⟩
    convert he using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    funext x
    simp only [insertOrder_other, succAbove_cut_forward]

theorem uniform_deleting (j : I) (event : ({i : I // i ≠ j} → Bool) → Bool) :
    let : Nonempty (I ≃ Fin (Fintype.card {i : I // i ≠ j} + 1)) :=
      ⟨insertOrder j 0 (Fintype.equivFin _)⟩
    (uniform (I ≃ Fin (Fintype.card {i : I // i ≠ j} + 1))).probability (omittedHit j event) =
      chainBudget event := by
  let : Nonempty (I ≃ Fin (Fintype.card {i : I // i ≠ j} + 1)) :=
    ⟨insertOrder j 0 (Fintype.equivFin _)⟩
  change (uniform _).probability (omittedHit j event) = chainBudget event
  rw [probability_eq_expect]
  rw [← uniform_transport (orderDecomposition j).symm, expectation_transport]
  rw [← uniform_product, expectation_product]
  change (uniform (Fin (Fintype.card {i : I // i ≠ j} + 1))).expectation
    (fun r => (uniform ({i : I // i ≠ j} ≃ Fin (Fintype.card {i : I // i ≠ j}))).expectation
      (fun e => if omittedHit j event (insertOrder j r e) then 1 else 0)) = _
  simp only [omittedHit_insert, expectation_const]
  rw [← uniform_transport (permutationOrder {i : I // i ≠ j}), expectation_transport]
  exact (probability_eq_expect _ _).symm

end DirectedFeedback.Pivotal

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Pivotal
open DirectedFeedback.SourceProbability FiniteDistribution
variable {I Ω : Type*} [Fintype I] [DecidableEq I] [Nonempty I] [Fintype Ω]

theorem labelOrder_hit_probability (f : (I → Bool) → Bool) :
    labelOrderLaw.probability (fun a : LabelOrder I => omittedHit a.1 (pivotalEvent f a.1) a.2) =
      budget f / Fintype.card I := by
  rw [probability_eq_expect, labelOrderLaw, expectation_sigma]
  simp_rw [← probability_eq_expect, uniform_deleting]
  rw [expectation_uniform]
  simp only [budget, div_eq_mul_inv, mul_comm]

theorem single_label_budget_charge (f : (I → Bool) → Bool) (deleted : LabelOrder I → Bool)
    (hforce : ∀ a, omittedHit a.1 (pivotalEvent f a.1) a.2 = true → deleted a = true) :
    budget f ≤ Fintype.card I * labelOrderLaw.probability deleted := by
  have hm := probability_mono (μ := labelOrderLaw) hforce
  rw [labelOrder_hit_probability] at hm
  have hc : (0:ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  exact (div_le_iff₀ hc).mp hm |>.trans_eq (mul_comm _ _)

omit [Nonempty I] in
theorem budget_nonneg (f : (I → Bool) → Bool) : 0 ≤ budget f := by
  exact Finset.sum_nonneg (fun _ _ => probability_nonnegative _ _)

omit [Nonempty I] in
theorem budget_le_card (f : (I → Bool) → Bool) : budget f ≤ Fintype.card I := by
  calc
    _ ≤ ∑ _ : I, (1:ℝ) := Finset.sum_le_sum (fun _ _ => probability_le_one _ _)
    _ = Fintype.card I := by simp

end DirectedFeedback.Pivotal

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.SourceProbability.FiniteDistribution
variable {I : Type*} [Fintype I]

theorem iid_snoc_transport (μ : FiniteDistribution I) (T : ℕ) :
    (μ.iid (T+1)).transport (splitSnoc T) = (μ.iid T).product μ := by
  apply eq_of_weight_eq
  intro a
  change (∏ t : Fin (T+1), μ.weight ((Fin.snoc a.1 a.2 : Fin (T+1) → I) t)) =
    (∏ t : Fin T, μ.weight (a.1 t)) * μ.weight a.2
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

theorem expectation_iid_snoc (μ : FiniteDistribution I) (T : ℕ) (f : (Fin (T+1) → I) → ℝ) :
    (μ.iid (T+1)).expectation f =
      (μ.iid T).expectation (fun a => μ.expectation (fun x => f (Fin.snoc a x))) := by
  have h := expectation_transport (μ.iid (T+1)) (splitSnoc T)
    (fun a => f (Fin.snoc a.1 a.2))
  rw [iid_snoc_transport, expectation_product] at h
  simpa only [splitSnoc, Equiv.coe_fn_mk, Fin.snoc_init_self] using h.symm

omit [Fintype I] in
theorem take_snoc_eq {t T : ℕ} (h : t ≤ T) (a : Fin T → I) (x : I) :
    takePrefix (by omega : t ≤ T+1) (Fin.snoc a x) = takePrefix h a := by
  funext i
  change (Fin.snoc a x : Fin (T+1) → I) ((Fin.castLE h i).castSucc) = a (Fin.castLE h i)
  simp only [Fin.snoc_castSucc]

theorem expectation_iid_take (μ : FiniteDistribution I) {t T : ℕ} (h : t ≤ T)
    (f : (Fin t → I) → ℝ) :
    (μ.iid T).expectation (fun a => f (takePrefix h a)) = (μ.iid t).expectation f := by
  induction T with
  | zero =>
    have ht : t = 0 := by omega
    subst t
    rfl
  | succ T ih =>
    by_cases ht : t ≤ T
    · rw [expectation_iid_snoc]
      simp_rw [take_snoc_eq ht, expectation_const]
      exact ih ht
    · have he : t = T+1 := by omega
      subst t
      simp

theorem expectation_iid_prefix_fresh (μ : FiniteDistribution I) {t T : ℕ} (h : t < T)
    (f : (Fin t → I) → I → ℝ) :
    (μ.iid T).expectation (fun a => f (takePrefix (by omega) a) (a ⟨t,h⟩)) =
      (μ.iid t).expectation (fun a => μ.expectation (f a)) := by
  have hh := expectation_iid_take μ (show t+1 ≤ T by omega)
    (fun a => f (Fin.init a) (a (Fin.last t)))
  rw [expectation_iid_snoc] at hh
  simp only [Fin.init_snoc, Fin.snoc_last] at hh
  exact hh

end DirectedFeedback.SourceProbability.FiniteDistribution

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.PrefixExperiment
open DirectedFeedback.SourceProbability FiniteDistribution
variable {U I P Ω : Type*} [Fintype U] [Fintype I] [Nonempty I] [Fintype P] [Fintype Ω]

def count (i : I) {T : ℕ} (f : Ω → (t : ℕ) → (Fin t → Atom U I P) → U → P → ℝ)
    (ω : Ω) (a : Fin T → Atom U I P) : ℝ :=
  ∑ t : Fin T, if (a t).2.1 = i then
    f ω t.val (takePrefix (Nat.le_of_lt t.isLt) a) (a t).1 (a t).2.2 else 0

def acceptance (μ : FiniteDistribution U) (ν : I → FiniteDistribution P) (i : I)
    (f : Ω → (t : ℕ) → (Fin t → Atom U I P) → U → P → ℝ)
    {T : ℕ} (d : Ω × (Σ t : Fin T, Fin t.val → Atom U I P)) : ℝ :=
  μ.expectation (fun u => (ν i).expectation (f d.1 d.2.1.val d.2.2 u))

theorem full_count_expectation (μΩ : FiniteDistribution Ω) (μ : FiniteDistribution U)
    (ν : I → FiniteDistribution P) (i : I) (T : ℕ) [NeZero T]
    (f : Ω → (t : ℕ) → (Fin t → Atom U I P) → U → P → ℝ) :
    (μΩ.product ((atomLaw μ ν).iid T)).expectation (fun a => count i f a.1 a.2) =
      ((T : ℝ) / Fintype.card I) * (commonLaw μΩ μ ν T).expectation (acceptance μ ν i f) := by
  rw [expectation_product]
  simp only [count]
  simp_rw [expectation_sum]
  have ht (ω : Ω) (t : Fin T) :
      ((atomLaw μ ν).iid T).expectation (fun a =>
        if (a t).2.1 = i then f ω t.val (takePrefix (Nat.le_of_lt t.isLt) a)
          (a t).1 (a t).2.2 else 0) =
      (1 / Fintype.card I) * ((atomLaw μ ν).iid t.val).expectation
        (fun a => μ.expectation (fun u => (ν i).expectation (f ω t.val a u))) := by
    rw [expectation_iid_prefix_fresh (atomLaw μ ν) t.isLt
      (fun a q => if q.2.1 = i then f ω t.val a q.1 q.2.2 else 0)]
    simp_rw [fresh_index_expectation, expectation_mul_left]
  simp_rw [ht]
  rw [commonLaw, expectation_product]
  simp_rw [expectation_sigma, expectation_uniform, acceptance]
  rw [← expectation_mul_left, ← expectation_sum]
  apply congrArg (expectation μΩ)
  funext ω
  rw [← Finset.mul_sum]
  simp only [Fintype.card_fin]
  have hT : (T : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne T
  field_simp

theorem acceptance_lower_bound (μΩ : FiniteDistribution Ω) (μ : FiniteDistribution U)
    (ν : I → FiniteDistribution P) (i : I) (T : ℕ) [NeZero T]
    (f : Ω → (t : ℕ) → (Fin t → Atom U I P) → U → P → ℝ)
    (p : ℝ) (hp : 0 ≤ p) (favorable : Ω × (Fin T → Atom U I P) → Bool)
    (hf : ∀ ω t a u q, 0 ≤ f ω t a u q)
    (hprob : 1/2 ≤ (μΩ.product ((atomLaw μ ν).iid T)).probability favorable)
    (hcount : ∀ a, favorable a = true →
      p * T / (2 * Fintype.card I) ≤ count i f a.1 a.2) :
    p/4 ≤ (commonLaw μΩ μ ν T).expectation (acceptance μ ν i f) := by
  have hM : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hT : (0 : ℝ) < T := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne T)
  have hnn (a : Ω × (Fin T → Atom U I P)) : 0 ≤ count i f a.1 a.2 := by
    apply Finset.sum_nonneg
    intro t _
    split_ifs <;> simp [hf]
  have hh := expectation_mono (μ := μΩ.product ((atomLaw μ ν).iid T))
    (f := fun a => (p * T / (2 * Fintype.card I)) * if favorable a then 1 else 0)
    (g := fun a => count i f a.1 a.2) (fun a => by
      cases ha : favorable a
      · simpa [ha] using hnn a
      · simpa [ha] using hcount a ha)
  rw [expectation_mul_left, ← probability_eq_expect, full_count_expectation] at hh
  have hmul := mul_le_mul_of_nonneg_left hprob
    (show 0 ≤ p * T / (2 * Fintype.card I) from by positivity)
  have hk : (p * T / (2 * Fintype.card I)) * (1/2) = (T / Fintype.card I) * (p/4) := by ring
  rw [hk] at hmul
  exact (mul_le_mul_iff_right₀ (div_pos hT hM)).mp (hmul.trans hh)

end DirectedFeedback.PrefixExperiment

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.SourceProbability.FiniteDistribution
variable {I B C D : Type*} [Fintype I] [Fintype B]

def splicePair (S : Finset I) : ((I → B) × (I → B)) ≃ ((I → B) × (I → B)) where
  toFun z := (splice S z.1 z.2, splice S z.2 z.1)
  invFun z := (splice S z.1 z.2, splice S z.2 z.1)
  left_inv z := by ext i <;> by_cases hi : i ∈ S <;> simp [splice, hi]
  right_inv z := by ext i <;> by_cases hi : i ∈ S <;> simp [splice, hi]

theorem splicePair_weight (α : I → FiniteDistribution B) (S : Finset I)
    (z : (I → B) × (I → B)) :
    ((table α).product (table α)).weight (splicePair S z) =
      ((table α).product (table α)).weight z := by
  change (∏ i, (α i).weight (splice S z.1 z.2 i)) *
    (∏ i, (α i).weight (splice S z.2 z.1 i)) =
    (∏ i, (α i).weight (z.1 i)) * (∏ i, (α i).weight (z.2 i))
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ S <;> simp [splice, hi, mul_comm]

theorem expectation_splicePair (α : I → FiniteDistribution B) (S : Finset I)
    (h : ((I → B) × (I → B)) → ℝ) :
    ((table α).product (table α)).expectation (fun z => h (splicePair S z)) =
      ((table α).product (table α)).expectation h := by
  unfold expectation
  apply Fintype.sum_equiv (splicePair S)
  intro z
  rw [splicePair_weight]

theorem expectation_disjoint (α : I → FiniteDistribution B) (S T : Finset I)
    (hST : Disjoint S T) (f g : (I → B) → ℝ) (hf : Uses S f) (hg : Uses T g) :
    (table α).expectation (fun x => f x * g x) =
      (table α).expectation f * (table α).expectation g := by
  have hs (z : (I → B) × (I → B)) : f (splice S z.1 z.2) = f z.1 := by
    apply hf
    intro i hi
    simp [splice, hi]
  have ht (z : (I → B) × (I → B)) : g (splice S z.1 z.2) = g z.2 := by
    apply hg
    intro i hi
    have hn : i ∉ S := fun hx => Finset.disjoint_left.mp hST hx hi
    simp [splice, hn]
  calc
    _ = ((table α).product (table α)).expectation (fun z => f z.1 * g z.1) := by
      rw [expectation_product]
      simp only [expectation_const]
    _ = ((table α).product (table α)).expectation
        (fun z => f (splice S z.1 z.2) * g (splice S z.1 z.2)) :=
      (expectation_splicePair α S (fun z => f z.1 * g z.1)).symm
    _ = ((table α).product (table α)).expectation (fun z => f z.1 * g z.2) := by
      apply expectation_congr
      intro z
      rw [hs, ht]
    _ = _ := by rw [expectation_product]; simp only [expectation_mul_left, expectation_mul_right]

theorem probability_disjoint_pattern (α : I → FiniteDistribution B) (S T : Finset I)
    (hST : Disjoint S T) (f g : (I → B) → Bool) (hf : Uses S f) (hg : Uses T g) :
    (table α).probability (fun x => f x && !(g x)) =
      (table α).probability f * (1 - (table α).probability g) := by
  rw [probability_eq_expect]
  have hid : (fun x => if f x && !(g x) then (1 : ℝ) else 0) =
      fun x => (if f x then 1 else 0) * (if !(g x) then 1 else 0) := by
    funext x
    cases f x <;> cases g x <;> norm_num
  rw [hid, expectation_disjoint α S T hST]
  · rw [← probability_eq_expect, ← probability_eq_expect, probability_not]
  · intro x y hxy
    dsimp only
    rw [hf x y hxy]
  · intro x y hxy
    dsimp only
    rw [hg x y hxy]

end DirectedFeedback.SourceProbability.FiniteDistribution

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Coupling
open DirectedFeedback.SourceProbability FiniteDistribution
open Pivotal
variable {X Y : Type*} [Fintype X] [Fintype Y]

theorem block_big (p : ℝ) (hp0 : 0 ≤ p) (hp : p ≤ 1/2) :
    (block p hp0 hp).pushforward Prod.fst =
      (coin p hp0 (by linarith)).product (coin p hp0 (by linarith)) := by
  apply eq_of_weight_eq
  rintro ⟨a,b⟩
  cases a <;> cases b <;>
    simp [pushforward, block, blockWeight, coin, product, Fintype.sum_prod_type] <;> ring

theorem block_small (p : ℝ) (hp0 : 0 ≤ p) (hp : p ≤ 1/2) :
    (block p hp0 hp).pushforward Prod.snd = coin (2*p) (by positivity) (by linarith) := by
  apply eq_of_weight_eq
  intro b
  cases b with
  | false => simp [pushforward, block, blockWeight, coin, Fintype.sum_prod_type]
  | true => simp [pushforward, block, blockWeight, coin, Fintype.sum_prod_type]; ring

theorem flatten_weight (e : X ≃ Y × Bool) (μ : FiniteDistribution Bool) (z : Y → Bool × Bool) :
    (table (fun _ : X => μ)).weight (flatten e z) =
      (table (fun _ : Y => μ.product μ)).weight z := by
  change (∏ x, μ.weight (flatten e z x)) = ∏ y, μ.weight (z y).1 * μ.weight (z y).2
  calc
    _ = ∏ q : Y × Bool, μ.weight (if q.2 then (z q.1).2 else (z q.1).1) :=
      e.prod_comp _
    _ = _ := by rw [Fintype.prod_prod_type]; simp [mul_comm]

theorem flatten_expectation (e : X ≃ Y × Bool) (μ : FiniteDistribution Bool)
    (f : (X → Bool) → ℝ) :
    (table (fun _ : Y => μ.product μ)).expectation (fun z => f (flatten e z)) =
      (table (fun _ : X => μ)).expectation f := by
  unfold expectation
  apply Fintype.sum_equiv (flatten e)
  intro z
  rw [flatten_weight]

theorem big_expectation (e : X ≃ Y × Bool) (p : ℝ) (hp0 : 0 ≤ p) (hp : p ≤ 1/2)
    (f : (X → Bool) → ℝ) :
    (law p hp0 hp).expectation (fun z => f (bigBits e z)) =
      (Pivotal.law p hp0 (by linarith)).expectation f := by
  unfold law bigBits
  rw [← expectation_pushforward (table (fun _ : Y => block p hp0 hp))
    (fun z y => (z y).1) (fun a => f (flatten e a)), table_pushforward]
  simp only [block_big]
  exact flatten_expectation e (coin p hp0 _) f

theorem small_expectation (p : ℝ) (hp0 : 0 ≤ p) (hp : p ≤ 1/2)
    (f : (Y → Bool) → ℝ) :
    (law p hp0 hp).expectation (fun z => f (smallBits z)) =
      (Pivotal.law (2*p) (by positivity) (by linarith)).expectation f := by
  unfold law smallBits
  rw [← expectation_pushforward (table (fun _ : Y => block p hp0 hp))
    (fun z y => (z y).2) f, table_pushforward]
  simp only [block_small, Pivotal.law]

theorem big_probability (e : X ≃ Y × Bool) (p : ℝ) (hp0 : 0 ≤ p) (hp : p ≤ 1/2)
    (f : (X → Bool) → Bool) :
    (law p hp0 hp).probability (fun z => f (bigBits e z)) =
      (Pivotal.law p hp0 (by linarith)).probability f := by
  simp only [probability_eq_expect]
  exact big_expectation e p hp0 hp (fun a => if f a then 1 else 0)

theorem small_probability (p : ℝ) (hp0 : 0 ≤ p) (hp : p ≤ 1/2)
    (f : (Y → Bool) → Bool) :
    (law p hp0 hp).probability (fun z => f (smallBits z)) =
      (Pivotal.law (2*p) (by positivity) (by linarith)).probability f := by
  simp only [probability_eq_expect]
  exact small_expectation p hp0 hp (fun a => if f a then 1 else 0)

theorem disjoint_pattern (e : X ≃ Y × Bool) (p : ℝ) (hp0 : 0 ≤ p) (hp : p ≤ 1/2)
    (J : Finset X) (K : Finset Y) (hJK : Disjoint (J.image (fun x => (e x).1)) K)
    (f : (X → Bool) → Bool) (g : (Y → Bool) → Bool) (hf : Uses J f) (hg : Uses K g) :
    (law p hp0 hp).probability (fun z => f (bigBits e z) && !(g (smallBits z))) =
      (Pivotal.law p hp0 (by linarith)).probability f *
        (1 - (Pivotal.law (2*p) (by positivity) (by linarith)).probability g) := by
  have hu : Uses (J.image (fun x => (e x).1)) (fun z => f (bigBits e z)) := by
    intro z w hzw
    apply hf
    intro x hx
    have h := hzw (e x).1 (Finset.mem_image.mpr ⟨x,hx,rfl⟩)
    simp only [bigBits, flatten, Equiv.coe_fn_mk, h]
  have hv : Uses K (fun z => g (smallBits z)) := by
    intro z w hzw
    apply hg
    intro y hy
    exact congrArg Prod.snd (hzw y hy)
  rw [show (law p hp0 hp) = table (fun _ : Y => block p hp0 hp) from rfl,
    probability_disjoint_pattern _ _ _ hJK _ _ hu hv]
  rw [← show (law p hp0 hp) = table (fun _ : Y => block p hp0 hp) from rfl,
    big_probability, small_probability]

end DirectedFeedback.Coupling

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Games
open DirectedFeedback.SourceProbability
open FiniteDistribution
variable {U V E X Y : Type} [Fintype U] [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]

def Game.Sound (G : Game U V E X Y) (θ : ℝ) : Prop :=
  ∀ lu lv, G.score lu lv ≤ θ

def listChoice (S : Finset X) : FiniteDistribution X :=
  if h : S.Nonempty then
    { weight := fun x => if x ∈ S then 1 / (S.card : ℝ) else 0
      nonnegative := fun x => by split_ifs <;> positivity
      normalized := by
        rw [← Finset.sum_filter]
        rw [show Finset.univ.filter (fun x => x ∈ S) = S by ext x; simp]
        simp only [Finset.sum_const, nsmul_eq_mul]
        have hz : (S.card : ℝ) ≠ 0 := by exact_mod_cast h.card_pos.ne'
        field_simp }
  else point (Classical.choice ‹Nonempty X›)

end DirectedFeedback.Games
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
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_Bias
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype _root_.OAI.DFVSGames.Soundness.ConditionalIncidences.zeroBits _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.RankPackets.shapeFintype _root_.OAI.DirectedFeedback.StackDSL.Code.labelFintype
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
namespace DirectedFeedback.Games
open DirectedFeedback.SourceProbability
open FiniteDistribution
variable {U V E X Y : Type} [Fintype U] [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]

theorem listChoice_weight {S : Finset X} {x : X} (hx : x ∈ S) :
    (listChoice S).weight x = 1 / (S.card : ℝ) := by
  have h : S.Nonempty := ⟨x, hx⟩
  simp only [listChoice, dite_eq_left h, hx, ↓reduceIte]

theorem listChoice_pair_success (π : X → Y) (S : Finset X) (R : Finset Y)
    (J : ℕ) (hJ : 1 ≤ J) (hS : S.card ≤ J) (hR : R.card ≤ J)
    (hh : ∃ x ∈ S, π x ∈ R) :
    1 / (J : ℝ)^2 ≤ ((listChoice S).product (listChoice R)).probability
      (fun z => decide (π z.1 = z.2)) := by
  obtain ⟨x, hx, hpx⟩ := hh
  have hcS : (0 : ℝ) < S.card := by exact_mod_cast (Finset.card_pos.mpr ⟨x, hx⟩)
  have hcR : (0 : ℝ) < R.card := by exact_mod_cast (Finset.card_pos.mpr ⟨π x, hpx⟩)
  have hSJ : (S.card : ℝ) ≤ J := by exact_mod_cast hS
  have hRJ : (R.card : ℝ) ≤ J := by exact_mod_cast hR
  have hJpos : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  calc
    1 / (J : ℝ)^2 = (1 / (J : ℝ)) * (1 / (J : ℝ)) := by ring
    _ ≤ (1 / (S.card : ℝ)) * (1 / (R.card : ℝ)) :=
      mul_le_mul (one_div_le_one_div_of_le hcS hSJ) (one_div_le_one_div_of_le hcR hRJ)
        (by positivity) (by positivity)
    _ = ((listChoice S).product (listChoice R)).weight (x, π x) := by
      simp only [product, listChoice_weight hx, listChoice_weight hpx]
    _ ≤ _ := probability_ge_atom _ _ (x, π x) (by simp)

omit [Nonempty X] [Nonempty Y] in

theorem randomized_score (G : Game U V E X Y)
    (α : U → FiniteDistribution X) (β : V → FiniteDistribution Y) :
    ((table α).product (table β)).expectation (fun l => G.score l.1 l.2) =
      G.edgeLaw.expectation (fun e => ((α (G.left e)).product (β (G.right e))).probability
        (fun z => decide (G.project e z.1 = z.2))) := by
  simp only [Game.score, probability_eq_expect, expectation_product]
  rw [show (table α).expectation (fun x => (table β).expectation
      (fun y => G.edgeLaw.expectation (fun e =>
        if decide (G.project e (x (G.left e)) = y (G.right e)) then 1 else 0))) =
      G.edgeLaw.expectation (fun e => (table α).expectation (fun x =>
        (table β).expectation (fun y =>
          if decide (G.project e (x (G.left e)) = y (G.right e)) then 1 else 0))) from by
      simp_rw [expectation_comm (table β) G.edgeLaw]
      exact expectation_comm (table α) G.edgeLaw _]
  apply expectation_congr
  intro e
  exact expectation_table_pair α β (G.left e) (G.right e)
    (fun x y => if decide (G.project e x = y) then 1 else 0)

theorem list_decoding (G : Game U V E X Y) (θ : ℝ) (hsound : G.Sound θ)
    (Ju : U → Finset X) (Jv : V → Finset Y) (J : ℕ) (hJ : 1 ≤ J)
    (hu : ∀ u, (Ju u).card ≤ J) (hv : ∀ v, (Jv v).card ≤ J) :
    G.edgeLaw.probability (fun e => decide (∃ x ∈ Ju (G.left e), G.project e x ∈ Jv (G.right e)))
      ≤ θ * (J : ℝ)^2 := by
  let α : U → FiniteDistribution X := fun u => listChoice (Ju u)
  let β : V → FiniteDistribution Y := fun v => listChoice (Jv v)
  have hscore : G.edgeLaw.expectation (fun e => ((α (G.left e)).product (β (G.right e))).probability
        (fun z => decide (G.project e z.1 = z.2))) ≤ θ := by
    rw [← randomized_score G α β]
    calc
      _ ≤ ((table α).product (table β)).expectation (fun _ => θ) :=
        expectation_mono _ (fun l => hsound l.1 l.2)
      _ = _ := expectation_const _ _
  have hJpos : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  rw [probability_eq_expect]
  calc
    _ ≤ G.edgeLaw.expectation (fun e => (J : ℝ)^2 *
      ((α (G.left e)).product (β (G.right e))).probability
        (fun z => decide (G.project e z.1 = z.2))) := by
      apply expectation_mono
      intro e
      by_cases hh : ∃ x ∈ Ju (G.left e), G.project e x ∈ Jv (G.right e)
      · simp only [hh, decide_true, ↓reduceIte]
        have h := listChoice_pair_success (G.project e) (Ju (G.left e)) (Jv (G.right e))
          J hJ (hu _) (hv _) hh
        exact (div_le_iff₀ (sq_pos_of_pos hJpos)).mp h |>.trans_eq (mul_comm _ _)
      · simp only [hh, decide_false, Bool.false_eq_true, ↓reduceIte]
        exact mul_nonneg (sq_nonneg _) (probability_nonnegative _ _)
    _ = (J : ℝ)^2 * G.edgeLaw.expectation (fun e =>
      ((α (G.left e)).product (β (G.right e))).probability
        (fun z => decide (G.project e z.1 = z.2))) := expectation_mul_left _ _ _
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hscore (sq_nonneg (J : ℝ))]

end DirectedFeedback.Games

noncomputable section
open scoped Classical BigOperators

noncomputable section
open scoped Classical BigOperators

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Construction
open DirectedFeedback.SourceProbability FiniteDistribution
open RankGraph Prefix PrefixExperiment Games
variable {U V E X Y : Type} [Fintype U] [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
variable {M T N : ℕ} [NeZero M] [NeZero T]

variable (G : Game U V E X Y) (ψLaw : FiniteDistribution (Emb (rankLength X T) N))

def OutputArc (hYX : Fintype.card Y ≤ Fintype.card X) (fiber : E → X ≃ Y × Bool) :=
  TestGraph.Arc (wildSupport (M := M) G ψLaw hYX) (compSupport (M := M) G ψLaw fiber)

theorem vertexCost_pos (D H K : ℝ) (hD : 0 ≤ D) (hH : 0 < H) (hK : 0 < K)
    (v : OutputVertex (M := M) G ψLaw) : 0 < vertexCost G ψLaw D H K v := by
  rcases v with r | (d | d)
  · dsimp [vertexCost]; linarith
  · rcases d with d | (d | d)
    · exact mul_pos hH d.property
    · exact mul_pos (by exact_mod_cast Fintype.card_pos) d.property
    · exact mul_pos (by exact_mod_cast Fintype.card_pos) d.property
  · exact mul_pos hK d.property

theorem rank_retained (D H K : ℝ) (hD : 0 ≤ D) (hH : 0 < H) (hK : 0 < K)
    (deleted : OutputVertex (M := M) G ψLaw → Bool)
    (hcost : totalDeletionCost G ψLaw D H K deleted ≤ D) (r : Rank U V X Y T N) :
    deleted (.inl r) = false := by
  by_contra h
  have ht : deleted (.inl r) = true := Bool.eq_true_of_not_eq_false h
  have hh := Finset.single_le_sum (fun v (_ : v ∈ (Finset.univ : Finset (OutputVertex (M := M) G ψLaw))) =>
    show (0:ℝ) ≤ (if deleted v then vertexCost G ψLaw D H K v else 0) from
      by split <;> [exact (vertexCost_pos G ψLaw D H K hD hH hK v).le; rfl])
    (Finset.mem_univ (Sum.inl r))
  change (if deleted (.inl r) then D+1 else 0) ≤ totalDeletionCost G ψLaw D H K deleted at hh
  rw [ht] at hh
  simp only [↓reduceIte] at hh
  linarith

end DirectedFeedback.Construction

noncomputable section
open scoped Classical
namespace DirectedFeedback.Prefix
variable {S X : Type*} {k : ℕ}

def normalizedCondition (g : Set S → Bool) (cell : S → Fin k)
    (h0 : g ∅ = false) (h1 : g Set.univ = true)
    (g' : Set (S × X) → Bool) (good : Prop) (fallback : X) (R : Set X) : Bool :=
  if good then g' (conditionedSet cell (transition g cell h0 h1) R)
  else decide (fallback ∈ R)

theorem normalized_eq (g : Set S → Bool) (cell : S → Fin k)
    (h0 : g ∅ = false) (h1 : g Set.univ = true)
    (g' : Set (S × X) → Bool) (good : Prop) (fallback : X) (hg : good) :
    normalizedCondition g cell h0 h1 g' good fallback =
      fun R => g' (conditionedSet cell (transition g cell h0 h1) R) := by
  funext R; simp [normalizedCondition, hg]

theorem normalized_properties (g : Set S → Bool) (cell : S → Fin k)
    (h0 : g ∅ = false) (h1 : g Set.univ = true)
    (g' : Set (S × X) → Bool) (good : Prop) (fallback : X)
    (hg' : good → Monotone g')
    (hlift : ∀ E, g' (Prod.fst ⁻¹' E) = g E) :
    Monotone (normalizedCondition g cell h0 h1 g' good fallback) ∧
    normalizedCondition g cell h0 h1 g' good fallback ∅ = false ∧
    normalizedCondition g cell h0 h1 g' good fallback Set.univ = true := by
  by_cases hg : good
  · rw [normalized_eq g cell h0 h1 g' good fallback hg]
    exact conditioned_properties g g' (hg' hg) cell _ (transition_spec g cell h0 h1) hlift
  · have he : normalizedCondition g cell h0 h1 g' good fallback =
        (fun R => decide (fallback ∈ R)) := by
      funext R; simp [normalizedCondition, hg]
    rw [he]
    refine ⟨?_, by simp, by simp⟩
    intro A B hAB
    rw [Bool.le_iff_imp]
    simpa using (fun h : fallback ∈ A => hAB h)

end DirectedFeedback.Prefix

namespace DirectedFeedback.RankGraph
open Prefix
variable {U V X Y : Type} {T N L k : ℕ}
variable (ord : Rank U V X Y T N → ℕ) (ψ : Fin L → Fin N)
variable (hL : 30 ≤ L) (hψ : StrictMono ψ)
variable (hord : ∀ {a b}, Arc a b → ord a < ord b)

def conditionedSmall (t : Fin T) (s : Fin t.val → U) (cell : (Fin t.val → X) → Fin k)
    (v : V) (fallback : Y) : Set Y → Bool :=
  normalizedCondition (referenceBit ord ψ hL (.inl ⟨⟨t.val, by omega⟩, s⟩)) cell
    (reference_empty hL hψ hord _) (reference_univ hL hψ hord _)
    (referenceBit ord ψ hL (.inr ⟨t, s, v⟩))
    (Good ord ψ hL (.inr ⟨t, s, v⟩)) fallback

theorem conditionedSmall_properties (t : Fin T) (s : Fin t.val → U)
    (cell : (Fin t.val → X) → Fin k) (v : V) (fallback : Y) :
    Monotone (conditionedSmall ord ψ hL hψ hord t s cell v fallback) ∧
      conditionedSmall ord ψ hL hψ hord t s cell v fallback ∅ = false ∧
      conditionedSmall ord ψ hL hψ hord t s cell v fallback Set.univ = true := by
  apply normalized_properties
  · exact good_monotone hL hψ hord _
  · intro E
    unfold referenceBit
    exact (compare_prefix_small (ord := ord) (ψ := ψ) t s v E _ _ _).symm

def bigStepBit (t : Fin T) (s : Fin t.val → U) (u : U)
    (E : Set ((Fin t.val → X) × X)) : Bool :=
  referenceBit ord ψ hL (.inl ⟨⟨t.val+1, by omega⟩, Fin.snoc s u⟩)
    (splitLast t.val ⁻¹' E)

theorem bigStepBit_lift (t : Fin T) (s : Fin t.val → U) (u : U)
    (E : Set (Fin t.val → X)) :
    bigStepBit ord ψ hL t s u (Prod.fst ⁻¹' E) =
      referenceBit ord ψ hL (.inl ⟨⟨t.val, by omega⟩, s⟩) E := by
  unfold bigStepBit referenceBit
  change compareBit ord ψ (.inl ⟨⟨t.val+1, by omega⟩, Fin.snoc s u⟩)
      (Fin.init ⁻¹' E) _ _ _ = _
  have hi := @Fin.init_snoc t.val (fun _ => U) u s
  have hh := compare_prefix_big (X := X) (Y := Y) (ord := ord) (ψ := ψ)
    t.val t.isLt (Fin.snoc s u) E ⟨1, by omega⟩ ⟨14, by omega⟩ ⟨L-2, by omega⟩
  rw [hi] at hh
  exact hh.symm

def conditionedBig (t : Fin T) (s : Fin t.val → U) (cell : (Fin t.val → X) → Fin k)
    (u : U) (fallback : X) : Set X → Bool :=
  normalizedCondition (referenceBit ord ψ hL (.inl ⟨⟨t.val, by omega⟩, s⟩)) cell
    (reference_empty hL hψ hord _) (reference_univ hL hψ hord _)
    (bigStepBit ord ψ hL t s u)
    (Good ord ψ hL (.inl ⟨⟨t.val+1, by omega⟩, Fin.snoc s u⟩)) fallback

theorem conditionedBig_properties (t : Fin T) (s : Fin t.val → U)
    (cell : (Fin t.val → X) → Fin k) (u : U) (fallback : X) :
    Monotone (conditionedBig ord ψ hL hψ hord t s cell u fallback) ∧
      conditionedBig ord ψ hL hψ hord t s cell u fallback ∅ = false ∧
      conditionedBig ord ψ hL hψ hord t s cell u fallback Set.univ = true := by
  apply normalized_properties
  · intro hg E E' hEE'
    apply good_monotone hL hψ hord _ hg
    exact Set.preimage_mono hEE'
  · exact bigStepBit_lift ord ψ hL t s u

end DirectedFeedback.RankGraph

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Prefix
variable {S : Type*} {k : ℕ}

theorem starred_transition_crosses (g : Set S → Bool) (hg : Monotone g)
    (cell : S → Fin k) (r : Fin k) (hr : Transition g cell r) (Z : Set S)
    (hz : ∀ a, cell a = r → a ∈ Z) :
    g (boundary cell r.val \ Z) = false ∧
      g ((boundary cell r.val \ Z) ∪ Z) = true := by
  constructor
  · have h := hg (Set.sdiff_subset : boundary cell r.val \ Z ⊆ boundary cell r.val)
    rw [hr.1] at h
    exact le_antisymm h (by simp)
  · have hsub : boundary cell (r.val+1) ⊆ (boundary cell r.val \ Z) ∪ Z := by
      intro a ha
      by_cases haz : a ∈ Z
      · exact Or.inr haz
      · left
        refine ⟨?_, haz⟩
        have hn : cell a ≠ r := fun he => haz (hz a he)
        have hnv : (cell a).val ≠ r.val := fun he => hn (Fin.ext he)
        change (cell a).val < r.val + 1 at ha
        change (cell a).val < r.val
        omega
    have h := hg hsub
    rw [hr.2] at h
    exact le_antisymm (by simp) h

theorem unstarred_transition_exists (g : Set S → Bool) (hg : Monotone g)
    (cell : S → Fin k) (r : Fin k) (hr : Transition g cell r) (Z : Set S)
    (hn : ¬(g (boundary cell r.val \ Z) = false ∧
      g ((boundary cell r.val \ Z) ∪ Z) = true)) :
    ∃ a, cell a = r ∧ a ∉ Z := by
  by_contra hh
  apply hn
  apply starred_transition_crosses g hg cell r hr Z
  intro a ha
  by_contra hz
  exact hh ⟨a, ha, hz⟩

end DirectedFeedback.Prefix

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Construction
open DirectedFeedback.SourceProbability FiniteDistribution
open RankGraph Prefix PrefixExperiment Games
variable {U V E X Y : Type} [Fintype U] [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
variable {M T N : ℕ} [NeZero M] [NeZero T]
variable (G : Game U V E X Y) (ψLaw : FiniteDistribution (Emb (rankLength X T) N))
variable (hYX : Fintype.card Y ≤ Fintype.card X) (fiber : E → X ≃ Y × Bool)
variable (deleted : OutputVertex (M := M) G ψLaw → Bool)
variable (ord : OutputVertex (M := M) G ψLaw → ℕ)
variable (hord : ∀ {a b}, deleted a = false → deleted b = false →
  OutputArc G ψLaw hYX fiber a b → ord a < ord b)
variable (hrank : ∀ r, deleted (.inl r) = false)

abbrev rankOrder : Rank U V X Y T N → ℕ := fun r => ord (.inl r)

include hord hrank in
theorem rankOrder_arc {a b : Rank U V X Y T N} (h : RankGraph.Arc a b) :
    rankOrder G ψLaw ord a < rankOrder G ψLaw ord b :=
  hord (hrank a) (hrank b) (.rank h)

omit [NeZero M] [NeZero T] [Nonempty X] in
theorem rankLength_ge : 30 ≤ rankLength X T := by unfold rankLength; omega

theorem full_unstarred (d : (fullLaw (M := M) G ψLaw).Support)
    (hkeep : deleted (.inr (.inl (.inl d))) = false)
    (hgood : Good (rankOrder G ψLaw ord) d.val.1.val rankLength_ge (fullWildcard (V := V) (Y := Y) d.val).tuple) :
    ∃ x : Fin T → X,
      cell d.val.2 x = transition
        (referenceBit (rankOrder G ψLaw ord) d.val.1.val rankLength_ge (fullWildcard (V := V) (Y := Y) d.val).tuple)
        (cell d.val.2)
        (reference_empty rankLength_ge d.val.1.property (rankOrder_arc G ψLaw hYX fiber deleted ord hord hrank) (fullWildcard (V := V) (Y := Y) d.val).tuple)
        (reference_univ rankLength_ge d.val.1.property (rankOrder_arc G ψLaw hYX fiber deleted ord hord hrank) (fullWildcard (V := V) (Y := Y) d.val).tuple) ∧
      x ∉ fullStars d.val.2 := by
  let g := referenceBit (rankOrder G ψLaw ord) d.val.1.val rankLength_ge (fullWildcard (V := V) (Y := Y) d.val).tuple
  have h0 : g ∅ = false := reference_empty rankLength_ge d.val.1.property
    (rankOrder_arc G ψLaw hYX fiber deleted ord hord hrank) _
  have h1 : g Set.univ = true := reference_univ rankLength_ge d.val.1.property
    (rankOrder_arc G ψLaw hYX fiber deleted ord hord hrank) _
  let r := transition g (cell d.val.2) h0 h1
  apply unstarred_transition_exists g (good_monotone rankLength_ge d.val.1.property
    (rankOrder_arc G ψLaw hYX fiber deleted ord hord hrank) _ hgood)
    (cell d.val.2) r (transition_spec g (cell d.val.2) h0 h1) (fullStars d.val.2)
  apply wildcard_forcing (K := maxCells X T) rfl full_cells_bound d.val.1.property
    (rankOrder G ψLaw ord) hgood (cell d.val.2) (fullStars d.val.2) r.val (Nat.le_of_lt r.isLt)
  intro x y hx hy
  exact TestGraph.wildcard_path (wildSupport G ψLaw hYX) (compSupport G ψLaw fiber)
    ord (fun v => deleted v = false) hord hrank (.inl d) hkeep x y hx hy

def bigFunction (fallback : X) (d : Common U X M T N) (u : U) : (X → Bool) → Bool :=
  fun b => conditionedBig (rankOrder G ψLaw ord) d.1.val rankLength_ge d.1.property
    (rankOrder_arc G ψLaw hYX fiber deleted ord hord hrank) d.2.1 (vertices d.2.2)
    (cell d.2.2) u fallback {x | b x = true}

def smallFunction (fallback : Y) (d : Common U X M T N) (v : V) : (Y → Bool) → Bool :=
  fun b => conditionedSmall (rankOrder G ψLaw ord) d.1.val rankLength_ge d.1.property
    (rankOrder_arc G ψLaw hYX fiber deleted ord hord hrank) d.2.1 (vertices d.2.2)
    (cell d.2.2) v fallback {y | b y = true}

def commonTransition (d : Common U X M T N) : Fin (cellCount d.2.1.val) :=
  transition (referenceBit (rankOrder G ψLaw ord) d.1.val rankLength_ge
    (.inl ⟨⟨d.2.1.val, by have := d.2.1.isLt; omega⟩, vertices d.2.2⟩)) (cell d.2.2)
    (reference_empty rankLength_ge d.1.property (rankOrder_arc G ψLaw hYX fiber deleted ord hord hrank) _)
    (reference_univ rankLength_ge d.1.property (rankOrder_arc G ψLaw hYX fiber deleted ord hord hrank) _)

theorem comparison_forces_deletion (d : ComparisonSupport (M := M) G ψLaw)
    (fallbackX : X) (fallbackY : Y)
    (hgoodU : Good (rankOrder G ψLaw ord) d.val.1.1.val rankLength_ge
      (.inl ⟨⟨d.val.1.2.1.val+1, by have := d.val.1.2.1.isLt; omega⟩,
        Fin.snoc (vertices d.val.1.2.2) (G.left d.val.2.1)⟩))
    (hgoodV : Good (rankOrder G ψLaw ord) d.val.1.1.val rankLength_ge
      (.inr ⟨d.val.1.2.1, vertices d.val.1.2.2, G.right d.val.2.1⟩))
    (hr : d.val.2.2.2.1 = commonTransition G ψLaw hYX fiber deleted ord hord hrank d.val.1)
    (hU : bigFunction G ψLaw hYX fiber deleted ord hord hrank fallbackX d.val.1 (G.left d.val.2.1)
      (Coupling.bigBits (fiber d.val.2.1) d.val.2.2.2.2) = true)
    (hV : smallFunction G ψLaw hYX fiber deleted ord hord hrank fallbackY d.val.1 (G.right d.val.2.1)
      (Coupling.smallBits d.val.2.2.2.2) = false) :
    deleted (.inr (.inr d)) = true := by
  by_contra h
  have hk : deleted (.inr (.inr d)) = false := Bool.eq_false_iff.mpr h
  have hp := TestGraph.comparison_path (wildSupport G ψLaw hYX) (compSupport G ψLaw fiber)
    ord (fun v => deleted v = false) hord hrank d hk
  apply comparison_forcing rankLength_ge (rankOrder G ψLaw ord) _ _ hgoodU hgoodV _ _ hp
  constructor
  · simpa only [bigFunction, conditionedBig, normalizedCondition, hgoodU, ↓reduceIte,
      bigStepBit, hr, commonTransition] using hU
  · simpa only [smallFunction, conditionedSmall, normalizedCondition, hgoodV, ↓reduceIte,
      hr, commonTransition] using hV

end DirectedFeedback.Construction

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Pivotal
open Prefix
variable {I S : Type} [Fintype I] [DecidableEq I] {k : ℕ}

theorem omitted_crossing (cell : S → Fin k) (r : Fin k)
    (g : Set (S × I) → Bool) (hg : Monotone g) (f : (I → Bool) → Bool)
    (hf : ∀ b, f b = g (conditionedSet cell r {i | b i = true}))
    (o : LabelOrder I) (hh : omittedHit o.1 (pivotalEvent f o.1) o.2 = true) :
    ∃ q ≤ Fintype.card {i : I // i ≠ o.1}+1,
      let E := boundary (orderedCell cell o.2)
        ((Fintype.card {i : I // i ≠ o.1}+1)*r.val+q) \ {a | a.2 = o.1}
      g E = false ∧ g (E ∪ {a | a.2 = o.1}) = true := by
  obtain ⟨q,hq,hp⟩ := of_decide_eq_true hh
  have hp' := of_decide_eq_true hp
  have hs0 : {i | insertBit o.1 false (fun x => decide ((o.2 x).val < q)) i = true} =
      {i | i ≠ o.1 ∧ (o.2 i).val < q} := by
    ext i
    by_cases hi : i = o.1
    · subst i; simp
    · simp [insertBit, hi]
  have hs1 : {i | insertBit o.1 true (fun x => decide ((o.2 x).val < q)) i = true} =
      {i | i ≠ o.1 ∧ (o.2 i).val < q} ∪ {o.1} := by
    ext i
    by_cases hi : i = o.1
    · subst i; simp
    · simp [insertBit, hi]
  rw [hf, hf, hs0, hs1] at hp'
  exact ⟨q,hq, single_label_crossing cell o.2 r q hq o.1 g hg hp'.1 hp'.2⟩

end DirectedFeedback.Pivotal

namespace DirectedFeedback.RankGraph
open Prefix Pivotal
variable {U V X Y S I : Type} [Fintype I] [DecidableEq I]
variable {T N L K k : ℕ} {d : Tuple U V T} {ψ : Fin L → Fin N}

theorem ordered_wildcard_forcing (hL : L = 10*K+30)
    (o : LabelOrder I) (hk : k*(Fintype.card {i : I // i ≠ o.1}+1) ≤ K)
    (hψ : StrictMono ψ) (ord : Rank U V X Y T N → ℕ)
    (hg : Good ord ψ (by omega) d)
    (e : Domain U V X Y T d ≃ S × I) (cell : S → Fin k) (r : Fin k)
    (f : (I → Bool) → Bool)
    (hf : ∀ b, f b = referenceBit ord ψ (by omega) d
      (e ⁻¹' conditionedSet cell r {i | b i = true}))
    (hm : Monotone (fun A : Set (S × I) => referenceBit ord ψ (by omega) d (e ⁻¹' A)))
    (hpath : ∀ x y, belowWildcard d (fun a => orderedCell cell o.2 (e a))
        {a | (e a).2 = o.1}
        (fun j => ψ ⟨10*j.val+19, by have := j.isLt; omega⟩) x →
      aboveWildcard d (fun a => orderedCell cell o.2 (e a)) {a | (e a).2 = o.1}
        (fun j => ψ ⟨10*j.val+19, by have := j.isLt; omega⟩) y →
      ord (vertex d x) < ord (vertex d y)) :
    omittedHit o.1 (pivotalEvent f o.1) o.2 = false := by
  apply Bool.eq_false_iff.mpr
  intro hh
  obtain ⟨q,hq,hcross⟩ := omitted_crossing cell r
    (fun A => referenceBit ord ψ (by omega) d (e ⁻¹' A)) hm f hf o hh
  have hcut : (Fintype.card {i : I // i ≠ o.1}+1)*r.val+q ≤
      k*(Fintype.card {i : I // i ≠ o.1}+1) := by
    have h := Nat.mul_le_mul_left (Fintype.card {i : I // i ≠ o.1}+1) r.isLt
    simp only [Nat.mul_succ] at h
    rw [Nat.mul_comm k]
    omega
  apply wildcard_forcing hL hk hψ ord hg
    (fun a => orderedCell cell o.2 (e a)) {a | (e a).2 = o.1}
    _ hcut hpath
  simpa only [boundary, Set.preimage_sdiff, Set.preimage_union, Set.preimage_ofPred_eq] using hcross

end DirectedFeedback.RankGraph

namespace DirectedFeedback.Construction
open DirectedFeedback.SourceProbability FiniteDistribution
open RankGraph Prefix PrefixExperiment Games Pivotal
variable {U V E X Y : Type} [Fintype U] [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
variable {M T N : ℕ} [NeZero M] [NeZero T]
variable (G : Game U V E X Y) (ψLaw : FiniteDistribution (Emb (rankLength X T) N))
variable (hYX : Fintype.card Y ≤ Fintype.card X) (fiber : E → X ≃ Y × Bool)
variable (deleted : OutputVertex (M := M) G ψLaw → Bool)
variable (ord : OutputVertex (M := M) G ψLaw → ℕ)
variable (hord : ∀ {a b}, deleted a = false → deleted b = false →
  OutputArc G ψLaw hYX fiber a b → ord a < ord b)
variable (hrank : ∀ r, deleted (.inl r) = false)

def bigGood (d : Common U X M T N) (u : U) : Prop :=
  Good (rankOrder G ψLaw ord) d.1.val rankLength_ge
    (.inl ⟨⟨d.2.1.val+1, by have := d.2.1.isLt; omega⟩, Fin.snoc (vertices d.2.2) u⟩)
def smallGood (d : Common U X M T N) (v : V) : Prop :=
  Good (rankOrder G ψLaw ord) d.1.val rankLength_ge
    (.inr ⟨d.2.1, vertices d.2.2, v⟩)

theorem small_forces_deletion (d : (smallLaw (M := M) G ψLaw).Support) (fallback : Y)
    (hgood : smallGood G ψLaw ord d.val.1 d.val.2.1)
    (hh : omittedHit d.val.2.2.1 (pivotalEvent
      (smallFunction G ψLaw hYX fiber deleted ord hord hrank fallback d.val.1 d.val.2.1)
      d.val.2.2.1) d.val.2.2.2 = true) :
    deleted (.inr (.inl (.inr (.inr d)))) = true := by
  by_contra h
  have hk : deleted (.inr (.inl (.inr (.inr d)))) = false := Bool.eq_false_iff.mpr h
  have hf := ordered_wildcard_forcing (K := maxCells X T) rfl d.val.2.2
    (ordered_cells_bound hYX d.val.1.2.1 d.val.2.2) d.val.1.1.property
    (rankOrder G ψLaw ord) hgood (Equiv.refl _) (cell d.val.1.2.2)
    (commonTransition G ψLaw hYX fiber deleted ord hord hrank d.val.1)
    (smallFunction G ψLaw hYX fiber deleted ord hord hrank fallback d.val.1 d.val.2.1)
    (by intro b; simp only [smallFunction, conditionedSmall, normalizedCondition,
                               smallGood] at *
        simp only [hgood, ↓reduceIte]; rfl)
    (by intro A B hAB
        exact good_monotone rankLength_ge d.val.1.1.property
          (rankOrder_arc G ψLaw hYX fiber deleted ord hord hrank) _ hgood hAB)
    (by intro x y hx hy
        exact TestGraph.wildcard_path (wildSupport G ψLaw hYX) (compSupport G ψLaw fiber)
          ord (fun v => deleted v = false) hord hrank (.inr (.inr d)) hk x y hx hy)
  exact Bool.noConfusion (hh.symm.trans hf)

theorem big_forces_deletion (d : (bigLaw (M := M) G ψLaw).Support) (fallback : X)
    (hgood : bigGood G ψLaw ord d.val.1 d.val.2.1)
    (hh : omittedHit d.val.2.2.1 (pivotalEvent
      (bigFunction G ψLaw hYX fiber deleted ord hord hrank fallback d.val.1 d.val.2.1)
      d.val.2.2.1) d.val.2.2.2 = true) :
    deleted (.inr (.inl (.inr (.inl d)))) = true := by
  by_contra h
  have hk : deleted (.inr (.inl (.inr (.inl d)))) = false := Bool.eq_false_iff.mpr h
  have hf := ordered_wildcard_forcing (K := maxCells X T) rfl d.val.2.2
    (ordered_cells_bound le_rfl d.val.1.2.1 d.val.2.2) d.val.1.1.property
    (rankOrder G ψLaw ord) hgood (splitLast d.val.1.2.1.val) (cell d.val.1.2.2)
    (commonTransition G ψLaw hYX fiber deleted ord hord hrank d.val.1)
    (bigFunction G ψLaw hYX fiber deleted ord hord hrank fallback d.val.1 d.val.2.1)
    (by intro b; simp only [bigFunction, conditionedBig, normalizedCondition,
                               bigGood] at *
        simp only [hgood, ↓reduceIte]; rfl)
    (by intro A B hAB
        exact good_monotone rankLength_ge d.val.1.1.property
          (rankOrder_arc G ψLaw hYX fiber deleted ord hord hrank) _ hgood
          (Set.preimage_mono hAB))
    (by intro x y hx hy
        exact TestGraph.wildcard_path (wildSupport G ψLaw hYX) (compSupport G ψLaw fiber)
          ord (fun v => deleted v = false) hord hrank (.inr (.inl d)) hk x y hx hy)
  exact Bool.noConfusion (hh.symm.trans hf)

end DirectedFeedback.Construction

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.SourceProbability.FiniteDistribution
variable {Ω : Type*} [Fintype Ω]

theorem expectation_mono_support (μ : FiniteDistribution Ω) {f g : Ω → ℝ}
    (h : ∀ x, 0 < μ.weight x → f x ≤ g x) : μ.expectation f ≤ μ.expectation g := by
  unfold expectation
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : 0 < μ.weight x
  · exact mul_le_mul_of_nonneg_left (h x hx) (μ.nonnegative x)
  · have hz : μ.weight x = 0 := le_antisymm (not_lt.mp hx) (μ.nonnegative x)
    simp [hz]

theorem probability_mono_support (μ : FiniteDistribution Ω) {f g : Ω → Bool}
    (h : ∀ x, 0 < μ.weight x → f x = true → g x = true) : μ.probability f ≤ μ.probability g := by
  simp only [probability_eq_expect]
  apply expectation_mono_support μ
  intro x hx
  cases hf : f x
  · cases g x <;> simp
  · simp [h x hx hf]

end DirectedFeedback.SourceProbability.FiniteDistribution

namespace DirectedFeedback.Pivotal
open DirectedFeedback.SourceProbability FiniteDistribution
variable {I Ω : Type*} [Fintype I] [DecidableEq I] [Nonempty I] [Fintype Ω]

theorem labelOrder_weight_pos (o : LabelOrder I) : 0 < labelOrderLaw.weight o := by
  simp only [labelOrderLaw, sigma, uniform]
  positivity

theorem averaged_budget_charge_support (μ : FiniteDistribution Ω) (f : Ω → (I → Bool) → Bool)
    (good : Ω → Bool) (deleted : Ω → LabelOrder I → Bool)
    (D ρ : ℝ) (hρ : Fintype.card I * ρ ≤ 1)
    (hbad : μ.probability (fun a => !(good a)) ≤ ρ)
    (hcost : Fintype.card I * μ.expectation (fun a => labelOrderLaw.probability (deleted a)) ≤ D)
    (hforce : ∀ a, 0 < μ.weight a → good a = true → ∀ o,
      omittedHit o.1 (pivotalEvent (f a) o.1) o.2 = true → deleted a o = true) :
    μ.expectation (fun a => budget (f a)) ≤ D+1 := by
  have hb (a : Ω) (ha : 0 < μ.weight a) : budget (f a) ≤
      Fintype.card I * labelOrderLaw.probability (deleted a) +
      Fintype.card I * (if !(good a) then 1 else 0 : ℝ) := by
    cases hg : good a
    · simp only [Bool.not_false, ↓reduceIte, mul_one]
      have hp := probability_nonnegative labelOrderLaw (deleted a)
      have hc : (0:ℝ) ≤ Fintype.card I := Nat.cast_nonneg _
      have h := budget_le_card (f a)
      nlinarith
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, mul_zero, add_zero]
      exact single_label_budget_charge (f a) (deleted a) (hforce a ha hg)
  have hm := expectation_mono_support μ hb
  rw [expectation_add, expectation_mul_left, expectation_mul_left, ← probability_eq_expect] at hm
  have hc : (0:ℝ) ≤ Fintype.card I := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hbad hc]

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
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_FailureEvent
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype _root_.OAI.DFVSGames.Reduction.ActualSource.sourceIndexNonempty _root_.OAI.DFVSGames.Soundness.ConditionalIncidences.zeroBits _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.CookLevin.NPTableau.codec_width_nonempty _root_.OAI.DirectedFeedback.RankPackets.shapeFintype _root_.OAI.DirectedFeedback.RawFamily.eNonempty _root_.OAI.DirectedFeedback.RawFamily.wNonempty _root_.OAI.DirectedFeedback.StackDSL.Code.labelFintype
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
namespace DirectedFeedback.Construction
open DirectedFeedback.SourceProbability FiniteDistribution
open RankGraph Prefix PrefixExperiment Games Pivotal
variable {U V E X Y : Type} [Fintype U] [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
variable {M T N : ℕ} [NeZero M] [NeZero T]
variable (G : Game U V E X Y) (ψLaw : FiniteDistribution (Emb (rankLength X T) N))
variable (hYX : Fintype.card Y ≤ Fintype.card X) (fiber : E → X ≃ Y × Bool)
variable (deleted : OutputVertex (M := M) G ψLaw → Bool)
variable (ord : OutputVertex (M := M) G ψLaw → ℕ)
variable (hord : ∀ {a b}, deleted a = false → deleted b = false →
  OutputArc G ψLaw hYX fiber a b → ord a < ord b)
variable (hrank : ∀ r, deleted (.inl r) = false)

theorem bigFunction_properties (fallback : X) (d : Common U X M T N) (u : U) :
    Monotone (bigFunction G ψLaw hYX fiber deleted ord hord hrank fallback d u) ∧
      bigFunction G ψLaw hYX fiber deleted ord hord hrank fallback d u (fun _ => false) = false ∧
      bigFunction G ψLaw hYX fiber deleted ord hord hrank fallback d u (fun _ => true) = true := by
  obtain ⟨hm,h0,h1⟩ := conditionedBig_properties (rankOrder G ψLaw ord) d.1.val rankLength_ge
    d.1.property (rankOrder_arc G ψLaw hYX fiber deleted ord hord hrank)
    d.2.1 (vertices d.2.2) (cell d.2.2) u fallback
  exact subset_function_properties _ hm h0 h1

theorem smallFunction_properties (fallback : Y) (d : Common U X M T N) (v : V) :
    Monotone (smallFunction G ψLaw hYX fiber deleted ord hord hrank fallback d v) ∧
      smallFunction G ψLaw hYX fiber deleted ord hord hrank fallback d v (fun _ => false) = false ∧
      smallFunction G ψLaw hYX fiber deleted ord hord hrank fallback d v (fun _ => true) = true := by
  obtain ⟨hm,h0,h1⟩ := conditionedSmall_properties (rankOrder G ψLaw ord) d.1.val rankLength_ge
    d.1.property (rankOrder_arc G ψLaw hYX fiber deleted ord hord hrank)
    d.2.1 (vertices d.2.2) (cell d.2.2) v fallback
  exact subset_function_properties _ hm h0 h1

theorem family_costs (D H K : ℝ) (hD : 0 ≤ D) (hH : 0 ≤ H) (hK : 0 ≤ K)
    (hcost : totalDeletionCost G ψLaw D H K deleted ≤ D) :
    H * (fullLaw G ψLaw).probability (fullDeleted G ψLaw deleted) ≤ D ∧
    Fintype.card X * (bigLaw G ψLaw).probability (bigDeleted G ψLaw deleted) ≤ D ∧
    Fintype.card Y * (smallLaw G ψLaw).probability (smallDeleted G ψLaw deleted) ≤ D ∧
    K * (comparisonLaw G ψLaw).probability (comparisonDeleted G ψLaw deleted) ≤ D := by
  rw [deletionCost_decomposition] at hcost
  have hr : 0 ≤ ∑ r : Rank U V X Y T N, if deleted (.inl r) then D+1 else 0 := by
    apply Finset.sum_nonneg
    intro r _
    split <;> linarith
  have hf := mul_nonneg hH (probability_nonnegative (fullLaw G ψLaw) (fullDeleted G ψLaw deleted))
  have hb := mul_nonneg (Nat.cast_nonneg (Fintype.card X) : (0:ℝ) ≤ Fintype.card X)
    (probability_nonnegative (bigLaw G ψLaw) (bigDeleted G ψLaw deleted))
  have hs := mul_nonneg (Nat.cast_nonneg (Fintype.card Y) : (0:ℝ) ≤ Fintype.card Y)
    (probability_nonnegative (smallLaw G ψLaw) (smallDeleted G ψLaw deleted))
  have hc := mul_nonneg hK (probability_nonnegative (comparisonLaw G ψLaw) (comparisonDeleted G ψLaw deleted))
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem big_budget (fallback : X) (D ρ : ℝ) (hρ : Fintype.card X * ρ ≤ 1)
    (hbad : ((common (M := M) G ψLaw).product (bigMarginal G)).probability
      (fun a => decide (¬bigGood G ψLaw ord a.1 a.2)) ≤ ρ)
    (hcost : Fintype.card X * (bigLaw G ψLaw).probability (bigDeleted G ψLaw deleted) ≤ D) :
    ((common (M := M) G ψLaw).product (bigMarginal G)).expectation
      (fun a => budget (bigFunction G ψLaw hYX fiber deleted ord hord hrank fallback a.1 a.2)) ≤ D+1 := by
  apply averaged_budget_charge_support _ _ (fun a => decide (bigGood G ψLaw ord a.1 a.2))
    (fun a o => bigDeleted G ψLaw deleted (a.1,(a.2,o))) D ρ hρ
  · simpa using hbad
  · simpa only [bigLaw, probability_eq_expect, expectation_product] using hcost
  · intro a ha hg o hh
    have hd : 0 < (bigLaw G ψLaw).weight (a.1,(a.2,o)) := by
      change 0 < (common G ψLaw).weight a.1 * ((bigMarginal G).weight a.2 * labelOrderLaw.weight o)
      rw [← mul_assoc]
      exact mul_pos ha (labelOrder_weight_pos o)
    change (bigLaw G ψLaw).extend _ _ = true
    rw [show (a.1,(a.2,o)) = (⟨(a.1,(a.2,o)),hd⟩ : (bigLaw G ψLaw).Support).val from rfl,
        extend_at_support]
    exact big_forces_deletion G ψLaw hYX fiber deleted ord hord hrank _ fallback
      (of_decide_eq_true hg) hh

theorem small_budget (fallback : Y) (D ρ : ℝ) (hρ : Fintype.card Y * ρ ≤ 1)
    (hbad : ((common (M := M) G ψLaw).product (smallMarginal G)).probability
      (fun a => decide (¬smallGood G ψLaw ord a.1 a.2)) ≤ ρ)
    (hcost : Fintype.card Y * (smallLaw G ψLaw).probability (smallDeleted G ψLaw deleted) ≤ D) :
    ((common (M := M) G ψLaw).product (smallMarginal G)).expectation
      (fun a => budget (smallFunction G ψLaw hYX fiber deleted ord hord hrank fallback a.1 a.2)) ≤ D+1 := by
  apply averaged_budget_charge_support _ _ (fun a => decide (smallGood G ψLaw ord a.1 a.2))
    (fun a o => smallDeleted G ψLaw deleted (a.1,(a.2,o))) D ρ hρ
  · simpa using hbad
  · simpa only [smallLaw, probability_eq_expect, expectation_product] using hcost
  · intro a ha hg o hh
    have hd : 0 < (smallLaw G ψLaw).weight (a.1,(a.2,o)) := by
      change 0 < (common G ψLaw).weight a.1 * ((smallMarginal G).weight a.2 * labelOrderLaw.weight o)
      rw [← mul_assoc]
      exact mul_pos ha (labelOrder_weight_pos o)
    change (smallLaw G ψLaw).extend _ _ = true
    rw [show (a.1,(a.2,o)) = (⟨(a.1,(a.2,o)),hd⟩ : (smallLaw G ψLaw).Support).val from rfl,
        extend_at_support]
    exact small_forces_deletion G ψLaw hYX fiber deleted ord hord hrank _ fallback
      (of_decide_eq_true hg) hh

end DirectedFeedback.Construction

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.SourceProbability.FiniteDistribution
variable {I Z : Type*} [Fintype I] [Nonempty I] [Fintype Z]

theorem uniform_single_le (f : I → ℝ) (hf : ∀ i, 0 ≤ f i) (i : I) :
    f i ≤ Fintype.card I * (uniform I).expectation f := by
  have hc : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have he : (Fintype.card I : ℝ) * (uniform I).expectation f = ∑ j, f j := by
    rw [expectation_uniform]
    field_simp
  rw [he]
  exact Finset.single_le_sum (fun j _ => hf j) (Finset.mem_univ i)

theorem fixed_choice_charge (μ : FiniteDistribution Z) (event : Z → Bool)
    (deleted : I → Z → Bool) (i : I)
    (hforce : ∀ z, 0 < μ.weight z → event z = true → deleted i z = true) :
    μ.probability event ≤ Fintype.card I * ((uniform I).product μ).probability
      (fun a => deleted a.1 a.2) := by
  have h := probability_mono_support μ hforce
  have he : ((uniform I).product μ).probability (fun a => deleted a.1 a.2) =
      (uniform I).expectation (fun i => μ.probability (deleted i)) := by
    simp only [probability_eq_expect, expectation_product]
  rw [he]
  exact h.trans (uniform_single_le _ (fun j => probability_nonnegative μ (deleted j)) i)

omit [Fintype I] [Nonempty I] in
theorem probability_good_restrict (μ : FiniteDistribution Z) (event : Z → Bool) (P Q : Prop) :
    μ.probability event ≤ μ.probability (fun z => decide (P ∧ Q) && event z) +
      (if ¬P then 1 else 0) + (if ¬Q then 1 else 0) := by
  have h := probability_le_one μ event
  rw [probability_eq_expect] at h
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP,hQ] <;> linarith

end DirectedFeedback.SourceProbability.FiniteDistribution

namespace DirectedFeedback.Construction
open DirectedFeedback.SourceProbability FiniteDistribution
open RankGraph Prefix PrefixExperiment Games
variable {U V E X Y : Type} [Fintype U] [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
variable {M T N : ℕ} [NeZero M] [NeZero T]
variable (G : Game U V E X Y) (ψLaw : FiniteDistribution (Emb (rankLength X T) N))
variable (hYX : Fintype.card Y ≤ Fintype.card X) (fiber : E → X ≃ Y × Bool)
variable (deleted : OutputVertex (M := M) G ψLaw → Bool)
variable (ord : OutputVertex (M := M) G ψLaw → ℕ)
variable (hord : ∀ {a b}, deleted a = false → deleted b = false →
  OutputArc G ψLaw hYX fiber a b → ord a < ord b)
variable (hrank : ∀ r, deleted (.inl r) = false)

def failureEvent (fallbackX : X) (fallbackY : Y) (a : Common U X M T N × E)
    (z : Y → Coupling.Block) : Bool :=
  bigFunction G ψLaw hYX fiber deleted ord hord hrank fallbackX a.1 (G.left a.2)
    (Coupling.bigBits (fiber a.2) z) &&
  !(smallFunction G ψLaw hYX fiber deleted ord hord hrank fallbackY a.1 (G.right a.2)
    (Coupling.smallBits z))

def scaleDeletion (i : Fin M) (a : Common U X M T N × E) : ℝ :=
  ((uniform (Fin (cellCount a.1.2.1.val))).product
    (Coupling.law (Y := Y) (bias i) (bias_pos i).le (by linarith [bias_le_quarter i]))).probability
    (fun q => comparisonDeleted G ψLaw deleted ⟨a.1,a.2,⟨i,q⟩⟩)

theorem scaleDeletion_nonneg (i : Fin M) (a : Common U X M T N × E) :
    0 ≤ scaleDeletion G ψLaw deleted i a := probability_nonnegative _ _

theorem comparison_probability_decomposition :
    (comparisonLaw G ψLaw).probability (comparisonDeleted G ψLaw deleted) =
      ((common (M := M) G ψLaw).product G.edgeLaw).expectation (fun a =>
        (uniform (Fin M)).expectation (fun i => scaleDeletion G ψLaw deleted i a)) := by
  simp only [comparisonLaw, scaleDeletion, probability_eq_expect, expectation_sigma, expectation_product]

theorem single_scale_cost (i : Fin M) :
    ((common (M := M) G ψLaw).product G.edgeLaw).expectation (scaleDeletion G ψLaw deleted i) ≤
      M * (comparisonLaw G ψLaw).probability (comparisonDeleted G ψLaw deleted) := by
  rw [comparison_probability_decomposition, ← expectation_mul_left]
  apply expectation_mono
  intro a
  simpa only [Fintype.card_fin] using uniform_single_le
    (fun j => scaleDeletion G ψLaw deleted j a) (fun j => scaleDeletion_nonneg G ψLaw deleted j a) i

theorem good_failure_charge (fallbackX : X) (fallbackY : Y) (i : Fin M)
    (a : Common U X M T N × E)
    (ha : 0 < ((common (M := M) G ψLaw).product G.edgeLaw).weight a) :
    (Coupling.law (Y := Y) (bias i) (bias_pos i).le (by linarith [bias_le_quarter i])).probability
      (fun z => decide (bigGood G ψLaw ord a.1 (G.left a.2) ∧
        smallGood G ψLaw ord a.1 (G.right a.2)) &&
        failureEvent G ψLaw hYX fiber deleted ord hord hrank fallbackX fallbackY a z) ≤
      (2:ℝ)^T * scaleDeletion G ψLaw deleted i a := by
  let ν := Coupling.law (Y := Y) (bias i) (bias_pos i).le (by linarith [bias_le_quarter i])
  have hf := fixed_choice_charge ν
    (fun z => decide (bigGood G ψLaw ord a.1 (G.left a.2) ∧ smallGood G ψLaw ord a.1 (G.right a.2)) &&
      failureEvent G ψLaw hYX fiber deleted ord hord hrank fallbackX fallbackY a z)
    (fun r z => comparisonDeleted G ψLaw deleted ⟨a.1,a.2,⟨i,r,z⟩⟩)
    (commonTransition G ψLaw hYX fiber deleted ord hord hrank a.1) (by
      intro z hz he
      let d : Compare U E X Y M T N := ⟨a.1,a.2,⟨i,commonTransition G ψLaw hYX fiber deleted ord hord hrank a.1,z⟩⟩
      have hp : 0 < (comparisonLaw G ψLaw).weight d := by
        have hp1 : 0 < (common G ψLaw).weight a.1 :=
          pos_of_mul_pos_left ha (G.edgeLaw.nonnegative a.2)
        have hp2 : 0 < G.edgeLaw.weight a.2 :=
          pos_of_mul_pos_right ha ((common G ψLaw).nonnegative a.1)
        simp only [d, comparisonLaw, sigma, product, uniform, Fintype.card_fin]
        change 0 < (common G ψLaw).weight a.1 * (G.edgeLaw.weight a.2 *
          (1/(M:ℝ) * (1/(cellCount a.1.2.1.val : ℝ) * ν.weight z)))
        have hM : (0:ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
        have hcell : (0:ℝ) < cellCount a.1.2.1.val := by
          exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (cellCount a.1.2.1.val))
        exact mul_pos hp1 (mul_pos hp2 (mul_pos (div_pos zero_lt_one hM)
          (mul_pos (div_pos zero_lt_one hcell) hz)))
      have he' : decide (bigGood G ψLaw ord a.1 (G.left a.2) ∧
          smallGood G ψLaw ord a.1 (G.right a.2)) = true ∧
          failureEvent G ψLaw hYX fiber deleted ord hord hrank fallbackX fallbackY a z = true := by
        simpa only [Bool.and_eq_true] using he
      obtain ⟨hg,he⟩ := he'
      obtain ⟨hgU,hgV⟩ := of_decide_eq_true hg
      have he' : bigFunction G ψLaw hYX fiber deleted ord hord hrank fallbackX a.1 (G.left a.2)
          (Coupling.bigBits (fiber a.2) z) = true ∧
          smallFunction G ψLaw hYX fiber deleted ord hord hrank fallbackY a.1 (G.right a.2)
          (Coupling.smallBits z) = false := by
        simpa only [failureEvent, Bool.and_eq_true, Bool.not_eq_true'] using he
      obtain ⟨hu,hv⟩ := he'
      have hh := comparison_forces_deletion G ψLaw hYX fiber deleted ord hord hrank ⟨d,hp⟩
        fallbackX fallbackY hgU hgV rfl hu (by simpa using hv)
      change (comparisonLaw G ψLaw).extend _ d = true
      rw [show d = (⟨d,hp⟩ : (comparisonLaw G ψLaw).Support).val from rfl, extend_at_support]
      exact hh)
  change _ ≤ (2:ℝ)^T * scaleDeletion G ψLaw deleted i a
  apply hf.trans
  change (Fintype.card (Fin (cellCount a.1.2.1.val)) : ℝ) * scaleDeletion G ψLaw deleted i a ≤ _
  apply mul_le_mul_of_nonneg_right _ (scaleDeletion_nonneg G ψLaw deleted i a)
  simp only [Fintype.card_fin, cellCount_eq, Nat.cast_pow, Nat.cast_ofNat]
  exact pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (Nat.le_of_lt a.1.2.1.isLt)

theorem comparison_charge (fallbackX : X) (fallbackY : Y) (i : Fin M)
    (D K ρ : ℝ) (hK : 0 < K)
    (hcost : K * (comparisonLaw G ψLaw).probability (comparisonDeleted G ψLaw deleted) ≤ D)
    (hbU : ((common (M := M) G ψLaw).product G.edgeLaw).probability (fun a =>
      decide (¬bigGood G ψLaw ord a.1 (G.left a.2))) ≤ ρ)
    (hbV : ((common (M := M) G ψLaw).product G.edgeLaw).probability (fun a =>
      decide (¬smallGood G ψLaw ord a.1 (G.right a.2))) ≤ ρ) :
    ((common (M := M) G ψLaw).product G.edgeLaw).expectation (fun a =>
      (Coupling.law (Y := Y) (bias i) (bias_pos i).le (by linarith [bias_le_quarter i])).probability
        (failureEvent G ψLaw hYX fiber deleted ord hord hrank fallbackX fallbackY a)) ≤
      2*ρ + M*(2:ℝ)^T*D/K := by
  let μ := (common (M := M) G ψLaw).product G.edgeLaw
  have hh := expectation_mono_support μ (f := fun a =>
      (Coupling.law (Y := Y) (bias i) (bias_pos i).le (by linarith [bias_le_quarter i])).probability
        (failureEvent G ψLaw hYX fiber deleted ord hord hrank fallbackX fallbackY a))
    (g := fun a => (2:ℝ)^T * scaleDeletion G ψLaw deleted i a +
      (if ¬bigGood G ψLaw ord a.1 (G.left a.2) then 1 else 0) +
      (if ¬smallGood G ψLaw ord a.1 (G.right a.2) then 1 else 0)) (by
      intro a ha
      have hp := probability_good_restrict
        (Coupling.law (Y := Y) (bias i) (bias_pos i).le (by linarith [bias_le_quarter i]))
        (failureEvent G ψLaw hYX fiber deleted ord hord hrank fallbackX fallbackY a)
        (bigGood G ψLaw ord a.1 (G.left a.2)) (smallGood G ψLaw ord a.1 (G.right a.2))
      have hc := good_failure_charge G ψLaw hYX fiber deleted ord hord hrank fallbackX fallbackY i a ha
      linarith)
  rw [expectation_add, expectation_add, expectation_mul_left] at hh
  have hbi : μ.expectation (fun a => if ¬bigGood G ψLaw ord a.1 (G.left a.2) then 1 else 0) ≤ ρ := by
    simpa only [probability_eq_expect, decide_eq_true_eq] using hbU
  have hsi : μ.expectation (fun a => if ¬smallGood G ψLaw ord a.1 (G.right a.2) then 1 else 0) ≤ ρ := by
    simpa only [probability_eq_expect, decide_eq_true_eq] using hbV
  have hc : (comparisonLaw G ψLaw).probability (comparisonDeleted G ψLaw deleted) ≤ D/K :=
    (le_div_iff₀ hK).mpr (by simpa [mul_comm] using hcost)
  have hs := (single_scale_cost G ψLaw deleted i).trans
    (mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg M))
  have hmul := mul_le_mul_of_nonneg_left hs (show 0 ≤ (2:ℝ)^T by positivity)
  change _ ≤ _ at hh
  have he : (2:ℝ)^T * ((M:ℝ) * (D/K)) = M*(2:ℝ)^T*D/K := by ring
  rw [he] at hmul
  linarith

end DirectedFeedback.Construction

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
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_RoundBoolean
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype _root_.OAI.DFVSGames.Soundness.ConditionalIncidences.zeroBits _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.RankPackets.shapeFintype _root_.OAI.DirectedFeedback.StackDSL.Code.labelFintype
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
namespace DirectedFeedback.Pivotal
open DirectedFeedback.SourceProbability FiniteDistribution

theorem family_dyadic_junta {M Jmax : ℕ} {B γ : ℝ}
    (hJ : DyadicJuntaBound M B γ Jmax) (k : Fin (M+2))
    {Ω U I : Type} [Fintype I] [DecidableEq I]
    (f : Ω → U → (I → Bool) → Bool) (hf : ∀ ω u, Monotone (f ω u)) :
    ∃ (S : Ω → U → Finset I) (g : Ω → U → (I → Bool) → Bool),
      (∀ ω u, (S ω u).card ≤ Jmax) ∧
      (∀ ω u x y, (∀ i ∈ S ω u, x i = y i) → g ω u x = g ω u y) ∧
      (∀ ω u, budget (f ω u) ≤ B →
        (law ((2:ℝ)⁻¹^k.val) (by positivity)
          (pow_le_one₀ (by norm_num) (by norm_num))).probability
            (fun x => decide (f ω u x ≠ g ω u x)) ≤ γ) := by
  have hex (ω : Ω) (u : U) : ∃ S : Finset I, S.card ≤ Jmax ∧
      ∃ g : (I → Bool) → Bool,
        (∀ x y, (∀ i ∈ S, x i = y i) → g x = g y) ∧
        (budget (f ω u) ≤ B →
          (law ((2:ℝ)⁻¹^k.val) (by positivity)
            (pow_le_one₀ (by norm_num) (by norm_num))).probability
              (fun x => decide (f ω u x ≠ g x)) ≤ γ) := by
    by_cases hb : budget (f ω u) ≤ B
    · obtain ⟨S,hS,g,hg,herr⟩ := hJ k I (f ω u) (hf ω u) hb
      exact ⟨S,hS,g,hg,fun _ => herr⟩
    · exact ⟨∅,by simp,fun _ => false,by simp,fun h => (hb h).elim⟩
  choose S hS g hg herr using hex
  exact ⟨S,g,hS,hg,herr⟩

end DirectedFeedback.Pivotal

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Coupling
open DirectedFeedback.SourceProbability FiniteDistribution
variable {X Y : Type*} [Fintype X] [Fintype Y]

theorem comparison_juntas (e : X ≃ Y × Bool) (p : ℝ) (hp0 : 0 ≤ p) (hp : p ≤ 1/2)
    (J : Finset X) (K : Finset Y) (hJK : Disjoint (J.image (fun x => (e x).1)) K)
    (f f' : (X → Bool) → Bool) (g g' : (Y → Bool) → Bool)
    (hf' : Uses J f') (hg' : Uses K g') (γ : ℝ)
    (hf : (Pivotal.law p hp0 (by linarith)).probability (fun x => decide (f x ≠ f' x)) ≤ γ)
    (hg : (Pivotal.law (2*p) (by positivity) (by linarith)).probability (fun y => decide (g y ≠ g' y)) ≤ γ) :
    |(Pivotal.law p hp0 (by linarith)).probability f *
      (1 - (Pivotal.law (2*p) (by positivity) (by linarith)).probability g) -
      (law p hp0 hp).probability (fun z => f (bigBits e z) && !(g (smallBits z)))| ≤ 4*γ := by
  let μ := Pivotal.law (I := X) p hp0 (by linarith)
  let ν := Pivotal.law (I := Y) (2*p) (by positivity) (by linarith)
  let ρ := law (Y := Y) p hp0 hp
  have hprod : |μ.probability f * (1-ν.probability g) -
      μ.probability f' * (1-ν.probability g')| ≤ 2*γ := by
    have h := product_pattern_lipschitz (probability_nonnegative ν g)
      (probability_nonnegative μ f') (probability_le_one μ f') (probability_le_one ν g)
      ((probability_abs_sub_le_disagree μ f f').trans hf)
      ((probability_abs_sub_le_disagree ν g g').trans hg)
    linarith
  have hc := pair_event_disagree ρ (fun z => f (bigBits e z)) (fun z => f' (bigBits e z))
    (fun z => !(g (smallBits z))) (fun z => !(g' (smallBits z)))
  have hnot : (fun z : Y → Block => decide ((!g (smallBits z)) ≠ (!g' (smallBits z)))) =
      fun z => decide (g (smallBits z) ≠ g' (smallBits z)) := by
    funext z; simp
  rw [hnot] at hc
  change |_ - _| ≤ (law p hp0 hp).probability (fun z => (fun x => decide (f x ≠ f' x)) (bigBits e z)) +
    (law p hp0 hp).probability (fun z => (fun y => decide (g y ≠ g' y)) (smallBits z)) at hc
  rw [big_probability e p hp0 hp (fun x => decide (f x ≠ f' x)),
    small_probability p hp0 hp (fun y => decide (g y ≠ g' y))] at hc
  have hcc : |ρ.probability (fun z => f (bigBits e z) && !(g (smallBits z))) -
      ρ.probability (fun z => f' (bigBits e z) && !(g' (smallBits z)))| ≤ 2*γ := by
    linarith
  have heq := disjoint_pattern e p hp0 hp J K hJK f' g' hf' hg'
  change ρ.probability (fun z => f' (bigBits e z) && !(g' (smallBits z))) =
    μ.probability f' * (1 - ν.probability g') at heq
  change |μ.probability f * (1-ν.probability g) -
      ρ.probability (fun z => f (bigBits e z) && !(g (smallBits z)))| ≤ _
  calc
    _ ≤ |μ.probability f * (1-ν.probability g) - μ.probability f' * (1-ν.probability g')| +
      |μ.probability f' * (1-ν.probability g') -
        ρ.probability (fun z => f (bigBits e z) && !(g (smallBits z)))| := abs_sub_le _ _ _
    _ ≤ 4*γ := by
      have hc' : |μ.probability f' * (1-ν.probability g') -
          ρ.probability (fun z => f (bigBits e z) && !(g (smallBits z)))| ≤ 2*γ := by
        rw [← heq, abs_sub_comm]
        exact hcc
      linarith

end DirectedFeedback.Coupling

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Soundness
open DirectedFeedback.SourceProbability FiniteDistribution
open Games
variable {Ω U V E X Y : Type} [Fintype Ω] [Fintype U] [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]

theorem averaged_comparison (μ : FiniteDistribution Ω) (G : Game U V E X Y)
    (θ : ℝ) (hsound : G.Sound θ) (fiber : E → X ≃ Y × Bool)
    (hproj : ∀ e x, (fiber e x).1 = G.project e x)
    (p γ C : ℝ) (hp0 : 0 ≤ p) (hp : p ≤ 1/2) (hγ : 0 < γ) (hC : 0 < C)
    (f : Ω → U → (X → Bool) → Bool) (g : Ω → V → (Y → Bool) → Bool)
    (Bu : Ω → U → ℝ) (Bv : Ω → V → ℝ)
    (hBu0 : ∀ ω u, 0 ≤ Bu ω u) (hBv0 : ∀ ω v, 0 ≤ Bv ω v)
    (hBu : (μ.product G.edgeLaw).expectation (fun a => Bu a.1 (G.left a.2)) ≤ C)
    (hBv : (μ.product G.edgeLaw).expectation (fun a => Bv a.1 (G.right a.2)) ≤ C)
    (J : ℕ) (hJ : 1 ≤ J) (Ju : Ω → U → Finset X) (Jv : Ω → V → Finset Y)
    (f' : Ω → U → (X → Bool) → Bool) (g' : Ω → V → (Y → Bool) → Bool)
    (hJu : ∀ ω u, (Ju ω u).card ≤ J) (hJv : ∀ ω v, (Jv ω v).card ≤ J)
    (hf' : ∀ ω u, Uses (Ju ω u) (f' ω u)) (hg' : ∀ ω v, Uses (Jv ω v) (g' ω v))
    (hf : ∀ ω u, Bu ω u ≤ C/γ →
      (Pivotal.law p hp0 (by linarith)).probability (fun x => decide (f ω u x ≠ f' ω u x)) ≤ γ)
    (hg : ∀ ω v, Bv ω v ≤ C/γ →
      (Pivotal.law (2*p) (by positivity) (by linarith)).probability
        (fun y => decide (g ω v y ≠ g' ω v y)) ≤ γ) :
    (μ.product G.edgeLaw).expectation (fun a =>
      (Pivotal.law p hp0 (by linarith)).probability (f a.1 (G.left a.2)) *
        (1 - (Pivotal.law (2*p) (by positivity) (by linarith)).probability (g a.1 (G.right a.2)))) ≤
    (μ.product G.edgeLaw).expectation (fun a =>
      (Coupling.law p hp0 hp).probability (fun z =>
        f a.1 (G.left a.2) (Coupling.bigBits (fiber a.2) z) &&
          !(g a.1 (G.right a.2) (Coupling.smallBits z)))) + 2*γ + θ*(J:ℝ)^2 + 4*γ := by
  let μc := μ.product G.edgeLaw
  let bU : Ω × E → Bool := fun a => decide (C/γ < Bu a.1 (G.left a.2))
  let bV : Ω × E → Bool := fun a => decide (C/γ < Bv a.1 (G.right a.2))
  let meet : Ω × E → Bool := fun a =>
    decide (∃ x ∈ Ju a.1 (G.left a.2), G.project a.2 x ∈ Jv a.1 (G.right a.2))
  have hU : μc.probability bU ≤ γ := by
    have hh := markov_bound μc (fun a => Bu a.1 (G.left a.2)) (fun a => hBu0 _ _)
      (C/γ) (div_pos hC hγ)
    have he : C / (C/γ) = γ := by field_simp
    exact hh.trans ((div_le_div_of_nonneg_right hBu (by positivity)).trans_eq he)
  have hV : μc.probability bV ≤ γ := by
    have hh := markov_bound μc (fun a => Bv a.1 (G.right a.2)) (fun a => hBv0 _ _)
      (C/γ) (div_pos hC hγ)
    have he : C / (C/γ) = γ := by field_simp
    exact hh.trans ((div_le_div_of_nonneg_right hBv (by positivity)).trans_eq he)
  have hmeet : μc.probability meet ≤ θ*(J:ℝ)^2 := by
    rw [probability_eq_expect, expectation_product]
    simp_rw [← probability_eq_expect]
    change μ.expectation (fun ω => G.edgeLaw.probability (fun e =>
      decide (∃ x ∈ Ju ω (G.left e), G.project e x ∈ Jv ω (G.right e)))) ≤ _
    calc
      _ ≤ μ.expectation (fun _ => θ*(J:ℝ)^2) := expectation_mono _
        (fun ω => list_decoding G θ hsound (Ju ω) (Jv ω) J hJ (hJu ω) (hJv ω))
      _ = _ := expectation_const _ _
  let A : Ω × E → ℝ := fun a =>
    (Pivotal.law p hp0 (by linarith)).probability (f a.1 (G.left a.2)) *
      (1 - (Pivotal.law (2*p) (by positivity) (by linarith)).probability (g a.1 (G.right a.2)))
  let B : Ω × E → ℝ := fun a =>
    (Coupling.law p hp0 hp).probability (fun z => f a.1 (G.left a.2) (Coupling.bigBits (fiber a.2) z) &&
      !(g a.1 (G.right a.2) (Coupling.smallBits z)))
  have hA1 (a : Ω × E) : A a ≤ 1 := by
    have h0 := probability_nonnegative (Pivotal.law (I := Y) (2*p) (by positivity) (by linarith))
      (g a.1 (G.right a.2))
    have h1 := probability_le_one (Pivotal.law (I := Y) (2*p) (by positivity) (by linarith))
      (g a.1 (G.right a.2))
    have hh := probability_le_one (Pivotal.law (I := X) p hp0 (by linarith)) (f a.1 (G.left a.2))
    exact (mul_le_mul_of_nonneg_right hh (by linarith)).trans (by simpa using h0)
  have hB0 (a : Ω × E) : 0 ≤ B a := probability_nonnegative _ _
  have hpoint (a : Ω × E) : A a ≤ B a + 4*γ +
      (if bU a then 1 else 0) + (if bV a then 1 else 0) + (if meet a then 1 else 0) := by
    by_cases hu : Bu a.1 (G.left a.2) ≤ C/γ
    · by_cases hv : Bv a.1 (G.right a.2) ≤ C/γ
      · by_cases hm : ∃ x ∈ Ju a.1 (G.left a.2), G.project a.2 x ∈ Jv a.1 (G.right a.2)
        · simp only [bU, bV, meet, not_lt.mpr hu, not_lt.mpr hv, hm, decide_false, decide_true,
            Bool.false_eq_true, ↓reduceIte, add_zero]
          linarith [hA1 a, hB0 a]
        · have hd : Disjoint ((Ju a.1 (G.left a.2)).image (fun x => (fiber a.2 x).1))
              (Jv a.1 (G.right a.2)) := by
            rw [Finset.disjoint_left]
            intro y hy hy'
            obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
            exact hm ⟨x,hx, by simpa [hproj] using hy'⟩
          have hh := Coupling.comparison_juntas (fiber a.2) p hp0 hp _ _ hd _ _ _ _
            (hf' _ _) (hg' _ _) γ (hf _ _ hu) (hg _ _ hv)
          have hh' : A a - B a ≤ 4*γ := (le_abs_self _).trans hh
          simpa only [bU, bV, meet, not_lt.mpr hu, not_lt.mpr hv, hm, decide_false,
            Bool.false_eq_true, ↓reduceIte, add_zero] using (show A a ≤ B a + 4*γ by linarith)
      · have hv' := lt_of_not_ge hv
        simp only [bU, bV, not_lt.mpr hu, hv', decide_false, decide_true,
          Bool.false_eq_true, ↓reduceIte, add_zero]
        split_ifs <;> linarith [hA1 a, hB0 a]
    · have hu' := lt_of_not_ge hu
      simp only [bU, hu', decide_true, ↓reduceIte]
      split_ifs <;> linarith [hA1 a, hB0 a]
  have hh := expectation_mono μc hpoint
  simp only [expectation_add, expectation_const, ← probability_eq_expect] at hh
  change μc.expectation A ≤ μc.expectation B + 2*γ + θ*(J:ℝ)^2 + 4*γ
  linarith

end DirectedFeedback.Soundness

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Construction
open DirectedFeedback.SourceProbability FiniteDistribution
open RankGraph Prefix PrefixExperiment Games Pivotal
variable {U V E X Y : Type} [Fintype U] [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
variable {M T N : ℕ} [NeZero M] [NeZero T]

omit [NeZero M] in
theorem double_bias (i : Fin M) : 2*bias i = (2:ℝ)⁻¹^(i.val+1) := by
  unfold bias
  rw [show i.val+2 = (i.val+1)+1 by omega, pow_succ]
  ring

variable (G : Game U V E X Y) (ψLaw : FiniteDistribution (Emb (rankLength X T) N))
variable (hYX : Fintype.card Y ≤ Fintype.card X) (fiber : E → X ≃ Y × Bool)
variable (deleted : OutputVertex (M := M) G ψLaw → Bool)
variable (ord : OutputVertex (M := M) G ψLaw → ℕ)
variable (hord : ∀ {a b}, deleted a = false → deleted b = false →
  OutputArc G ψLaw hYX fiber a b → ord a < ord b)
variable (hrank : ∀ r, deleted (.inl r) = false)

def bigAcceptance (fallback : X) (i : Fin M) (a : Common U X M T N × E) : ℝ :=
  (subsetLaw i).probability (bigFunction G ψLaw hYX fiber deleted ord hord hrank fallback a.1 (G.left a.2))

def smallAcceptance (fallback : Y) (i : Fin M) (a : Common U X M T N × E) : ℝ :=
  (Pivotal.law (2*bias i) (mul_nonneg (by norm_num) (bias_pos i).le) (by linarith [bias_le_quarter i])).probability
    (smallFunction G ψLaw hYX fiber deleted ord hord hrank fallback a.1 (G.right a.2))

def bigBudget (fallback : X) (a : Common U X M T N × E) : ℝ :=
  budget (bigFunction G ψLaw hYX fiber deleted ord hord hrank fallback a.1 (G.left a.2))

def smallBudget (fallback : Y) (a : Common U X M T N × E) : ℝ :=
  budget (smallFunction G ψLaw hYX fiber deleted ord hord hrank fallback a.1 (G.right a.2))

theorem independent_comparison (fallbackX : X) (fallbackY : Y) (i : Fin M)
    (D K ρ γ θ : ℝ) (hD : 0 ≤ D) (hK : 0 < K) (hγ : 0 < γ)
    (hsound : G.Sound θ) (hproj : ∀ e x, (fiber e x).1 = G.project e x)
    (J : ℕ) (hJ : 1 ≤ J) (hJunta : DyadicJuntaBound M ((D+1)/γ) γ J)
    (hBu : ((common (M := M) G ψLaw).product G.edgeLaw).expectation
      (bigBudget G ψLaw hYX fiber deleted ord hord hrank fallbackX) ≤ D+1)
    (hBv : ((common (M := M) G ψLaw).product G.edgeLaw).expectation
      (smallBudget G ψLaw hYX fiber deleted ord hord hrank fallbackY) ≤ D+1)
    (hcost : K * (comparisonLaw G ψLaw).probability (comparisonDeleted G ψLaw deleted) ≤ D)
    (hbU : ((common (M := M) G ψLaw).product G.edgeLaw).probability (fun a =>
      decide (¬bigGood G ψLaw ord a.1 (G.left a.2))) ≤ ρ)
    (hbV : ((common (M := M) G ψLaw).product G.edgeLaw).probability (fun a =>
      decide (¬smallGood G ψLaw ord a.1 (G.right a.2))) ≤ ρ) :
    ((common (M := M) G ψLaw).product G.edgeLaw).expectation (fun a =>
      bigAcceptance G ψLaw hYX fiber deleted ord hord hrank fallbackX i a *
        (1-smallAcceptance G ψLaw hYX fiber deleted ord hord hrank fallbackY i a)) ≤
      2*ρ + M*(2:ℝ)^T*D/K + 6*γ + θ*(J:ℝ)^2 := by
  let f := bigFunction G ψLaw hYX fiber deleted ord hord hrank fallbackX
  let g := smallFunction G ψLaw hYX fiber deleted ord hord hrank fallbackY
  have hfm : ∀ d u, Monotone (f d u) := fun d u =>
    (bigFunction_properties G ψLaw hYX fiber deleted ord hord hrank fallbackX d u).1
  have hgm : ∀ d v, Monotone (g d v) := fun d v =>
    (smallFunction_properties G ψLaw hYX fiber deleted ord hord hrank fallbackY d v).1
  obtain ⟨Ju,fu,hJu,hfu,hEu⟩ := family_dyadic_junta hJunta
    ⟨i.val+2,by have := i.isLt; omega⟩ f hfm
  obtain ⟨Jv,gv,hJv,hgv,hEv⟩ := family_dyadic_junta hJunta
    ⟨i.val+1,by have := i.isLt; omega⟩ g hgm
  have hh := Soundness.averaged_comparison (common G ψLaw) G θ hsound fiber hproj
    (bias i) γ (D+1) (bias_pos i).le (by linarith [bias_le_quarter i]) hγ (by linarith)
    f g (fun d u => budget (f d u)) (fun d v => budget (g d v))
    (fun d u => budget_nonneg _) (fun d v => budget_nonneg _) hBu hBv
    J hJ Ju Jv fu gv hJu hJv hfu hgv hEu (by
      intro d v hv
      simpa only [double_bias] using hEv d v hv)
  have hc := comparison_charge G ψLaw hYX fiber deleted ord hord hrank
    fallbackX fallbackY i D K ρ hK hcost hbU hbV
  change _ ≤ _ at hh
  change _ ≤ _ at hc
  have he : ((common (M := M) G ψLaw).product G.edgeLaw).expectation (fun a =>
      bigAcceptance G ψLaw hYX fiber deleted ord hord hrank fallbackX i a *
        (1-smallAcceptance G ψLaw hYX fiber deleted ord hord hrank fallbackY i a)) ≤
      ((common (M := M) G ψLaw).product G.edgeLaw).expectation (fun a =>
        (Coupling.law (Y := Y) (bias i) (bias_pos i).le (by linarith [bias_le_quarter i])).probability
          (failureEvent G ψLaw hYX fiber deleted ord hord hrank fallbackX fallbackY a)) +
        2*γ + θ*(J:ℝ)^2 + 4*γ := hh
  linarith

end DirectedFeedback.Construction

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Prefix

theorem prefixCell_congr {X : Type} (t : ℕ) (P Q : ℕ → Set X)
    (h : ∀ j < t, P j = Q j) : prefixCell t P = prefixCell t Q := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext a
    dsimp only [prefixCell]
    rw [ih (fun j hj => h j (by omega)), h t (by omega)]

end DirectedFeedback.Prefix

namespace DirectedFeedback.RankGraph
open DirectedFeedback.SourceProbability.FiniteDistribution Prefix
variable {U V X Y : Type} {T N L : ℕ}

theorem good_take_prefix (ord : Rank U V X Y T N → ℕ) (ψ : Fin L → Fin N)
    (hL : 30 ≤ L) (n : ℕ) (hn : n ≤ T) (s : Fin n → U)
    (hg : Good ord ψ hL (.inl ⟨⟨n,by omega⟩,s⟩)) (t : ℕ) (ht : t ≤ n) :
    Good ord ψ hL (.inl ⟨⟨t,by omega⟩,takePrefix ht s⟩) := by
  induction n with
  | zero => have he : t = 0 := by omega
            subst t
            exact hg
  | succ n ih =>
    by_cases ht' : t ≤ n
    · have hp := good_prefix_big (ord := ord) (ψ := ψ) hL n (by omega) s hg
      exact ih (by omega) (Fin.init s) hp ht'
    · have he : t = n+1 := by omega
      subst t
      exact hg

end DirectedFeedback.RankGraph

namespace DirectedFeedback.Construction
open DirectedFeedback.SourceProbability FiniteDistribution
open RankGraph Prefix PrefixExperiment Games
variable {U V E X Y : Type} [Fintype U] [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
variable {M T N : ℕ} [NeZero M] [NeZero T]

omit [Fintype U] [Fintype X] [NeZero M] [NeZero T] [Nonempty X] in
theorem cell_takePrefix {t : ℕ} (ht : t ≤ T) (a : PrefixData U X M T) :
    cell (takePrefix ht a) = prefixCell t (sets a) := by
  apply prefixCell_congr
  intro j hj
  simp only [sets, hj, dite_eq_left, takePrefix, lt_of_lt_of_le hj ht]

end DirectedFeedback.Construction
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
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_PrefixBit
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype _root_.OAI.DFVSGames.Reduction.ActualSource.sourceIndexNonempty _root_.OAI.DFVSGames.Soundness.ConditionalIncidences.zeroBits _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.CookLevin.NPTableau.codec_width_nonempty _root_.OAI.DirectedFeedback.RankPackets.shapeFintype _root_.OAI.DirectedFeedback.RawFamily.eNonempty _root_.OAI.DirectedFeedback.RawFamily.wNonempty _root_.OAI.DirectedFeedback.StackDSL.Code.labelFintype
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
namespace DirectedFeedback.Construction
open DirectedFeedback.SourceProbability FiniteDistribution
open RankGraph Prefix PrefixExperiment Games
variable {U V E X Y : Type} [Fintype U] [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
variable {M T N : ℕ} [NeZero M] [NeZero T]
omit [Fintype U] [Fintype X] [NeZero M] [NeZero T] [Nonempty X] in
theorem vertices_takePrefix {t : ℕ} (ht : t ≤ T) (a : PrefixData U X M T) :
    vertices (takePrefix ht a) = takePrefix ht (vertices a) := rfl

variable (G : Game U V E X Y) (ψLaw : FiniteDistribution (Emb (rankLength X T) N))
variable (hYX : Fintype.card Y ≤ Fintype.card X) (fiber : E → X ≃ Y × Bool)
variable (deleted : OutputVertex (M := M) G ψLaw → Bool)
variable (ord : OutputVertex (M := M) G ψLaw → ℕ)
variable (hord : ∀ {a b}, deleted a = false → deleted b = false →
  OutputArc G ψLaw hYX fiber a b → ord a < ord b)
variable (hrank : ∀ r, deleted (.inl r) = false)

def prefixBit (d : Full U X M T N) (t : ℕ) : Set (Fin t → X) → Bool :=
  if h : t ≤ T then referenceBit (rankOrder G ψLaw ord) d.1.val rankLength_ge
    (.inl ⟨⟨t,by omega⟩,takePrefix h (vertices d.2)⟩) else fun _ => false

include hord hrank in
theorem prefixBit_properties (d : Full U X M T N) {t : ℕ} (ht : t ≤ T) :
    prefixBit G ψLaw ord d t ∅ = false ∧ prefixBit G ψLaw ord d t Set.univ = true := by
  simp only [prefixBit, dite_eq_left ht]
  exact ⟨reference_empty rankLength_ge d.1.property
    (rankOrder_arc G ψLaw hYX fiber deleted ord hord hrank) _,
    reference_univ rankLength_ge d.1.property
    (rankOrder_arc G ψLaw hYX fiber deleted ord hord hrank) _⟩

def prefixTransition (d : Full U X M T N) (t : ℕ) : Fin (cellCount t) :=
  if h : t ≤ T then transition (prefixBit G ψLaw ord d t) (prefixCell t (sets d.2))
    (prefixBit_properties G ψLaw hYX fiber deleted ord hord hrank d h).1
    (prefixBit_properties G ψLaw hYX fiber deleted ord hord hrank d h).2
  else 0

theorem prefixBit_lift (d : Full U X M T N) (t : ℕ) (ht : t < T)
    (A : Set (Fin t → X)) :
    prefixBit G ψLaw ord d (t+1) (Fin.init ⁻¹' A) = prefixBit G ψLaw ord d t A := by
  simp only [prefixBit, dite_eq_left (show t+1 ≤ T by omega), dite_eq_left (show t ≤ T by omega), referenceBit]
  exact (compare_prefix_big (ord := rankOrder G ψLaw ord) (ψ := d.1.val)
    t ht (takePrefix (by omega) (vertices d.2)) A _ _ _).symm

theorem full_membership (fallback : X) (d : Full U X M T N)
    (hgood : Good (rankOrder G ψLaw ord) d.1.val rankLength_ge (fullWildcard (V := V) (Y := Y) d).tuple)
    (a : Fin T → X)
    (ha : cell d.2 a = prefixTransition G ψLaw hYX fiber deleted ord hord hrank d T)
    (j : Fin T) :
    (d.2 j).2.2 (a j) = bigFunction G ψLaw hYX fiber deleted ord hord hrank fallback
      (d.1, ⟨j,takePrefix (Nat.le_of_lt j.isLt) d.2⟩) (d.2 j).1 (d.2 j).2.2 := by
  let g := prefixBit G ψLaw ord d
  let r := prefixTransition G ψLaw hYX fiber deleted ord hord hrank d
  have hg (t : ℕ) (ht : t ≤ T) : Monotone (g t) := by
    simp only [g, prefixBit, dite_eq_left ht]
    exact good_monotone rankLength_ge d.1.property
      (rankOrder_arc G ψLaw hYX fiber deleted ord hord hrank) _
      (good_take_prefix _ _ rankLength_ge T le_rfl (vertices d.2) hgood t ht)
  have hr (t : ℕ) (ht : t ≤ T) : Transition (g t) (prefixCell t (sets d.2)) (r t) := by
    simp only [r, prefixTransition, dite_eq_left ht]
    exact transition_spec _ _ _ _
  have hh := full_transition_membership g (sets d.2) r T hg
    (prefixBit_lift G ψLaw ord d) hr a ha j
  have hgood' : Good (rankOrder G ψLaw ord) d.1.val rankLength_ge
      (.inl ⟨⟨j.val+1,by have := j.isLt; omega⟩,
        Fin.snoc (vertices (takePrefix (Nat.le_of_lt j.isLt) d.2)) (d.2 j).1⟩) := by
    convert good_take_prefix (rankOrder G ψLaw ord) d.1.val rankLength_ge T le_rfl
      (vertices d.2) hgood (j.val+1) (by have := j.isLt; omega) using 1
    all_goals try with_reducible_and_instances rfl
    congr 2
    funext i
    refine Fin.lastCases ?_ (fun k => ?_) i
    · simp [vertices, takePrefix]
    · simp [vertices, takePrefix]
  have hvertices : takePrefix (by have := j.isLt; omega : j.val+1 ≤ T) (vertices d.2) =
      Fin.snoc (vertices (takePrefix (Nat.le_of_lt j.isLt) d.2)) (d.2 j).1 := by
    funext i
    refine Fin.lastCases ?_ (fun k => ?_) i
    · simp [vertices, takePrefix]
    · simp [vertices, takePrefix]
  simp only [vertices_takePrefix] at hvertices
  have hgood'' := hgood'
  simp only [vertices_takePrefix] at hgood''
  have hb (b : Bool) : decide (b = true) = b := by cases b <;> rfl
  simp only [g, r, conditionedValue, stepFunction, prefixBit,
    dite_eq_left (Nat.le_of_lt j.isLt), dite_eq_left (show j.val+1 ≤ T by have := j.isLt; omega),
    prefixTransition, sets, dite_eq_left j.isLt, Set.mem_ofPred_eq,
    hb, bigFunction, conditionedBig, normalizedCondition, ↓reduceIte,
    bigStepBit, cell_takePrefix, vertices_takePrefix, hgood''] at hh ⊢
  rw [hvertices] at hh
  exact hh

end DirectedFeedback.Construction

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Construction
open DirectedFeedback.SourceProbability FiniteDistribution
open RankGraph Prefix PrefixExperiment Games
variable {U V E X Y : Type} [Fintype U] [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
variable {M T N : ℕ} [NeZero M] [NeZero T]
variable (G : Game U V E X Y) (ψLaw : FiniteDistribution (Emb (rankLength X T) N))
variable (hYX : Fintype.card Y ≤ Fintype.card X) (fiber : E → X ≃ Y × Bool)
variable (deleted : OutputVertex (M := M) G ψLaw → Bool)
variable (ord : OutputVertex (M := M) G ψLaw → ℕ)
variable (hord : ∀ {a b}, deleted a = false → deleted b = false →
  OutputArc G ψLaw hYX fiber a b → ord a < ord b)
variable (hrank : ∀ r, deleted (.inl r) = false)

def favorable (d : Full U X M T N) : Bool := decide (
  0 < (fullLaw G ψLaw).weight d ∧ fullDeleted G ψLaw deleted d = false ∧
  Good (rankOrder G ψLaw ord) d.1.val rankLength_ge (fullWildcard (V := V) (Y := Y) d).tuple)

def prefixValue (fallback : X) (ψ : Emb (rankLength X T) N) (t : ℕ)
    (a : PrefixData U X M t) (u : U) (b : X → Bool) : ℝ :=
  if ht : t < T then
    if bigFunction G ψLaw hYX fiber deleted ord hord hrank fallback (ψ,⟨⟨t,ht⟩,a⟩) u b
    then 1 else 0
  else 0

theorem favorable_count (fallback : X) (d : Full U X M T N)
    (hd : favorable G ψLaw deleted ord d = true) (i : Fin M) :
    bias i * T / (2*M) ≤ count i (prefixValue G ψLaw hYX fiber deleted ord hord hrank fallback)
      d.1 d.2 := by
  obtain ⟨hpos,hkeep,hgood⟩ := of_decide_eq_true hd
  have hk : deleted (.inr (.inl (.inl ⟨d,hpos⟩))) = false := by
    simpa only [fullDeleted, extend, dite_eq_left hpos] using hkeep
  obtain ⟨x,hx,hstar⟩ := full_unstarred G ψLaw hYX fiber deleted ord hord hrank ⟨d,hpos⟩ hk hgood
  have hm (j : Fin T) := full_membership G ψLaw hYX fiber deleted ord hord hrank fallback d hgood x
    (by simpa only [prefixTransition, prefixBit, dite_eq_left le_rfl, takePrefix_self, fullWildcard, cell] using hx) j
  have he : count i (prefixValue G ψLaw hYX fiber deleted ord hord hrank fallback) d.1 d.2 =
      (fullCount d.2 i x : ℝ) := by
    simp only [count, fullCount, Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
      Nat.cast_one, Nat.cast_zero, prefixValue]
    apply Finset.sum_congr rfl
    intro j _
    simp only [dite_eq_left j.isLt]
    rw [← hm j]
    by_cases hi : (d.2 j).2.1 = i <;> cases (d.2 j).2.2 (x j) <;> simp [hi]
  rw [he]
  exact not_lt.mp (fun h => hstar ⟨i,h⟩)

theorem favorable_probability (D H ρ : ℝ) (hH : 0 < H)
    (hcost : H * (fullLaw G ψLaw).probability (fullDeleted G ψLaw deleted) ≤ D)
    (hbad : (fullLaw (M := M) G ψLaw).probability (fun d => decide (¬
      Good (rankOrder G ψLaw ord) d.1.val rankLength_ge
        (fullWildcard (V := V) (Y := Y) d).tuple)) ≤ ρ)
    (hnum : ρ + D/H ≤ 1/2) :
    1/2 ≤ (fullLaw G ψLaw).probability (favorable G ψLaw deleted ord) := by
  have he := expectation_mono_support (fullLaw (M := M) G ψLaw)
    (f := fun _ => (1:ℝ))
    (g := fun d => (if favorable G ψLaw deleted ord d then 1 else 0) +
      (if fullDeleted G ψLaw deleted d then 1 else 0) +
      (if decide (¬Good (rankOrder G ψLaw ord) d.1.val rankLength_ge
        (fullWildcard (V := V) (Y := Y) d).tuple) then 1 else 0)) (by
      intro d hp
      by_cases hg : Good (rankOrder G ψLaw ord) d.1.val rankLength_ge
        (fullWildcard (V := V) (Y := Y) d).tuple
      <;> cases hk : fullDeleted G ψLaw deleted d <;> simp [favorable,hp,hg,hk])
  simp only [expectation_add, ← probability_eq_expect, expectation_const] at he
  have hc : (fullLaw G ψLaw).probability (fullDeleted G ψLaw deleted) ≤ D/H :=
    (le_div_iff₀ hH).mpr (by simpa [mul_comm] using hcost)
  linarith

theorem full_acceptance (fallback : X)
    (hprob : 1/2 ≤ (fullLaw G ψLaw).probability (favorable G ψLaw deleted ord)) (i : Fin M) :
    bias i / 4 ≤ (common (M := M) G ψLaw).expectation (fun d =>
      (bigMarginal G).expectation (fun u => (subsetLaw i).probability
        (bigFunction G ψLaw hYX fiber deleted ord hord hrank fallback d u))) := by
  have hh := acceptance_lower_bound ψLaw (bigMarginal G) subsetLaw i T
    (prefixValue G ψLaw hYX fiber deleted ord hord hrank fallback) (bias i) (bias_pos i).le
    (favorable G ψLaw deleted ord)
    (by intro ψ t a u b; unfold prefixValue; split_ifs <;> norm_num)
    hprob (fun d hd => by
      simpa only [Fintype.card_fin] using
        (favorable_count G ψLaw hYX fiber deleted ord hord hrank fallback d hd i))
  apply hh.trans_eq
  apply expectation_congr
  intro d
  change (bigMarginal G).expectation (fun u =>
    (subsetLaw i).expectation (prefixValue G ψLaw hYX fiber deleted ord hord hrank fallback
      d.1 d.2.1.val d.2.2 u)) = _
  apply expectation_congr
  intro u
  rw [probability_eq_expect]
  apply expectation_congr
  intro b
  simp only [prefixValue, dite_eq_left d.2.1.isLt]

end DirectedFeedback.Construction

noncomputable section
open scoped BigOperators

noncomputable section
open scoped BigOperators

noncomputable section
open scoped BigOperators
open scoped Classical
namespace DirectedFeedback.Ranks
open DirectedFeedback.SourceProbability
open DirectedFeedback.SourceProbability.FiniteDistribution

theorem triple_data_processing {L N : ℕ} {η : ℝ}
    (μ : FiniteDistribution (Increasing L N)) (hs : Spreads μ η)
    (f g : Fin 3 → Fin L) (hf : StrictMono f) (hg : StrictMono g)
    (K : (Fin 3 → Fin N) → Bool) :
    |μ.probability (fun ψ => K (ψ.val ∘ f)) -
      μ.probability (fun ψ => K (ψ.val ∘ g))| ≤ η := by
  classical
  let I (f : Fin 3 → Fin L) (hf : StrictMono f) : Triple L :=
    ⟨Finset.univ.image f, by rw [Finset.card_image_of_injective _ hf.injective]; simp⟩
  let event (s : Finset (Fin N)) : Bool :=
    if h : s.card = 3 then K (s.orderEmbOfFin h) else false
  let A : Finset (Finset (Fin N)) := Finset.univ.filter (fun s => event s = true)
  have hevent (f : Fin 3 → Fin L) (hf : StrictMono f) (ψ : Increasing L N) :
      decide ((I f hf).val.image ψ.val ∈ A) = K (ψ.val ∘ f) := by
    have hmono := ψ.property.comp hf
    have hc : ((I f hf).val.image ψ.val).card = 3 := by
      rw [Finset.card_image_of_injective _ ψ.property.injective]
      exact (I f hf).property
    have heq := Finset.orderEmbOfFin_unique hc (f := ψ.val ∘ f)
      (fun j => by simp [I]) hmono
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
    have hh : event ((I f hf).val.image ψ.val) = K (ψ.val ∘ f) := by
      dsimp [event]
      rw [dite_eq_left hc, ← heq]
    simp [hh]
  simpa only [hevent] using hs (I f hf) (I g hg) A

end DirectedFeedback.Ranks

namespace DirectedFeedback.RankGraph
open DirectedFeedback.SourceProbability
open DirectedFeedback.SourceProbability.FiniteDistribution
open DirectedFeedback.Ranks
variable {U V X Y : Type} {T N L : ℕ}

theorem comparison_expectations {η : ℝ}
    (μ : FiniteDistribution (Increasing L N)) (hs : Spreads μ η)
    (ord : Rank U V X Y T N → ℕ) (d : Tuple U V T)
    (E : Set (Domain U V X Y T d)) (a c h a' c' h' : Fin L)
    (hac : a < c) (hch : c < h) (hac' : a' < c') (hch' : c' < h') :
    |μ.probability (fun ψ => compareBit ord ψ.val d E a c h) -
      μ.probability (fun ψ => compareBit ord ψ.val d E a' c' h')| ≤ η := by
  classical
  exact triple_data_processing μ hs _ _ (tripleVector_strict hac hch)
    (tripleVector_strict hac' hch')
    (fun r => decide (ord (vertex d (fun lambda => if lambda ∈ E then r 0 else r 2)) <
      ord (marker (r 1))))

theorem ordered_disagreement {I : Type*} [Fintype I]
    (μ : FiniteDistribution I) (p q : I → Bool)
    (hpq : (∀ i, p i ≤ q i) ∨ (∀ i, q i ≤ p i)) {η : ℝ}
    (hc : |μ.probability p - μ.probability q| ≤ η) :
    μ.probability (fun i => decide (p i ≠ q i)) ≤ η := by
  rcases hpq with h | h
  · rw [indicator_difference μ p q (fun i => (Bool.le_iff_imp.mp (h i)))]
    exact (le_abs_self _).trans (by rwa [abs_sub_comm])
  · have he := indicator_difference μ q p (fun i => (Bool.le_iff_imp.mp (h i)))
    have hh : (fun i => decide (p i ≠ q i)) = (fun i => decide (q i ≠ p i)) := by
      funext i; simp [ne_comm]
    rw [hh, he]
    exact (le_abs_self _).trans hc

theorem compare_marker_mono (ord : Rank U V X Y T N → ℕ)
    (hord : ∀ {a b}, Arc a b → ord a < ord b)
    (ψ : Increasing L N) (d : Tuple U V T) (E : Set (Domain U V X Y T d))
    (a h : Fin L) {c c' : Fin L} (hc : c ≤ c') :
    compareBit ord ψ.val d E a c h ≤ compareBit ord ψ.val d E a c' h := by
  rcases hc.eq_or_lt with rfl | hc
  · exact le_rfl
  rw [Bool.le_iff_imp]
  simp only [compareBit, decide_eq_true_eq]
  exact fun hh => hh.trans (hord (marker_arc (ψ.property hc)))

theorem comparison_disagreement (hL : 30 ≤ L) {η : ℝ}
    (μ : FiniteDistribution (Increasing L N)) (hs : Spreads μ η)
    (ord : Rank U V X Y T N → ℕ)
    (hord : ∀ {a b}, Arc a b → ord a < ord b)
    (d : Tuple U V T) (E : Set (Domain U V X Y T d))
    (a c h : Fin L) (hu : usable a c h) :
    μ.probability (fun ψ => decide (compareBit ord ψ.val d E a c h ≠
      referenceBit ord ψ.val hL d E)) ≤ 3 * η := by
  have hua := hu.1
  have hac := hu.2.1
  have huc := hu.2.2.1
  have hucL := hu.2.2.2.1
  have huh := hu.2.2.2.2
  let z : Fin L := ⟨0, by omega⟩
  let lo : Fin L := ⟨1, by omega⟩
  let ref : Fin L := ⟨14, by omega⟩
  let hi : Fin L := ⟨L - 2, by omega⟩
  let cp : Fin L := ⟨c.val + 1, by omega⟩
  let A0 (ψ : Increasing L N) := compareBit ord ψ.val d E lo ref hi
  let A1 (ψ : Increasing L N) := compareBit ord ψ.val d E lo c hi
  let A2 (ψ : Increasing L N) := compareBit ord ψ.val d E z c cp
  let A3 (ψ : Increasing L N) := compareBit ord ψ.val d E a c h
  have h01 : μ.probability (fun ψ => decide (A0 ψ ≠ A1 ψ)) ≤ η := by
    apply ordered_disagreement
    · rcases le_total ref c with hc | hc
      · exact Or.inl (fun ψ => compare_marker_mono ord hord ψ d E lo hi hc)
      · exact Or.inr (fun ψ => compare_marker_mono ord hord ψ d E lo hi hc)
    · exact comparison_expectations μ hs ord d E lo ref hi lo c hi
        (by simp [Fin.lt_def, lo, ref]) (by simp [Fin.lt_def, ref, hi]; omega)
        (by simp [Fin.lt_def, lo]; omega) (by simp [Fin.lt_def, hi]; omega)
  have h12 : μ.probability (fun ψ => decide (A1 ψ ≠ A2 ψ)) ≤ η := by
    apply ordered_disagreement
    · apply Or.inl
      intro ψ
      apply compareBit_mono_of_arc hord
      exact twoLevel_arc ψ.property d (Set.Subset.refl _) (by simp [Fin.lt_def, z, lo])
        (by simp [Fin.lt_def, z, hi]; omega) (by simp [Fin.lt_def, cp, hi]; omega)
    · exact comparison_expectations μ hs ord d E lo c hi z c cp
        (by simp [Fin.lt_def, lo]; omega) (by simp [Fin.lt_def, hi]; omega)
        (by simp [Fin.lt_def, z]; omega) (by simp [Fin.lt_def, cp])
  have h23 : μ.probability (fun ψ => decide (A2 ψ ≠ A3 ψ)) ≤ η := by
    apply ordered_disagreement
    · apply Or.inr
      intro ψ
      apply compareBit_mono_of_arc hord
      exact twoLevel_arc ψ.property d (Set.Subset.refl _) (by simp [Fin.lt_def, z]; omega)
        (by simp [Fin.lt_def, z]; omega) (by simp [Fin.lt_def, cp]; omega)
    · exact comparison_expectations μ hs ord d E z c cp a c h
        (by simp [Fin.lt_def, z]; omega) (by simp [Fin.lt_def, cp]) hac (by omega)
  have hh := probability_disagree_triangle μ A0 A1 A3
  have hh' := probability_disagree_triangle μ A1 A2 A3
  have he : μ.probability (fun ψ => decide (A0 ψ ≠ A3 ψ)) ≤ 3 * η := by linarith
  calc
    _ = μ.probability (fun ψ => decide (A0 ψ ≠ A3 ψ)) := by
      apply congrArg (μ.probability)
      funext ψ
      change decide (A3 ψ ≠ A0 ψ) = decide (A0 ψ ≠ A3 ψ)
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      exact ne_comm
    _ ≤ _ := he

theorem goodness_probability [Fintype X] [Fintype Y]
    (hL : 30 ≤ L) {η : ℝ} (hη : 0 ≤ η)
    (μ : FiniteDistribution (Increasing L N)) (hs : Spreads μ η)
    (ord : Rank U V X Y T N → ℕ)
    (hord : ∀ {a b}, Arc a b → ord a < ord b) (d : Tuple U V T) :
    μ.probability (fun ψ => decide (¬Good ord ψ.val hL d)) ≤
      3 * η * (L : ℝ)^3 * 2^(Fintype.card (Domain U V X Y T d)) := by
  classical
  let J := Set (Domain U V X Y T d) × Fin L × Fin L × Fin L
  let bad (j : J) (ψ : Increasing L N) : Bool :=
    decide (usable j.2.1 j.2.2.1 j.2.2.2 ∧
      compareBit ord ψ.val d j.1 j.2.1 j.2.2.1 j.2.2.2 ≠ referenceBit ord ψ.val hL d j.1)
  have hb (j : J) : μ.probability (bad j) ≤ 3 * η := by
    by_cases hu : usable j.2.1 j.2.2.1 j.2.2.2
    · simpa only [bad, hu, true_and] using comparison_disagreement hL μ hs ord hord d j.1
        j.2.1 j.2.2.1 j.2.2.2 hu
    · simp only [bad, hu, false_and, decide_false, probability_false]
      positivity
  calc
    _ ≤ μ.probability (fun ψ => decide (∃ j : J, bad j ψ = true)) := by
      apply probability_mono
      intro ψ hp
      have hn : ¬Good ord ψ.val hL d := of_decide_eq_true hp
      unfold Good at hn
      push Not at hn
      obtain ⟨E, a, c, h, hu, he⟩ := hn
      apply decide_eq_true
      refine ⟨(E, a, c, h), ?_⟩
      simpa only [bad, decide_eq_true_eq] using And.intro hu he
    _ ≤ ∑ j : J, μ.probability (bad j) := probability_exists_le_sum μ bad
    _ ≤ ∑ _j : J, 3 * η := Finset.sum_le_sum (fun j _ => hb j)
    _ = _ := by simp [J, Fintype.card_set, Nat.cast_mul, Nat.cast_pow]; ring

end DirectedFeedback.RankGraph

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.RankGraph
open DirectedFeedback.SourceProbability FiniteDistribution
open Ranks
variable {U V X Y : Type} [Fintype X] [Fintype Y] [Nonempty X]
variable {T N L : ℕ}

theorem domain_card_bound (hYX : Fintype.card Y ≤ Fintype.card X) (d : Tuple U V T) :
    Fintype.card (Domain U V X Y T d) ≤ (Fintype.card X)^T := by
  have hm : 1 ≤ Fintype.card X := Fintype.card_pos
  rcases d with ⟨t,s⟩ | ⟨t,s,v⟩
  · change Fintype.card (Fin t.val → X) ≤ _
    rw [Fintype.card_fun, Fintype.card_fin]
    exact Nat.pow_le_pow_right hm (by have := t.isLt; omega)
  · change Fintype.card ((Fin t.val → X) × Y) ≤ _
    rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
    calc
      _ ≤ (Fintype.card X)^t.val * Fintype.card X := Nat.mul_le_mul_left _ hYX
      _ = (Fintype.card X)^(t.val+1) := (pow_succ _ _).symm
      _ ≤ _ := Nat.pow_le_pow_right hm t.isLt

theorem goodness_bound (hYX : Fintype.card Y ≤ Fintype.card X)
    (hL : 30 ≤ L) {η ρ : ℝ} (hη : 0 ≤ η)
    (haccuracy : 3*η*(L:ℝ)^3*2^((Fintype.card X)^T) ≤ ρ)
    (μ : FiniteDistribution (Increasing L N)) (hs : Spreads μ η)
    (ord : Rank U V X Y T N → ℕ)
    (hord : ∀ {a b}, Arc a b → ord a < ord b) (d : Tuple U V T) :
    μ.probability (fun ψ => decide (¬Good ord ψ.val hL d)) ≤ ρ := by
  apply (goodness_probability hL hη μ hs ord hord d).trans
  apply le_trans _ haccuracy
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (domain_card_bound hYX d)

theorem sampled_goodness {Ω : Type*} [Fintype Ω]
    (hYX : Fintype.card Y ≤ Fintype.card X) (hL : 30 ≤ L) {η ρ : ℝ} (hη : 0 ≤ η)
    (haccuracy : 3*η*(L:ℝ)^3*2^((Fintype.card X)^T) ≤ ρ)
    (μ : FiniteDistribution (Increasing L N)) (hs : Spreads μ η)
    (ν : FiniteDistribution Ω) (tuple : Ω → Tuple U V T)
    (ord : Rank U V X Y T N → ℕ)
    (hord : ∀ {a b}, Arc a b → ord a < ord b) :
    (μ.product ν).probability (fun a => decide (¬Good ord a.1.val hL (tuple a.2))) ≤ ρ := by
  rw [probability_eq_expect, expectation_product, expectation_comm]
  simp_rw [← probability_eq_expect]
  calc
    _ ≤ ν.expectation (fun _ => ρ) := expectation_mono _ (fun a =>
      goodness_bound hYX hL hη haccuracy μ hs ord hord (tuple a))
    _ = _ := expectation_const _ _

end DirectedFeedback.RankGraph

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Construction
open DirectedFeedback.SourceProbability FiniteDistribution
open RankGraph Prefix PrefixExperiment Games Ranks
variable {U V E X Y : Type} [Fintype U] [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
variable {M T N : ℕ} [NeZero M] [NeZero T]
variable (G : Game U V E X Y) (ψLaw : FiniteDistribution (Emb (rankLength X T) N))
variable (hYX : Fintype.card Y ≤ Fintype.card X) (fiber : E → X ≃ Y × Bool)
variable (deleted : OutputVertex (M := M) G ψLaw → Bool)
variable (ord : OutputVertex (M := M) G ψLaw → ℕ)
variable (hord : ∀ {a b}, deleted a = false → deleted b = false →
  OutputArc G ψLaw hYX fiber a b → ord a < ord b)
variable (hrank : ∀ r, deleted (.inl r) = false)
variable {η ρ : ℝ} (hη : 0 ≤ η)
variable (haccuracy : 3*η*(rankLength X T : ℝ)^3*2^((Fintype.card X)^T) ≤ ρ)
variable (hs : Spreads ψLaw η)

include hord hrank hη haccuracy hs in
theorem full_badness :
    (fullLaw (M := M) G ψLaw).probability (fun d => decide (¬
      Good (rankOrder G ψLaw ord) d.1.val rankLength_ge
        (fullWildcard (V := V) (Y := Y) d).tuple)) ≤ ρ := by
  exact sampled_goodness hYX rankLength_ge hη haccuracy ψLaw hs
    ((atomLaw (bigMarginal G) subsetLaw).iid T)
    (fun a => Sum.inl ⟨⟨T,by omega⟩,vertices a⟩)
    (rankOrder G ψLaw ord) (rankOrder_arc G ψLaw hYX fiber deleted ord hord hrank)

end DirectedFeedback.Construction
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
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_LastBias
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype _root_.OAI.DFVSGames.Reduction.ActualSource.sourceIndexNonempty _root_.OAI.DFVSGames.Soundness.ConditionalIncidences.zeroBits _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.CookLevin.NPTableau.codec_width_nonempty _root_.OAI.DirectedFeedback.RankPackets.shapeFintype _root_.OAI.DirectedFeedback.RawFamily.eNonempty _root_.OAI.DirectedFeedback.RawFamily.wNonempty _root_.OAI.DirectedFeedback.StackDSL.Code.labelFintype
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
namespace DirectedFeedback.Construction
open DirectedFeedback.SourceProbability FiniteDistribution
open RankGraph Prefix PrefixExperiment Games Ranks
variable {U V E X Y : Type} [Fintype U] [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
variable {M T N : ℕ} [NeZero M] [NeZero T]
variable (G : Game U V E X Y) (ψLaw : FiniteDistribution (Emb (rankLength X T) N))
variable (hYX : Fintype.card Y ≤ Fintype.card X) (fiber : E → X ≃ Y × Bool)
variable (deleted : OutputVertex (M := M) G ψLaw → Bool)
variable (ord : OutputVertex (M := M) G ψLaw → ℕ)
variable (hord : ∀ {a b}, deleted a = false → deleted b = false →
  OutputArc G ψLaw hYX fiber a b → ord a < ord b)
variable (hrank : ∀ r, deleted (.inl r) = false)
variable {η ρ : ℝ} (hη : 0 ≤ η)
variable (haccuracy : 3*η*(rankLength X T : ℝ)^3*2^((Fintype.card X)^T) ≤ ρ)
variable (hs : Spreads ψLaw η)
include hord hrank hη haccuracy hs in
theorem big_badness :
    ((common (M := M) G ψLaw).product (bigMarginal G)).probability
      (fun a => decide (¬bigGood G ψLaw ord a.1 a.2)) ≤ ρ := by
  let prefLaw := (uniform (Fin T)).sigma (fun t =>
    (atomLaw (bigMarginal G) (subsetLaw (X := X) (M := M))).iid t.val)
  have hh := sampled_goodness hYX rankLength_ge hη haccuracy ψLaw hs
    (prefLaw.product (bigMarginal G))
    (fun a => Sum.inl ⟨⟨a.1.1.val+1, by have := a.1.1.isLt; omega⟩,
      Fin.snoc (vertices a.1.2) a.2⟩)
    (rankOrder G ψLaw ord) (rankOrder_arc G ψLaw hYX fiber deleted ord hord hrank)
  simp only [probability_eq_expect, expectation_product, common, commonLaw,
    bigGood, prefLaw] at hh ⊢
  apply le_trans (le_of_eq ?_) hh
  apply expectation_congr
  intro psi
  apply expectation_congr
  intro pre
  apply expectation_congr
  intro u
  rfl

include hord hrank hη haccuracy hs in
theorem small_badness :
    ((common (M := M) G ψLaw).product (smallMarginal G)).probability
      (fun a => decide (¬smallGood G ψLaw ord a.1 a.2)) ≤ ρ := by
  let prefLaw := (uniform (Fin T)).sigma (fun t =>
    (atomLaw (bigMarginal G) (subsetLaw (X := X) (M := M))).iid t.val)
  have hh := sampled_goodness hYX rankLength_ge hη haccuracy ψLaw hs
    (prefLaw.product (smallMarginal G))
    (fun a => Sum.inr ⟨a.1.1,vertices a.1.2,a.2⟩)
    (rankOrder G ψLaw ord) (rankOrder_arc G ψLaw hYX fiber deleted ord hord hrank)
  simp only [probability_eq_expect, expectation_product, common, commonLaw,
    smallGood, prefLaw] at hh ⊢
  apply le_trans (le_of_eq ?_) hh
  apply expectation_congr
  intro psi
  apply expectation_congr
  intro pre
  apply expectation_congr
  intro v
  rfl

include hord hrank hη haccuracy hs in
theorem edge_badness :
    ((common (M := M) G ψLaw).product G.edgeLaw).probability
      (fun a => decide (¬bigGood G ψLaw ord a.1 (G.left a.2))) ≤ ρ ∧
    ((common (M := M) G ψLaw).product G.edgeLaw).probability
      (fun a => decide (¬smallGood G ψLaw ord a.1 (G.right a.2))) ≤ ρ := by
  constructor
  · have hh := big_badness G ψLaw hYX fiber deleted ord hord hrank hη haccuracy hs
    simpa only [probability_eq_expect, expectation_product, bigMarginal,
      expectation_pushforward] using hh
  · have hh := small_badness G ψLaw hYX fiber deleted ord hord hrank hη haccuracy hs
    simpa only [probability_eq_expect, expectation_product, smallMarginal,
      expectation_pushforward] using hh

end DirectedFeedback.Construction

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Soundness
open DirectedFeedback.SourceProbability
open FiniteDistribution
variable {Ω : Type*} [Fintype Ω]

theorem acceptance_forces_tail (μ : FiniteDistribution Ω) (p : ℝ) (hp : 0 < p)
    (a b B : Ω → ℝ) (ha0 : ∀ ω, 0 ≤ a ω) (ha1 : ∀ ω, a ω ≤ 1)
    (hb1 : ∀ ω, b ω ≤ 1) (hbB : ∀ ω, b ω ≤ 2 * p * B ω)
    (hlower : p / 4 ≤ μ.expectation a)
    (hcomp : μ.expectation (fun ω => a ω * (1 - b ω)) ≤ p / 16) :
    p / 8 ≤ μ.probability (fun ω => decide (1 / (4 * p) ≤ B ω)) := by
  have hp4 : 0 < 4 * p := by positivity
  have hpoint (ω) : a ω ≤ 2 * (a ω * (1 - b ω)) +
      if 1 / (4 * p) ≤ B ω then 1 else 0 := by
    by_cases hh : 1 / (4 * p) ≤ B ω
    · simp only [hh, ↓reduceIte]
      have hz : 0 ≤ a ω * (1 - b ω) := mul_nonneg (ha0 ω) (sub_nonneg.mpr (hb1 ω))
      linarith [ha1 ω]
    · simp only [hh, ↓reduceIte, add_zero]
      have hsmall : 4 * p * B ω < 1 := by
        have hh' := (lt_div_iff₀ hp4).mp (lt_of_not_ge hh)
        nlinarith
      have hbhalf : b ω < 1 / 2 := by nlinarith [hbB ω]
      nlinarith [mul_nonneg (ha0 ω) (show 0 ≤ 1 / 2 - b ω by linarith)]
  have he := μ.expectation_mono hpoint
  have heq : μ.expectation (fun ω => 2 * (a ω * (1 - b ω)) +
      if 1 / (4 * p) ≤ B ω then 1 else 0) =
      2 * μ.expectation (fun ω => a ω * (1 - b ω)) +
        μ.probability (fun ω => decide (1 / (4 * p) ≤ B ω)) := by
    unfold expectation probability
    simp only [mul_add, Finset.sum_add_distrib, decide_eq_true_eq, mul_ite, mul_one, mul_zero]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ω _
    ring
  rw [heq] at he
  linarith

theorem dyadic_tails_expectation (μ : FiniteDistribution Ω) (M : ℕ) (B : Ω → ℝ)
    (hB : ∀ ω, 0 ≤ B ω)
    (htail : ∀ i < M, (2 : ℝ)⁻¹ ^ (i + 2) / 8 ≤
      μ.probability (fun ω => decide (2^i ≤ B ω))) :
    (M : ℝ) / 64 ≤ μ.expectation B := by
  have he := μ.expectation_mono (fun ω => dyadic_layer_cake M (B ω) (hB ω))
  have heq : μ.expectation (fun ω =>
      ∑ i ∈ Finset.range M, (2 : ℝ)^i / 2 * if 2^i ≤ B ω then 1 else 0) =
      ∑ i ∈ Finset.range M, (2 : ℝ)^i / 2 *
        μ.probability (fun ω => decide (2^i ≤ B ω)) := by
    unfold expectation probability
    simp only [Finset.mul_sum, decide_eq_true_eq, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro ω _
    split_ifs <;> ring
  rw [heq] at he
  calc
    _ = ∑ i ∈ Finset.range M, (2 : ℝ)^i / 2 * ((2 : ℝ)⁻¹ ^ (i + 2) / 8) := by
      have hterm (i : ℕ) : (2 : ℝ)^i / 2 * ((2 : ℝ)⁻¹ ^ (i + 2) / 8) = 1 / 64 := by
        rw [inv_pow, pow_add]
        have hz : (2 : ℝ)^i ≠ 0 := by positivity
        field_simp
        ring
      simp_rw [hterm]
      simp
      ring
    _ ≤ _ := (Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left
      (htail i (Finset.mem_range.mp hi)) (by positivity))).trans he

theorem dyadic_contradiction (μ : FiniteDistribution Ω) (D : ℝ) (hD : 0 ≤ D)
    (M : ℕ) (hM : (M : ℝ) = 128 * (D + 1)) (B : Ω → ℝ)
    (hB0 : ∀ ω, 0 ≤ B ω) (hB : μ.expectation B ≤ D + 1)
    (a b : Fin M → Ω → ℝ) (ha0 : ∀ i ω, 0 ≤ a i ω) (ha1 : ∀ i ω, a i ω ≤ 1)
    (hb1 : ∀ i ω, b i ω ≤ 1)
    (hbB : ∀ i ω, b i ω ≤ 2 * ((2 : ℝ)⁻¹ ^ (i.val + 2)) * B ω)
    (hlower : ∀ i, (2 : ℝ)⁻¹ ^ (i.val + 2) / 4 ≤ μ.expectation (a i))
    (hcomp : ∀ i, μ.expectation (fun ω => a i ω * (1 - b i ω)) ≤
      (2 : ℝ)⁻¹ ^ (i.val + 2) / 16) : False := by
  have ht (i : ℕ) (hi : i < M) := acceptance_forces_tail μ ((2 : ℝ)⁻¹ ^ (i + 2))
    (by positivity) (a ⟨i, hi⟩) (b ⟨i, hi⟩) B (ha0 ⟨i, hi⟩) (ha1 ⟨i, hi⟩) (hb1 ⟨i, hi⟩) (hbB ⟨i, hi⟩)
    (hlower ⟨i, hi⟩) (hcomp ⟨i, hi⟩)
  have hthreshold (i : ℕ) : 1 / (4 * ((2 : ℝ)⁻¹ ^ (i + 2))) = 2^i := by
    rw [pow_add, inv_pow]
    have hz : (2 : ℝ)^i ≠ 0 := by positivity
    field_simp
    ring
  simp_rw [hthreshold] at ht
  have hh := dyadic_tails_expectation μ M B hB0 ht
  rw [hM] at hh
  linarith

end DirectedFeedback.Soundness

noncomputable section
open scoped Classical BigOperators

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Construction
open DirectedFeedback.SourceProbability FiniteDistribution
open RankGraph Prefix PrefixExperiment Games Pivotal Ranks
variable {U V E X Y : Type} [Fintype U] [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
variable {M T N : ℕ} [NeZero M] [NeZero T]

theorem weighted_soundness
    (G : Game U V E X Y) (ψLaw : FiniteDistribution (Emb (rankLength X T) N))
    (hYX : Fintype.card Y ≤ Fintype.card X) (fiber : E → X ≃ Y × Bool)
    (hproj : ∀ e x, (fiber e x).1 = G.project e x)
    (D H K η ρ γ θ : ℝ) (hD : 0 ≤ D) (hH : 0 < H) (hK : 0 < K)
    (hη : 0 ≤ η) (hγ : 0 < γ) (hM : (M:ℝ) = 128*(D+1))
    (haccuracy : 3*η*(rankLength X T : ℝ)^3*2^((Fintype.card X)^T) ≤ ρ)
    (hspreads : Spreads ψLaw η) (hρ : Fintype.card X * ρ ≤ 1)
    (hρ0 : 0 ≤ ρ) (hfull : ρ+D/H ≤ 1/2)
    (J : ℕ) (hJ : 1 ≤ J) (hJunta : DyadicJuntaBound M ((D+1)/γ) γ J)
    (hcomp : 2*ρ + M*(2:ℝ)^T*D/K + 6*γ + θ*(J:ℝ)^2 ≤ lastBias M/16)
    (hsound : G.Sound θ)
    (F : Finset (OutputVertex (M := M) G ψLaw))
    (hF : FeedbackR (OutputArc G ψLaw hYX fiber) F) :
    D < totalDeletionCost G ψLaw D H K (fun v => decide (v ∈ F)) := by
  by_contra hn
  have hcost := not_lt.mp hn
  let deleted : OutputVertex (M := M) G ψLaw → Bool := fun v => decide (v ∈ F)
  obtain ⟨ord, hord', _⟩ := exists_topological_order (OutputArc G ψLaw hYX fiber) F hF
  have hord : ∀ {a b}, deleted a = false → deleted b = false →
      OutputArc G ψLaw hYX fiber a b → ord a < ord b := by
    intro a b ha hb hab
    exact hord' a b (by simpa [deleted] using ha) (by simpa [deleted] using hb) hab
  have hrank := rank_retained G ψLaw D H K hD hH hK deleted hcost
  obtain ⟨hf,hb,hv,hc⟩ := family_costs G ψLaw deleted D H K hD hH.le hK.le hcost
  have hbu := big_badness G ψLaw hYX fiber deleted ord hord hrank hη haccuracy hspreads
  have hbv := small_badness G ψLaw hYX fiber deleted ord hord hrank hη haccuracy hspreads
  have hρY : (Fintype.card Y:ℝ)*ρ ≤ 1 :=
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hYX) hρ0).trans hρ
  let fx : X := Classical.choice inferInstance
  let fy : Y := Classical.choice inferInstance
  have hBu' := big_budget G ψLaw hYX fiber deleted ord hord hrank fx D ρ hρ hbu hb
  have hBv' := small_budget G ψLaw hYX fiber deleted ord hord hrank fy D ρ hρY hbv hv
  have hBu : ((common (M := M) G ψLaw).product G.edgeLaw).expectation
      (bigBudget G ψLaw hYX fiber deleted ord hord hrank fx) ≤ D+1 := by
    simpa only [bigBudget, expectation_product, bigMarginal, expectation_pushforward] using hBu'
  have hBv : ((common (M := M) G ψLaw).product G.edgeLaw).expectation
      (smallBudget G ψLaw hYX fiber deleted ord hord hrank fy) ≤ D+1 := by
    simpa only [smallBudget, expectation_product, smallMarginal, expectation_pushforward] using hBv'
  have hbad := full_badness G ψLaw hYX fiber deleted ord hord hrank hη haccuracy hspreads
  have hgoodprob := favorable_probability G ψLaw deleted ord D H ρ hH hf hbad hfull
  obtain ⟨hebu,hebv⟩ := edge_badness G ψLaw hYX fiber deleted ord hord hrank hη haccuracy hspreads
  apply Soundness.dyadic_contradiction ((common (M := M) G ψLaw).product G.edgeLaw)
    D hD M hM (smallBudget G ψLaw hYX fiber deleted ord hord hrank fy)
    (fun a => budget_nonneg _) hBv
    (bigAcceptance G ψLaw hYX fiber deleted ord hord hrank fx)
    (smallAcceptance G ψLaw hYX fiber deleted ord hord hrank fy)
  · intro i a
    exact probability_nonnegative _ _
  · intro i a
    exact probability_le_one _ _
  · intro i a
    exact probability_le_one _ _
  · intro i a
    have hp := smallFunction_properties G ψLaw hYX fiber deleted ord hord hrank fy a.1 (G.right a.2)
    exact acceptance_le_mul_budget _ hp.1 hp.2.1 (2*bias i)
      (mul_nonneg (by norm_num) (bias_pos i).le) (by linarith [bias_le_quarter i])
  · intro i
    have ha := full_acceptance G ψLaw hYX fiber deleted ord hord hrank fx hgoodprob i
    simpa only [bigAcceptance, expectation_product, bigMarginal, expectation_pushforward, bias] using ha
  · intro i
    have hh := independent_comparison G ψLaw hYX fiber deleted ord hord hrank fx fy i
      D K ρ γ θ hD hK hγ hsound hproj J hJ hJunta hBu hBv hc hebu hebv
    exact hh.trans (hcomp.trans (div_le_div_of_nonneg_right (lastBias_le i) (by norm_num)))

end DirectedFeedback.Construction

noncomputable section
open scoped Classical BigOperators

noncomputable section
open scoped Classical BigOperators

namespace DirectedFeedback.Pivotal
open DirectedFeedback.SourceProbability FiniteDistribution
variable {Ω : Type*} [Fintype Ω]

theorem iid_event_lower_tail (μ : FiniteDistribution Ω) (event : Ω → Bool)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (he : μ.probability event = p) (T : ℕ) :
    (μ.iid T).probability (fun a => decide (countTrue (fun t => event (a t)) < p*T/2)) ≤
      Real.exp (-(p*T)/8) := by
  rw [← probability_pushforward (μ.iid T) (fun a t => event (a t))
      (fun b => decide (countTrue b < p*T/2)), ← iid_pushforward,
    pushforward_bool μ event p hp0 hp1 he]
  exact bernoulli_lower_tail p hp0 hp1 T

end DirectedFeedback.Pivotal

noncomputable section
open scoped Classical BigOperators

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Construction
open DirectedFeedback.SourceProbability FiniteDistribution
open PrefixExperiment Pivotal Games
variable {U V E X Y : Type} [Fintype U] [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
variable {M T N : ℕ} [NeZero M] [NeZero T]

omit [NeZero T] [Fintype V] [Fintype Y] [Nonempty X] [Nonempty Y] in

theorem fullCount_lower_tail (G : Game U V E X Y) (ell : U → X) (i : Fin M) :
    ((atomLaw (bigMarginal G) subsetLaw).iid T).probability (fun a =>
      decide ((fullCount a i (fun t => ell (vertices a t)) : ℝ) < bias i*T/(2*M))) ≤
      Real.exp (-(bias i*T/(8*M))) := by
  have hM : (0:ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  have hM' : (1:ℝ) ≤ M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  have hp0 : 0 ≤ bias i / M := (div_pos (bias_pos i) hM).le
  have hp1 : bias i / M ≤ 1 := (div_le_one hM).mpr (by linarith [bias_le_quarter i])
  have hh := iid_event_lower_tail (atomLaw (bigMarginal G) subsetLaw)
    (fun a => decide (a.2.1 = i) && a.2.2 (ell a.1)) (bias i / M) hp0 hp1
    (slot_label_probability G ell i) T
  have hc (a : PrefixData U X M T) :
      countTrue (fun t => decide ((a t).2.1 = i) && (a t).2.2 (ell (a t).1)) =
        (fullCount a i (fun t => ell (vertices a t)) : ℝ) := by
    simp only [countTrue, fullCount, Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
      Nat.cast_one, Nat.cast_zero]
    apply Finset.sum_congr rfl
    intro t _
    by_cases hi : (a t).2.1 = i <;> cases hb : (a t).2.2 (ell (a t).1) <;> simp [hi,hb,bitValue,vertices]
  simp_rw [hc] at hh
  have he1 : bias i / (M:ℝ) * T / 2 = bias i*T/(2*M) := by ring
  have he2 : -(bias i / (M:ℝ) * T) / 8 = -(bias i*T/(8*M)) := by ring
  simpa only [he1, he2] using hh

omit [Fintype V] [Fintype Y] [Nonempty X] [Nonempty Y] [NeZero T] in

theorem fullStars_probability (G : Game U V E X Y)
    (ψLaw : FiniteDistribution (Emb (rankLength X T) N)) (ell : U → X) :
    (fullLaw (M := M) G ψLaw).probability (fun d =>
      decide ((fun t => ell (vertices d.2 t)) ∈ fullStars d.2)) ≤
      M * Real.exp (-(lastBias M * T/(8*M))) := by
  rw [fullLaw, probability_eq_expect, expectation_product]
  dsimp only
  have he : (ψLaw.expectation fun _ =>
      ((atomLaw (bigMarginal G) (subsetLaw (M := M))).iid T).probability (fun a =>
        decide ((fun t => ell (vertices a t)) ∈ fullStars a))) =
      ((atomLaw (bigMarginal G) (subsetLaw (M := M))).iid T).probability (fun a =>
        decide ((fun t => ell (vertices a t)) ∈ fullStars a)) := expectation_const _ _
  apply le_trans (le_of_eq (Eq.trans ?_ he))
  swap
  · simp only [probability_eq_expect]
  have hu := probability_exists_le_sum ((atomLaw (bigMarginal G) (subsetLaw (M := M))).iid T)
    (fun i a => decide ((fullCount a i (fun t => ell (vertices a t)) : ℝ) < bias i*T/(2*M)))
  simp only [decide_eq_true_eq] at hu
  apply le_trans (b := ∑ i : Fin M, ((atomLaw (bigMarginal G) (subsetLaw (M := M))).iid T).probability
    (fun a => decide ((fullCount a i (fun t => ell (vertices a t)) : ℝ) < bias i*T/(2*M))))
  · have hev : (fun a : PrefixData U X M T =>
          decide ((fun t => ell (vertices a t)) ∈ fullStars a)) =
        (fun a => decide (∃ i : Fin M,
          (fullCount a i (fun t => ell (vertices a t)) : ℝ) < bias i*T/(2*M))) := by
      funext a
      apply Bool.eq_iff_iff.mpr
      rw [decide_eq_true_eq, decide_eq_true_eq]
      rfl
    rw [hev]
    exact hu
  calc
    _ ≤ ∑ i : Fin M, Real.exp (-(bias i*T/(8*M))) :=
      Finset.sum_le_sum (fun i _ => fullCount_lower_tail G ell i)
    _ ≤ ∑ _i : Fin M, Real.exp (-(lastBias M*T/(8*M))) := by
      apply Finset.sum_le_sum
      intro i _
      apply Real.exp_le_exp.mpr
      apply neg_le_neg
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (lastBias_le i)
        (Nat.cast_nonneg _)) (by positivity)
    _ = _ := by simp

end DirectedFeedback.Construction

noncomputable section
open scoped Classical BigOperators

namespace DirectedFeedback.Construction
open DirectedFeedback.SourceProbability FiniteDistribution
open RankGraph Prefix PrefixExperiment Games Pivotal
variable {U V E X Y : Type} [Fintype U] [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
variable {M T N : ℕ} [NeZero M] [NeZero T]
variable (G : Game U V E X Y) (ψLaw : FiniteDistribution (Emb (rankLength X T) N))
variable (hYX : Fintype.card Y ≤ Fintype.card X) (fiber : E → X ≃ Y × Bool)
variable (ellU : U → X) (ellV : V → Y)

theorem full_label_cost :
    (fullLaw (M := M) G ψLaw).probability
      (fullDeleted G ψLaw (labelDeleted (M := M) G ψLaw hYX fiber ellU ellV)) ≤
      M * Real.exp (-(lastBias M*T/(8*M))) := by
  rw [fullDeleted, probability_extend]
  have he : (fullLaw (M := M) G ψLaw).supported.probability (fun d =>
      labelDeleted (M := M) G ψLaw hYX fiber ellU ellV (.inr (.inl (.inl d)))) =
      (fullLaw (M := M) G ψLaw).probability (fun d =>
        decide ((fun t => ellU (vertices d.2 t)) ∈ fullStars d.2)) := by
    exact probability_supported (fullLaw (M := M) G ψLaw)
      (fun d => decide ((fun t => ellU (vertices d.2 t)) ∈ fullStars d.2))
  rw [he]
  exact fullStars_probability G ψLaw ellU

theorem weighted_completeness (hproject : ∀ e x, (fiber e x).1 = G.project e x)
    (D H K : ℝ) (hH : 0 ≤ H) (hK : 0 ≤ K) :
    totalDeletionCost G ψLaw D H K (labelDeleted (M := M) G ψLaw hYX fiber ellU ellV) ≤
      H * (M * Real.exp (-(lastBias M*T/(8*M)))) + 2 + K*(1-G.score ellU ellV) := by
  rw [deletionCost_decomposition]
  have hr : (∑ r : Rank U V X Y T N,
      if labelDeleted (M := M) G ψLaw hYX fiber ellU ellV (.inl r) then D+1 else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro r _
    have h : labelDeleted (M := M) G ψLaw hYX fiber ellU ellV (.inl r) = false := by
      cases e : labelDeleted (M := M) G ψLaw hYX fiber ellU ellV (.inl r) with
      | false => rfl
      | true => exact False.elim (of_decide_eq_true e : TestGraph.LabelDeleted
          (wildSupport G ψLaw hYX) (compSupport G ψLaw fiber) ellU ellV (.inl r))
    rw [h]
    rfl
  rw [hr, zero_add, big_label_cost, small_label_cost]
  have hf := mul_le_mul_of_nonneg_left (full_label_cost (M := M) G ψLaw hYX fiber ellU ellV) hH
  have hc := mul_le_mul_of_nonneg_left
    (comparison_label_cost (M := M) G ψLaw hYX fiber ellU ellV hproject) hK
  linarith

end DirectedFeedback.Construction

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Construction
open Pivotal

namespace Parameters
variable {D : ℕ} (P : Parameters D)

theorem gamma_pos : 0 < lastBias P.M/1000 := by unfold lastBias; positivity

theorem gamma_le : lastBias P.M/1000 ≤ 1/1000 := by
  have hp : lastBias P.M ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  linarith

theorem full_error (ρ : ℝ) (hρ : ρ ≤ lastBias P.M/1000) :
    ρ + (D:ℝ)/(8*((D:ℝ)+1)) ≤ 1/2 := by
  have hsmall : (D:ℝ)/(8*((D:ℝ)+1)) ≤ 1/8 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  linarith [P.gamma_le]

theorem product_error (ρ : ℝ) (hρ : ρ ≤ lastBias P.M/1000) :
    2*ρ + P.M*(2:ℝ)^P.T*D/P.K + 6*(lastBias P.M/1000) +
      (P.theta:ℝ)*(P.J:ℝ)^2 ≤ lastBias P.M/16 := by
  have hp : 0 < lastBias P.M := by unfold lastBias; positivity
  linarith [P.comparison,P.Jtheta]

end Parameters
end DirectedFeedback.Construction

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
attribute [-instance] _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.BoundedExpr.UnaryRead
open DFVSGames.Foundations.Complexity

theorem zerosBefore_def {r : Nat} {i : List Bool → (Fin r → Nat) → Nat} (hi : Def i) :
    Def (fun x a => zerosBefore x (i x a)) := by
  have hb := (LDef.input (r:=r+1)).get (fun _ a => a 0) (Def.arg 0)
  apply ((hi.min Def.length).sum (hb (some false))).congr
  intro x a
  rw [zerosBefore,count_eq_sum,List.length_take]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j < min (i x a) x.length := Finset.mem_range.mp hj
  simp [show j < i x a by omega]

theorem word_def {r : Nat} {j : List Bool → (Fin r → Nat) → Nat} (hj : Def j) :
    Def (fun x a => word x (j x a)) := by
  have hz := zerosBefore_def (r:=r+1) (Def.arg 0)
  have hb := (LDef.input (r:=r+1)).get (fun _ a => a 0) (Def.arg 0)
  have hp := PDef.and (hb (some true) : PDef (fun x a => x[a 0]?=some true))
    (PDef.nat_eq hz (hj.rename Fin.succ))
  apply (Def.length.sum hp).congr
  intro x a
  simp only [word,Function.comp_def,Fin.cons_zero,Fin.cons_succ]

end DirectedFeedback.BoundedExpr.UnaryRead

end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_Rational
attribute [-instance] _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.RankPackets.shapeFintype
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
namespace DirectedFeedback.Construction
open DirectedFeedback.SourceProbability FiniteDistribution
open RankGraph Prefix PrefixExperiment Games Pivotal Ranks
variable {U V E X Y : Type} [Fintype U] [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]

theorem parameterized_soundness {D : ℕ} (P : Parameters D) (R : RankParameters P X)
    (G : Game U V E X Y) (hYX : Fintype.card Y ≤ Fintype.card X)
    (fiber : E → X ≃ Y × Bool) (hproj : ∀ e x, (fiber e x).1 = G.project e x)
    (hsound : G.Sound P.theta)
    (F : Finset (OutputVertex (M := P.M) G R.law))
    (hF : FeedbackR (OutputArc G R.law hYX fiber) F) :
    (D:ℝ) < totalDeletionCost G R.law D (8*((D:ℝ)+1)) P.K (fun v => decide (v ∈ F)) := by
  apply weighted_soundness (J := P.J) G R.law hYX fiber hproj D (8*((D:ℝ)+1)) P.K
    R.eta R.rho (lastBias P.M/1000) P.theta (Nat.cast_nonneg _) (by positivity)
    (by exact_mod_cast P.K_pos) R.eta_pos.le P.gamma_pos
  · exact_mod_cast P.M_eq
  · exact R.accuracy
  · exact R.spreads
  · exact R.rho_alphabet
  · exact R.rho_nonneg
  · exact P.full_error R.rho R.rho_small
  · exact P.J_pos
  · exact P.junta
  · exact P.product_error R.rho R.rho_small
  · exact hsound
  · exact hF

end DirectedFeedback.Construction

open scoped Classical BigOperators

open scoped Classical BigOperators

open scoped Classical BigOperators

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
namespace DirectedFeedback.Construction
open SourceProbability FiniteDistribution Games RankGraph
variable {U V E X Y : Type} [Fintype U] [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
variable {M T N : Nat} [NeZero M] [NeZero T]

instance rawBigFintype : Fintype (Big U X M T N) := inferInstance

variable (G : Game U V E X Y) (ψLaw : FiniteDistribution (Emb (rankLength X T) N))

theorem supportEmbed_injective : Function.Injective (supportEmbed (M:=M) G ψLaw) := by
  intro a b h
  rcases a with a | (a | a) <;> rcases b with b | (b | b) <;>
    simp only [supportEmbed,Sum.inl.injEq,Sum.inr.injEq,Sum.inl_ne_inr,Sum.inr_ne_inl] at h ⊢
  · exact h
  · rcases a with a | (a | a) <;> rcases b with b | (b | b) <;>
      simp_all [forgetWild,Subtype.ext_iff]
  · exact Subtype.ext h

theorem embed_arc (hYX : Fintype.card Y≤Fintype.card X) (fiber : E → X ≃ Y × Bool)
    {a b : OutputVertex (M:=M) G ψLaw} (h : OutputArc G ψLaw hYX fiber a b) :
    AllArc G hYX fiber (supportEmbed G ψLaw a) (supportEmbed G ψLaw b) := by
  cases h with
  | rank h => exact .rank h
  | wild_in w x h => exact .wild_in (forgetWild G ψLaw w) x h
  | wild_out w x h => exact .wild_out (forgetWild G ψLaw w) x h
  | comp_in c => exact .comp_in c.val
  | comp_out c => exact .comp_out c.val

theorem all_soundness {D : Nat} (P : Parameters D) (R : RankParameters P X)
    (hYX : Fintype.card Y≤Fintype.card X) (fiber : E → X ≃ Y × Bool)
    (hproj : ∀ e x, (fiber e x).1=G.project e x) (hsound : G.Sound P.theta)
    (F : Finset (AllVertex U V E X Y P.M P.T R.N))
    (hF : FeedbackR (AllArc G hYX fiber) F) :
    (D:ℝ) < ∑ v ∈ F, allCost G R.law D (8*((D:ℝ)+1)) P.K v := by
  let Q := Finset.univ.filter (fun v => supportEmbed G R.law v ∈ F)
  have hQ : FeedbackR (OutputArc G R.law hYX fiber) Q := by
    intro n f hi ha
    obtain ⟨i,hi⟩ := hF n (fun i => supportEmbed G R.law (f i))
      ((supportEmbed_injective G R.law).comp hi) (fun i => embed_arc G R.law hYX fiber (ha i))
    exact ⟨i,by simpa [Q] using hi⟩
  have h := parameterized_soundness P R G hYX fiber hproj hsound Q hQ
  have hv : (fun v => decide (v ∈ Q))=(fun v => decide (supportEmbed G R.law v ∈ F)) := by
    funext v
    simp only [Q, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hv] at h
  rw [← allCost_sum G R.law (D:ℝ) (8*((D:ℝ)+1)) P.K (fun v => decide (v ∈ F))] at h
  simpa using h

end DirectedFeedback.Construction

end
end

section

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.AllLabels
open Construction SourceProbability FiniteDistribution Games RankGraph
variable {U V E X Y : Type} [Fintype U] [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
variable {M T N : Nat} [NeZero M] [NeZero T]
variable (G : Game U V E X Y) (hYX : Fintype.card Y≤Fintype.card X) (fiber : E → X ≃ Y × Bool)

theorem completeness {D : Nat} (P : Parameters D) (R : RankParameters P X)
    (G : Game U V E X Y) (hYX : Fintype.card Y≤Fintype.card X) (fiber : E → X ≃ Y × Bool)
    (hproj : ∀ e x, (fiber e x).1=G.project e x)
    (a : U → X) (b : V → Y) (hscore : 1-(P.theta:ℝ)≤G.score a b) :
    (∑ v : AllVertex U V E X Y P.M P.T R.N,
      if deleted G hYX fiber a b v then allCost G R.law D (8*((D:ℝ)+1)) P.K v else 0) ≤ 4 := by
  have hh := weighted_completeness (M:=P.M) G R.law hYX fiber a b hproj
      D (8*((D:ℝ)+1)) P.K (by positivity) (by exact_mod_cast P.K_pos.le)
  have hloss : (P.K:ℝ)*(1-G.score a b) ≤ (P.K:ℝ)*P.theta :=
      mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
  have he := allCost_sum (M:=P.M) G R.law (D:ℝ) (8*((D:ℝ)+1)) P.K
    (fun v => decide (deleted G hYX fiber a b v))
  simp only [decide_eq_true_eq] at he
  rw [he]
  simp only [embed_deleted]
  linarith [P.fullChernoff,P.Ktheta]

end DirectedFeedback.AllLabels

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
open Turing BoundedExpr
variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
  [Fintype σ] [Fintype Λ] [∀ k, Fintype (Γ k)] {r : Nat}

def WDef (S : List Bool → (Fin r → Nat) → Words Γ) : Prop :=
  ∀ k (i : List Bool → (Fin r → Nat) → Nat), Def i → FDef (fun x a => S x a k (i x a))

namespace WDef
variable {S T : List Bool → (Fin r → Nat) → Words Γ}

omit [DecidableEq K] [∀ k, Fintype (Γ k)] in
theorem congr (hS : WDef S) (h : ∀ x a k i, S x a k i = T x a k i) : WDef T :=
  fun k i hi => (hS k i hi).congr (fun x a => h x a k (i x a))

omit [DecidableEq K] [∀ k, Fintype (Γ k)] in
theorem ite {p : List Bool → (Fin r → Nat) → Prop} (hp : PDef p)
    (hS : WDef S) (hT : WDef T) : WDef (fun x a => if p x a then S x a else T x a) := by
  intro k i hi
  exact (hp.ite (hS k i hi) (hT k i hi)).congr (by intro x a; split <;> simp_all)

end WDef

structure CDef (c : List Bool → (Fin r → Nat) → WordCfg Γ Λ σ) : Prop where
  label : FDef (fun x a => (c x a).label)
  var : FDef (fun x a => (c x a).var)
  stk : WDef (fun x a => (c x a).stk)

namespace CDef
variable {c d : List Bool → (Fin r → Nat) → WordCfg Γ Λ σ}

omit [DecidableEq K] [Fintype σ] [Fintype Λ] [∀ k, Fintype (Γ k)] in
theorem congr (hc : CDef c) (h : ∀ x a, c x a=d x a) : CDef d := by
  have he : c=d := funext (fun x => funext (h x))
  rwa [← he]

omit [DecidableEq K] [Fintype σ] [Fintype Λ] [∀ k, Fintype (Γ k)] in
theorem ite {p : List Bool → (Fin r → Nat) → Prop} (hp : PDef p)
    (hc : CDef c) (hd : CDef d) : CDef (fun x a => if p x a then c x a else d x a) := by
  constructor
  · exact (hp.ite hc.label hd.label).congr (by intro x a; split <;> simp_all)
  · exact (hp.ite hc.var hd.var).congr (by intro x a; split <;> simp_all)
  · exact (WDef.ite hp hc.stk hd.stk).congr (by intro x a k i; split <;> simp_all)

omit [DecidableEq K] [Fintype σ] [Fintype Λ] [∀ k, Fintype (Γ k)] in
theorem bind {A : Type} [Fintype A] {f : List Bool → (Fin r → Nat) → A}
    (hf : FDef f) {g : A → List Bool → (Fin r → Nat) → WordCfg Γ Λ σ}
    (hg : ∀ v, CDef (g v)) : CDef (fun x a => g (f x a) x a) := by
  constructor
  · exact hf.bind (fun v => (hg v).label)
  · exact hf.bind (fun v => (hg v).var)
  · intro k i hi
    exact hf.bind (fun v => (hg v).stk k i hi)
end CDef

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

omit [DecidableEq K] [Fintype K] in
theorem localWord_def {d : List Bool → (Fin r → Nat) → LocalData Γ Λ σ R}
    (hc : FDef (fun x a => (d x a).ctrl))
    (hh : ∀ i k, FDef (fun x a => (d x a).head i k))
    (hb : ∀ i k, FDef (fun x a => (d x a).band i k))
    {j : List Bool → (Fin r → Nat) → Nat} (hj : Def j) :
    CDef (fun x a => (d x a).wordCfg (j x a)) := by
  constructor
  · exact hc.map Prod.fst
  · exact hc.map Prod.snd
  · intro k i hi
    have head := FDef.select (fun t => hh t k) hi none
    have band := FDef.select (fun t => hb t k) (hi.sub (hj.sub (Def.lit R))) none
    have cond := (PDef.le (hj.sub (Def.lit R)) hi).and
      (PDef.lt hi ((hj.sub (Def.lit R)).add (Def.lit (2*R+1))))
    have result := (PDef.lt hi (Def.lit R)).ite head (cond.ite band (FDef.const none))
    apply result.congr
    intro x a
    dsimp [LocalData.wordCfg]
    by_cases h : i x a<R
    · simp [h]
    · by_cases hb : j x a-R ≤ i x a ∧ i x a<j x a-R+(2*R+1)
      · have hu : i x a-(j x a-R)<2*R+1 := by omega
        simp [h,hb,hu]
      · have hn : ¬(j x a ≤ i x a+R ∧ i x a<j x a-R+(2*R+1)) := by omega
        simp [h,hn]

namespace NPTableau
attribute [local instance] FinTM2.ΛFin FinTM2.kFin FinTM2.σFin

theorem certBound_def (V : NPVerifier) {r : Nat} : Def (fun (x : List Bool) (_ : Fin r → Nat) => certBound V x.length) :=
  Def.length.poly V.witnessBound

theorem inputBound_def (V : NPVerifier) {r : Nat} : Def (fun (x : List Bool) (_ : Fin r → Nat) => inputBound V x.length) :=
  (((Def.lit 2).mul Def.length).add (certBound_def V)).add (Def.lit 1)

theorem horizon_def (V : NPVerifier) {r : Nat} : Def (fun (x : List Bool) (_ : Fin r → Nat) => horizon V x.length) :=
  (inputBound_def V).poly V.computation.time

theorem capacity_def (V : NPVerifier) {r : Nat} : Def (fun (x : List Bool) (_ : Fin r → Nat) => capacity V x.length) :=
  (inputBound_def V).add ((horizon_def V).mul (Def.lit _))

theorem fixedPrefix_def (V : NPVerifier) {r : Nat} :
    LDef (fun x (_ : Fin r → Nat) => fixedPrefix V x) :=
  ((((LDef.replicate Def.length true).append (LDef.const [false])).append LDef.input).map
    V.computation.inputAlphabet.invFun)

theorem rawInitialAccepts_def (V : NPVerifier) {r : Nat}
    {j : List Bool → (Fin r → Nat) → Nat} (hj : Def j)
    (a : Fin 3 → Atom V.computation.tm.Γ V.computation.tm.Λ V.computation.tm.σ) :
    FDef (fun x v => rawInitialAccepts V x (j x v) a) := by
  let tm := V.computation.tm
  have cur (k : tm.K) := (PDef.lt hj (capacity_def V)).ite
    (FDef.const ((a 1).2 k)) (FDef.const none)
  have next (k : tm.K) := (PDef.lt (hj.add (Def.lit 1)) (capacity_def V)).ite
    (FDef.const ((a 2).2 k)) (FDef.const none)
  have hp := fixedPrefix_def (r:=r) V
  have hctrl : PDef (r:=r) (fun (_ : List Bool) _ =>
      (a 0).1 = (some tm.main,tm.initialState)) := PDef.const _
  have hp' := hctrl.and ((PDef.all (fun k : tm.K => (PDef.const (k≠tm.k₀)).imp
    (PDef.eq (cur k) (FDef.const none)))).and
    (((PDef.lt hj hp.length).imp (PDef.eq (cur tm.k₀) (hp.get j hj))).and
    (((PDef.le (hp.length.add (certBound_def V)) hj).imp (PDef.eq (cur tm.k₀) (FDef.const none))).and
    ((PDef.le hp.length hj).imp ((PDef.eq (cur tm.k₀) (FDef.const none)).imp
      (PDef.eq (next tm.k₀) (FDef.const none)))))))
  apply hp'.decide.congr
  intro x v
  by_cases h : j x v < capacity V x.length <;>
    by_cases h' : j x v+1 < capacity V x.length <;>
      simp [rawInitialAccepts,initialPredicate,h,h',tm]

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

def AddrDef {r : Nat} (f : List Bool → (Fin r → Nat) → Nat × Nat) : Prop :=
  Def (fun x a => (f x a).1) ∧ Def (fun x a => (f x a).2)

namespace AddrDef
variable {r : Nat} {f g : List Bool → (Fin r → Nat) → Nat × Nat}
theorem const (p : Nat × Nat) : AddrDef (r:=r) (fun _ _ => p) := ⟨Def.lit _,Def.lit _⟩
theorem ite {p : List Bool → (Fin r → Nat) → Prop} (hp : PDef p)
    (hf : AddrDef f) (hg : AddrDef g) : AddrDef (fun x a => if p x a then f x a else g x a) := by
  constructor
  · exact (hp.nite hf.1 hg.1).congr (by intro x a; by_cases h : p x a <;> simp [h])
  · exact (hp.nite hf.2 hg.2).congr (by intro x a; by_cases h : p x a <;> simp [h])
theorem congr (hf : AddrDef f) (h : ∀ x a, f x a=g x a) : AddrDef g :=
  ⟨hf.1.congr (fun x a => congrArg Prod.fst (h x a)),
    hf.2.congr (fun x a => congrArg Prod.snd (h x a))⟩
end AddrDef

end DirectedFeedback.CookLevin

end
end

section

noncomputable section
open scoped Classical
namespace DirectedFeedback.CookLevin.NPTableau
open BoundedExpr Turing DFVSGames.Foundations.PCP
attribute [local instance] FinTM2.ΛFin FinTM2.kFin FinTM2.σFin

def decodedPattern (V : NPVerifier) (p : VerifierToCNF.Pattern (queryNumber V))
    (s : TableauSlot V.computation.tm) : Atom V.computation.tm.Γ V.computation.tm.Λ V.computation.tm.σ :=
  (alphabetCodec V).decode (fun b => p (slotIndex V (.inl (s,b))))

def rawAccepts (V : NPVerifier) (p : VerifierToCNF.Pattern (queryNumber V)) (x : List Bool) (e : Nat) : Bool :=
  let H := horizon V x.length
  let S := capacity V x.length
  let a := decodedPattern V p
  if e < S+1 then rawInitialAccepts V x e (a ∘ Sum.inl)
  else if e-(S+1) < H*(S+1) then
    rawStepAccepts V.computation.tm.m S ((e-(S+1))%(S+1)) (a ∘ Sum.inr ∘ Sum.inl)
  else decide ((a (.inr (.inr ()))).2 V.computation.tm.k₁ = some (V.computation.outputAlphabet.invFun true))

end DirectedFeedback.CookLevin.NPTableau

end
end

section

noncomputable section
open scoped Classical
namespace DirectedFeedback.BinaryEmbed
open DFVSGames DFVSGames.Foundations

theorem frame_replicate (n : Nat) : BinaryEncoding.frame (List.replicate n true)=
    List.replicate (2*n) true ++ [false] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ,BinaryEncoding.frame,ih]
    have h : 2*(n+1)=2*n+1+1 := by omega
    simp [h,List.replicate_succ]

end DirectedFeedback.BinaryEmbed

end
end

end OAI
end


