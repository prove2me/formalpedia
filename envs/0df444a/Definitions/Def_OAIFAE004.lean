-- Prove2me | Definitions.Def_OAIFAE004
-- name    : OAIFAE004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-24T19:34:06.267658+00:00
-- url     : https://prove2.me/theorems/f102e79a-4f63-47b5-978b-222eb043ccbc
-- title:
--   Definitions bundle OAIFAE004 of the split of OpenAI, Finite algebraic envelopes and the Boone–Higman conjecture
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.FiniteAlgebraicEnvelopes.main`, carved from OpenAI's openai/math development (OpenAI, *Finite algebraic envelopes and the Boone–Higman conjecture*, OpenAI Math Release, September 23, 2026, result family 250, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 475 declarations of OpenAI's Lean: 170 definitions, 1 inductive type or structure, 13 instances and 291 theorems. The definitions and types are `OAI.FiniteAlgebraicEnvelopes.AlgebraGenerators.envelopingGenerators`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Quotient.normal`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Quotient.normalCon`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Quotient.rawMap`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Quotient.representative`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.AlgebraGenerators`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.AlgebraRelations`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.BigAlgebra`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.CoefficientGenerators`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.CoefficientRelations`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.ColumnSpace`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.FullGroup`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.H`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.K`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.KMachine`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.LinearTorus`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.R`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.SmallAlgebra`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.T`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.TAlgebra`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.TClass`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.TCode`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.TLetter`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.TTest`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.affineTorusEquivalence`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.affineTransition`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.algebraEmbedding`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.algebraPresentation`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.ambientUnits`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.bigGenerators`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.coefficientPresentation`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.coefficientUnits`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.columnTransition`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.copyEmbedding`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.detectingElement`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.detectionInput`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.detectionLinear`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.elementaryInFull`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.elementaryInput`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.fullLinearAction` and 131 more.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory/BooneHigman, lean/OAI/Computability/FiniteCompiler, in whole or in part: `ActionEnvelope`, `AffineModules`, `AlgebraPresentations`, `CantorBricks`, `Corners`, `DecoratedPresentation`, `Diagrams`, `EndpointCoherence`, `FinitePresentation`, `Generators`, `MonoidAlgebras`, `Normalization`, `PartialAffine`, `Quotients`, `Rewriting`, `Selectors`, `SelfReference`, `TreeCoherence`, `TreeRefinement`, `Trees`, `TwistedSimplicity`, `UniformPaths`.
--
--   **Imports.** It imports the published bundle `Def_BooneHigman`; the bundles `OAIFAE002` and `OAIFAE003` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.FiniteAlgebraicEnvelopes.TwistedBrinThompson.finitelyPresented`, `OAI.FiniteAlgebraicEnvelopes.envelope` and `OAI.FiniteAlgebraicEnvelopes.main`.
-- source:
--   OpenAI, Finite algebraic envelopes and the Boone–Higman conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 250; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Finite-algebraic-envelopes-and-the-Boone-Higman-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory/BooneHigman, lean/OAI/Computability/FiniteCompiler at commit adc7f12

import Mathlib
import Definitions.Def_BooneHigman
import Definitions.Def_OAIFAE002
import Definitions.Def_OAIFAE003

section
-- module Solutions.OAIFAE.Normalization
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.Compiler.Path.instPrimcodableLetter _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Raw-run folds, full word compilation, partial budgets, and bounded normalization.
-/

namespace FiniteAlgebraicEnvelopes.Compiler.Word

section
open Relation
variable {S Γ Q : Type*}
variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
  [Fintype S] [Fintype Γ] [Fintype Q] [LinearOrder (Control.Sector S Γ Q)]

omit [DecidableEq Q] [Fintype S] [Fintype Γ] [Fintype Q]
    [LinearOrder (Control.Sector S Γ Q)] in
theorem present_reduce {u v : List (Letter S Γ Q)} (h : Reduce A M u v) :
    present A M u = present A M v := by
  cases h.1 with
  | apply x y hr =>
    apply present_context A M ?_ x y
    rcases hr with hr | hr
    · exact PresentedMonoid.mk_eq_mk_of_rel hr
    · exact (PresentedMonoid.mk_eq_mk_of_rel hr).symm

omit [DecidableEq Q] [Fintype S] [Fintype Γ] [Fintype Q]
    [LinearOrder (Control.Sector S Γ Q)] in
theorem present_reduces {u v : List (Letter S Γ Q)} (h : Reduces A M u v) :
    present A M u = present A M v := by
  induction h with
  | refl => rfl
  | tail _ h ih => exact ih.trans (present_reduce A M h)

theorem present_normal {f : List S → List S} {m : ℕ}
    (h : RawRuns.Budget f m) (hcomp : ComputesAt A M f m)
    (w : List (Letter S Γ Q)) (hm : grade w ≤ m) :
    present A M w = present A M (normal A M f w) :=
  present_reduces A M (reduces_normal A M h hcomp w hm)

/-- No maximum grade of a presentation derivation is assumed. Its finitely many
    contextual uses are handled by the theorem at all finite budgets. -/
theorem normal_conGen
    (hdecode : ∀ g a, A.output g = some a → g = A.input a)
    {f : List S → List S} (h : ∀ m, RawRuns.Budget f m) (hcomp : ∀ m, ComputesAt A M f m)
    {u v : FreeMonoid (Letter S Γ Q)} (he : conGen (Rel A M) u v) :
    normal A M f u = normal A M f v := by
  induction he with
  | of u v hr =>
    change Rule A M u.toList v.toList at hr
    change normal A M f u.toList = normal A M f v.toList
    have hp := normal_rule A M hdecode (h (max (grade u.toList) (grade v.toList)))
      (hcomp (max (grade u.toList) (grade v.toList))) hr [] []
      (by simpa only [List.nil_append,List.append_nil] using le_max_left (grade u.toList) (grade v.toList))
      (by simpa only [List.nil_append,List.append_nil] using le_max_right (grade u.toList) (grade v.toList))
    simpa only [List.nil_append,List.append_nil] using hp
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih ij => exact ih.trans ij
  | @mul w x y z _ _ ih ij =>
    change normal A M f (w.toList++y.toList) = normal A M f (x.toList++z.toList)
    change normal A M f w.toList = normal A M f x.toList at ih
    change normal A M f y.toList = normal A M f z.toList at ij
    have hp := normal_context A M hdecode
      (h (max (grade (w.toList++y.toList)) (grade (x.toList++y.toList))))
      (hcomp (max (grade (w.toList++y.toList)) (grade (x.toList++y.toList)))) ih [] y.toList
      (by simpa only [List.nil_append] using le_max_left (grade (w.toList++y.toList)) (grade (x.toList++y.toList)))
      (by simpa only [List.nil_append] using le_max_right (grade (w.toList++y.toList)) (grade (x.toList++y.toList)))
    have hq := normal_context A M hdecode
      (h (max (grade (x.toList++y.toList)) (grade (x.toList++z.toList))))
      (hcomp (max (grade (x.toList++y.toList)) (grade (x.toList++z.toList)))) ij x.toList []
      (by simpa only [List.append_nil] using le_max_left (grade (x.toList++y.toList)) (grade (x.toList++z.toList)))
      (by simpa only [List.append_nil] using le_max_right (grade (x.toList++y.toList)) (grade (x.toList++z.toList)))
    simp only [List.nil_append,List.append_nil] at hp hq
    exact hp.trans hq

/-- Exact equality criterion for the finite presentation under the global
    (not assumed for constructing the presentation) evaluator hypotheses. -/
theorem present_eq_iff_normal
    (hdecode : ∀ g a, A.output g = some a → g = A.input a)
    {f : List S → List S} (h : ∀ m, RawRuns.Budget f m) (hcomp : ∀ m, ComputesAt A M f m)
    (u v : List (Letter S Γ Q)) :
    present A M u = present A M v ↔ normal A M f u = normal A M f v := by
  constructor
  · intro he
    exact normal_conGen A M hdecode h hcomp (PresentedMonoid.mk_eq_mk_iff.mp he)
  · intro he
    rw [present_normal A M (h (grade u)) (hcomp (grade u)) u le_rfl,
      present_normal A M (h (grade v)) (hcomp (grade v)) v le_rfl,he]

end

open Relation

end FiniteAlgebraicEnvelopes.Compiler.Word

/- The actual partial evaluator is a finite plan followed by partial calls.
   Its definition has no budget and does not totalize an undefined program. -/

end OAI
end

section
-- module Solutions.OAIFAE.Rewriting
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Newman normalization, block coding, canonical representatives, and static tests.
-/

/- Rewriting layer for the self-reference construction.  No assumptions on
   either main theorem are introduced here. -/
namespace FiniteAlgebraicEnvelopes.Bootstrap

section
open Relation

variable {S : Type*}

variable [DecidableEq S]

omit [DecidableEq S] in
/-- Bounded local confluence is enough: every intervening reduction has
    nonincreasing length, so no confluence outside the source budget is used. -/
theorem evaluate_unique_on {r : S → S → Prop} {rules : List (List S × List S)}
    (wf : WellFounded r) (dec : ∀ p ∈ rules, List.Shortlex r p.2 p.1) (n : ℕ)
    (localJoin : ∀ a b c, a.length ≤ n → Step rules a b → Step rules a c →
      Join (Steps rules) b c) {a b c : List S} (ha : a.length ≤ n)
    (hab : Steps rules a b) (hac : Steps rules a c)
    (hb : Irreducible (Step rules) b) (hc : Irreducible (Step rules) c) : b = c := by
  induction a using (steps_wellFounded wf dec).induction generalizing b c with
  | h a ih =>
    rcases hab.cases_head with rfl | ⟨b₁,hab₁,hb₁b⟩
    · exact irreducible_reaches _ hb hac
    rcases hac.cases_head with rfl | ⟨c₁,hac₁,hc₁c⟩
    · exact (irreducible_reaches _ hc (.head hab₁ hb₁b)).symm
    obtain ⟨d,hb₁d,hc₁d⟩ := localJoin a b₁ c₁ ha hab₁ hac₁
    obtain ⟨e,hde,he⟩ := exists_irreducible _ (steps_wellFounded wf dec) d
    have hb₁ : b₁.length ≤ n := (steps_length dec (.single hab₁)).trans ha
    have hc₁ : c₁.length ≤ n := (steps_length dec (.single hac₁)).trans ha
    exact (ih b₁ hab₁ hb₁ hb₁b (hb₁d.trans hde) hb he).trans
      (ih c₁ hac₁ hc₁ hc₁c (hc₁d.trans hde) hc he).symm

theorem evaluate_context_on {r : S → S → Prop} {rules : List (List S × List S)}
    (wf : WellFounded r) (dec : ∀ p ∈ rules, List.Shortlex r p.2 p.1) (n : ℕ)
    (localJoin : ∀ a b c, a.length ≤ n → Step rules a b → Step rules a c →
      Join (Steps rules) b c) {w v : List S} (hv : v ∈ evaluate rules w)
    (x y : List S) (hm : (x++w++y).length ≤ n) :
    evaluate rules (x++v++y) = evaluate rules (x++w++y) := by
  obtain ⟨a,ha⟩ := Part.dom_iff_mem.mp (evaluate_total (steps_wellFounded wf dec) (x++v++y))
  obtain ⟨b,hb⟩ := Part.dom_iff_mem.mp (evaluate_total (steps_wellFounded wf dec) (x++w++y))
  obtain ⟨hva,haI⟩ := evaluate_sound ha
  obtain ⟨hwb,hbI⟩ := evaluate_sound hb
  have hab := evaluate_unique_on wf dec n localJoin hm
    ((steps_context (evaluate_sound hv).1 x y).trans hva) hwb haI hbI
  subst b
  exact (Part.eq_some_iff.mpr ha).trans (Part.eq_some_iff.mpr hb).symm

variable [Primcodable S]

 theorem primrec_iteration : Primrec (@iteration S _) := by
  exact (Primrec.option_casesOn (primrec_next.comp Primrec.fst Primrec.snd)
    (Primrec.sumInl.comp Primrec.snd)
    ((Primrec.sumInr.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)).to₂)).of_eq
    (by intro s; cases h : next s.1 s.2 <;> simp [iteration,h])

 theorem partrec_evaluate : Partrec₂ (@evaluate S _) :=
  Partrec.fix primrec_iteration.to_comp

end

/- The marker/constant-width code used in the self-reference construction.
   A block has its marker only at the start, not at the end. -/

open Relation
end FiniteAlgebraicEnvelopes.Bootstrap

end OAI
end

section
-- module Solutions.OAIFAE.Selectors
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Literal selector envelopes, rewrite saturation, and zero recognition.
-/

/- Literal selector envelopes from the self-reference construction. -/
namespace FiniteAlgebraicEnvelopes.Bootstrap

namespace Search

variable {A S Q : Type*} [DecidableEq A] [DecidableEq S] [DecidableEq Q]
variable {r : A → A → Prop} [DecidableRel (List.Shortlex r)]

variable [Fintype A] [Std.Trichotomous r] (wf : WellFounded r) (q : List A → Option Q)

variable [Primcodable A] [Primcodable S] [Primcodable Q]
omit [Std.Trichotomous r]

omit [DecidableEq A] [Fintype A] in
 theorem primrec_pick (hr : PrimrecRel (List.Shortlex r))
    {X : Type*} [Primcodable X]
    {ps : X → List (List A × Option Q)} {v : X → List A} {q : X → Option Q}
    (hp : Primrec ps) (hv : Primrec v) (hq : Primrec q) :
    Primrec (fun x => Canonical.pick (r:=r) (ps x) (v x) (q x)) :=
  Primrec.list_foldl hp hv (primrec_pickStep (Q:=Q) hr
    (hq.comp Primrec.fst) (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂

end Search
end FiniteAlgebraicEnvelopes.Bootstrap

end OAI
end

section
-- module Solutions.OAIFAE.Quotients
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Canonical compiler quotients and effective tested classes for word problems.
-/

namespace FiniteAlgebraicEnvelopes.Bootstrap
open Relation

open Relation
variable {S : Type*} [DecidableEq S] {r : S → S → Prop}

omit [DecidableEq S] in
theorem steps_bounded {rs rt : List (List S × List S)} {k : ℕ}
    (hh : Selectors.BoundedEq rs rt k)
    (hd : ∀ p ∈ rs,List.Shortlex r p.2 p.1) {u v : List S} (hu : u.length ≤ k)
    (h : Steps rs u v) : Steps rt u v := by
  induction h with
  | refl => exact .refl
  | tail h hs ih => exact ih.tail ((step_stable hh ((steps_length hd h).trans hu)).mp hs)

theorem tableNormal_at {T : ℕ → Part (List (List S × List S))} {n : ℕ}
    (wf : WellFounded r) (ht : ∀ k ≤ n,GoodTable (r:=r) T k)
    (hs : ∀ k ≤ n,∀ rk ∈ T k,∀ rn ∈ T n,Selectors.BoundedEq rk rn k)
    {rn : List (List S × List S)} (hrn : rn ∈ T n) {w : List S} (hw : w.length ≤ n) :
    tableNormal T w=evaluate rn w := by
  obtain ⟨rk,hrk,hdk,hck⟩ := ht w.length hw
  obtain ⟨rt,hrt,hdt,hct⟩ := ht n le_rfl
  have he := Part.mem_unique hrt hrn
  subst rt
  obtain ⟨u,hu⟩ := Part.dom_iff_mem.mp (evaluate_total (steps_wellFounded wf hdk) w)
  obtain ⟨v,hv⟩ := Part.dom_iff_mem.mp (evaluate_total (steps_wellFounded wf hdt) w)
  obtain ⟨hwu,huI⟩ := evaluate_sound hu
  obtain ⟨hwv,hvI⟩ := evaluate_sound hv
  have hstab := hs w.length hw rk hrk rn hrn
  have hwu' := steps_bounded hstab hdk le_rfl hwu
  have huI' := (Selectors.irreducible_bounded hstab (steps_length hdk hwu)).mp huI
  have huv := evaluate_unique_on wf hdt n (fun _ _ _ h => critical_localJoin hct h)
    hw hwu' hwv huI' hvI
  subst v
  rw [tableNormal,Part.eq_some_iff.mpr hrk,Part.bind_some]
  exact (Part.eq_some_iff.mpr hu).trans (Part.eq_some_iff.mpr hv).symm

/-- This is the whole contextual-induction step, including the table at the
    shortened contextual endpoint and irreducibility in the larger table. -/
theorem tableNormal_budget {T : ℕ → Part (List (List S × List S))} {n : ℕ}
    (wf : WellFounded r) (ht : ∀ k ≤ n,GoodTable (r:=r) T k)
    (hs : ∀ k m, k ≤ m → m ≤ n → ∀ rk ∈ T k,∀ rm ∈ T m,Selectors.BoundedEq rk rm k) :
    Compiler.PartialBudget (tableNormal T) n := by
  have htotal (w : List S) (hw : w.length ≤ n) : (tableNormal T w).Dom := by
    obtain ⟨rs,hrs,hd,hc⟩ := ht w.length hw
    rw [tableNormal,Part.eq_some_iff.mpr hrs,Part.bind_some]
    exact evaluate_total (steps_wellFounded wf hd) w
  have hlen (w : List S) (hw : w.length ≤ n) (out : List S) (ho : out ∈ tableNormal T w) :
      out.length ≤ w.length := by
    obtain ⟨rs,hrs,hd,hc⟩ := ht w.length hw
    rw [tableNormal,Part.eq_some_iff.mpr hrs,Part.bind_some] at ho
    exact steps_length hd (evaluate_sound ho).1
  refine ⟨htotal,hlen,?_⟩
  intro x w y hlenxy out hout
  obtain ⟨rs,hrs,hd,hc⟩ := ht n le_rfl
  have hw : w.length ≤ n := by simp only [List.length_append] at hlenxy; omega
  have hlenout := hlen w hw out hout
  have hshort : (x++out++y).length ≤ n := by simp only [List.length_append] at hlenxy ⊢; omega
  have heq (v : List S) (hv : v.length ≤ n) : tableNormal T v = evaluate rs v :=
    tableNormal_at wf ht (fun k hk => hs k n hk le_rfl) hrs hv
  have ehw := heq w hw
  rw [ehw] at hout
  rw [heq _ hshort,heq _ hlenxy]
  exact evaluate_context_on wf hd n (fun _ _ _ h => critical_localJoin hc h) hout x y hlenxy

/-- The source's simultaneous length induction, for the table builder actually
    fed to the recursion theorem.  `build` only receives strictly smaller budgets.
    Thus this lemma never assumes the desired total/contextual program outright. -/
theorem bootstrap_length_induction (wf : WellFounded r)
    (T : ℕ → Part (List (List S × List S))) (f : List S → Part (List S))
    (fixed : f=tableNormal T)
    (stable : ∀ k n, k ≤ n → ∀ rk ∈ T k,∀ rn ∈ T n,Selectors.BoundedEq rk rn k)
    (build : ∀ n, (∀ m<n,Compiler.PartialBudget f m) → GoodTable (r:=r) T n) :
    ∀ n, GoodTable (r:=r) T n ∧ Compiler.PartialBudget f n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hn := build n (fun m hm => (ih m hm).2)
    refine ⟨hn,?_⟩
    rw [fixed]
    apply tableNormal_budget wf
    · intro k hk
      rcases lt_or_eq_of_le hk with hk | rfl
      · exact (ih k hk).1
      · exact hn
    · intro k m hkm _
      exact stable k m hkm

end FiniteAlgebraicEnvelopes.Bootstrap

namespace FiniteAlgebraicEnvelopes

namespace Bootstrap

 theorem partrec_tableNormal_parameter {X S : Type*} [DecidableEq S]
    [Primcodable X] [Primcodable S] {T : X → ℕ → Part (List (List S × List S))}
    (ht : Partrec₂ T) : Partrec₂ (fun x => tableNormal (T x)) := by
  exact ((ht.comp Computable.fst (Primrec.list_length.to_comp.comp Computable.snd)).bind
    (partrec_evaluate.comp Computable.snd (Computable.snd.comp Computable.fst)).to₂).to₂

end Bootstrap
end FiniteAlgebraicEnvelopes

namespace FiniteAlgebraicEnvelopes.Bootstrap

section

namespace Quotient
open Relation
variable {S : Type*} [DecidableEq S]
variable (T : ℕ → Part (List (List S × List S)))

noncomputable def normal (w : List S) : List S := Compiler.partValue (tableNormal T w)

omit [DecidableEq S] in
 theorem present_steps {r : S → S → Prop} {n : ℕ} {rs : List (List S × List S)}
    (hrs : rs ∈ T n) (hd : ∀ p∈rs,List.Shortlex r p.2 p.1)
    {u v : List S} (hu : u.length ≤ n) (h : Steps rs u v) : present T u=present T v := by
  induction h with
  | refl => rfl
  | tail h hs ih => exact ih.trans (present_step T hrs ((steps_length hd h).trans hu) hs)

variable {r : S → S → Prop} (wf : WellFounded r)
  (good : ∀ n,GoodTable (r:=r) T n)
  (stable : ∀ k n,k ≤ n → ∀ rk∈T k,∀ rn∈T n,Selectors.BoundedEq rk rn k)
include wf good stable

 theorem budget (n : ℕ) : Compiler.PartialBudget (tableNormal T) n :=
  tableNormal_budget wf (fun _ _ => good _) (fun k m h _ => stable k m h)

 theorem normal_mem (w : List S) : normal T w ∈ tableNormal T w :=
  Compiler.partValue_mem ((budget T wf good stable w.length).total w le_rfl)

 theorem present_normal (w : List S) : present T w=present T (normal T w) := by
  obtain ⟨rs,hrs,hd,_⟩ := good w.length
  have h := normal_mem T wf good stable w
  rw [tableNormal,Part.eq_some_iff.mpr hrs,Part.bind_some] at h
  exact present_steps T hrs hd le_rfl (evaluate_sound h).1

 theorem normal_context (x w y : List S) :
    normal T (x++normal T w++y)=normal T (x++w++y) := by
  exact congrArg Compiler.partValue ((budget T wf good stable (x++w++y).length).context
    x w y le_rfl _ (normal_mem T wf good stable w))

 theorem normal_append (u v : List S) :
    normal T (u++v)=normal T (normal T u++normal T v) := by
  have hu := normal_context T wf good stable [] u v
  have hv := normal_context T wf good stable (normal T u) v []
  simp only [List.nil_append,List.append_nil] at hu hv
  exact hu.symm.trans hv.symm

 theorem normal_rel {u v : FreeMonoid S} (h : Rel T u v) : normal T u.toList=normal T v.toList := by
  obtain ⟨n,rs,hrs,huv,hu⟩ := h
  obtain ⟨rt,hrt,hd,hc⟩ := good n
  have he := Part.mem_unique hrt hrs
  subst rt
  have hstep : Step rs u.toList v.toList := by
    simpa only [List.nil_append,List.append_nil] using Step.apply huv [] []
  have hv : v.toList.length ≤ n := (steps_length hd (.single hstep)).trans hu
  have hat (w : List S) (hw : w.length ≤ n) : tableNormal T w=evaluate rs w :=
    tableNormal_at wf (fun _ _ => good _) (fun k hk => stable k n hk) hrs hw
  have hnu := normal_mem T wf good stable u.toList
  have hnv := normal_mem T wf good stable v.toList
  rw [hat _ hu] at hnu
  rw [hat _ hv] at hnv
  exact evaluate_unique_on wf hd n (fun _ _ _ h => critical_localJoin hc h) hu
    (evaluate_sound hnu).1 ((ReflTransGen.single hstep).trans (evaluate_sound hnv).1)
    (evaluate_sound hnu).2 (evaluate_sound hnv).2

noncomputable def normalCon : Con (FreeMonoid S) where
  r u v := normal T u.toList=normal T v.toList
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h g => h.trans g⟩
  mul' := by
    intro u v x y huv hxy
    change normal T (u.toList++x.toList)=normal T (v.toList++y.toList)
    exact (normal_append T wf good stable _ _).trans
      ((congrArg₂ (fun a b => normal T (a++b)) huv hxy).trans
        (normal_append T wf good stable _ _).symm)

 theorem present_eq_iff (u v : List S) : present T u=present T v ↔ normal T u=normal T v := by
  constructor
  · intro h
    exact (Con.conGen_le.mpr (fun _ _ h => normal_rel T wf good stable h) :
      conGen (Rel T) ≤ normalCon T wf good stable) (PresentedMonoid.mk_eq_mk_iff.mp h)
  · intro h
    exact (present_normal T wf good stable u).trans (h ▸ (present_normal T wf good stable v).symm)

end Quotient

open Relation

namespace Quotient
variable {S : Type*} [DecidableEq S]
variable (T : ℕ → Part (List (List S × List S)))
variable {r : S → S → Prop} (wf : WellFounded r)
  (good : ∀ n,GoodTable (r:=r) T n)
  (stable : ∀ k n,k ≤ n → ∀ rk∈T k,∀ rn∈T n,Selectors.BoundedEq rk rn k)
include wf good stable

 theorem normal_idempotent (w : List S) : normal T (normal T w)=normal T w := by
  simpa only [List.nil_append,List.append_nil] using normal_context T wf good stable [] w []

 theorem normal_eq_self {w : List S} {rs : List (List S × List S)} (hrs : rs∈T w.length)
    (hi : Irreducible (Step rs) w) : normal T w=w := by
  have hw := normal_mem T wf good stable w
  rw [tableNormal,Part.eq_some_iff.mpr hrs,Part.bind_some] at hw
  exact (irreducible_reaches (Step rs) hi (evaluate_sound hw).1).symm

noncomputable def representative (x : Mon T) : List S :=
  normal T (Classical.choose (present_surjective T x))

 theorem present_representative (x : Mon T) : present T (representative T x)=x := by
  rw [representative,←present_normal T wf good stable]
  exact Classical.choose_spec (present_surjective T x)

end Quotient
end

end FiniteAlgebraicEnvelopes.Bootstrap

namespace FiniteAlgebraicEnvelopes

namespace Bootstrap.Quotient
variable {S : Type*} [DecidableEq S]
variable (T : ℕ → Part (List (List S × List S)))
variable {r : S → S → Prop} (wf : WellFounded r)
  (good : ∀ n,GoodTable (r:=r) T n)
  (stable : ∀ k n,k ≤ n → ∀ rk∈T k,∀ rn∈T n,Selectors.BoundedEq rk rn k)
include wf good stable

theorem representative_mul (x y : Mon T) : representative T (x*y)=
    normal T (representative T x++representative T y) := by
  have he : present T (representative T (x*y))=
      present T (representative T x++representative T y) := by
    rw [present_append,present_representative T wf good stable,
      present_representative T wf good stable,present_representative T wf good stable]
  have hn := (present_eq_iff T wf good stable _ _).mp he
  simpa only [representative,normal_idempotent T wf good stable] using hn

variable {Γ Q : Type*} [Fintype S] [Fintype Γ] [Fintype Q]
  [DecidableEq Γ] [DecidableEq Q] [LinearOrder (Compiler.Control.Sector S Γ Q)]
variable (A : Compiler.Simulator.Alphabet S Γ) (M : Compiler.Simulator.Machine Q Γ)
variable (hdecode : ∀ g a,A.output g=some a → g=A.input a)
variable (hr : Compiler.Word.Realizes A M (tableNormal T))

noncomputable def rawMap (hdecode : ∀ g a,A.output g=some a → g=A.input a)
    (hr : Compiler.Word.Realizes A M (tableNormal T)) : Mon T →ₙ* Compiler.Word.Presentation A M where
  toFun x := Compiler.Word.present A M (Compiler.Word.raw A.blank (representative T x))
  map_mul' x y := by
    have hb := fun n => (budget T wf good stable n).totalize
    have hc := fun n => Compiler.Word.Realizes.computesAt A M hr (budget T wf good stable n)
    apply (Compiler.Word.present_eq_iff_normal A M hdecode hb hc _ _).mpr
    change Compiler.Word.normal A M (fun w => Compiler.partValue (tableNormal T w))
      (Compiler.Word.raw A.blank (representative T (x*y))) =
      Compiler.Word.normal A M (fun w => Compiler.partValue (tableNormal T w))
      (Compiler.Word.raw A.blank (representative T x) ++
        Compiler.Word.raw A.blank (representative T y))
    rw [Compiler.Word.normal_raw,Compiler.Word.normal_raw_product,
      representative_mul T wf good stable]
    rfl

end Bootstrap.Quotient
end FiniteAlgebraicEnvelopes

namespace FiniteAlgebraicEnvelopes.Bootstrap

section
open Relation
variable {S : Type*}

namespace Static
variable {A Q : Type*} [Fintype A] [DecidableEq A] [DecidableEq S] [DecidableEq Q]
variable {r : A → A → Prop} [Std.Trichotomous r]
variable (C : BlockCode A S) (wf : WellFounded r) (q : List A → Option Q) (z : S)

omit [DecidableEq A] [DecidableEq Q] in
theorem canonical_no_infix (hc : ∀ n,Contextual q n) (hi : ∀ n,ZeroIdeal q n)
    {w : List A} (hw : q w≠none) {n : ℕ} {u v : List S}
    (hp : (u,v)∈table C wf q z n) : ¬ u <:+: C.encode (Canonical.least wf q w) := by
  obtain ⟨c,_,hcn,hn,rfl,rfl⟩ := (mem_table C wf q z).mp hp
  rintro ⟨x,y,he⟩
  obtain ⟨a,b,hab,hx,hy⟩ := C.occurrence_decode hcn he.symm
  have hq : q (a++c++b)=q w := hab ▸ Canonical.least_class wf q w
  by_cases hz : q c=none
  · exact hw (hq.symm.trans (hi _ a b c le_rfl hz))
  · have hlt : List.Shortlex r (Canonical.least wf q c) c := by
      rcases Canonical.least_lt_or_eq wf q c with h | h
      · exact h
      · exact False.elim (hn (by simp [output,hz,h]))
    have hb : (a++Canonical.least wf q c++b).length≤(a++c++b).length := by
      have hh := Canonical.least_length wf q c
      simp only [List.length_append]
      omega
    have hclass : q (a++Canonical.least wf q c++b)=q w :=
      (hc _ a b _ c hb le_rfl (Canonical.least_class wf q c)).trans hq
    apply Canonical.least_global_min wf q hclass
    rw [hab]
    exact shortlex_context hlt a b

omit [DecidableEq A] [DecidableEq Q] in
/-- Rules of the other code and selector/zero rules cannot occur in a pure code. -/
theorem canonical_irreducible {rs : List (List S × List S)} {n : ℕ}
    (hiso : ∀ p∈rs,p∈table C wf q z n ∨ ∃ s∈p.1,s∉C.Alphabet)
    (hc : ∀ k,Contextual q k) (hi : ∀ k,ZeroIdeal q k)
    {w : List A} (hw : q w≠none) :
    Irreducible (Step rs) (C.encode (Canonical.least wf q w)) := by
  apply irreducible_of_no_infix
  intro p hp hif
  rcases hiso p hp with hp | ⟨s,hs,hn⟩
  · exact canonical_no_infix C wf q z hc hi hw hp hif
  · exact hn (C.mem_alphabet (hif.subset hs))
end Static

namespace Quotient
variable [DecidableEq S]
variable (T : ℕ → Part (List (List S × List S)))
variable {t : S → S → Prop} (wt : WellFounded t)
  (good : ∀ n,GoodTable (r:=t) T n)
  (stable : ∀ k n,k≤n → ∀ rk∈T k,∀ rn∈T n,Selectors.BoundedEq rk rn k)
variable {A Q : Type*} [Fintype A] [DecidableEq A] [DecidableEq Q]
  {r : A → A → Prop} [Std.Trichotomous r]
variable (C : BlockCode A S) (wf : WellFounded r) (q : List A → Option Q) (z : S)
variable (hshort : ∀ n rs,rs∈T n → ∀ p∈rs,1<p.1.length)
variable (hiso : ∀ n rs,rs∈T n → ∀ p∈rs,p∈Static.table C wf q z n ∨ ∃ s∈p.1,s∉C.Alphabet)
variable (hstatic : ∀ n rs,rs∈T ((C.width+1)*n) → ∀ p∈Static.table C wf q z n,p∈rs)
variable (hc : ∀ n,Static.Contextual q n) (hi : ∀ n,Static.ZeroIdeal q n) (hzero : q []≠none)
include wt good stable hshort hiso hstatic hc hi hzero

omit [DecidableEq A] [DecidableEq Q] in
theorem normal_encode (w : List A) : normal T (C.encode w)=Static.output C wf q z w := by
  have hfixed : normal T (Static.output C wf q z w)=Static.output C wf q z w := by
    by_cases hq : q w=none
    · rw [Static.output,ite_eq_left hq]
      obtain ⟨rs,hrs,_⟩ := good 1
      exact normal_eq_self T wt good stable hrs
        (irreducible_of_short (fun p hp => hshort 1 rs hrs p hp))
    · rw [Static.output,ite_eq_right hq]
      obtain ⟨rs,hrs,_⟩ := good (C.encode (Canonical.least wf q w)).length
      exact normal_eq_self T wt good stable hrs
        (Static.canonical_irreducible C wf q z (hiso _ rs hrs) hc hi hq)
  have hpres : present T (C.encode w)=present T (Static.output C wf q z w) := by
    obtain ⟨rs,hrs,hd,_⟩ := good ((C.width+1)*w.length)
    exact present_steps T hrs hd (by rw [C.encode_length])
      (steps_mono (hstatic w.length rs hrs) (Static.whole_steps C wf q z hzero le_rfl))
  exact ((present_eq_iff T wt good stable _ _).mp hpres).trans hfixed

omit [DecidableEq A] [DecidableEq Q] in
theorem present_encode_iff (hz : z∉C.Alphabet) (u v : List A) :
    present T (C.encode u)=present T (C.encode v) ↔ q u=q v := by
  rw [present_eq_iff T wt good stable,
    normal_encode T wt good stable C wf q z hshort hiso hstatic hc hi hzero,
    normal_encode T wt good stable C wf q z hshort hiso hstatic hc hi hzero]
  exact Static.output_eq_iff C wf q z hz u v
end Quotient

namespace Selectors
variable [DecidableEq S] (a : Markers S)
theorem process_isolate {A Q : Type*} [Fintype A] [DecidableEq A] [DecidableEq Q]
    {r : A → A → Prop} [Std.Trichotomous r]
    (C : BlockCode A S) (wf : WellFounded r) (q : List A → Option Q)
    {rs : List (List S × List S)} {n : ℕ}
    (hbase : ∀ p∈rs,p∈Static.table C wf q a.zero n ∨ ∃ s∈p.1,s∉C.Alphabet)
    (hd : a.d∉C.Alphabet) (stages : ℕ → Stage S) (budget j : ℕ)
    {p : List S × List S} (hp : p∈process (a:=a) rs stages budget j) :
    p∈Static.table C wf q a.zero n ∨ ∃ s∈p.1,s∉C.Alphabet := by
  rcases process_members hp with hp | ⟨i,_,hp⟩
  · exact hbase p hp
  · obtain ⟨w,_,he,_⟩ := (mem_rules a).mp hp
    exact Or.inr ⟨a.d,by simp [he,Markers.wrap,Envelopes.frame],hd⟩
end Selectors

end

variable {S : Type*}

namespace Static
variable {A Q : Type*} [Fintype A] [DecidableEq A] [DecidableEq S] [DecidableEq Q]
variable {r : A → A → Prop} [Std.Trichotomous r]
variable (C : BlockCode A S) (wf : WellFounded r) (q : List A → Option Q) (zero sep : S)

omit [DecidableEq A] [DecidableEq Q] in
theorem separator_irreducible (hs : sep∉C.Alphabet)
    {rs : List (List S × List S)} {n : ℕ}
    (hiso : ∀ p∈rs,p∈table C wf q zero n ∨ ∃ b∈p.1,b∉C.Alphabet ∧ b≠sep)
    (hc : ∀ k,Contextual q k) (hi : ∀ k,ZeroIdeal q k)
    {u v : List A} (hu : q u≠none) (hv : q v≠none) :
    Irreducible (Step rs)
      (C.encode (Canonical.least wf q u)++sep::C.encode (Canonical.least wf q v)) := by
  apply irreducible_of_no_infix
  intro p hp hif
  rcases hiso p hp with hp | ⟨b,hb,hbc,hbs⟩
  · have hs' : sep∉p.1 := fun hh => hs ((table_support C wf q zero hp).2 sep hh)
    rcases Separator.infix_split hs' hif with hif | hif
    · exact canonical_no_infix C wf q zero hc hi hu hp hif
    · exact canonical_no_infix C wf q zero hc hi hv hp hif
  · have hh := hif.subset hb
    simp only [List.mem_append,List.mem_cons] at hh
    rcases hh with hh | hh | hh
    · exact hbc (C.mem_alphabet hh)
    · exact hbs hh
    · exact hbc (C.mem_alphabet hh)

end Static

namespace Selectors
variable [DecidableEq S] (a : Markers S)
theorem process_isolate_separator {A Q : Type*} [Fintype A] [DecidableEq A] [DecidableEq Q]
    {r : A → A → Prop} [Std.Trichotomous r]
    (C : BlockCode A S) (wf : WellFounded r) (q : List A → Option Q) (sep : S)
    {rs : List (List S × List S)} {n : ℕ}
    (hbase : ∀ p∈rs,p∈Static.table C wf q a.zero n ∨ ∃ b∈p.1,b∉C.Alphabet ∧ b≠sep)
    (hd : a.d∉C.Alphabet) (hds : a.d≠sep) (stages : ℕ → Stage S) (budget j : ℕ)
    {p : List S × List S} (hp : p∈process (a:=a) rs stages budget j) :
    p∈Static.table C wf q a.zero n ∨ ∃ b∈p.1,b∉C.Alphabet ∧ b≠sep := by
  rcases process_members hp with hp | ⟨i,_,hp⟩
  · exact hbase p hp
  · obtain ⟨w,_,he,_⟩ := (mem_rules a).mp hp
    exact Or.inr ⟨a.d,by simp [he,Markers.wrap,Envelopes.frame],hd,hds⟩
end Selectors

namespace Quotient
variable [DecidableEq S]
variable (T : ℕ → Part (List (List S × List S)))
variable {t : S → S → Prop} (wt : WellFounded t)
  (good : ∀ n,GoodTable (r:=t) T n)
  (stable : ∀ k n,k≤n → ∀ rk∈T k,∀ rn∈T n,Selectors.BoundedEq rk rn k)
variable {A Q : Type*} [Fintype A] [DecidableEq A] [DecidableEq Q]
  {r : A → A → Prop} [Std.Trichotomous r]
variable (C : BlockCode A S) (wf : WellFounded r) (q : List A → Option Q) (zero sep : S)
variable (hshort : ∀ n rs,rs∈T n → ∀ p∈rs,1<p.1.length)
variable (hiso : ∀ n rs,rs∈T n → ∀ p∈rs,p∈Static.table C wf q zero n ∨ ∃ b∈p.1,b∉C.Alphabet ∧ b≠sep)
variable (hstatic : ∀ n rs,rs∈T ((C.width+1)*n) → ∀ p∈Static.table C wf q zero n,p∈rs)
variable (hc : ∀ n,Static.Contextual q n) (hi : ∀ n,Static.ZeroIdeal q n) (hzero : q []≠none)
variable (hs : sep∉C.Alphabet)
include wt good stable hshort hiso hstatic hc hi hzero hs

omit [DecidableEq A] [DecidableEq Q] in
theorem normal_separator {u v : List A} (hu : q u≠none) (hv : q v≠none) :
    normal T (C.encode u++sep::C.encode v)=
      C.encode (Canonical.least wf q u)++sep::C.encode (Canonical.least wf q v) := by
  have hcode (w : List A) (hw : q w≠none) :
      normal T (C.encode w)=C.encode (Canonical.least wf q w) := by
    rw [normal_encode T wt good stable C wf q zero hshort
      (fun n rs hrs p hp => (hiso n rs hrs p hp).imp id (by rintro ⟨b,hb,hbc,_⟩; exact ⟨b,hb,hbc⟩))
      hstatic hc hi hzero,Static.output,ite_eq_right hw]
  have hleft : normal T (C.encode u++sep::C.encode v)=
      normal T (normal T (C.encode u)++sep::C.encode v) := by
    simpa only [List.nil_append] using
      (normal_context T wt good stable [] (C.encode u) (sep::C.encode v)).symm
  have hright : normal T (normal T (C.encode u)++sep::C.encode v)=
      normal T (normal T (C.encode u)++sep::normal T (C.encode v)) := by
    simpa only [List.append_nil,List.append_assoc,List.singleton_append] using
      (normal_context T wt good stable (normal T (C.encode u)++[sep]) (C.encode v) []).symm
  rw [hleft,hright,hcode u hu,hcode v hv]
  obtain ⟨rs,hrs,_⟩ := good
    (C.encode (Canonical.least wf q u)++sep::C.encode (Canonical.least wf q v)).length
  exact normal_eq_self T wt good stable hrs
    (Static.separator_irreducible C wf q zero sep hs (hiso _ rs hrs) hc hi hu hv)

omit [DecidableEq A] [DecidableEq Q] in
theorem present_separator_ne_zero (hz : zero∉C.Alphabet) (hzs : zero≠sep)
    {u v : List A} (hu : q u≠none) (hv : q v≠none) :
    present T (C.encode u++sep::C.encode v)≠present T [zero] := by
  intro he
  have hn := (present_eq_iff T wt good stable _ _).mp he
  rw [normal_separator T wt good stable C wf q zero sep hshort hiso hstatic hc hi hzero hs hu hv] at hn
  obtain ⟨rs,hrs,_⟩ := good 1
  have hz0 : normal T [zero]=[zero] := normal_eq_self T wt good stable hrs
    (irreducible_of_short (fun p hp => hshort 1 rs hrs p hp))
  rw [hz0] at hn
  have hm : zero∈C.encode (Canonical.least wf q u)++sep::C.encode (Canonical.least wf q v) := by
    rw [hn]; simp
  simp only [List.mem_append,List.mem_cons] at hm
  rcases hm with hm | hm | hm
  · exact hz (C.mem_alphabet hm)
  · exact hzs hm
  · exact hz (C.mem_alphabet hm)
end Quotient

end FiniteAlgebraicEnvelopes.Bootstrap

namespace FiniteAlgebraicEnvelopes
namespace Effect
variable {X A B : Type*} [Primcodable X] [Primcodable A] [Primcodable B]

/-- Finite traversal of a total computable family is a computable list map. -/
theorem computable_map_parameter {f : X → A → B} (hf : Computable₂ f) :
    Computable₂ (fun x (l : List A) => l.map (f x)) := by
  apply (partrec_traverse_parameter hf.partrec₂).of_eq_tot
  intro p
  exact Bootstrap.Search.traverse_map _ _ _ (fun a _ => Part.mem_some _)
end Effect

namespace Bootstrap.Canonical
variable {A Q : Type*} [Fintype A] [Primcodable A]
  {r : A → A → Prop} [DecidableRel (List.Shortlex r)] [Std.Trichotomous r]
  (wf : WellFounded r) (q : List A → Q)

/-- Canonical representatives do not require a coding of the semantic class
    type. Only its word-equivalence test must be algorithmic. -/
theorem computable_least (hr : PrimrecRel (List.Shortlex r))
    (hq : ComputablePred (fun p : List A × List A => q p.1=q p.2)) : Computable (least wf q) := by
  classical
  let e (w v : List A) : Option Bool := some (decide (q v=q w))
  have he : Computable₂ e := (Primrec.option_some.to_comp.comp (hq.decide.comp (Computable.snd.pair Computable.fst))).to₂
  let ps (w : List A) := (Static.words A w.length).map (fun v => (v,e w v))
  have hp : Computable ps :=
    (Effect.computable_map_parameter (Computable.snd.pair he).to₂).comp
      Computable.id (Search.primrec_words.to_comp.comp Primrec.list_length.to_comp)
  have hc : Computable (fun w => pick (r:=r) (ps w) w (some true)) :=
    ((Search.primrec_pick (Q:=Bool) hr Primrec.snd Primrec.fst (Primrec.const (some true))).to_comp.comp
      (Computable.id.pair hp))
  apply hc.of_eq
  intro w
  have hew : e w w=some true := by simp [e]
  have heq : least wf (e w) w=least wf q w := by
    apply (eq_least_iff wf q).mpr
    refine ⟨least_length wf (e w) w,?_,?_⟩
    · have hh := least_class wf (e w) w
      simpa [e] using hh
    · intro v hv hh
      apply least_min wf (e w) hv
      simp [e,hh]
  rw [← hew]
  rw [pick_eq_least wf (e w) (fun p hp => by
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp hp
    rfl)]
  · exact heq
  · apply List.mem_map.mpr
    refine ⟨least wf (e w) w,(Static.mem_words _ _).mpr (least_length wf (e w) w),?_⟩
    simp only [Prod.mk.injEq,true_and]
    exact least_class wf (e w) w

end Bootstrap.Canonical

end FiniteAlgebraicEnvelopes

namespace FiniteAlgebraicEnvelopes.WordProblem

variable {G : Type*} [Group G] {n : ℕ} (s : Fin n → G)

 attribute [local instance] OAI.FiniteAlgebraicEnvelopes.WordProblem.instTrichotomousProdFinBoolLetterRel
theorem computable_testedClass (h : ComputablePred (fun w : Word n => evalWord s w=1)) :
    Computable (testedClass s) := by
  classical
  exact Bootstrap.Canonical.computable_least (letterRel_wf n) (evalWord s)
    (primrec_letterShortlex n) (computable_word_equiv s h)

end FiniteAlgebraicEnvelopes.WordProblem

end OAI
end

section
-- module Solutions.OAIFAE.PartialAffine
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Primitive recursive dyadic partial affine monoid and its six-letter presentation.
-/

namespace FiniteAlgebraicEnvelopes.PartialAffine

 theorem computable_testedClass : Computable testedClass := by
  classical
  apply Bootstrap.Canonical.computable_least
  · exact Bootstrap.Search.primrec_shortlex ⟨inferInstance,Primrec.dom_finite _⟩
  · exact ⟨inferInstance,primrec_word_equivalence.decide.to_comp⟩

end FiniteAlgebraicEnvelopes.PartialAffine

end OAI
end

section
-- module Solutions.OAIFAE.UniformPaths
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Uniform surface and path normalization with recursive compiler interfaces.
-/

namespace FiniteAlgebraicEnvelopes.Compiler.Path.Uniform
open FiniteAlgebraicEnvelopes.Compiler.Path HeadCodec FiniteAlgebraicEnvelopes.Effect
open scoped HeadCodec
variable {C H : Type*} [Primcodable C] [Primcodable H]

theorem primrec_typeOf : Primrec (typeOf (C := C) (H := H)) := by
  let f : Fin 3 → Shape := fun k => if k=0 then .zero else if k=1 then .path .outer .left else .path .right .outer
  exact ((primrec_sumElim (Primrec.dom_finite f)
    (primrec_sumElim (Primrec.const (Shape.path .left .left))
      (primrec_sumElim (Primrec.const (Shape.path .right .right)) (Primrec.const (Shape.path .left .right))))).comp
        primrec_pathCode).of_eq fun a => by cases a <;> rfl

theorem primrec_shape : Primrec (shape (C := C) (H := H)) := by
  have hp : Primrec (fun p : Letter C H × Shape => typeOf p.1 * p.2) :=
    (Primrec.dom_finite (fun p : Shape × Shape => p.1*p.2)).comp
      ((primrec_typeOf.comp Primrec.fst).pair Primrec.snd)
  exact (Primrec.list_foldr Primrec.id (Primrec.const Shape.unit)
    (hp.comp Primrec.snd).to₂).of_eq fun w => by
      induction w with
      | nil => rfl
      | cons a w ih => simpa only [id_eq,List.foldr_cons,shape_cons] using congrArg (typeOf a * ·) ih

end FiniteAlgebraicEnvelopes.Compiler.Path.Uniform

namespace FiniteAlgebraicEnvelopes.Compiler
open HeadCodec FiniteAlgebraicEnvelopes.Effect
open scoped HeadCodec

namespace Word.Uniform
variable {P S Γ Q : Type*} [Fintype S] [Fintype Γ] [Primcodable Q] [Primcodable P] [Primcodable S]
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
variable (blank : Γ) (rep : P × Control.Sector S Γ Q → Control.Sector S Γ Q)

theorem partrec_partialNormal (hrep : Primrec rep)
    {f : P × List S → Part (List S)} (hf : Partrec f) :
    Partrec (partialNormal blank rep f) := by
  have hp : Primrec (fun x : P × List (Letter S Γ Q) =>
      (preprocess blank rep x).map (classify blank)) :=
    Primrec.list_map (primrec_preprocess blank rep hrep) ((primrec_classify blank).comp Primrec.snd).to₂
  have hr : Primrec (fun w : List (Item S Γ Q) => w.flatMap (realize blank)) :=
    Primrec.list_flatMap Primrec.id ((primrec_realize blank).comp Primrec.snd).to₂
  have hb : Partrec (fun x : P × List (Letter S Γ Q) =>
      (RawRuns.partialSource (fun w => f (x.1,w)) ((preprocess blank rep x).map (classify blank))).map
        (List.flatMap (realize blank))) :=
    ((RawRuns.Uniform.partrec_partialSource hf).comp (Computable.fst.pair hp.to_comp)).map
      (hr.to_comp.comp Computable.snd).to₂
  have ho : Primrec (fun x : P × List (Letter S Γ Q) =>
      if Path.shape x.2 = .zero then none else some x) :=
    Primrec.ite (Primrec.eq.comp (Path.Uniform.primrec_shape.comp Primrec.snd) (Primrec.const Path.Shape.zero))
      (Primrec.const none) Primrec.option_some
  exact (Partrec.optionCasesOn_right ho.to_comp (Computable.const [Path.Letter.zero])
    (hb.comp Computable.snd).to₂).of_eq fun x => by
      by_cases h : Path.shape x.2 = .zero <;> simp [h,partialNormal]

end Word.Uniform
end FiniteAlgebraicEnvelopes.Compiler

namespace FiniteAlgebraicEnvelopes.MachineRealization.ParameterCode

section
open Compiler Compiler.Simulator Compiler.HeadCodec ParameterMachine
open scoped Compiler.HeadCodec
variable {S T Γ Q : Type*} [Fintype T] [Fintype Γ] [Fintype Q]
  [DecidableEq T] [DecidableEq Γ] [DecidableEq Q]
  [Primcodable T] [Primcodable Γ] [Primcodable Q]
variable (A : Alphabet S Γ) (M : Machine Q Γ) (p : S) (B : Alphabet T (Bool×Γ))

theorem partrec_codedNormal {f : ℕ × List T → Part (List T)} (hf : Partrec f) :
    Partrec (codedNormal A M p B f) :=
  Compiler.Word.Uniform.partrec_partialNormal B.blank _ (primrec_codedRepresentative A M p B) hf

end

open Compiler Compiler.HeadCodec ParameterMachine
open scoped Compiler.HeadCodec

end FiniteAlgebraicEnvelopes.MachineRealization.ParameterCode

end OAI
end

section
-- module Solutions.OAIFAE.SelfReference
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Controlled shorter-input evaluator calls, fixed points, totality, and tested-class realization.
-/

namespace FiniteAlgebraicEnvelopes.Bootstrap

namespace Tested
open Compiler Compiler.Simulator MachineRealization MachineRealization.ParameterCode
open scoped Compiler.HeadCodec

variable {S T Γ Q : Type*} [Fintype T] [Fintype Γ] [Fintype Q]
  [DecidableEq T] [DecidableEq Γ] [DecidableEq Q]
  [Primcodable T] [Primcodable Γ] [Primcodable Q]
variable (A : Alphabet S Γ) (M : Machine Q Γ) (p : S) (B : Alphabet T (Bool×Γ))

 theorem partrec_family {f : ℕ × List T → Part (List T)} (hf : Partrec f) :
    Partrec₂ (family A M p B f) := by
  have hh : Partrec (fun x : ℕ × List (Y T Γ Q) =>
      codedNormal A M p B f (x.1,Projection.left x.2)) :=
    (partrec_codedNormal A M p B hf).comp
    (Computable.fst.pair ((Projection.primrec_left (A:=X T Γ Q) (B:=PartialAffine.Letter)).to_comp.comp Computable.snd))
  exact (hh.map (primrec_combine.to_comp.comp
    (Computable.snd.pair (PartialAffine.computable_testedClass.comp
      (Projection.primrec_right.to_comp.comp (Computable.snd.comp Computable.fst))))).to₂).to₂

end Tested
end FiniteAlgebraicEnvelopes.Bootstrap

namespace FiniteAlgebraicEnvelopes.Bootstrap.Rank
variable {P A B C : Type*} [DecidableEq A]

variable [Primcodable P] [Primcodable A]

 theorem primrec_less (ls : P → List A) (hls : Primrec ls) :
    Primrec (fun x : P × List A × List A => less (ls x.1) x.2.1 x.2.2) := by
  classical
  exact (Search.primrec_shortlex Primrec.nat_lt).decide.comp
    (primrec_word.comp (hls.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
    (primrec_word.comp (hls.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))

end FiniteAlgebraicEnvelopes.Bootstrap.Rank

namespace FiniteAlgebraicEnvelopes.Bootstrap.Source
open Compiler Compiler.Simulator MachineRealization
open scoped Compiler.HeadCodec

variable {G : Type*} [Group G] {k : ℕ} (s : Fin k → G)
variable {Γ Q : Type*} [Fintype Γ] [Fintype Q] [DecidableEq Γ] [DecidableEq Q]
  [Primcodable Γ] [Primcodable Q]
variable (A : Alphabet (Sigma ⊕ Unit) Γ) (M : Machine Q Γ)

 theorem partrec_testT : Partrec₂ (testT A M) :=
  Tested.partrec_family A M (.inr ()) (UniversalMachine.restrict (ParameterMachine.alphabet A)) partrec_raw

 attribute [local instance] OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.instDecidableEqXSigma
theorem partrec_tables (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word k => FiniteAlgebraicEnvelopes.evalWord s w=1)) :
    Partrec₂ (tables s A M) := by
  have hg : Partrec₂ (testG s) :=
    (Primrec.option_some.to_comp.comp ((WordProblem.computable_testedClass s h).comp Computable.snd)).partrec
  exact Uniform.partrec_tables markers yLetters (fun _ => zLetters k)
    codeT (codeG (Γ:=Γ) (Q:=Q)) (fun n => Rank.less (yLetters n)) (fun _ => Rank.less (zLetters k))
    (fun n => width (Γ:=Γ) (Q:=Q) k n+1) (fun n => width (Γ:=Γ) (Q:=Q) k n+1) (testT A M) (testG s)
    Tested.primrec_letters (Primrec.const _) primrec_codeT primrec_codeG
    (Rank.primrec_less _ Tested.primrec_letters) (Rank.primrec_less _ (Primrec.const _))
    (Primrec.nat_add.comp primrec_width (Primrec.const 1))
    (Primrec.nat_add.comp primrec_width (Primrec.const 1)) (partrec_testT A M) hg

/-- Literal source fixed point. No termination or contextual correctness is
    assumed: equality here also preserves divergence of the two procedures. -/
 theorem exists_fixed_point (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word k => FiniteAlgebraicEnvelopes.evalWord s w=1)) :
    ∃ n,raw n=tableNormal (tables s A M n) := by
  have hh := partrec_tableNormal_parameter (partrec_tables s A M h)
  have hc : Partrec₂ (fun c : Nat.Partrec.Code => tableNormal (tables s A M (Encodable.encode c))) :=
    hh.comp (Computable.encode.comp Computable.fst) Computable.snd
  obtain ⟨c,hc⟩ := WordProgramming.fixed_point hc
  exact ⟨Encodable.encode c,(raw_encode c).trans hc⟩

end FiniteAlgebraicEnvelopes.Bootstrap.Source

end OAI
end

section
-- module Solutions.OAIFAE.MonoidAlgebras
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Finite compiler monoids, zero products, both F₂ algebras, and selector constructions.
-/

namespace FiniteAlgebraicEnvelopes.Bootstrap.Source

section
open Compiler Compiler.Simulator MachineRealization
variable {Γ Q : Type*} [Fintype Γ] [Fintype Q] [DecidableEq Γ] [DecidableEq Q]
  [Primcodable Γ] [Primcodable Q]
variable {G : Type*} [Group G] {k : ℕ} (s : Fin k → G)
variable (A : Alphabet (Sigma ⊕ Unit) Γ) (M : Machine Q Γ)

omit [Primcodable Γ] in
 theorem all_budgets (n : ℕ) (fixed : raw n=tableNormal (tables s A M n))
    (hr : Word.Realizes (terminalAlphabet A) (terminalMachine A M n) (raw n))
    (hd : ∀ g a,(terminalAlphabet A).output g=some a → g=(terminalAlphabet A).input a) :
    ∀ j, GoodTable (r:=fun a b : Sigma => a<b) (tables s A M n) j ∧ PartialBudget (raw n) j := by
  apply bootstrap_length_induction (r:=fun a b : Sigma => a<b)
    (InvImage.wf Fin.val Nat.lt_wfRel.wf) (tables s A M n) (raw n) fixed
  · intro j m hjm rk hrk rn hrn
    exact stable s A M n hjm hrk hrn
  · intro j ih
    have ht :
        (∀ w : List (FiniteY (Γ:=Γ) (Q:=Q) n),w.length≤j/(width (Γ:=Γ) (Q:=Q) k n+1) → (finiteTest A M n w).Dom) ∧
          Search.value (finiteTest A M n) []≠none ∧
          Static.Contextual (Search.value (finiteTest A M n)) (j/(width (Γ:=Γ) (Q:=Q) k n+1)) ∧
          Static.ZeroIdeal (Search.value (finiteTest A M n)) (j/(width (Γ:=Γ) (Q:=Q) k n+1)) := by
      rcases Nat.eq_zero_or_pos j with rfl|hj
      · simpa using tests_zero A M n
      · exact tests_bounded A M n _ (ih _ (quota_smaller k n j hj)) hr hd
    have hg := group_tests s n (j/(width (Γ:=Γ) (Q:=Q) k n+1))
    exact good_of_tests s A M n j ht.1 ht.2.1 ht.2.2.1 ht.2.2.2 hg.1 hg.2.1 hg.2.2

 theorem exists_total_fixed_point
    (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word k => evalWord s w=1))
    (hr : ∀ n, Word.Realizes (terminalAlphabet A) (terminalMachine A M n) (raw n))
    (hd : ∀ g a,(terminalAlphabet A).output g=some a → g=(terminalAlphabet A).input a) :
    ∃ n, raw n=tableNormal (tables s A M n) ∧
      ∀ j, GoodTable (r:=fun a b : Sigma => a<b) (tables s A M n) j ∧ PartialBudget (raw n) j := by
  obtain ⟨n,hn⟩ := exists_fixed_point s A M h
  exact ⟨n,hn,all_budgets s A M n hn (hr n) hd⟩

end

section
open Compiler Compiler.Simulator MachineRealization

attribute [instance] Family.finiteΓ Family.finiteQ Family.decΓ Family.decQ Family.codeΓ Family.codeQ

variable {G : Type*} [Group G] {k : ℕ} (s : Fin k → G)
 theorem source_bootstrap
    (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word k => evalWord s w=1)) :
    ∃ n, raw n=tableNormal (tables s family.A family.M n) ∧
      ∀ j, GoodTable (r:=fun a b : Sigma => a<b) (tables s family.A family.M n) j ∧ PartialBudget (raw n) j :=
  exists_total_fixed_point s family.A family.M h family.realizes family.decode

end

open Compiler Compiler.Simulator MachineRealization
open scoped Compiler.HeadCodec
variable {Γ Q : Type*} [Fintype Γ] [Fintype Q] [DecidableEq Γ] [DecidableEq Q]
  [Primcodable Γ] [Primcodable Q]
variable {G : Type*} [Group G] {k : ℕ} (s : Fin k → G)
variable (A : Alphabet (Sigma ⊕ Unit) Γ) (M : Machine Q Γ)

attribute [local instance] OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.instDecidableEqXSigma_5
attribute [local instance] OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.instFintypeLetterSigmaProdBoolState_2
omit [Primcodable Γ] in
 theorem tables_members (n j : ℕ) {rs : List (List Sigma × List Sigma)} (hrs : rs∈tables s A M n j) :
    RulesEq rs (Selectors.process (a:=markers) (base s A M n j) (Selectors.stages markers.zero) j j) := by
  rw [tables_eq_finite] at hrs
  exact Uniform.tables_members_support markers (finiteCodeT (Γ:=Γ) (Q:=Q) k n) (finiteCodeG (Γ:=Γ) (Q:=Q) k n)
    (wf_relT n) (wf_relG k) (finiteLetters n) (zLetters k) (mem_finiteLetters n)
    (by intro x; simp [zLetters,Static.letters]) (finiteTest A M n) (testG s n) hrs

omit [Primcodable Γ] in
 theorem tables_absorb (n j : ℕ) {rs : List (List Sigma × List Sigma)} (hrs : rs∈tables s A M n j) :
    Absorbs rs markers.zero := by
  have hh := Selectors.process_contains (a:=markers) (base s A M n j) (Selectors.stages markers.zero) j j
  have hz := Base.absorbs (finiteCodeT (Γ:=Γ) (Q:=Q) k n) (finiteCodeG (Γ:=Γ) (Q:=Q) k n)
    (wf_relT n) (wf_relG k) (Search.value (finiteTest A M n)) (Search.value (testG s n)) markers.zero j
  intro b
  exact ⟨(tables_members s A M n j hrs _).mpr (hh _ (hz b).1),
    (tables_members s A M n j hrs _).mpr (hh _ (hz b).2)⟩

omit [Primcodable Γ] in
 theorem tables_short (n j : ℕ) {rs : List (List Sigma × List Sigma)} (hrs : rs∈tables s A M n j) :
    ∀ p∈rs,1<p.1.length := by
  intro p hp
  have hp := (tables_members s A M n j hrs p).mp hp
  rcases Selectors.process_members hp with hp | ⟨i,hi,hp⟩
  · rcases (Base.mem_table _ _ (wf_relT n) (wf_relG k) _ _ markers.zero).mp hp with hp|hp|hp
    · obtain ⟨b,(he|he),_⟩ := (Base.mem_absorption markers.zero).mp hp <;> rw [he] <;> simp
    · apply Static.table_short _ (wf_relT n) _ _ _ hp
      change 1<width (Γ:=Γ) (Q:=Q) k n+1
      unfold width; omega
    · apply Static.table_short _ (wf_relG k) _ _ _ hp
      change 1<width (Γ:=Γ) (Q:=Q) k n+1
      unfold width; omega
  · obtain ⟨w,_,he,_⟩ := (Selectors.mem_rules markers).mp hp
    rw [he]
    simp only [Selectors.Markers.wrap,Envelopes.length_frame]
    omega

attribute [local instance] OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.instDecidableEqFiniteY_4
omit [Primcodable Γ] in
 theorem tables_isolateT (n j : ℕ) {rs : List (List Sigma × List Sigma)} (hrs : rs∈tables s A M n j) :
    ∀ p∈rs,p∈Static.table (finiteCodeT (Γ:=Γ) (Q:=Q) k n) (wf_relT n)
      (Search.value (finiteTest A M n)) markers.zero j ∨ ∃ b∈p.1,b∉(finiteCodeT (Γ:=Γ) (Q:=Q) k n).Alphabet := by
  intro p hp
  apply Selectors.process_isolate markers _ (wf_relT n) (Search.value (finiteTest A M n))
    (fun p hp => Base.isolate_left (finiteCodeT (Γ:=Γ) (Q:=Q) k n) (finiteCodeG (Γ:=Γ) (Q:=Q) k n) (wf_relT n) (wf_relG k) (Search.value (finiteTest A M n)) (Search.value (testG s n)) markers.zero
      (codeT_avoid (Γ:=Γ) (Q:=Q) k n _ (by simp)) (codes_disjoint (Γ:=Γ) (Q:=Q) k n) hp)
    (codeT_avoid (Γ:=Γ) (Q:=Q) k n _ (by simp)) _ _ _
  exact (tables_members s A M n j hrs p).mp hp

omit [Primcodable Γ] in
 theorem tables_staticT (n j : ℕ) {rs : List (List Sigma × List Sigma)}
    (hrs : rs∈tables s A M n ((width (Γ:=Γ) (Q:=Q) k n+1)*j)) :
    ∀ p∈Static.table (finiteCodeT (Γ:=Γ) (Q:=Q) k n) (wf_relT n)
      (Search.value (finiteTest A M n)) markers.zero j,p∈rs := by
  intro p hp
  apply (tables_members s A M n _ hrs p).mpr
  apply Selectors.process_contains
  apply (Base.mem_table _ _ (wf_relT n) (wf_relG k) _ _ markers.zero).mpr
  apply Or.inr; apply Or.inl
  change p∈Static.table (finiteCodeT (Γ:=Γ) (Q:=Q) k n) (wf_relT n)
    (Search.value (finiteTest A M n)) markers.zero (((width (Γ:=Γ) (Q:=Q) k n+1)*j)/(width (Γ:=Γ) (Q:=Q) k n+1))
  simpa using hp

omit [Primcodable Γ] in
 theorem tables_isolateG (n j : ℕ) {rs : List (List Sigma × List Sigma)} (hrs : rs∈tables s A M n j) :
    ∀ p∈rs,p∈Static.table (finiteCodeG (Γ:=Γ) (Q:=Q) k n) (wf_relG k)
      (Search.value (testG s n)) markers.zero j ∨ ∃ b∈p.1,b∉(finiteCodeG (Γ:=Γ) (Q:=Q) k n).Alphabet := by
  intro p hp
  apply Selectors.process_isolate markers _ (wf_relG k) (Search.value (testG s n)) ?_
    (codeG_avoid (Γ:=Γ) (Q:=Q) k n _ (by simp)) _ _ _ ((tables_members s A M n j hrs p).mp hp)
  intro p hp
  rcases (Base.mem_table _ _ (wf_relT n) (wf_relG k) _ _ markers.zero).mp hp with hp | hp | hp
  · obtain ⟨b,hb,_⟩ := (Base.mem_absorption markers.zero).mp hp
    exact Or.inr ⟨markers.zero,by rcases hb with h|h <;> simp [h],codeG_avoid (Γ:=Γ) (Q:=Q) k n _ (by simp)⟩
  · obtain ⟨hn,hs⟩ := Static.table_support _ (wf_relT n) _ _ hp
    obtain ⟨b,hb⟩ := List.exists_mem_of_ne_nil _ hn
    exact Or.inr ⟨b,hb,fun hc => Set.disjoint_left.mp (codes_disjoint (Γ:=Γ) (Q:=Q) k n) (hs b hb) hc⟩
  · exact Or.inl (Static.table_mono _ (wf_relG k) _ _ (Nat.div_le_self j _) hp)

omit [Primcodable Γ] in
 theorem tables_staticG (n j : ℕ) {rs : List (List Sigma × List Sigma)}
    (hrs : rs∈tables s A M n ((width (Γ:=Γ) (Q:=Q) k n+1)*j)) :
    ∀ p∈Static.table (finiteCodeG (Γ:=Γ) (Q:=Q) k n) (wf_relG k)
      (Search.value (testG s n)) markers.zero j,p∈rs := by
  intro p hp
  apply (tables_members s A M n _ hrs p).mpr
  apply Selectors.process_contains
  apply (Base.mem_table _ _ (wf_relT n) (wf_relG k) _ _ markers.zero).mpr
  apply Or.inr; apply Or.inr
  change p∈Static.table (finiteCodeG (Γ:=Γ) (Q:=Q) k n) (wf_relG k)
    (Search.value (testG s n)) markers.zero (((width (Γ:=Γ) (Q:=Q) k n+1)*j)/(width (Γ:=Γ) (Q:=Q) k n+1))
  simpa using hp

end FiniteAlgebraicEnvelopes.Bootstrap.Source

namespace FiniteAlgebraicEnvelopes.Bootstrap.Source
open Compiler Compiler.Simulator MachineRealization
variable {G : Type*} [Group G] {k : ℕ} (s : Fin k → G)
variable (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word k => evalWord s w=1))

noncomputable def index : ℕ := (source_bootstrap s h).choose
abbrev processor := tables s family.A family.M (index s h)

theorem index_fixed : raw (index s h)=tableNormal (processor s h) := (source_bootstrap s h).choose_spec.1

theorem index_good (j : ℕ) : GoodTable (r:=fun a b : Sigma => a<b) (processor s h) j :=
  ((source_bootstrap s h).choose_spec.2 j).1

theorem index_budget (j : ℕ) : PartialBudget (raw (index s h)) j :=
  ((source_bootstrap s h).choose_spec.2 j).2

theorem index_stable : ∀ j m : ℕ, j ≤ m → ∀ rs∈processor s h j,∀ rt∈processor s h m,Selectors.BoundedEq rs rt j := by
  intro j m hjm rs hrs rt hrt
  exact stable s family.A family.M (index s h) hjm hrs hrt

abbrev H := Quotient.Mon (processor s h)

noncomputable instance hMonoidWithZero : MonoidWithZero (H s h) :=
  Quotient.monoidWithZero (processor s h) markers.zero (index_good s h 2).choose_spec.1
    (tables_absorb s family.A family.M (index s h) 2 (index_good s h 2).choose_spec.1)

theorem zero_H : (0 : H s h)=Quotient.present (processor s h) [markers.zero] := rfl

 theorem group_code_eq_iff (u v : List (Z k)) :
    Quotient.present (processor s h) ((finiteCodeG (Γ:=family.Γ) (Q:=family.Q) k (index s h)).encode u)=
      Quotient.present (processor s h) ((finiteCodeG (Γ:=family.Γ) (Q:=family.Q) k (index s h)).encode v) ↔
        evalWord s u=evalWord s v := by
  have hh := Quotient.present_encode_iff (processor s h) wf_sigma (index_good s h) (index_stable s h)
    (finiteCodeG (Γ:=family.Γ) (Q:=family.Q) k (index s h)) (wf_relG k)
    (Search.value (testG s (index s h))) markers.zero
    (fun j rs hrs => tables_short s family.A family.M (index s h) j hrs)
    (fun j rs hrs => tables_isolateG s family.A family.M (index s h) j hrs)
    (fun j rs hrs => tables_staticG s family.A family.M (index s h) j hrs)
    (fun j => (group_tests s (index s h) j).2.1)
    (fun j => (group_tests s (index s h) j).2.2)
    (group_tests s (index s h) 0).1
    (codeG_avoid (Γ:=family.Γ) (Q:=family.Q) k (index s h) _ (by simp)) u v
  simpa only [group_search_value,Option.some.injEq,WordProblem.testedClass_eq_iff] using hh

noncomputable def groupEmbedding (hs : Subgroup.closure (Set.range s)=⊤) : G →* H s h :=
  Quotient.descendCode (finiteCodeG (Γ:=family.Γ) (Q:=family.Q) k (index s h)) (groupEval s)
    (groupEval_surjective s hs) (group_code_eq_iff s h)

abbrev KMachine := terminalMachine family.A family.M (index s h)
abbrev K := Word.Presentation KAlphabet (KMachine s h)

local instance instLinearOrderSectorSigmaProdBoolΓFamilyStateQIndex : LinearOrder (Control.Sector Sigma (Bool × family.Γ) (ParameterMachine.State family.Q (index s h))) :=
  Effect.codeOrder _

noncomputable instance kMonoidWithZero : MonoidWithZero (K s h) := Word.monoidWithZero KAlphabet (KMachine s h)

theorem zero_K : (0 : K s h)=Word.present KAlphabet (KMachine s h) [.zero] := rfl

theorem realizes_processor : Word.Realizes KAlphabet (KMachine s h) (tableNormal (processor s h)) :=
  index_fixed s h ▸ family.realizes (index s h)

noncomputable def copyEmbedding : H s h →ₙ* K s h :=
  Quotient.rawMap (processor s h) wf_sigma (index_good s h) (index_stable s h)
    KAlphabet (KMachine s h) family.decode (realizes_processor s h)

instance hFG : Monoid.FG (H s h) :=
  Monoid.fg_of_surjective (PresentedMonoid.mk (Quotient.Rel (processor s h))) PresentedMonoid.surjective_mk

instance kFG : Monoid.FG (K s h) :=
  Monoid.fg_of_surjective (PresentedMonoid.mk (Word.Rel KAlphabet (KMachine s h))) PresentedMonoid.surjective_mk

noncomputable def groupUnitsEmbedding (hs : Subgroup.closure (Set.range s)=⊤) : G →* (H s h)ˣ :=
  (groupEmbedding s h hs).toHomUnits

abbrev SmallAlgebra (𝕜 : Type*) [CommRing 𝕜] := Contracted.Algebra 𝕜 (H s h)
abbrev BigAlgebra (𝕜 : Type*) [CommRing 𝕜] := Contracted.Algebra 𝕜 (K s h)

noncomputable def algebraEmbedding (𝕜 : Type*) [CommRing 𝕜] :
    SmallAlgebra s h 𝕜 →ₙₐ[𝕜] BigAlgebra s h 𝕜 := Contracted.embedding (copyEmbedding s h)

end FiniteAlgebraicEnvelopes.Bootstrap.Source

namespace FiniteAlgebraicEnvelopes.Bootstrap.Source
open Compiler Compiler.Simulator MachineRealization
variable {G : Type*} [Group G] {n : ℕ} (s : Fin n → G)
variable (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word n => evalWord s w=1))
variable (k : Type*) [CommRing k]

abbrev AlgebraGenerators := Word.Letter Sigma (Bool×family.Γ) (ParameterMachine.State family.Q (index s h))

def AlgebraRelations : FreeAlgebra k (AlgebraGenerators s h) → FreeAlgebra k (AlgebraGenerators s h) → Prop :=
  ContractedPresentation.Rel k (AlgebraGenerators s h) (Word.Rel KAlphabet (KMachine s h)) [.zero]

/-- The source algebra B has precisely the literal compiler equations and a zero equation. -/
def algebraPresentation : RingQuot (AlgebraRelations s h k) ≃ₐ[k] BigAlgebra s h k :=
  ContractedPresentation.equivalence k (AlgebraGenerators s h) (Word.Rel KAlphabet (KMachine s h))
    (MulEquiv.refl (K s h)) [.zero] rfl

end FiniteAlgebraicEnvelopes.Bootstrap.Source

section

namespace FiniteAlgebraicEnvelopes.Bootstrap.Source
variable {G : Type*} [Group G] {n : ℕ} (s : Fin n → G)
variable (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word n => evalWord s w=1))
variable (k : Type*) [CommRing k]

def bigGenerators : Set (BigAlgebra s h k) := Set.range (fun x => algebraPresentation s h k
  (ContractedPresentation.quotientGenerators k _ (AlgebraRelations s h k) x))

end FiniteAlgebraicEnvelopes.Bootstrap.Source
end

namespace FiniteAlgebraicEnvelopes.Bootstrap.Source

section
open Compiler Compiler.Simulator MachineRealization MachineRealization.ParameterCode
open scoped Compiler.HeadCodec
variable {G : Type*} [Group G] {k : ℕ} (s : Fin k → G)
variable (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word k => evalWord s w=1))

abbrev T := FiniteAlgebraicEnvelopes.ZeroProduct.Mon (K s h) PartialAffine.monoid
abbrev TLetter := FiniteY (Γ:=family.Γ) (Q:=family.Q) (index s h)
abbrev TCode := finiteCodeT (Γ:=family.Γ) (Q:=family.Q) k (index s h)
abbrev TClass := finiteClass family.A family.M (index s h)
abbrev TTest := Search.value (finiteTest family.A family.M (index s h))

local instance instLinearOrderSectorSigmaProdBoolΓFamilyStateQIndex_1 : LinearOrder (Control.Sector Sigma (Bool×family.Γ) (ParameterMachine.State family.Q (index s h))) :=
  finiteOrder (T:=Sigma) (Γ:=family.Γ) (Q:=family.Q) (index s h)

def tPairEval : FreeMonoid (TLetter s h) →* K s h × PartialAffine.monoid where
  toFun w := (Word.present KAlphabet (KMachine s h) (Projection.left w.toList),PartialAffine.wordValue (Projection.right w.toList))
  map_one' := rfl
  map_mul' u v := by
    apply Prod.ext
    · simp only [FreeMonoid.toList_mul,Projection.left_append]
      rfl
    · apply Subtype.ext
      simp [PartialAffine.wordValue,PartialAffine.value]

def tEval : FreeMonoid (TLetter s h) →* T s h :=
  (FiniteAlgebraicEnvelopes.ZeroProduct.pair (K s h) PartialAffine.monoid).comp (tPairEval s h)

 theorem tPairEval_surjective : Function.Surjective (tPairEval s h) := by
  rintro ⟨x,y⟩
  obtain ⟨u,rfl⟩ := Word.present_surjective KAlphabet (KMachine s h) x
  obtain ⟨v,rfl⟩ := PartialAffine.wordValue_surjective y
  refine ⟨FreeMonoid.ofList (u.map Sum.inl++v.map Sum.inr),?_⟩
  simp [tPairEval,Projection.left,Projection.right,List.filterMap_map]

 theorem tEval_surjective : Function.Surjective (tEval s h) :=
  (FiniteAlgebraicEnvelopes.ZeroProduct.pair_surjective _ _).comp (tPairEval_surjective s h)

 theorem finiteValue_eq_iff (u v : List (TLetter s h)) :
    finiteValue family.A family.M (index s h) u=finiteValue family.A family.M (index s h) v ↔
      Word.present KAlphabet (KMachine s h) (Projection.left u)=Word.present KAlphabet (KMachine s h) (Projection.left v) := by
  rw [finiteValue,finiteValue,(List.map_injective_iff.mpr (Word.letterMap_injective _ (MachineRealization.ParameterCode.encode_injective (index s h)))).eq_iff]
  exact (Word.present_eq_iff_normal KAlphabet (KMachine s h) family.decode
    (fun j => (index_budget s h j).totalize)
    (fun j => (family.realizes (index s h)).computesAt KAlphabet (KMachine s h) (index_budget s h j)) _ _).symm

 theorem finiteValue_eq_zero (w : List (TLetter s h)) :
    finiteValue family.A family.M (index s h) w=[.zero] ↔
      Word.present KAlphabet (KMachine s h) (Projection.left w)=(0 : K s h) := by
  rw [finiteValue_zero,zero_K,Word.present_eq_iff_normal KAlphabet (KMachine s h) family.decode
    (fun j => (index_budget s h j).totalize)
    (fun j => (family.realizes (index s h)).computesAt KAlphabet (KMachine s h) (index_budget s h j)),Word.normal_omega]

 attribute [local instance] OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.instDecidableEqXSigmaΓFamilyQ
theorem tClass_eq_iff (u v : List (TLetter s h)) :
    TClass s h u=TClass s h v ↔ tEval s h (FreeMonoid.ofList u)=tEval s h (FreeMonoid.ofList v) := by
  change ZeroProduct.test _ _ _ u=ZeroProduct.test _ _ _ v ↔
    FiniteAlgebraicEnvelopes.ZeroProduct.pair _ _ _=FiniteAlgebraicEnvelopes.ZeroProduct.pair _ _ _
  rw [FiniteAlgebraicEnvelopes.ZeroProduct.pair_eq_iff]
  change ZeroProduct.test _ _ _ u=ZeroProduct.test _ _ _ v ↔
    (Word.present KAlphabet (KMachine s h) (Projection.left u),PartialAffine.wordValue (Projection.right u))=
      (Word.present KAlphabet (KMachine s h) (Projection.left v),PartialAffine.wordValue (Projection.right v)) ∨
       Word.present KAlphabet (KMachine s h) (Projection.left u)=0 ∧ Word.present KAlphabet (KMachine s h) (Projection.left v)=0
  rw [Prod.ext_iff,←finiteValue_eq_iff s h,←finiteValue_eq_zero s h,←finiteValue_eq_zero s h]
  have hp : PartialAffine.wordValue (Projection.right u)=PartialAffine.wordValue (Projection.right v) ↔
      PartialAffine.testedClass (Projection.right u)=PartialAffine.testedClass (Projection.right v) := by
    rw [PartialAffine.testedClass_eq_iff]
    exact Subtype.ext_iff
  rw [hp]
  by_cases hu : finiteValue family.A family.M (index s h) u=[Path.Letter.zero] <;>
    by_cases hv : finiteValue family.A family.M (index s h) v=[Path.Letter.zero] <;>
    simp [ZeroProduct.test,hu,hv]
  aesop

 theorem tClass_eq_none (w : List (TLetter s h)) : TClass s h w=none ↔ tEval s h (FreeMonoid.ofList w)=0 := by
  change ZeroProduct.test _ _ _ w=none ↔ FiniteAlgebraicEnvelopes.ZeroProduct.pair _ _ _=0
  rw [FiniteAlgebraicEnvelopes.ZeroProduct.pair_eq_zero]
  change ZeroProduct.test _ _ _ w=none ↔ Word.present KAlphabet (KMachine s h) (Projection.left w)=0
  rw [←finiteValue_eq_zero s h]
  simp [ZeroProduct.test]

 theorem tTest_eq_class (w : List (TLetter s h)) : TTest s h w=TClass s h w :=
  search_value_eq family.A family.M (index s h) w.length (index_budget s h (2*w.length)) w le_rfl

 theorem tTest_properties (j : ℕ) : TTest s h []≠none ∧ Static.Contextual (TTest s h) j ∧ Static.ZeroIdeal (TTest s h) j :=
  (tests_bounded family.A family.M (index s h) j (index_budget s h (2*j))
    (family.realizes (index s h)) family.decode).2

 theorem t_code_eq_iff (u v : List (TLetter s h)) :
    Quotient.present (processor s h) ((TCode s h).encode u)=Quotient.present (processor s h) ((TCode s h).encode v) ↔
      tEval s h (FreeMonoid.ofList u)=tEval s h (FreeMonoid.ofList v) := by
  rw [Quotient.present_encode_iff (processor s h) wf_sigma (index_good s h) (index_stable s h)
    (TCode s h) (wf_relT (index s h)) (TTest s h) markers.zero
    (fun j _ hrs => tables_short s family.A family.M (index s h) j hrs)
    (fun j _ hrs => tables_isolateT s family.A family.M (index s h) j hrs)
    (fun j _ hrs => tables_staticT s family.A family.M (index s h) j hrs)
    (fun j => (tTest_properties s h j).2.1) (fun j => (tTest_properties s h j).2.2)
    (tTest_properties s h 0).1 (codeT_avoid (Γ:=family.Γ) (Q:=family.Q) k (index s h) _ (by simp))]
  rw [tTest_eq_class,tTest_eq_class,tClass_eq_iff]

noncomputable def kappa : T s h →* H s h :=
  Quotient.descendCode (TCode s h) (tEval s h) (tEval_surjective s h) (t_code_eq_iff s h)

 theorem kappa_word (w : List (TLetter s h)) : kappa s h (tEval s h (FreeMonoid.ofList w))=
    Quotient.present (processor s h) ((TCode s h).encode w) :=
  Quotient.descendCode_apply (TCode s h) (tEval s h) (tEval_surjective s h) (t_code_eq_iff s h) w

end

open Compiler Compiler.Simulator MachineRealization MachineRealization.ParameterCode
open scoped Compiler.HeadCodec
variable {G : Type*} [Group G] {k : ℕ} (s : Fin k → G)
variable (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word k => evalWord s w=1))
local instance instDecidableEqLetterSigmaProdBoolΓFamilyStateQIndex_1 : DecidableEq (Word.Letter Sigma (Bool×family.Γ) (ParameterMachine.State family.Q (index s h))) := inferInstance
local instance instDecidableEqTLetter_1 : DecidableEq (TLetter s h) := inferInstance
local instance instFintypeTLetter_1 : Fintype (TLetter s h) := inferInstance

 theorem t_normal (w : List (TLetter s h)) :
    Quotient.normal (processor s h) ((TCode s h).encode w)=
      Static.output (TCode s h) (wf_relT (index s h)) (TTest s h) markers.zero w :=
  Quotient.normal_encode (processor s h) wf_sigma (index_good s h) (index_stable s h)
    (TCode s h) (wf_relT (index s h)) (TTest s h) markers.zero
    (fun j _ hrs => tables_short s family.A family.M (index s h) j hrs)
    (fun j _ hrs => tables_isolateT s family.A family.M (index s h) j hrs)
    (fun j _ hrs => tables_staticT s family.A family.M (index s h) j hrs)
    (fun j => (tTest_properties s h j).2.1) (fun j => (tTest_properties s h j).2.2)
    (tTest_properties s h 0).1 w

 theorem tTest_eq_none (w : List (TLetter s h)) :
    TTest s h w=none ↔ tEval s h (FreeMonoid.ofList w)=0 := by
  rw [tTest_eq_class,tClass_eq_none]

 theorem kappa_zero : kappa s h 0=0 := by
  obtain ⟨w,hw⟩ := tEval_surjective s h 0
  have hq : TTest s h w.toList=none := (tTest_eq_none s h w.toList).mpr hw
  rw [←hw]
  change kappa s h (tEval s h (FreeMonoid.ofList w.toList))=0
  rw [kappa_word,Quotient.present_normal (processor s h) wf_sigma (index_good s h) (index_stable s h),t_normal]
  simp only [Static.output,hq,ite_true]
  rfl

/-- The source's separator is the seventh letter, distinct from both code
    alphabets, all four selector markers, and the zero letter. -/
def separator : H s h := Quotient.present (processor s h) [6]

 theorem separator_avoid_T : (6:Sigma)∉(TCode s h).Alphabet := by
  intro hh
  have hh := codeT_alphabet (Γ:=family.Γ) (Q:=family.Q) k (index s h) hh
  norm_num [Fin.ext_iff] at hh

 theorem separator_avoid_G : (6:Sigma)∉(finiteCodeG (Γ:=family.Γ) (Q:=family.Q) k (index s h)).Alphabet := by
  intro hh
  have hh := codeG_alphabet (Γ:=family.Γ) (Q:=family.Q) k (index s h) hh
  norm_num [Fin.ext_iff] at hh

 attribute [local instance] OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.instDecidableEqXSigmaΓFamilyQ_1
theorem tables_isolate_separator (j : ℕ) {rs : List (List Sigma × List Sigma)}
    (hrs : rs∈processor s h j) :
    ∀ p∈rs,p∈Static.table (TCode s h) (wf_relT (index s h)) (TTest s h) markers.zero j ∨
      ∃ b∈p.1,b∉(TCode s h).Alphabet ∧ b≠6 := by
  intro p hp
  apply Selectors.process_isolate_separator markers (TCode s h) (wf_relT (index s h)) (TTest s h) 6 ?_
    (codeT_avoid (Γ:=family.Γ) (Q:=family.Q) k (index s h) _ (by simp)) (by decide) _ _ _
    ((tables_members s family.A family.M (index s h) j hrs p).mp hp)
  intro p hp
  exact Base.isolate_separator (TCode s h) (finiteCodeG (Γ:=family.Γ) (Q:=family.Q) k (index s h))
    (wf_relT (index s h)) (wf_relG k) (TTest s h) (Search.value (testG s (index s h))) markers.zero (6:Sigma)
    (codeT_avoid (Γ:=family.Γ) (Q:=family.Q) k (index s h) _ (by simp)) (by decide)
    (separator_avoid_G s h)
    (codes_disjoint (Γ:=family.Γ) (Q:=family.Q) k (index s h)) hp

 theorem separator_word (u v : List (TLetter s h)) :
    kappa s h (tEval s h (FreeMonoid.ofList u))*separator s h*kappa s h (tEval s h (FreeMonoid.ofList v))=
      Quotient.present (processor s h) ((TCode s h).encode u++6::(TCode s h).encode v) := by
  rw [kappa_word,kappa_word]
  simp only [separator,←Quotient.present_append,List.append_assoc,List.singleton_append]

 theorem separator_nonzero (x y : T s h) (hx : x≠0) (hy : y≠0) :
    kappa s h x*separator s h*kappa s h y≠0 := by
  obtain ⟨u,rfl⟩ := tEval_surjective s h x
  obtain ⟨v,rfl⟩ := tEval_surjective s h y
  change kappa s h (tEval s h (FreeMonoid.ofList u.toList))*separator s h*kappa s h (tEval s h (FreeMonoid.ofList v.toList))≠0
  rw [separator_word,zero_H]
  exact Quotient.present_separator_ne_zero (processor s h) wf_sigma (index_good s h) (index_stable s h)
    (TCode s h) (wf_relT (index s h)) (TTest s h) markers.zero (6:Sigma)
    (fun j rs hrs => tables_short s family.A family.M (index s h) j hrs)
    (fun j rs hrs => tables_isolate_separator s h j hrs)
    (fun j rs hrs => tables_staticT s family.A family.M (index s h) j hrs)
    (fun j => (tTest_properties s h j).2.1) (fun j => (tTest_properties s h j).2.2)
    (tTest_properties s h 0).1
    (separator_avoid_T s h)
    (codeT_avoid (Γ:=family.Γ) (Q:=family.Q) k (index s h) _ (by simp)) (by decide)
    (fun he => hx ((tTest_eq_none s h _).mp he)) (fun he => hy ((tTest_eq_none s h _).mp he))

end FiniteAlgebraicEnvelopes.Bootstrap.Source

section

namespace FiniteAlgebraicEnvelopes.Bootstrap.Source
variable {G : Type*} [Group G] {k : ℕ} (s : Fin k → G)
variable (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word k => evalWord s w=1))

def kappa₀ : T s h →*₀ H s h := { kappa s h with map_zero' := kappa_zero s h }

def kappaAlgebra (𝕜 : Type*) [CommRing 𝕜] : Contracted.Algebra 𝕜 (T s h) →ₐ[𝕜] SmallAlgebra s h 𝕜 :=
  Contracted.map (kappa₀ s h)

end FiniteAlgebraicEnvelopes.Bootstrap.Source
end

end

end OAI
end

section
-- module Solutions.OAIFAE.Corners
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.Steinberg.instNormalGroupFinOfNatNatRingKernel _root_.OAI.FiniteAlgebraicEnvelopes.SteinbergFiniteFree.freeAlgebra_finitelyPresented _root_.OAI.FiniteAlgebraicEnvelopes.SteinbergFiniteFree.polynomial_finitelyPresented
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Tensor embeddings and the nonunital corner maps between the two algebras.
-/

section

namespace FiniteAlgebraicEnvelopes.Bootstrap.Source
open scoped TensorProduct
variable {G : Type*} [Group G] {n : ℕ} (s : Fin n → G)
variable (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word n => evalWord s w=1))
variable (k : Type*) [CommRing k]

/-- The actual unital tensor embedding from the algebra construction, not supplied as a hypothesis. -/
def rho : BigAlgebra s h k ⊗[k] MonoidAlgebra k PartialAffine.monoid →ₐ[k] SmallAlgebra s h k :=
  (kappaAlgebra s h k).comp (ZeroProduct.tensorMap k (K s h) PartialAffine.monoid)

def j : BigAlgebra s h k →ₙₐ[k] SmallAlgebra s h k :=
  (rho s h k).toNonUnitalAlgHom.comp (PartialAffine.Corner.cornerTensor k (BigAlgebra s h k))

def phi : BigAlgebra s h k →ₙₐ[k] BigAlgebra s h k :=
  (algebraEmbedding s h k).comp (j s h k)

end FiniteAlgebraicEnvelopes.Bootstrap.Source
end

namespace FiniteAlgebraicEnvelopes.Bootstrap.Source

section
open scoped TensorProduct
open PartialAffine.Corner
variable {G : Type*} [Group G] {n : ℕ} (s : Fin n → G)
variable (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word n => evalWord s w=1))
variable (k : Type*) [CommRing k]

def xi : BigAlgebra s h k ⊗[k] MonoidAlgebra k PartialAffine.monoid →ₙₐ[k] BigAlgebra s h k :=
  (algebraEmbedding s h k).comp (rho s h k).toNonUnitalAlgHom

 theorem phi_eq (a : BigAlgebra s h k) : phi s h k a=xi s h k (a⊗ₜ[k] q k) := rfl

 theorem xi_constant_commute (c : MonoidAlgebra k PartialAffine.monoid)
    (hqc : q k*c=c) (hcq : c*q k=c) (a : BigAlgebra s h k) :
    Commute (xi s h k (1⊗ₜ[k] c)) (phi s h k a) := by
  change xi s h k (1⊗ₜ[k] c)*phi s h k a=phi s h k a*xi s h k (1⊗ₜ[k] c)
  rw [phi_eq,←map_mul,←map_mul]
  simp only [Algebra.TensorProduct.tmul_mul_tmul,one_mul,mul_one,hqc,hcq]

def supported (c d : MonoidAlgebra k PartialAffine.monoid)
    (hdc : d*c=q k) (hqc : q k*c=c) (hcq : c*q k=c) (hqd : q k*d=d) (hdq : d*q k=d) :
    Steinberg.SupportedPair (phi s h k : BigAlgebra s h k →ₙ+* BigAlgebra s h k) where
  U := xi s h k (1⊗ₜ[k] c)
  V := xi s h k (1⊗ₜ[k] d)
  VU := by
    change xi s h k (1⊗ₜ[k] (d))*xi s h k (1⊗ₜ[k] (c))=xi s h k (1⊗ₜ[k] (q k))
    rw [←map_mul]; simp [Algebra.TensorProduct.tmul_mul_tmul,hdc]
  PU := by
    change xi s h k (1⊗ₜ[k] (q k))*xi s h k (1⊗ₜ[k] (c))=xi s h k (1⊗ₜ[k] (c))
    rw [←map_mul]; simp [Algebra.TensorProduct.tmul_mul_tmul,hqc]
  UP := by
    change xi s h k (1⊗ₜ[k] (c))*xi s h k (1⊗ₜ[k] (q k))=xi s h k (1⊗ₜ[k] (c))
    rw [←map_mul]; simp [Algebra.TensorProduct.tmul_mul_tmul,hcq]
  PV := by
    change xi s h k (1⊗ₜ[k] (q k))*xi s h k (1⊗ₜ[k] (d))=xi s h k (1⊗ₜ[k] (d))
    rw [←map_mul]; simp [Algebra.TensorProduct.tmul_mul_tmul,hqd]
  VP := by
    change xi s h k (1⊗ₜ[k] (d))*xi s h k (1⊗ₜ[k] (q k))=xi s h k (1⊗ₜ[k] (d))
    rw [←map_mul]; simp [Algebra.TensorProduct.tmul_mul_tmul,hdq]
  commU := xi_constant_commute s h k c hqc hcq
  commV := xi_constant_commute s h k d hqd hdq

def pair0 : Steinberg.SupportedPair (phi s h k : BigAlgebra s h k →ₙ+* BigAlgebra s h k) :=
  supported s h k (s0 k) (t0 k) (t0_s0 k) (q_s0 k) (s0_q k) (q_t0 k) (t0_q k)
def pair1 : Steinberg.SupportedPair (phi s h k : BigAlgebra s h k →ₙ+* BigAlgebra s h k) :=
  supported s h k (s1 k) (t1 k) (t1_s1 k) (q_s1 k) (s1_q k) (q_t1 k) (t1_q k)

theorem pair0_pair1 : (pair0 s h k).V*(pair1 s h k).U=0 := by
  change xi s h k (1⊗ₜ[k] t0 k)*xi s h k (1⊗ₜ[k] s1 k)=0
  rw [←map_mul,Algebra.TensorProduct.tmul_mul_tmul,t0_s1,TensorProduct.tmul_zero,map_zero]
theorem pair1_pair0 : (pair1 s h k).V*(pair0 s h k).U=0 := by
  change xi s h k (1⊗ₜ[k] t1 k)*xi s h k (1⊗ₜ[k] s0 k)=0
  rw [←map_mul,Algebra.TensorProduct.tmul_mul_tmul,t1_s0,TensorProduct.tmul_zero,map_zero]

theorem pairs_sum : (pair0 s h k).U*(pair0 s h k).V+(pair1 s h k).U*(pair1 s h k).V=phi s h k 1 := by
  change xi s h k (1⊗ₜ[k] s0 k)*xi s h k (1⊗ₜ[k] t0 k)+
    xi s h k (1⊗ₜ[k] s1 k)*xi s h k (1⊗ₜ[k] t1 k)=_
  rw [←map_mul,←map_mul,←map_add,phi_eq]
  simp only [Algebra.TensorProduct.tmul_mul_tmul,one_mul,←TensorProduct.tmul_add,s0_t0_add_s1_t1]

end

open scoped TensorProduct
open Contracted
variable {G : Type*} [Group G] {n : ℕ} (s : Fin n → G)
variable (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word n => evalWord s w=1))
variable (k : Type*) [CommRing k]

abbrev TAlgebra := Contracted.Algebra k (T s h)

def separatingElement : SmallAlgebra s h k := basis k (H s h) (separator s h) 1

def separationBilinear : TAlgebra s h k →ₗ[k] TAlgebra s h k →ₗ[k] SmallAlgebra s h k :=
  LinearMap.mk₂ k (fun x y => kappaAlgebra s h k x*separatingElement s h k*kappaAlgebra s h k y)
    (by intro a b c; simp [add_mul])
    (by intro r a b; simp [smul_mul_assoc])
    (by intro a b c; simp [mul_add])
    (by intro r a b; simp [mul_smul_comm])

def separationLinear : TAlgebra s h k ⊗[k] TAlgebra s h k →ₗ[k] SmallAlgebra s h k :=
  TensorProduct.lift (separationBilinear s h k)

@[simp] theorem separationLinear_tmul (x y : TAlgebra s h k) :
    separationLinear s h k (x⊗ₜ[k] y)=kappaAlgebra s h k x*separatingElement s h k*kappaAlgebra s h k y := rfl

def separatorIndex (p : {a : T s h // a≠0} × {a : T s h // a≠0}) : {a : H s h // a≠0} :=
  ⟨kappa s h p.1*separator s h*kappa s h p.2,separator_nonzero s h _ _ p.1.property p.2.property⟩

/-- The map j before the final κ extension, with image in the actual T algebra. -/
def jT : BigAlgebra s h k →ₙₐ[k] TAlgebra s h k :=
  (ZeroProduct.tensorMap k (K s h) PartialAffine.monoid).toNonUnitalAlgHom.comp
    (PartialAffine.Corner.cornerTensor k (BigAlgebra s h k))

end FiniteAlgebraicEnvelopes.Bootstrap.Source

namespace FiniteAlgebraicEnvelopes.Bootstrap.Source
open scoped TensorProduct
variable {G : Type*} [Group G] {n : ℕ} (s : Fin n → G)
variable (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word n => evalWord s w=1))
variable (k : Type*) [CommRing k]

abbrev R := Enveloping.Coeff k (BigAlgebra s h k)

def psi := NonunitalTensor.coefficient (phi s h k)

@[simp] theorem psi_tmul (a b : BigAlgebra s h k) :
    psi s h k (a⊗ₜ[k] MulOpposite.op b)=phi s h k a⊗ₜ[k] MulOpposite.op (phi s h k b) := rfl

def detectionInput : R s h k →ₗ[k] TAlgebra s h k ⊗[k] TAlgebra s h k :=
  TensorProduct.map (NonunitalTensor.linear (jT s h k))
    ((NonunitalTensor.linear (jT s h k)).comp
      (MulOpposite.opLinearEquiv k : BigAlgebra s h k ≃ₗ[k] (BigAlgebra s h k)ᵐᵒᵖ).symm.toLinearMap)

def detectionLinear : R s h k →ₗ[k] BigAlgebra s h k :=
  (NonunitalTensor.linear (algebraEmbedding s h k)).comp
    ((separationLinear s h k).comp (detectionInput s h k))

def detectingElement : BigAlgebra s h k := algebraEmbedding s h k (separatingElement s h k)

end FiniteAlgebraicEnvelopes.Bootstrap.Source

namespace FiniteAlgebraicEnvelopes.NonunitalTensor

section
open scoped TensorProduct
variable {k A : Type*} [CommRing k] [Ring A] [Algebra k A]
variable (f : A →ₙₐ[k] A)

def coefficientRing :
    @NonUnitalRingHom (Enveloping.Coeff k A) (Enveloping.Coeff k A)
      (inferInstance : Ring (Enveloping.Coeff k A)).toNonAssocRing.toNonUnitalNonAssocSemiring
      (inferInstance : Ring (Enveloping.Coeff k A)).toNonAssocRing.toNonUnitalNonAssocSemiring :=
  coefficient f

 theorem coefficient_one : coefficient f 1=f 1⊗ₜ[k] MulOpposite.op (f 1) := by
  change coefficient f ((1:A)⊗ₜ[k] (1:(A)ᵐᵒᵖ))=_
  rfl

 theorem tensor_constant_commute (c : A) (hc : ∀ a, Commute c (f a))
    (r : Enveloping.Coeff k A) : Commute (c⊗ₜ[k] MulOpposite.op (f 1)) (coefficient f r) := by
   induction r using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add]; exact ha.add_right hb
  | tmul a b =>
    change (c⊗ₜ[k] MulOpposite.op (f 1))*(f a⊗ₜ[k] MulOpposite.op (f b.unop))=
      (f a⊗ₜ[k] MulOpposite.op (f b.unop))*(c⊗ₜ[k] MulOpposite.op (f 1))
    simp only [Algebra.TensorProduct.tmul_mul_tmul,←MulOpposite.op_mul,image_left,image_right,(hc a).eq]

def supportedPair (p : Steinberg.SupportedPair (f : A →ₙ+* A)) :
    Steinberg.SupportedPair (coefficientRing f) where
  U := p.U⊗ₜ[k] MulOpposite.op (f 1)
  V := p.V⊗ₜ[k] MulOpposite.op (f 1)
  VU := by
    change (p.V⊗ₜ[k] MulOpposite.op (f 1))*(p.U⊗ₜ[k] MulOpposite.op (f 1))=coefficient f 1
    rw [coefficient_one,Algebra.TensorProduct.tmul_mul_tmul,←MulOpposite.op_mul,image_left,p.VU]
    rfl
  PU := by
    change coefficient f 1*(p.U⊗ₜ[k] MulOpposite.op (f 1))=_
    rw [coefficient_one,Algebra.TensorProduct.tmul_mul_tmul,←MulOpposite.op_mul,image_left]
    change ((f : A →ₙ+* A) 1*p.U)⊗ₜ[k] MulOpposite.op (f 1)=_
    rw [p.PU]
  UP := by
    change (p.U⊗ₜ[k] MulOpposite.op (f 1))*coefficient f 1=_
    rw [coefficient_one,Algebra.TensorProduct.tmul_mul_tmul,←MulOpposite.op_mul,image_left]
    change (p.U*(f : A →ₙ+* A) 1)⊗ₜ[k] MulOpposite.op (f 1)=_
    rw [p.UP]
  PV := by
    change coefficient f 1*(p.V⊗ₜ[k] MulOpposite.op (f 1))=_
    rw [coefficient_one,Algebra.TensorProduct.tmul_mul_tmul,←MulOpposite.op_mul,image_left]
    change ((f : A →ₙ+* A) 1*p.V)⊗ₜ[k] MulOpposite.op (f 1)=_
    rw [p.PV]
  VP := by
    change (p.V⊗ₜ[k] MulOpposite.op (f 1))*coefficient f 1=_
    rw [coefficient_one,Algebra.TensorProduct.tmul_mul_tmul,←MulOpposite.op_mul,image_left]
    change (p.V*(f : A →ₙ+* A) 1)⊗ₜ[k] MulOpposite.op (f 1)=_
    rw [p.VP]
  commU := tensor_constant_commute f p.U (by intro a; exact p.commU a)
  commV := tensor_constant_commute f p.V (by intro a; exact p.commV a)

theorem supportedPair_cross (p q : Steinberg.SupportedPair (f : A →ₙ+* A)) (hpq : p.V*q.U=0) :
    (supportedPair f p).V*(supportedPair f q).U=0 := by
  change (p.V⊗ₜ[k] MulOpposite.op (f 1))*(q.U⊗ₜ[k] MulOpposite.op (f 1))=0
  rw [Algebra.TensorProduct.tmul_mul_tmul,hpq,TensorProduct.zero_tmul]

theorem supportedPair_sum (p q : Steinberg.SupportedPair (f : A →ₙ+* A)) (hpq : p.U*p.V+q.U*q.V=f 1) :
    (supportedPair f p).U*(supportedPair f p).V+(supportedPair f q).U*(supportedPair f q).V=coefficient f 1 := by
  change (p.U⊗ₜ[k] MulOpposite.op (f 1))*(p.V⊗ₜ[k] MulOpposite.op (f 1))+
    (q.U⊗ₜ[k] MulOpposite.op (f 1))*(q.V⊗ₜ[k] MulOpposite.op (f 1))=_
  simp only [Algebra.TensorProduct.tmul_mul_tmul,←MulOpposite.op_mul,image_left,←TensorProduct.add_tmul,hpq,coefficient_one]

end

variable {k A : Type*} [CommRing k] [Ring A] [Algebra k A]
variable (f : A →ₙₐ[k] A)

theorem annihilation (p q : Steinberg.SupportedPair (f : A →ₙ+* A))
    (hpq : p.V*q.U=0) (hqp : q.V*p.U=0) (hsum : p.U*p.V+q.U*q.V=f 1)
    (z : Steinberg.Group (Fin 6) (Enveloping.Coeff k A)) (hz : Steinberg.matrixMap z=1) :
    Steinberg.coefficientMap (coefficientRing f) z=1 :=
  (supportedPair f p).annihilation (supportedPair f q) (supportedPair_cross f p q hpq)
    (supportedPair_cross f q p hqp) (supportedPair_sum f p q hsum) hz

end FiniteAlgebraicEnvelopes.NonunitalTensor

namespace FiniteAlgebraicEnvelopes.Bootstrap.Source
variable {G : Type*} [Group G] {n : ℕ} (s : Fin n → G)
variable (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word n => evalWord s w=1))
variable (k : Type*) [CommRing k]

local instance instNonUnitalNonAssocSemiringR : NonUnitalNonAssocSemiring (R s h k) :=
  (inferInstance : Ring (R s h k)).toNonAssocRing.toNonUnitalNonAssocSemiring

def ringPsi : R s h k →ₙ+* R s h k := NonunitalTensor.coefficientRing (phi s h k)

end FiniteAlgebraicEnvelopes.Bootstrap.Source

end

end OAI
end

section
-- module Solutions.OAIFAE.AlgebraPresentations
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Finite presentations of tensor, opposite, contracted, unitized, and coefficient algebras.
-/

namespace FiniteAlgebraicEnvelopes.AlgebraGenerators

open scoped TensorProduct
variable {B : Type*} [Ring B] [Algebra (ZMod 2) B]

def envelopingGenerators (S : Set B) : Set (Enveloping.Coeff (ZMod 2) B) :=
  tensorGenerators (k:=ZMod 2) S (MulOpposite.op '' S)

end FiniteAlgebraicEnvelopes.AlgebraGenerators

section

namespace FiniteAlgebraicEnvelopes.Bootstrap.Source
variable {G : Type*} [Group G] {n : ℕ} (s : Fin n → G)
variable (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word n => evalWord s w=1))
variable (k : Type*) [CommRing k] [Nontrivial k]
variable (hs : Subgroup.closure (Set.range s)=⊤)

/-- Input units in the simple algebra, whose internal identity is preserved. -/
def groupAlgebraEmbedding : G →* SmallAlgebra s h k :=
  (ContractedPresentation.monoidBasis k).comp (groupEmbedding s h hs)

end FiniteAlgebraicEnvelopes.Bootstrap.Source
end

namespace FiniteAlgebraicEnvelopes.Enveloping
open scoped TensorProduct
variable (k A : Type*) [CommRing k] [Ring A] [Algebra k A]

def includeLeft : A →ₐ[k] Coeff k A := Algebra.TensorProduct.includeLeft

@[simp] theorem includeLeft_apply (a : A) : includeLeft k A a=a⊗ₜ[k] (1:Aᵐᵒᵖ) := rfl

def unitsInclude : Aˣ →* (Coeff k A)ˣ := Units.map (includeLeft k A).toMonoidHom

end FiniteAlgebraicEnvelopes.Enveloping

namespace FiniteAlgebraicEnvelopes.Bootstrap.Source

section
variable {G : Type*} [Group G] {n : ℕ} (s : Fin n → G)
variable (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word n => evalWord s w=1))
variable (k : Type*) [CommRing k] [Nontrivial k]
variable (hs : Subgroup.closure (Set.range s)=⊤)

def ambientUnits : G →* (BigAlgebra s h k)ˣ :=
  Unitize.unitsHom (algebraEmbedding s h k) (groupAlgebraEmbedding s h k hs)

def coefficientUnits : G →* (R s h k)ˣ :=
  (Enveloping.unitsInclude k (BigAlgebra s h k)).comp (ambientUnits s h k hs)

end

variable {G : Type*} [Group G] {n : ℕ} (s : Fin n → G)
variable (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word n => evalWord s w=1))
variable (k : Type*) [CommRing k] [Nontrivial k]

def linearTransition := Steinberg.elementaryTransition (R:=R s h k) (ringPsi s h k)

end FiniteAlgebraicEnvelopes.Bootstrap.Source

namespace FiniteAlgebraicEnvelopes.Bootstrap.Source
open scoped TensorProduct
variable {G : Type*} [Group G] {n : ℕ} (s : Fin n → G)
variable (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word n => evalWord s w=1))

local instance ringRightSMul :
    SMul (BigAlgebra s h (ZMod 2))ᵐᵒᵖ (BigAlgebra s h (ZMod 2)) :=
  Mul.toSMulMulOpposite _

def ringGenerators : Set (R s h (ZMod 2)) :=
  AlgebraGenerators.tensorGenerators (k:=ZMod 2) (bigGenerators s h (ZMod 2))
    (MulOpposite.op '' bigGenerators s h (ZMod 2))

end FiniteAlgebraicEnvelopes.Bootstrap.Source

namespace FiniteAlgebraicEnvelopes.EnvelopingPresentation
open scoped TensorProduct
variable (k : Type*) [CommRing k] {A : Type*}
variable (r : FreeAlgebra k A → FreeAlgebra k A → Prop)

variable {B : Type*} [Ring B] [Algebra k B]
def ofPresentation (e : RingQuot r ≃ₐ[k] B) : RingQuot (Rel k r) ≃ₐ[k] Enveloping.Coeff k B :=
  (equivalence k r).trans (Algebra.TensorProduct.congr e e.op)

end FiniteAlgebraicEnvelopes.EnvelopingPresentation

namespace FiniteAlgebraicEnvelopes.Bootstrap.Source
variable {G : Type*} [Group G] {n : ℕ} (s : Fin n → G)
variable (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word n => evalWord s w=1))
variable (k : Type*) [CommRing k]

abbrev CoefficientGenerators := AlgebraGenerators s h ⊕ AlgebraGenerators s h

def CoefficientRelations := EnvelopingPresentation.Rel k (AlgebraRelations s h k)

def coefficientPresentation := EnvelopingPresentation.ofPresentation k (AlgebraRelations s h k)
  (algebraPresentation s h k)

end FiniteAlgebraicEnvelopes.Bootstrap.Source

end

end OAI
end

section
-- module Solutions.OAIFAE.AffineModules
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Affine module presentations, stabilized actions, and finite stabilizers.
-/

section

namespace FiniteAlgebraicEnvelopes.NonunitalTensor
open scoped TensorProduct
variable {k B : Type*} [CommRing k] [Ring B] [Algebra k B]

theorem coefficient_compatible (f : B →ₙₐ[k] B) (r : Enveloping.Coeff k B) (b : B) :
    f (r • b)=coefficientRing f r • f b := by
  induction r using TensorProduct.induction_on with
  | zero =>
    change f (Enveloping.act k B 0 b)=Enveloping.act k B (coefficientRing f 0) (f b)
    simp
  | add r s hr hs => simp only [add_smul,map_add,hr,hs]
  | tmul a c =>
    rw [←MulOpposite.op_unop c]
    change f (Enveloping.act k B (a⊗ₜ[k] MulOpposite.op c.unop) b)=
      Enveloping.act k B (f a⊗ₜ[k] MulOpposite.op (f c.unop)) (f b)
    simp only [Enveloping.act_tmul,map_mul]

end FiniteAlgebraicEnvelopes.NonunitalTensor
end

section

namespace FiniteAlgebraicEnvelopes.NonunitalTensor
open SequentialLimit
variable {k B : Type*} [CommRing k] [Ring B] [Algebra k B]
variable (φ : B →ₙₐ[k] B)

abbrev LinearGroup := Steinberg.ElementaryGroup (Enveloping.Coeff k B)

def linearAction : LinearGroup (k:=k) (B:=B) →* MulAut (Columns (B:=B)) := MatrixModule.elementaryAction

def linearStep : Monoid.End (LinearGroup (k:=k) (B:=B)) := Steinberg.elementaryTransition (coefficientRing φ)

theorem linear_column_compatible (x : LinearGroup (k:=k) (B:=B)) (v : Columns (B:=B)) :
    columnStep φ (linearAction x v)=linearAction (linearStep φ x) (columnStep φ v) := by
  apply Multiplicative.toAdd.injective
  exact MatrixModule.columnMap_corrected φ.toAddMonoidHom (coefficientRing φ)
    (coefficient_compatible φ) x.val.val v.toAdd

def limitAction : Limit (linearStep φ) →* MulAut (Limit (columnStep φ)) :=
  LimitAction.action linearAction (linearStep φ) (columnStep φ) (linear_column_compatible φ)

end FiniteAlgebraicEnvelopes.NonunitalTensor
end

end

end OAI
end

section
-- module Solutions.OAIFAE.ActionEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Full finitely presented faithful two-transitive action envelope and type-(A) applications.
-/

namespace FiniteAlgebraicEnvelopes.NonunitalTensor

section
open SequentialLimit
variable {k B : Type*} [CommRing k] [Ring B] [Algebra k B]
variable (φ : B →ₙₐ[k] B)

def torusAction : Torus (linearStep φ) →* MulAut (Limit (columnStep φ)) :=
  LimitAction.torusAction (linearAction (k:=k) (B:=B)) (linearStep φ) (columnStep φ)
    (linear_column_compatible φ)

@[simp] theorem torusAction_inl (x : Limit (linearStep φ)) :
    torusAction φ (SemidirectProduct.inl x)=limitAction φ x := by
  exact LimitAction.torusAction_inl _ _ _ _ x

abbrev SteinbergGroup := Steinberg.Group (Fin 6) (Enveloping.Coeff k B)
def steinbergStep : Monoid.End (SteinbergGroup (k:=k) (B:=B)) :=
  Steinberg.coefficientMap (coefficientRing φ)

theorem steinberg_column_compatible (x : SteinbergGroup (k:=k) (B:=B)) (v : Columns (B:=B)) :
    columnStep φ (AffineAction.action x v)=AffineAction.action (steinbergStep φ x) (columnStep φ v) := by
  rw [←MatrixModule.elementaryAction_quotient,←MatrixModule.elementaryAction_quotient]
  change columnStep φ (linearAction (Steinberg.elementaryQuotient x) v)=
    linearAction (Steinberg.elementaryQuotient (steinbergStep φ x)) (columnStep φ v)
  erw [steinbergStep,Steinberg.elementary_natural]
  exact linear_column_compatible φ _ _

def affineSteinbergStep : Monoid.End ((Columns (B:=B)) ⋊[AffineAction.action] SteinbergGroup (k:=k) (B:=B)) :=
  LimitAction.affineStep AffineAction.action (steinbergStep φ) (columnStep φ)
    (steinberg_column_compatible φ)

def affineTorusFullEquivalence (p q : Steinberg.SupportedPair (φ : B →ₙ+* B))
    (hpq : p.V*q.U=0) (hqp : q.V*p.U=0) (hsum : p.U*p.V+q.U*q.V=φ 1) :
    Torus (affineSteinbergStep φ) ≃* (Limit (columnStep φ)) ⋊[torusAction φ] Torus (linearStep φ) :=
  LimitAction.affineQuotientFullEquivalence AffineAction.action linearAction
    (steinbergStep φ) (linearStep φ) (columnStep φ)
    (steinberg_column_compatible φ) (linear_column_compatible φ)
    Steinberg.elementaryQuotient (Steinberg.elementary_natural (coefficientRing φ))
    (by intro x v; exact DFunLike.congr_fun (MatrixModule.elementaryAction_quotient x).symm v)
    Steinberg.elementaryQuotient_surjective
    (by intro x hx; apply annihilation φ p q hpq hqp hsum x; exact congrArg Subtype.val hx)

end

open SequentialLimit

end FiniteAlgebraicEnvelopes.NonunitalTensor

section
namespace FiniteAlgebraicEnvelopes.Contracted
instance countableAlgebra (k H : Type*) [CommRing k] [MonoidWithZero H] [Countable k] [Countable H] :
    Countable (Algebra k H) := by
  let : Countable (MonoidAlgebra k H) := MonoidAlgebra.coeff_injective.countable
  exact (zeroIdeal k H).ringCon.mkₐ_surjective (α:=k) |>.countable
end FiniteAlgebraicEnvelopes.Contracted
namespace FiniteAlgebraicEnvelopes.Bootstrap.Source
variable {G : Type*} [Group G] {n : ℕ} (s : Fin n → G)
variable (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word n => evalWord s w=1))

instance bigAlgebra_countable : Countable (BigAlgebra s h (ZMod 2)) := by
  let : Countable (K s h) := (PresentedMonoid.surjective_mk (rels := Compiler.Word.Rel (KAlphabet) (KMachine s h))).countable
  exact Contracted.countableAlgebra _ _

def columnTransition : Monoid.End (Multiplicative (Fin 6 → BigAlgebra s h (ZMod 2))) :=
  ColumnLimit.transition (phi s h (ZMod 2) : _ →ₙ+* _)

abbrev ColumnSpace := SequentialLimit.Limit (columnTransition s h)

instance columnSpace_countable : Countable (ColumnSpace s h) := by
  let : Countable (Multiplicative (Fin 6 → BigAlgebra s h (ZMod 2))) := Multiplicative.toAdd.injective.countable
  exact SequentialLimit.countable_limit (columnTransition s h)

end FiniteAlgebraicEnvelopes.Bootstrap.Source
end

namespace FiniteAlgebraicEnvelopes.Bootstrap.Source

section
variable {G : Type*} [Group G] {n : ℕ} (s : Fin n → G)
variable (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word n => evalWord s w=1))
variable (k : Type*) [CommRing k] [Nontrivial k]

def linearAction := NonunitalTensor.limitAction (phi s h k)

end

end FiniteAlgebraicEnvelopes.Bootstrap.Source

namespace FiniteAlgebraicEnvelopes.SequentialLimit
variable {Q : Type*} [Group Q] (f : Monoid.End Q)

instance torus_finitelyGenerated [Group.FG Q] : Group.FG (Torus f) := by
  obtain ⟨S,hS,hfin⟩ := Group.fg_iff.mp (inferInstance : Group.FG Q)
  let T : Set (Torus f) := insert (stable f) (base f '' S)
  let H := Subgroup.closure T
  have ht : stable f∈H := Subgroup.subset_closure (Set.mem_insert _ _)
  have hb (x : Q) : base f x∈H := by
    have hh : Subgroup.closure S≤H.comap (base f) := (Subgroup.closure_le (H.comap (base f))).mpr (by
      intro x hx
      exact Subgroup.subset_closure (Set.mem_insert_of_mem _ ⟨x,hx,rfl⟩))
    rw [hS] at hh
    exact hh (Subgroup.mem_top x)
  have hl (x : Limit f) : (SemidirectProduct.inl x : Torus f)∈H := by
    obtain ⟨i,q,rfl⟩ := DirectLimit.exists_eq_mk (transition f) x
    change SemidirectProduct.inl (of f i q)∈H
    rw [inl_of]
    exact H.mul_mem (H.mul_mem (H.pow_mem ht i) (hb q)) (H.inv_mem (H.pow_mem ht i))
  have hr (z : Multiplicative ℤ) : (SemidirectProduct.inr z : Torus f)∈H := by
    have he : z=(Multiplicative.ofAdd 1)^z.toAdd := by
      apply Multiplicative.toAdd.injective
      simp
    have he' : (SemidirectProduct.inr z : Torus f)=(stable f)^z.toAdd := by
      calc
        _ = SemidirectProduct.inr ((Multiplicative.ofAdd 1)^z.toAdd) := congrArg SemidirectProduct.inr he
        _ = _ := map_zpow SemidirectProduct.inr _ _
    rw [he']
    exact H.zpow_mem ht _
  apply Group.fg_iff.mpr
  refine ⟨T,?_,(hfin.image (base f)).insert (stable f)⟩
  apply top_unique
  intro a _
  change a∈H
  rcases a with ⟨x,z⟩
  rw [SemidirectProduct.mk_eq_inl_mul_inr]
  exact H.mul_mem (hl x) (hr z)

end FiniteAlgebraicEnvelopes.SequentialLimit

namespace FiniteAlgebraicEnvelopes.Bootstrap.Source
variable {G : Type*} [Group G] {n : ℕ} (s : Fin n → G)
variable (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word n => evalWord s w=1))

abbrev LinearTorus := SequentialLimit.Torus (NonunitalTensor.linearStep (phi s h (ZMod 2)))

def fullLinearAction : LinearTorus s h →* MulAut (ColumnSpace s h) :=
  NonunitalTensor.torusAction (phi s h (ZMod 2))

abbrev FullGroup := ColumnSpace s h ⋊[fullLinearAction s h] LinearTorus s h

def affineTransition := NonunitalTensor.affineSteinbergStep (phi s h (ZMod 2))

/-- The literal affine-Steinberg mapping torus is the previously constructed full action group. -/
def affineTorusEquivalence : SequentialLimit.Torus (affineTransition s h) ≃* FullGroup s h :=
  NonunitalTensor.affineTorusFullEquivalence (phi s h (ZMod 2)) (pair0 s h (ZMod 2)) (pair1 s h (ZMod 2))
    (pair0_pair1 s h (ZMod 2)) (pair1_pair0 s h (ZMod 2)) (pairs_sum s h (ZMod 2))

end FiniteAlgebraicEnvelopes.Bootstrap.Source

namespace FiniteAlgebraicEnvelopes.Bootstrap.Source
open scoped commutatorElement
variable {G H : Type*} [Group G] [Group H] {n : ℕ} (s : Fin n → H)
variable (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word n => evalWord s w=1))
variable (hs : Subgroup.closure (Set.range s)=⊤)
variable (f : G×G →* H) (t : H) (hc : ∀ g : G, ⁅f (g,g),t⁆=f (g,1))

def elementaryInput : G →* Steinberg.ElementaryGroup (R s h (ZMod 2)) :=
  Steinberg.elementaryEmbedding ((coefficientUnits s h (ZMod 2) hs).comp f)
    (coefficientUnits s h (ZMod 2) hs t) (by
      intro g
      change ⁅coefficientUnits s h (ZMod 2) hs (f (g,g)),coefficientUnits s h (ZMod 2) hs t⁆=
        coefficientUnits s h (ZMod 2) hs (f (g,1))
      rw [←map_commutatorElement,hc])

def elementaryInFull : Steinberg.ElementaryGroup (R s h (ZMod 2)) →* FullGroup s h :=
  SemidirectProduct.inr.comp (SemidirectProduct.inl.comp
    (SequentialLimit.of (NonunitalTensor.linearStep (phi s h (ZMod 2))) 0))

def inputInFull : G →* FullGroup s h :=
  (elementaryInFull s h).comp (elementaryInput s h hs f t hc)

end FiniteAlgebraicEnvelopes.Bootstrap.Source

end

end OAI
end

section
-- module Solutions.OAIFAE.CantorBricks
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Cantor prefixes, bricks, charts, finite-table group, localization, and displacement.
-/

namespace FiniteAlgebraicEnvelopes.TwistedBrinThompson

section
universe u v
attribute [local instance] Classical.propDecidable
namespace Prefix
variable {X : Type u}

lemma extends_of_ranges {p q : Prefix X}
    (h : ∀ z, (∃ w, q.attach w=z) → ∃ w, p.attach w=z) : p.Extends q := by
  intro x
  by_cases hl : (p.word x).length ≤ (q.word x).length
  · let z : Cube X := q.attach (fun _ _ => false)
    have hp := (mem_range_iff p z).mp (h z ⟨fun _ _ => false,rfl⟩) x
    have htake : (z x).take (p.word x).length = (q.word x).take (p.word x).length :=
      Stream'.take_append_of_le_length _ _ _ hl
    rw [htake] at hp
    rw [← hp]
    exact List.take_prefix _ _
  · have hlt : (q.word x).length < (p.word x).length := by omega
    let a₀ : Stream' Bool := fun _ => false
    let a₁ : Stream' Bool := fun _ => true
    let z₀ : Cube X := q.attach (fun _ => a₀)
    let z₁ : Cube X := q.attach (fun _ => a₁)
    have hp₀ := (mem_range_iff p z₀).mp (h z₀ ⟨fun _ => a₀,rfl⟩) x
    have hp₁ := (mem_range_iff p z₁).mp (h z₁ ⟨fun _ => a₁,rfl⟩) x
    have he := congrArg (fun (l : List Bool) => l[(q.word x).length]?) (hp₀.trans hp₁.symm)
    rw [Stream'.getElem?_take hlt,Stream'.getElem?_take hlt] at he
    simp only [z₀,z₁,attach] at he
    rw [Stream'.get_append_length,Stream'.get_append_length] at he
    simp [a₀,a₁,Stream'.get] at he

end Prefix

end

universe u v
attribute [local instance] Classical.propDecidable

variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]

namespace Table
variable {f : Equiv.Perm (Cube X)}

lemma refined_chart (A : Table (Γ:=Γ) f) (i : A.index) (r : Prefix X) (z : Cube X) :
    f (((A.source i).comp r).attach z) =
      ((A.target i).comp (twistPrefix (A.label i) r)).attach (twist (A.label i) z) := by
  rw [Prefix.comp_attach,A.chart,twist_attach,Prefix.comp_attach]

end Table

end FiniteAlgebraicEnvelopes.TwistedBrinThompson

end

end OAI
end

section
-- module Solutions.OAIFAE.TwistedSimplicity
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Partition refinement, simplicity, faithful group embedding, and countability.
-/

namespace FiniteAlgebraicEnvelopes.TwistedBrinThompson

section
universe u v
attribute [local instance] Classical.propDecidable
namespace Prefix
variable {X : Type v}

lemma eq_of_range_eq {p q : Prefix X} (h : Set.range p.attach=Set.range q.attach) : p=q := by
  have hpq : p.Extends q := extends_of_ranges (by
    intro z hz
    change z∈Set.range p.attach
    rw [h]
    exact hz)
  have hqp : q.Extends p := extends_of_ranges (by
    intro z hz
    change z∈Set.range q.attach
    rw [← h]
    exact hz)
  apply Prefix.ext
  intro x
  exact List.Sublist.antisymm (hpq x).sublist (hqp x).sublist

end Prefix

variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]

lemma chart_prefix_rigidity {p q : Prefix X} {a b : Γ}
    (h : ∀ z : Cube X,p.attach (twist a z)=q.attach (twist b z)) : p=q := by
  apply Prefix.eq_of_range_eq
  ext z
  constructor
  · rintro ⟨w,rfl⟩
    refine ⟨twist b (twist a⁻¹ w),?_⟩
    rw [← h,twist_twist_inv]
  · rintro ⟨w,rfl⟩
    refine ⟨twist a (twist b⁻¹ w),?_⟩
    rw [h,twist_twist_inv]

lemma chart_rigidity [FaithfulSMul Γ X] {p q : Prefix X} {a b : Γ}
    (h : ∀ z : Cube X,p.attach (twist a z)=q.attach (twist b z)) : p=q ∧ a=b := by
  have hp := chart_prefix_rigidity h
  refine ⟨hp,?_⟩
  subst q
  apply twist_injective (X:=X)
  apply Equiv.ext
  intro z
  exact p.attach_injective (h z)

end

section
universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]

namespace Partition

/-- Shift a split from an exterior brick to the selected one. -/
def splitShift (P : Partition X) (i j : P.index) :
    ({k : P.index // k≠j} ⊕ Bool) ≃ ({k : P.index // k≠i} ⊕ Bool) :=
  Equiv.sumCongr (Equiv.subtypeEquiv (Equiv.swap i j) (by
    intro k
    constructor
    · intro hk he
      apply hk
      have h := congrArg (Equiv.swap i j) he
      simpa using h
    · intro hk he
      subst k
      simp at hk)) (Equiv.refl Bool)

def compressIndex (P : Partition X) (i j : P.index) (hji : j≠i) (b : Bool) :
    ({k : P.index // k≠j} ⊕ Bool) ≃ ({k : P.index // k≠i} ⊕ Bool) :=
  (splitShift P i j).trans
    (Equiv.swap (Sum.inl (⟨j,hji⟩ : {k : P.index // k≠i})) (Sum.inr b))

end Partition

end

section
universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]

lemma Prefix.comp_oneBit_comm {p : Prefix X} {x : X} (hx : p.word x=[]) (b : Bool) :
    p.comp (Prefix.oneBit x b)=(Prefix.oneBit x b).comp p := by
  apply Prefix.ext
  intro y
  by_cases hy : y=x
  · subst y; simp [hx]
  · simp [hy]

lemma localizePerm_comp (p q : Prefix X) (f : Equiv.Perm (Cube X)) :
    localizePerm (p.comp q) f=localizePerm p (localizePerm q f) := by
  apply Equiv.ext
  intro z
  by_cases hz : z∈Set.range p.attach
  · obtain ⟨w,rfl⟩ := hz
    rw [localizePerm_attach]
    by_cases hw : w∈Set.range q.attach
    · obtain ⟨a,rfl⟩ := hw
      rw [← Prefix.comp_attach,localizePerm_attach,localizePerm_attach,Prefix.comp_attach]
    · have hn : p.attach w∉Set.range (p.comp q).attach := by
        rintro ⟨a,ha⟩
        apply hw
        exact ⟨a,p.attach_injective ((Prefix.comp_attach _ _ _).symm.trans ha)⟩
      rw [localizePerm_outside _ _ hn,localizePerm_outside _ _ hw]
  · have hn : z∉Set.range (p.comp q).attach := by
      rintro ⟨a,rfl⟩
      exact hz ⟨q.attach a,Prefix.comp_attach _ _ _ |>.symm⟩
    rw [localizePerm_outside _ _ hn,localizePerm_outside _ _ hz]

lemma localize_comp (p q : Prefix X) (f : group (Γ:=Γ) (X:=X)) :
    localize (p.comp q) f=localize p (localize q f) :=
  Subtype.ext (localizePerm_comp p q f.val)

/-- Two equal local copies in the coordinate halves. -/
def diagonal (x : X) (f : group (Γ:=Γ) (X:=X)) : group (Γ:=Γ) (X:=X) :=
  localize (Prefix.oneBit x false) f * localize (Prefix.oneBit x true) f

lemma diagonal_attach (x : X) (f : group (Γ:=Γ) (X:=X)) (b : Bool) (z : Cube X) :
    (diagonal x f).val ((Prefix.oneBit x b).attach z)=
      (Prefix.oneBit x b).attach (f.val z) := by
  have hout (a c : Bool) (hac : a≠c) (w : Cube X) :
      (Prefix.oneBit x a).attach w∉Set.range (Prefix.oneBit x c).attach := by
    intro hh
    have hc := (Prefix.mem_oneBit x c _).mp hh
    have ha := (Prefix.mem_oneBit x a _).mp ⟨w,rfl⟩
    exact hac (ha.symm.trans hc)
  change localizePerm (Prefix.oneBit x false) f.val
    (localizePerm (Prefix.oneBit x true) f.val ((Prefix.oneBit x b).attach z))=_
  cases b
  · rw [localizePerm_outside _ _ (hout false true Bool.false_ne_true z),localizePerm_attach]
  · rw [localizePerm_attach,
      localizePerm_outside _ _ (hout true false (Ne.symm Bool.false_ne_true) (f.val z))]

/-- A table with no coordinate twisting on any chart. -/
def Untwisted (f : group (Γ:=Γ) (X:=X)) : Prop :=
  ∃ A : Table (Γ:=Γ) f.val, ∀ i,A.label i=1

end

section
universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Table
variable {f : group (Γ:=Γ) (X:=X)}

abbrev CorrectionIndex (A : Table (Γ:=Γ) f.val) := Bool × A.index

instance correctionIndex_finite (A : Table (Γ:=Γ) f.val) : Fintype (CorrectionIndex A) := by
  letI := A.finite
  exact inferInstanceAs (Fintype (Bool × A.index))

def correctionSource (A : Table (Γ:=Γ) f.val) (x : X) (bi : CorrectionIndex A) : Prefix X :=
  (Prefix.oneBit x bi.1).comp (A.target bi.2)

def correctionTarget (A : Table (Γ:=Γ) f.val) (x : X) (bi : CorrectionIndex A) : Prefix X :=
  (A.target bi.2).comp (twistPrefix (A.label bi.2) (Prefix.oneBit x bi.1))

lemma correction_chart (A : Table (Γ:=Γ) f.val) (x : X)
    (hx : ∀ i,(A.source i).word x=[]) (bi : CorrectionIndex A) (z : Cube X) :
    (f * (diagonal x f)⁻¹).val ((correctionSource A x bi).attach z)=
      (correctionTarget A x bi).attach (twist (1 : Γ) z) := by
  obtain ⟨b,i⟩ := bi
  have hd : (diagonal x f).val
      (((Prefix.oneBit x b).comp (A.source i)).attach (twist (A.label i)⁻¹ z))=
      ((Prefix.oneBit x b).comp (A.target i)).attach z := by
    rw [Prefix.comp_attach,diagonal_attach,A.chart,twist_twist_inv,Prefix.comp_attach]
  have hi : (diagonal x f).val.symm
      (((Prefix.oneBit x b).comp (A.target i)).attach z)=
      ((Prefix.oneBit x b).comp (A.source i)).attach (twist (A.label i)⁻¹ z) := by
    apply (diagonal x f).val.injective
    rw [Equiv.apply_symm_apply,hd]
  change f.val ((diagonal x f).val.symm
    (((Prefix.oneBit x b).comp (A.target i)).attach z))=
    ((A.target i).comp (twistPrefix (A.label i) (Prefix.oneBit x b))).attach (twist (1 : Γ) z)
  rw [hi,← Prefix.comp_oneBit_comm (hx i),A.refined_chart,twist_twist_inv,twist_one]
  rfl

/-- All coordinate labels cancel when a table is compared with its double along
a coordinate unused by its source prefixes. -/
def correction (A : Table (Γ:=Γ) f.val) (x : X)
    (hx : ∀ i,(A.source i).word x=[]) : Table (Γ:=Γ) (f * (diagonal x f)⁻¹).val where
  index := CorrectionIndex A
  finite := correctionIndex_finite A
  source := correctionSource A x
  target := correctionTarget A x
  label _ := 1
  source_cover := (Partition.allRefine (Partition.bit x) A.targetPartition).cover
  target_cover := transport_partition _ _ _ _
    (Partition.allRefine (Partition.bit x) A.targetPartition).cover
    (correction_chart A x hx)
  chart := correction_chart A x hx

end Table

end

section
universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Partition

abbrev size (P : Partition X) : ℕ := @Fintype.card P.index P.finite

end Partition

end

universe u v
attribute [local instance] Classical.propDecidable
namespace Prefix
variable {X : Type v}

instance instCountable [Countable X] : Countable (Prefix X) := by
  let : Zero (List Bool) := ⟨[]⟩
  let encode (p : Prefix X) : X →₀ List Bool := Finsupp.ofSupportFinite p.word p.finite_support
  apply Function.Injective.countable (f:=encode)
  intro p q hpq
  apply Prefix.ext
  intro x
  exact congrArg (fun f : X →₀ List Bool => f x) hpq

end Prefix

end FiniteAlgebraicEnvelopes.TwistedBrinThompson

end

end OAI
end

section
-- module Solutions.OAIFAE.Trees
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Coordinate grids, binary trees, and tree-pair representatives.
-/

namespace FiniteAlgebraicEnvelopes.TwistedBrinThompson

section
universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Table
variable {f : Equiv.Perm (Cube X)}

def reindex (A : Table (Γ:=Γ) f) {I : Type} [Fintype I] (e : I ≃ A.index) : Table (Γ:=Γ) f where
  index := I
  finite := inferInstance
  source i := A.source (e i)
  target i := A.target (e i)
  label i := A.label (e i)
  source_cover := by
    intro z
    obtain ⟨i,hi,hu⟩ := A.source_cover z
    refine ⟨e.symm i,by simpa using hi,?_⟩
    intro j hj
    apply e.injective
    simpa using hu (e j) hj
  target_cover := by
    intro z
    obtain ⟨i,hi,hu⟩ := A.target_cover z
    refine ⟨e.symm i,by simpa using hi,?_⟩
    intro j hj
    apply e.injective
    simpa using hu (e j) hj
  chart i z := A.chart (e i) z

abbrev FamilyIndex (A : Table (Γ:=Γ) f) (P : A.index → Partition X) := (i : A.index) × (P i).index

instance familyIndex_fintype (A : Table (Γ:=Γ) f) (P : A.index → Partition X) :
    Fintype (FamilyIndex A P) := by
  letI := A.finite
  letI (i : A.index) := (P i).finite
  exact inferInstanceAs (Fintype ((i : A.index) × (P i).index))

lemma family_source_cover (A : Table (Γ:=Γ) f) (P : A.index → Partition X) :
    ∀ z : Cube X,∃! ij : FamilyIndex A P,
      ∃ w,((A.source ij.1).comp ((P ij.1).brick ij.2)).attach w=z := by
  intro z
  obtain ⟨i,⟨w,hw⟩,hi⟩ := A.source_cover z
  obtain ⟨j,⟨r,hr⟩,hj⟩ := (P i).cover w
  refine ⟨⟨i,j⟩,⟨r,?_⟩,?_⟩
  · rw [Prefix.comp_attach,hr,hw]
  · rintro ⟨k,l⟩ ⟨a,ha⟩
    rw [Prefix.comp_attach] at ha
    have hki : k=i := hi k ⟨(P k).brick l |>.attach a,ha⟩
    subst k
    have hlj := hj l ⟨a,(A.source i).attach_injective (ha.trans hw.symm)⟩
    subst l
    rfl

/-- Refining each chart by an independently chosen finite partition preserves
its actual cube permutation and transports the tail with the original label. -/
def refineFamily (A : Table (Γ:=Γ) f) (P : A.index → Partition X) : Table (Γ:=Γ) f where
  index := FamilyIndex A P
  finite := familyIndex_fintype A P
  source ij := (A.source ij.1).comp ((P ij.1).brick ij.2)
  target ij := (A.target ij.1).comp (twistPrefix (A.label ij.1) ((P ij.1).brick ij.2))
  label ij := A.label ij.1
  source_cover := family_source_cover A P
  target_cover := transport_partition _ _ _ _ (family_source_cover A P) (by
    intro ij z
    exact A.refined_chart ij.1 ((P ij.1).brick ij.2) z)
  chart ij z := A.refined_chart ij.1 ((P ij.1).brick ij.2) z

lemma exists_source_tree (A : Table (Γ:=Γ) f) :
    ∃ (t : Tree X) (B : Table (Γ:=Γ) f) (e : B.index ≃ t.Leaves),
      ∀ i,B.source i=t.brick (e i) := by
  classical
  let := A.finite
  obtain ⟨l,hl⟩ := Partition.exists_tree_grid_bound A.source
  let P (i : A.index) := (Tree.grid (l.diff (A.source i).schedule)).partition
  let B := A.refineFamily P
  have hb (ij : B.index) (x : X) : ((B.source ij).word x).length=l.count x := by
    change ((A.source ij.1).word x ++ ((Tree.grid (l.diff (A.source ij.1).schedule)).brick ij.2).word x).length=_
    rw [List.length_append,Tree.grid_length,List.count_diff,Prefix.schedule_count]
    exact Nat.add_sub_of_le (hl ij.1 x)
  have he := B.sourcePartition.grid_bricks_of_lengths l hb
  exact ⟨Tree.grid l,B,B.sourcePartition.indexEquivOfBricks (Tree.grid l).partition he,
    fun i => (he i).choose_spec⟩

end Table
end

universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Table
variable {f : Equiv.Perm (Cube X)}

/-- Every actual finite labelled table admits a coloured tree-pair model.
This is the normal form needed for a forest presentation; it does not by itself
prove finite presentation. -/
lemma exists_tree_pair (A : Table (Γ:=Γ) f) :
    ∃ (s t : Tree X) (B : Table (Γ:=Γ) f)
      (es : B.index ≃ s.Leaves) (et : B.index ≃ t.Leaves),
      (∀ i,B.source i=s.brick (es i)) ∧ (∀ i,B.target i=t.brick (et i)) := by
  classical
  obtain ⟨s,B,e,he⟩ := A.exists_source_tree
  let C := B.reindex e.symm
  have hc (i : s.Leaves) : C.source i=s.brick i := by
    exact (he (e.symm i)).trans (by simp)
  let := C.finite
  obtain ⟨l,hl⟩ := Partition.exists_tree_grid_bound C.target
  let Q (i : s.Leaves) : Tree X :=
    Tree.grid ((l.diff (C.target i).schedule).map (fun x => (C.label i)⁻¹ • x))
  let D := C.refineFamily (fun i => (Q i).partition)
  have hd (ij : D.index) (x : X) : ((D.target ij).word x).length=l.count x := by
    change ((C.target ij.1).word x ++
      ((Q ij.1).brick ij.2).word ((C.label ij.1)⁻¹ • x)).length=_
    rw [List.length_append,Tree.grid_length]
    rw [List.count_map_of_injective _ _ (MulAction.injective _),List.count_diff,Prefix.schedule_count]
    exact Nat.add_sub_of_le (hl ij.1 x)
  have ht := D.targetPartition.grid_bricks_of_lengths l hd
  refine ⟨s.graft Q,Tree.grid l,D,(s.graftLeaves Q).symm,
    D.targetPartition.indexEquivOfBricks (Tree.grid l).partition ht,?_,fun i => (ht i).choose_spec⟩
  intro ij
  change (C.source ij.1).comp ((Q ij.1).brick ij.2)=
    (s.graft Q).brick ((s.graftLeaves Q).symm ⟨ij.1,ij.2⟩)
  rw [Tree.graft_prefix,Equiv.apply_symm_apply]
  exact congrArg (fun p => p.comp ((Q ij.1).brick ij.2)) (hc ij.1)

end Table
end FiniteAlgebraicEnvelopes.TwistedBrinThompson

end

end OAI
end

section
-- module Solutions.OAIFAE.Generators
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Concrete finite generators of the twisted group.
-/

namespace FiniteAlgebraicEnvelopes.TwistedBrinThompson

section
universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Generators

lemma associator_left (x : X) (z : Cube X) :
    (associator (Γ:=Γ) x).val ((left x).attach z)=
      ((left x).comp (left x)).attach z := by
  have h := Partition.changeChart_apply (Γ:=Γ)
    (Tree.split x Tree.leaf (Tree.split x Tree.leaf Tree.leaf)).partition
    (Tree.split x (Tree.split x Tree.leaf Tree.leaf) Tree.leaf).partition
    (Equiv.sumAssoc PUnit PUnit PUnit).symm (Sum.inl PUnit.unit) z
  simpa only [associator,left,Equiv.sumAssoc_symm_apply_inl,Tree.partition,Tree.brick,Prefix.comp_empty] using h

def subgroup (x : X) : Subgroup (group (Γ:=Γ) (X:=X)) :=
  (embedding (Γ:=Γ) (X:=X)).range ⊔ ((localize (left x)).comp embedding).range ⊔
    Subgroup.closure (↑(finiteSet (Γ:=Γ) x) : Set (group (Γ:=Γ) (X:=X)))

lemma root_mem (x : X) (g : Γ) : embedding g∈subgroup (Γ:=Γ) x :=
  (show (embedding (Γ:=Γ) (X:=X)).range ≤ subgroup (Γ:=Γ) x from (le_sup_left.trans le_sup_left)) ⟨g,rfl⟩

lemma half_root_mem (x : X) (g : Γ) : localize (left x) (embedding g)∈subgroup (Γ:=Γ) x :=
  (show ((localize (left x)).comp (embedding (Γ:=Γ) (X:=X))).range ≤ subgroup (Γ:=Γ) x from (le_sup_right.trans le_sup_left)) ⟨g,rfl⟩

lemma finite_mem (x : X) {g : group (Γ:=Γ) (X:=X)} (hg : g∈finiteSet x) : g∈subgroup x :=
by
  change g∈(embedding (Γ:=Γ) (X:=X)).range ⊔ ((localize (left x)).comp embedding).range ⊔
    Subgroup.closure (↑(finiteSet (Γ:=Γ) x) : Set (group (Γ:=Γ) (X:=X)))
  exact Subgroup.mem_sup_right (Subgroup.subset_closure hg)

lemma associator_mem (x : X) : associator (Γ:=Γ) x∈subgroup x :=
  finite_mem x (by simp [finiteSet])
lemma flip_mem (x : X) : flip (Γ:=Γ) x∈subgroup x :=
  finite_mem x (by simp [finiteSet])
lemma half_associator_mem (x : X) : localize (left x) (associator (Γ:=Γ) x)∈subgroup x :=
  finite_mem x (by simp [finiteSet])
lemma half_flip_mem (x : X) : localize (left x) (flip (Γ:=Γ) x)∈subgroup x :=
  finite_mem x (by simp [finiteSet])

lemma double_local_mem (x : X) (g : group (Γ:=Γ) (X:=X))
    (hg : localize (left x) g∈subgroup x) :
    localize (left x) (localize (left x) g)∈subgroup x := by
  rw [← localize_comp,← localize_conj (associator x) (associator_left x)]
  exact (subgroup x).mul_mem ((subgroup x).mul_mem (associator_mem x) hg)
    ((subgroup x).inv_mem (associator_mem x))

lemma left_local_mem (x : X) {g : group (Γ:=Γ) (X:=X)} (hg : g∈subgroup x) :
    localize (left x) g∈subgroup x := by
  have h : subgroup (Γ:=Γ) x≤(subgroup x).comap (localize (left x)) := by
    refine sup_le (sup_le ?_ ?_) ((Subgroup.closure_le _).2 ?_)
    · rintro g ⟨a,rfl⟩
      exact half_root_mem x a
    · rintro g ⟨a,rfl⟩
      exact double_local_mem x (embedding a) (half_root_mem x a)
    · intro a ha
      simp only [finiteSet,Finset.coe_insert,Finset.coe_singleton,Set.mem_insert_iff,
        Set.mem_singleton_iff] at ha
      rcases ha with rfl|rfl|rfl|rfl
      · exact half_associator_mem x
      · exact double_local_mem x _ (half_associator_mem x)
      · exact half_flip_mem x
      · exact double_local_mem x _ (half_flip_mem x)
  exact h hg

lemma right_local_mem (x : X) {g : group (Γ:=Γ) (X:=X)} (hg : g∈subgroup x) :
    localize (right x) g∈subgroup x := by
  rw [← localize_conj (flip x) (flip_left x)]
  exact (subgroup x).mul_mem ((subgroup x).mul_mem (flip_mem x) (left_local_mem x hg))
    ((subgroup x).inv_mem (flip_mem x))

end Generators
end

section
universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]

namespace Generators

lemma baker_inverse (x y : X) : (baker (Γ:=Γ) x y)⁻¹=baker y x := by
  apply Subtype.ext
  apply Equiv.ext
  intro z
  obtain ⟨b,⟨w,rfl⟩,_⟩ := (Partition.bit y).cover z
  apply (baker (Γ:=Γ) x y).val.injective
  change (baker (Γ:=Γ) x y).val ((baker (Γ:=Γ) x y).val.symm
    ((Prefix.oneBit y b).attach w))=_
  rw [Equiv.apply_symm_apply,baker_attach,baker_attach]

lemma baker_smul (x : X) (g : Γ) :
    baker (g • x) x=diagonal x (embedding g) * (embedding g)⁻¹ := by
  rw [← map_inv]
  apply Subtype.ext
  apply Equiv.ext
  intro z
  obtain ⟨b,⟨w,rfl⟩,_⟩ := (Partition.bit (g • x)).cover z
  rw [baker_attach]
  change _=(diagonal x (embedding g)).val (twist g⁻¹ ((Prefix.oneBit (g • x) b).attach w))
  rw [twist_attach,twistPrefix_oneBit,inv_smul_smul,diagonal_attach]
  change _=(Prefix.oneBit x b).attach (twist g (twist g⁻¹ w))
  rw [twist_twist_inv]

lemma baker_smul_mem (x : X) (g : Γ) : baker (g • x) x∈subgroup (Γ:=Γ) x := by
  rw [baker_smul]
  exact (subgroup x).mul_mem
    ((subgroup x).mul_mem (left_local_mem x (root_mem x g)) (right_local_mem x (root_mem x g)))
    ((subgroup x).inv_mem (root_mem x g))

variable [MulAction.IsPretransitive Γ X]

lemma baker_mem (x y : X) : baker (Γ:=Γ) x y∈subgroup x := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Γ x y
  have h := (subgroup (Γ:=Γ) x).inv_mem (baker_smul_mem x g)
  rwa [baker_inverse,hg] at h

lemma bit_local_mem (x y : X) (b : Bool) {g : group (Γ:=Γ) (X:=X)}
    (hg : g∈subgroup x) : localize (Prefix.oneBit y b) g∈subgroup x := by
  rw [← localize_conj (baker x y) (baker_attach x y b)]
  apply (subgroup x).mul_mem
  · apply (subgroup x).mul_mem (baker_mem x y)
    cases b
    · exact left_local_mem x hg
    · exact right_local_mem x hg
  · exact (subgroup x).inv_mem (baker_mem x y)

end Generators
end

section
universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]

namespace Generators
variable (x : X)
/-- A complete chart change between coloured splitting trees, already lying in
the proposed finite-generator subgroup. Leaf order is not imposed. -/
structure Move (s t : Tree X) where
  leaves : s.Leaves ≃ t.Leaves
  element : group (Γ:=Γ) (X:=X)
  mem_subgroup : element∈subgroup (Γ:=Γ) x
  chart : ∀ i z,element.val ((s.brick i).attach z)=(t.brick (leaves i)).attach z

namespace Move
variable {x : X} {s t r : Tree X}

def refl (s : Tree X) : Move (Γ:=Γ) x s s where
  leaves := Equiv.refl _
  element := 1
  mem_subgroup := (subgroup x).one_mem
  chart _ _ := rfl

def trans (h : Move (Γ:=Γ) x s t) (k : Move (Γ:=Γ) x t r) : Move (Γ:=Γ) x s r where
  leaves := h.leaves.trans k.leaves
  element := k.element*h.element
  mem_subgroup := (subgroup x).mul_mem k.mem_subgroup h.mem_subgroup
  chart i z := by
    change k.element.val (h.element.val ((s.brick i).attach z))=_
    rw [h.chart,k.chart]
    rfl

def symm (h : Move (Γ:=Γ) x s t) : Move (Γ:=Γ) x t s where
  leaves := h.leaves.symm
  element := h.element⁻¹
  mem_subgroup := (subgroup x).inv_mem h.mem_subgroup
  chart i z := by
    apply h.element.val.injective
    change h.element.val (h.element.val.symm ((t.brick i).attach z))=_
    rw [Equiv.apply_symm_apply,h.chart,Equiv.apply_symm_apply]

lemma element_eq_chart (h : Move (Γ:=Γ) x s t) :
    h.element=s.partition.changeChart t.partition h.leaves := by
  apply Subtype.ext
  apply Equiv.ext
  intro z
  obtain ⟨i,⟨w,rfl⟩,_⟩ := s.cover z
  exact (h.chart i w).trans (s.partition.changeChart_apply t.partition h.leaves i w).symm

variable [MulAction.IsPretransitive Γ X]

def join {s₁ s₂ t₁ t₂ : Tree X} (h : Move (Γ:=Γ) x s₁ t₁)
    (k : Move (Γ:=Γ) x s₂ t₂) (y : X) :
    Move (Γ:=Γ) x (Tree.split y s₁ s₂) (Tree.split y t₁ t₂) where
  leaves := Equiv.sumCongr h.leaves k.leaves
  element := sumElement y h.element k.element
  mem_subgroup := (subgroup x).mul_mem (bit_local_mem x y false h.mem_subgroup)
    (bit_local_mem x y true k.mem_subgroup)
  chart i z := by
    cases i with
    | inl i =>
      change (sumElement y h.element k.element).val
        (((Prefix.oneBit y false).comp (s₁.brick i)).attach z)=
        ((Prefix.oneBit y false).comp (t₁.brick (h.leaves i))).attach z
      rw [Prefix.comp_attach,Prefix.comp_attach,sumElement_left,h.chart]
    | inr i =>
      change (sumElement y h.element k.element).val
        (((Prefix.oneBit y true).comp (s₂.brick i)).attach z)=
        ((Prefix.oneBit y true).comp (t₂.brick (k.leaves i))).attach z
      rw [Prefix.comp_attach,Prefix.comp_attach,sumElement_right,k.chart]

def recolor (y : X) (a b : Tree X) :
    Move (Γ:=Γ) x (Tree.split y a b) (Tree.split x a b) where
  leaves := Equiv.refl _
  element := baker y x
  mem_subgroup := by
    rw [← baker_inverse]
    exact (subgroup x).inv_mem (baker_mem x y)
  chart i z := by
    cases i with
    | inl i =>
      change (baker (Γ:=Γ) y x).val (((Prefix.oneBit y false).comp (a.brick i)).attach z)=
        ((Prefix.oneBit x false).comp (a.brick i)).attach z
      rw [Prefix.comp_attach,Prefix.comp_attach,baker_attach]
    | inr i =>
      change (baker (Γ:=Γ) y x).val (((Prefix.oneBit y true).comp (b.brick i)).attach z)=
        ((Prefix.oneBit x true).comp (b.brick i)).attach z
      rw [Prefix.comp_attach,Prefix.comp_attach,baker_attach]

end Move

lemma associator_middle (x : X) (z : Cube X) :
    (associator (Γ:=Γ) x).val (((right x).comp (left x)).attach z)=
      ((left x).comp (right x)).attach z := by
  have h := Partition.changeChart_apply (Γ:=Γ)
    (Tree.split x Tree.leaf (Tree.split x Tree.leaf Tree.leaf)).partition
    (Tree.split x (Tree.split x Tree.leaf Tree.leaf) Tree.leaf).partition
    (Equiv.sumAssoc PUnit PUnit PUnit).symm (Sum.inr (Sum.inl PUnit.unit)) z
  simpa only [associator,left,right,Equiv.sumAssoc_symm_apply_inr_inl,Tree.partition,
    Tree.brick,Prefix.comp_empty] using h

lemma associator_right (x : X) (z : Cube X) :
    (associator (Γ:=Γ) x).val (((right x).comp (right x)).attach z)=
      (right x).attach z := by
  have h := Partition.changeChart_apply (Γ:=Γ)
    (Tree.split x Tree.leaf (Tree.split x Tree.leaf Tree.leaf)).partition
    (Tree.split x (Tree.split x Tree.leaf Tree.leaf) Tree.leaf).partition
    (Equiv.sumAssoc PUnit PUnit PUnit).symm (Sum.inr (Sum.inr PUnit.unit)) z
  simpa only [associator,left,right,Equiv.sumAssoc_symm_apply_inr_inr,Tree.partition,
    Tree.brick,Prefix.comp_empty] using h

namespace Move

def rotate (a b c : Tree X) :
    Move (Γ:=Γ) x (Tree.split x a (Tree.split x b c)) (Tree.split x (Tree.split x a b) c) where
  leaves := (Equiv.sumAssoc a.Leaves b.Leaves c.Leaves).symm
  element := associator x
  mem_subgroup := associator_mem x
  chart i z := by
    cases i with
    | inl i =>
      change (associator (Γ:=Γ) x).val (((left x).comp (a.brick i)).attach z)=
        ((left x).comp ((left x).comp (a.brick i))).attach z
      simp only [Prefix.comp_attach]
      simpa only [Prefix.comp_attach] using associator_left (Γ:=Γ) x ((a.brick i).attach z)
    | inr i =>
      cases i with
      | inl i =>
        change (associator (Γ:=Γ) x).val (((right x).comp ((left x).comp (b.brick i))).attach z)=
          ((left x).comp ((right x).comp (b.brick i))).attach z
        simpa only [Prefix.comp_attach] using associator_middle (Γ:=Γ) x ((b.brick i).attach z)
      | inr i =>
        change (associator (Γ:=Γ) x).val (((right x).comp ((right x).comp (c.brick i))).attach z)=
          ((right x).comp (c.brick i)).attach z
        simpa only [Prefix.comp_attach] using associator_right (Γ:=Γ) x ((c.brick i).attach z)

end Move

end Generators
end

section
universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Tree

lemma linear_card (x : X) (n : ℕ) : Fintype.card (linear x n).Leaves=n+1 := by
  induction n with
  | zero => exact Fintype.card_punit
  | succ n ih =>
    change Fintype.card (PUnit ⊕ (linear x n).Leaves)=n+1+1
    rw [Fintype.card_sum,Fintype.card_punit,ih]
    omega

end Tree
namespace Generators
variable (x : X) [MulAction.IsPretransitive Γ X]

/-- Binary associativity reduces two right combs to one right comb. -/
def linearJoin (m n : ℕ) :
    Move (Γ:=Γ) x (Tree.split x (Tree.linear x m) (Tree.linear x n))
      (Tree.linear x (m+n+1)) := by
  induction m with
  | zero =>
    simpa only [Nat.zero_add,Tree.linear] using
      (Move.refl (Γ:=Γ) (x:=x) (Tree.split x Tree.leaf (Tree.linear x n)))
  | succ m ih =>
    have h := (Move.rotate (Γ:=Γ) x Tree.leaf (Tree.linear x m) (Tree.linear x n)).symm
    have k := (Move.refl (Γ:=Γ) (x:=x) Tree.leaf).join ih x
    simpa only [Tree.linear,Nat.succ_add,Nat.add_succ] using h.trans k

lemma exists_linear (t : Tree X) :
    ∃ n : ℕ,Nonempty (Move (Γ:=Γ) x t (Tree.linear x n)) := by
  induction t with
  | leaf => exact ⟨0,⟨Move.refl Tree.leaf⟩⟩
  | split y a b ha hb =>
    obtain ⟨m,⟨h⟩⟩ := ha
    obtain ⟨n,⟨k⟩⟩ := hb
    exact ⟨m+n+1,⟨((h.join k y).trans (Move.recolor y _ _)).trans (linearJoin x m n)⟩⟩

end Generators
end

section
universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Generators

variable (x : X) [MulAction.IsPretransitive Γ X]

lemma join_permute_mem {a b : Tree X} (e : Equiv.Perm a.Leaves) (f : Equiv.Perm b.Leaves)
    (he : a.partition.permute (Γ:=Γ) e∈subgroup x)
    (hf : b.partition.permute (Γ:=Γ) f∈subgroup x) (y : X) :
    (Tree.split y a b).partition.permute (Γ:=Γ) (Equiv.sumCongr e f)∈subgroup x := by
  let h : Move (Γ:=Γ) x a a := ⟨e,a.partition.permute e,he,a.partition.permute_attach e⟩
  let k : Move (Γ:=Γ) x b b := ⟨f,b.partition.permute f,hf,b.partition.permute_attach f⟩
  have hh := (h.join k y).mem_subgroup
  rw [(h.join k y).element_eq_chart] at hh
  exact hh

omit [MulAction.IsPretransitive Γ X] in
lemma linear_two_swap :
    (Tree.linear x 1).partition.permute (Γ:=Γ)
      (fixedSwap (Sum.inl PUnit.unit) (Sum.inr PUnit.unit))=flip x := by
  classical
  apply Subtype.ext
  apply Equiv.ext
  intro z
  obtain ⟨i,⟨w,rfl⟩,_⟩ := (Tree.linear x 1).cover z
  rw [Partition.permute_attach]
  cases i with
  | inl i =>
    cases i
    simp only [Equiv.swap_apply_left,Tree.partition,Tree.linear,Tree.brick,
      Prefix.comp_empty,flip_attach,Bool.not_false]
  | inr i =>
    cases i
    simp only [Equiv.swap_apply_right,Tree.partition,Tree.linear,Tree.brick,
      Prefix.comp_empty,flip_attach,Bool.not_true]

omit [MulAction.IsPretransitive Γ X] in
/-- The first two leaves of every nontrivial right comb can be interchanged
using the associator and a half-flip. -/
lemma linear_front_swap (n : ℕ) :
    (Tree.linear x (n+2)).partition.permute (Γ:=Γ)
      (fixedSwap (Sum.inl PUnit.unit) (Sum.inr (Sum.inl PUnit.unit)))=
      (associator x)⁻¹ * localize (left x) (flip x) * associator x := by
  classical
  apply (mul_left_cancel_iff (a:=associator (Γ:=Γ) x)).mp
  rw [← mul_assoc,← mul_assoc,mul_inv_cancel,one_mul]
  apply Subtype.ext
  apply Equiv.ext
  intro z
  obtain ⟨i,⟨w,rfl⟩,_⟩ := (Tree.linear x (n+2)).cover z
  change (associator (Γ:=Γ) x).val
    (((Tree.linear x (n+2)).partition.permute (Γ:=Γ)
      (fixedSwap (Sum.inl PUnit.unit) (Sum.inr (Sum.inl PUnit.unit)))).val
      (((Tree.linear x (n+2)).brick i).attach w))=
    localizePerm (left x) (flip (Γ:=Γ) x).val
      ((associator (Γ:=Γ) x).val (((Tree.linear x (n+2)).brick i).attach w))
  rw [Partition.permute_attach]
  cases i with
  | inl i =>
    cases i
    simp only [Equiv.swap_apply_left,Tree.partition,Tree.linear,Tree.brick,Prefix.comp_empty]
    rw [associator_middle,associator_left]
    simp only [Prefix.comp_attach,localizePerm_attach,flip_attach,Bool.not_false]
  | inr i =>
    cases i with
    | inl i =>
      cases i
      simp only [Equiv.swap_apply_right,Tree.partition,Tree.linear,Tree.brick,Prefix.comp_empty]
      rw [associator_left,associator_middle]
      simp only [Prefix.comp_attach,localizePerm_attach,flip_attach,Bool.not_true]
    | inr j =>
      simp only [Equiv.swap_apply_def,Sum.inr.injEq,Sum.inr_ne_inl,
        ↓reduceIte,Tree.partition]
      change (associator (Γ:=Γ) x).val
        (((right x).comp ((right x).comp ((Tree.linear x n).brick j))).attach w)=_
      simp only [Tree.brick,Prefix.comp_attach]
      have h := associator_right (Γ:=Γ) x (((Tree.linear x n).brick j).attach w)
      rw [Prefix.comp_attach] at h
      rw [h,localizePerm_outside _ _ (oneBit_outside x (Ne.symm Bool.false_ne_true) _)]

omit [MulAction.IsPretransitive Γ X] in
lemma linear_front_mem (n : ℕ) :
    (Tree.linear x (n+2)).partition.permute (Γ:=Γ)
      (fixedSwap (Sum.inl PUnit.unit) (Sum.inr (Sum.inl PUnit.unit)))∈subgroup x := by
  rw [linear_front_swap]
  exact (subgroup x).mul_mem
    ((subgroup x).mul_mem ((subgroup x).inv_mem (associator_mem x)) (half_flip_mem x))
    (associator_mem x)

end Generators
end

section
universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Generators
variable (x : X) [MulAction.IsPretransitive Γ X]

lemma linear_permute_mem (n : ℕ) (e : Equiv.Perm (Tree.linear x n).Leaves) :
    (Tree.linear x n).partition.permute (Γ:=Γ) e∈subgroup x := by
  induction n with
  | zero =>
    have he : e=1 := Subsingleton.elim _ _
    rw [he,map_one]
    exact (subgroup x).one_mem
  | succ n ih =>
    have hcross (j : (Tree.linear x n).Leaves) :
        (Tree.linear x (n+1)).partition.permute (Γ:=Γ)
          (fixedSwap (Sum.inl PUnit.unit) (Sum.inr j))∈subgroup x := by
      cases n with
      | zero =>
        cases j
        have hh := flip_mem (Γ:=Γ) x
        rw [← linear_two_swap] at hh
        exact hh
      | succ k =>
        let E : Equiv.Perm (Tree.linear x (k+2)).Leaves :=
          Equiv.sumCongr (Equiv.refl PUnit.{1}) (fixedSwap (Sum.inl PUnit.unit) j)
        have hE : (Tree.linear x (k+2)).partition.permute (Γ:=Γ) E∈subgroup x :=
          join_permute_mem x (a:=Tree.leaf) (b:=Tree.linear x (k+1))
            (1 : Equiv.Perm PUnit.{1}) (fixedSwap (Sum.inl PUnit.unit) j)
            (by rw [map_one]; exact (subgroup x).one_mem) (ih _) x
        have heq : fixedSwap (Sum.inl PUnit.unit) (Sum.inr j)=
            E * fixedSwap (Sum.inl PUnit.unit) (Sum.inr (Sum.inl PUnit.unit)) * E⁻¹ := by
          have hleft : E (Sum.inl PUnit.unit) = Sum.inl PUnit.unit := rfl
          have hright : E (Sum.inr (Sum.inl PUnit.unit)) = Sum.inr j := by
            simp [E]
          have hh := Equiv.swap_apply_apply E (Sum.inl PUnit.unit) (Sum.inr (Sum.inl PUnit.unit))
          rw [hleft, hright] at hh
          simpa only [swap_eq_fixedSwap] using hh
        rw [heq,map_mul,map_mul,map_inv]
        exact (subgroup x).mul_mem ((subgroup x).mul_mem hE (linear_front_mem x k))
          ((subgroup x).inv_mem hE)
    have hswap (i j : (Tree.linear x (n+1)).Leaves) :
        (Tree.linear x (n+1)).partition.permute (Γ:=Γ) (fixedSwap i j)∈subgroup x := by
      cases i with
      | inl i =>
        cases i
        cases j with
        | inl j =>
          cases j
          rw [fixedSwap_self,map_one]; exact (subgroup x).one_mem
        | inr j => exact hcross j
      | inr i =>
        cases j with
        | inl j =>
          cases j
          rw [fixedSwap_comm]; exact hcross i
        | inr j =>
          rw [← sum_swap_right]
          exact join_permute_mem x (a:=Tree.leaf) (b:=Tree.linear x n)
            (1 : Equiv.Perm PUnit.{1}) (fixedSwap i j)
            (by rw [map_one]; exact (subgroup x).one_mem) (ih _) x
    induction e using Equiv.Perm.swap_induction_on with
    | one => rw [map_one]; exact (subgroup x).one_mem
    | swap_mul e i j _ he =>
      rw [map_mul]
      exact (subgroup x).mul_mem (by simpa only [swap_eq_fixedSwap] using hswap i j) he

end Generators
end

universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Generators
variable (x : X) [MulAction.IsPretransitive Γ X]

lemma tree_chart_mem (s t : Tree X) (e : s.Leaves ≃ t.Leaves) :
    s.partition.changeChart (Γ:=Γ) t.partition e∈subgroup x := by
  obtain ⟨m,⟨h⟩⟩ := exists_linear (Γ:=Γ) x s
  obtain ⟨n,⟨k⟩⟩ := exists_linear (Γ:=Γ) x t
  have hmn : m=n := by
    have hc := Fintype.card_congr (h.leaves.symm.trans (e.trans k.leaves))
    rw [Tree.linear_card,Tree.linear_card] at hc
    omega
  subst n
  let E : Equiv.Perm (Tree.linear x m).Leaves := h.leaves.symm.trans (e.trans k.leaves)
  let g := (Tree.linear x m).partition.permute (Γ:=Γ) E
  have heq : s.partition.changeChart (Γ:=Γ) t.partition e=k.element⁻¹*g*h.element := by
    apply Subtype.ext
    apply Equiv.ext
    intro z
    obtain ⟨i,⟨w,rfl⟩,_⟩ := s.cover z
    rw [Partition.changeChart_apply]
    change (t.brick (e i)).attach w=k.element.val.symm (g.val (h.element.val ((s.brick i).attach w)))
    rw [h.chart]
    change (t.brick (e i)).attach w=k.element.val.symm
      (((Tree.linear x m).partition.permute (Γ:=Γ) E).val (((Tree.linear x m).brick (h.leaves i)).attach w))
    rw [Partition.permute_attach]
    apply k.element.val.injective
    rw [Equiv.apply_symm_apply,k.chart]
    simp [E]
  rw [heq]
  exact (subgroup x).mul_mem ((subgroup x).mul_mem ((subgroup x).inv_mem k.mem_subgroup)
    (linear_permute_mem x m E)) h.mem_subgroup

lemma tree_decorate_mem (s : Tree X) (a : s.Leaves → Γ) :
    decorate s.partition a∈subgroup x := by
  induction s with
  | leaf =>
    have heq : decorate (Tree.leaf (X:=X)).partition a=embedding (a PUnit.unit) := by
      apply Subtype.ext
      apply Equiv.ext
      intro z
      change decoratePerm (Tree.leaf (X:=X)).partition a z=twist (a PUnit.unit) z
      have h := decoratePerm_attach (Γ:=Γ) (Tree.leaf (X:=X)).partition a PUnit.unit z
      simpa only [Tree.partition,Tree.brick,Prefix.empty_attach] using h
    rw [heq]
    exact root_mem x _
  | split y s t hs ht =>
    have heq : decorate (Tree.split y s t).partition a=
        sumElement y (decorate s.partition (fun i => a (Sum.inl i)))
          (decorate t.partition (fun i => a (Sum.inr i))) := by
      apply Subtype.ext
      apply Equiv.ext
      intro z
      obtain ⟨i,⟨w,rfl⟩,_⟩ := (Tree.split y s t).cover z
      change (decoratePerm (Tree.split y s t).partition a) (((Tree.split y s t).brick i).attach w)=_
      rw [decoratePerm_attach]
      cases i with
      | inl i =>
        change (((Prefix.oneBit y false).comp (s.brick i)).attach (twist (a (Sum.inl i)) w))=
          (sumElement y (decorate s.partition (fun i => a (Sum.inl i)))
            (decorate t.partition (fun i => a (Sum.inr i)))).val
              (((Prefix.oneBit y false).comp (s.brick i)).attach w)
        rw [Prefix.comp_attach,Prefix.comp_attach,sumElement_left,decorate_val,decoratePerm_attach]
      | inr i =>
        change (((Prefix.oneBit y true).comp (t.brick i)).attach (twist (a (Sum.inr i)) w))=
          (sumElement y (decorate s.partition (fun i => a (Sum.inl i)))
            (decorate t.partition (fun i => a (Sum.inr i)))).val
              (((Prefix.oneBit y true).comp (t.brick i)).attach w)
        rw [Prefix.comp_attach,Prefix.comp_attach,sumElement_right,decorate_val,decoratePerm_attach]
    rw [heq]
    exact (subgroup x).mul_mem (bit_local_mem x y false (hs _))
      (bit_local_mem x y true (ht _))

lemma all_mem (f : group (Γ:=Γ) (X:=X)) : f∈subgroup x := by
  obtain ⟨A⟩ := (mem_group_iff_table f.val).mp f.property
  obtain ⟨s,t,B,es,et,hs,ht⟩ := A.exists_tree_pair
  let e := es.symm.trans et
  let a : s.Leaves → Γ := fun i => B.label (es.symm i)
  have heq : f=s.partition.changeChart t.partition e * decorate s.partition a := by
    apply Subtype.ext
    apply Equiv.ext
    intro z
    obtain ⟨i,⟨w,rfl⟩,_⟩ := B.source_cover z
    change f.val ((B.source i).attach w)=
      (s.partition.changeChart (Γ:=Γ) t.partition e).val
        (decoratePerm s.partition a ((B.source i).attach w))
    rw [B.chart,hs i,decoratePerm_attach,Partition.changeChart_apply,ht i]
    simp [e,a]
  rw [heq]
  exact (subgroup x).mul_mem (tree_chart_mem x s t e) (tree_decorate_mem x s a)

lemma subgroup_eq_top : subgroup (Γ:=Γ) x=⊤ := by
  apply top_unique
  intro f _
  exact all_mem x f

end Generators
end FiniteAlgebraicEnvelopes.TwistedBrinThompson

end

end OAI
end

section
-- module Solutions.OAIFAE.FinitePresentation
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Finite presentation seeds, localization, and structural relations.
-/

namespace FiniteAlgebraicEnvelopes.TwistedBrinThompson

section
universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Generators
variable (x : X)

instance seed_finitelyPresented [Group.IsFinitelyPresented Γ] :
    Group.IsFinitelyPresented (Seed (Γ:=Γ) x) :=
  inferInstanceAs (Group.IsFinitelyPresented (Monoid.Coprod (Monoid.Coprod Γ Γ)
    (FreeGroup (finiteSet (Γ:=Γ) x))))

lemma evaluation_range : (evaluation (Γ:=Γ) x).range=subgroup x := by
  change (Monoid.Coprod.lift
    (Monoid.Coprod.lift embedding ((localize (left x)).comp embedding))
    (FreeGroup.lift (fun a : finiteSet (Γ:=Γ) x => a.val))).range=_
  rw [Monoid.Coprod.range_lift,Monoid.Coprod.range_lift]
  change _ ⊔ _ ⊔ (FreeGroup.lift (fun a : finiteSet (Γ:=Γ) x => a.val)).range =
    _ ⊔ _ ⊔ Subgroup.closure (finiteSet (Γ:=Γ) x : Set (group (Γ:=Γ) (X:=X)))
  congr 1
  exact (FreeGroup.closure_eq_range (finiteSet (Γ:=Γ) x : Set (group (Γ:=Γ) (X:=X)))).symm

lemma evaluation_surjective [MulAction.IsPretransitive Γ X] :
    Function.Surjective (evaluation (Γ:=Γ) x) := by
  rw [← MonoidHom.range_eq_top,evaluation_range,subgroup_eq_top]

end Generators
end

section
universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]

lemma half_copies_commute (x : X) (f h : group (Γ:=Γ) (X:=X)) :
    Commute (localize (Prefix.oneBit x false) f) (localize (Prefix.oneBit x true) h) := by
  apply Subtype.ext
  apply Equiv.ext
  intro z
  obtain ⟨b,⟨w,rfl⟩,_⟩ := (Partition.bit x).cover z
  change localizePerm (Prefix.oneBit x false) f.val
      (localizePerm (Prefix.oneBit x true) h.val ((Prefix.oneBit x b).attach w))=
    localizePerm (Prefix.oneBit x true) h.val
      (localizePerm (Prefix.oneBit x false) f.val ((Prefix.oneBit x b).attach w))
  cases b
  · rw [localizePerm_outside _ _ (oneBit_outside x Bool.false_ne_true w),
      localizePerm_attach,
      localizePerm_outside _ _ (oneBit_outside x Bool.false_ne_true (f.val w))]
  · rw [localizePerm_attach,
      localizePerm_outside _ _ (oneBit_outside x (Ne.symm Bool.false_ne_true) (h.val w)),
      localizePerm_outside _ _ (oneBit_outside x (Ne.symm Bool.false_ne_true) w),
      localizePerm_attach]

lemma embedding_eq_diagonal_of_fixed (x : X) (g : Γ) (hg : g • x=x) :
    embedding (X:=X) g=diagonal x (embedding g) := by
  apply Subtype.ext
  apply Equiv.ext
  intro z
  obtain ⟨b,⟨w,rfl⟩,_⟩ := (Partition.bit x).cover z
  change twist g ((Prefix.oneBit x b).attach w)=_
  rw [twist_attach,twistPrefix_oneBit,hg,diagonal_attach]
  rfl

namespace Generators
variable (x : X)

/-- A point-stabilizer relation: its root copy equals its two half-copies. -/
def fixedWord (g : MulAction.stabilizer Γ x) : Seed (Γ:=Γ) x :=
  rootWord x g.val * (halfWord x g.val * rightWord x g.val)⁻¹

lemma evaluation_fixedWord (g : MulAction.stabilizer Γ x) : evaluation (Γ:=Γ) x (fixedWord x g)=1 := by
  simp only [fixedWord,map_mul,map_inv,evaluation_rootWord,evaluation_halfWord,evaluation_rightWord]
  conv_lhs => arg 1; rw [embedding_eq_diagonal_of_fixed x g.val g.property]
  change diagonal x (embedding g.val) * (diagonal x (embedding g.val))⁻¹=1
  exact mul_inv_cancel _

end Generators
end

universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Generators
variable (x : X)

lemma flip_mul_self : flip (Γ:=Γ) x * flip x=1 := by
  change (Partition.bit x).permute (Γ:=Γ) Equiv.boolNot *
    (Partition.bit x).permute Equiv.boolNot=1
  rw [← map_mul]
  have h : (Equiv.boolNot : Equiv.Perm Bool) * Equiv.boolNot=1 := by
    ext b
    cases b <;> rfl
  rw [h,map_one]

end Generators
end FiniteAlgebraicEnvelopes.TwistedBrinThompson

namespace FiniteAlgebraicEnvelopes.TwistedBrinThompson
universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Generators
variable (x : X)

lemma localize_twice (g : group (Γ:=Γ) (X:=X)) :
    localize (left x) (localize (left x) g)=
      associator x * localize (left x) g * (associator x)⁻¹ := by
  rw [← localize_comp]
  exact (localize_conj (associator x) (associator_left x) g).symm

variable [MulAction.IsPretransitive Γ X]

/-- An actual lift of prefix localization to the presentation seed. It respects
both Γ factors as homomorphisms; only the free factor uses chosen preimages. -/
def localizationSeed : Seed (Γ:=Γ) x →* Seed (Γ:=Γ) x :=
  Monoid.Coprod.lift
    (Monoid.Coprod.lift (halfWord x)
      ((MulAut.conj (associatorWord x)).toMonoidHom.comp (halfWord x)))
    (FreeGroup.lift (fun g : finiteSet (Γ:=Γ) x =>
      (evaluation_surjective (Γ:=Γ) x (localize (left x) g.val)).choose))

lemma localizationSeed_correct :
    (evaluation (Γ:=Γ) x).comp (localizationSeed x)=
      (localize (left x)).comp (evaluation (Γ:=Γ) x) := by
  apply Monoid.Coprod.hom_ext
  · apply Monoid.Coprod.hom_ext
    · apply MonoidHom.ext
      intro g
      rfl
    · apply MonoidHom.ext
      intro g
      change evaluation (Γ:=Γ) x (associatorWord x * halfWord x g * (associatorWord x)⁻¹)=
        localize (left x) (localize (left x) (embedding g))
      rw [map_mul,map_mul,map_inv,evaluation_associatorWord,evaluation_halfWord]
      exact (localize_twice x (embedding g)).symm
  · apply FreeGroup.ext_hom
    intro g
    change evaluation (Γ:=Γ) x
      (FreeGroup.lift (fun k : finiteSet (Γ:=Γ) x =>
        (evaluation_surjective (Γ:=Γ) x (localize (left x) k.val)).choose) (FreeGroup.of g)) =
      localize (left x) (FreeGroup.lift (fun k : finiteSet (Γ:=Γ) x => k.val) (FreeGroup.of g))
    simpa only [FreeGroup.lift_apply_of] using
      (evaluation_surjective (Γ:=Γ) x (localize (left x) g.val)).choose_spec

lemma evaluation_localizationSeed (g : Seed (Γ:=Γ) x) :
    evaluation (Γ:=Γ) x (localizationSeed x g)=localize (left x) (evaluation (Γ:=Γ) x g) :=
  DFunLike.congr_fun (localizationSeed_correct x) g

/-- The finite self-similar closure of any given finite family of actual table
relations. Completeness of a particular family still has to be proved. -/
abbrev LocalQuotient (s r : Finset (Seed (Γ:=Γ) x)) :=
  FiniteLocalizationClosure.Quotient (localizationSeed x) (associatorWord x) s r

def localEvaluation (s r : Finset (Seed (Γ:=Γ) x))
    (hr : ∀ g∈r,evaluation (Γ:=Γ) x g=1) :
    LocalQuotient x s r →* group (Γ:=Γ) (X:=X) :=
  FiniteLocalizationClosure.evaluate _ _ s r (evaluation (Γ:=Γ) x) (localize (left x))
    (evaluation_localizationSeed x)
    (by intro g; rw [evaluation_associatorWord]; exact localize_twice x g) hr

lemma localEvaluation_surjective (s r : Finset (Seed (Γ:=Γ) x))
    (hr : ∀ g∈r,evaluation (Γ:=Γ) x g=1) :
    Function.Surjective (localEvaluation x s r hr) :=
  FiniteLocalizationClosure.evaluate_surjective _ _ s r _ _ _ _ hr (evaluation_surjective x)

end Generators
end FiniteAlgebraicEnvelopes.TwistedBrinThompson

end

end OAI
end

section
-- module Solutions.OAIFAE.TreeRefinement
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Tree prefixes, common refinements, and quotient refinement relations.
-/

namespace FiniteAlgebraicEnvelopes.TwistedBrinThompson

section
universe v
attribute [local instance] Classical.propDecidable
namespace Prefix
variable {X : Type v}

lemma comp_left_injective (p : Prefix X) : Function.Injective p.comp := by
  intro q r h
  apply Prefix.ext
  intro x
  exact List.append_cancel_left (congrArg (fun t : Prefix X => t.word x) h)

lemma oneBit_comp_comm {x y : X} (hxy : x≠y) (a b : Bool) :
    (oneBit x a).comp (oneBit y b)=(oneBit y b).comp (oneBit x a) := by
  ext z
  by_cases hzx : z=x
  · subst z; simp [hxy]
  · by_cases hzy : z=y
    · subst z; simp [Ne.symm hxy]
    · simp [hzx,hzy]

lemma oneBit_comp_disjoint (x : X) {a b : Bool} (hab : a≠b) (p q : Prefix X) :
    (oneBit x a).comp p≠(oneBit x b).comp q := by
  intro he
  have hh := congrArg (fun t : Prefix X => t.word x) he
  simp only [comp_word,oneBit_word] at hh
  exact hab (List.cons.inj hh).1
end Prefix
namespace Tree
variable {X : Type v}

instance leaves_nonempty (t : Tree X) : Nonempty t.Leaves := by
  induction t with
  | leaf => exact inferInstanceAs (Nonempty PUnit)
  | split x a b ha hb =>
    obtain ⟨i⟩ := ha
    exact ⟨Sum.inl i⟩

lemma image_comp_comp (p q : Prefix X) (A : Set (Prefix X)) :
    p.comp '' (q.comp '' A)=(p.comp q).comp '' A := by
  rw [Set.image_image]
  congr 1
  funext r
  exact (Prefix.comp_assoc p q r).symm

lemma Coherent.brickSet_eq {s t : Tree X} (h : Coherent s t) : brickSet s=brickSet t := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | split x _ _ ih₁ ih₂ => simp only [brickSet_split,ih₁,ih₂]
  | @interchange x y hxy a b c d =>
    simp only [brickSet_split,Set.image_union,image_comp_comp]
    rw [Prefix.oneBit_comp_comm hxy false false,
      Prefix.oneBit_comp_comm hxy false true,
      Prefix.oneBit_comp_comm hxy true false,
      Prefix.oneBit_comp_comm hxy true true]
    ac_rfl

/-- If every leaf has already read a bit on x, the x split can be commuted
all the way to the root. This is the nontrivial coordinate-coherence step. -/
lemma extract_root (x : X) (t : Tree X)
    (h : ∀ i,(t.brick i).word x≠[]) :
    ∃ a b,Coherent t (.split x a b) := by
  induction t with
  | leaf => exact False.elim (h PUnit.unit rfl)
  | split y a b ha hb =>
    by_cases hyx : y=x
    · subst y; exact ⟨a,b,.refl _⟩
    · have hxa : ∀ i,(a.brick i).word x≠[] := by
        intro i hi
        apply h (Sum.inl i)
        change (Prefix.oneBit y false).word x ++ (a.brick i).word x=[]
        simp [Prefix.oneBit_word,Ne.symm hyx,hi]
      have hxb : ∀ i,(b.brick i).word x≠[] := by
        intro i hi
        apply h (Sum.inr i)
        change (Prefix.oneBit y true).word x ++ (b.brick i).word x=[]
        simp [Prefix.oneBit_word,Ne.symm hyx,hi]
      obtain ⟨a₀,a₁,ha'⟩ := ha hxa
      obtain ⟨b₀,b₁,hb'⟩ := hb hxb
      exact ⟨.split y a₀ b₀,.split y a₁ b₁,
        (Coherent.split y ha' hb').trans (.interchange hyx a₀ a₁ b₀ b₁)⟩

lemma brickSet_split_injective (x : X) {a b c d : Tree X}
    (h : brickSet (.split x a b)=brickSet (.split x c d)) :
    brickSet a=brickSet c ∧ brickSet b=brickSet d := by
  simp only [brickSet_split] at h
  have halves (β : Bool) (A B C D : Set (Prefix X))
      (he : (Prefix.oneBit x β).comp '' A ∪ (Prefix.oneBit x (!β)).comp '' B=
        (Prefix.oneBit x β).comp '' C ∪ (Prefix.oneBit x (!β)).comp '' D) : A=C := by
    apply Set.Subset.antisymm
    · intro p hp
      have hm : (Prefix.oneBit x β).comp p∈
          (Prefix.oneBit x β).comp '' C ∪ (Prefix.oneBit x (!β)).comp '' D := by
        rw [← he]; exact Or.inl ⟨p,hp,rfl⟩
      rcases hm with ⟨q,hq,hqp⟩|⟨q,hq,hqp⟩
      · exact (Prefix.comp_left_injective _ hqp) ▸ hq
      · exact False.elim (Prefix.oneBit_comp_disjoint x (by cases β <;> decide) _ _ hqp.symm)
    · intro p hp
      have hm : (Prefix.oneBit x β).comp p∈
          (Prefix.oneBit x β).comp '' A ∪ (Prefix.oneBit x (!β)).comp '' B := by
        rw [he]; exact Or.inl ⟨p,hp,rfl⟩
      rcases hm with ⟨q,hq,hqp⟩|⟨q,hq,hqp⟩
      · exact (Prefix.comp_left_injective _ hqp) ▸ hq
      · exact False.elim (Prefix.oneBit_comp_disjoint x (by cases β <;> decide) _ _ hqp.symm)
  refine ⟨halves false _ _ _ _ h,halves true (brickSet b) (brickSet a) (brickSet d) (brickSet c) ?_⟩
  simpa only [Bool.not_true,Set.union_comm] using h

lemma brickSet_eq_leaf {t : Tree X} (h : brickSet t=brickSet (.leaf : Tree X)) : t=.leaf := by
  cases t with
  | leaf => rfl
  | split x a b =>
    let i : a.Leaves := Classical.arbitrary a.Leaves
    have hm : (Tree.split x a b).brick (Sum.inl i)∈brickSet (.leaf : Tree X) :=
      h ▸ ⟨Sum.inl i,rfl⟩
    rw [brickSet_leaf,Set.mem_singleton_iff] at hm
    have he := congrArg (fun p : Prefix X => p.word x) hm
    simp [brick,Prefix.empty] at he

/-- Completeness of local interchange for finite coloured trees. The proof
uses tree induction and root extraction, not an equality-as-relation shortcut. -/
lemma coherent_of_brickSet_eq (s t : Tree X) (h : brickSet s=brickSet t) : Coherent s t := by
  induction s generalizing t with
  | leaf =>
    have ht := brickSet_eq_leaf h.symm
    subst t
    exact .refl _
  | split x a b ha hb =>
    have ht : ∀ i,(t.brick i).word x≠[] := by
      intro i hi
      have hm : t.brick i∈brickSet (.split x a b) := h.symm ▸ ⟨i,rfl⟩
      rcases hm with ⟨j,hj⟩
      have hje := congrArg (fun p : Prefix X => p.word x) hj
      cases j <;> simp [brick,hi] at hje
    obtain ⟨c,d,hcd⟩ := extract_root x t ht
    have he := h.trans hcd.brickSet_eq
    obtain ⟨hac,hbd⟩ := brickSet_split_injective x he
    exact (Coherent.split x (ha c hac) (hb d hbd)).trans hcd.symm

end Tree
end

section
universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Generators
namespace Move
variable {x : X} {s t : Tree X}

lemma element_eq_of_leaves (h k : Move (Γ:=Γ) x s t) (he : h.leaves=k.leaves) :
    h.element=k.element := by
  rw [h.element_eq_chart,k.element_eq_chart,he]

/-- Symmetry of the two subtrees, with its literal untwisted cube chart. -/
def exchange [MulAction.IsPretransitive Γ X] (x : X) (a b : Tree X) :
    Move (Γ:=Γ) x (.split x a b) (.split x b a) where
  leaves := Equiv.sumComm _ _
  element := flip x
  mem_subgroup := flip_mem x
  chart i z := by
    cases i with
    | inl i =>
      change (flip (Γ:=Γ) x).val (((left x).comp (a.brick i)).attach z)=
        ((right x).comp (a.brick i)).attach z
      simpa only [left,right,Prefix.comp_attach,Bool.not_false] using
        flip_attach (Γ:=Γ) x false ((a.brick i).attach z)
    | inr i =>
      change (flip (Γ:=Γ) x).val (((right x).comp (b.brick i)).attach z)=
        ((left x).comp (b.brick i)).attach z
      simpa only [left,right,Prefix.comp_attach,Bool.not_true] using
        flip_attach (Γ:=Γ) x true ((b.brick i).attach z)
end Move
variable (x : X) [MulAction.IsPretransitive Γ X]

/-- The actual associator satisfies the pentagon, proved by its four leaf
charts, not imposed on the constructed group as an extra hypothesis. -/
lemma associator_pentagon :
    associator (Γ:=Γ) x * associator x =
      localize (left x) (associator x) * associator x * localize (right x) (associator x) := by
  let l : Tree X := .leaf
  let r := Move.rotate (Γ:=Γ) x l l l
  let h₁ := (Move.refl (Γ:=Γ) (x:=x) l).join r x
  let h₂ := Move.rotate (Γ:=Γ) x l (.split x l l) l
  let h₃ := r.join (Move.refl l) x
  let k₁ := Move.rotate (Γ:=Γ) x l l (.split x l l)
  let k₂ := Move.rotate (Γ:=Γ) x (.split x l l) l l
  have he : ((h₁.trans h₂).trans h₃).leaves=(k₁.trans k₂).leaves := by
    apply Equiv.ext
    intro i
    rcases i with i | i | i | i <;> rfl
  have hh := Move.element_eq_of_leaves ((h₁.trans h₂).trans h₃) (k₁.trans k₂) he
  simpa only [h₁,h₂,h₃,k₁,k₂,r,Move.trans,Move.join,Move.refl,Move.rotate,
    sumElement,map_one,one_mul,mul_one,mul_assoc] using hh.symm

/-- The actual associator and half swaps satisfy the symmetry hexagon. -/
lemma flip_hexagon :
    flip (Γ:=Γ) x = associator x * localize (right x) (flip x) * (associator x)⁻¹ *
      localize (left x) (flip x) * associator x := by
  let l : Tree X := .leaf
  let a := Move.rotate (Γ:=Γ) x l l l
  let c := Move.exchange (Γ:=Γ) x l l
  let h₁ := a
  let h₂ := c.join (Move.refl l) x
  let h₃ := a.symm
  let h₄ := (Move.refl l).join c x
  let h₅ := a
  let k := Move.exchange (Γ:=Γ) x l (.split x l l)
  have he : ((((h₁.trans h₂).trans h₃).trans h₄).trans h₅).leaves=k.leaves := by
    apply Equiv.ext
    intro i
    rcases i with i | i | i <;> rfl
  have hh := Move.element_eq_of_leaves ((((h₁.trans h₂).trans h₃).trans h₄).trans h₅) k he
  simpa only [h₁,h₂,h₃,h₄,h₅,k,a,c,Move.trans,Move.join,Move.refl,Move.rotate,
    Move.exchange,Move.symm,sumElement,map_one,one_mul,mul_one,mul_assoc] using hh.symm

omit [MulAction.IsPretransitive Γ X] in
lemma associator_middle_naturality (g : group (Γ:=Γ) (X:=X)) :
    associator x * localize (right x) (localize (left x) g) * (associator x)⁻¹=
      localize (left x) (localize (right x) g) := by
  rw [← localize_comp,← localize_comp]
  exact localize_conj _ (associator_middle x) g

omit [MulAction.IsPretransitive Γ X] in
lemma associator_right_naturality (g : group (Γ:=Γ) (X:=X)) :
    associator x * localize (right x) (localize (right x) g) * (associator x)⁻¹=
      localize (right x) g := by
  rw [← localize_comp]
  exact localize_conj _ (associator_right x) g

end Generators
end

section
universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Generators
variable (x : X) [MulAction.IsPretransitive Γ X]

/-- The lifted right localization is obtained by the actual half swap. -/
def rightLocalizationSeed : Seed (Γ:=Γ) x →* Seed (Γ:=Γ) x :=
  (MulAut.conj (flipWord x)).toMonoidHom.comp (localizationSeed x)

lemma evaluation_rightLocalizationSeed (w : Seed (Γ:=Γ) x) :
    evaluation (Γ:=Γ) x (rightLocalizationSeed x w)=
      localize (right x) (evaluation (Γ:=Γ) x w) := by
  change evaluation (Γ:=Γ) x (flipWord x * localizationSeed x w * (flipWord x)⁻¹)=_
  rw [map_mul,map_mul,map_inv,evaluation_flipWord,evaluation_localizationSeed]
  exact localize_conj _ (flip_left x) _

def structuralComm (g h : Seed (Γ:=Γ) x) : Seed (Γ:=Γ) x :=
  localizationSeed x g * rightLocalizationSeed x h *
    (localizationSeed x g)⁻¹ * (rightLocalizationSeed x h)⁻¹

def structuralMiddle (g : Seed (Γ:=Γ) x) : Seed (Γ:=Γ) x :=
  (associatorWord x * rightLocalizationSeed x (localizationSeed x g) * (associatorWord x)⁻¹) *
    (localizationSeed x (rightLocalizationSeed x g))⁻¹

def structuralRight (g : Seed (Γ:=Γ) x) : Seed (Γ:=Γ) x :=
  (associatorWord x * rightLocalizationSeed x (rightLocalizationSeed x g) * (associatorWord x)⁻¹) *
    (rightLocalizationSeed x g)⁻¹

def pentagonWord : Seed (Γ:=Γ) x :=
  (associatorWord x * associatorWord x) *
    (localizationSeed x (associatorWord x) * associatorWord x *
      rightLocalizationSeed x (associatorWord x))⁻¹

def hexagonWord : Seed (Γ:=Γ) x :=
  flipWord x * (associatorWord x * rightLocalizationSeed x (flipWord x) * (associatorWord x)⁻¹ *
    localizationSeed x (flipWord x) * associatorWord x)⁻¹

/-- All root-level structural laws are finite after checking naturality and
commutation only on a finite generating family of Seed. -/
def structuralRelations (s : Finset (Seed (Γ:=Γ) x)) : Finset (Seed (Γ:=Γ) x) :=
  (s ×ˢ s).image (fun gh => structuralComm x gh.1 gh.2) ∪
    s.image (structuralMiddle x) ∪ s.image (structuralRight x) ∪
      {flipWord x * flipWord x,pentagonWord x,hexagonWord x}

lemma evaluation_structuralComm (g h : Seed (Γ:=Γ) x) :
    evaluation x (structuralComm x g h)=1 := by
  simp only [structuralComm,map_mul,map_inv,evaluation_localizationSeed,evaluation_rightLocalizationSeed]
  rw [(half_copies_commute x (evaluation x g) (evaluation x h)).eq]
  group
lemma evaluation_structuralMiddle (g : Seed (Γ:=Γ) x) :
    evaluation x (structuralMiddle x g)=1 := by
  simp only [structuralMiddle,map_mul,map_inv,evaluation_associatorWord,
    evaluation_localizationSeed,evaluation_rightLocalizationSeed,associator_middle_naturality,mul_inv_cancel]
lemma evaluation_structuralRight (g : Seed (Γ:=Γ) x) :
    evaluation x (structuralRight x g)=1 := by
  simp only [structuralRight,map_mul,map_inv,evaluation_associatorWord,
    evaluation_rightLocalizationSeed,associator_right_naturality,mul_inv_cancel]
lemma evaluation_pentagonWord : evaluation (Γ:=Γ) x (pentagonWord (Γ:=Γ) x)=1 := by
  simp only [pentagonWord,map_mul,map_inv,evaluation_associatorWord,
    evaluation_localizationSeed,evaluation_rightLocalizationSeed]
  rw [← associator_pentagon,mul_inv_cancel]
lemma evaluation_hexagonWord : evaluation (Γ:=Γ) x (hexagonWord (Γ:=Γ) x)=1 := by
  simp only [hexagonWord,map_mul,map_inv,evaluation_associatorWord,evaluation_flipWord,
    evaluation_localizationSeed,evaluation_rightLocalizationSeed]
  rw [← flip_hexagon,mul_inv_cancel]

lemma structuralRelations_valid (s : Finset (Seed (Γ:=Γ) x)) :
    ∀ g∈structuralRelations x s,evaluation x g=1 := by
  intro g hg
  simp only [structuralRelations,Finset.mem_union,Finset.mem_image,Finset.mem_insert,
    Finset.mem_singleton] at hg
  rcases hg with ((⟨⟨g,h⟩,_,rfl⟩|⟨g,_,rfl⟩)|⟨g,_,rfl⟩)|(rfl|rfl|rfl)
  · exact evaluation_structuralComm x g h
  · exact evaluation_structuralMiddle x g
  · exact evaluation_structuralRight x g
  · rw [map_mul,evaluation_flipWord,flip_mul_self]
  · exact evaluation_pentagonWord x
  · exact evaluation_hexagonWord x

/-- Finitely presented structural quotient with genuine evaluation map.
The absence of an injectivity assertion is substantive: coloured coherence
and label covariance/completeness are still required for the main theorem. -/
abbrev StructuralQuotient (s : Finset (Seed (Γ:=Γ) x)) := LocalQuotient x s (structuralRelations x s)

end Generators
end

section
universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Generators
variable (x : X) [MulAction.IsPretransitive Γ X] (s : Finset (Seed (Γ:=Γ) x))

def structuralProject : Seed (Γ:=Γ) x →* StructuralQuotient x s :=
  FiniteLocalizationClosure.project _ _ _ _

lemma structuralProject_rel {g : Seed (Γ:=Γ) x} (hg : g∈structuralRelations x s) :
    structuralProject x s g=1 :=
  FiniteLocalizationClosure.project_base _ _ _ _ (Finset.mem_union_left _ hg)

lemma structuralProject_comm {g h : Seed (Γ:=Γ) x} (hg : g∈s) (hh : h∈s) :
    Commute (structuralProject x s (localizationSeed x g))
      (structuralProject x s (rightLocalizationSeed x h)) := by
  have hm : structuralComm x g h∈structuralRelations x s := by
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨(g,h),Finset.mem_product.mpr ⟨hg,hh⟩,rfl⟩
  have he := structuralProject_rel x s hm
  simp only [structuralComm,map_mul,map_inv] at he
  apply mul_inv_eq_one.mp
  simpa only [mul_inv_rev,mul_assoc] using he

lemma structuralProject_middle {g : Seed (Γ:=Γ) x} (hg : g∈s) :
    structuralProject x s (associatorWord x * rightLocalizationSeed x (localizationSeed x g) *
      (associatorWord x)⁻¹)=structuralProject x s (localizationSeed x (rightLocalizationSeed x g)) := by
  have hm : structuralMiddle x g∈structuralRelations x s := by
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨g,hg,rfl⟩
  have he := structuralProject_rel x s hm
  change structuralProject x s (_*_⁻¹)=1 at he
  rw [map_mul,map_inv] at he
  exact mul_inv_eq_one.mp he

lemma structuralProject_right {g : Seed (Γ:=Γ) x} (hg : g∈s) :
    structuralProject x s (associatorWord x * rightLocalizationSeed x (rightLocalizationSeed x g) *
      (associatorWord x)⁻¹)=structuralProject x s (rightLocalizationSeed x g) := by
  have hm : structuralRight x g∈structuralRelations x s := by
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨g,hg,rfl⟩
  have he := structuralProject_rel x s hm
  change structuralProject x s (_*_⁻¹)=1 at he
  rw [map_mul,map_inv] at he
  exact mul_inv_eq_one.mp he

variable (hs : Subgroup.closure (s : Set (Seed (Γ:=Γ) x))=⊤)
include hs

/-- Infinite naturality families are consequences of their finite generator
checks. This is an algebraic reduction, not an appeal to diagram coherence. -/
lemma structuralProject_comm_all (g h : Seed (Γ:=Γ) x) :
    Commute (structuralProject x s (localizationSeed x g))
      (structuralProject x s (rightLocalizationSeed x h)) :=
  commute_homs_of_generators (s : Set (Seed (Γ:=Γ) x)) hs
    ((structuralProject x s).comp (localizationSeed x))
    ((structuralProject x s).comp (rightLocalizationSeed x))
    (fun _ hg _ hh => structuralProject_comm x s hg hh) g h

lemma structuralProject_middle_all (g : Seed (Γ:=Γ) x) :
    structuralProject x s (associatorWord x * rightLocalizationSeed x (localizationSeed x g) *
      (associatorWord x)⁻¹)=structuralProject x s (localizationSeed x (rightLocalizationSeed x g)) := by
  have he : (structuralProject x s).comp
      ((MulAut.conj (associatorWord x)).toMonoidHom.comp
        ((rightLocalizationSeed x).comp (localizationSeed x)))=
      (structuralProject x s).comp ((localizationSeed x).comp (rightLocalizationSeed x)) := by
    apply MonoidHom.eq_of_eqOn_dense hs
    intro g hg
    exact structuralProject_middle x s hg
  exact DFunLike.congr_fun he g

lemma structuralProject_right_all (g : Seed (Γ:=Γ) x) :
    structuralProject x s (associatorWord x * rightLocalizationSeed x (rightLocalizationSeed x g) *
      (associatorWord x)⁻¹)=structuralProject x s (rightLocalizationSeed x g) := by
  have he : (structuralProject x s).comp
      ((MulAut.conj (associatorWord x)).toMonoidHom.comp
        ((rightLocalizationSeed x).comp (rightLocalizationSeed x)))=
      (structuralProject x s).comp (rightLocalizationSeed x) := by
    apply MonoidHom.eq_of_eqOn_dense hs
    intro g hg
    exact structuralProject_right x s hg
  exact DFunLike.congr_fun he g

lemma structuralProject_left_all (g : Seed (Γ:=Γ) x) :
    structuralProject x s (localizationSeed x (localizationSeed x g))=
      structuralProject x s (associatorWord x * localizationSeed x g * (associatorWord x)⁻¹) :=
  FiniteLocalizationClosure.twice_eq_conjugate _ _ _ _ hs g

/-- The endomorphism exists on the finitely presented structural quotient,
not just on its semantic image in the actual table group. -/
def structuralLocalization : StructuralQuotient x s →* StructuralQuotient x s :=
  FiniteLocalizationClosure.localization _ _ _ _ hs

lemma structuralLocalization_project (g : Seed (Γ:=Γ) x) :
    structuralLocalization x s hs (structuralProject x s g)=
      structuralProject x s (localizationSeed x g) := rfl

omit hs in
lemma structuralProject_flip_square :
    structuralProject x s (flipWord x) * structuralProject x s (flipWord x)=1 := by
  rw [← map_mul]
  exact structuralProject_rel x s (Finset.mem_union_right _ (by simp))

omit hs in
lemma structuralProject_pentagon : structuralProject x s (pentagonWord (Γ:=Γ) x)=1 :=
  structuralProject_rel x s (Finset.mem_union_right _ (by simp))

omit hs in
lemma structuralProject_hexagon : structuralProject x s (hexagonWord (Γ:=Γ) x)=1 :=
  structuralProject_rel x s (Finset.mem_union_right _ (by simp))

end Generators
end

universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Generators
variable (x : X) [MulAction.IsPretransitive Γ X] (s : Finset (Seed (Γ:=Γ) x))
variable (hs : Subgroup.closure (s : Set (Seed (Γ:=Γ) x))=⊤)

lemma structuralProject_surjective : Function.Surjective (structuralProject (Γ:=Γ) x s) :=
  QuotientGroup.mk'_surjective _

def structuralSymmetry : StructuralQuotient (Γ:=Γ) x s := structuralProject x s (flipWord x)
def structuralAssociator : StructuralQuotient (Γ:=Γ) x s := structuralProject x s (associatorWord x)

lemma structuralSymmetry_square : structuralSymmetry (Γ:=Γ) x s * structuralSymmetry x s=1 :=
  structuralProject_flip_square x s

lemma structuralSymmetry_inv : (structuralSymmetry (Γ:=Γ) x s)⁻¹=structuralSymmetry x s := by
  exact inv_eq_of_mul_eq_one_right (structuralSymmetry_square x s)

def structuralRightLocalization : StructuralQuotient (Γ:=Γ) x s →* StructuralQuotient x s :=
  (MulAut.conj (structuralSymmetry x s)).toMonoidHom.comp (structuralLocalization x s hs)

lemma structuralRightLocalization_project (g : Seed (Γ:=Γ) x) :
    structuralRightLocalization x s hs (structuralProject x s g)=
      structuralProject x s (rightLocalizationSeed x g) := by
  change structuralProject x s (flipWord x) * structuralProject x s (localizationSeed x g) *
    (structuralProject x s (flipWord x))⁻¹=structuralProject x s
      (flipWord x * localizationSeed x g * (flipWord x)⁻¹)
  simp only [map_mul,map_inv]

lemma structuralLocalizations_commute (g h : StructuralQuotient (Γ:=Γ) x s) :
    Commute (structuralLocalization x s hs g) (structuralRightLocalization x s hs h) := by
  obtain ⟨g,rfl⟩ := structuralProject_surjective x s g
  obtain ⟨h,rfl⟩ := structuralProject_surjective x s h
  rw [structuralLocalization_project,structuralRightLocalization_project]
  exact structuralProject_comm_all x s hs g h

/-- A genuine binary tensor homomorphism on the actual finite structural
quotient. Its functoriality follows from the finitely generated disjointness
relations, not from semantic equality after evaluation. -/
def structuralTensor : StructuralQuotient (Γ:=Γ) x s × StructuralQuotient x s →*
    StructuralQuotient x s :=
  (structuralLocalization x s hs).noncommCoprod (structuralRightLocalization x s hs)
    (structuralLocalizations_commute x s hs)

lemma structuralTensor_apply (g h : StructuralQuotient (Γ:=Γ) x s) :
    structuralTensor x s hs (g,h)=structuralLocalization x s hs g *
      structuralRightLocalization x s hs h := rfl

lemma structuralConjugate_left (g : StructuralQuotient (Γ:=Γ) x s) :
    structuralAssociator x s * structuralLocalization x s hs g * (structuralAssociator x s)⁻¹=
      structuralLocalization x s hs (structuralLocalization x s hs g) := by
  obtain ⟨g,rfl⟩ := structuralProject_surjective x s g
  symm
  simpa only [structuralAssociator,structuralLocalization_project,map_mul,map_inv] using
    structuralProject_left_all x s hs g

lemma structuralConjugate_middle (g : StructuralQuotient (Γ:=Γ) x s) :
    structuralAssociator x s * structuralRightLocalization x s hs (structuralLocalization x s hs g) *
      (structuralAssociator x s)⁻¹=
      structuralLocalization x s hs (structuralRightLocalization x s hs g) := by
  obtain ⟨g,rfl⟩ := structuralProject_surjective x s g
  simpa only [structuralAssociator,structuralLocalization_project,
    structuralRightLocalization_project,map_mul,map_inv] using structuralProject_middle_all x s hs g

lemma structuralConjugate_right (g : StructuralQuotient (Γ:=Γ) x s) :
    structuralAssociator x s * structuralRightLocalization x s hs (structuralRightLocalization x s hs g) *
      (structuralAssociator x s)⁻¹=structuralRightLocalization x s hs g := by
  obtain ⟨g,rfl⟩ := structuralProject_surjective x s g
  simpa only [structuralAssociator,structuralLocalization_project,
    structuralRightLocalization_project,map_mul,map_inv] using structuralProject_right_all x s hs g

/-- Associativity is natural for every morphism of the finite quotient. -/
lemma structuralTensor_associativity (g h k : StructuralQuotient (Γ:=Γ) x s) :
    structuralAssociator x s * structuralTensor x s hs (g,structuralTensor x s hs (h,k)) *
      (structuralAssociator x s)⁻¹=
      structuralTensor x s hs (structuralTensor x s hs (g,h),k) := by
  simp only [structuralTensor_apply,map_mul]
  calc
    _=(structuralAssociator x s * structuralLocalization x s hs g * (structuralAssociator x s)⁻¹) *
        (structuralAssociator x s * structuralRightLocalization x s hs (structuralLocalization x s hs h) *
          (structuralAssociator x s)⁻¹) *
        (structuralAssociator x s * structuralRightLocalization x s hs (structuralRightLocalization x s hs k) *
          (structuralAssociator x s)⁻¹) := by group
    _=_ := by rw [structuralConjugate_left,structuralConjugate_middle,structuralConjugate_right]

lemma structuralSymmetry_localization (g : StructuralQuotient (Γ:=Γ) x s) :
    structuralSymmetry x s * structuralRightLocalization x s hs g * (structuralSymmetry x s)⁻¹=
      structuralLocalization x s hs g := by
  change structuralSymmetry x s * (structuralSymmetry x s * structuralLocalization x s hs g *
    (structuralSymmetry x s)⁻¹) * (structuralSymmetry x s)⁻¹=_
  rw [structuralSymmetry_inv]
  have h := structuralSymmetry_square (Γ:=Γ) x s
  calc
    _=(structuralSymmetry x s * structuralSymmetry x s) * structuralLocalization x s hs g *
        (structuralSymmetry x s * structuralSymmetry x s) := by group
    _=_ := by rw [h,one_mul,mul_one]

/-- The symmetry is natural, using involutivity and disjointness inside the
finite quotient, not merely a relation holding in the semantic group. -/
lemma structuralTensor_symmetry (g h : StructuralQuotient (Γ:=Γ) x s) :
    structuralSymmetry x s * structuralTensor x s hs (g,h) * (structuralSymmetry x s)⁻¹=
      structuralTensor x s hs (h,g) := by
  rw [structuralTensor_apply,structuralTensor_apply]
  calc
    _=(structuralSymmetry x s * structuralLocalization x s hs g * (structuralSymmetry x s)⁻¹) *
      (structuralSymmetry x s * structuralRightLocalization x s hs h * (structuralSymmetry x s)⁻¹) := by group
    _=structuralRightLocalization x s hs g * structuralLocalization x s hs h := by
      rw [structuralSymmetry_localization]; rfl
    _=_ := (structuralLocalizations_commute x s hs h g).eq.symm

lemma structuralTensor_pentagon :
    structuralAssociator (Γ:=Γ) x s * structuralAssociator x s=
      structuralLocalization x s hs (structuralAssociator x s) * structuralAssociator x s *
        structuralRightLocalization x s hs (structuralAssociator x s) := by
  have h := structuralProject_pentagon (Γ:=Γ) x s
  simp only [pentagonWord,map_mul,map_inv] at h
  exact mul_inv_eq_one.mp h

lemma structuralTensor_hexagon :
    structuralSymmetry (Γ:=Γ) x s =
      structuralAssociator x s * structuralRightLocalization x s hs (structuralSymmetry x s) *
        (structuralAssociator x s)⁻¹ * structuralLocalization x s hs (structuralSymmetry x s) *
          structuralAssociator x s := by
  have h := structuralProject_hexagon (Γ:=Γ) x s
  simp only [hexagonWord,map_mul,map_inv] at h
  exact mul_inv_eq_one.mp h

end Generators
end FiniteAlgebraicEnvelopes.TwistedBrinThompson

end

end OAI
end

section
-- module Solutions.OAIFAE.DecoratedPresentation
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Stabilizer cocycles, decorations, and explicit finite endpoint relations.
-/

namespace FiniteAlgebraicEnvelopes.TwistedBrinThompson
universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Generators
variable (x : X) [MulAction.IsPretransitive Γ X]
variable (s : Finset (Seed (Γ:=Γ) x)) (t : Finset (MulAction.stabilizer Γ x))

/-- Finite structural laws together with the point stabilizer laws. -/
def decoratedRelations : Finset (Seed (Γ:=Γ) x) :=
  structuralRelations x s ∪ t.image (fixedWord x)

lemma decoratedRelations_valid : ∀ g∈decoratedRelations x s t,evaluation x g=1 := by
  intro g hg
  rcases Finset.mem_union.mp hg with hg|hg
  · exact structuralRelations_valid x s g hg
  · obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hg
    exact evaluation_fixedWord x k

abbrev DecoratedQuotient := LocalQuotient x s (decoratedRelations x s t)

def decoratedProject : Seed (Γ:=Γ) x →* DecoratedQuotient x s t :=
  FiniteLocalizationClosure.project _ _ _ _

def structuralToDecorated : StructuralQuotient x s →* DecoratedQuotient x s t :=
  FiniteLocalizationClosure.quotientMap _ _ _ (Finset.subset_union_left)

lemma structuralToDecorated_project (g : Seed (Γ:=Γ) x) :
    structuralToDecorated x s t (structuralProject x s g)=decoratedProject x s t g := rfl

def decoratedRoot : Γ →* DecoratedQuotient x s t := (decoratedProject x s t).comp (rootWord x)
def decoratedHalf : Γ →* DecoratedQuotient x s t := (decoratedProject x s t).comp (halfWord x)
def decoratedRight : Γ →* DecoratedQuotient x s t := (decoratedProject x s t).comp (rightWord x)

variable (hs : Subgroup.closure (s : Set (Seed (Γ:=Γ) x))=⊤)
include hs

lemma decorated_commute (g h : Γ) :
    Commute (decoratedHalf x s t g) (decoratedRight x s t h) := by
  have hc := (structuralProject_comm_all x s hs (rootWord x g) (rootWord x h)).map
    (structuralToDecorated x s t)
  exact hc

def decoratedDiagonal : Γ →* DecoratedQuotient x s t where
  toFun g := decoratedHalf x s t g * decoratedRight x s t g
  map_one' := by simp
  map_mul' g h := by
    simp only [map_mul]
    exact ((decorated_commute x s t hs h g).symm.mul_mul_mul_comm _ _).symm

lemma decorated_fixed {g : MulAction.stabilizer Γ x} (hg : g∈t) :
    decoratedRoot x s t g.val=decoratedDiagonal x s t hs g.val := by
  have hm : fixedWord x g∈decoratedRelations x s t :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨g,hg,rfl⟩)
  have hp := FiniteLocalizationClosure.project_base (localizationSeed x) (associatorWord x)
    s (decoratedRelations x s t) (Finset.mem_union_left _ hm)
  change decoratedProject x s t (rootWord x g.val * (halfWord x g.val * rightWord x g.val)⁻¹)=1 at hp
  simp only [map_mul,map_inv] at hp
  exact mul_inv_eq_one.mp hp

lemma decorated_fixed_all (ht : Subgroup.closure (t : Set (MulAction.stabilizer Γ x))=⊤)
    (g : MulAction.stabilizer Γ x) :
    decoratedRoot x s t g.val=decoratedDiagonal x s t hs g.val := by
  have he : (decoratedRoot x s t).comp (MulAction.stabilizer Γ x).subtype=
      (decoratedDiagonal x s t hs).comp (MulAction.stabilizer Γ x).subtype := by
    apply MonoidHom.eq_of_eqOn_dense ht
    intro k hk
    exact decorated_fixed x s t hs hk
  exact DFunLike.congr_fun he g

end Generators
end FiniteAlgebraicEnvelopes.TwistedBrinThompson

namespace FiniteAlgebraicEnvelopes.TwistedBrinThompson

section
universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Generators
variable (x : X) [MulAction.IsPretransitive Γ X]
variable (s : Finset (Seed (Γ:=Γ) x)) (t : Finset (MulAction.stabilizer Γ x))
variable (hs : Subgroup.closure (s : Set (Seed (Γ:=Γ) x))=⊤)
variable (ht : Subgroup.closure (t : Set (MulAction.stabilizer Γ x))=⊤)

/-- A baker element defined inside the finitely presented quotient, before
any injectivity or table-presentation completeness theorem. -/
def decoratedBaker (y : X) : DecoratedQuotient x s t :=
  StabilizerCocycle.value x (decoratedRoot x s t) (decoratedDiagonal x s t hs) y

include ht

lemma decoratedBaker_base : decoratedBaker x s t hs x=1 :=
  StabilizerCocycle.value_base x _ _ (decorated_fixed_all x s t hs ht)

/-- The complete colour covariance family follows from the finite stabilizer
relations. It is not imposed once for each point of the infinite set. -/
lemma decoratedBaker_covariance (g : Γ) (y : X) :
    decoratedRoot x s t g*decoratedBaker x s t hs y=
      decoratedBaker x s t hs (g • y)*decoratedDiagonal x s t hs g :=
  StabilizerCocycle.covariance x _ _ (decorated_fixed_all x s t hs ht) g y

end Generators
end

section
universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Generators
variable (x : X) [MulAction.IsPretransitive Γ X]
variable (s : Finset (Seed (Γ:=Γ) x)) (t : Finset (MulAction.stabilizer Γ x))
variable (hs : Subgroup.closure (s : Set (Seed (Γ:=Γ) x))=⊤)

lemma decoratedProject_surjective : Function.Surjective (decoratedProject (Γ:=Γ) x s t) :=
  QuotientGroup.mk_surjective

lemma structuralToDecorated_surjective : Function.Surjective (structuralToDecorated (Γ:=Γ) x s t) :=
  FiniteLocalizationClosure.quotientMap_surjective _ _ _ _

def decoratedLocalization : DecoratedQuotient x s t →* DecoratedQuotient x s t :=
  FiniteLocalizationClosure.localization _ _ _ _ hs

def decoratedRightLocalization : DecoratedQuotient x s t →* DecoratedQuotient x s t :=
  (MulAut.conj (decoratedProject x s t (flipWord x))).toMonoidHom.comp
    (decoratedLocalization x s t hs)

lemma decoratedLocalization_project (g : Seed (Γ:=Γ) x) :
    decoratedLocalization x s t hs (decoratedProject x s t g)=
      decoratedProject x s t (localizationSeed x g) := rfl

lemma decoratedRightLocalization_project (g : Seed (Γ:=Γ) x) :
    decoratedRightLocalization x s t hs (decoratedProject x s t g)=
      decoratedProject x s t (rightLocalizationSeed x g) := by
  change decoratedProject x s t (flipWord x) * decoratedProject x s t (localizationSeed x g) *
    (decoratedProject x s t (flipWord x))⁻¹=decoratedProject x s t
      (flipWord x * localizationSeed x g * (flipWord x)⁻¹)
  simp only [map_mul,map_inv]

lemma decoratedLocalizations_commute (g h : DecoratedQuotient (Γ:=Γ) x s t) :
    Commute (decoratedLocalization x s t hs g) (decoratedRightLocalization x s t hs h) := by
  obtain ⟨g,rfl⟩ := decoratedProject_surjective x s t g
  obtain ⟨h,rfl⟩ := decoratedProject_surjective x s t h
  rw [decoratedLocalization_project,decoratedRightLocalization_project]
  exact (structuralProject_comm_all x s hs g h).map (structuralToDecorated x s t)

def decoratedTensor : DecoratedQuotient (Γ:=Γ) x s t × DecoratedQuotient x s t →*
    DecoratedQuotient x s t :=
  (decoratedLocalization x s t hs).noncommCoprod (decoratedRightLocalization x s t hs)
    (decoratedLocalizations_commute x s t hs)

lemma decoratedTensor_apply (g h : DecoratedQuotient (Γ:=Γ) x s t) :
    decoratedTensor x s t hs (g,h)=decoratedLocalization x s t hs g *
      decoratedRightLocalization x s t hs h := rfl

lemma decoratedDiagonal_tensor (g : Γ) :
    decoratedDiagonal x s t hs g=decoratedTensor x s t hs
      (decoratedRoot x s t g,decoratedRoot x s t g) := rfl

lemma structuralToDecorated_localization (g : StructuralQuotient (Γ:=Γ) x s) :
    structuralToDecorated x s t (structuralLocalization x s hs g)=
      decoratedLocalization x s t hs (structuralToDecorated x s t g) :=
  FiniteLocalizationClosure.quotientMap_localization _ _ _ _ hs g

lemma structuralToDecorated_rightLocalization (g : StructuralQuotient (Γ:=Γ) x s) :
    structuralToDecorated x s t (structuralRightLocalization x s hs g)=
      decoratedRightLocalization x s t hs (structuralToDecorated x s t g) := by
  change structuralToDecorated x s t (structuralSymmetry x s * structuralLocalization x s hs g *
    (structuralSymmetry x s)⁻¹)=_
  rw [map_mul,map_mul,map_inv,structuralToDecorated_localization]
  rfl

lemma structuralToDecorated_tensor (g h : StructuralQuotient (Γ:=Γ) x s) :
    structuralToDecorated x s t (structuralTensor x s hs (g,h))=
      decoratedTensor x s t hs (structuralToDecorated x s t g,structuralToDecorated x s t h) := by
  simp only [structuralTensor_apply,decoratedTensor_apply,map_mul,
    structuralToDecorated_localization,structuralToDecorated_rightLocalization]

end Generators
end

section
universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Generators
variable (x : X) [MulAction.IsPretransitive Γ X]

def bakerWord (y : X) : Seed (Γ:=Γ) x :=
  let g := (MulAction.exists_smul_eq Γ x y).choose
  rootWord x g*(halfWord x g*rightWord x g)⁻¹

lemma evaluation_bakerWord (y : X) : evaluation (Γ:=Γ) x (bakerWord x y)=baker x y := by
  let g := (MulAction.exists_smul_eq Γ x y).choose
  have hg : g • x=y := (MulAction.exists_smul_eq Γ x y).choose_spec
  change evaluation x (rootWord x g*(halfWord x g*rightWord x g)⁻¹)=_
  rw [map_mul,map_inv,map_mul,evaluation_rootWord,evaluation_halfWord,evaluation_rightWord]
  change embedding g*(diagonal x (embedding g))⁻¹=baker x y
  rw [← hg,← baker_inverse,baker_smul,mul_inv_rev,inv_inv]

def middleSwapWord : Seed (Γ:=Γ) x :=
  associatorWord x * rightLocalizationSeed x
    ((associatorWord x)⁻¹*localizationSeed x (flipWord x)*associatorWord x) * (associatorWord x)⁻¹

def middleSwapMove : Move (Γ:=Γ) x
    (.split x (.split x .leaf .leaf) (.split x .leaf .leaf))
    (.split x (.split x .leaf .leaf) (.split x .leaf .leaf)) :=
  let l : Tree X := .leaf
  let a := Move.rotate (Γ:=Γ) x l l (.split x l l)
  let b := (Move.refl (Γ:=Γ) (x:=x) l).join (Move.rotate x l l l) x
  let c := (Move.refl (Γ:=Γ) (x:=x) l).join
    ((Move.exchange x l l).join (Move.refl l) x) x
  (((a.symm.trans b).trans c).trans b.symm).trans a

lemma evaluation_middleSwapWord : evaluation (Γ:=Γ) x (middleSwapWord x)=(middleSwapMove x).element := by
  simp only [middleSwapWord,map_mul,map_inv,evaluation_associatorWord,
    evaluation_rightLocalizationSeed,evaluation_localizationSeed,evaluation_flipWord]
  simp only [middleSwapMove,Move.trans,Move.symm,Move.rotate,Move.join,Move.refl,
    Move.exchange,sumElement,map_one,one_mul,mul_one]
  group

lemma middleSwap_attach (b c : Bool) (z : Cube X) :
    (evaluation (Γ:=Γ) x (middleSwapWord x)).val
      ((Prefix.oneBit x b).attach ((Prefix.oneBit x c).attach z))=
      (Prefix.oneBit x c).attach ((Prefix.oneBit x b).attach z) := by
  rw [evaluation_middleSwapWord]
  cases b <;> cases c
  · have hh := (middleSwapMove (Γ:=Γ) x).chart (Sum.inl (Sum.inl PUnit.unit)) z
    have hi : (middleSwapMove (Γ:=Γ) x).leaves (Sum.inl (Sum.inl PUnit.unit))=
        Sum.inl (Sum.inl PUnit.unit) := rfl
    rw [hi] at hh
    simpa only [Tree.brick,Prefix.comp_attach,Prefix.empty_attach] using hh
  · have hh := (middleSwapMove (Γ:=Γ) x).chart (Sum.inl (Sum.inr PUnit.unit)) z
    have hi : (middleSwapMove (Γ:=Γ) x).leaves (Sum.inl (Sum.inr PUnit.unit))=
        Sum.inr (Sum.inl PUnit.unit) := rfl
    rw [hi] at hh
    simpa only [Tree.brick,Prefix.comp_attach,Prefix.empty_attach] using hh
  · have hh := (middleSwapMove (Γ:=Γ) x).chart (Sum.inr (Sum.inl PUnit.unit)) z
    have hi : (middleSwapMove (Γ:=Γ) x).leaves (Sum.inr (Sum.inl PUnit.unit))=
        Sum.inl (Sum.inr PUnit.unit) := rfl
    rw [hi] at hh
    simpa only [Tree.brick,Prefix.comp_attach,Prefix.empty_attach] using hh
  · have hh := (middleSwapMove (Γ:=Γ) x).chart (Sum.inr (Sum.inr PUnit.unit)) z
    have hi : (middleSwapMove (Γ:=Γ) x).leaves (Sum.inr (Sum.inr PUnit.unit))=
        Sum.inr (Sum.inr PUnit.unit) := rfl
    rw [hi] at hh
    simpa only [Tree.brick,Prefix.comp_attach,Prefix.empty_attach] using hh

def gridWord (y z : X) : Seed (Γ:=Γ) x :=
  bakerWord x y * (localizationSeed x (bakerWord x z) * rightLocalizationSeed x (bakerWord x z))

lemma evaluation_gridWord (y z : X) : evaluation (Γ:=Γ) x (gridWord x y z)=
    baker x y*sumElement x (baker x z) (baker x z) := by
  simp only [gridWord,map_mul,evaluation_bakerWord,evaluation_localizationSeed,
    evaluation_rightLocalizationSeed,sumElement,left,right]

lemma gridWord_attach (y z : X) (b c : Bool) (w : Cube X) :
    (evaluation (Γ:=Γ) x (gridWord x y z)).val
      ((Prefix.oneBit x b).attach ((Prefix.oneBit x c).attach w))=
      (Prefix.oneBit y b).attach ((Prefix.oneBit z c).attach w) := by
  rw [evaluation_gridWord]
  change (baker (Γ:=Γ) x y).val ((sumElement x (baker x z) (baker x z)).val
    ((Prefix.oneBit x b).attach ((Prefix.oneBit x c).attach w)))=_
  cases b <;> simp only [sumElement_left,sumElement_right,baker_attach]

/-- One coordinate-interchange relation, between the two literal grids. -/
def interchangeWord (y z : X) : Seed (Γ:=Γ) x :=
  gridWord x y z*(gridWord x z y*middleSwapWord x)⁻¹

omit [MulAction.IsPretransitive Γ X] in
lemma eq_of_doubleBit (f g : group (Γ:=Γ) (X:=X))
    (h : ∀ b c w,f.val ((Prefix.oneBit x b).attach ((Prefix.oneBit x c).attach w))=
      g.val ((Prefix.oneBit x b).attach ((Prefix.oneBit x c).attach w))) : f=g := by
  apply Subtype.ext
  apply Equiv.ext
  intro w
  obtain ⟨b,⟨v,rfl⟩,_⟩ := (Partition.bit x).cover w
  obtain ⟨c,⟨w,rfl⟩,_⟩ := (Partition.bit x).cover v
  exact h b c w

lemma grid_interchange {y z : X} (hyz : y≠z) :
    evaluation (Γ:=Γ) x (gridWord x y z)=
      evaluation x (gridWord x z y)*evaluation x (middleSwapWord x) := by
  apply eq_of_doubleBit x
  intro b c w
  change (evaluation (Γ:=Γ) x (gridWord x y z)).val
    ((Prefix.oneBit x b).attach ((Prefix.oneBit x c).attach w))=
      (evaluation (Γ:=Γ) x (gridWord x z y)).val
        ((evaluation x (middleSwapWord x)).val
          ((Prefix.oneBit x b).attach ((Prefix.oneBit x c).attach w)))
  rw [middleSwap_attach,gridWord_attach,gridWord_attach]
  rw [← Prefix.comp_attach,← Prefix.comp_attach,Prefix.oneBit_comp_comm hyz]

lemma evaluation_interchangeWord {y z : X} (hyz : y≠z) :
    evaluation (Γ:=Γ) x (interchangeWord x y z)=1 := by
  simp only [interchangeWord,map_mul,map_inv]
  rw [grid_interchange x hyz,mul_inv_cancel]

end Generators
end

section
universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Generators
variable (x : X) [MulAction.IsPretransitive Γ X]

def halfAssociatorBinding : Seed (Γ:=Γ) x :=
  generatorWord x ⟨localize (left x) (associator x),by simp [finiteSet]⟩ *
    (localizationSeed x (associatorWord x))⁻¹

def halfFlipBinding : Seed (Γ:=Γ) x :=
  generatorWord x ⟨localize (left x) (flip x),by simp [finiteSet]⟩ *
    (localizationSeed x (flipWord x))⁻¹

lemma evaluation_halfAssociatorBinding : evaluation (Γ:=Γ) x (halfAssociatorBinding x)=1 := by
  simp only [halfAssociatorBinding,map_mul,map_inv,evaluation_generatorWord,
    evaluation_localizationSeed,evaluation_associatorWord,mul_inv_cancel]

lemma evaluation_halfFlipBinding : evaluation (Γ:=Γ) x (halfFlipBinding x)=1 := by
  simp only [halfFlipBinding,map_mul,map_inv,evaluation_generatorWord,
    evaluation_localizationSeed,evaluation_flipWord,mul_inv_cancel]

variable (s : Finset (Seed (Γ:=Γ) x)) (t : Finset (MulAction.stabilizer Γ x)) (y : X)

/-- Explicit finite presentation candidate: structure, stabilizer, generator
bindings, and one orbit representative of distinct-colour interchange.
Its completeness is not built into this definition. -/
def endpointRelations : Finset (Seed (Γ:=Γ) x) :=
  decoratedRelations x s t ∪ {halfAssociatorBinding x,halfFlipBinding x,interchangeWord x x y}

lemma endpointRelations_valid (hxy : x≠y) :
    ∀ g∈endpointRelations x s t y,evaluation x g=1 := by
  intro g hg
  rcases Finset.mem_union.mp hg with hg|hg
  · exact decoratedRelations_valid x s t g hg
  · simp only [Finset.mem_insert,Finset.mem_singleton] at hg
    rcases hg with rfl|rfl|rfl
    · exact evaluation_halfAssociatorBinding x
    · exact evaluation_halfFlipBinding x
    · exact evaluation_interchangeWord x hxy

/-- A finite presentation with a surjection to the concrete simple table group. -/

abbrev EndpointQuotient := LocalQuotient x s (endpointRelations x s t y)

def endpointEvaluation (hxy : x≠y) : EndpointQuotient x s t y →* group (Γ:=Γ) (X:=X) :=
  localEvaluation x s _ (endpointRelations_valid x s t y hxy)

lemma endpointEvaluation_surjective (hxy : x≠y) :
    Function.Surjective (endpointEvaluation x s t y hxy) :=
  localEvaluation_surjective x s _ (endpointRelations_valid x s t y hxy)

def endpointProject : Seed (Γ:=Γ) x →* EndpointQuotient x s t y :=
  FiniteLocalizationClosure.project _ _ _ _

def decoratedToEndpoint : DecoratedQuotient x s t →* EndpointQuotient x s t y :=
  FiniteLocalizationClosure.quotientMap _ _ _ (Finset.subset_union_left)

lemma decoratedToEndpoint_project (g : Seed (Γ:=Γ) x) :
    decoratedToEndpoint x s t y (decoratedProject x s t g)=endpointProject x s t y g := rfl

lemma endpointProject_rel {g : Seed (Γ:=Γ) x} (hg : g∈endpointRelations x s t y) :
    endpointProject x s t y g=1 :=
  FiniteLocalizationClosure.project_base _ _ _ _ (Finset.mem_union_left _ hg)

lemma endpoint_halfAssociatorBinding : endpointProject x s t y
    (generatorWord x ⟨localize (left x) (associator x),by simp [finiteSet]⟩)=
      endpointProject x s t y (localizationSeed x (associatorWord x)) := by
  have h := endpointProject_rel x s t y
    (show halfAssociatorBinding (Γ:=Γ) x∈endpointRelations x s t y from
      Finset.mem_union_right _ (by simp))
  change endpointProject x s t y (_*_⁻¹)=1 at h
  rw [map_mul,map_inv] at h
  exact mul_inv_eq_one.mp h

lemma endpoint_halfFlipBinding : endpointProject x s t y
    (generatorWord x ⟨localize (left x) (flip x),by simp [finiteSet]⟩)=
      endpointProject x s t y (localizationSeed x (flipWord x)) := by
  have h := endpointProject_rel x s t y
    (show halfFlipBinding (Γ:=Γ) x∈endpointRelations x s t y from
      Finset.mem_union_right _ (by simp))
  change endpointProject x s t y (_*_⁻¹)=1 at h
  rw [map_mul,map_inv] at h
  exact mul_inv_eq_one.mp h

lemma endpoint_interchange : endpointProject x s t y (gridWord x x y)=
    endpointProject x s t y (gridWord x y x)*endpointProject x s t y (middleSwapWord x) := by
  have h := endpointProject_rel x s t y
    (show interchangeWord (Γ:=Γ) x x y∈endpointRelations x s t y from
      Finset.mem_union_right _ (by simp))
  simp only [interchangeWord,map_mul,map_inv] at h
  exact mul_inv_eq_one.mp h

end Generators
end

universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Generators
variable (x : X) [MulAction.IsPretransitive Γ X]
variable (s : Finset (Seed (Γ:=Γ) x)) (t : Finset (MulAction.stabilizer Γ x))
variable (hs : Subgroup.closure (s : Set (Seed (Γ:=Γ) x))=⊤)

def decoratedGrid (y z : X) : DecoratedQuotient x s t :=
  decoratedBaker x s t hs y*decoratedTensor x s t hs
    (decoratedBaker x s t hs z,decoratedBaker x s t hs z)

lemma decoratedProject_bakerWord (y : X) :
    decoratedProject x s t (bakerWord x y)=decoratedBaker x s t hs y := by
  simp only [bakerWord,map_mul,map_inv]
  rfl

lemma decoratedProject_gridWord (y z : X) :
    decoratedProject x s t (gridWord x y z)=decoratedGrid x s t hs y z := by
  simp only [gridWord,map_mul]
  rw [← decoratedLocalization_project x s t hs,← decoratedRightLocalization_project x s t hs,
    decoratedProject_bakerWord,decoratedProject_bakerWord]
  rfl

variable (ht : Subgroup.closure (t : Set (MulAction.stabilizer Γ x))=⊤)
include ht

/-- A label at the root passes through a two-colour grid as four identical
leaf labels. All colours here are arbitrary; only finite stabilizer laws were used. -/
lemma decoratedGrid_covariance (g : Γ) (y z : X) :
    decoratedRoot x s t g*decoratedGrid x s t hs y z=
      decoratedGrid x s t hs (g • y) (g • z)*decoratedTensor x s t hs
        (decoratedDiagonal x s t hs g,decoratedDiagonal x s t hs g) := by
  let B := decoratedBaker x s t hs
  let T := decoratedTensor x s t hs
  let R := decoratedRoot x s t g
  let D := decoratedDiagonal x s t hs g
  have hc (y : X) : R*B y=B (g • y)*D := decoratedBaker_covariance x s t hs ht g y
  have hd : D=T (R,R) := decoratedDiagonal_tensor x s t hs g
  have hm₁ : D*T (B z,B z)=T (R*B z,R*B z) := by
    rw [hd]
    exact (map_mul T (R,R) (B z,B z)).symm
  have hm₂ : T (B (g • z)*D,B (g • z)*D)=T (B (g • z),B (g • z))*T (D,D) :=
    map_mul T (B (g • z),B (g • z)) (D,D)
  change R*(B y*T (B z,B z))=(B (g • y)*T (B (g • z),B (g • z)))*T (D,D)
  rw [← mul_assoc,hc,mul_assoc,hm₁,hc,hm₂,mul_assoc]

end Generators
end FiniteAlgebraicEnvelopes.TwistedBrinThompson

end

end OAI
end

section
-- module Solutions.OAIFAE.EndpointCoherence
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Associators, symmetries, coordinate invariance, and coherence of endpoint quotient data.
-/

namespace FiniteAlgebraicEnvelopes.TwistedBrinThompson

section
universe u v
open CategoryTheory
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Generators
variable (x : X) [MulAction.IsPretransitive Γ X] (s : Finset (Seed (Γ:=Γ) x))
variable (hs : Subgroup.closure (s : Set (Seed (Γ:=Γ) x))=⊤)

/-- Every algebraic field comes from the finite structural quotient's proved
relations. No new relation is postulated in order to invoke coherence. -/
def structuralBinaryData : BinaryGroupCategory.Data (StructuralQuotient (Γ:=Γ) x s) where
  tensor := structuralTensor x s hs
  a := structuralAssociator x s
  naturality := structuralTensor_associativity x s hs
  pentagon := by
    simpa only [structuralTensor_apply,map_one,mul_one,one_mul] using
      structuralTensor_pentagon x s hs

/-- The actual finite quotient is the positive-object automorphism group of a
monoidal category. Its empty object is separate, with trivial automorphism group. -/
@[instance_reducible] def structuralMonoidal :
    MonoidalCategory (BinaryGroupCategory.Object (StructuralQuotient (Γ:=Γ) x s)) :=
  BinaryGroupCategory.monoidal (structuralBinaryData x s hs)

end Generators
end

section
universe u v
open CategoryTheory
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Generators
variable (x : X) [MulAction.IsPretransitive Γ X] (s : Finset (Seed (Γ:=Γ) x))
variable (hs : Subgroup.closure (s : Set (Seed (Γ:=Γ) x))=⊤)

def structuralSymmetryData : BinaryGroupCategory.SymmetryData (structuralBinaryData (Γ:=Γ) x s hs) where
  c := structuralSymmetry x s
  square := structuralSymmetry_square x s
  naturality := structuralTensor_symmetry x s hs
  hexagon := by
    change structuralSymmetry x s = structuralAssociator x s *
      structuralTensor x s hs (1,structuralSymmetry x s) * (structuralAssociator x s)⁻¹ *
        structuralTensor x s hs (structuralSymmetry x s,1) * structuralAssociator x s
    simpa only [structuralTensor_apply,map_one,mul_one,one_mul] using structuralTensor_hexagon x s hs

@[instance_reducible] def structuralSymmetric : letI := structuralMonoidal (Γ:=Γ) x s hs;
    SymmetricCategory (BinaryGroupCategory.Object (StructuralQuotient x s)) :=
  BinaryGroupCategory.symmetric (structuralBinaryData x s hs) (structuralSymmetryData x s hs)

end Generators
end

universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Generators
variable (x : X) [MulAction.IsPretransitive Γ X]
variable (s : Finset (Seed (Γ:=Γ) x)) (t : Finset (MulAction.stabilizer Γ x))
variable (hs : Subgroup.closure (s : Set (Seed (Γ:=Γ) x))=⊤)

lemma structuralProject_middleSwapWord :
    structuralProject x s (middleSwapWord x)=
      BinaryGroupCategory.middleSwap (structuralBinaryData x s hs) (structuralSymmetryData x s hs) := by
  simp only [BinaryGroupCategory.middleSwap,structuralBinaryData,structuralSymmetryData,
    structuralTensor_apply,map_one,one_mul,mul_one,structuralAssociator,structuralSymmetry,
    structuralLocalization_project,structuralRightLocalization_project,middleSwapWord,
    map_mul,map_inv]

lemma structuralMiddleSwap_naturality (g : StructuralQuotient (Γ:=Γ) x s) :
    Commute (structuralProject x s (middleSwapWord x))
      (structuralTensor x s hs (structuralTensor x s hs (g,g),structuralTensor x s hs (g,g))) := by
  rw [structuralProject_middleSwapWord x s hs]
  exact BinaryGroupCategory.middleSwap_naturality (structuralBinaryData x s hs)
    (structuralSymmetryData x s hs) g

lemma decoratedMiddleSwap_naturality (g : DecoratedQuotient (Γ:=Γ) x s t) :
    Commute (decoratedProject x s t (middleSwapWord x))
      (decoratedTensor x s t hs (decoratedTensor x s t hs (g,g),decoratedTensor x s t hs (g,g))) := by
  obtain ⟨g,rfl⟩ := structuralToDecorated_surjective x s t g
  have h := (structuralMiddleSwap_naturality x s hs g).map (structuralToDecorated x s t)
  simpa only [structuralToDecorated_tensor,structuralToDecorated_project] using h

end Generators
end FiniteAlgebraicEnvelopes.TwistedBrinThompson

namespace FiniteAlgebraicEnvelopes.TwistedBrinThompson

section
universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Generators
variable (x : X) [MulAction.IsPretransitive Γ X]
variable (s : Finset (Seed (Γ:=Γ) x)) (t : Finset (MulAction.stabilizer Γ x))
variable (hs : Subgroup.closure (s : Set (Seed (Γ:=Γ) x))=⊤)
variable (ht : Subgroup.closure (t : Set (MulAction.stabilizer Γ x))=⊤)
variable (y : X) (hxy : x≠y)
variable (htwo : ∀ x₁ x₂ y₁ y₂ : X,x₁≠x₂ → y₁≠y₂ →
  ∃ g : Γ,g • x₁=y₁ ∧ g • x₂=y₂)
include hs ht hxy htwo

/-- Every distinct-colour elementary interchange follows inside the explicit
finite endpoint quotient, from its one pair representative and finite label
and structural laws. This is not a completeness theorem for arbitrary tables. -/
lemma endpoint_interchange_all (a b : X) (hab : a≠b) :
    endpointProject x s t y (gridWord x a b)=
      endpointProject x s t y (gridWord x b a)*endpointProject x s t y (middleSwapWord x) := by
  let F := decoratedToEndpoint x s t y
  let E := fun a b=>F (decoratedGrid x s t hs a b)
  let R := fun g=>F (decoratedRoot x s t g)
  let D := fun g=>F (decoratedTensor x s t hs
    (decoratedDiagonal x s t hs g,decoratedDiagonal x s t hs g))
  let M := endpointProject x s t y (middleSwapWord x)
  have hc (g : Γ) (a b : X) : R g*E a b=E (g • a) (g • b)*D g := by
    simpa only [map_mul] using congrArg F (decoratedGrid_covariance x s t hs ht g a b)
  have hm (g : Γ) : Commute M (D g) := by
    have h := decoratedMiddleSwap_naturality x s t hs (decoratedRoot x s t g)
    rw [← decoratedDiagonal_tensor x s t hs g] at h
    exact h.map F
  have he (a b : X) : E a b=endpointProject x s t y (gridWord x a b) := by
    dsimp only [E,F]
    rw [← decoratedProject_gridWord x s t hs,decoratedToEndpoint_project]
  have hr : E x y=E y x*M := by
    rw [he,he]
    exact endpoint_interchange x s t y
  obtain ⟨g,hga,hgb⟩ := htwo x y a b hxy hab
  have h := covariant_interchange R D E M hc hm g hga hgb hr
  rwa [he,he] at h

end Generators
end

section
universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Generators
variable (x : X) [MulAction.IsPretransitive Γ X]
variable (s : Finset (Seed (Γ:=Γ) x)) (t : Finset (MulAction.stabilizer Γ x)) (y₀ : X)
variable (hs : Subgroup.closure (s : Set (Seed (Γ:=Γ) x))=⊤)

lemma decoratedToEndpoint_surjective : Function.Surjective (decoratedToEndpoint (Γ:=Γ) x s t y₀) :=
  FiniteLocalizationClosure.quotientMap_surjective _ _ _ _

def endpointLocalization : EndpointQuotient x s t y₀ →* EndpointQuotient x s t y₀ :=
  FiniteLocalizationClosure.localization _ _ _ _ hs

def endpointRightLocalization : EndpointQuotient x s t y₀ →* EndpointQuotient x s t y₀ :=
  (MulAut.conj (endpointProject x s t y₀ (flipWord x))).toMonoidHom.comp
    (endpointLocalization x s t y₀ hs)

lemma decoratedToEndpoint_localization (g : DecoratedQuotient (Γ:=Γ) x s t) :
    decoratedToEndpoint x s t y₀ (decoratedLocalization x s t hs g)=
      endpointLocalization x s t y₀ hs (decoratedToEndpoint x s t y₀ g) :=
  FiniteLocalizationClosure.quotientMap_localization _ _ _ _ hs g

lemma decoratedToEndpoint_rightLocalization (g : DecoratedQuotient (Γ:=Γ) x s t) :
    decoratedToEndpoint x s t y₀ (decoratedRightLocalization x s t hs g)=
      endpointRightLocalization x s t y₀ hs (decoratedToEndpoint x s t y₀ g) := by
  change decoratedToEndpoint x s t y₀ (decoratedProject x s t (flipWord x)*
    decoratedLocalization x s t hs g*(decoratedProject x s t (flipWord x))⁻¹)=_
  rw [map_mul,map_mul,map_inv,decoratedToEndpoint_localization]
  rfl

lemma endpointLocalizations_commute (g h : EndpointQuotient (Γ:=Γ) x s t y₀) :
    Commute (endpointLocalization x s t y₀ hs g) (endpointRightLocalization x s t y₀ hs h) := by
  obtain ⟨g,rfl⟩ := decoratedToEndpoint_surjective x s t y₀ g
  obtain ⟨h,rfl⟩ := decoratedToEndpoint_surjective x s t y₀ h
  simpa only [decoratedToEndpoint_localization,decoratedToEndpoint_rightLocalization] using
    (decoratedLocalizations_commute x s t hs g h).map (decoratedToEndpoint x s t y₀)

def endpointTensor : EndpointQuotient (Γ:=Γ) x s t y₀ × EndpointQuotient x s t y₀ →*
    EndpointQuotient x s t y₀ :=
  (endpointLocalization x s t y₀ hs).noncommCoprod (endpointRightLocalization x s t y₀ hs)
    (endpointLocalizations_commute x s t y₀ hs)

lemma endpointTensor_apply (g h : EndpointQuotient (Γ:=Γ) x s t y₀) :
    endpointTensor x s t y₀ hs (g,h)=endpointLocalization x s t y₀ hs g *
      endpointRightLocalization x s t y₀ hs h := rfl

lemma decoratedToEndpoint_tensor (g h : DecoratedQuotient (Γ:=Γ) x s t) :
    decoratedToEndpoint x s t y₀ (decoratedTensor x s t hs (g,h))=
      endpointTensor x s t y₀ hs (decoratedToEndpoint x s t y₀ g,decoratedToEndpoint x s t y₀ h) := by
  simp only [decoratedTensor_apply,endpointTensor_apply,map_mul,
    decoratedToEndpoint_localization,decoratedToEndpoint_rightLocalization]

def endpointBaker (y : X) : EndpointQuotient x s t y₀ :=
  decoratedToEndpoint x s t y₀ (decoratedBaker x s t hs y)

end Generators
end

universe u v w
attribute [local instance] Classical.propDecidable

variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]

namespace Generators
variable (x : X) [MulAction.IsPretransitive Γ X]
variable (s : Finset (Seed (Γ:=Γ) x)) (t : Finset (MulAction.stabilizer Γ x)) (y₀ : X)
variable (hs : Subgroup.closure (s : Set (Seed (Γ:=Γ) x))=⊤)
variable (ht : Subgroup.closure (t : Set (MulAction.stabilizer Γ x))=⊤)

def endpointRoot : Γ →* EndpointQuotient x s t y₀ :=
  (endpointProject x s t y₀).comp (rootWord x)

lemma decoratedToEndpoint_root (g : Γ) :
    decoratedToEndpoint x s t y₀ (decoratedRoot x s t g)=endpointRoot x s t y₀ g :=
  decoratedToEndpoint_project x s t y₀ (rootWord x g)

end Generators
end FiniteAlgebraicEnvelopes.TwistedBrinThompson

end

end OAI
end

section
-- module Solutions.OAIFAE.TreeCoherence
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Decorated tree interpretation, grafting, leaf values, and common-refinement invariance.
-/

namespace FiniteAlgebraicEnvelopes.TwistedBrinThompson.Tree

universe v w
open BinaryGroupCategory
variable {X : Type v} {H : Type w} [Group H] (d:Data H) (q:SymmetryData d) (B:X → H)

lemma flatten_quad (x y:X) : flatten d B (quad x y)=B x*d.tensor (B y,B y)*d.a := by
  change B x*d.tensor (flatten d B (.split y .leaf .leaf),flatten d B (.split y .leaf .leaf))*
    (merge d 1)⁻¹=_
  rw [flatten_bit,merge_succ,merge_zero,map_one,one_mul,inv_inv]

lemma ordinalEquiv_quad (x y z w:X) :
    ordinalEquiv (a:=quad x y) (b:=quad z w) (Equiv.sumSumSumComm PUnit PUnit PUnit PUnit)=
      Equiv.swap (1:Fin 4) (2:Fin 4) := by
  apply Equiv.ext; intro i
  fin_cases i <;> rfl

lemma leafValue_quad_middle (x y z w:X) :
    leafValue d q B (a:=quad x y) (b:=quad z w) (Equiv.sumSumSumComm PUnit PUnit PUnit PUnit)=
      (B z*d.tensor (B w,B w))*middleSwap d q*(B x*d.tensor (B y,B y))⁻¹ := by
  rw [leafValue,ordinalEquiv_quad,equivVal_same,flatten_quad,flatten_quad]
  change (B z*d.tensor (B w,B w)*d.a)*
    combPermutation d q 3 (Equiv.swap (1:Fin 3).castSucc (1:Fin 3).succ)*
      (B x*d.tensor (B y,B y)*d.a)⁻¹=_
  rw [combPermutation_swap,combSwap_internal d q (by decide)]
  change (B z*d.tensor (B w,B w)*d.a)*
    d.tensor (1,d.a⁻¹*d.tensor (q.c,1)*d.a)*(B x*d.tensor (B y,B y)*d.a)⁻¹=_
  dsimp only [middleSwap]
  group

lemma leafValue_middle (x y z w:X) (a b c f:Tree X) :
    leafValue d q B (a:=.split x (.split y a b) (.split y c f))
      (b:=.split z (.split w a c) (.split w b f)) (Equiv.sumSumSumComm _ _ _ _)=
      (B z*d.tensor (B w,B w))*middleSwap d q*(B x*d.tensor (B y,B y))⁻¹ := by
  let F : (quad z w).Leaves → Tree X
    | Sum.inl (Sum.inl _) => a
    | Sum.inl (Sum.inr _) => c
    | Sum.inr (Sum.inl _) => b
    | Sum.inr (Sum.inr _) => f
  let e : (quad x y).Leaves ≃ (quad z w).Leaves := Equiv.sumSumSumComm _ _ _ _
  have he : graftLift e F=Equiv.sumSumSumComm a.Leaves b.Leaves c.Leaves f.Leaves := by
    apply Equiv.ext
    rintro ((i|i)|(i|i)) <;> rfl
  have hv := leafValue_graftLift d q B x e F
  rw [he] at hv
  exact hv.trans (leafValue_quad_middle d q B x y z w)

lemma leafValue_interchange (g:GridLaw d q B) {x y:X} (hxy:x≠y) (a b c f:Tree X) :
    leafValue d q B (a:=.split x (.split y a b) (.split y c f))
      (b:=.split y (.split x a c) (.split x b f)) (Equiv.sumSumSumComm _ _ _ _)=1 := by
  rw [leafValue_middle,← g.grid x y hxy,mul_inv_cancel]

lemma SameBricks.unique {a b:Tree X} {e f:a.Leaves ≃ b.Leaves}
    (he:SameBricks e) (hf:SameBricks f) : e=f := by
  apply Equiv.ext; intro i
  exact b.partition.brick_injective ((he i).symm.trans (hf i))

lemma SameBricks.brickSet_eq {a b:Tree X} {e:a.Leaves ≃ b.Leaves} (he:SameBricks e) :
    a.brickSet=b.brickSet := by
  ext p
  constructor
  · rintro ⟨i,rfl⟩; exact ⟨e i,(he i).symm⟩
  · rintro ⟨i,rfl⟩; exact ⟨e.symm i,by simpa using he (e.symm i)⟩

lemma sameBricks_sum {a b c f:Tree X} (x:X) {e:a.Leaves ≃ c.Leaves} {g:b.Leaves ≃ f.Leaves}
    (he:SameBricks e) (hg:SameBricks g) :
    SameBricks (a:=.split x a b) (b:=.split x c f) (Equiv.sumCongr e g) := by
  rintro (i|i)
  · exact congrArg ((Prefix.oneBit x false).comp) (he i)
  · exact congrArg ((Prefix.oneBit x true).comp) (hg i)

lemma sameBricks_interchange {x y:X} (hxy:x≠y) (a b c f:Tree X) :
    SameBricks (a:=.split x (.split y a b) (.split y c f))
      (b:=.split y (.split x a c) (.split x b f)) (Equiv.sumSumSumComm _ _ _ _) := by
  rintro ((i|i)|(i|i)) <;>
    change (Prefix.oneBit x _).comp ((Prefix.oneBit y _).comp _) =
      (Prefix.oneBit y _).comp ((Prefix.oneBit x _).comp _) <;>
    rw [← Prefix.comp_assoc,← Prefix.comp_assoc,Prefix.oneBit_comp_comm hxy] <;> rfl

lemma Coherent.exists_value_one (g:GridLaw d q B) {a b:Tree X} (h:Coherent a b) :
    ∃ e:a.Leaves ≃ b.Leaves,SameBricks e ∧ leafValue d q B e=1 := by
  induction h with
  | refl a => exact ⟨Equiv.refl _,fun _=>rfl,leafValue_refl d q B a⟩
  | symm h ih =>
    obtain ⟨e,he,hv⟩ := ih
    exact ⟨e.symm,he.symm,by rw [leafValue_symm,hv,inv_one]⟩
  | trans h k ih ik =>
    obtain ⟨e,he,hv⟩ := ih
    obtain ⟨f,hf,hw⟩ := ik
    exact ⟨e.trans f,he.trans hf,by rw [leafValue_trans,hv,hw,mul_one]⟩
  | split x h k ih ik =>
    obtain ⟨e,he,hv⟩ := ih
    obtain ⟨f,hf,hw⟩ := ik
    refine ⟨Equiv.sumCongr e f,sameBricks_sum x he hf,?_⟩
    rw [leafValue_sum,hv,hw]
    have ht : d.tensor (1,1)=1 := d.tensor.map_one
    rw [ht,mul_one,mul_inv_cancel]
  | interchange hxy a b c f =>
    exact ⟨Equiv.sumSumSumComm _ _ _ _,sameBricks_interchange hxy a b c f,
      leafValue_interchange d q B g hxy a b c f⟩

/-- All equality between actual tree partitions follows from the finite colour
interchange law, including the induced full permutation of their leaves. -/
lemma leafValue_of_sameBricks (g:GridLaw d q B) {a b:Tree X} (e:a.Leaves ≃ b.Leaves)
    (he:SameBricks e) : leafValue d q B e=1 := by
  obtain ⟨f,hf,hv⟩ := (coherent_of_brickSet_eq a b he.brickSet_eq).exists_value_one d q B g
  rwa [← he.unique hf] at hv

end FiniteAlgebraicEnvelopes.TwistedBrinThompson.Tree

namespace FiniteAlgebraicEnvelopes.TwistedBrinThompson
universe u v
open BinaryGroupCategory
variable {Γ:Type u} {X:Type v} [Group Γ] [MulAction Γ X]
namespace Generators
variable (x:X) [MulAction.IsPretransitive Γ X]
variable (s:Finset (Seed (Γ:=Γ) x)) (t:Finset (MulAction.stabilizer Γ x)) (y₀:X)
variable (hs:Subgroup.closure (s:Set (Seed (Γ:=Γ) x))=⊤)

def structuralToEndpoint : StructuralQuotient x s →* EndpointQuotient x s t y₀ :=
  (decoratedToEndpoint x s t y₀).comp (structuralToDecorated x s t)
lemma structuralToEndpoint_project (g:Seed (Γ:=Γ) x) :
    structuralToEndpoint x s t y₀ (structuralProject x s g)=endpointProject x s t y₀ g := rfl
lemma structuralToEndpoint_surjective : Function.Surjective (structuralToEndpoint (Γ:=Γ) x s t y₀) :=
  (decoratedToEndpoint_surjective x s t y₀).comp (structuralToDecorated_surjective x s t)
lemma structuralToEndpoint_tensor (a b:StructuralQuotient (Γ:=Γ) x s) :
    structuralToEndpoint x s t y₀ (structuralTensor x s hs (a,b))=
      endpointTensor x s t y₀ hs (structuralToEndpoint x s t y₀ a,structuralToEndpoint x s t y₀ b) := by
  change decoratedToEndpoint x s t y₀ (structuralToDecorated x s t (structuralTensor x s hs (a,b)))=_
  rw [structuralToDecorated_tensor,decoratedToEndpoint_tensor]; rfl

/-- The finite endpoint quotient supplies the full binary symmetric structure. -/
def endpointData : Data (EndpointQuotient (Γ:=Γ) x s t y₀) where
  tensor := endpointTensor x s t y₀ hs
  a := endpointProject x s t y₀ (associatorWord x)
  naturality := by
    intro a b c
    obtain ⟨a,rfl⟩ := structuralToEndpoint_surjective x s t y₀ a
    obtain ⟨b,rfl⟩ := structuralToEndpoint_surjective x s t y₀ b
    obtain ⟨c,rfl⟩ := structuralToEndpoint_surjective x s t y₀ c
    have h := congrArg (structuralToEndpoint x s t y₀) ((structuralBinaryData x s hs).naturality a b c)
    simpa only [map_mul,map_inv,structuralBinaryData,structuralAssociator,
      structuralToEndpoint_project,structuralToEndpoint_tensor] using h
  pentagon := by
    have h := congrArg (structuralToEndpoint x s t y₀) ((structuralBinaryData x s hs).pentagon)
    simpa only [map_mul,map_one,structuralBinaryData,structuralAssociator,
      structuralToEndpoint_project,structuralToEndpoint_tensor] using h

def endpointSymmetryData : SymmetryData (endpointData (Γ:=Γ) x s t y₀ hs) where
  c := endpointProject x s t y₀ (flipWord x)
  square := by
    have h := congrArg (structuralToEndpoint x s t y₀) ((structuralSymmetryData x s hs).square)
    simpa only [map_mul,map_one,structuralSymmetryData,structuralSymmetry,
      structuralToEndpoint_project] using h
  naturality := by
    intro a b
    obtain ⟨a,rfl⟩ := structuralToEndpoint_surjective x s t y₀ a
    obtain ⟨b,rfl⟩ := structuralToEndpoint_surjective x s t y₀ b
    have h := congrArg (structuralToEndpoint x s t y₀) ((structuralSymmetryData x s hs).naturality a b)
    simpa only [map_mul,map_inv,structuralSymmetryData,structuralBinaryData,structuralSymmetry,
      structuralToEndpoint_project,structuralToEndpoint_tensor,endpointData] using h
  hexagon := by
    have h := congrArg (structuralToEndpoint x s t y₀) ((structuralSymmetryData x s hs).hexagon)
    simpa only [map_mul,map_inv,map_one,structuralSymmetryData,structuralBinaryData,structuralSymmetry,
      structuralAssociator,structuralToEndpoint_project,structuralToEndpoint_tensor,endpointData] using h

lemma endpointProject_middleSwapWord : endpointProject x s t y₀ (middleSwapWord (Γ:=Γ) x)=
    middleSwap (endpointData x s t y₀ hs) (endpointSymmetryData x s t y₀ hs) := by
  have h := congrArg (structuralToEndpoint x s t y₀) (structuralProject_middleSwapWord x s hs)
  simpa only [middleSwap,map_mul,map_inv,map_one,structuralToEndpoint_tensor,
    structuralToEndpoint_project,structuralBinaryData,structuralSymmetryData,
    structuralAssociator,structuralSymmetry,endpointData,endpointSymmetryData] using h

lemma endpointProject_gridWord (a b:X) : endpointProject x s t y₀ (gridWord (Γ:=Γ) x a b)=
    endpointBaker x s t y₀ hs a * endpointTensor x s t y₀ hs
      (endpointBaker x s t y₀ hs b,endpointBaker x s t y₀ hs b) := by
  have h := congrArg (decoratedToEndpoint x s t y₀) (decoratedProject_gridWord x s t hs a b)
  simpa only [decoratedToEndpoint_project,decoratedGrid,map_mul,decoratedToEndpoint_tensor,
    endpointBaker] using h

variable (ht:Subgroup.closure (t:Set (MulAction.stabilizer Γ x))=⊤)
include ht
lemma endpointBaker_base : endpointBaker x s t y₀ hs x=1 := by
  rw [endpointBaker,decoratedBaker_base x s t hs ht,map_one]
lemma endpointBaker_covariance (g:Γ) (y:X) :
    endpointRoot x s t y₀ g*endpointBaker x s t y₀ hs y=
      endpointBaker x s t y₀ hs (g • y)*endpointTensor x s t y₀ hs
        (endpointRoot x s t y₀ g,endpointRoot x s t y₀ g) := by
  have h := congrArg (decoratedToEndpoint x s t y₀) (decoratedBaker_covariance x s t hs ht g y)
  simpa only [map_mul,decoratedDiagonal_tensor,decoratedToEndpoint_tensor,
    decoratedToEndpoint_root,endpointBaker] using h

variable (hxy:x≠y₀) (htwo:∀ x₁ x₂ y₁ y₂:X,x₁≠x₂ → y₁≠y₂ → ∃ g:Γ,g • x₁=y₁ ∧ g • x₂=y₂)

include hxy htwo in
theorem endpointGridLaw : Tree.GridLaw (endpointData x s t y₀ hs) (endpointSymmetryData x s t y₀ hs)
    (endpointBaker x s t y₀ hs) where
  grid a b hab := by
    have h := endpoint_interchange_all x s t hs ht y₀ hxy htwo a b hab
    simpa only [endpointProject_gridWord x s t y₀ hs,endpointData,
      endpointProject_middleSwapWord x s t y₀ hs] using h

end Generators
end FiniteAlgebraicEnvelopes.TwistedBrinThompson

end

end OAI
end

section
-- module Solutions.OAIFAE.Diagrams
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Represented diagrams and actual endpoint evaluation injectivity and equivalence.
-/

namespace FiniteAlgebraicEnvelopes.TwistedBrinThompson

section
universe u v w
open BinaryGroupCategory

namespace Diagram
variable {Γ:Type u} {X:Type v} {H:Type w} [Group Γ] [MulAction Γ X] [Group H]
variable (d:Data H) (q:SymmetryData d) (B:X → H) (R:Γ →* H)

omit [MulAction Γ X] in
lemma value_root (g:Γ) : value d q B R (root (X:=X) g)=R g := by
  change Tree.leafValue d q B (a:=.leaf) (b:=.leaf) (Equiv.refl _)*R g=R g
  rw [Tree.leafValue_refl,one_mul]
lemma realizes_root (g:Γ) : Realizes (root (X:=X) g) (twist g) := by
  intro i z; simp only [root,Tree.brick,Prefix.empty_attach]

lemma value_one_of_realizes_one (gl:Tree.GridLaw d q B) [FaithfulSMul Γ X]
    (A:Diagram Γ X) (h:Realizes A 1) : value d q B R A=1 := by
  have hr (i:A.source.Leaves) : A.source.brick i=A.target.brick (A.wires i) ∧ 1=A.label i := by
    apply chart_rigidity
    intro z
    simpa only [twist_one,Equiv.Perm.one_apply] using h i z
  rw [value,Tree.leafValue_of_sameBricks d q B gl A.wires (fun i=>(hr i).1),one_mul]
  have hl : (fun i=>R (A.label i))=fun _=>1 := by
    funext i; rw [← (hr i).2,map_one]
  rw [hl,Tree.fold_one]

end Diagram
end

section
universe u v w
open BinaryGroupCategory
attribute [local instance] Classical.propDecidable
variable {Γ:Type u} {X:Type v} {H:Type w} [Group Γ] [MulAction Γ X] [Group H]
namespace Diagram
variable (d:Data H) (q:SymmetryData d) (B:X → H) (R:Γ →* H) (x:X)
variable (hR:∀ g x,R g*B x=B (g • x)*d.tensor (R g,R g))
include x hR

/-- The actual tree-pair value is closed under multiplication, synchronizing
all intermediate bricks by a finite grid; no patching assumption is used. -/
lemma product (gl:Tree.GridLaw d q B) {A C:Diagram Γ X} {f g:Equiv.Perm (Cube X)}
    (ha:Realizes A f) (hc:Realizes C g) :
    ∃ D:Diagram Γ X,Realizes D (g*f) ∧ value d q B R D=value d q B R C*value d q B R A := by
  obtain ⟨l,hl⟩ := Partition.exists_tree_grid_bound
    (Sum.elim A.target.brick C.source.brick)
  obtain ⟨A',ha',hvA,e,he⟩ := refine_target_grid d q B R x hR ha l (fun i=>hl (Sum.inl i))
  obtain ⟨C',hc',hvC,e',he'⟩ := refine_source_grid d q B R x hR hc l (fun i=>hl (Sum.inr i))
  refine ⟨compose A' C' (e.trans e'.symm),ha'.compose hc' _ (he.trans he'.symm),?_⟩
  rw [value_compose d q B R x,Tree.leafValue_of_sameBricks d q B gl _ (he.trans he'.symm),
    mul_one,hvC,hvA]

end Diagram
end

universe u v w
open BinaryGroupCategory
variable {Γ:Type u} {X:Type v} {H:Type w} [Group Γ] [MulAction Γ X] [Group H]
namespace Diagram
variable (d:Data H) (q:SymmetryData d) (B:X → H) (R:Γ →* H)

omit [MulAction Γ X] in
lemma value_plain (a b:Tree X) (e:a.Leaves ≃ b.Leaves) :
    value d q B R (plain (Γ:=Γ) a b e)=Tree.leafValue d q B e := by
  change Tree.leafValue d q B e*Tree.fold d B a (fun _=>R 1)=_
  simp only [map_one,Tree.fold_one,mul_one]
lemma realizes_plain (a b:Tree X) (e:a.Leaves ≃ b.Leaves) :
    Realizes (plain (Γ:=Γ) a b e) (a.partition.changeChart (Γ:=Γ) b.partition e).val := by
  change ∀ (i:a.Leaves) z, _
  intro i z
  change (a.partition.changeChart (Γ:=Γ) b.partition e).val ((a.brick i).attach z)=
    (b.brick (e i)).attach (twist (1:Γ) z)
  rw [twist_one,Equiv.Perm.one_apply]
  exact Partition.changeChart_apply (Γ:=Γ) a.partition b.partition e i z

omit [MulAction Γ X] in
lemma value_half (x:X) (A:Diagram Γ X) :
    value d q B R (half x A)=B x*d.tensor (value d q B R A,1)*(B x)⁻¹ := by
  change Tree.leafValue d q B (a:=.split x A.source .leaf) (b:=.split x A.target .leaf)
    (Equiv.sumCongr A.wires (Equiv.refl _))*
    (B x*d.tensor (Tree.fold d B A.source (fun i=>R (A.label i)),R 1)*(B x)⁻¹)=_
  rw [Tree.leafValue_sum,Tree.leafValue_refl,map_one]
  calc
    _=B x*(d.tensor (Tree.leafValue d q B A.wires,1)*
      d.tensor (Tree.fold d B A.source (fun i=>R (A.label i)),1))*(B x)⁻¹ := by group
    _=_ := by rw [← map_mul]; simp only [Prod.mk_mul_mk,mul_one]; rfl

abbrev rotation (x:X) : Diagram Γ X :=
  plain (.split x .leaf (.split x .leaf .leaf)) (.split x (.split x .leaf .leaf) .leaf)
    (Equiv.sumAssoc _ _ _).symm

omit [MulAction Γ X] in
lemma value_rotation (x:X) (hx:B x=1) : value d q B R (rotation (Γ:=Γ) x)=d.a := by
  rw [value_plain,Tree.leafValue_symm,Tree.leafValue_assoc,hx]
  simp only [show d.tensor (1,1)=1 from d.tensor.map_one,one_mul,mul_one,inv_one,inv_inv]
lemma realizes_rotation (x:X) : Realizes (rotation (Γ:=Γ) x) (Generators.associator (Γ:=Γ) x).val :=
  realizes_plain _ _ _

omit [MulAction Γ X] in
lemma value_exchange (x:X) (hx:B x=1) : value d q B R (exchange (Γ:=Γ) x)=q.c := by
  rw [value_plain,Tree.leafValue_exchange,hx,one_mul,inv_one,mul_one]
lemma realizes_exchange (x:X) : Realizes (exchange (Γ:=Γ) x) (Generators.flip (Γ:=Γ) x).val := by
  change ∀ (i:(Tree.leaf:Tree X).Leaves ⊕ (Tree.leaf:Tree X).Leaves) z, _
  rintro (i|i) z
  · change (Generators.flip (Γ:=Γ) x).val
      (((Prefix.oneBit x false).comp Prefix.empty).attach z)=
        (((Prefix.oneBit x true).comp Prefix.empty).attach (twist (1:Γ) z))
    rw [Prefix.comp_empty,Prefix.comp_empty,twist_one,Equiv.Perm.one_apply]
    exact Generators.flip_left x z
  · change (Generators.flip (Γ:=Γ) x).val
      (((Prefix.oneBit x true).comp Prefix.empty).attach z)=
        (((Prefix.oneBit x false).comp Prefix.empty).attach (twist (1:Γ) z))
    rw [Prefix.comp_empty,Prefix.comp_empty,twist_one,Equiv.Perm.one_apply]
    exact (Partition.bit x).permute_attach (Γ:=Γ) Equiv.boolNot true z

end Diagram
end FiniteAlgebraicEnvelopes.TwistedBrinThompson

namespace FiniteAlgebraicEnvelopes.TwistedBrinThompson.Diagram
universe u v w k
open BinaryGroupCategory
variable {Γ:Type u} {X:Type v} {H:Type w} {K:Type k}
  [Group Γ] [MulAction Γ X] [Group H] [Group K]
variable (d:Data H) (q:SymmetryData d) (B:X → H) (R:Γ →* H) (x:X)
variable (hR:∀ g x,R g*B x=B (g • x)*d.tensor (R g,R g)) (gl:Tree.GridLaw d q B)
variable (P:K →* H) (E:K →* Equiv.Perm (Cube X))

/-- Elements with a genuine decorated-tree witness for both their algebraic
value and their actual cube action form a subgroup. -/
def represented : Subgroup K where
  carrier k := ∃ A:Diagram Γ X,value d q B R A=P k ∧ Realizes A (E k)
  one_mem' := by
    refine ⟨root 1,?_,?_⟩
    · rw [value_root,map_one,map_one]
    · rw [map_one]; simpa only [twist_one] using realizes_root (X:=X) (1:Γ)
  inv_mem' := by
    rintro a ⟨A,hv,ha⟩
    refine ⟨A.inverse,?_,?_⟩
    · rw [value_inverse d q B R x,hv,map_inv]
    · rw [map_inv]; exact ha.inverse
  mul_mem' := by
    rintro a b ⟨A,hvA,ha⟩ ⟨C,hvC,hc⟩
    obtain ⟨D,hd,hv⟩ := product d q B R x hR gl hc ha
    refine ⟨D,?_,?_⟩
    · rw [hv,hvA,hvC,map_mul]
    · rw [map_mul]; exact hd

end FiniteAlgebraicEnvelopes.TwistedBrinThompson.Diagram

namespace FiniteAlgebraicEnvelopes.TwistedBrinThompson

section
universe u v
open BinaryGroupCategory
attribute [local instance] Classical.propDecidable
variable {Γ:Type u} {X:Type v} [Group Γ] [MulAction Γ X]
namespace Generators
variable (x:X) [MulAction.IsPretransitive Γ X]
variable (s:Finset (Seed (Γ:=Γ) x)) (t:Finset (MulAction.stabilizer Γ x)) (y₀:X)
variable (hs:Subgroup.closure (s:Set (Seed (Γ:=Γ) x))=⊤)
variable (ht:Subgroup.closure (t:Set (MulAction.stabilizer Γ x))=⊤)
variable (hxy:x≠y₀) (htwo:∀ x₁ x₂ y₁ y₂:X,x₁≠x₂ → y₁≠y₂ → ∃ g:Γ,g • x₁=y₁ ∧ g • x₂=y₂)

local notation "D" => endpointData x s t y₀ hs
local notation "Q" => endpointSymmetryData x s t y₀ hs
local notation "B" => endpointBaker x s t y₀ hs
local notation "R" => endpointRoot x s t y₀
local notation "P" => endpointProject x s t y₀
local notation "E" => MonoidHom.comp (Subgroup.subtype (group (Γ:=Γ) (X:=X))) (evaluation x)

def seedRepresented : Subgroup (Seed (Γ:=Γ) x) :=
  Diagram.represented D Q B R x (endpointBaker_covariance x s t y₀ hs ht)
    (endpointGridLaw x s t y₀ hs ht hxy htwo) P E

lemma root_mem_seedRepresented (g:Γ) : rootWord x g∈seedRepresented x s t y₀ hs ht hxy htwo := by
  refine ⟨Diagram.root g,?_,?_⟩
  · exact Diagram.value_root D Q B R g
  · exact Diagram.realizes_root g

lemma half_mem_seedRepresented (g:Γ) : halfWord x g∈seedRepresented x s t y₀ hs ht hxy htwo := by
  refine ⟨Diagram.half x (Diagram.root g),?_,?_⟩
  · change Diagram.value D Q B R (Diagram.half x (Diagram.root g))=P (halfWord x g)
    rw [Diagram.value_half,Diagram.value_root,endpointBaker_base x s t y₀ hs ht]
    simp only [one_mul,inv_one,mul_one]
    change endpointTensor x s t y₀ hs (R g,1)=_
    rw [endpointTensor_apply,map_one,mul_one]
    rfl
  · exact (Diagram.realizes_root g).half x

lemma associator_mem_seedRepresented : associatorWord (Γ:=Γ) x∈seedRepresented x s t y₀ hs ht hxy htwo := by
  refine ⟨Diagram.rotation x,?_,?_⟩
  · exact Diagram.value_rotation D Q B R x (endpointBaker_base x s t y₀ hs ht)
  · exact Diagram.realizes_rotation x

lemma flip_mem_seedRepresented : flipWord (Γ:=Γ) x∈seedRepresented x s t y₀ hs ht hxy htwo := by
  refine ⟨Diagram.exchange x,?_,?_⟩
  · exact Diagram.value_exchange D Q B R x (endpointBaker_base x s t y₀ hs ht)
  · exact Diagram.realizes_exchange x

lemma half_associator_mem_seedRepresented :
    generatorWord x ⟨localize (left x) (associator (Γ:=Γ) x),by simp [finiteSet]⟩∈
      seedRepresented x s t y₀ hs ht hxy htwo := by
  refine ⟨Diagram.half x (Diagram.rotation x),?_,?_⟩
  · change Diagram.value D Q B R (Diagram.half x (Diagram.rotation x))=P _
    rw [Diagram.value_half,Diagram.value_rotation D Q B R x (endpointBaker_base x s t y₀ hs ht),
      endpointBaker_base x s t y₀ hs ht]
    simp only [one_mul,inv_one,mul_one]
    change endpointTensor x s t y₀ hs (P (associatorWord x),1)=_
    rw [endpointTensor_apply,map_one,mul_one]
    exact (endpoint_halfAssociatorBinding x s t y₀).symm
  · exact (Diagram.realizes_rotation (Γ:=Γ) x).half x

lemma half_flip_mem_seedRepresented :
    generatorWord x ⟨localize (left x) (flip (Γ:=Γ) x),by simp [finiteSet]⟩∈
      seedRepresented x s t y₀ hs ht hxy htwo := by
  refine ⟨Diagram.half x (Diagram.exchange x),?_,?_⟩
  · change Diagram.value D Q B R (Diagram.half x (Diagram.exchange x))=P _
    rw [Diagram.value_half,Diagram.value_exchange D Q B R x (endpointBaker_base x s t y₀ hs ht),
      endpointBaker_base x s t y₀ hs ht]
    simp only [one_mul,inv_one,mul_one]
    change endpointTensor x s t y₀ hs (P (flipWord x),1)=_
    rw [endpointTensor_apply,map_one,mul_one]
    exact (endpoint_halfFlipBinding x s t y₀).symm
  · exact (Diagram.realizes_exchange (Γ:=Γ) x).half x

lemma generator_mem_seedRepresented (g:finiteSet (Γ:=Γ) x) :
    generatorWord x g∈seedRepresented x s t y₀ hs ht hxy htwo := by
  rcases g with ⟨g,hg⟩
  simp only [finiteSet,Finset.mem_insert,Finset.mem_singleton] at hg
  rcases hg with rfl|rfl|rfl|rfl
  · exact associator_mem_seedRepresented x s t y₀ hs ht hxy htwo
  · exact half_associator_mem_seedRepresented x s t y₀ hs ht hxy htwo
  · exact flip_mem_seedRepresented x s t y₀ hs ht hxy htwo
  · exact half_flip_mem_seedRepresented x s t y₀ hs ht hxy htwo

/-- The entire finite presentation seed, not just its selected finite
subgenerators, is represented by genuine decorated diagrams. -/
lemma all_seedRepresented (g:Seed (Γ:=Γ) x) : g∈seedRepresented x s t y₀ hs ht hxy htwo := by
  let S := seedRepresented x s t y₀ hs ht hxy htwo
  change g∈S
  refine Monoid.Coprod.induction_on g ?_ ?_ (fun _ _ ha hb=>S.mul_mem ha hb)
  · intro a
    refine Monoid.Coprod.induction_on a ?_ ?_ ?_
    · intro a; exact root_mem_seedRepresented x s t y₀ hs ht hxy htwo a
    · intro a; exact half_mem_seedRepresented x s t y₀ hs ht hxy htwo a
    · intro a b ha hb; rw [map_mul]; exact S.mul_mem ha hb
  · intro a
    refine FreeGroup.induction_on a ?_ ?_ ?_ ?_
    · rw [map_one]; exact S.one_mem
    · intro a; exact generator_mem_seedRepresented x s t y₀ hs ht hxy htwo a
    · intro a ha; rw [map_inv]; exact S.inv_mem ha
    · intro a b ha hb; rw [map_mul]; exact S.mul_mem ha hb

end Generators
end

universe u v
open BinaryGroupCategory
variable {Γ:Type u} {X:Type v} [Group Γ] [MulAction Γ X]
namespace Generators
variable (x:X) [MulAction.IsPretransitive Γ X]
variable (s:Finset (Seed (Γ:=Γ) x)) (t:Finset (MulAction.stabilizer Γ x)) (y₀:X)
variable (hs:Subgroup.closure (s:Set (Seed (Γ:=Γ) x))=⊤)
variable (ht:Subgroup.closure (t:Set (MulAction.stabilizer Γ x))=⊤)
variable (hxy:x≠y₀) (htwo:∀ x₁ x₂ y₁ y₂:X,x₁≠x₂ → y₁≠y₂ → ∃ g:Γ,g • x₁=y₁ ∧ g • x₂=y₂)

lemma endpointProject_surjective : Function.Surjective (endpointProject (Γ:=Γ) x s t y₀) :=
  QuotientGroup.mk'_surjective _

include hs ht htwo

/-- Every element of the actual finite endpoint presentation has a finite
coloured decorated tree-pair whose value and semantics agree with it. -/
lemma endpoint_diagram (z:EndpointQuotient (Γ:=Γ) x s t y₀) :
    ∃ A:Diagram Γ X,
      Diagram.value (endpointData x s t y₀ hs) (endpointSymmetryData x s t y₀ hs)
        (endpointBaker x s t y₀ hs) (endpointRoot x s t y₀) A=z ∧
      Diagram.Realizes A (endpointEvaluation x s t y₀ hxy z).val := by
  obtain ⟨g,rfl⟩ := endpointProject_surjective x s t y₀ z
  exact all_seedRepresented x s t y₀ hs ht hxy htwo g

/-- Completeness of the explicit finite presentation via whole permutations and
decorated common refinement; semantic injectivity follows from the construction. -/

theorem endpointEvaluation_injective [FaithfulSMul Γ X] :
    Function.Injective (endpointEvaluation x s t y₀ hxy) := by
  apply (injective_iff_map_eq_one _).mpr
  intro z hz
  obtain ⟨A,hv,ha⟩ := endpoint_diagram x s t y₀ hs ht hxy htwo z
  rw [hz] at ha
  have hc := Diagram.value_one_of_realizes_one
    (endpointData x s t y₀ hs) (endpointSymmetryData x s t y₀ hs)
    (endpointBaker x s t y₀ hs) (endpointRoot x s t y₀)
    (endpointGridLaw x s t y₀ hs ht hxy htwo) A ha
  exact hv.symm.trans hc

def endpointEquivalence [FaithfulSMul Γ X] :
    EndpointQuotient (Γ:=Γ) x s t y₀ ≃* group (Γ:=Γ) (X:=X) :=
  MulEquiv.ofBijective (endpointEvaluation x s t y₀ hxy)
    ⟨endpointEvaluation_injective x s t y₀ hs ht hxy htwo,
      endpointEvaluation_surjective x s t y₀ hxy⟩

end Generators
end FiniteAlgebraicEnvelopes.TwistedBrinThompson

end

end OAI
end


