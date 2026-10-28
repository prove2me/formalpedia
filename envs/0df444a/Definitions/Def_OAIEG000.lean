-- Prove2me | Definitions.Def_OAIEG000
-- name    : OAIEG000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-24T23:50:38.792757+00:00
-- url     : https://prove2.me/theorems/f9bb6aaf-8c5a-4af2-8c0a-b0e621d078e9
-- title:
--   Definitions bundle OAIEG000 of the split of OpenAI, A finitely generated counterexample to the Eilenberg–Ganea conjecture
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.EilenbergGanea.source_main`, carved from OpenAI's openai/math development (OpenAI, *A finitely generated counterexample to the Eilenberg–Ganea conjecture*, OpenAI Math Release, September 23, 2026, result family 249, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1080 declarations of OpenAI's Lean: 363 definitions, 13 inductive types or structures, 10 instances and 694 theorems. The definitions and types are `OAI.CubicalChains.Chains`, `OAI.CubicalChains.DescentSystem`, `OAI.CubicalChains.DescentSystem.Valid`, `OAI.CubicalChains.DescentSystem.admissible`, `OAI.CubicalChains.DescentSystem.homotopy`, `OAI.CubicalChains.DescentSystem.homotopyTerm`, `OAI.CubicalChains.DescentSystem.remainder`, `OAI.CubicalChains.HeightFiltration.above`, `OAI.CubicalChains.HeightFiltration.embed`, `OAI.CubicalChains.HeightFiltration.homotopy`, `OAI.CubicalChains.HeightFiltration.homotopyTerm`, `OAI.CubicalChains.HeightFiltration.push`, `OAI.CubicalChains.HeightFiltration.total`, `OAI.CubicalChains.LevelExact.crossPart`, `OAI.CubicalChains.LevelExact.crossing`, `OAI.CubicalChains.LevelExact.levelBoundary`, `OAI.CubicalChains.LevelExact.minus`, `OAI.CubicalChains.LevelExact.plus`, `OAI.CubicalChains.LevelExact.select`, `OAI.CubicalChains.Reflection.below`, `OAI.CubicalChains.Reflection.letters`, `OAI.CubicalChains.Reflection.mirror`, `OAI.CubicalChains.Reflection.relabel`, `OAI.CubicalChains.Removed`, `OAI.CubicalChains.Reorientation.Signed`, `OAI.CubicalChains.Reorientation.normalTerm`, `OAI.CubicalChains.Reorientation.normalize`, `OAI.CubicalChains.Reorientation.origin`, `OAI.CubicalChains.Reorientation.sign`, `OAI.CubicalChains.Reorientation.step`, `OAI.CubicalChains.boundary`, `OAI.CubicalChains.boundaryTerm`, `OAI.CubicalChains.cone`, `OAI.CubicalChains.coneTerm`, `OAI.CubicalChains.front`, `OAI.CubicalChains.lower`, `OAI.CubicalChains.lowerTerm`, `OAI.CubicalChains.shift`, `OAI.CubicalChains.upper`, `OAI.CubicalChains.upperTerm` and 336 more.
--
--   **Sources.** They come from these modules of lean/OAI/Topology/EilenbergGanea, lean/OAI/AlgebraicTopology, lean/OAI/GroupTheory, in whole or in part: `AffineTransport`, `CWComplex_CellularPaths`, `CWComplex_Collar`, `CWComplex_Cover`, `CubicalCover`, `Cubical_ArtinChains`, `Cubical_Chains`, `Cubical_Descending`, `Cubical_HeightChains`, `Cubical_PathChains`, `Cubical_Realization`, `Cubical_Singular`, `LevelBasis`, `PresentationComparison`, `RightAngledArtin_Basic`, `RightAngledArtin_CubeDescents`, `RightAngledArtin_ResidualFiniteness`, `RightAngledArtin_TraceWords`, `Simplicial_Chains`, `SmallHolonomy`, `UnitaryWords`, `WordEquations`.
--
--   **Imports.** It imports the published bundle `Def_EilenbergGanea`.
--
--   **Imported by** (directly, in this split): the bundles `OAIEG011`, `OAIEG018`, `OAIEG031`, `OAIEG032` and `OAIEG034`; the proof of `OAI.EilenbergGanea.source_residuallyFinite`.
-- source:
--   OpenAI, A finitely generated counterexample to the Eilenberg–Ganea conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 249; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-finitely-generated-counterexample-to-the-Eilenberg-Ganea-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Topology/EilenbergGanea, lean/OAI/AlgebraicTopology, lean/OAI/GroupTheory at commit adc7f12

import Mathlib
import Definitions.Def_EilenbergGanea

section
-- module Solutions.OAIEG.Compat
namespace OAI

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

end OAI
end

section
-- module Solutions.OAIEG.RightAngledArtin_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set

namespace EilenbergGanea


section FiniteGeneration
variable {V : Type*} (L : SimpleGraph V)

abbrev artinGenerator (v : V) : ArtinGroup L := PresentedGroup.of v

@[simp] theorem height_generator (v : V) :
    height L (artinGenerator L v) = Multiplicative.ofAdd (1 : ℤ) := by
  simp [height, artinGenerator]

theorem adjacent_generators_commute {v w : V} (h : L.Adj v w) :
    Commute (artinGenerator L v) (artinGenerator L w) := by
  have he := PresentedGroup.one_of_mem (rels := artinRelations L)
    (x := FreeGroup.of v * FreeGroup.of w * (FreeGroup.of v)⁻¹ * (FreeGroup.of w)⁻¹)
    ⟨v, w, h, rfl⟩
  simp only [map_mul, map_inv] at he
  change artinGenerator L v * artinGenerator L w =
    artinGenerator L w * artinGenerator L v
  apply mul_inv_eq_one.mp
  simpa only [artinGenerator, PresentedGroup.of, mul_inv_rev, mul_assoc] using he

end FiniteGeneration

end EilenbergGanea

end

end OAI
end

section
-- module Solutions.OAIEG.RightAngledArtin_ResidualFiniteness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set

namespace EilenbergGanea
universe u
/-! Finite permutation separation for free groups. -/

section ArtinUniversal

variable {V W K : Type*} [Group K] (L : SimpleGraph V)

/-- Universal property in commuting-generator form. -/
def artinLift (f : V → K) (hf : ∀ v w, L.Adj v w → Commute (f v) (f w)) :
    ArtinGroup L →* K :=
  PresentedGroup.toGroup (by
    rintro _ ⟨v, w, hvw, rfl⟩
    simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
    rw [(hf v w hvw).eq]
    group)

@[simp] theorem artinLift_generator (f : V → K)
    (hf : ∀ v w, L.Adj v w → Commute (f v) (f w)) (v : V) :
    artinLift L f hf (artinGenerator L v) = f v := by
  exact PresentedGroup.toGroup.of _

/-- Renaming vertices along a graph isomorphism gives the expected group map. -/
def artinMap (M : SimpleGraph W) (f : V → W)
    (hf : ∀ v w, L.Adj v w → M.Adj (f v) (f w)) : ArtinGroup L →* ArtinGroup M :=
  artinLift L (fun v => artinGenerator M (f v))
    (fun v w h => adjacent_generators_commute M (hf v w h))

@[simp] theorem artinMap_generator (M : SimpleGraph W) (f : V → W)
    (hf : ∀ v w, L.Adj v w → M.Adj (f v) (f w)) (v : V) :
    artinMap L M f hf (artinGenerator L v) = artinGenerator M (f v) := by
  exact artinLift_generator _ _ _ _

end ArtinUniversal

section ArtinOption

variable {V : Type*} (L : SimpleGraph (Option V))

abbrev deletedGraph := L.comap Option.some
abbrev deletedGroup := ArtinGroup (deletedGraph L)

local instance instDecidableRelOptionAdj_solutions : DecidableRel L.Adj := Classical.decRel _

def linkRetraction : deletedGroup L →* deletedGroup L :=
  artinLift (deletedGraph L)
    (fun v => if L.Adj none (some v) then artinGenerator (deletedGraph L) v else 1) (by
    classical
    intro v w hvw
    split_ifs <;> first
    | exact adjacent_generators_commute (deletedGraph L) hvw
    | exact Commute.one_left _
    | exact Commute.one_right _)

@[simp] theorem linkRetraction_generator (v : V) :
    linkRetraction L (artinGenerator (deletedGraph L) v) =
      if L.Adj none (some v) then artinGenerator (deletedGraph L) v else 1 := by
  exact artinLift_generator _ _ _ _

end ArtinOption


end EilenbergGanea

end

end OAI
end

section
-- module Solutions.OAIEG.RightAngledArtin_TraceWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set

namespace EilenbergGanea
/-! Signed trace normal forms and slowly varying barycentric directions. -/

namespace TraceWords

variable {V : Type*} (L : SimpleGraph V)
abbrev Letter (V : Type*) := V × Bool
abbrev Word (V : Type*) := List (Letter V)

def invLetter (x : Letter V) : Letter V := (x.1, !x.2)
@[simp] theorem invLetter_invLetter (x : Letter V) : invLetter (invLetter x) = x := by
  cases x; simp [invLetter]

def Independent (x y : Letter V) : Prop := L.Adj x.1 y.1
@[simp] theorem independent_inv_left (x y : Letter V) :
    Independent L (invLetter x) y ↔ Independent L x y := Iff.rfl
@[simp] theorem independent_inv_right (x y : Letter V) :
    Independent L x (invLetter y) ↔ Independent L x y := Iff.rfl
@[simp] theorem independent_self (x : Letter V) : ¬ Independent L x x := fun h => L.irrefl h
theorem Independent.symm {x y : Letter V} (h : Independent L x y) : Independent L y x :=
  L.symm.symm _ _ h

/-- A single exchange of independent neighboring occurrences. -/
inductive Swap : Word V → Word V → Prop
  | head {x y : Letter V} {w : Word V} (h : Independent L x y) :
      Swap (x :: y :: w) (y :: x :: w)
  | cons (x : Letter V) {w w' : Word V} (h : Swap w w') : Swap (x :: w) (x :: w')

variable {L}
theorem Swap.symm {w w' : Word V} (h : Swap L w w') : Swap L w' w := by
  induction h with
  | head h => exact .head h.symm
  | cons x _ ih => exact .cons x ih

theorem Swap.length {w w' : Word V} (h : Swap L w w') : w.length = w'.length := by
  induction h <;> simp_all

variable (L)
abbrev Equivalent := Relation.EqvGen (Swap L)

variable {L}
@[refl] theorem Equivalent.refl (w : Word V) : Equivalent L w w := Relation.EqvGen.refl _
@[symm] theorem Equivalent.symm {w w' : Word V} (h : Equivalent L w w') :
    Equivalent L w' w := Relation.EqvGen.symm _ _ h
@[trans] theorem Equivalent.trans {w w' w'' : Word V} (h : Equivalent L w w')
    (h' : Equivalent L w' w'') : Equivalent L w w'' := Relation.EqvGen.trans _ _ _ h h'

theorem Equivalent.cons (x : Letter V) {w w' : Word V} (h : Equivalent L w w') :
    Equivalent L (x :: w) (x :: w') := by
  induction h with
  | rel _ _ h => exact .rel _ _ (.cons x h)
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm ih
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

theorem Equivalent.length {w w' : Word V} (h : Equivalent L w w') : w.length = w'.length := by
  induction h with
  | rel _ _ h => exact h.length
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

variable (L)
/-- Remove an occurrence accessible from the left through independent letters.
This retains the actual other occurrences, not merely their group value. -/
inductive Extract (x : Letter V) : Word V → Word V → Prop
  | head (w : Word V) : Extract x (x :: w) w
  | cons {y : Letter V} {w w' : Word V} (h : Independent L x y)
      (e : Extract x w w') : Extract x (y :: w) (y :: w')

variable {L}
theorem Extract.length {x : Letter V} {w w' : Word V} (h : Extract L x w w') :
    w'.length + 1 = w.length := by
  induction h <;> simp_all

theorem Extract.equivalent {x : Letter V} {w w' : Word V} (h : Extract L x w w') :
    Equivalent L w (x :: w') := by
  induction h with
  | head => exact .refl _
  | @cons y w w' h e ih =>
      exact (ih.cons y).trans (.rel _ _ (.head h.symm))

theorem Extract.unique {x : Letter V} {w v v' : Word V}
    (h : Extract L x w v) (h' : Extract L x w v') : v = v' := by
  induction h generalizing v' with
  | head w =>
      cases h' with
      | head => rfl
      | cons hi _ => exact False.elim (independent_self L x hi)
  | @cons y w v hi he ih =>
      cases h' with
      | head => exact False.elim (independent_self L x hi)
      | cons _ he' => exact congrArg (List.cons y) (ih he')

/-- Independent accessible occurrences may be removed in either order. -/
theorem Extract.diamond {x y : Letter V} {w v u : Word V}
    (hxy : Independent L x y) (hx : Extract L x w v) (hy : Extract L y w u) :
    ∃ t, Extract L y v t ∧ Extract L x u t := by
  induction hx generalizing u with
  | head w =>
      cases hy with
      | head => exact False.elim (independent_self L x hxy)
      | cons _ he => exact ⟨_,he,.head _⟩
  | @cons a w v hxa hx ih =>
      cases hy with
      | head => exact ⟨_,.head _,hx⟩
      | cons hya hy =>
          obtain ⟨t,ht,h't⟩ := ih hy
          exact ⟨a :: t,.cons hya ht,.cons hxa h't⟩

/-- An adjacent commutation does not destroy accessible occurrences. -/
theorem Extract.swap {x : Letter V} {w w' v : Word V}
    (hs : Swap L w w') (he : Extract L x w v) :
    ∃ v', Extract L x w' v' ∧ Equivalent L v v' := by
  induction hs generalizing v with
  | @head a b w hab =>
      cases he with
      | head => exact ⟨_,.cons hab (.head _),.refl _⟩
      | cons hxa he =>
          cases he with
          | head => exact ⟨_,.head _,.refl _⟩
          | cons hxb he =>
              exact ⟨_,.cons hxb (.cons hxa he),.rel _ _ (.head hab)⟩
  | @cons a w w' hs ih =>
      cases he with
      | head => exact ⟨_,.head _,.rel _ _ hs⟩
      | cons hxa he =>
          obtain ⟨v',he',hv'⟩ := ih he
          exact ⟨_,.cons hxa he',hv'.cons a⟩

variable (L)
/-- Delete an inverse pair after commuting its endpoints together. -/
inductive Step : Word V → Word V → Prop
  | head {x : Letter V} {w w' : Word V} (h : Extract L (invLetter x) w w') :
      Step (x :: w) w'
  | cons (x : Letter V) {w w' : Word V} (h : Step w w') : Step (x :: w) (x :: w')

variable {L}
theorem Step.length {w w' : Word V} (h : Step L w w') : w'.length + 2 = w.length := by
  induction h with
  | head h => have := h.length; simp only [List.length_cons]; omega
  | cons _ _ ih => simp_all

/-- Lift a cancellation across one independent exchange, tracking its output. -/
theorem Step.swap {w w' v : Word V} (hs : Swap L w w') (he : Step L w v) :
    ∃ v', Step L w' v' ∧ Equivalent L v v' := by
  induction hs generalizing v with
  | @head a b w hab =>
      cases he with
      | head he =>
          cases he with
          | head => exact False.elim (independent_self L a hab)
          | cons _ he => exact ⟨_,.cons b (.head he),.refl _⟩
      | cons _ he =>
          cases he with
          | head he => exact ⟨_,.head (.cons hab.symm he),.refl _⟩
          | cons _ he => exact ⟨_,.cons b (.cons a he),.rel _ _ (.head hab)⟩
  | @cons a w w' hs ih =>
      cases he with
      | head he =>
          obtain ⟨v',he',hv'⟩ := he.swap hs
          exact ⟨_,.head he',hv'⟩
      | cons _ he =>
          obtain ⟨v',he',hv'⟩ := ih he
          exact ⟨_,.cons a he',hv'.cons a⟩

/-- The only overlapping cancellation shares the accessible occurrence.
Its two outcomes differ only by exchanges; disjoint deletions commute. -/
theorem Extract.step {x : Letter V} {w v u : Word V}
    (hx : Extract L x w v) (hs : Step L w u) :
    Equivalent L v (invLetter x :: u) ∨
      ∃ t, Step L v t ∧ Extract L x u t := by
  induction hx generalizing u with
  | head w =>
      cases hs with
      | head he => exact Or.inl he.equivalent
      | cons _ hs => exact Or.inr ⟨_,hs,.head _⟩
  | @cons a w v hxa hx ih =>
      cases hs with
      | head he =>
          obtain ⟨t,ht,h't⟩ := hx.diamond (show Independent L x (invLetter a) from hxa) he
          exact Or.inr ⟨t,.head ht,h't⟩
      | cons _ hs =>
          rcases ih hs with h | ⟨t,ht,h't⟩
          · exact Or.inl ((h.cons a).trans (.rel _ _ (.head hxa.symm)))
          · exact Or.inr ⟨a :: t,.cons a ht,.cons hxa h't⟩

/-- Local confluence modulo independent exchanges. -/
theorem Step.diamond {w v u : Word V} (hv : Step L w v) (hu : Step L w u) :
    Equivalent L v u ∨ ∃ t t', Step L v t ∧ Step L u t' ∧ Equivalent L t t' := by
  induction hv generalizing u with
  | @head x w v he =>
      cases hu with
      | head he' => exact Or.inl (he.unique he' ▸ .refl _)
      | cons _ hu =>
          rcases he.step hu with h | ⟨t,ht,h't⟩
          · exact Or.inl (by simpa using h)
          · exact Or.inr ⟨t,t,ht,.head h't,.refl _⟩
  | @cons x w v hv ih =>
      cases hu with
      | head he =>
          rcases he.step hv with h | ⟨t,ht,h't⟩
          · exact Or.inl (by simpa using h.symm)
          · exact Or.inr ⟨t,t,.head h't,ht,.refl _⟩
      | cons _ hu =>
          rcases ih hu with h | ⟨t,t',ht,h't,htt'⟩
          · exact Or.inl (h.cons x)
          · exact Or.inr ⟨x :: t,x :: t',.cons x ht,.cons x h't,htt'.cons x⟩

instance instSymmWordSwap : Std.Symm (Swap L) where
  symm _ _ h := h.symm

theorem Equivalent.step {w w' v : Word V} (hs : Equivalent L w w') (he : Step L w v) :
    ∃ v', Step L w' v' ∧ Equivalent L v v' := by
  have hh : Relation.ReflTransGen (Swap L) w w' := by
    rwa [← Relation.EqvGen.eqvGen_eq_reflTransGen]
  clear hs
  induction hh with
  | refl => exact ⟨_,he,.refl _⟩
  | tail _ hs ih =>
      obtain ⟨v',he',hv'⟩ := ih
      obtain ⟨v'',he'',hv''⟩ := he'.swap hs
      exact ⟨_,he'',hv'.trans hv''⟩

variable (L)
def traceSetoid : Setoid (Word V) where
  r := Equivalent L
  iseqv := ⟨Equivalent.refl,Equivalent.symm,Equivalent.trans⟩

abbrev Trace := Quotient (traceSetoid L)
def ofWord (w : Word V) : Trace L := Quotient.mk _ w

def traceLength : Trace L → ℕ := Quotient.lift List.length (fun _ _ h => h.length)
@[simp] theorem traceLength_ofWord (w : Word V) : traceLength L (ofWord L w) = w.length := rfl

@[simp] theorem ofWord_eq {w v : Word V} : ofWord L w = ofWord L v ↔ Equivalent L w v :=
  Quotient.eq

/-- Reduction of traces, not a choice of ordered representative. -/
def ReductionStep (t t' : Trace L) : Prop :=
  ∃ w v, Step L w v ∧ ofWord L w = t ∧ ofWord L v = t'

variable {L}
theorem Step.trace {w v : Word V} (h : Step L w v) :
    ReductionStep L (ofWord L w) (ofWord L v) := ⟨w,v,h,rfl,rfl⟩

theorem ReductionStep.representative {w : Word V} {t : Trace L}
    (h : ReductionStep L (ofWord L w) t) :
    ∃ v, Step L w v ∧ ofWord L v = t := by
  obtain ⟨a,b,hab,ha,hb⟩ := h
  obtain ⟨v,hv,hbv⟩ := ((ofWord_eq L).mp ha).step hab
  exact ⟨v,hv,((ofWord_eq L).mpr hbv).symm.trans hb⟩

theorem ReductionStep.length {t t' : Trace L} (h : ReductionStep L t t') :
    traceLength L t' + 2 = traceLength L t := by
  obtain ⟨w,v,h,rfl,rfl⟩ := h
  exact h.length

theorem ReductionStep.diamond {t t' t'' : Trace L}
    (h : ReductionStep L t t') (h' : ReductionStep L t t'') :
    t' = t'' ∨ ∃ u, ReductionStep L t' u ∧ ReductionStep L t'' u := by
  induction t using Quotient.inductionOn with
  | h w =>
      obtain ⟨v,hv,rfl⟩ := h.representative
      obtain ⟨u,hu,rfl⟩ := h'.representative
      rcases hv.diamond hu with he | ⟨a,b,ha,hb,hab⟩
      · exact Or.inl ((ofWord_eq L).mpr he)
      · refine Or.inr ⟨ofWord L a,ha.trace,?_⟩
        rw [(ofWord_eq L).mpr hab]
        exact hb.trace

variable (L)
abbrev Reduction := Relation.ReflTransGen (ReductionStep L)
def Reduced (t : Trace L) : Prop := ∀ t', ¬ ReductionStep L t t'

variable {L}

theorem Reduction.confluence {t t' t'' : Trace L}
    (h : Reduction L t t') (h' : Reduction L t t'') :
    ∃ u, Reduction L t' u ∧ Reduction L t'' u := by
  apply Relation.church_rosser (r := ReductionStep L) _ h h'
  intro _ _ _ ha hb
  rcases ha.diamond hb with rfl | ⟨u,hu,hu'⟩
  · exact ⟨_,.refl,.refl⟩
  · exact ⟨u,.single hu,.single hu'⟩

theorem Reduced.reduction_eq {t t' : Trace L} (h : Reduced L t) (hr : Reduction L t t') :
    t = t' := by
  rcases hr.cases_head with he | ⟨u,hu,_⟩
  · exact he
  · exact False.elim (h u hu)

theorem exists_reduced (t : Trace L) : ∃ t', Reduction L t t' ∧ Reduced L t' := by
  classical
  induction hn : traceLength L t using Nat.strong_induction_on generalizing t with
  | h n ih =>
      by_cases ht : Reduced L t
      · exact ⟨t,.refl,ht⟩
      · obtain ⟨u,hu⟩ : ∃ u, ReductionStep L t u := by simpa [Reduced] using ht
        have hl := hu.length
        obtain ⟨v,hv,hv'⟩ := ih (traceLength L u) (by omega) u rfl
        exact ⟨v,hv.head hu,hv'⟩

theorem reduced_unique {t u v : Trace L} (hu : Reduction L t u) (hv : Reduction L t v)
    (hru : Reduced L u) (hrv : Reduced L v) : u = v := by
  obtain ⟨a,ha,h'a⟩ := hu.confluence hv
  exact (hru.reduction_eq ha).trans (hrv.reduction_eq h'a).symm

variable (L)
def normalTrace (t : Trace L) : Trace L := (exists_reduced t).choose

theorem normalTrace_reduction (t : Trace L) : Reduction L t (normalTrace L t) :=
  (exists_reduced t).choose_spec.1

theorem normalTrace_reduced (t : Trace L) : Reduced L (normalTrace L t) :=
  (exists_reduced t).choose_spec.2

variable {L}
theorem Reduced.normalTrace_eq {t : Trace L} (h : Reduced L t) : normalTrace L t = t :=
  (h.reduction_eq (normalTrace_reduction L t)).symm

theorem Reduction.normalTrace_eq {t u : Trace L} (h : Reduction L t u) :
    normalTrace L t = normalTrace L u :=
  reduced_unique (normalTrace_reduction L t) (h.trans (normalTrace_reduction L u))
    (normalTrace_reduced L t) (normalTrace_reduced L u)

@[simp] theorem normalTrace_idem (t : Trace L) :
    normalTrace L (normalTrace L t) = normalTrace L t :=
  (normalTrace_reduced L t).normalTrace_eq

theorem Swap.append_right {w v : Word V} (h : Swap L w v) (u : Word V) :
    Swap L (w ++ u) (v ++ u) := by
  induction h with
  | head h => exact .head h
  | cons x _ ih => exact .cons x ih

theorem Equivalent.append_right {w v : Word V} (h : Equivalent L w v) (u : Word V) :
    Equivalent L (w ++ u) (v ++ u) := by
  induction h with
  | rel _ _ h => exact .rel _ _ (h.append_right u)
  | refl => exact .refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

theorem Equivalent.append_left {w v : Word V} (h : Equivalent L w v) (u : Word V) :
    Equivalent L (u ++ w) (u ++ v) := by
  induction u with
  | nil => exact h
  | cons a u ih => exact ih.cons a

theorem Extract.append_right {x : Letter V} {w v : Word V}
    (h : Extract L x w v) (u : Word V) : Extract L x (w ++ u) (v ++ u) := by
  induction h with
  | head => exact .head _
  | cons hi _ ih => exact .cons hi ih

theorem Step.append_right {w v : Word V} (h : Step L w v) (u : Word V) :
    Step L (w ++ u) (v ++ u) := by
  induction h with
  | head h => exact .head (h.append_right u)
  | cons x _ ih => exact .cons x ih

theorem Step.append_left {w v : Word V} (h : Step L w v) (u : Word V) :
    Step L (u ++ w) (u ++ v) := by
  induction u with
  | nil => exact h
  | cons a u ih => exact .cons a ih

variable (L)
def appendTrace (t u : Trace L) : Trace L :=
  Quotient.liftOn₂ t u (fun w v => ofWord L (w ++ v)) (by
    intro w v w' v' hw hv
    exact (ofWord_eq L).mpr ((hw.append_right v).trans (hv.append_left w')))

@[simp] theorem appendTrace_ofWord (w v : Word V) :
    appendTrace L (ofWord L w) (ofWord L v) = ofWord L (w ++ v) := rfl

variable {L}
theorem ReductionStep.append_left {t t' : Trace L} (h : ReductionStep L t t') (u : Trace L) :
    ReductionStep L (appendTrace L u t) (appendTrace L u t') := by
  obtain ⟨w,v,h,rfl,rfl⟩ := h
  induction u using Quotient.inductionOn with
  | h a => exact (h.append_left a).trace

theorem ReductionStep.append_right {t t' : Trace L} (h : ReductionStep L t t') (u : Trace L) :
    ReductionStep L (appendTrace L t u) (appendTrace L t' u) := by
  obtain ⟨w,v,h,rfl,rfl⟩ := h
  induction u using Quotient.inductionOn with
  | h a => exact (h.append_right a).trace

theorem Reduction.append_left {t t' : Trace L} (h : Reduction L t t') (u : Trace L) :
    Reduction L (appendTrace L u t) (appendTrace L u t') := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact ih.tail (h.append_left u)

theorem Reduction.append_right {t t' : Trace L} (h : Reduction L t t') (u : Trace L) :
    Reduction L (appendTrace L t u) (appendTrace L t' u) := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact ih.tail (h.append_right u)

theorem normalTrace_append (t u : Trace L) :
    normalTrace L (appendTrace L t u) =
      normalTrace L (appendTrace L (normalTrace L t) (normalTrace L u)) :=
  Reduction.normalTrace_eq (((normalTrace_reduction L t).append_right u).trans
    ((normalTrace_reduction L u).append_left (normalTrace L t)))

variable (L)
/-- Equality of reduced traces is a monoid congruence on signed words. -/
def normalCon : Con (FreeMonoid (Letter V)) where
  r w v := normalTrace L (ofWord L w.toList) = normalTrace L (ofWord L v.toList)
  iseqv := ⟨fun _ => rfl,fun h => h.symm,fun h h' => h.trans h'⟩
  mul' {x y z t} hxy hzt := by
    change normalTrace L (appendTrace L (ofWord L x.toList) (ofWord L z.toList)) =
      normalTrace L (appendTrace L (ofWord L y.toList) (ofWord L t.toList))
    calc
      _ = normalTrace L (appendTrace L (normalTrace L (ofWord L x.toList))
        (normalTrace L (ofWord L z.toList))) := normalTrace_append _ _
      _ = normalTrace L (appendTrace L (normalTrace L (ofWord L y.toList))
        (normalTrace L (ofWord L t.toList))) := by rw [hxy,hzt]
      _ = _ := (normalTrace_append _ _).symm

abbrev WordGroup := (normalCon L).Quotient

def groupWord (w : Word V) : WordGroup L := (normalCon L).mk' (FreeMonoid.ofList w)

@[simp] theorem groupWord_nil : groupWord L [] = 1 := rfl
@[simp] theorem groupWord_append (w v : Word V) : groupWord L (w ++ v) =
    groupWord L w * groupWord L v := rfl

@[simp] theorem groupWord_eq {w v : Word V} : groupWord L w = groupWord L v ↔
    normalTrace L (ofWord L w) = normalTrace L (ofWord L v) := Quotient.eq

variable {L}
theorem Step.groupWord {w v : Word V} (h : Step L w v) : groupWord L w = groupWord L v :=
  (groupWord_eq L).mpr (Reduction.normalTrace_eq (Relation.ReflTransGen.single h.trace))

theorem Swap.groupWord {w v : Word V} (h : Swap L w v) : groupWord L w = groupWord L v := by
  apply (groupWord_eq L).mpr
  rw [(ofWord_eq L).mpr (.rel _ _ h)]

theorem isUnit_groupWord_singleton (x : Letter V) : IsUnit (groupWord L [x]) := by
  refine ⟨⟨groupWord L [x],groupWord L [invLetter x],?_,?_⟩,rfl⟩
  · change groupWord L [x,invLetter x] = groupWord L []
    exact (Step.head (.head [])).groupWord
  · change groupWord L [invLetter x,x] = groupWord L []
    exact (Step.head (by simpa using (Extract.head (L := L) (x := invLetter (invLetter x)) []))).groupWord

theorem isUnit_groupWord (w : Word V) : IsUnit (groupWord L w) := by
  induction w with
  | nil => exact isUnit_one
  | cons x w ih =>
      change IsUnit (groupWord L [x] * groupWord L w)
      exact (isUnit_groupWord_singleton x).mul ih

variable (L)
noncomputable instance wordGroupGroup : Group (WordGroup L) := groupOfIsUnit (by
  intro x
  induction x using Con.induction_on with
  | H w => exact isUnit_groupWord w.toList)

@[simp] theorem groupWord_inv_singleton (x : Letter V) :
    groupWord L [invLetter x] = (groupWord L [x])⁻¹ := by
  apply mul_left_cancel (a := groupWord L [x])
  rw [mul_inv_cancel,← groupWord_append]
  exact (Step.head (.head [])).groupWord

section Evaluation
variable {K : Type*} [Group K] (f : V → K)

def letterValue (x : Letter V) : K := if x.2 then f x.1 else (f x.1)⁻¹
@[simp] theorem letterValue_positive (v : V) : letterValue f (v,true) = f v := rfl
@[simp] theorem letterValue_negative (v : V) : letterValue f (v,false) = (f v)⁻¹ := rfl
@[simp] theorem letterValue_inverse (x : Letter V) : letterValue f (invLetter x) =
    (letterValue f x)⁻¹ := by
  rcases x with ⟨x,b⟩; cases b <;> simp [letterValue,invLetter]

def wordEval (w : Word V) : K := (w.map (letterValue f)).prod
@[simp] theorem wordEval_nil : wordEval f [] = 1 := rfl
@[simp] theorem wordEval_cons (x : Letter V) (w : Word V) :
    wordEval f (x :: w) = letterValue f x * wordEval f w := rfl
@[simp] theorem wordEval_append (w v : Word V) :
    wordEval f (w ++ v) = wordEval f w * wordEval f v := by simp [wordEval]
@[simp] theorem wordEval_singleton (x : Letter V) : wordEval f [x] = letterValue f x := by
  simp

variable {L f}
theorem letterValue_commute (hf : ∀ x y, L.Adj x y → Commute (f x) (f y))
    {x y : Letter V} (h : Independent L x y) : Commute (letterValue f x) (letterValue f y) := by
  rcases x with ⟨x,b⟩; rcases y with ⟨y,c⟩
  have hh := hf x y h
  cases b <;> cases c
  · exact hh.inv_left.inv_right
  · exact hh.inv_left
  · exact hh.inv_right
  · exact hh

theorem Swap.wordEval (hf : ∀ x y, L.Adj x y → Commute (f x) (f y))
    {w v : Word V} (h : Swap L w v) : wordEval f w = wordEval f v := by
  induction h with
  | head h => simp only [wordEval_cons,← mul_assoc,(letterValue_commute hf h).eq]
  | cons _ _ ih => simp only [wordEval_cons,ih]

theorem Equivalent.wordEval (hf : ∀ x y, L.Adj x y → Commute (f x) (f y))
    {w v : Word V} (h : Equivalent L w v) : wordEval f w = wordEval f v := by
  induction h with
  | rel _ _ h => exact h.wordEval hf
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

theorem Step.wordEval (hf : ∀ x y, L.Adj x y → Commute (f x) (f y))
    {w v : Word V} (h : Step L w v) : wordEval f w = wordEval f v := by
  induction h with
  | head h =>
      rw [wordEval_cons,h.equivalent.wordEval hf,wordEval_cons,letterValue_inverse,
        mul_inv_cancel_left]
  | cons _ _ ih => simp only [wordEval_cons,ih]

variable (L f)
def traceEval (hf : ∀ x y, L.Adj x y → Commute (f x) (f y)) : Trace L → K :=
  Quotient.lift (wordEval f) (fun _ _ h => h.wordEval hf)

@[simp] theorem traceEval_ofWord (hf : ∀ x y, L.Adj x y → Commute (f x) (f y))
    (w : Word V) : traceEval L f hf (ofWord L w) = wordEval f w := rfl

variable {L f}
theorem ReductionStep.traceEval (hf : ∀ x y, L.Adj x y → Commute (f x) (f y))
    {t u : Trace L} (h : ReductionStep L t u) : traceEval L f hf t = traceEval L f hf u := by
  obtain ⟨w,v,h,rfl,rfl⟩ := h
  exact h.wordEval hf

theorem Reduction.traceEval (hf : ∀ x y, L.Adj x y → Commute (f x) (f y))
    {t u : Trace L} (h : Reduction L t u) : traceEval L f hf t = traceEval L f hf u := by
  induction h with
  | refl => rfl
  | tail _ h ih => exact ih.trans (h.traceEval hf)

theorem traceEval_normalTrace (hf : ∀ x y, L.Adj x y → Commute (f x) (f y))
    (t : Trace L) : traceEval L f hf (normalTrace L t) = traceEval L f hf t :=
  ((normalTrace_reduction L t).traceEval hf).symm

variable (L f)
def groupEval (hf : ∀ x y, L.Adj x y → Commute (f x) (f y)) : WordGroup L →* K :=
  (normalCon L).lift (FreeMonoid.lift (letterValue f)) (by
    intro w v h
    change normalTrace L (ofWord L w.toList) = normalTrace L (ofWord L v.toList) at h
    have hh := congrArg (traceEval L f hf) h
    change FreeMonoid.lift (letterValue f) w = FreeMonoid.lift (letterValue f) v
    simpa only [FreeMonoid.lift_apply,traceEval_normalTrace,traceEval_ofWord,wordEval] using hh)

@[simp] theorem groupEval_word (hf : ∀ x y, L.Adj x y → Commute (f x) (f y))
    (w : Word V) : groupEval L f hf (groupWord L w) = wordEval f w := by
  change FreeMonoid.lift (letterValue f) (FreeMonoid.ofList w) = wordEval f w
  exact FreeMonoid.lift_ofList _ _

end Evaluation

/-- The kernel presentation is compared with the signed trace group, not with
an assumed normal-form model. -/
def toArtin : WordGroup L →* ArtinGroup L :=
  groupEval L (artinGenerator L) (fun _ _ h => adjacent_generators_commute L h)

theorem groupWord_commute {v w : V} (h : L.Adj v w) :
    Commute (groupWord L [(v,true)]) (groupWord L [(w,true)]) := by
  change groupWord L [(v,true),(w,true)] = groupWord L [(w,true),(v,true)]
  exact (Swap.head (L := L) (x := (v,true)) (y := (w,true)) (w := []) h).groupWord

def ofArtin : ArtinGroup L →* WordGroup L :=
  artinLift L (fun v => groupWord L [(v,true)]) (fun _ _ h => groupWord_commute L h)

@[simp] theorem ofArtin_generator (v : V) : ofArtin L (artinGenerator L v) =
    groupWord L [(v,true)] := artinLift_generator _ _ _ _

@[simp] theorem toArtin_word (w : Word V) :
    toArtin L (groupWord L w) = wordEval (artinGenerator L) w := groupEval_word _ _ _ _

@[simp] theorem ofArtin_letter (x : Letter V) :
    ofArtin L (letterValue (artinGenerator L) x) = groupWord L [x] := by
  rcases x with ⟨x,b⟩
  cases b
  · change ofArtin L (artinGenerator L x)⁻¹ = groupWord L [(x,false)]
    rw [map_inv,ofArtin_generator]
    exact (groupWord_inv_singleton L (x,true)).symm
  · exact ofArtin_generator L x

theorem ofArtin_word (w : Word V) :
    ofArtin L (wordEval (artinGenerator L) w) = groupWord L w := by
  induction w with
  | nil => exact (ofArtin L).map_one
  | cons x w ih =>
      rw [wordEval_cons,map_mul,ofArtin_letter,ih]
      rfl

theorem toArtin_ofArtin (g : ArtinGroup L) : toArtin L (ofArtin L g) = g := by
  have he : (toArtin L).comp (ofArtin L) = MonoidHom.id _ := by
    apply PresentedGroup.ext
    intro v
    change toArtin L (ofArtin L (artinGenerator L v)) = artinGenerator L v
    rw [ofArtin_generator,toArtin_word,wordEval_singleton,letterValue_positive]
  exact DFunLike.congr_fun he g

/-- Two words have the same value in the actual Artin group exactly when they
have the same reduced trace. -/
theorem artin_word_eq_iff (w v : Word V) :
    wordEval (artinGenerator L) w = wordEval (artinGenerator L) v ↔
      normalTrace L (ofWord L w) = normalTrace L (ofWord L v) := by
  rw [← groupWord_eq]
  constructor
  · intro h
    simpa only [ofArtin_word] using congrArg (ofArtin L) h
  · intro h
    simpa only [toArtin_word] using congrArg (toArtin L) h


/-! The occurrence-level normal form is now used to control an actual generator
step. No geometric normal-form or direction-vector assertion is assumed. -/

variable {L}

theorem Reduced.of_equivalent {w v : Word V} (h : Reduced L (ofWord L w))
    (he : Equivalent L w v) : Reduced L (ofWord L v) := by
  rwa [← (ofWord_eq L).mpr he]

theorem Reduced.of_append_left {w v : Word V} (h : Reduced L (ofWord L (w ++ v))) :
    Reduced L (ofWord L v) := by
  intro t ht
  exact h _ (ht.append_left (ofWord L w))

theorem Reduced.of_append_right {w v : Word V} (h : Reduced L (ofWord L (w ++ v))) :
    Reduced L (ofWord L w) := by
  intro t ht
  exact h _ (ht.append_right (ofWord L v))

theorem Reduced.tail {x : Letter V} {w : Word V} (h : Reduced L (ofWord L (x :: w))) :
    Reduced L (ofWord L w) :=
  Reduced.of_append_left (w := [x]) h

theorem Extract.append_singleton {x y : Letter V} {w v : Word V}
    (h : Extract L x (w ++ [y]) v) :
    (∃ v', Extract L x w v' ∧ v = v' ++ [y]) ∨
      (x = y ∧ v = w ∧ ∀ a ∈ w, Independent L x a) := by
  induction w generalizing v with
  | nil =>
      cases h with
      | head => exact Or.inr ⟨rfl,rfl,by simp⟩
      | cons _ he => cases he
  | cons a w ih =>
      cases h with
      | head => exact Or.inl ⟨w,.head _,rfl⟩
      | cons ha he =>
          rcases ih he with ⟨v',hv',rfl⟩ | ⟨hxy,rfl,hw⟩
          · exact Or.inl ⟨a :: v',.cons ha hv',rfl⟩
          · refine Or.inr ⟨hxy,rfl,?_⟩
            intro b hb
            rcases List.mem_cons.mp hb with rfl | hb
            · exact ha
            · exact hw b hb

theorem Extract.last {x : Letter V} {w : Word V}
    (h : ∀ a ∈ w, Independent L x a) : Extract L x (w ++ [x]) w := by
  induction w with
  | nil => exact .head []
  | cons a w ih =>
      exact .cons (h a (by simp)) (ih (fun b hb => h b (by simp [hb])))

/-- A cancellation in a reduced word with one appended occurrence must cancel
that new occurrence. The old inverse occurrence was maximal: it can be moved
all the way to the right by independent exchanges. -/
theorem Step.append_reduced {x : Letter V} {w v : Word V}
    (hw : Reduced L (ofWord L w)) (h : Step L (w ++ [x]) v) :
    Equivalent L w (v ++ [invLetter x]) := by
  induction w generalizing v with
  | nil =>
      cases h with
      | head he => cases he
      | cons _ he => cases he
  | cons a w ih =>
      cases h with
      | head he =>
          rcases he.append_singleton with ⟨v',hv',_⟩ | ⟨hax,hv,hi⟩
          · exact False.elim (hw _ (Step.head hv').trace)
          · subst v
            have hia : ∀ b ∈ w, Independent L a b := hi
            have ha : a = invLetter x := by rw [← hax,invLetter_invLetter]
            rw [← ha]
            exact (Extract.last hia).equivalent.symm
      | cons _ he => exact (ih hw.tail he).cons a

/-- On an actual reduced trace, a generator step either adds a maximal
occurrence or removes a maximal inverse occurrence, with no further reduction. -/
theorem reduced_append_alternative {x : Letter V} {w : Word V}
    (hw : Reduced L (ofWord L w)) :
    Reduced L (ofWord L (w ++ [x])) ∨
      ∃ v, Reduced L (ofWord L v) ∧ Equivalent L w (v ++ [invLetter x]) ∧
        normalTrace L (ofWord L (w ++ [x])) = ofWord L v := by
  classical
  by_cases h : Reduced L (ofWord L (w ++ [x]))
  · exact Or.inl h
  · obtain ⟨t,ht⟩ : ∃ t, ReductionStep L (ofWord L (w ++ [x])) t := by
      simpa only [Reduced,not_forall,not_not] using h
    obtain ⟨v,hv,rfl⟩ := ht.representative
    have he := hv.append_reduced hw
    have hr : Reduced L (ofWord L v) := (hw.of_equivalent he).of_append_right
    exact Or.inr ⟨v,hr,he,(Reduction.normalTrace_eq (Relation.ReflTransGen.single hv.trace)).trans
      hr.normalTrace_eq⟩


section RootCounts
variable [LinearOrder V]
variable (L)

/-- The previously encountered minimal ancestral directions of letters
which are dependent on the next direction. Taking the minimum recursively
computes the first minimal ancestor in the occurrence poset. -/
def predecessorRoots (s : Multiset (V × V)) (v : V) : Finset V := by
  classical
  exact ((s.filter (fun p => ¬ L.Adj p.1 v)).map Prod.snd).toFinset

def nextRoot (s : Multiset (V × V)) (v : V) : V :=
  if h : (predecessorRoots L s v).Nonempty then (predecessorRoots L s v).min' h else v

def rootInsert (s : Multiset (V × V)) (v : V) : Multiset (V × V) :=
  (v,nextRoot L s v) ::ₘ s

/-- Each pair records an occurrence's direction and its assigned minimal
ancestral direction. Signs do not change the occurrence dependency relation. -/
def rootScan (s : Multiset (V × V)) (w : Word V) : Multiset (V × V) :=
  w.foldl (fun s x => rootInsert L s x.1) s

@[simp] theorem rootScan_nil (s : Multiset (V × V)) : rootScan L s [] = s := rfl
@[simp] theorem rootScan_cons (s : Multiset (V × V)) (x : Letter V) (w : Word V) :
    rootScan L s (x :: w) = rootScan L (rootInsert L s x.1) w := rfl

variable {L}

theorem predecessorRoots_cons_independent (s : Multiset (V × V)) {a v : V}
    (r : V) (h : L.Adj a v) :
    predecessorRoots L ((a,r) ::ₘ s) v = predecessorRoots L s v := by
  classical
  simp [predecessorRoots,h]

theorem nextRoot_cons_independent (s : Multiset (V × V)) {a v : V}
    (r : V) (h : L.Adj a v) :
    nextRoot L ((a,r) ::ₘ s) v = nextRoot L s v := by
  simp only [nextRoot,predecessorRoots_cons_independent s r h]

theorem rootInsert_commute (s : Multiset (V × V)) {v w : V} (h : L.Adj v w) :
    rootInsert L (rootInsert L s v) w = rootInsert L (rootInsert L s w) v := by
  simp only [rootInsert,nextRoot_cons_independent s _ h,
    nextRoot_cons_independent s _ (L.symm.symm _ _ h)]
  exact Multiset.cons_swap _ _ _

theorem Swap.rootScan {w v : Word V} (h : Swap L w v) (s : Multiset (V × V)) :
    rootScan L s w = rootScan L s v := by
  induction h generalizing s with
  | head h => simp only [rootScan_cons,rootInsert_commute s h]
  | cons _ _ ih => exact ih _

theorem Equivalent.rootScan {w v : Word V} (h : Equivalent L w v) (s : Multiset (V × V)) :
    rootScan L s w = rootScan L s v := by
  induction h with
  | rel _ _ h => exact h.rootScan s
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

variable (L)
def rootCounts (s : Multiset (V × V)) : V →₀ ℕ :=
  (s.map (fun p => Finsupp.single p.2 1)).sum

def wordCounts (w : Word V) : V →₀ ℕ := rootCounts (rootScan L 0 w)

def traceCounts : Trace L → V →₀ ℕ :=
  Quotient.lift (wordCounts L) (fun _ _ h => congrArg rootCounts (h.rootScan 0))

@[simp] theorem traceCounts_ofWord (w : Word V) :
    traceCounts L (ofWord L w) = wordCounts L w := rfl

end RootCounts

variable (L)

/-- The normal trace of an element, obtained from the actual Artin presentation. -/
def groupNormalTrace : WordGroup L → Trace L :=
  Quotient.lift (fun w : FreeMonoid (Letter V) => normalTrace L (ofWord L w.toList))
    (fun _ _ h => h)

def artinNormalTrace (g : ArtinGroup L) : Trace L := groupNormalTrace L (ofArtin L g)

@[simp] theorem artinNormalTrace_word (w : Word V) :
    artinNormalTrace L (wordEval (artinGenerator L) w) = normalTrace L (ofWord L w) := by
  simp only [artinNormalTrace,ofArtin_word]
  rfl

theorem artinNormalTrace_reduced (g : ArtinGroup L) : Reduced L (artinNormalTrace L g) := by
  suffices ∀ h : WordGroup L, Reduced L (groupNormalTrace L h) from this _
  intro h
  induction h using Con.induction_on with
  | H w => exact normalTrace_reduced L (ofWord L w.toList)

theorem artinNormalTrace_eval (g : ArtinGroup L) :
    traceEval L (artinGenerator L) (fun _ _ h => adjacent_generators_commute L h)
      (artinNormalTrace L g) = g := by
  suffices ∀ h : WordGroup L,
      traceEval L (artinGenerator L) (fun _ _ h => adjacent_generators_commute L h)
        (groupNormalTrace L h) = toArtin L h by
    simpa only [artinNormalTrace,toArtin_ofArtin] using this (ofArtin L g)
  intro h
  induction h using Con.induction_on with
  | H w =>
      change traceEval L (artinGenerator L) _ (normalTrace L (ofWord L w.toList)) =
        toArtin L (groupWord L w.toList)
      rw [traceEval_normalTrace,traceEval_ofWord,toArtin_word]

theorem exists_reduced_word (g : ArtinGroup L) :
    ∃ w : Word V, Reduced L (ofWord L w) ∧ wordEval (artinGenerator L) w = g := by
  obtain ⟨w,hw⟩ := Quotient.exists_rep (artinNormalTrace L g)
  refine ⟨w,?_,?_⟩
  · rw [show ofWord L w = artinNormalTrace L g from hw]
    exact artinNormalTrace_reduced L g
  · change traceEval L (artinGenerator L) (fun _ _ h => adjacent_generators_commute L h)
      (ofWord L w) = g
    rw [show ofWord L w = artinNormalTrace L g from hw]
    exact artinNormalTrace_eval L g

/-- A right generator step in the actual presented group is addition/removal
of exactly one maximal occurrence in its reduced trace. -/
theorem artinNormalTrace_right_step (g : ArtinGroup L) (x : Letter V) :
    (artinNormalTrace L (g * letterValue (artinGenerator L) x) =
      appendTrace L (artinNormalTrace L g) (ofWord L [x])) ∨
    (artinNormalTrace L g = appendTrace L
      (artinNormalTrace L (g * letterValue (artinGenerator L) x)) (ofWord L [invLetter x])) := by
  obtain ⟨w,hw,rfl⟩ := exists_reduced_word L g
  have he : wordEval (artinGenerator L) w * letterValue (artinGenerator L) x =
      wordEval (artinGenerator L) (w ++ [x]) := by simp
  rw [he,artinNormalTrace_word,artinNormalTrace_word,hw.normalTrace_eq]
  rcases reduced_append_alternative hw with hl | ⟨v,hv,he,hn⟩
  · left
    exact hl.normalTrace_eq
  · right
    rw [hn]
    exact (ofWord_eq L).mpr he


section DirectionVectors
variable [Fintype V] [LinearOrder V]

omit [Fintype V] [LinearOrder V] in
theorem traceLength_append_singleton (t : Trace L) (x : Letter V) :
    traceLength L (appendTrace L t (ofWord L [x])) = traceLength L t + 1 := by
  induction t using Quotient.inductionOn with
  | h w =>
      change (w ++ [x]).length = w.length + 1
      simp

end DirectionVectors


section HeightAndExactDirections

@[simp] theorem height_generator (v : V) :
    height L (artinGenerator L v) = Multiplicative.ofAdd 1 := PresentedGroup.toGroup.of _

def wordHeight (w : Word V) : ℤ := (w.map fun x => if x.2 then 1 else -1).sum

@[simp] theorem wordHeight_nil : wordHeight ([] : Word V) = 0 := rfl
@[simp] theorem wordHeight_cons (x : Letter V) (w : Word V) :
    wordHeight (x :: w) = (if x.2 then 1 else -1) + wordHeight w := rfl

end HeightAndExactDirections

end TraceWords

end EilenbergGanea

end

end OAI
end

section
-- module Solutions.OAIEG.UnitaryWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Filter Topology
open scoped Quaternion ContDiff

open scoped Quaternion
namespace EilenbergGanea
abbrev SU2 := unitary ℍ

theorem quaternion_mem_unitary_iff (q : ℍ) : q ∈ unitary ℍ ↔ ‖q‖ = 1 := by
  rw [Unitary.mem_iff, Quaternion.star_mul_self, Quaternion.self_mul_star, and_self]
  constructor
  · intro h
    have he : Quaternion.normSq q = 1 := Quaternion.coe_inj.mp h
    rw [Quaternion.normSq_eq_norm_mul_self] at he
    nlinarith [norm_nonneg q]
  · intro h
    simp [Quaternion.normSq_eq_norm_mul_self, h]

def circleQuaternion : Circle →* SU2 where
  toFun z := ⟨Quaternion.ofComplex z, by
    rw [Unitary.mem_iff, Quaternion.star_mul_self, Quaternion.self_mul_star, and_self]
    have hz := Circle.normSq_coe z
    have he : Quaternion.normSq (Quaternion.ofComplex z) = 1 := by
      simpa [Quaternion.normSq_def', Complex.normSq_apply, sq] using hz
    rw [he]; rfl⟩
  map_one' := Subtype.ext (map_one Quaternion.ofComplex)
  map_mul' z w := Subtype.ext (map_mul Quaternion.ofComplex (z : ℂ) (w : ℂ))

@[simp] theorem circleQuaternion_coe (z : Circle) :
    ((circleQuaternion z : SU2) : ℍ) = (z : ℂ) := rfl

open Set Filter Topology
open scoped ContDiff

/-- Radial normalization is only used on nonzero quaternions. The harmless
value at zero makes it a total function without changing that domain. -/
def normalizeQuaternion (q : ℍ) : SU2 := by
  classical
  exact if h : q = 0 then 1 else
    ⟨‖q‖⁻¹ • q, (quaternion_mem_unitary_iff _).mpr (by
      simp only [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr h))⟩

end EilenbergGanea

namespace EilenbergGanea
open Set Filter Topology
open scoped Quaternion ContDiff

/-- Ambient conjugation, compatible with the group operation on unit quaternions. -/
def quaternionConjugate (a : SU2) (q : ℍ) : ℍ := (a : ℍ) * q * star (a : ℍ)

@[simp] theorem quaternionConjugate_norm (a : SU2) (q : ℍ) :
    ‖quaternionConjugate a q‖ = ‖q‖ := by
  have ha := (quaternion_mem_unitary_iff _).mp a.property
  simp [quaternionConjugate, ha]

@[simp] theorem quaternionConjugate_zero (a : SU2) : quaternionConjugate a 0 = 0 := by
  simp [quaternionConjugate]

@[simp] theorem quaternionConjugate_one (a : SU2) : quaternionConjugate a 1 = 1 := by
  simp [quaternionConjugate]

@[simp] theorem quaternionConjugate_coe (a q : SU2) :
    quaternionConjugate a (q : ℍ) = ((a * q * a⁻¹ : SU2) : ℍ) := rfl

end EilenbergGanea


end

end OAI
end

section
-- module Solutions.OAIEG.WordEquations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Filter Topology MeasureTheory
open scoped Quaternion ContDiff

namespace EilenbergGanea
open Set Filter Topology
open scoped Quaternion ContDiff

/-- Word evaluation with a fixed alphabet of coefficient letters and a finite
alphabet of unknowns. Coefficients may vary smoothly with a real parameter. -/
def coefficientWordMap {ι : Type*} {m d : ℕ}
    (w : Fin d → FreeGroup (ι ⊕ Fin m)) (a : ℝ → ι → SU2)
    (q : ℝ × (Fin m → SU2)) : Fin d → SU2 :=
  fun i => FreeGroup.lift (Sum.elim (a q.1) q.2) (w i)

def radialCoefficientWordMap {ι : Type*} {m : ℕ}
    (w : Fin m → FreeGroup (ι ⊕ Fin m)) (a : ℝ → ι → SU2)
    (q : ℝ × (Fin m → ℍ)) : Fin m → ℍ :=
  fun i => ‖q.2 i‖ • (coefficientWordMap w a (q.1, fun j => normalizeQuaternion (q.2 j)) i : ℍ)

@[simp] theorem radialCoefficientWordMap_norm {ι : Type*} {m : ℕ}
    (w : Fin m → FreeGroup (ι ⊕ Fin m)) (a : ℝ → ι → SU2)
    (q : ℝ × (Fin m → ℍ)) (i : Fin m) :
    ‖radialCoefficientWordMap w a q i‖ = ‖q.2 i‖ := by
  have h := (quaternion_mem_unitary_iff _).mp
    (coefficientWordMap w a (q.1, fun j => normalizeQuaternion (q.2 j)) i).property
  simp [radialCoefficientWordMap, norm_smul, h]

end EilenbergGanea


end

end OAI
end

section
-- module Solutions.OAIEG.SmallHolonomy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Filter Topology MeasureTheory
open scoped Quaternion ContDiff

namespace EilenbergGanea
open scoped Quaternion ContDiff
open Set
section SelectedEquations
variable {E : Type*} {m d : ℕ}

/-- The selected unknowns remain separate from coefficients, even when two
letters have the same image in the group quotient. -/
def selectedAlphabet (σ : Fin m ↪ E) (e : E) : E ⊕ Fin m := by
  classical
  exact if h : ∃ i, σ i = e then .inr h.choose else .inl e

@[simp] theorem selectedAlphabet_selected (σ : Fin m ↪ E) (i : Fin m) :
    selectedAlphabet σ (σ i) = .inr i := by
  classical
  have h : ∃ j, σ j = σ i := ⟨i,rfl⟩
  simp only [selectedAlphabet, dite_eq_left h]
  exact congrArg Sum.inr (σ.injective h.choose_spec)

def selectedLabel (σ : Fin m ↪ E) (a : E → SU2) (x : Fin m → SU2) (e : E) : SU2 :=
  Sum.elim a x (selectedAlphabet σ e)

@[simp] theorem selectedLabel_selected (σ : Fin m ↪ E) (a : E → SU2)
    (x : Fin m → SU2) (i : Fin m) : selectedLabel σ a x (σ i) = x i := by
  simp [selectedLabel]

end SelectedEquations
end EilenbergGanea

open scoped Quaternion


end

end OAI
end

section
-- module Solutions.OAIEG.AffineTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Filter Topology MeasureTheory
open scoped Quaternion ContDiff

namespace EilenbergGanea
namespace AffineTransport


@[simp] theorem unit_norm (h : SU2) : ‖(h : ℍ)‖ = 1 :=
  (quaternion_mem_unitary_iff _).mp h.property

def leftLinearEquiv (h : SU2) : ℍ ≃ₗ[ℝ] ℍ where
  toFun q := (h : ℍ) * q
  invFun q := (h⁻¹ : SU2) * q
  left_inv q := by simp [← mul_assoc,← Submonoid.coe_mul]
  right_inv q := by simp [← mul_assoc,← Submonoid.coe_mul]
  map_add' _ _ := mul_add _ _ _
  map_smul' r q := mul_smul_comm r (h : ℍ) q

@[simp] theorem leftLinearEquiv_apply (h : SU2) (q : ℍ) :
    leftLinearEquiv h q = (h : ℍ) * q := rfl

section FiniteSimplex
variable {V : Type*} [Fintype V]

def coordinateSimplex : Set (V → ℝ) :=
  {weights | (∀ vertex, 0 ≤ weights vertex) ∧ ∑ vertex, weights vertex = 1}

/-- Closed coordinate face of the standard simplex. -/
def face (s : Finset V) : Set (V → ℝ) :=
  {b | b ∈ coordinateSimplex ∧ ∀ v ∉ s, b v = 0}

/-- The whole two-skeleton of a finite standard simplex. -/
def triangleSet : Set (V → ℝ) :=
  ⋃ s : {s : Finset V // s.card ≤ 3}, face s.val

abbrev TrianglePoint (V : Type*) [Fintype V] := (triangleSet : Set (V → ℝ))

theorem mem_triangleSet {b : V → ℝ} : b ∈ triangleSet ↔
    ∃ s : Finset V, s.card ≤ 3 ∧ b ∈ coordinateSimplex ∧ ∀ v ∉ s, b v = 0 := by
  simp only [triangleSet,Set.mem_iUnion,face,Set.mem_ofPred_eq,Subtype.exists,exists_prop]

theorem point_simplex (b : TrianglePoint V) : (b : V → ℝ) ∈ coordinateSimplex := by
  obtain ⟨_,_,h,_⟩ := mem_triangleSet.mp b.property
  exact h

theorem point_exists_nonzero (b : TrianglePoint V) : ∃ v, (b : V → ℝ) v ≠ 0 := by
  by_contra! h
  have he := (point_simplex b).2
  simp only [h,Finset.sum_const_zero] at he
  norm_num at he

variable (h : V → V → SU2) (q : V → ℍ)

def rawGauge (a : V) (b : V → ℝ) : ℍ := ∑ v, b v • ((h a v : ℍ) * q v)

def GeneralPosition : Prop := ∀ a (s : Finset V), s.card ≤ 3 →
  LinearIndepOn ℝ (fun v => (h a v : ℍ) * q v) (s : Set V)

def gauge (a : V) (b : TrianglePoint V) : SU2 := normalizeQuaternion (rawGauge h q a b)

end FiniteSimplex

section Connection
variable {V : Type*} [Fintype V]
variable (L : SimpleGraph V)

def Related (a b : V) : Prop := a = b ∨ L.Adj a b

def Star (a : V) (b : TrianglePoint V) : Prop :=
  ∀ v, (b : V → ℝ) v ≠ 0 → Related L a v

def CliquePoint (b : TrianglePoint V) : Prop :=
  ∀ a, (b : V → ℝ) a ≠ 0 → Star L a b

def Compatible (b c : TrianglePoint V) : Prop :=
  ∀ v w, ((b : V → ℝ) v ≠ 0 ∨ (c : V → ℝ) v ≠ 0) →
    ((b : V → ℝ) w ≠ 0 ∨ (c : V → ℝ) w ≠ 0) → Related L v w

def root (b : TrianglePoint V) : V := Classical.choose (point_exists_nonzero b)

variable (h : V → V → SU2) (q : V → ℍ)

def FlatConnection : Prop := ∀ a b c, Related L a b → Related L b c →
  Related L a c → h a b * h b c = h a c

def chartTransport (a : V) (b c : TrianglePoint V) : SU2 :=
  (gauge h q a b)⁻¹ * gauge h q a c

def transport (b c : TrianglePoint V) : SU2 := chartTransport h q (root b) b c

/-- Two compatible pieces, rather than a chosen homotopy class of paths, suffice. -/
def edgeTransport (b c d : TrianglePoint V) : SU2 := transport h q b c * transport h q c d

end Connection

end AffineTransport




end EilenbergGanea

end

end OAI
end

section
-- module Solutions.OAIEG.CWComplex_Cover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Metric Topology

/-! Actual characteristic-cell lifts for an ordinary Whitehead CW complex.
This is a dependency toward (not an assumption replacing) the arbitrary-CW
presentation and cellular-cycle bridge. -/
open Set Metric Topology
namespace EilenbergGanea.CWCover

abbrev Disk (n : ℕ) := closedBall (0 : Fin n → ℝ) 1

def diskCenter (n : ℕ) : Disk n := ⟨0,by simp⟩

instance diskContractible (n : ℕ) : ContractibleSpace (Disk n) :=
  contractibleSpace_closedBall (by norm_num)

instance diskLocallyPathConnected (n : ℕ) : LocallyPathConnectedSpace (Disk n) :=
  (convex_closedBall (0 : Fin n → ℝ) 1).locallyPathConnectedSpace

variable {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
variable [CWComplex (univ : Set X)] {p : E → X} (cov : IsCoveringMap p)

abbrev Cell (n : ℕ) := Topology.RelCWComplex.cell (univ : Set X) n

def characteristic {n : ℕ} (i : Cell (X := X) n) : C(Disk n,X) :=
  ⟨fun z => Topology.RelCWComplex.map n i z.val,
    continuousOn_iff_continuous_domRestrict.mp (Topology.RelCWComplex.continuousOn n i)⟩

abbrev LiftedCell (n : ℕ) := Σ i : Cell (X := X) n, {e : E // p e = characteristic i (diskCenter n)}

noncomputable def cellLift {n : ℕ} (c : LiftedCell (p := p) n) : C(Disk n,E) :=
  (cov.existsUnique_continuousMap_lifts (characteristic c.1) (diskCenter n) c.2.val c.2.property).exists.choose

@[simp] theorem cellLift_center {n : ℕ} (c : LiftedCell (p := p) n) :
    cellLift cov c (diskCenter n) = c.2.val :=
  (cov.existsUnique_continuousMap_lifts (characteristic c.1) (diskCenter n) c.2.val c.2.property).exists.choose_spec.1

end EilenbergGanea.CWCover


end

end OAI
end

section
-- module Solutions.OAIEG.Cubical_Singular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Topology

/-! Low-dimensional normalized cubical singular chains for the actual
cellular comparison of arbitrary ordinary two-dimensional CW spaces. Neither
cellular exactness nor a presentation theorem is included as an assumption. -/
open Classical Set
namespace EilenbergGanea.CubicalSingular
variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
abbrev I := unitInterval
abbrev Cube₁ (X : Type*) [TopologicalSpace X] := C(I,X)
abbrev Cube₂ (X : Type*) [TopologicalSpace X] := C(I × I,X)
abbrev Cube₃ (X : Type*) [TopologicalSpace X] := C(I × I × I,X)
abbrev C₀ (X : Type*) := X →₀ ℤ
abbrev C₁ (X : Type*) [TopologicalSpace X] := Cube₁ X →₀ ℤ
abbrev C₂ (X : Type*) [TopologicalSpace X] := Cube₂ X →₀ ℤ
abbrev C₃ (X : Type*) [TopologicalSpace X] := Cube₃ X →₀ ℤ

def edge₁ (σ : Cube₂ X) (a : I) : Cube₁ X := ⟨fun t => σ (a,t),by fun_prop⟩
def edge₂ (σ : Cube₂ X) (a : I) : Cube₁ X := ⟨fun t => σ (t,a),by fun_prop⟩
def face₁ (σ : Cube₃ X) (a : I) : Cube₂ X := ⟨fun t => σ (a,t),by fun_prop⟩
def face₂ (σ : Cube₃ X) (a : I) : Cube₂ X := ⟨fun t => σ (t.1,a,t.2),by fun_prop⟩
def face₃ (σ : Cube₃ X) (a : I) : Cube₂ X := ⟨fun t => σ (t.1,t.2,a),by fun_prop⟩

def b₁ : C₁ X →ₗ[ℤ] C₀ X := Finsupp.linearCombination ℤ
  (fun σ => Finsupp.single (σ 1) 1 - Finsupp.single (σ 0) 1)
def b₂ : C₂ X →ₗ[ℤ] C₁ X := Finsupp.linearCombination ℤ
  (fun σ => Finsupp.single (edge₁ σ 1) 1 - Finsupp.single (edge₁ σ 0) 1 -
      Finsupp.single (edge₂ σ 1) 1 + Finsupp.single (edge₂ σ 0) 1)
def b₃ : C₃ X →ₗ[ℤ] C₂ X := Finsupp.linearCombination ℤ
  (fun σ => Finsupp.single (face₁ σ 1) 1 - Finsupp.single (face₁ σ 0) 1 -
      Finsupp.single (face₂ σ 1) 1 + Finsupp.single (face₂ σ 0) 1 +
      Finsupp.single (face₃ σ 1) 1 - Finsupp.single (face₃ σ 0) 1)

@[simp] theorem b₁_single (σ : Cube₁ X) (a : ℤ) :
    b₁ (Finsupp.single σ a) = a • (Finsupp.single (σ 1) 1 - Finsupp.single (σ 0) 1) := by
  simp [b₁]
@[simp] theorem b₂_single (σ : Cube₂ X) (a : ℤ) :
    b₂ (Finsupp.single σ a) = a • (Finsupp.single (edge₁ σ 1) 1 -
      Finsupp.single (edge₁ σ 0) 1 - Finsupp.single (edge₂ σ 1) 1 + Finsupp.single (edge₂ σ 0) 1) := by
  simp [b₂]
@[simp] theorem b₃_single (σ : Cube₃ X) (a : ℤ) :
    b₃ (Finsupp.single σ a) = a • (Finsupp.single (face₁ σ 1) 1 -
      Finsupp.single (face₁ σ 0) 1 - Finsupp.single (face₂ σ 1) 1 +
      Finsupp.single (face₂ σ 0) 1 + Finsupp.single (face₃ σ 1) 1 - Finsupp.single (face₃ σ 0) 1) := by
  simp [b₃]

theorem b₁_b₂ : (b₁ : C₁ X →ₗ[ℤ] C₀ X).comp b₂ = 0 := by
  apply Finsupp.lhom_ext
  intro σ a
  simp only [LinearMap.comp_apply,b₂_single,one_smul,map_add,map_sub,map_smul,b₁_single,edge₁,edge₂,
    ContinuousMap.coe_mk,LinearMap.zero_apply]
  abel_nf

@[simp] theorem edge₁_face₂ (σ : Cube₃ X) (a b : I) : edge₁ (face₂ σ a) b = edge₁ (face₁ σ b) a := rfl
@[simp] theorem edge₁_face₃ (σ : Cube₃ X) (a b : I) : edge₁ (face₃ σ a) b = edge₂ (face₁ σ b) a := rfl
@[simp] theorem edge₂_face₃ (σ : Cube₃ X) (a b : I) : edge₂ (face₃ σ a) b = edge₂ (face₂ σ b) a := rfl

theorem b₂_b₃ : (b₂ : C₂ X →ₗ[ℤ] C₁ X).comp b₃ = 0 := by
  apply Finsupp.lhom_ext
  intro σ a
  simp only [LinearMap.comp_apply,b₃_single,one_smul,map_add,map_sub,map_smul,b₂_single,
    edge₁_face₂,edge₁_face₃,edge₂_face₃,LinearMap.zero_apply]
  abel_nf

def constant₁ (x : X) : Cube₁ X := ContinuousMap.const _ x
def degenerate₁ (σ : Cube₁ X) : Cube₂ X := ⟨fun t => σ t.1,by fun_prop⟩
def degenerate₂ (σ : Cube₁ X) : Cube₂ X := ⟨fun t => σ t.2,by fun_prop⟩
@[simp] theorem edge₁_degenerate₁ (σ : Cube₁ X) (a : I) :
    edge₁ (degenerate₁ σ) a = constant₁ (σ a) := ContinuousMap.ext (fun _ => rfl)
@[simp] theorem edge₂_degenerate₁ (σ : Cube₁ X) (a : I) :
    edge₂ (degenerate₁ σ) a = σ := ContinuousMap.ext (fun _ => rfl)
@[simp] theorem edge₁_degenerate₂ (σ : Cube₁ X) (a : I) :
    edge₁ (degenerate₂ σ) a = σ := ContinuousMap.ext (fun _ => rfl)
@[simp] theorem edge₂_degenerate₂ (σ : Cube₁ X) (a : I) :
    edge₂ (degenerate₂ σ) a = constant₁ (σ a) := ContinuousMap.ext (fun _ => rfl)
def D₁ (X : Type*) [TopologicalSpace X] : Submodule ℤ (C₁ X) :=
  Submodule.span ℤ (Set.range (fun x : X => Finsupp.single (constant₁ x) 1))
def D₂ (X : Type*) [TopologicalSpace X] : Submodule ℤ (C₂ X) :=
  Submodule.span ℤ (Set.range (fun σ : Cube₁ X => Finsupp.single (degenerate₁ σ) 1) ∪
    Set.range (fun σ : Cube₁ X => Finsupp.single (degenerate₂ σ) 1))
abbrev N₁ (X : Type*) [TopologicalSpace X] := C₁ X ⧸ D₁ X
abbrev N₂ (X : Type*) [TopologicalSpace X] := C₂ X ⧸ D₂ X

theorem D₁_le_ker : D₁ X ≤ LinearMap.ker (b₁ : C₁ X →ₗ[ℤ] C₀ X) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨x,rfl⟩
  simp [constant₁]

theorem b₂_D₂ : D₂ X ≤ (D₁ X).comap (b₂ : C₂ X →ₗ[ℤ] C₁ X) := by
  apply Submodule.span_le.mpr
  rintro _ (⟨σ,rfl⟩ | ⟨σ,rfl⟩)
  · change b₂ (Finsupp.single (degenerate₁ σ) 1) ∈ D₁ X
    have h₁ (x : X) : Finsupp.single (constant₁ x) 1 ∈ D₁ X :=
      Submodule.subset_span ⟨x,rfl⟩
    simpa using (D₁ X).sub_mem (h₁ (σ 1)) (h₁ (σ 0))
  · change b₂ (Finsupp.single (degenerate₂ σ) 1) ∈ D₁ X
    have h₁ (x : X) : Finsupp.single (constant₁ x) 1 ∈ D₁ X :=
      Submodule.subset_span ⟨x,rfl⟩
    have he : b₂ (Finsupp.single (degenerate₂ σ) 1) =
        Finsupp.single (constant₁ (σ 0)) 1 - Finsupp.single (constant₁ (σ 1)) 1 := by
      simp [sub_eq_add_neg]
      abel
    rw [he]
    exact (D₁ X).sub_mem (h₁ (σ 0)) (h₁ (σ 1))

def d₁ : N₁ X →ₗ[ℤ] C₀ X := (D₁ X).liftQ b₁ D₁_le_ker
def d₂ : N₂ X →ₗ[ℤ] N₁ X := (D₂ X).mapQ (D₁ X) b₂ b₂_D₂
def d₃ : C₃ X →ₗ[ℤ] N₂ X := (D₂ X).mkQ.comp b₃

@[simp] theorem d₁_mk (c : C₁ X) : d₁ ((D₁ X).mkQ c) = b₁ c := rfl
@[simp] theorem d₂_mk (c : C₂ X) : d₂ ((D₂ X).mkQ c) = (D₁ X).mkQ (b₂ c) := rfl

theorem d₁_d₂ (c : N₂ X) : d₁ (d₂ c) = 0 := by
  obtain ⟨c,rfl⟩ := Submodule.mkQ_surjective (D₂ X) c
  exact LinearMap.congr_fun b₁_b₂ c

theorem d₂_d₃ (c : C₃ X) : d₂ (d₃ c) = 0 := by
  change (D₁ X).mkQ ((b₂ : C₂ X →ₗ[ℤ] C₁ X) (b₃ c)) = 0
  have h := LinearMap.congr_fun b₂_b₃ c
  change b₂ (b₃ c) = 0 at h
  rw [h]
  exact map_zero _


def push₀ (f : C(X,Y)) : C₀ X →ₗ[ℤ] C₀ Y :=
  Finsupp.linearCombination ℤ (fun x => Finsupp.single (f x) 1)
def push₁ (f : C(X,Y)) : C₁ X →ₗ[ℤ] C₁ Y :=
  Finsupp.linearCombination ℤ (fun σ => Finsupp.single (f.comp σ) 1)
def push₂ (f : C(X,Y)) : C₂ X →ₗ[ℤ] C₂ Y :=
  Finsupp.linearCombination ℤ (fun σ => Finsupp.single (f.comp σ) 1)

@[simp] theorem push₀_single (f : C(X,Y)) (x : X) (a : ℤ) :
    push₀ f (Finsupp.single x a) = Finsupp.single (f x) a := by simp [push₀]
@[simp] theorem push₁_single (f : C(X,Y)) (σ : Cube₁ X) (a : ℤ) :
    push₁ f (Finsupp.single σ a) = Finsupp.single (f.comp σ) a := by simp [push₁]
@[simp] theorem push₂_single (f : C(X,Y)) (σ : Cube₂ X) (a : ℤ) :
    push₂ f (Finsupp.single σ a) = Finsupp.single (f.comp σ) a := by simp [push₂]

@[simp] theorem edge₁_comp (f : C(X,Y)) (σ : Cube₂ X) (a : I) :
    edge₁ (f.comp σ) a = f.comp (edge₁ σ a) := rfl
@[simp] theorem edge₂_comp (f : C(X,Y)) (σ : Cube₂ X) (a : I) :
    edge₂ (f.comp σ) a = f.comp (edge₂ σ a) := rfl
@[simp] theorem face₁_comp (f : C(X,Y)) (σ : Cube₃ X) (a : I) :
    face₁ (f.comp σ) a = f.comp (face₁ σ a) := rfl
@[simp] theorem face₂_comp (f : C(X,Y)) (σ : Cube₃ X) (a : I) :
    face₂ (f.comp σ) a = f.comp (face₂ σ a) := rfl
@[simp] theorem face₃_comp (f : C(X,Y)) (σ : Cube₃ X) (a : I) :
    face₃ (f.comp σ) a = f.comp (face₃ σ a) := rfl

theorem b₁_push (f : C(X,Y)) : b₁.comp (push₁ f) = (push₀ f).comp b₁ := by
  apply Finsupp.lhom_ext
  intro σ a
  simp

theorem b₂_push (f : C(X,Y)) : b₂.comp (push₂ f) = (push₁ f).comp b₂ := by
  apply Finsupp.lhom_ext
  intro σ a
  simp

section Prism
variable {f g : C(X,Y)} (H : f.Homotopy g)
def prism₀ (x : X) : Cube₁ Y := ⟨fun t => H (t,x),by fun_prop⟩
def prism₁ (σ : Cube₁ X) : Cube₂ Y := ⟨fun t => H (t.1,σ t.2),by fun_prop⟩
def prism₂ (σ : Cube₂ X) : Cube₃ Y := ⟨fun t => H (t.1,σ t.2),by fun_prop⟩

def P₀ : C₀ X →ₗ[ℤ] C₁ Y := Finsupp.linearCombination ℤ
  (fun x => Finsupp.single (prism₀ H x) 1)
def P₁ : C₁ X →ₗ[ℤ] C₂ Y := Finsupp.linearCombination ℤ
  (fun σ => Finsupp.single (prism₁ H σ) 1)
def P₂ : C₂ X →ₗ[ℤ] C₃ Y := Finsupp.linearCombination ℤ
  (fun σ => Finsupp.single (prism₂ H σ) 1)
@[simp] theorem P₀_single (x : X) (a : ℤ) :
    P₀ H (Finsupp.single x a) = Finsupp.single (prism₀ H x) a := by simp [P₀]
@[simp] theorem P₁_single (σ : Cube₁ X) (a : ℤ) :
    P₁ H (Finsupp.single σ a) = Finsupp.single (prism₁ H σ) a := by simp [P₁]
@[simp] theorem P₂_single (σ : Cube₂ X) (a : ℤ) :
    P₂ H (Finsupp.single σ a) = Finsupp.single (prism₂ H σ) a := by simp [P₂]
@[simp] theorem prism₀_zero (x : X) : prism₀ H x 0 = f x := H.apply_zero x
@[simp] theorem prism₀_one (x : X) : prism₀ H x 1 = g x := H.apply_one x
@[simp] theorem prism₁_edge₁_zero (σ : Cube₁ X) : edge₁ (prism₁ H σ) 0 = f.comp σ :=
  ContinuousMap.ext (fun _ => H.apply_zero _)
@[simp] theorem prism₁_edge₁_one (σ : Cube₁ X) : edge₁ (prism₁ H σ) 1 = g.comp σ :=
  ContinuousMap.ext (fun _ => H.apply_one _)
@[simp] theorem prism₁_edge₂ (σ : Cube₁ X) (a : I) : edge₂ (prism₁ H σ) a = prism₀ H (σ a) := rfl
@[simp] theorem prism₂_face₁_zero (σ : Cube₂ X) : face₁ (prism₂ H σ) 0 = f.comp σ :=
  ContinuousMap.ext (fun _ => H.apply_zero _)
@[simp] theorem prism₂_face₁_one (σ : Cube₂ X) : face₁ (prism₂ H σ) 1 = g.comp σ :=
  ContinuousMap.ext (fun _ => H.apply_one _)
@[simp] theorem prism₂_face₂ (σ : Cube₂ X) (a : I) : face₂ (prism₂ H σ) a = prism₁ H (edge₁ σ a) := rfl
@[simp] theorem prism₂_face₃ (σ : Cube₂ X) (a : I) : face₃ (prism₂ H σ) a = prism₁ H (edge₂ σ a) := rfl

theorem prism_boundary₁ : b₂.comp (P₁ H) + (P₀ H).comp b₁ = push₁ g - push₁ f := by
  apply Finsupp.lhom_ext
  intro σ a
  simp [smul_add,smul_sub,Finsupp.smul_single]

theorem prism_boundary₂ : b₃.comp (P₂ H) + (P₁ H).comp b₂ = push₂ g - push₂ f := by
  apply Finsupp.lhom_ext
  intro σ a
  simp [smul_add,smul_sub,Finsupp.smul_single]

theorem P₁_D₁ : D₁ X ≤ (D₂ Y).comap (P₁ H) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨x,rfl⟩
  change P₁ H (Finsupp.single (constant₁ x) 1) ∈ D₂ Y
  rw [P₁_single]
  have he : prism₁ H (constant₁ x) = degenerate₁ (prism₀ H x) :=
    ContinuousMap.ext (fun _ => rfl)
  rw [he]
  exact Submodule.subset_span (Or.inl ⟨_,rfl⟩)
end Prism

@[simp] theorem push₁_id : push₁ (ContinuousMap.id X) = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro σ a
  simp
@[simp] theorem push₂_id : push₂ (ContinuousMap.id X) = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro σ a
  simp

theorem push₁_const_mem (x : X) (c : C₁ X) : push₁ (ContinuousMap.const X x) c ∈ D₁ X := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simpa only [map_add] using (D₁ X).add_mem hc hd
  | single σ a =>
    rw [push₁_single]
    have he : (ContinuousMap.const X x).comp σ = constant₁ x := ContinuousMap.ext (fun _ => rfl)
    rw [he,← Finsupp.smul_single_one]
    exact (D₁ X).smul_mem a (Submodule.subset_span ⟨x,rfl⟩)

theorem push₂_const_mem (x : X) (c : C₂ X) : push₂ (ContinuousMap.const X x) c ∈ D₂ X := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simpa only [map_add] using (D₂ X).add_mem hc hd
  | single σ a =>
    rw [push₂_single]
    have he : (ContinuousMap.const X x).comp σ = degenerate₁ (constant₁ x) :=
      ContinuousMap.ext (fun _ => rfl)
    rw [he,← Finsupp.smul_single_one]
    exact (D₂ X).smul_mem a (Submodule.subset_span (Or.inl ⟨_,rfl⟩))

theorem exact₁_of_contractible [ContractibleSpace X] (c : N₁ X) (hc : d₁ c = 0) :
    ∃ b : N₂ X, d₂ b = c := by
  obtain ⟨x,⟨H⟩⟩ := id_nullhomotopic X
  obtain ⟨c,rfl⟩ := (D₁ X).mkQ_surjective c
  change b₁ c = 0 at hc
  refine ⟨(D₂ X).mkQ (-P₁ H c),?_⟩
  have he := LinearMap.congr_fun (prism_boundary₁ H) c
  change b₂ (P₁ H c) + P₀ H (b₁ c) = push₁ (ContinuousMap.const X x) c -
    push₁ (ContinuousMap.id X) c at he
  simp only [hc,map_zero,add_zero,push₁_id,LinearMap.id_apply] at he
  rw [d₂_mk,map_neg,he,map_neg,map_sub]
  have hz : (D₁ X).mkQ (push₁ (ContinuousMap.const X x) c) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr (push₁_const_mem x c)
  rw [hz,zero_sub,neg_neg]

theorem exact₂_of_contractible [ContractibleSpace X] (c : N₂ X) (hc : d₂ c = 0) :
    ∃ b : C₃ X, d₃ b = c := by
  obtain ⟨x,⟨H⟩⟩ := id_nullhomotopic X
  obtain ⟨c,rfl⟩ := (D₂ X).mkQ_surjective c
  change (D₁ X).mkQ (b₂ c) = 0 at hc
  have hc' : b₂ c ∈ D₁ X := (Submodule.Quotient.mk_eq_zero _).mp hc
  refine ⟨-P₂ H c,?_⟩
  have he := LinearMap.congr_fun (prism_boundary₂ H) c
  change b₃ (P₂ H c) + P₁ H (b₂ c) = push₂ (ContinuousMap.const X x) c -
    push₂ (ContinuousMap.id X) c at he
  rw [push₂_id,LinearMap.id_apply] at he
  have hP : (D₂ X).mkQ (P₁ H (b₂ c)) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr (P₁_D₁ H hc')
  have hz : (D₂ X).mkQ (push₂ (ContinuousMap.const X x) c) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr (push₂_const_mem x c)
  have hn := congrArg (D₂ X).mkQ he
  simp only [map_add,map_sub,hP,hz,add_zero,zero_sub] at hn
  change (D₂ X).mkQ (b₃ (-P₂ H c)) = _
  rw [map_neg,map_neg,hn,neg_neg]


@[simp] theorem comp_constant₁ (f : C(X,Y)) (x : X) :
    f.comp (constant₁ x) = constant₁ (f x) := ContinuousMap.ext (fun _ => rfl)
@[simp] theorem comp_degenerate₁ (f : C(X,Y)) (σ : Cube₁ X) :
    f.comp (degenerate₁ σ) = degenerate₁ (f.comp σ) := rfl
@[simp] theorem comp_degenerate₂ (f : C(X,Y)) (σ : Cube₁ X) :
    f.comp (degenerate₂ σ) = degenerate₂ (f.comp σ) := rfl

theorem push₁_D₁ (f : C(X,Y)) : D₁ X ≤ (D₁ Y).comap (push₁ f) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨x,rfl⟩
  change push₁ f (Finsupp.single (constant₁ x) 1) ∈ D₁ Y
  simp only [push₁_single,comp_constant₁]
  exact Submodule.subset_span ⟨_,rfl⟩

theorem push₂_D₂ (f : C(X,Y)) : D₂ X ≤ (D₂ Y).comap (push₂ f) := by
  apply Submodule.span_le.mpr
  rintro _ (⟨σ,rfl⟩ | ⟨σ,rfl⟩)
  · change push₂ f (Finsupp.single (degenerate₁ σ) 1) ∈ D₂ Y
    simp only [push₂_single,comp_degenerate₁]
    exact Submodule.subset_span (Or.inl ⟨_,rfl⟩)
  · change push₂ f (Finsupp.single (degenerate₂ σ) 1) ∈ D₂ Y
    simp only [push₂_single,comp_degenerate₂]
    exact Submodule.subset_span (Or.inr ⟨_,rfl⟩)

def pushN₁ (f : C(X,Y)) : N₁ X →ₗ[ℤ] N₁ Y := (D₁ X).mapQ (D₁ Y) (push₁ f) (push₁_D₁ f)
def pushN₂ (f : C(X,Y)) : N₂ X →ₗ[ℤ] N₂ Y := (D₂ X).mapQ (D₂ Y) (push₂ f) (push₂_D₂ f)
@[simp] theorem pushN₁_mk (f : C(X,Y)) (c : C₁ X) :
    pushN₁ f ((D₁ X).mkQ c) = (D₁ Y).mkQ (push₁ f c) := rfl
@[simp] theorem pushN₂_mk (f : C(X,Y)) (c : C₂ X) :
    pushN₂ f ((D₂ X).mkQ c) = (D₂ Y).mkQ (push₂ f c) := rfl

theorem d₁_push (f : C(X,Y)) (c : N₁ X) : d₁ (pushN₁ f c) = push₀ f (d₁ c) := by
  obtain ⟨c,rfl⟩ := (D₁ X).mkQ_surjective c
  exact LinearMap.congr_fun (b₁_push f) c

theorem d₂_push (f : C(X,Y)) (c : N₂ X) : d₂ (pushN₂ f c) = pushN₁ f (d₂ c) := by
  obtain ⟨c,rfl⟩ := (D₂ X).mkQ_surjective c
  change (D₁ Y).mkQ (b₂ (push₂ f c)) = (D₁ Y).mkQ (push₁ f (b₂ c))
  exact congrArg (D₁ Y).mkQ (LinearMap.congr_fun (b₂_push f) c)

theorem push₁_comp (g : C(Y,Z)) (f : C(X,Y)) : push₁ (g.comp f) = (push₁ g).comp (push₁ f) := by
  apply Finsupp.lhom_ext
  intro σ a
  simp

theorem push₂_comp (g : C(Y,Z)) (f : C(X,Y)) : push₂ (g.comp f) = (push₂ g).comp (push₂ f) := by
  apply Finsupp.lhom_ext
  intro σ a
  simp

theorem pushN₁_comp (g : C(Y,Z)) (f : C(X,Y)) (c : N₁ X) :
    pushN₁ (g.comp f) c = pushN₁ g (pushN₁ f c) := by
  obtain ⟨c,rfl⟩ := (D₁ X).mkQ_surjective c
  simp only [pushN₁_mk,push₁_comp,LinearMap.comp_apply]

theorem pushN₂_comp (g : C(Y,Z)) (f : C(X,Y)) (c : N₂ X) :
    pushN₂ (g.comp f) c = pushN₂ g (pushN₂ f c) := by
  obtain ⟨c,rfl⟩ := (D₂ X).mkQ_surjective c
  simp only [pushN₂_mk,push₂_comp,LinearMap.comp_apply]

@[simp] theorem pushN₁_id (c : N₁ X) : pushN₁ (ContinuousMap.id X) c = c := by
  obtain ⟨c,rfl⟩ := (D₁ X).mkQ_surjective c
  rw [pushN₁_mk,push₁_id]
  rfl
@[simp] theorem pushN₂_id (c : N₂ X) : pushN₂ (ContinuousMap.id X) c = c := by
  obtain ⟨c,rfl⟩ := (D₂ X).mkQ_surjective c
  rw [pushN₂_mk,push₂_id]
  rfl

@[simp] theorem pushN₁_const (y : Y) (c : N₁ X) : pushN₁ (ContinuousMap.const X y) c = 0 := by
  obtain ⟨c,rfl⟩ := (D₁ X).mkQ_surjective c
  rw [pushN₁_mk]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simpa only [map_add] using (D₁ Y).add_mem hc hd
  | single σ a =>
    rw [push₁_single]
    have he : (ContinuousMap.const X y).comp σ = constant₁ y := ContinuousMap.ext (fun _ => rfl)
    rw [he,← Finsupp.smul_single_one]
    exact (D₁ Y).smul_mem a (Submodule.subset_span ⟨y,rfl⟩)

@[simp] theorem pushN₂_const (y : Y) (c : N₂ X) : pushN₂ (ContinuousMap.const X y) c = 0 := by
  obtain ⟨c,rfl⟩ := (D₂ X).mkQ_surjective c
  rw [pushN₂_mk]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simpa only [map_add] using (D₂ Y).add_mem hc hd
  | single σ a =>
    rw [push₂_single]
    have he : (ContinuousMap.const X y).comp σ = degenerate₁ (constant₁ y) :=
      ContinuousMap.ext (fun _ => rfl)
    rw [he,← Finsupp.smul_single_one]
    exact (D₂ Y).smul_mem a (Submodule.subset_span (Or.inl ⟨_,rfl⟩))

end EilenbergGanea.CubicalSingular

namespace EilenbergGanea.CubicalSingular
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def half (b : Bool) : C(I,I) where
  toFun t := if b then ⟨(1 + t.val) / 2,by constructor <;> linarith [t.property.1,t.property.2]⟩
    else ⟨t.val / 2,by constructor <;> linarith [t.property.1,t.property.2]⟩
  continuous_toFun := by cases b <;> dsimp <;> fun_prop
@[simp] theorem half_false_zero : half false 0 = 0 := Subtype.ext (by norm_num [half])
@[simp] theorem half_true_one : half true 1 = 1 := Subtype.ext (by norm_num [half])
theorem half_mid : half false 1 = half true 0 := Subtype.ext (by norm_num [half])

def cut₁ (σ : Cube₁ X) (i : Bool) : Cube₁ X := σ.comp (half i)
def cut₂ (σ : Cube₂ X) (i j : Bool) : Cube₂ X :=
  ⟨fun t => σ (half i t.1,half j t.2),by fun_prop⟩
def cut₃ (σ : Cube₃ X) (i j k : Bool) : Cube₃ X :=
  ⟨fun t => σ (half i t.1,half j t.2.1,half k t.2.2),by fun_prop⟩

def S₁ : C₁ X →ₗ[ℤ] C₁ X := Finsupp.linearCombination ℤ
  (fun σ => ∑ i : Bool, Finsupp.single (cut₁ σ i) 1)
def S₂ : C₂ X →ₗ[ℤ] C₂ X := Finsupp.linearCombination ℤ
  (fun σ => ∑ i : Bool, ∑ j : Bool, Finsupp.single (cut₂ σ i j) 1)
def S₃ : C₃ X →ₗ[ℤ] C₃ X := Finsupp.linearCombination ℤ
  (fun σ => ∑ i : Bool, ∑ j : Bool, ∑ k : Bool, Finsupp.single (cut₃ σ i j k) 1)

@[simp] theorem S₁_single (σ : Cube₁ X) (a : ℤ) :
    S₁ (Finsupp.single σ a) = ∑ i : Bool, Finsupp.single (cut₁ σ i) a := by
  simp [S₁,Finsupp.smul_single]
@[simp] theorem S₂_single (σ : Cube₂ X) (a : ℤ) :
    S₂ (Finsupp.single σ a) = ∑ i : Bool, ∑ j : Bool, Finsupp.single (cut₂ σ i j) a := by
  simp [S₂,Finsupp.smul_single]
@[simp] theorem S₃_single (σ : Cube₃ X) (a : ℤ) :
    S₃ (Finsupp.single σ a) = ∑ i : Bool, ∑ j : Bool, ∑ k : Bool, Finsupp.single (cut₃ σ i j k) a := by
  simp [S₃,Finsupp.smul_single]

@[simp] theorem edge₁_cut₂ (σ : Cube₂ X) (i j : Bool) (a : I) :
    edge₁ (cut₂ σ i j) a = cut₁ (edge₁ σ (half i a)) j := rfl
@[simp] theorem edge₂_cut₂ (σ : Cube₂ X) (i j : Bool) (a : I) :
    edge₂ (cut₂ σ i j) a = cut₁ (edge₂ σ (half j a)) i := rfl
@[simp] theorem face₁_cut₃ (σ : Cube₃ X) (i j k : Bool) (a : I) :
    face₁ (cut₃ σ i j k) a = cut₂ (face₁ σ (half i a)) j k := rfl
@[simp] theorem face₂_cut₃ (σ : Cube₃ X) (i j k : Bool) (a : I) :
    face₂ (cut₃ σ i j k) a = cut₂ (face₂ σ (half j a)) i k := rfl
@[simp] theorem face₃_cut₃ (σ : Cube₃ X) (i j k : Bool) (a : I) :
    face₃ (cut₃ σ i j k) a = cut₂ (face₃ σ (half k a)) i j := rfl

theorem b₁_subdivision : b₁.comp (S₁ : C₁ X →ₗ[ℤ] C₁ X) = b₁ := by
  apply Finsupp.lhom_ext
  intro σ a
  simp [cut₁,half_mid,smul_sub,Finsupp.smul_single]

theorem b₂_subdivision : b₂.comp (S₂ : C₂ X →ₗ[ℤ] C₂ X) = S₁.comp b₂ := by
  apply Finsupp.lhom_ext
  intro σ a
  simp only [LinearMap.comp_apply,S₂_single,Fintype.sum_bool,map_add,b₂_single,edge₁_cut₂,
    edge₂_cut₂,half_false_zero,half_true_one,half_mid,map_sub,S₁_single,
    smul_add,smul_sub,Finsupp.smul_single,smul_eq_mul,mul_one]
  abel

theorem b₃_subdivision : b₃.comp (S₃ : C₃ X →ₗ[ℤ] C₃ X) = S₂.comp b₃ := by
  apply Finsupp.lhom_ext
  intro σ a
  simp only [LinearMap.comp_apply,S₃_single,Fintype.sum_bool,map_add,b₃_single,face₁_cut₃,
    face₂_cut₃,face₃_cut₃,half_false_zero,half_true_one,half_mid,map_sub,S₂_single,
    smul_add,smul_sub,Finsupp.smul_single,smul_eq_mul,mul_one]
  abel

@[simp] theorem cut₁_comp (f : C(X,Y)) (σ : Cube₁ X) (i : Bool) :
    cut₁ (f.comp σ) i = f.comp (cut₁ σ i) := rfl
@[simp] theorem cut₂_comp (f : C(X,Y)) (σ : Cube₂ X) (i j : Bool) :
    cut₂ (f.comp σ) i j = f.comp (cut₂ σ i j) := rfl
@[simp] theorem cut₃_comp (f : C(X,Y)) (σ : Cube₃ X) (i j k : Bool) :
    cut₃ (f.comp σ) i j k = f.comp (cut₃ σ i j k) := rfl

theorem S₁_push (f : C(X,Y)) : S₁.comp (push₁ f) = (push₁ f).comp S₁ := by
  apply Finsupp.lhom_ext
  intro σ a
  simp

theorem S₂_push (f : C(X,Y)) : S₂.comp (push₂ f) = (push₂ f).comp S₂ := by
  apply Finsupp.lhom_ext
  intro σ a
  simp

@[simp] theorem cut₁_constant (x : X) (i : Bool) : cut₁ (constant₁ x) i = constant₁ x :=
  ContinuousMap.ext (fun _ => rfl)
@[simp] theorem cut₂_degenerate₁ (σ : Cube₁ X) (i j : Bool) :
    cut₂ (degenerate₁ σ) i j = degenerate₁ (cut₁ σ i) := rfl
@[simp] theorem cut₂_degenerate₂ (σ : Cube₁ X) (i j : Bool) :
    cut₂ (degenerate₂ σ) i j = degenerate₂ (cut₁ σ j) := rfl

theorem S₁_D₁ : D₁ X ≤ (D₁ X).comap S₁ := by
  apply Submodule.span_le.mpr
  rintro _ ⟨x,rfl⟩
  change S₁ (Finsupp.single (constant₁ x) 1) ∈ D₁ X
  rw [S₁_single]
  apply Submodule.sum_mem
  intro i hi
  simp only [cut₁_constant]
  exact Submodule.subset_span ⟨x,rfl⟩

theorem S₂_D₂ : D₂ X ≤ (D₂ X).comap S₂ := by
  apply Submodule.span_le.mpr
  rintro _ (⟨σ,rfl⟩ | ⟨σ,rfl⟩)
  · change S₂ (Finsupp.single (degenerate₁ σ) 1) ∈ D₂ X
    rw [S₂_single]
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.sum_mem
    intro j hj
    simp only [cut₂_degenerate₁]
    exact Submodule.subset_span (Or.inl ⟨_,rfl⟩)
  · change S₂ (Finsupp.single (degenerate₂ σ) 1) ∈ D₂ X
    rw [S₂_single]
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.sum_mem
    intro j hj
    simp only [cut₂_degenerate₂]
    exact Submodule.subset_span (Or.inr ⟨_,rfl⟩)

def SN₁ : N₁ X →ₗ[ℤ] N₁ X := (D₁ X).mapQ (D₁ X) S₁ S₁_D₁
def SN₂ : N₂ X →ₗ[ℤ] N₂ X := (D₂ X).mapQ (D₂ X) S₂ S₂_D₂
@[simp] theorem SN₁_mk (c : C₁ X) : SN₁ ((D₁ X).mkQ c) = (D₁ X).mkQ (S₁ c) := rfl
@[simp] theorem SN₂_mk (c : C₂ X) : SN₂ ((D₂ X).mkQ c) = (D₂ X).mkQ (S₂ c) := rfl

theorem d₁_subdivision (c : N₁ X) : d₁ (SN₁ c) = d₁ c := by
  obtain ⟨c,rfl⟩ := (D₁ X).mkQ_surjective c
  exact LinearMap.congr_fun b₁_subdivision c

theorem d₂_subdivision (c : N₂ X) : d₂ (SN₂ c) = SN₁ (d₂ c) := by
  obtain ⟨c,rfl⟩ := (D₂ X).mkQ_surjective c
  change (D₁ X).mkQ (b₂ (S₂ c)) = (D₁ X).mkQ (S₁ (b₂ c))
  exact congrArg (D₁ X).mkQ (LinearMap.congr_fun b₂_subdivision c)

theorem d₃_subdivision (c : C₃ X) : d₃ (S₃ c) = SN₂ (d₃ c) := by
  change (D₂ X).mkQ (b₃ (S₃ c)) = (D₂ X).mkQ (S₂ (b₃ c))
  exact congrArg (D₂ X).mkQ (LinearMap.congr_fun b₃_subdivision c)

theorem SN₁_push (f : C(X,Y)) (c : N₁ X) : SN₁ (pushN₁ f c) = pushN₁ f (SN₁ c) := by
  obtain ⟨c,rfl⟩ := (D₁ X).mkQ_surjective c
  change (D₁ Y).mkQ (S₁ (push₁ f c)) = (D₁ Y).mkQ (push₁ f (S₁ c))
  exact congrArg (D₁ Y).mkQ (LinearMap.congr_fun (S₁_push f) c)

theorem SN₂_push (f : C(X,Y)) (c : N₂ X) : SN₂ (pushN₂ f c) = pushN₂ f (SN₂ c) := by
  obtain ⟨c,rfl⟩ := (D₂ X).mkQ_surjective c
  change (D₂ Y).mkQ (S₂ (push₂ f c)) = (D₂ Y).mkQ (push₂ f (S₂ c))
  exact congrArg (D₂ Y).mkQ (LinearMap.congr_fun (S₂_push f) c)

end EilenbergGanea.CubicalSingular

namespace EilenbergGanea.CubicalSingular
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def gen₁ (σ : Cube₁ X) : N₁ X := (D₁ X).mkQ (Finsupp.single σ 1)
def gen₂ (σ : Cube₂ X) : N₂ X := (D₂ X).mkQ (Finsupp.single σ 1)
@[simp] theorem pushN₁_gen (f : C(X,Y)) (σ : Cube₁ X) : pushN₁ f (gen₁ σ) = gen₁ (f.comp σ) := by
  rw [gen₁,pushN₁_mk,push₁_single]
  rfl
@[simp] theorem pushN₂_gen (f : C(X,Y)) (σ : Cube₂ X) : pushN₂ f (gen₂ σ) = gen₂ (f.comp σ) := by
  rw [gen₂,pushN₂_mk,push₂_single]
  rfl

local instance instContractibleSpaceElemRealI : ContractibleSpace I :=
  (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0,by norm_num⟩

def subdivisionFiller₁ : N₂ I :=
  (exact₁_of_contractible (SN₁ (gen₁ (ContinuousMap.id I)) - gen₁ (ContinuousMap.id I))
    (by rw [map_sub,d₁_subdivision,sub_self])).choose

theorem subdivisionFiller₁_boundary : d₂ subdivisionFiller₁ =
    SN₁ (gen₁ (ContinuousMap.id I)) - gen₁ (ContinuousMap.id I) :=
  (exact₁_of_contractible (SN₁ (gen₁ (ContinuousMap.id I)) - gen₁ (ContinuousMap.id I))
    (by rw [map_sub,d₁_subdivision,sub_self])).choose_spec

def H₁raw : C₁ X →ₗ[ℤ] N₂ X := Finsupp.linearCombination ℤ
  (fun σ => pushN₂ σ subdivisionFiller₁)
@[simp] theorem H₁raw_single (σ : Cube₁ X) (a : ℤ) :
    H₁raw (Finsupp.single σ a) = a • pushN₂ σ subdivisionFiller₁ := by simp [H₁raw]

theorem H₁raw_D₁ : D₁ X ≤ LinearMap.ker H₁raw := by
  apply Submodule.span_le.mpr
  rintro _ ⟨x,rfl⟩
  change H₁raw (Finsupp.single (constant₁ x) 1) = 0
  simp [constant₁]

def H₁ : N₁ X →ₗ[ℤ] N₂ X := (D₁ X).liftQ H₁raw H₁raw_D₁
@[simp] theorem H₁_mk (c : C₁ X) : H₁ ((D₁ X).mkQ c) = H₁raw c := rfl

theorem subdivision_homotopy₁ (c : N₁ X) : d₂ (H₁ c) = SN₁ c - c := by
  obtain ⟨c,rfl⟩ := (D₁ X).mkQ_surjective c
  have he : d₂.comp (H₁raw : C₁ X →ₗ[ℤ] N₂ X) =
      (SN₁ - LinearMap.id).comp (D₁ X).mkQ := by
    apply Finsupp.lhom_ext
    intro σ a
    simp only [LinearMap.comp_apply,H₁raw_single,map_smul,d₂_push,subdivisionFiller₁_boundary,
      map_sub,← SN₁_push,pushN₁_gen,ContinuousMap.comp_id]
    change a • (SN₁ (gen₁ σ) - gen₁ σ) = SN₁ ((D₁ X).mkQ (Finsupp.single σ a)) -
      (D₁ X).mkQ (Finsupp.single σ a)
    rw [← Finsupp.smul_single_one σ a,map_smul,map_smul,smul_sub]
    rfl
  exact LinearMap.congr_fun he c

end EilenbergGanea.CubicalSingular

namespace EilenbergGanea.CubicalSingular
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def bad₁ (X : Type*) [TopologicalSpace X] : Set (Cube₁ X) := Set.range constant₁
def bad₂ (X : Type*) [TopologicalSpace X] : Set (Cube₂ X) :=
  Set.range degenerate₁ ∪ Set.range degenerate₂

theorem D₁_supported : D₁ X = Finsupp.supported ℤ ℤ (bad₁ X) := by
  rw [Finsupp.supported_eq_span_single]
  unfold D₁ bad₁
  congr 1
  ext c
  simp only [Set.mem_range,Set.mem_image]
  aesop

theorem D₂_supported : D₂ X = Finsupp.supported ℤ ℤ (bad₂ X) := by
  rw [Finsupp.supported_eq_span_single]
  unfold D₂ bad₂
  rw [Set.image_union]
  congr 1
  ext c
  simp only [Set.mem_union,Set.mem_range,Set.mem_image]
  aesop

def cubeSet (D : Type*) [TopologicalSpace D] (U : Set X) : Set C(D,X) :=
  {σ | Set.range σ ⊆ U}

theorem cubeSet_mono {D : Type*} [TopologicalSpace D] {U V : Set X} (h : U ⊆ V) :
    cubeSet D U ⊆ cubeSet D V := fun _ hσ => hσ.trans h

@[simp] theorem cubeSet_inter (D : Type*) [TopologicalSpace D] (U V : Set X) :
    cubeSet D (U ∩ V) = cubeSet D U ∩ cubeSet D V := by
  ext σ
  exact Set.subset_inter_iff

@[simp] theorem cubeSet_univ (D : Type*) [TopologicalSpace D] :
    cubeSet D (Set.univ : Set X) = Set.univ := by ext; simp [cubeSet]

def inc (U : Set X) : C(U,X) := ⟨Subtype.val,continuous_subtype_val⟩

theorem range_comp_inc (D : Type*) [TopologicalSpace D] (U : Set X) :
    Set.range (fun σ : C(D,U) => (inc U).comp σ) = cubeSet D U := by
  ext σ
  constructor
  · rintro ⟨σ,rfl⟩ _ ⟨t,rfl⟩
    exact (σ t).property
  · intro hσ
    refine ⟨⟨fun t => ⟨σ t,hσ ⟨t,rfl⟩⟩,σ.continuous.subtype_mk _⟩,?_⟩
    rfl

def raw₁ (U : Set X) : Submodule ℤ (C₁ X) := Finsupp.supported ℤ ℤ (cubeSet I U)
def raw₂ (U : Set X) : Submodule ℤ (C₂ X) := Finsupp.supported ℤ ℤ (cubeSet (I × I) U)
def L₁ (U : Set X) : Submodule ℤ (N₁ X) := (raw₁ U).map (D₁ X).mkQ
def L₂ (U : Set X) : Submodule ℤ (N₂ X) := (raw₂ U).map (D₂ X).mkQ
def L₃ (U : Set X) : Submodule ℤ (C₃ X) := Finsupp.supported ℤ ℤ (cubeSet (I × I × I) U)

theorem supported_quotient_inter {A : Type*} (D : Submodule ℤ (A →₀ ℤ))
    (bad s t : Set A) (hD : D = Finsupp.supported ℤ ℤ bad) :
    (Finsupp.supported ℤ ℤ (s ∩ t)).map D.mkQ =
      (Finsupp.supported ℤ ℤ s).map D.mkQ ⊓ (Finsupp.supported ℤ ℤ t).map D.mkQ := by
  apply Submodule.comap_injective_of_surjective D.mkQ_surjective
  rw [Submodule.comap_inf,Submodule.comap_map_eq,Submodule.comap_map_eq,
    Submodule.comap_map_eq,Submodule.ker_mkQ,hD,← Finsupp.supported_union,
    ← Finsupp.supported_union,← Finsupp.supported_union,← Finsupp.supported_inter]
  congr 1
  ext x
  simp only [mem_union,mem_inter_iff]
  tauto

@[simp] theorem L₁_inter (U V : Set X) : L₁ (U ∩ V) = L₁ U ⊓ L₁ V := by
  unfold L₁ raw₁
  rw [cubeSet_inter]
  exact supported_quotient_inter _ _ _ _ D₁_supported
@[simp] theorem L₂_inter (U V : Set X) : L₂ (U ∩ V) = L₂ U ⊓ L₂ V := by
  unfold L₂ raw₂
  rw [cubeSet_inter]
  exact supported_quotient_inter _ _ _ _ D₂_supported
@[simp] theorem L₃_inter (U V : Set X) : L₃ (U ∩ V) = L₃ U ⊓ L₃ V := by
  unfold L₃
  rw [cubeSet_inter,Finsupp.supported_inter]

theorem L₁_mono {U V : Set X} (h : U ⊆ V) : L₁ U ≤ L₁ V :=
  Submodule.map_mono (Finsupp.supported_mono (cubeSet_mono h))
theorem L₂_mono {U V : Set X} (h : U ⊆ V) : L₂ U ≤ L₂ V :=
  Submodule.map_mono (Finsupp.supported_mono (cubeSet_mono h))

theorem L₁_span (U : Set X) : L₁ U = Submodule.span ℤ (gen₁ '' cubeSet I U) := by
  rw [L₁,raw₁,Finsupp.supported_eq_span_single,Submodule.map_span,← Set.image_comp]
  rfl

theorem L₂_span (U : Set X) : L₂ U = Submodule.span ℤ (gen₂ '' cubeSet (I × I) U) := by
  rw [L₂,raw₂,Finsupp.supported_eq_span_single,Submodule.map_span,← Set.image_comp]
  rfl

theorem gen₁_mem {U : Set X} {σ : Cube₁ X} (hσ : σ ∈ cubeSet I U) : gen₁ σ ∈ L₁ U := by
  rw [L₁_span]
  exact Submodule.subset_span ⟨σ,hσ,rfl⟩
theorem gen₂_mem {U : Set X} {σ : Cube₂ X} (hσ : σ ∈ cubeSet (I × I) U) : gen₂ σ ∈ L₂ U := by
  rw [L₂_span]
  exact Submodule.subset_span ⟨σ,hσ,rfl⟩

theorem d₂_support (U : Set X) : L₂ U ≤ (L₁ U).comap d₂ := by
  rw [L₂_span]
  apply Submodule.span_le.mpr
  rintro _ ⟨σ,hσ,rfl⟩
  change (D₁ X).mkQ (b₂ (Finsupp.single σ 1)) ∈ L₁ U
  rw [b₂_single,one_smul,map_add,map_sub,map_sub]
  apply Submodule.add_mem
  · apply Submodule.sub_mem
    · apply Submodule.sub_mem
      · exact gen₁_mem (by rintro _ ⟨t,rfl⟩; exact hσ ⟨(1,t),rfl⟩)
      · exact gen₁_mem (by rintro _ ⟨t,rfl⟩; exact hσ ⟨(0,t),rfl⟩)
    · exact gen₁_mem (by rintro _ ⟨t,rfl⟩; exact hσ ⟨(t,1),rfl⟩)
  · exact gen₁_mem (by rintro _ ⟨t,rfl⟩; exact hσ ⟨(t,0),rfl⟩)

theorem d₃_support (U : Set X) : L₃ U ≤ (L₂ U).comap d₃ := by
  rw [L₃,Finsupp.supported_eq_span_single]
  apply Submodule.span_le.mpr
  rintro _ ⟨σ,hσ,rfl⟩
  change (D₂ X).mkQ (b₃ (Finsupp.single σ 1)) ∈ L₂ U
  simp only [b₃_single,one_smul,map_sub,map_add]
  apply Submodule.sub_mem
  · apply Submodule.add_mem
    · apply Submodule.add_mem
      · apply Submodule.sub_mem
        · apply Submodule.sub_mem
          · exact gen₂_mem (by rintro _ ⟨t,rfl⟩; exact hσ ⟨(1,t),rfl⟩)
          · exact gen₂_mem (by rintro _ ⟨t,rfl⟩; exact hσ ⟨(0,t),rfl⟩)
        · exact gen₂_mem (by rintro _ ⟨t,rfl⟩; exact hσ ⟨(t.1,1,t.2),rfl⟩)
      · exact gen₂_mem (by rintro _ ⟨t,rfl⟩; exact hσ ⟨(t.1,0,t.2),rfl⟩)
    · exact gen₂_mem (by rintro _ ⟨t,rfl⟩; exact hσ ⟨(t.1,t.2,1),rfl⟩)
  · exact gen₂_mem (by rintro _ ⟨t,rfl⟩; exact hσ ⟨(t.1,t.2,0),rfl⟩)

end EilenbergGanea.CubicalSingular


open Classical Set
namespace EilenbergGanea.NormalizedSupport
variable {A : Type*}


variable {B : Type*}
theorem comap_supported_of_injective (f : A → B) (hf : Function.Injective f) (s : Set B) :
    (Finsupp.supported ℤ ℤ s).comap (Finsupp.lmapDomain ℤ ℤ f) =
      Finsupp.supported ℤ ℤ (f ⁻¹' s) := by
  ext c
  change Finsupp.mapDomain f c ∈ Finsupp.supported ℤ ℤ s ↔
    c ∈ Finsupp.supported ℤ ℤ (f ⁻¹' s)
  rw [Finsupp.mem_supported,Finsupp.mem_supported,Finsupp.mapDomain_support_of_injective hf]
  simp

end EilenbergGanea.NormalizedSupport

namespace EilenbergGanea.CubicalSingular
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem compose_injective {D : Type*} [TopologicalSpace D] (f : C(X,Y))
    (hf : Function.Injective f) : Function.Injective (fun σ : C(D,X) => f.comp σ) := by
  intro σ τ h
  exact ContinuousMap.ext (fun x => hf (congrArg (fun a : C(D,Y) => a x) h))

theorem preimage_bad₁ (f : C(X,Y)) (hf : Function.Injective f) :
    (fun σ : Cube₁ X => f.comp σ) ⁻¹' bad₁ Y = bad₁ X := by
  ext σ
  constructor
  · rintro ⟨y,hy⟩
    refine ⟨σ 0,ContinuousMap.ext (fun t => ?_)⟩
    apply hf
    have h₀ := congrArg (fun a : Cube₁ Y => a 0) hy
    have ht := congrArg (fun a : Cube₁ Y => a t) hy
    exact h₀.symm.trans ht
  · rintro ⟨x,rfl⟩
    exact ⟨f x,rfl⟩

theorem push₀_lmapDomain (f : C(X,Y)) :
    push₀ f = Finsupp.lmapDomain ℤ ℤ (f) := by
  apply Finsupp.lhom_ext
  intro σ a
  simp

theorem push₁_lmapDomain (f : C(X,Y)) :
    push₁ f = Finsupp.lmapDomain ℤ ℤ (fun σ => f.comp σ) := by
  apply Finsupp.lhom_ext
  intro σ a
  simp

theorem push₂_lmapDomain (f : C(X,Y)) :
    push₂ f = Finsupp.lmapDomain ℤ ℤ (fun σ => f.comp σ) := by
  apply Finsupp.lhom_ext
  intro σ a
  simp

theorem push₀_injective (f : C(X,Y)) (hf : Function.Injective f) :
    Function.Injective (push₀ f) := by
  rw [push₀_lmapDomain]
  exact Finsupp.mapDomain_injective hf

theorem pushN₁_injective (f : C(X,Y)) (hf : Function.Injective f) :
    Function.Injective (pushN₁ f) := by
  apply LinearMap.ker_eq_bot.mp
  change LinearMap.ker ((D₁ X).mapQ (D₁ Y) (push₁ f) _) = ⊥
  rw [Submodule.ker_mapQ]
  have h : (D₁ Y).comap (push₁ f) = D₁ X := by
    rw [D₁_supported,D₁_supported]
    rw [push₁_lmapDomain]
    rw [NormalizedSupport.comap_supported_of_injective _ (compose_injective f hf),preimage_bad₁ f hf]
  rw [h]
  simp

theorem range_push₁_inc (U : Set X) : (push₁ (inc U)).range = raw₁ U := by
  rw [push₁_lmapDomain]
  have h := Finsupp.lmapDomain_supported ℤ ℤ (fun σ : Cube₁ U => (inc U).comp σ) Set.univ
  rw [Finsupp.supported_univ,Submodule.map_top,Set.image_univ,range_comp_inc] at h
  exact h

theorem range_push₂_inc (U : Set X) : (push₂ (inc U)).range = raw₂ U := by
  rw [push₂_lmapDomain]
  have h := Finsupp.lmapDomain_supported ℤ ℤ (fun σ : Cube₂ U => (inc U).comp σ) Set.univ
  rw [Finsupp.supported_univ,Submodule.map_top,Set.image_univ,range_comp_inc] at h
  exact h

theorem range_pushN₁_inc (U : Set X) : (pushN₁ (inc U)).range = L₁ U := by
  ext z
  constructor
  · rintro ⟨c,rfl⟩
    obtain ⟨c,rfl⟩ := (D₁ U).mkQ_surjective c
    rw [pushN₁_mk]
    refine ⟨push₁ (inc U) c,?_,rfl⟩
    rw [← range_push₁_inc]
    exact ⟨c,rfl⟩
  · rintro ⟨c,hc,rfl⟩
    rw [← range_push₁_inc] at hc
    obtain ⟨c,rfl⟩ := hc
    exact ⟨(D₁ U).mkQ c,rfl⟩

theorem range_pushN₂_inc (U : Set X) : (pushN₂ (inc U)).range = L₂ U := by
  ext z
  constructor
  · rintro ⟨c,rfl⟩
    obtain ⟨c,rfl⟩ := (D₂ U).mkQ_surjective c
    rw [pushN₂_mk]
    refine ⟨push₂ (inc U) c,?_,rfl⟩
    rw [← range_push₂_inc]
    exact ⟨c,rfl⟩
  · rintro ⟨c,hc,rfl⟩
    rw [← range_push₂_inc] at hc
    obtain ⟨c,rfl⟩ := hc
    exact ⟨(D₂ U).mkQ c,rfl⟩

theorem pushN₂_support (f : C(X,Y)) {U : Set Y} (hf : Set.range f ⊆ U) (c : N₂ X) :
    pushN₂ f c ∈ L₂ U := by
  let f' : C(X,U) := ⟨fun x => ⟨f x,hf ⟨x,rfl⟩⟩,f.continuous.subtype_mk _⟩
  have h : f = (inc U).comp f' := rfl
  rw [h,pushN₂_comp,← range_pushN₂_inc]
  exact ⟨pushN₂ f' c,rfl⟩

theorem H₁_support (U : Set X) : L₁ U ≤ (L₂ U).comap H₁ := by
  rw [L₁_span]
  apply Submodule.span_le.mpr
  rintro _ ⟨σ,hσ,rfl⟩
  change H₁raw (Finsupp.single σ 1) ∈ L₂ U
  rw [H₁raw_single,one_smul]
  exact pushN₂_support σ hσ _

end EilenbergGanea.CubicalSingular

open Classical Set
namespace EilenbergGanea.CubicalMesh
variable {D X : Type*} [MetricSpace D] [CompactSpace D] [Nonempty D] [TopologicalSpace X]
variable {κ : Type*} [Fintype κ]

abbrev Chains (D X : Type*) [TopologicalSpace D] [TopologicalSpace X] := C(D,X) →₀ ℤ

def small (U : Set (Set X)) : Set C(D,X) := {σ | ∃ u ∈ U, Set.range σ ⊆ u}
def subchains (U : Set (Set X)) : Submodule ℤ (Chains D X) := Finsupp.supported ℤ ℤ (small U)

def subdivision (a : κ → C(D,D)) : Chains D X →ₗ[ℤ] Chains D X :=
  Finsupp.linearCombination ℤ (fun σ => ∑ i, Finsupp.single (σ.comp (a i)) 1)

omit [CompactSpace D] [Nonempty D] in
@[simp] theorem subdivision_single (a : κ → C(D,D)) (σ : C(D,X)) (z : ℤ) :
    subdivision a (Finsupp.single σ z) = ∑ i, Finsupp.single (σ.comp (a i)) z := by
  simp [subdivision,Finset.smul_sum,Finsupp.smul_single]

def shrinking (r : ℝ) (σ : C(D,X)) (n : ℕ) : Set C(D,X) :=
  {τ | ∃ f : C(D,D), (∀ x y, dist (f x) (f y) ≤ r ^ n * dist x y) ∧ τ = σ.comp f}

omit [CompactSpace D] [Nonempty D] in
theorem iterate_parametrized (a : κ → C(D,D)) {r : ℝ} (hr : 0 ≤ r)
    (ha : ∀ i x y, dist (a i x) (a i y) ≤ r * dist x y) (σ : C(D,X)) (n : ℕ) :
    ((subdivision a)^[n]) (Finsupp.single σ 1) ∈ Finsupp.supported ℤ ℤ (shrinking r σ n) := by
  induction n with
  | zero =>
    apply Finsupp.single_mem_supported
    refine ⟨ContinuousMap.id D,?_,?_⟩
    · intro x y
      simp
    · simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have hm : Finsupp.supported ℤ ℤ (shrinking r σ n) ≤
        (Finsupp.supported ℤ ℤ (shrinking r σ (n+1))).comap (subdivision a) := by
      apply le_trans (le_of_eq (Finsupp.supported_eq_span_single ℤ (shrinking r σ n)))
      apply Submodule.span_le.mpr
      rintro _ ⟨τ,⟨f,hf,rfl⟩,rfl⟩
      change subdivision a (Finsupp.single (σ.comp f) 1) ∈ Finsupp.supported ℤ ℤ (shrinking r σ (n+1))
      rw [subdivision_single]
      apply Submodule.sum_mem
      intro i hi
      apply Finsupp.single_mem_supported
      refine ⟨f.comp (a i),?_,rfl⟩
      intro x y
      calc
        dist (f (a i x)) (f (a i y)) ≤ r ^ n * dist (a i x) (a i y) := hf _ _
        _ ≤ r ^ n * (r * dist x y) := mul_le_mul_of_nonneg_left (ha i x y) (pow_nonneg hr n)
        _ = r ^ (n+1) * dist x y := by rw [pow_succ,mul_assoc]
    exact hm ih

theorem shrinking_small (hD : ∀ x y : D, dist x y ≤ 1) {r : ℝ} (hr : r < 1)
    (U : Set (Set X)) (hU : ∀ u ∈ U, IsOpen u) (hcover : ⋃₀ U = Set.univ) (σ : C(D,X)) :
    ∃ N : ℕ, ∀ n, N ≤ n → 0 ≤ r → shrinking r σ n ⊆ small U := by
  obtain ⟨δ,hδ,hLeb⟩ := lebesgue_number_lemma_of_metric (s := Set.univ)
    (c := fun u : U => σ ⁻¹' (u : Set X)) isCompact_univ
    (fun u => (hU u u.property).preimage σ.continuous) (by
      intro x hx
      have : σ x ∈ ⋃₀ U := hcover ▸ Set.mem_univ _
      obtain ⟨u,hu,hx⟩ := this
      exact Set.mem_iUnion.mpr ⟨⟨u,hu⟩,hx⟩)
  obtain ⟨N,hN⟩ := exists_pow_lt_of_lt_one hδ hr
  refine ⟨N,fun n hn hr0 τ hτ => ?_⟩
  obtain ⟨f,hf,rfl⟩ := hτ
  let x₀ : D := Classical.choice inferInstance
  obtain ⟨u,hu⟩ := hLeb (f x₀) trivial
  refine ⟨u,u.property,?_⟩
  rintro _ ⟨x,rfl⟩
  apply hu
  change dist (f x) (f x₀) < δ
  calc
    dist (f x) (f x₀) ≤ r ^ n * dist x x₀ := hf _ _
    _ ≤ r ^ n * 1 := mul_le_mul_of_nonneg_left (hD _ _) (pow_nonneg hr0 n)
    _ = r ^ n := mul_one _
    _ ≤ r ^ N := pow_le_pow_of_le_one hr0 hr.le hn
    _ < δ := hN

theorem single_eventually_small (a : κ → C(D,D)) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1)
    (ha : ∀ i x y, dist (a i x) (a i y) ≤ r * dist x y)
    (hD : ∀ x y : D, dist x y ≤ 1)
    (U : Set (Set X)) (hU : ∀ u ∈ U, IsOpen u) (hcover : ⋃₀ U = Set.univ) (σ : C(D,X)) :
    ∃ N : ℕ, ∀ n, N ≤ n → ((subdivision a)^[n]) (Finsupp.single σ 1) ∈ subchains U := by
  obtain ⟨N,hN⟩ := shrinking_small hD hr U hU hcover σ
  exact ⟨N,fun n hn => Finsupp.supported_mono (hN n hn hr0) (iterate_parametrized a hr0 ha σ n)⟩

theorem chain_eventually_small (a : κ → C(D,D)) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1)
    (ha : ∀ i x y, dist (a i x) (a i y) ≤ r * dist x y)
    (hD : ∀ x y : D, dist x y ≤ 1)
    (U : Set (Set X)) (hU : ∀ u ∈ U, IsOpen u) (hcover : ⋃₀ U = Set.univ) (c : Chains D X) :
    ∃ N : ℕ, ∀ n, N ≤ n → ((subdivision a)^[n]) c ∈ subchains U := by
  classical
  induction c using Finsupp.induction_linear with
  | zero =>
    refine ⟨0,fun n hn => ?_⟩
    have hz : ((subdivision a)^[n]) (0 : Chains D X) = 0 := by
      clear hn
      induction n with
      | zero => rfl
      | succ n ih => rw [Function.iterate_succ_apply',ih,map_zero]
    rw [hz]
    exact Submodule.zero_mem _
  | add c d hc hd =>
    obtain ⟨N,hN⟩ := hc
    obtain ⟨M,hM⟩ := hd
    refine ⟨max N M,fun n hn => ?_⟩
    have hadd : ((subdivision a)^[n]) (c+d) =
        ((subdivision a)^[n]) c + ((subdivision a)^[n]) d := by
      clear hn
      induction n with
      | zero => rfl
      | succ n ih => simp only [Function.iterate_succ_apply',ih,map_add]
    rw [hadd]
    exact Submodule.add_mem _ (hN n ((le_max_left _ _).trans hn)) (hM n ((le_max_right _ _).trans hn))
  | single σ z =>
    obtain ⟨N,hN⟩ := single_eventually_small a hr0 hr ha hD U hU hcover σ
    refine ⟨N,fun n hn => ?_⟩
    have hsmul : ((subdivision a)^[n]) (Finsupp.single σ z) =
        z • ((subdivision a)^[n]) (Finsupp.single σ 1) := by
      clear hn
      induction n with
      | zero => simp [Finsupp.smul_single]
      | succ n ih => simp only [Function.iterate_succ_apply',ih,map_smul]
    rw [hsmul]
    exact Submodule.smul_mem _ z (hN n hn)

end EilenbergGanea.CubicalMesh

namespace EilenbergGanea.CubicalSingular
variable {X : Type*} [TopologicalSpace X]

theorem half_dist (b : Bool) (x y : I) : dist (half b x) (half b y) = (1/2:ℝ) * dist x y := by
  have h : (half b x : ℝ) - (half b y : ℝ) = (1/2:ℝ) * ((x:ℝ) - (y:ℝ)) := by
    cases b <;> simp only [half,Bool.false_eq_true,ite_false,ite_true,ContinuousMap.coe_mk] <;> ring
  change |(half b x : ℝ) - (half b y : ℝ)| = (1/2:ℝ) * |(x:ℝ) - (y:ℝ)|
  rw [h,abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 1/2)]

theorem interval_diameter (x y : I) : dist x y ≤ 1 := by
  rw [Subtype.dist_eq,Real.dist_eq,abs_le]
  constructor <;> linarith [x.property.1,x.property.2,y.property.1,y.property.2]

def half₂ (b : Bool × Bool) : C(I × I,I × I) :=
  ⟨fun t => (half b.1 t.1,half b.2 t.2),by fun_prop⟩
def half₃ (b : Bool × Bool × Bool) : C(I × I × I,I × I × I) :=
  ⟨fun t => (half b.1 t.1,half b.2.1 t.2.1,half b.2.2 t.2.2),by fun_prop⟩

theorem half₂_dist (b : Bool × Bool) (x y : I × I) :
    dist (half₂ b x) (half₂ b y) ≤ (1/2:ℝ) * dist x y := by
  simp only [half₂,ContinuousMap.coe_mk,Prod.dist_eq,half_dist]
  rw [max_le_iff]
  exact ⟨mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num),
    mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num)⟩

theorem half₃_dist (b : Bool × Bool × Bool) (x y : I × I × I) :
    dist (half₃ b x) (half₃ b y) ≤ (1/2:ℝ) * dist x y := by
  simp only [half₃,ContinuousMap.coe_mk,Prod.dist_eq,half_dist]
  rw [max_le_iff,max_le_iff]
  exact ⟨mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num),
    mul_le_mul_of_nonneg_left ((le_max_left _ _).trans (le_max_right _ _)) (by norm_num),
    mul_le_mul_of_nonneg_left ((le_max_right _ _).trans (le_max_right _ _)) (by norm_num)⟩

theorem S₂_mesh : (S₂ : C₂ X →ₗ[ℤ] C₂ X) = CubicalMesh.subdivision half₂ := by
  apply Finsupp.lhom_ext
  intro σ a
  simp only [S₂_single,CubicalMesh.subdivision_single,Fintype.sum_prod_type]
  rfl

theorem S₃_mesh : (S₃ : C₃ X →ₗ[ℤ] C₃ X) = CubicalMesh.subdivision half₃ := by
  apply Finsupp.lhom_ext
  intro σ a
  simp only [S₃_single,CubicalMesh.subdivision_single,Fintype.sum_prod_type]
  rfl

theorem small_pair (D : Type*) [MetricSpace D] (U V : Set X) :
    CubicalMesh.small (D := D) {U,V} = cubeSet D U ∪ cubeSet D V := by
  ext σ
  simp only [CubicalMesh.small,Set.mem_ofPred_eq,Set.mem_insert_iff,Set.mem_singleton_iff,
    Set.mem_union,cubeSet,exists_eq_or_imp,exists_eq_left]

theorem S₂_eventually_small (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = univ)
    (c : C₂ X) : ∃ N : ℕ, ∀ n, N ≤ n → (S₂^[n]) c ∈ raw₂ U ⊔ raw₂ V := by
  have h := CubicalMesh.chain_eventually_small half₂ (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1)
    half₂_dist (fun x y => max_le (interval_diameter x.1 y.1) (interval_diameter x.2 y.2)) {U,V}
    (by intro u hu; rcases hu with rfl | hu; exact hU; obtain rfl := hu; exact hV)
    (by simpa using hUV) c
  simpa only [← S₂_mesh,CubicalMesh.subchains,small_pair,Finsupp.supported_union,raw₂] using h

theorem S₃_eventually_small (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = univ)
    (c : C₃ X) : ∃ N : ℕ, ∀ n, N ≤ n → (S₃^[n]) c ∈ L₃ U ⊔ L₃ V := by
  have h := CubicalMesh.chain_eventually_small half₃ (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1)
    half₃_dist (fun x y => max_le (interval_diameter x.1 y.1)
      (max_le (interval_diameter x.2.1 y.2.1) (interval_diameter x.2.2 y.2.2))) {U,V}
    (by intro u hu; rcases hu with rfl | hu; exact hU; obtain rfl := hu; exact hV)
    (by simpa using hUV) c
  simpa only [← S₃_mesh,CubicalMesh.subchains,small_pair,Finsupp.supported_union,L₃] using h

theorem SN₂_iter_mk (c : C₂ X) (n : ℕ) :
    (SN₂^[n]) ((D₂ X).mkQ c) = (D₂ X).mkQ ((S₂^[n]) c) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply',ih,SN₂_mk]

theorem SN₂_eventually_small (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = univ)
    (c : N₂ X) : ∃ N : ℕ, ∀ n, N ≤ n → (SN₂^[n]) c ∈ L₂ U ⊔ L₂ V := by
  obtain ⟨c,rfl⟩ := (D₂ X).mkQ_surjective c
  obtain ⟨N,hN⟩ := S₂_eventually_small U V hU hV hUV c
  refine ⟨N,fun n hn => ?_⟩
  rw [SN₂_iter_mk,L₂,L₂,← Submodule.map_sup]
  exact ⟨_,hN n hn,rfl⟩

theorem SN₁_support (U : Set X) : L₁ U ≤ (L₁ U).comap SN₁ := by
  intro c hc
  rw [← range_pushN₁_inc] at hc
  obtain ⟨c,rfl⟩ := hc
  change SN₁ (pushN₁ (inc U) c) ∈ L₁ U
  rw [SN₁_push,← range_pushN₁_inc]
  exact ⟨SN₁ c,rfl⟩

theorem SN₂_support (U : Set X) : L₂ U ≤ (L₂ U).comap SN₂ := by
  intro c hc
  rw [← range_pushN₂_inc] at hc
  obtain ⟨c,rfl⟩ := hc
  change SN₂ (pushN₂ (inc U) c) ∈ L₂ U
  rw [SN₂_push,← range_pushN₂_inc]
  exact ⟨SN₂ c,rfl⟩

theorem SN₁_iter_support (U : Set X) {c : N₁ X} (hc : c ∈ L₁ U) (n : ℕ) : (SN₁^[n]) c ∈ L₁ U := by
  induction n with
  | zero => exact hc
  | succ n ih => rw [Function.iterate_succ_apply']; exact SN₁_support U ih

theorem SN₂_iter_support (U : Set X) {c : N₂ X} (hc : c ∈ L₂ U) (n : ℕ) : (SN₂^[n]) c ∈ L₂ U := by
  induction n with
  | zero => exact hc
  | succ n ih => rw [Function.iterate_succ_apply']; exact SN₂_support U ih

theorem d₂_SN₂_iter (c : N₂ X) (n : ℕ) : d₂ ((SN₂^[n]) c) = (SN₁^[n]) (d₂ c) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply',d₂_subdivision,ih]

theorem d₃_S₃_iter (c : C₃ X) (n : ℕ) : d₃ ((S₃^[n]) c) = (SN₂^[n]) (d₃ c) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply',d₃_subdivision,ih]

def K₁ : ℕ → N₁ X →ₗ[ℤ] N₂ X
  | 0 => 0
  | n+1 => H₁.comp (SN₁ ^ n) + K₁ n

theorem K₁_boundary (n : ℕ) (c : N₁ X) : d₂ (K₁ n c) = (SN₁^[n]) c - c := by
  induction n with
  | zero => simp [K₁]
  | succ n ih =>
    simp only [K₁,LinearMap.add_apply,LinearMap.comp_apply,map_add,subdivision_homotopy₁,ih]
    rw [Module.End.pow_apply,Function.iterate_succ_apply']
    abel

theorem K₁_support (U : Set X) {c : N₁ X} (hc : c ∈ L₁ U) (n : ℕ) : K₁ n c ∈ L₂ U := by
  induction n with
  | zero => exact Submodule.zero_mem _
  | succ n ih =>
    change H₁ ((SN₁ ^ n) c) + K₁ n c ∈ L₂ U
    rw [Module.End.pow_apply]
    exact Submodule.add_mem _ (H₁_support U (SN₁_iter_support U hc n)) ih

end EilenbergGanea.CubicalSingular


end

end OAI
end

section
-- module Solutions.OAIEG.Cubical_PathChains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Topology

namespace EilenbergGanea.PathTransport
open Set CubicalSingular
variable {X : Type*} [TopologicalSpace X] {G : Type*} [Group G]

structure Local (U : Set (Set X)) where
  value : Cube₁ X → G
  constant : ∀ x, value (ContinuousMap.const I x) = 1
  split : ∀ γ ∈ CubicalMesh.small U, value γ = value (cut₁ γ false) * value (cut₁ γ true)
  square : ∀ σ ∈ CubicalMesh.small U,
    value (edge₂ σ 0) * value (edge₁ σ 1) = value (edge₁ σ 0) * value (edge₂ σ 1)

namespace Local
variable {U : Set (Set X)} (l : Local (G:=G) U)

def fold : ℕ → Cube₁ X → G
  | 0, γ => l.value γ
  | n+1, γ => fold n (cut₁ γ false) * fold n (cut₁ γ true)

def Good₁ (n : ℕ) (γ : Cube₁ X) : Prop :=
  CubicalMesh.shrinking (1/2:ℝ) γ n ⊆ CubicalMesh.small U
def Good₂ (n : ℕ) (σ : Cube₂ X) : Prop :=
  CubicalMesh.shrinking (1/2:ℝ) σ n ⊆ CubicalMesh.small U

omit [Group G] in
theorem small_comp {D E : Type*} [MetricSpace D] [MetricSpace E]
    {γ : C(D,X)} (h : γ ∈ CubicalMesh.small U) (f : C(E,D)) :
    γ.comp f ∈ CubicalMesh.small U := by
  obtain ⟨u,hu,hγ⟩ := h
  refine ⟨u,hu,?_⟩
  rintro y ⟨x,hx⟩
  exact hx ▸ hγ ⟨f x,rfl⟩

omit [Group G] in
theorem good₁_zero {γ : Cube₁ X} (h : Good₁ (U:=U) 0 γ) : γ ∈ CubicalMesh.small U := by
  apply h
  exact ⟨ContinuousMap.id I,by simp,rfl⟩
omit [Group G] in
theorem good₂_zero {σ : Cube₂ X} (h : Good₂ (U:=U) 0 σ) : σ ∈ CubicalMesh.small U := by
  apply h
  exact ⟨ContinuousMap.id (I × I),by simp,rfl⟩

omit [Group G] in
theorem good₁_cut {n : ℕ} {γ : Cube₁ X} (h : Good₁ (U:=U) (n+1) γ) (b : Bool) :
    Good₁ (U:=U) n (cut₁ γ b) := by
  rintro τ ⟨f,hf,rfl⟩
  apply h
  refine ⟨(half b).comp f,?_,rfl⟩
  intro x y
  change dist (half b (f x)) (half b (f y)) ≤ _
  rw [half_dist]
  calc
    (1/2:ℝ) * dist (f x) (f y) ≤ (1/2:ℝ) * ((1/2:ℝ)^n * dist x y) :=
      mul_le_mul_of_nonneg_left (hf x y) (by norm_num)
    _ = (1/2:ℝ)^(n+1) * dist x y := by rw [pow_succ]; ring

omit [Group G] in
theorem good₂_cut {n : ℕ} {σ : Cube₂ X} (h : Good₂ (U:=U) (n+1) σ) (b c : Bool) :
    Good₂ (U:=U) n (cut₂ σ b c) := by
  rintro τ ⟨f,hf,rfl⟩
  apply h
  refine ⟨(half₂ (b,c)).comp f,?_,rfl⟩
  intro x y
  change dist (half₂ (b,c) (f x)) (half₂ (b,c) (f y)) ≤ _
  calc
    _ ≤ (1/2:ℝ) * dist (f x) (f y) := half₂_dist _ _ _
    _ ≤ (1/2:ℝ) * ((1/2:ℝ)^n * dist x y) := mul_le_mul_of_nonneg_left (hf x y) (by norm_num)
    _ = (1/2:ℝ)^(n+1) * dist x y := by rw [pow_succ]; ring

theorem fold_small {γ : Cube₁ X} (h : γ ∈ CubicalMesh.small U) (n : ℕ) :
    l.fold n γ = l.value γ := by
  induction n generalizing γ with
  | zero => rfl
  | succ n ih =>
    change l.fold n (cut₁ γ false) * l.fold n (cut₁ γ true) = _
    rw [ih (γ:=cut₁ γ false) (small_comp h _),ih (γ:=cut₁ γ true) (small_comp h _),← l.split γ h]

theorem fold_stable {n : ℕ} {γ : Cube₁ X} (h : Good₁ (U:=U) n γ) (m : ℕ) (hm : n ≤ m) :
    l.fold m γ = l.fold n γ := by
  induction n generalizing m γ with
  | zero => exact l.fold_small (good₁_zero h) m
  | succ n ih =>
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
    change l.fold k (cut₁ γ false) * l.fold k (cut₁ γ true) = _
    rw [ih (good₁_cut h false) k (by omega),ih (good₁_cut h true) k (by omega)]
    rfl

variable (hU : ∀ u ∈ U, IsOpen u) (hcover : ⋃₀ U = univ)
include hU hcover

omit [Group G] in
theorem good₁_eventually (γ : Cube₁ X) : ∀ᶠ n in Filter.atTop, Good₁ (U:=U) n γ := by
  obtain ⟨N,hN⟩ := CubicalMesh.shrinking_small interval_diameter (by norm_num : (1/2:ℝ) < 1) U hU hcover γ
  exact Filter.eventually_atTop.mpr ⟨N,fun n hn => hN n hn (by norm_num)⟩

omit [Group G] in
theorem good₂_eventually (σ : Cube₂ X) : ∀ᶠ n in Filter.atTop, Good₂ (U:=U) n σ := by
  obtain ⟨N,hN⟩ := CubicalMesh.shrinking_small
    (fun x y : I × I => by rw [Prod.dist_eq,max_le_iff]; exact ⟨interval_diameter _ _,interval_diameter _ _⟩)
    (by norm_num : (1/2:ℝ) < 1) U hU hcover σ
  exact Filter.eventually_atTop.mpr ⟨N,fun n hn => hN n hn (by norm_num)⟩

def depth (γ : Cube₁ X) : ℕ := ((good₁_eventually hU hcover γ).exists).choose

theorem depth_good (γ : Cube₁ X) : Good₁ (U:=U) (depth hU hcover γ) γ :=
  ((good₁_eventually hU hcover γ).exists).choose_spec

def transport (γ : Cube₁ X) : G := l.fold (depth hU hcover γ) γ

theorem transport_eq_fold {n : ℕ} {γ : Cube₁ X} (h : Good₁ (U:=U) n γ) :
    l.transport hU hcover γ = l.fold n γ := by
  let m := max n (depth hU hcover γ)
  exact (l.fold_stable (depth_good hU hcover γ) m (le_max_right _ _)).symm.trans
    (l.fold_stable h m (le_max_left _ _))

theorem transport_small {γ : Cube₁ X} (h : γ ∈ CubicalMesh.small U) :
    l.transport hU hcover γ = l.value γ := l.fold_small h _

theorem transport_const (x : X) : l.transport hU hcover (ContinuousMap.const I x) = 1 := by
  rw [l.transport_small hU hcover,l.constant]
  have hx : x ∈ ⋃₀ U := hcover ▸ mem_univ x
  obtain ⟨u,hu,hx⟩ := hx
  refine ⟨u,hu,?_⟩
  rintro y ⟨t,rfl⟩
  exact hx

omit hU hcover in
theorem four_squares (A B C D E F H K M₀ M₁ N₀ N₁ : G)
    (h₀ : A*M₀ = C*N₀) (h₁ : B*D = M₀*N₁)
    (h₂ : N₀*M₁ = E*F) (h₃ : N₁*H = M₁*K) :
    (A*B)*(D*H) = (C*E)*(F*K) := by
  calc
    _ = A*((B*D)*H) := by simp only [mul_assoc]
    _ = A*((M₀*N₁)*H) := by rw [h₁]
    _ = (A*M₀)*(N₁*H) := by simp only [mul_assoc]
    _ = (C*N₀)*(M₁*K) := by rw [h₀,h₃]
    _ = C*((N₀*M₁)*K) := by simp only [mul_assoc]
    _ = C*((E*F)*K) := by rw [h₂]
    _ = (C*E)*(F*K) := by simp only [mul_assoc]

omit hU hcover in
theorem fold_square {n : ℕ} {σ : Cube₂ X} (h : Good₂ (U:=U) n σ) :
    l.fold n (edge₂ σ 0) * l.fold n (edge₁ σ 1) =
      l.fold n (edge₁ σ 0) * l.fold n (edge₂ σ 1) := by
  induction n generalizing σ with
  | zero => exact l.square σ (good₂_zero h)
  | succ n ih =>
    have h₀ := ih (good₂_cut h false false)
    have h₁ := ih (good₂_cut h true false)
    have h₂ := ih (good₂_cut h false true)
    have h₃ := ih (good₂_cut h true true)
    simp only [edge₁_cut₂,edge₂_cut₂,half_false_zero,half_true_one,half_mid] at h₀ h₁ h₂ h₃
    exact four_squares _ _ _ _ _ _ _ _ _ _ _ _ h₀ h₁ h₂ h₃

theorem transport_square (σ : Cube₂ X) :
    l.transport hU hcover (edge₂ σ 0) * l.transport hU hcover (edge₁ σ 1) =
      l.transport hU hcover (edge₁ σ 0) * l.transport hU hcover (edge₂ σ 1) := by
  have hh := (good₂_eventually hU hcover σ).and
    ((good₁_eventually hU hcover (edge₂ σ 0)).and
    ((good₁_eventually hU hcover (edge₁ σ 1)).and
    ((good₁_eventually hU hcover (edge₁ σ 0)).and
      (good₁_eventually hU hcover (edge₂ σ 1)))))
  obtain ⟨n,hσ,h₀,h₁,h₂,h₃⟩ := hh.exists
  rw [l.transport_eq_fold hU hcover h₀,l.transport_eq_fold hU hcover h₁,
    l.transport_eq_fold hU hcover h₂,l.transport_eq_fold hU hcover h₃]
  exact l.fold_square hσ

end Local
end EilenbergGanea.PathTransport

namespace EilenbergGanea.PathTransport.Local
open Set CubicalSingular
variable {X : Type*} [TopologicalSpace X] {G : Type*} [Group G]
variable {U : Set (Set X)} (l : Local (G:=G) U)
variable (hU : ∀ u ∈ U, IsOpen u) (hcover : ⋃₀ U = univ)

omit [Group G] in
theorem good₁_mono {n m : ℕ} (hnm : n ≤ m) {γ : Cube₁ X} (h : Good₁ (U:=U) n γ) :
    Good₁ (U:=U) m γ := by
  rintro τ ⟨f,hf,rfl⟩
  apply h
  refine ⟨f,?_,rfl⟩
  intro x y
  exact (hf x y).trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) ≤ 1) hnm) dist_nonneg)

theorem transport_split (γ : Cube₁ X) :
    l.transport hU hcover γ = l.transport hU hcover (cut₁ γ false) * l.transport hU hcover (cut₁ γ true) := by
  let n := max (depth hU hcover γ) (max (depth hU hcover (cut₁ γ false)) (depth hU hcover (cut₁ γ true)))
  have hγ : Good₁ (U:=U) (n+1) γ := good₁_mono ((le_max_left _ _).trans (Nat.le_succ n)) (depth_good hU hcover γ)
  have h₀ : Good₁ (U:=U) n (cut₁ γ false) := good₁_mono ((le_max_left _ _).trans (le_max_right _ _)) (depth_good hU hcover _)
  have h₁ : Good₁ (U:=U) n (cut₁ γ true) := good₁_mono ((le_max_right _ _).trans (le_max_right _ _)) (depth_good hU hcover _)
  rw [l.transport_eq_fold hU hcover hγ,l.transport_eq_fold hU hcover h₀,l.transport_eq_fold hU hcover h₁]
  rfl

omit [Group G] in
theorem cut_trans_left {x y z : X} (p : Path x y) (q : Path y z) :
    cut₁ (p.trans q).toContinuousMap false = p.toContinuousMap := by
  apply ContinuousMap.ext
  intro t
  change (p.trans q) (half false t) = p t
  rw [← Path.extend_extends' (p.trans q),Path.extend_trans_of_le_half]
  · have h : 2 * (half false t : ℝ) = (t:ℝ) := by simp [half]; ring
    rw [h,Path.extend_extends']
  · change (t:ℝ)/2 ≤ 1/2
    linarith [t.property.2]

omit [Group G] in
theorem cut_trans_right {x y z : X} (p : Path x y) (q : Path y z) :
    cut₁ (p.trans q).toContinuousMap true = q.toContinuousMap := by
  apply ContinuousMap.ext
  intro t
  change (p.trans q) (half true t) = q t
  rw [← Path.extend_extends' (p.trans q),Path.extend_trans_of_half_le]
  · have h : 2 * (half true t : ℝ) - 1 = (t:ℝ) := by simp [half]; ring
    rw [h,Path.extend_extends']
  · change 1/2 ≤ (1+(t:ℝ))/2
    linarith [t.property.1]

theorem transport_trans {x y z : X} (p : Path x y) (q : Path y z) :
    l.transport hU hcover (p.trans q).toContinuousMap =
      l.transport hU hcover p.toContinuousMap * l.transport hU hcover q.toContinuousMap := by
  rw [l.transport_split,cut_trans_left,cut_trans_right]

theorem transport_homotopy {x y : X} {p q : Path x y} (H : p.Homotopy q) :
    l.transport hU hcover p.toContinuousMap = l.transport hU hcover q.toContinuousMap := by
  have h := l.transport_square hU hcover H.toHomotopy.toContinuousMap
  have e₀ : edge₁ H.toHomotopy.toContinuousMap 0 = p.toContinuousMap := by ext t; simp [edge₁]
  have e₁ : edge₁ H.toHomotopy.toContinuousMap 1 = q.toContinuousMap := by ext t; simp [edge₁]
  have c₀ : edge₂ H.toHomotopy.toContinuousMap 0 = ContinuousMap.const I x := by ext t; simp [edge₂]
  have c₁ : edge₂ H.toHomotopy.toContinuousMap 1 = ContinuousMap.const I y := by ext t; simp [edge₂]
  rw [e₀,e₁,c₀,c₁,l.transport_const,l.transport_const,one_mul,mul_one] at h
  exact h.symm

def quotientTransport {x y : X} : Path.Homotopic.Quotient x y → G :=
  Quotient.lift (fun p => l.transport hU hcover p.toContinuousMap)
    (fun _ _ ⟨H⟩ => l.transport_homotopy hU hcover H)

@[simp] theorem quotientTransport_mk {x y : X} (p : Path x y) :
    l.quotientTransport hU hcover (⟦p⟧ : Path.Homotopic.Quotient x y) =
      l.transport hU hcover p.toContinuousMap := rfl

@[simp] theorem quotientTransport_refl (x : X) :
    l.quotientTransport hU hcover (Path.Homotopic.Quotient.refl x) = 1 := l.transport_const hU hcover x

@[simp] theorem quotientTransport_trans {x y z : X}
    (p : Path.Homotopic.Quotient x y) (q : Path.Homotopic.Quotient y z) :
    l.quotientTransport hU hcover (p.trans q) =
      l.quotientTransport hU hcover p * l.quotientTransport hU hcover q := by
  induction p using Quotient.inductionOn
  induction q using Quotient.inductionOn
  exact l.transport_trans hU hcover _ _

end EilenbergGanea.PathTransport.Local

namespace EilenbergGanea.PathTransport
open CubicalSingular
variable {X : Type*} [TopologicalSpace X]
local instance instContractibleSpaceElemRealI : ContractibleSpace I := (convex_Icc (0:ℝ) 1).contractibleSpace ⟨0,by norm_num⟩

abbrev PQ (x y : X) := Path.Homotopic.Quotient x y

def cubePath (γ : Cube₁ X) : Path (γ 0) (γ 1) := ⟨γ,rfl,rfl⟩
abbrev asClass {x y : X} (p : Path x y) : PQ x y := Path.Homotopic.Quotient.mk p

def based {r : X} (q : ∀ x, Path r x) {x y : X} (p : PQ x y) : (FundamentalGroup X r)ᵐᵒᵖ :=
  MulOpposite.op (((asClass (q x)).trans p).trans (asClass (q y)).symm)

theorem based_trans {r x y z : X} (q : ∀ x, Path r x) (p : PQ x y) (s : PQ y z) :
    based q (p.trans s) = based q p * based q s := by
  apply MulOpposite.unop_injective
  change ((asClass (q x)).trans (p.trans s)).trans _ =
    (((asClass (q x)).trans p).trans (asClass (q y)).symm).trans
      (((asClass (q y)).trans s).trans (asClass (q z)).symm)
  simp only [Path.Homotopic.Quotient.trans_assoc]
  rw [← Path.Homotopic.Quotient.trans_assoc (asClass (q y)).symm (asClass (q y)),
    Path.Homotopic.Quotient.symm_trans,Path.Homotopic.Quotient.refl_trans]

@[simp] theorem based_refl {r : X} (q : ∀ x, Path r x) (x : X) :
    based q (Path.Homotopic.Quotient.refl x) = 1 := by
  apply MulOpposite.unop_injective
  change ((asClass (q x)).trans (Path.Homotopic.Quotient.refl x)).trans (asClass (q x)).symm = _
  simp only [Path.Homotopic.Quotient.trans_refl,Path.Homotopic.Quotient.trans_symm]
  rfl

def basedPath {r : X} (q : ∀ x, Path r x) {x y : X} (p : Path x y) : (FundamentalGroup X r)ᵐᵒᵖ :=
  based q (asClass p)

theorem basedPath_congr {r x y x' y' : X} (q : ∀ x, Path r x) (p : Path x y) (p' : Path x' y')
    (h : ∀ t, p t = p' t) : basedPath q p = basedPath q p' := by
  have hx : x = x' := by simpa using h 0
  have hy : y = y' := by simpa using h 1
  subst x'; subst y'
  have hp : p = p' := Path.ext (funext h)
  rw [hp]

theorem basedPath_homotopic {r x y : X} (q : ∀ x, Path r x) {p p' : Path x y}
    (h : Path.Homotopic p p') : basedPath q p = basedPath q p' :=
  congrArg (based q) (Quotient.sound h)

@[simp] theorem basedPath_trans {r x y z : X} (q : ∀ x, Path r x) (p : Path x y) (s : Path y z) :
    basedPath q (p.trans s) = basedPath q p * basedPath q s := by
  exact (congrArg (based q) (Path.Homotopic.Quotient.mk_trans p s)).trans (based_trans q _ _)
@[simp] theorem basedPath_refl {r : X} (q : ∀ x, Path r x) (x : X) : basedPath q (Path.refl x) = 1 := based_refl q x

def holonomy {r : X} (q : ∀ x, Path r x) (γ : Cube₁ X) : (FundamentalGroup X r)ᵐᵒᵖ :=
  basedPath q (cubePath γ)

@[simp] theorem holonomy_path {r x y : X} (q : ∀ x, Path r x) (p : Path x y) :
    holonomy q p.toContinuousMap = basedPath q p := basedPath_congr q _ _ (fun _ => rfl)
@[simp] theorem holonomy_const {r : X} (q : ∀ x, Path r x) (x : X) :
    holonomy q (ContinuousMap.const I x) = 1 := basedPath_refl q x

def bottom : Path ((0:I),(0:I)) (1,0) := Path.id.prod (Path.refl 0)
def rightSide : Path ((1:I),(0:I)) (1,1) := (Path.refl 1).prod Path.id
def leftSide : Path ((0:I),(0:I)) (0,1) := (Path.refl 0).prod Path.id
def topSide : Path ((0:I),(1:I)) (1,1) := Path.id.prod (Path.refl 1)

theorem square_paths (σ : Cube₂ X) :
    Path.Homotopic ((bottom.map σ.continuous).trans (rightSide.map σ.continuous))
      ((leftSide.map σ.continuous).trans (topSide.map σ.continuous)) := by
  have h := (SimplyConnectedSpace.paths_homotopic (bottom.trans rightSide) (leftSide.trans topSide)).map σ
  simpa only [Path.map_trans] using h

theorem holonomy_square {r : X} (q : ∀ x, Path r x) (σ : Cube₂ X) :
    holonomy q (edge₂ σ 0) * holonomy q (edge₁ σ 1) =
      holonomy q (edge₁ σ 0) * holonomy q (edge₂ σ 1) := by
  have h := basedPath_homotopic q (square_paths σ)
  rw [basedPath_trans,basedPath_trans] at h
  have h₀ := basedPath_congr q (bottom.map σ.continuous) (cubePath (edge₂ σ 0)) (fun _ => rfl)
  have h₁ := basedPath_congr q (rightSide.map σ.continuous) (cubePath (edge₁ σ 1)) (fun _ => rfl)
  have h₂ := basedPath_congr q (leftSide.map σ.continuous) (cubePath (edge₁ σ 0)) (fun _ => rfl)
  have h₃ := basedPath_congr q (topSide.map σ.continuous) (cubePath (edge₂ σ 1)) (fun _ => rfl)
  exact (congrArg₂ (· * ·) h₀ h₁).symm.trans (h.trans (congrArg₂ (· * ·) h₂ h₃))

end EilenbergGanea.PathTransport

namespace EilenbergGanea.CubicalSingular
variable {X : Type*} [TopologicalSpace X]

/-- Low-dimensional Mayer–Vietoris injectivity, derived by subdivision. -/
theorem mayerVietoris_injective [ContractibleSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = univ)
    {z : N₁ X} (hz : z ∈ L₁ (U ∩ V))
    {a b : N₂ X} (ha : a ∈ L₂ U) (hb : b ∈ L₂ V) (hda : d₂ a = z) (hdb : d₂ b = z) :
    ∃ c ∈ L₂ (U ∩ V), d₂ c = z := by
  have hcycle : d₂ (a-b) = 0 := by rw [map_sub,hda,hdb,sub_self]
  obtain ⟨w,hw⟩ := exact₂_of_contractible (a-b) hcycle
  obtain ⟨n,hn⟩ := S₃_eventually_small U V hU hV hUV w
  obtain ⟨u,hu,v,hv,huv⟩ := Submodule.mem_sup.mp (hn n le_rfl)
  have he : d₃ u + d₃ v = (SN₂^[n]) a - (SN₂^[n]) b := by
    rw [← map_add,huv,d₃_S₃_iter,hw,← Module.End.pow_apply]
    simpa only [Module.End.pow_apply] using (SN₂ ^ n).map_sub a b
  let c : N₂ X := (SN₂^[n]) a - d₃ u
  have hcU : c ∈ L₂ U := Submodule.sub_mem _ (SN₂_iter_support U ha n) (d₃_support U hu)
  have hc_eq : c = (SN₂^[n]) b + d₃ v := by
    apply sub_eq_iff_eq_add.mpr
    calc
      (SN₂^[n]) a = ((SN₂^[n]) a - (SN₂^[n]) b) + (SN₂^[n]) b := (sub_add_cancel _ _).symm
      _ = (d₃ u + d₃ v) + (SN₂^[n]) b := by rw [he]
      _ = ((SN₂^[n]) b + d₃ v) + d₃ u := by abel
  have hcV : c ∈ L₂ V := by
    rw [hc_eq]
    exact Submodule.add_mem _ (SN₂_iter_support V hb n) (d₃_support V hv)
  have hdc : d₂ c = (SN₁^[n]) z := by
    change d₂ ((SN₂^[n]) a - d₃ u) = _
    rw [map_sub,d₂_SN₂_iter,hda,d₂_d₃,sub_zero]
  refine ⟨c - K₁ n z,?_,?_⟩
  · exact Submodule.sub_mem _ (by rw [L₂_inter]; exact ⟨hcU,hcV⟩) (K₁_support _ hz n)
  · rw [map_sub,hdc,K₁_boundary]
    abel

/-- The other half of the same exact sequence, with literal supported chains. -/
theorem mayerVietoris_surjective [ContractibleSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = univ)
    {z : N₁ X} (hzU : z ∈ L₁ U) (hz : d₁ z = 0) :
    ∃ t ∈ L₁ (U ∩ V), d₁ t = 0 ∧
      (∃ b ∈ L₂ U, d₂ b = t-z) ∧ (∃ b ∈ L₂ V, d₂ b = t) := by
  obtain ⟨a,ha⟩ := exact₁_of_contractible z hz
  obtain ⟨n,hn⟩ := SN₂_eventually_small U V hU hV hUV a
  obtain ⟨u,hu,v,hv,huv⟩ := Submodule.mem_sup.mp (hn n le_rfl)
  have he : d₂ u + d₂ v = (SN₁^[n]) z := by rw [← map_add,huv,d₂_SN₂_iter,ha]
  have ht_eq : d₂ v = (SN₁^[n]) z - d₂ u := by
    apply eq_sub_iff_add_eq.mpr
    rw [add_comm,he]
  refine ⟨d₂ v,?_,d₁_d₂ v,?_,⟨v,hv,rfl⟩⟩
  · rw [L₁_inter]
    refine ⟨?_,d₂_support V hv⟩
    rw [ht_eq]
    exact Submodule.sub_mem _ (SN₁_iter_support U hzU n) (d₂_support U hu)
  · refine ⟨K₁ n z-u,Submodule.sub_mem _ (K₁_support U hzU n) hu,?_⟩
    rw [map_sub,K₁_boundary,ht_eq]
    abel

/-- Cycles and boundaries are actual submodules of normalized singular chains. -/
def cyclesOn (U : Set X) : Submodule ℤ (N₁ X) := L₁ U ⊓ LinearMap.ker d₁
def boundsOn (U : Set X) : Submodule ℤ (N₁ X) := (L₂ U).map d₂

def boundaries (U : Set X) : Submodule ℤ (cyclesOn U) := (boundsOn U).comap (cyclesOn U).subtype
abbrev Homology₁ (U : Set X) := cyclesOn U ⧸ boundaries U

def cycleInclusion {U V : Set X} (h : U ⊆ V) : cyclesOn U →ₗ[ℤ] cyclesOn V :=
  Submodule.inclusion (inf_le_inf_right _ (L₁_mono h))

theorem cycleInclusion_bounds {U V : Set X} (h : U ⊆ V) :
    boundaries U ≤ (boundaries V).comap (cycleInclusion h) := by
  rintro z ⟨b,hb,he⟩
  exact ⟨b,L₂_mono h hb,he⟩

def homologyInclusion {U V : Set X} (h : U ⊆ V) : Homology₁ U →ₗ[ℤ] Homology₁ V :=
  (boundaries U).mapQ (boundaries V) (cycleInclusion h) (cycleInclusion_bounds h)

theorem homologyInclusion_injective [ContractibleSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = univ)
    (hVex : ∀ z : N₁ X, z ∈ L₁ V → d₁ z = 0 → ∃ b ∈ L₂ V, d₂ b = z) :
    Function.Injective (homologyInclusion (Set.inter_subset_left : U ∩ V ⊆ U)) := by
  apply LinearMap.ker_eq_bot.mp
  refine le_antisymm ?_ bot_le
  intro z hz
  obtain ⟨z,rfl⟩ := (boundaries (U ∩ V)).mkQ_surjective z
  change (boundaries U).mkQ (cycleInclusion Set.inter_subset_left z) = 0 at hz
  have hzm := (Submodule.Quotient.mk_eq_zero (boundaries U)).mp hz
  obtain ⟨a,ha,hda⟩ := hzm
  obtain ⟨b,hb,hdb⟩ := hVex z.val (L₁_mono Set.inter_subset_right z.property.1) z.property.2
  obtain ⟨c,hc,hdc⟩ := mayerVietoris_injective U V hU hV hUV z.property.1 ha hb hda hdb
  change (boundaries (U ∩ V)).mkQ z = 0
  exact (Submodule.Quotient.mk_eq_zero (boundaries (U ∩ V))).mpr ⟨c,hc,hdc⟩

theorem homologyInclusion_surjective [ContractibleSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = univ) :
    Function.Surjective (homologyInclusion (Set.inter_subset_left : U ∩ V ⊆ U)) := by
  intro z
  obtain ⟨z,rfl⟩ := (boundaries U).mkQ_surjective z
  obtain ⟨t,ht,htz,⟨b,hb,hdb⟩,_⟩ := mayerVietoris_surjective U V hU hV hUV z.property.1 z.property.2
  let t' : cyclesOn (U ∩ V) := ⟨t,ht,htz⟩
  refine ⟨(boundaries (U ∩ V)).mkQ t',?_⟩
  change (boundaries U).mkQ (cycleInclusion Set.inter_subset_left t') = (boundaries U).mkQ z
  rw [← sub_eq_zero,← map_sub]
  exact (Submodule.Quotient.mk_eq_zero (boundaries U)).mpr ⟨b,hb,hdb⟩

/-- No cellular theorem is assumed: this is the comparison for actual open sets
in an actually contractible space, proved by finite singular subdivision. -/
def mayerVietoris_equiv [ContractibleSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = univ)
    (hVex : ∀ z : N₁ X, z ∈ L₁ V → d₁ z = 0 → ∃ b ∈ L₂ V, d₂ b = z) :
    Homology₁ (U ∩ V) ≃ₗ[ℤ] Homology₁ U :=
  LinearEquiv.ofBijective (homologyInclusion Set.inter_subset_left)
    ⟨homologyInclusion_injective U V hU hV hUV hVex,homologyInclusion_surjective U V hU hV hUV⟩

end EilenbergGanea.CubicalSingular

namespace EilenbergGanea.CubicalSingular
open Set
variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

theorem pushN₁_mapsTo (f : C(X,Y)) {U : Set X} {V : Set Y} (hf : MapsTo f U V) :
    L₁ U ≤ (L₁ V).comap (pushN₁ f) := by
  rw [L₁_span]
  apply Submodule.span_le.mpr
  rintro _ ⟨σ,hσ,rfl⟩
  change pushN₁ f (gen₁ σ) ∈ L₁ V
  simp only [gen₁,pushN₁_mk,push₁_single]
  change gen₁ (f.comp σ) ∈ L₁ V
  exact gen₁_mem (by rintro _ ⟨t,rfl⟩; exact hf (hσ ⟨t,rfl⟩))

theorem pushN₂_mapsTo (f : C(X,Y)) {U : Set X} {V : Set Y} (hf : MapsTo f U V) :
    L₂ U ≤ (L₂ V).comap (pushN₂ f) := by
  rw [L₂_span]
  apply Submodule.span_le.mpr
  rintro _ ⟨σ,hσ,rfl⟩
  change pushN₂ f (gen₂ σ) ∈ L₂ V
  simp only [gen₂,pushN₂_mk,push₂_single]
  change gen₂ (f.comp σ) ∈ L₂ V
  exact gen₂_mem (by rintro _ ⟨t,rfl⟩; exact hf (hσ ⟨t,rfl⟩))

@[simp] theorem L₁_univ : L₁ (univ : Set X) = ⊤ := by
  rw [L₁,raw₁,cubeSet_univ,Finsupp.supported_univ,Submodule.map_top]
  exact LinearMap.range_eq_top.mpr (D₁ X).mkQ_surjective
@[simp] theorem L₂_univ : L₂ (univ : Set X) = ⊤ := by
  rw [L₂,raw₂,cubeSet_univ,Finsupp.supported_univ,Submodule.map_top]
  exact LinearMap.range_eq_top.mpr (D₂ X).mkQ_surjective

def cycleMap (f : C(X,Y)) {U : Set X} {V : Set Y} (hf : MapsTo f U V) :
    cyclesOn U →ₗ[ℤ] cyclesOn V :=
  (pushN₁ f).restrict (fun z hz => ⟨pushN₁_mapsTo f hf hz.1,by
    change d₁ (pushN₁ f z) = 0
    rw [d₁_push,hz.2,map_zero]⟩)

theorem cycleMap_bounds (f : C(X,Y)) {U : Set X} {V : Set Y} (hf : MapsTo f U V) :
    boundaries U ≤ (boundaries V).comap (cycleMap f hf) := by
  rintro z ⟨b,hb,he⟩
  refine ⟨pushN₂ f b,pushN₂_mapsTo f hf hb,?_⟩
  exact (d₂_push f b).trans (congrArg (pushN₁ f) he)

def homologyMap (f : C(X,Y)) {U : Set X} {V : Set Y} (hf : MapsTo f U V) :
    Homology₁ U →ₗ[ℤ] Homology₁ V :=
  (boundaries U).mapQ (boundaries V) (cycleMap f hf) (cycleMap_bounds f hf)

@[simp] theorem homologyMap_mk (f : C(X,Y)) {U : Set X} {V : Set Y} (hf : MapsTo f U V)
    (z : cyclesOn U) : homologyMap f hf ((boundaries U).mkQ z) =
      (boundaries V).mkQ (cycleMap f hf z) := rfl

def normalizedPrism {f g : C(X,Y)} (H : f.Homotopy g) : N₁ X →ₗ[ℤ] N₂ Y :=
  (D₁ X).liftQ ((D₂ Y).mkQ.comp (P₁ H)) (by
    intro z hz
    exact (Submodule.Quotient.mk_eq_zero _).mpr (P₁_D₁ H hz))

@[simp] theorem normalizedPrism_mk {f g : C(X,Y)} (H : f.Homotopy g) (c : C₁ X) :
    normalizedPrism H ((D₁ X).mkQ c) = (D₂ Y).mkQ (P₁ H c) := rfl

theorem normalizedPrism_boundary {f g : C(X,Y)} (H : f.Homotopy g)
    {z : N₁ X} (hz : d₁ z = 0) : d₂ (normalizedPrism H z) = pushN₁ g z - pushN₁ f z := by
  obtain ⟨c,rfl⟩ := (D₁ X).mkQ_surjective z
  change b₁ c = 0 at hz
  have h := LinearMap.congr_fun (prism_boundary₁ H) c
  change b₂ (P₁ H c) + P₀ H (b₁ c) = push₁ g c - push₁ f c at h
  simp only [hz,map_zero,add_zero] at h
  change (D₁ Y).mkQ (b₂ (P₁ H c)) = _
  rw [h,map_sub]
  rfl

theorem normalizedPrism_support {f g : C(X,Y)} (H : f.Homotopy g)
    {U : Set X} {V : Set Y} (hH : ∀ t x, x ∈ U → H (t,x) ∈ V) :
    L₁ U ≤ (L₂ V).comap (normalizedPrism H) := by
  rw [L₁_span]
  apply Submodule.span_le.mpr
  rintro _ ⟨σ,hσ,rfl⟩
  change (D₂ Y).mkQ (P₁ H (Finsupp.single σ 1)) ∈ L₂ V
  rw [P₁_single]
  exact gen₂_mem (by rintro _ ⟨t,rfl⟩; exact hH t.1 (σ t.2) (hσ ⟨t.2,rfl⟩))

theorem homologyMap_homotopic {f g : C(X,Y)} (H : f.Homotopy g)
    {U : Set X} {V : Set Y} (hf : MapsTo f U V) (hg : MapsTo g U V)
    (hH : ∀ t x, x ∈ U → H (t,x) ∈ V) : homologyMap f hf = homologyMap g hg := by
  apply LinearMap.ext
  intro q
  obtain ⟨z,rfl⟩ := (boundaries U).mkQ_surjective q
  rw [homologyMap_mk,homologyMap_mk]
  apply eq_of_sub_eq_zero
  rw [← map_sub]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  refine ⟨-normalizedPrism H z.val,Submodule.neg_mem _ (normalizedPrism_support H hH z.property.1),?_⟩
  rw [map_neg,normalizedPrism_boundary H z.property.2]
  change -(pushN₁ g z.val - pushN₁ f z.val) = pushN₁ f z.val - pushN₁ g z.val
  abel

theorem homologyMap_id (U : Set X) : homologyMap (ContinuousMap.id X) (show MapsTo (ContinuousMap.id X) U U from fun _ h => h) = LinearMap.id := by
  apply LinearMap.ext
  intro q
  obtain ⟨z,rfl⟩ := (boundaries U).mkQ_surjective q
  rw [homologyMap_mk,LinearMap.id_apply]
  congr 1
  apply Subtype.ext
  exact pushN₁_id z.val

theorem homologyMap_comp (g : C(Y,Z)) (f : C(X,Y)) {U : Set X} {V : Set Y} {W : Set Z}
    (hf : MapsTo f U V) (hg : MapsTo g V W) :
    homologyMap (g.comp f) (hg.comp hf) = (homologyMap g hg).comp (homologyMap f hf) := by
  apply LinearMap.ext
  intro q
  obtain ⟨z,rfl⟩ := (boundaries U).mkQ_surjective q
  simp only [homologyMap_mk,LinearMap.comp_apply]
  congr 1
  apply Subtype.ext
  exact pushN₁_comp g f z.val

abbrev HomologyOne (X : Type*) [TopologicalSpace X] := Homology₁ (univ : Set X)
def homologyOneMap (f : C(X,Y)) : HomologyOne X →ₗ[ℤ] HomologyOne Y := homologyMap f (mapsTo_univ _ _)
@[simp] theorem homologyOneMap_id : homologyOneMap (ContinuousMap.id X) = LinearMap.id := homologyMap_id univ
@[simp] theorem homologyOneMap_comp (g : C(Y,Z)) (f : C(X,Y)) :
    homologyOneMap (g.comp f) = (homologyOneMap g).comp (homologyOneMap f) := homologyMap_comp g f _ _

theorem homologyOneMap_homotopic {f g : C(X,Y)} (H : f.Homotopy g) : homologyOneMap f = homologyOneMap g :=
  homologyMap_homotopic H _ _ (by intros; trivial)

/-- Actual homotopy equivalences induce integral cubical H1 isomorphisms. -/
def homologyOneEquiv (f : C(X,Y)) (g : C(Y,X))
    (Hgf : (g.comp f).Homotopy (ContinuousMap.id X))
    (Hfg : (f.comp g).Homotopy (ContinuousMap.id Y)) : HomologyOne X ≃ₗ[ℤ] HomologyOne Y :=
  LinearEquiv.ofLinearMap (homologyOneMap f) (homologyOneMap g)
    (by rw [← homologyOneMap_comp,homologyOneMap_homotopic Hfg,homologyOneMap_id])
    (by rw [← homologyOneMap_comp,homologyOneMap_homotopic Hgf,homologyOneMap_id])

end EilenbergGanea.CubicalSingular

namespace EilenbergGanea.CubicalSingular
open Set PathTransport
variable {X : Type*} [TopologicalSpace X]

abbrev PathChains (X : Type*) [TopologicalSpace X] := N₁ X ⧸ LinearMap.range (d₂ : N₂ X →ₗ[ℤ] N₁ X)
def chainClass : N₁ X →ₗ[ℤ] PathChains X := (LinearMap.range d₂).mkQ
def pathClass {x y : X} (p : Path x y) : PathChains X := chainClass (gen₁ p.toContinuousMap)

@[simp] theorem chainClass_boundary (b : N₂ X) : chainClass (d₂ b) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr ⟨b,rfl⟩
@[simp] theorem gen₁_const (x : X) : gen₁ (ContinuousMap.const I x) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.subset_span ⟨x,rfl⟩)
@[simp] theorem pathClass_refl (x : X) : pathClass (Path.refl x) = 0 := by
  change chainClass (gen₁ (ContinuousMap.const I x)) = 0
  rw [gen₁_const,map_zero]

theorem chainClass_subdivision (z : N₁ X) : chainClass (SN₁ z) = chainClass z := by
  have h := chainClass_boundary (K₁ 1 z)
  rw [K₁_boundary] at h
  exact sub_eq_zero.mp (by simpa only [Function.iterate_one,map_sub] using h)

theorem pathClass_trans {x y z : X} (p : Path x y) (q : Path y z) :
    pathClass (p.trans q) = pathClass p + pathClass q := by
  rw [pathClass,← chainClass_subdivision]
  simp only [gen₁,SN₁_mk,S₁_single,Fintype.sum_bool,map_add,
    PathTransport.Local.cut_trans_left,PathTransport.Local.cut_trans_right]
  rw [add_comm]
  rfl

theorem pathClass_homotopy {x y : X} {p q : Path x y} (H : p.Homotopy q) :
    pathClass p = pathClass q := by
  have h := chainClass_boundary (gen₂ H.toHomotopy.toContinuousMap)
  have e₀ : edge₁ H.toHomotopy.toContinuousMap 0 = p.toContinuousMap := by ext t; simp [edge₁]
  have e₁ : edge₁ H.toHomotopy.toContinuousMap 1 = q.toContinuousMap := by ext t; simp [edge₁]
  have c₀ : edge₂ H.toHomotopy.toContinuousMap 0 = ContinuousMap.const I x := by ext t; simp [edge₂]
  have c₁ : edge₂ H.toHomotopy.toContinuousMap 1 = ContinuousMap.const I y := by ext t; simp [edge₂]
  change chainClass ((D₁ X).mkQ (b₂ (Finsupp.single H.toHomotopy.toContinuousMap 1))) = 0 at h
  simp only [b₂_single,one_smul,map_sub,map_add,e₀,e₁,c₀,c₁] at h
  change pathClass q - pathClass p - chainClass (gen₁ (ContinuousMap.const I y)) +
    chainClass (gen₁ (ContinuousMap.const I x)) = 0 at h
  have hh : pathClass q - pathClass p = 0 := by simpa only [gen₁_const,map_zero,sub_zero,add_zero] using h
  exact (sub_eq_zero.mp hh).symm

def quotientPathClass {x y : X} : PQ x y → PathChains X :=
  Quotient.lift (fun p => pathClass p) (fun _ _ ⟨H⟩ => pathClass_homotopy H)
@[simp] theorem quotientPathClass_mk {x y : X} (p : Path x y) :
    quotientPathClass (asClass p) = pathClass p := rfl
@[simp] theorem quotientPathClass_trans {x y z : X} (p : PQ x y) (q : PQ y z) :
    quotientPathClass (p.trans q) = quotientPathClass p + quotientPathClass q := by
  induction p using Quotient.inductionOn
  induction q using Quotient.inductionOn
  exact pathClass_trans _ _
@[simp] theorem quotientPathClass_refl (x : X) : quotientPathClass (Path.Homotopic.Quotient.refl x) = 0 :=
  pathClass_refl x
@[simp] theorem quotientPathClass_symm {x y : X} (p : PQ x y) :
    quotientPathClass p.symm = -quotientPathClass p := by
  have h := congrArg (quotientPathClass) (Path.Homotopic.Quotient.trans_symm p)
  rw [quotientPathClass_trans,quotientPathClass_refl] at h
  exact eq_neg_of_add_eq_zero_right h

def loopChainHom (r : X) : (FundamentalGroup X r)ᵐᵒᵖ →* Multiplicative (PathChains X) where
  toFun g := Multiplicative.ofAdd (quotientPathClass g.unop)
  map_one' := congrArg Multiplicative.ofAdd (quotientPathClass_refl r)
  map_mul' g h := congrArg Multiplicative.ofAdd (quotientPathClass_trans g.unop h.unop)

abbrev AbLoops (X : Type*) [TopologicalSpace X] (r : X) := Additive (Abelianization (FundamentalGroup X r)ᵐᵒᵖ)

def loopToChains (r : X) : AbLoops X r →ₗ[ℤ] PathChains X :=
  (Abelianization.lift (loopChainHom r)).toAdditive.toIntLinearMap

@[simp] theorem loopToChains_of (r : X) (g : (FundamentalGroup X r)ᵐᵒᵖ) :
    loopToChains r (Additive.ofMul (Abelianization.of g)) = quotientPathClass g.unop := rfl

def abHolonomy {r : X} (q : ∀ x, Path r x) (γ : Cube₁ X) : AbLoops X r :=
  Additive.ofMul (Abelianization.of (holonomy q γ))
@[simp] theorem abHolonomy_const {r : X} (q : ∀ x, Path r x) (x : X) :
    abHolonomy q (ContinuousMap.const I x) = 0 := by
  simp [abHolonomy]

def abHolonomyRaw {r : X} (q : ∀ x, Path r x) : C₁ X →ₗ[ℤ] AbLoops X r :=
  Finsupp.linearCombination ℤ (abHolonomy q)

def abHolonomyMap {r : X} (q : ∀ x, Path r x) : N₁ X →ₗ[ℤ] AbLoops X r :=
  (D₁ X).liftQ (abHolonomyRaw q) (by
    apply Submodule.span_le.mpr
    rintro _ ⟨x,rfl⟩
    simp [abHolonomyRaw,constant₁])

@[simp] theorem abHolonomyMap_gen {r : X} (q : ∀ x, Path r x) (γ : Cube₁ X) :
    abHolonomyMap q (gen₁ γ) = abHolonomy q γ := by simp [abHolonomyMap,gen₁,abHolonomyRaw]

theorem abHolonomy_square {r : X} (q : ∀ x, Path r x) (σ : Cube₂ X) :
    abHolonomy q (edge₂ σ 0) + abHolonomy q (edge₁ σ 1) =
      abHolonomy q (edge₁ σ 0) + abHolonomy q (edge₂ σ 1) := by
  have h := congrArg (fun g => Additive.ofMul (Abelianization.of g)) (holonomy_square q σ)
  simp only [map_mul] at h
  exact h

theorem abHolonomyMap_boundary {r : X} (q : ∀ x, Path r x) :
    (abHolonomyMap q).comp d₂ = 0 := by
  apply LinearMap.ext
  intro z
  obtain ⟨z,rfl⟩ := (D₂ X).mkQ_surjective z
  have he : (abHolonomyRaw q).comp b₂ = 0 := by
    apply Finsupp.lhom_ext
    intro σ a
    simp only [LinearMap.comp_apply,b₂_single,map_smul,map_sub,map_add,abHolonomyRaw,
      Finsupp.linearCombination_single,one_smul,LinearMap.zero_apply]
    have h := abHolonomy_square q σ
    have hz : abHolonomy q (edge₁ σ 1) - abHolonomy q (edge₁ σ 0) -
      abHolonomy q (edge₂ σ 1) + abHolonomy q (edge₂ σ 0) = 0 := by
      calc
        _ = (abHolonomy q (edge₂ σ 0) + abHolonomy q (edge₁ σ 1)) -
          (abHolonomy q (edge₁ σ 0) + abHolonomy q (edge₂ σ 1)) := by abel
        _ = 0 := by rw [h,sub_self]
    rw [hz,smul_zero]
  exact LinearMap.congr_fun he z

def chainsToLoops {r : X} (q : ∀ x, Path r x) : PathChains X →ₗ[ℤ] AbLoops X r :=
  (LinearMap.range d₂).liftQ (abHolonomyMap q) (by
    rintro _ ⟨z,rfl⟩
    exact LinearMap.congr_fun (abHolonomyMap_boundary q) z)
@[simp] theorem chainsToLoops_class {r : X} (q : ∀ x, Path r x) (z : N₁ X) :
    chainsToLoops q (chainClass z) = abHolonomyMap q z := rfl
@[simp] theorem chainsToLoops_path {r x y : X} (q : ∀ x, Path r x) (p : Path x y) :
    chainsToLoops q (pathClass p) = abHolonomy q p.toContinuousMap := abHolonomyMap_gen q _

end EilenbergGanea.CubicalSingular

namespace EilenbergGanea.CubicalSingular
open Set PathTransport
variable {X : Type*} [TopologicalSpace X]

@[simp] theorem quotientPathClass_based {r : X} (q : ∀ x, Path r x) {x y : X} (p : PQ x y) :
    quotientPathClass (based q p).unop = pathClass (q x) + quotientPathClass p - pathClass (q y) := by
  simp only [based,MulOpposite.unop_op,quotientPathClass_trans,quotientPathClass_symm,quotientPathClass_mk,sub_eq_add_neg]

def anchorChains {r : X} (q : ∀ x, Path r x) : C₀ X →ₗ[ℤ] PathChains X :=
  Finsupp.linearCombination ℤ (fun x => pathClass (q x))

theorem loopToChains_abHolonomy {r : X} (q : ∀ x, Path r x) (γ : Cube₁ X) :
    loopToChains r (abHolonomy q γ) = chainClass (gen₁ γ) - anchorChains q (d₁ (gen₁ γ)) := by
  change quotientPathClass (based q (asClass (cubePath γ))).unop = _
  rw [quotientPathClass_based,quotientPathClass_mk]
  simp only [gen₁,d₁_mk,b₁_single,one_smul,map_sub,anchorChains,Finsupp.linearCombination_single,one_smul]
  change pathClass (q (γ 0)) + pathClass (cubePath γ) - pathClass (q (γ 1)) =
    pathClass (cubePath γ) - (pathClass (q (γ 1)) - pathClass (q (γ 0)))
  abel

theorem loops_chains_identity {r : X} (q : ∀ x, Path r x) (z : N₁ X) :
    loopToChains r (abHolonomyMap q z) = chainClass z - anchorChains q (d₁ z) := by
  obtain ⟨c,rfl⟩ := (D₁ X).mkQ_surjective z
  have he : (loopToChains r).comp (abHolonomyRaw q) =
      chainClass.comp (D₁ X).mkQ - (anchorChains q).comp b₁ := by
    apply Finsupp.lhom_ext
    intro γ m
    change loopToChains r (abHolonomyRaw q (Finsupp.single γ m)) = _
    rw [← Finsupp.smul_single_one γ m]
    simp only [map_smul,LinearMap.sub_apply,LinearMap.comp_apply]
    rw [show abHolonomyRaw q (Finsupp.single γ 1) = abHolonomy q γ by simp [abHolonomyRaw],loopToChains_abHolonomy]
    simp only [smul_sub]
    rfl
  exact LinearMap.congr_fun he c

theorem ab_based_loop {r : X} (q : ∀ x, Path r x) (g : FundamentalGroup X r) :
    Abelianization.of (based q g) = Abelianization.of (MulOpposite.op g) := by
  let u : FundamentalGroup X r := asClass (q r)
  have he : based q g = (MulOpposite.op u : (FundamentalGroup X r)ᵐᵒᵖ) *
      MulOpposite.op g * (MulOpposite.op u)⁻¹ := rfl
  rw [he,map_mul,map_mul,map_inv]
  simp [mul_comm]

theorem chains_loops_identity {r : X} (q : ∀ x, Path r x) (g : AbLoops X r) :
    chainsToLoops q (loopToChains r g) = g := by
  revert g
  change ∀ g : Abelianization (FundamentalGroup X r)ᵐᵒᵖ,
    chainsToLoops q (loopToChains r (Additive.ofMul g)) = Additive.ofMul g
  intro g
  induction g using QuotientGroup.induction_on with
  | H g =>
    change chainsToLoops q (loopToChains r (Additive.ofMul (Abelianization.of g))) = Additive.ofMul (Abelianization.of g)
    rw [loopToChains_of]
    induction g using MulOpposite.rec' with
    | h g =>
      induction g using Quotient.inductionOn with
      | h p =>
        change chainsToLoops q (quotientPathClass (asClass p)) = Additive.ofMul ((Abelianization.of (G := (FundamentalGroup X r)ᵐᵒᵖ)) (MulOpposite.op (asClass p)))
        rw [quotientPathClass_mk,chainsToLoops_path]
        rw [abHolonomy,holonomy_path]
        change Additive.ofMul (Abelianization.of (based q (asClass p))) = _
        exact congrArg Additive.ofMul (ab_based_loop q (asClass p))

def homologyChainsMap : HomologyOne X →ₗ[ℤ] PathChains X :=
  (boundaries univ).liftQ (chainClass.comp (cyclesOn univ).subtype) (by
    rintro z ⟨b,_,he⟩
    change chainClass z.val = 0
    change d₂ b = z.val at he
    rw [← he,chainClass_boundary])
@[simp] theorem homologyChainsMap_mk (z : cyclesOn (univ : Set X)) :
    homologyChainsMap ((boundaries univ).mkQ z) = chainClass z.val := rfl

theorem homologyChainsMap_injective : Function.Injective (homologyChainsMap (X:=X)) := by
  apply LinearMap.ker_eq_bot.mp
  refine le_antisymm ?_ bot_le
  intro h hh
  obtain ⟨z,rfl⟩ := (boundaries univ).mkQ_surjective h
  change chainClass z.val = 0 at hh
  obtain ⟨b,hb⟩ := (Submodule.Quotient.mk_eq_zero (LinearMap.range d₂)).mp hh
  change (boundaries univ).mkQ z = 0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact ⟨b,by rw [L₂_univ]; trivial,hb⟩

def homologyToLoops {r : X} (q : ∀ x, Path r x) : HomologyOne X →ₗ[ℤ] AbLoops X r :=
  (chainsToLoops q).comp homologyChainsMap

theorem homologyToLoops_injective {r : X} (q : ∀ x, Path r x) : Function.Injective (homologyToLoops q) := by
  apply LinearMap.ker_eq_bot.mp
  refine le_antisymm ?_ bot_le
  intro h hh
  obtain ⟨z,rfl⟩ := (boundaries univ).mkQ_surjective h
  change abHolonomyMap q z.val = 0 at hh
  have hc := loops_chains_identity q z.val
  rw [z.property.2,map_zero,sub_zero,hh,map_zero] at hc
  apply homologyChainsMap_injective
  simpa only [homologyChainsMap_mk,map_zero] using hc.symm

theorem homologyToLoops_surjective {r : X} (q : ∀ x, Path r x) : Function.Surjective (homologyToLoops q) := by
  intro g
  have hg : ∃ w : (FundamentalGroup X r)ᵐᵒᵖ, Additive.ofMul (Abelianization.of w) = g := by
    exact QuotientGroup.mk'_surjective _ g
  obtain ⟨w,rfl⟩ := hg
  obtain ⟨p,hp⟩ := Quotient.exists_rep w.unop
  have hc : d₁ (gen₁ p.toContinuousMap) = 0 := by
    simp only [gen₁,d₁_mk,b₁_single,one_smul]
    change (Finsupp.single (p 1) (1:ℤ) - Finsupp.single (p 0) (1:ℤ)) = 0
    rw [p.target,p.source,sub_self]
  let z : cyclesOn (univ : Set X) := ⟨gen₁ p.toContinuousMap,by rw [L₁_univ]; trivial,hc⟩
  refine ⟨(boundaries univ).mkQ z,?_⟩
  change chainsToLoops q (pathClass p) = Additive.ofMul (Abelianization.of w)
  have he : loopToChains r (Additive.ofMul (Abelianization.of w)) = pathClass p := by
    rw [loopToChains_of]
    change quotientPathClass w.unop = quotientPathClass (asClass p)
    exact congrArg quotientPathClass hp.symm
  rw [← he,chains_loops_identity]

/-- Integral degree-one Hurewicz for actual paths, with no cellular hypothesis:
finite singular 1-cycles equal the abelianized topological fundamental group. -/
def hurewiczOne {r : X} (q : ∀ x, Path r x) : HomologyOne X ≃ₗ[ℤ] AbLoops X r :=
  LinearEquiv.ofBijective (homologyToLoops q)
    ⟨homologyToLoops_injective q,homologyToLoops_surjective q⟩

end EilenbergGanea.CubicalSingular


end

end OAI
end

section
-- module Solutions.OAIEG.CWComplex_Collar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Metric Topology

namespace EilenbergGanea.CWCollar
open Classical Set Metric Topology
open CWCover
universe u v
variable {X : Type u} [TopologicalSpace X] {J : Type v} {n : ℕ}

/-- Single-dimensional ordinary disk attachment. All fields will be derived
from the actual CW structure, not posited for the classifying-space theorem. -/
structure Attachment (X : Type u) [TopologicalSpace X] (J : Type v) (n : ℕ) where
  lower : Set X
  closed_lower : IsClosed lower
  chart : J → C(Disk n,X)
  boundary : ∀ j (z : Disk n), ‖z.val‖ = 1 → chart j z ∈ lower
  interior : ∀ j (z : Disk n), ‖z.val‖ < 1 → chart j z ∉ lower
  disjoint : ∀ j k (z w : Disk n), ‖z.val‖ < 1 → ‖w.val‖ < 1 →
    chart j z = chart k w → j = k ∧ z = w
  quotient : IsQuotientMap (Sum.elim (Subtype.val : lower → X)
    (fun p : Σ _ : J, Disk n => chart p.1 p.2))

namespace Attachment
variable (a : Attachment X J n)
abbrev Rep := a.lower ⊕ (Σ _ : J, Disk n)
def q : a.Rep → X := Sum.elim Subtype.val (fun p => a.chart p.1 p.2)
def coordinate : a.Rep → ℝ := Sum.elim (fun _ => 1) (fun p => ‖p.2.val‖)

@[simp] theorem disk_norm_le (z : Disk n) : ‖z.val‖ ≤ 1 := by
  simpa only [mem_closedBall,dist_zero_right] using z.property

theorem coordinate_eq_of_q_eq (p r : a.Rep) (h : a.q p = a.q r) :
    a.coordinate p = a.coordinate r := by
  cases p with
  | inl x =>
    cases r with
    | inl y => rfl
    | inr p =>
      change x.val = a.chart p.1 p.2 at h
      change (1:ℝ) = ‖p.2.val‖
      apply le_antisymm _ (disk_norm_le p.2)
      by_contra hn
      exact a.interior p.1 p.2 (lt_of_not_ge hn) (h ▸ x.property)
  | inr p =>
    cases r with
    | inl x =>
      change a.chart p.1 p.2 = x.val at h
      change ‖p.2.val‖ = 1
      apply le_antisymm (disk_norm_le p.2)
      by_contra hn
      exact a.interior p.1 p.2 (lt_of_not_ge hn) (h.symm ▸ x.property)
    | inr r =>
      change a.chart p.1 p.2 = a.chart r.1 r.2 at h
      change ‖p.2.val‖ = ‖r.2.val‖
      by_cases hp : ‖p.2.val‖ < 1
      · have hr : ‖r.2.val‖ < 1 := by
          by_contra hr
          have hr' : ‖r.2.val‖ = 1 := le_antisymm (disk_norm_le r.2) (le_of_not_gt hr)
          exact a.interior p.1 p.2 hp (h.symm ▸ a.boundary r.1 r.2 hr')
        exact congrArg (fun z : Disk n => ‖z.val‖) (a.disjoint p.1 r.1 p.2 r.2 hp hr h).2
      · have hp' : ‖p.2.val‖ = 1 := le_antisymm (disk_norm_le p.2) (le_of_not_gt hp)
        have hr : ¬ ‖r.2.val‖ < 1 := fun hr =>
          a.interior r.1 r.2 hr (h ▸ a.boundary p.1 p.2 hp')
        exact hp'.trans (le_antisymm (disk_norm_le r.2) (le_of_not_gt hr)).symm

def representative (x : X) : a.Rep := (a.quotient.surjective x).choose
@[simp] theorem q_representative (x : X) : a.q (a.representative x) = x :=
  (a.quotient.surjective x).choose_spec

def radius (x : X) : ℝ := a.coordinate (a.representative x)
@[simp] theorem radius_q (p : a.Rep) : a.radius (a.q p) = a.coordinate p :=
  a.coordinate_eq_of_q_eq _ _ (a.q_representative _)

theorem coordinate_continuous : Continuous a.coordinate := by
  apply Continuous.sumElim continuous_const
  exact continuous_sigma (fun _ => continuous_norm.comp continuous_subtype_val)

theorem radius_continuous : Continuous a.radius := by
  apply a.quotient.continuous_iff.mpr
  change Continuous (a.radius ∘ a.q)
  simpa only [Function.comp_def,a.radius_q] using a.coordinate_continuous

@[simp] theorem radius_lower (x : a.lower) : a.radius x.val = 1 := a.radius_q (.inl x)
@[simp] theorem radius_chart (j : J) (z : Disk n) : a.radius (a.chart j z) = ‖z.val‖ :=
  a.radius_q (.inr ⟨j,z⟩)

theorem radius_eq_one_iff (x : X) : a.radius x = 1 ↔ x ∈ a.lower := by
  constructor
  · intro h
    obtain ⟨p,rfl⟩ := a.quotient.surjective x
    change a.radius (a.q p) = 1 at h
    rw [a.radius_q] at h
    cases p with
    | inl y => exact y.property
    | inr p => exact a.boundary p.1 p.2 h
  · intro h
    exact a.radius_lower ⟨x,h⟩

def outer : Set X := {x | 0 < a.radius x}
def inner : Set X := {x | a.radius x < 1}
theorem outer_open : IsOpen a.outer := isOpen_lt continuous_const a.radius_continuous
theorem inner_open : IsOpen a.inner := isOpen_lt a.radius_continuous continuous_const
theorem outer_union_inner : a.outer ∪ a.inner = univ := by
  ext x
  simp only [mem_union,mem_univ,iff_true]
  change 0 < a.radius x ∨ a.radius x < 1
  by_cases h : 0 < a.radius x
  · exact Or.inl h
  · exact Or.inr (by linarith)

theorem lower_subset_outer : a.lower ⊆ a.outer := by
  intro x hx
  change 0 < a.radius x
  rw [(a.radius_eq_one_iff x).mpr hx]
  norm_num

end Attachment
end EilenbergGanea.CWCollar

namespace EilenbergGanea.CWCollar
open Classical Set Metric Topology CWCover
open scoped unitInterval
variable {n : ℕ}
abbrev PuncturedDisk (n : ℕ) := {z : Disk n // 0 < ‖z.val‖}
def radialScale (t : I) (z : PuncturedDisk n) : ℝ := (1-t.val) + t.val / ‖z.val.val‖

theorem radialScale_nonneg (t : I) (z : PuncturedDisk n) : 0 ≤ radialScale t z :=
  add_nonneg (sub_nonneg.mpr t.property.2) (div_nonneg t.property.1 (norm_nonneg _))

def radialCoords (t : I) (z : PuncturedDisk n) : Fin n → ℝ := radialScale t z • z.val.val

theorem radialCoords_norm (t : I) (z : PuncturedDisk n) :
    ‖radialCoords t z‖ = (1-t.val)*‖z.val.val‖ + t.val := by
  rw [radialCoords,norm_smul,Real.norm_eq_abs,abs_of_nonneg (radialScale_nonneg t z)]
  dsimp [radialScale]
  rw [add_mul,div_mul_cancel₀ _ (ne_of_gt z.property)]

theorem radialCoords_pos (t : I) (z : PuncturedDisk n) : 0 < ‖radialCoords t z‖ := by
  rw [radialCoords_norm]
  have hz := z.property
  have hb := Attachment.disk_norm_le z.val
  have ht := mul_nonneg t.property.1 (sub_nonneg.mpr hb)
  nlinarith

theorem radialCoords_le (t : I) (z : PuncturedDisk n) : ‖radialCoords t z‖ ≤ 1 := by
  rw [radialCoords_norm]
  have h := mul_nonneg (sub_nonneg.mpr t.property.2) (sub_nonneg.mpr (Attachment.disk_norm_le z.val))
  nlinarith

def radialDisk (t : I) (z : PuncturedDisk n) : PuncturedDisk n :=
  ⟨⟨radialCoords t z,by simpa only [mem_closedBall,dist_zero_right] using radialCoords_le t z⟩,
    radialCoords_pos t z⟩

@[simp] theorem radialDisk_zero (z : PuncturedDisk n) : radialDisk 0 z = z := by
  apply Subtype.ext
  apply Subtype.ext
  simp [radialDisk,radialCoords,radialScale]

@[simp] theorem radialDisk_norm_one (z : PuncturedDisk n) : ‖(radialDisk 1 z).val.val‖ = 1 := by
  change ‖radialCoords 1 z‖ = 1
  rw [radialCoords_norm]
  norm_num

theorem radialDisk_boundary (t : I) (z : PuncturedDisk n) (hz : ‖z.val.val‖ = 1) :
    radialDisk t z = z := by
  apply Subtype.ext
  apply Subtype.ext
  change ((1-t.val) + t.val / ‖z.val.val‖) • z.val.val = z.val.val
  rw [hz,div_one,sub_add_cancel,one_smul]

theorem radialDisk_continuous : Continuous (fun p : I × PuncturedDisk n => radialDisk p.1 p.2) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  change Continuous (fun p : I × PuncturedDisk n =>
    ((1-p.1.val) + p.1.val / ‖p.2.val.val‖) • p.2.val.val)
  have hz : Continuous (fun p : I × PuncturedDisk n => p.2.val.val) := by fun_prop
  exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).add
    ((continuous_subtype_val.comp continuous_fst).div (continuous_norm.comp hz)
      (fun p => ne_of_gt p.2.property))).smul hz

end EilenbergGanea.CWCollar

namespace EilenbergGanea.CWCollar
open Classical Set Metric Topology CWCover
open scoped unitInterval
variable {X J : Type*} [TopologicalSpace X] {n : ℕ}
namespace Attachment
variable (a : Attachment X J n)
abbrev OuterRep := a.lower ⊕ (Σ _ : J, PuncturedDisk n)

def outerIn : a.OuterRep → a.Rep := Sum.map id (Sigma.map id (fun _ z => z.val))
def outerQ : a.OuterRep → a.outer := fun p => ⟨a.q (a.outerIn p),by
  change 0 < a.radius (a.q (a.outerIn p))
  rw [a.radius_q]
  cases p with
  | inl x => exact (zero_lt_one : (0:ℝ) < 1)
  | inr p => exact p.2.property⟩

theorem outerIn_continuous : Continuous a.outerIn :=
  continuous_id.sumMap (continuous_sigma fun _ => continuous_sigmaMk.comp continuous_subtype_val)

theorem outerIn_openMap : IsOpenMap a.outerIn :=
  IsOpenMap.id.sumMap (isOpenMap_sigma.mpr (fun _ => isOpenMap_sigmaMk.comp
    ((isOpen_lt continuous_const (continuous_norm.comp continuous_subtype_val)).isOpenMap_subtype_val)))

theorem outerQ_continuous : Continuous a.outerQ :=
  (a.quotient.continuous.comp a.outerIn_continuous).subtype_mk _

theorem range_outerIn : Set.range a.outerIn = {p | 0 < a.coordinate p} := by
  ext p
  constructor
  · rintro ⟨p,rfl⟩
    cases p with
    | inl x => exact (zero_lt_one : (0:ℝ) < 1)
    | inr p => exact p.2.property
  · intro hp
    cases p with
    | inl x => exact ⟨.inl x,rfl⟩
    | inr p => exact ⟨.inr ⟨p.1,⟨p.2,hp⟩⟩,rfl⟩

theorem outerQ_surjective : Function.Surjective a.outerQ := by
  intro x
  obtain ⟨p,hp⟩ := a.quotient.surjective x.val
  change a.q p = x.val at hp
  have hr : 0 < a.coordinate p := by
    rw [← a.radius_q]
    rw [hp]
    exact x.property
  obtain ⟨r,rfl⟩ := (show p ∈ Set.range a.outerIn from by rw [a.range_outerIn]; exact hr)
  exact ⟨r,Subtype.ext hp⟩

theorem outerQ_quotient : IsQuotientMap a.outerQ := by
  refine ⟨IsCoinducing.of_isOpen_preimage_iff_isOpen (fun A => ?_),a.outerQ_surjective⟩
  constructor
  · intro hA
    have he : a.outerIn '' (a.outerQ ⁻¹' A) = a.q ⁻¹' ((Subtype.val : a.outer → X) '' A) := by
      ext p
      constructor
      · rintro ⟨r,hr,rfl⟩
        exact ⟨a.outerQ r,hr,rfl⟩
      · rintro ⟨x,hx,hp⟩
        have hr : 0 < a.coordinate p := by
          rw [← a.radius_q,← hp]
          exact x.property
        obtain ⟨r,rfl⟩ := (show p ∈ Set.range a.outerIn from by rw [a.range_outerIn]; exact hr)
        refine ⟨r,?_,rfl⟩
        have hh : a.outerQ r = x := Subtype.ext hp.symm
        change a.outerQ r ∈ A
        rw [hh]
        exact hx
    have ho : IsOpen ((Subtype.val : a.outer → X) '' A) :=
      a.quotient.isOpen_preimage.mp (he ▸ a.outerIn_openMap _ hA)
    have := ho.preimage (continuous_subtype_val (p := fun x => x ∈ a.outer))
    simpa only [Set.preimage_image_eq _ Subtype.val_injective] using this
  · intro hA
    exact hA.preimage a.outerQ_continuous

end Attachment

theorem continuous_sum_prod {A B C T : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace C] [TopologicalSpace T] {f : (A ⊕ B) × T → C}
    (hA : Continuous (fun p : A × T => f (.inl p.1,p.2)))
    (hB : Continuous (fun p : B × T => f (.inr p.1,p.2))) : Continuous f := by
  have h : Continuous (f ∘ (Homeomorph.sumProdDistrib : (A ⊕ B) × T ≃ₜ (A × T) ⊕ (B × T)).symm) :=
    continuous_sum_dom.mpr ⟨hA,hB⟩
  simpa only [Function.comp_def,Homeomorph.symm_apply_apply] using h.comp (Homeomorph.sumProdDistrib).continuous

theorem continuous_sigma_prod {A : Type*} {B : A → Type*} {C T : Type*}
    [∀ a,TopologicalSpace (B a)] [TopologicalSpace C] [TopologicalSpace T]
    {f : (Sigma B) × T → C}
    (h : ∀ a, Continuous (fun p : B a × T => f (⟨a,p.1⟩,p.2))) : Continuous f := by
  have hh : Continuous (f ∘ (Homeomorph.sigmaProdDistrib : (Sigma B) × T ≃ₜ Σ a,B a × T).symm) :=
    continuous_sigma h
  simpa only [Function.comp_def,Homeomorph.symm_apply_apply] using hh.comp (Homeomorph.sigmaProdDistrib).continuous

namespace Attachment
variable (a : Attachment X J n)
def repFlow : a.OuterRep × I → a.OuterRep := fun p =>
  match p.1 with
  | .inl x => .inl x
  | .inr c => .inr ⟨c.1,radialDisk p.2 c.2⟩

theorem repFlow_continuous : Continuous a.repFlow := by
  apply continuous_sum_prod
  · exact continuous_inl.comp continuous_fst
  · apply continuous_sigma_prod
    intro j
    exact continuous_inr.comp (continuous_sigmaMk.comp (radialDisk_continuous.comp continuous_swap))

@[simp] theorem repFlow_zero (p : a.OuterRep) : a.repFlow (p,0) = p := by
  cases p with
  | inl x => rfl
  | inr c => simp [repFlow]

theorem outerQ_repFlow_one (p : a.OuterRep) : (a.outerQ (a.repFlow (p,1))).val ∈ a.lower := by
  cases p with
  | inl x => exact x.property
  | inr c => exact a.boundary c.1 (radialDisk 1 c.2).val (radialDisk_norm_one c.2)

theorem repFlow_respects (t : I) {p r : a.OuterRep} (h : a.outerQ p = a.outerQ r) :
    a.outerQ (a.repFlow (p,t)) = a.outerQ (a.repFlow (r,t)) := by
  apply Subtype.ext
  have h' := congrArg Subtype.val h
  cases p with
  | inl x =>
    cases r with
    | inl y => exact h'
    | inr c =>
      change x.val = a.chart c.1 c.2.val at h'
      have hc : ‖c.2.val.val‖ = 1 := by
        rw [← a.radius_chart,← h',a.radius_lower]
      change x.val = a.chart c.1 (radialDisk t c.2).val
      rw [radialDisk_boundary t c.2 hc]
      exact h'
  | inr c =>
    cases r with
    | inl x =>
      change a.chart c.1 c.2.val = x.val at h'
      have hc : ‖c.2.val.val‖ = 1 := by
        rw [← a.radius_chart,h',a.radius_lower]
      change a.chart c.1 (radialDisk t c.2).val = x.val
      rw [radialDisk_boundary t c.2 hc]
      exact h'
    | inr d =>
      change a.chart c.1 c.2.val = a.chart d.1 d.2.val at h'
      by_cases hc : ‖c.2.val.val‖ < 1
      · have hd : ‖d.2.val.val‖ < 1 := by
          rw [← a.radius_chart,← h',a.radius_chart]
          exact hc
        obtain ⟨hj,hz⟩ := a.disjoint c.1 d.1 c.2.val d.2.val hc hd h'
        have he : c = d := by
          cases c with
          | mk j z =>
            cases d with
            | mk k w =>
              dsimp at hj hz
              subst k
              have hw : z = w := Subtype.ext hz
              subst w
              rfl
        subst d
        rfl
      · have hc' : ‖c.2.val.val‖ = 1 := le_antisymm (disk_norm_le c.2.val) (le_of_not_gt hc)
        have hd : ‖d.2.val.val‖ = 1 := by rw [← a.radius_chart,← h',a.radius_chart,hc']
        change a.chart c.1 (radialDisk t c.2).val = a.chart d.1 (radialDisk t d.2).val
        rw [radialDisk_boundary t c.2 hc',radialDisk_boundary t d.2 hd]
        exact h'

end Attachment
end EilenbergGanea.CWCollar

namespace EilenbergGanea.CWCollar.Attachment
open Classical Set Metric Topology
open scoped unitInterval
variable {X J : Type*} [TopologicalSpace X] {n : ℕ} (a : Attachment X J n)

def outerRepresentative (x : a.outer) : a.OuterRep := (a.outerQ_surjective x).choose
@[simp] theorem outerQ_representative (x : a.outer) : a.outerQ (a.outerRepresentative x) = x :=
  (a.outerQ_surjective x).choose_spec

def flow (p : a.outer × I) : a.outer := a.outerQ (a.repFlow (a.outerRepresentative p.1,p.2))
@[simp] theorem flow_q (p : a.OuterRep) (t : I) : a.flow (a.outerQ p,t) = a.outerQ (a.repFlow (p,t)) :=
  a.repFlow_respects t (a.outerQ_representative (a.outerQ p))

theorem flow_continuous : Continuous a.flow := by
  apply a.outerQ_quotient.continuous_lift_prod_left
  have h := a.outerQ_continuous.comp a.repFlow_continuous
  simpa only [Function.comp_def,a.flow_q] using h

@[simp] theorem flow_zero (x : a.outer) : a.flow (x,0) = x := by
  change a.outerQ (a.repFlow (a.outerRepresentative x,0)) = x
  rw [a.repFlow_zero,a.outerQ_representative]

theorem flow_one_lower (x : a.outer) : (a.flow (x,1)).val ∈ a.lower :=
  a.outerQ_repFlow_one (a.outerRepresentative x)

def sectionMap : C(a.lower,a.outer) :=
  ⟨fun x => ⟨x.val,a.lower_subset_outer x.property⟩,continuous_subtype_val.subtype_mk _⟩

def retractMap : C(a.outer,a.lower) :=
  ⟨fun x => ⟨(a.flow (x,1)).val,a.flow_one_lower x⟩,
    (continuous_subtype_val.comp (a.flow_continuous.comp (continuous_id.prodMk continuous_const))).subtype_mk _⟩

@[simp] theorem flow_section (x : a.lower) (t : I) : a.flow (a.sectionMap x,t) = a.sectionMap x := by
  change a.flow (a.outerQ (.inl x),t) = a.outerQ (.inl x)
  rw [a.flow_q]
  rfl

@[simp] theorem retract_section (x : a.lower) : a.retractMap (a.sectionMap x) = x := by
  apply Subtype.ext
  change (a.flow (a.sectionMap x,1)).val = x.val
  exact congrArg Subtype.val (a.flow_section x 1)

end EilenbergGanea.CWCollar.Attachment

namespace EilenbergGanea.CWCollar
open Classical Set Metric Topology CWCover
variable {X J : Type*} [TopologicalSpace X] {n : ℕ}
abbrev OpenDisk (n : ℕ) := {z : Disk n // ‖z.val‖ < 1}
namespace Attachment
variable (a : Attachment X J n)

theorem q_injective_interior {p r : a.Rep} (hp : a.coordinate p < 1) (h : a.q p = a.q r) : p = r := by
  have hr : a.coordinate r < 1 := (a.coordinate_eq_of_q_eq p r h) ▸ hp
  cases p with
  | inl x => exact (lt_irrefl (1:ℝ) hp).elim
  | inr p =>
    cases r with
    | inl x => exact (lt_irrefl (1:ℝ) hr).elim
    | inr r =>
      obtain ⟨hj,hz⟩ := a.disjoint p.1 r.1 p.2 r.2 hp hr h
      congr 1
      exact Sigma.ext hj (heq_of_eq hz)

def innerIn : (Σ _ : J, OpenDisk n) → a.Rep := fun p => .inr ⟨p.1,p.2.val⟩
def innerQ : (Σ _ : J, OpenDisk n) → a.inner := fun p => ⟨a.q (a.innerIn p),by
  change a.radius (a.chart p.1 p.2.val) < 1
  rw [a.radius_chart]
  exact p.2.property⟩

theorem innerIn_continuous : Continuous a.innerIn :=
  continuous_inr.comp (continuous_sigma fun _ => continuous_sigmaMk.comp continuous_subtype_val)

theorem innerIn_openMap : IsOpenMap a.innerIn :=
  isOpenMap_inr.comp (isOpenMap_sigma.mpr (fun _ => isOpenMap_sigmaMk.comp
    ((isOpen_lt (continuous_norm.comp continuous_subtype_val) continuous_const).isOpenMap_subtype_val)))

theorem innerQ_continuous : Continuous a.innerQ :=
  (a.quotient.continuous.comp a.innerIn_continuous).subtype_mk _

theorem innerQ_injective : Function.Injective a.innerQ := by
  intro p r h
  have he := a.q_injective_interior (p := a.innerIn p) (r := a.innerIn r) p.2.property (congrArg Subtype.val h)
  have hh : (⟨p.1,p.2.val⟩ : Σ _ : J, Disk n) = ⟨r.1,r.2.val⟩ := Sum.inr_injective he
  cases p with
  | mk j z =>
    cases r with
    | mk k w =>
      have hj : j = k := congrArg Sigma.fst hh
      subst k
      have hz : z.val = w.val := by simpa only [Sigma.mk.inj_iff,heq_eq_eq,true_and] using hh
      have hz' : z = w := Subtype.ext hz
      subst w
      rfl

theorem innerQ_surjective : Function.Surjective a.innerQ := by
  intro x
  obtain ⟨p,hp⟩ := a.quotient.surjective x.val
  change a.q p = x.val at hp
  have hr : a.coordinate p < 1 := by rw [← a.radius_q,hp]; exact x.property
  cases p with
  | inl y => exact (lt_irrefl (1:ℝ) hr).elim
  | inr p => exact ⟨⟨p.1,⟨p.2,hr⟩⟩,Subtype.ext hp⟩

theorem innerQ_openMap : IsOpenMap a.innerQ := by
  have h : IsOpenMap (a.q ∘ a.innerIn) := by
    intro W hW
    apply a.quotient.isOpen_preimage.mp
    have he : a.q ⁻¹' ((a.q ∘ a.innerIn) '' W) = a.innerIn '' W := by
      ext p
      constructor
      · rintro ⟨r,hr,he⟩
        exact ⟨r,hr,a.q_injective_interior (p := a.innerIn r) r.2.property he⟩
      · rintro ⟨r,hr,rfl⟩
        exact ⟨r,hr,rfl⟩
    change IsOpen (a.q ⁻¹' ((a.q ∘ a.innerIn) '' W))
    rw [he]
    exact a.innerIn_openMap W hW
  exact h.subtype_mk _

/-- Actual pairwise-disjoint open top-dimensional cells, including arbitrary
index universes, with their ordinary disk interiors. -/
def innerHomeomorph : (Σ _ : J, OpenDisk n) ≃ₜ a.inner :=
  (Equiv.ofBijective a.innerQ ⟨a.innerQ_injective,a.innerQ_surjective⟩).toHomeomorphOfContinuousOpen
    a.innerQ_continuous a.innerQ_openMap

end Attachment
end EilenbergGanea.CWCollar

namespace EilenbergGanea.CWCollar
open Set Metric Topology CWCover
variable {X J : Type*} [TopologicalSpace X] {n : ℕ}
abbrev Annulus (n : ℕ) := {z : OpenDisk n // 0 < ‖z.val.val‖}

def annulusSigmaIn : (Σ _ : J, Annulus n) → (Σ _ : J, OpenDisk n) :=
  fun p => ⟨p.1,p.2.val⟩

theorem annulusSigmaIn_continuous : Continuous (annulusSigmaIn (J:=J) (n:=n)) :=
  continuous_sigma (fun _ => continuous_sigmaMk.comp continuous_subtype_val)

theorem annulusSigmaIn_openMap : IsOpenMap (annulusSigmaIn (J:=J) (n:=n)) :=
  isOpenMap_sigma.mpr (fun _ => isOpenMap_sigmaMk.comp
    ((isOpen_lt continuous_const (continuous_norm.comp (continuous_subtype_val.comp continuous_subtype_val))).isOpenMap_subtype_val))

def annulusSigmaHomeomorph : (Σ _ : J, Annulus n) ≃ₜ
    {p : (Σ _ : J, OpenDisk n) // 0 < ‖p.2.val.val‖} :=
  (show (Σ _ : J, Annulus n) ≃ {p : (Σ _ : J, OpenDisk n) // 0 < ‖p.2.val.val‖} from
    { toFun := fun p => ⟨annulusSigmaIn p,p.2.property⟩
      invFun := fun p => ⟨p.val.1,⟨p.val.2,p.property⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }).toHomeomorphOfContinuousOpen
    (annulusSigmaIn_continuous.subtype_mk _) (annulusSigmaIn_openMap.subtype_mk _)

namespace Attachment
variable (a : Attachment X J n)

def innerOuterHomeomorph : {x : a.inner // x.val ∈ a.outer} ≃ₜ (a.outer ∩ a.inner : Set X) where
  toFun x := ⟨x.val.val,x.property,x.val.property⟩
  invFun x := ⟨⟨x.val,x.property.2⟩,x.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- The actual overlap of the two CW collar open sets is the disjoint union of
punctured open disks, even for an unrestricted cell index. -/
def annulusHomeomorph : (Σ _ : J, Annulus n) ≃ₜ (a.outer ∩ a.inner : Set X) :=
  annulusSigmaHomeomorph.trans ((a.innerHomeomorph.subtype (p := fun p => 0 < ‖p.2.val.val‖)
    (q := fun x => x.val ∈ a.outer) (by
      intro p
      change (0 < ‖p.2.val.val‖) ↔ (0 < a.radius (a.chart p.1 p.2.val))
      rw [a.radius_chart])).trans a.innerOuterHomeomorph)

end Attachment
end EilenbergGanea.CWCollar

namespace EilenbergGanea.CWCollar
open Set Metric Topology CWCover

def openDiskBallHomeomorph (n : ℕ) : OpenDisk n ≃ₜ ball (0 : Fin n → ℝ) 1 where
  toFun z := ⟨z.val.val,by simpa only [mem_ball,dist_zero_right] using z.property⟩
  invFun z := ⟨⟨z.val,ball_subset_closedBall z.property⟩,by simpa only [mem_ball,dist_zero_right] using z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

def spaceOpenDiskHomeomorph (n : ℕ) : (Fin n → ℝ) ≃ₜ OpenDisk n :=
  Homeomorph.unitBall.trans (openDiskBallHomeomorph n).symm

@[simp] theorem spaceOpenDiskHomeomorph_zero (n : ℕ) :
    (spaceOpenDiskHomeomorph n 0).val.val = 0 := Homeomorph.coe_unitBall_apply_zero

def puncturedAnnulusHomeomorph (n : ℕ) : ({0}ᶜ : Set (Fin n → ℝ)) ≃ₜ Annulus n :=
  (spaceOpenDiskHomeomorph n).subtype (p := fun x => x ∈ ({0}ᶜ : Set (Fin n → ℝ)))
    (q := fun z => 0 < ‖z.val.val‖) (by
      intro x
      simp only [mem_compl_iff,mem_singleton_iff,norm_pos_iff]
      have he : (spaceOpenDiskHomeomorph n x).val.val = 0 ↔ x = 0 := by
        constructor
        · intro h
          apply (spaceOpenDiskHomeomorph n).injective
          apply Subtype.ext
          apply Subtype.ext
          simpa only [spaceOpenDiskHomeomorph_zero] using h
        · rintro rfl; exact spaceOpenDiskHomeomorph_zero n
      exact not_congr he.symm)

instance annulusTwoPathConnected : PathConnectedSpace (Annulus 2) := by
  have hr : 1 < Module.rank ℝ (Fin 2 → ℝ) := by simp
  let : PathConnectedSpace ({0}ᶜ : Set (Fin 2 → ℝ)) :=
    isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_compl_singleton_of_one_lt_rank hr 0)
  exact (puncturedAnnulusHomeomorph 2).surjective.pathConnectedSpace (puncturedAnnulusHomeomorph 2).continuous

end EilenbergGanea.CWCollar

namespace EilenbergGanea.CWCollar
open Set Metric Topology CWCover CategoryTheory
open scoped ContinuousMap

def planeComplexHomeomorph : (Fin 2 → ℝ) ≃ₜ ℂ :=
  (Homeomorph.piFinTwo (fun _ => ℝ)).trans Complex.equivRealProdCLM.symm.toHomeomorph

@[simp] theorem planeComplexHomeomorph_zero : planeComplexHomeomorph 0 = 0 := by
  simp [planeComplexHomeomorph,Homeomorph.piFinTwo]

def puncturedPlaneComplexHomeomorph : ({0}ᶜ : Set (Fin 2 → ℝ)) ≃ₜ ({0}ᶜ : Set ℂ) :=
  planeComplexHomeomorph.subtype (p := fun x => x ∈ ({0}ᶜ : Set (Fin 2 → ℝ)))
    (q := fun z => z ∈ ({0}ᶜ : Set ℂ)) (by
      intro x
      simp only [mem_compl_iff,mem_singleton_iff]
      constructor
      · intro hx he
        apply hx
        apply planeComplexHomeomorph.injective
        simpa only [planeComplexHomeomorph_zero] using he
      · intro hx he
        apply hx
        rw [he,planeComplexHomeomorph_zero])

def circleSphereHomeomorph : sphere (0 : ℂ) 1 ≃ₜ Circle :=
  Homeomorph.setCongr rfl

def annulusCircleProdHomeomorph : Annulus 2 ≃ₜ Circle × Ioi (0 : ℝ) :=
  (puncturedAnnulusHomeomorph 2).symm.trans (puncturedPlaneComplexHomeomorph.trans
    ((homeomorphUnitSphereProd ℂ).trans (circleSphereHomeomorph.prodCongr (Homeomorph.refl _))))

instance positiveRealsContractible : ContractibleSpace (Ioi (0 : ℝ)) :=
  (convex_Ioi (0 : ℝ)).contractibleSpace ⟨1,by norm_num⟩

noncomputable def annulusCircleEquiv : Annulus 2 ≃ₕ Circle :=
  annulusCircleProdHomeomorph.toHomotopyEquiv.trans
    (((ContinuousMap.HomotopyEquiv.refl Circle).prodCongr (ContractibleSpace.hequiv_unit (Ioi (0:ℝ))).some).trans
      (Homeomorph.prodUnique Circle Unit).toHomotopyEquiv)

noncomputable def homotopyFundamentalEquiv {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₕ Y) (x : X) : FundamentalGroup X x ≃* FundamentalGroup Y (e x) :=
  MulEquiv.ofBijective (FundamentalGroup.map e.toFun x)
    (FundamentalGroupoidFunctor.equivOfHomotopyEquiv e).fullyFaithfulFunctor.homEquiv.bijective

noncomputable def periodIntEquiv : ℤ ≃+ AddSubgroup.zmultiples (2 * Real.pi) := by
  let f : ℤ →+ AddSubgroup.zmultiples (2 * Real.pi) :=
    { toFun := fun n => ⟨n • (2 * Real.pi),AddSubgroup.zsmul_mem_zmultiples _ _⟩
      map_zero' := Subtype.ext (zero_zsmul _)
      map_add' := fun m n => Subtype.ext (add_zsmul _ _ _) }
  apply AddEquiv.ofBijective f
  constructor
  · intro m n h
    have he := congrArg Subtype.val h
    change m • (2*Real.pi) = n • (2*Real.pi) at he
    simp only [zsmul_eq_mul] at he
    exact_mod_cast mul_right_cancel₀ (show 2*Real.pi ≠ 0 by positivity) he
  · intro x
    obtain ⟨n,hn⟩ := AddSubgroup.mem_zmultiples_iff.mp x.property
    exact ⟨n,Subtype.ext hn⟩

noncomputable def circleFundamentalInt : FundamentalGroup Circle 1 ≃* Multiplicative ℤ := by
  let : ContractibleSpace ℝ := inferInstance
  exact (Circle.isAddQuotientCoveringMap_exp.fundamentalGroupEquiv (⟨0,by simp⟩ : Circle.exp ⁻¹' {1})).trans
    ((MulEquiv.inv' (Multiplicative (AddSubgroup.zmultiples (2*Real.pi)))).symm.trans
      periodIntEquiv.symm.toMultiplicative)

noncomputable def annulusFundamentalInt (x : Annulus 2) : FundamentalGroup (Annulus 2) x ≃* Multiplicative ℤ :=
  (homotopyFundamentalEquiv annulusCircleEquiv x).trans
    ((FundamentalGroup.fundamentalGroupMulEquivOfPathConnected (annulusCircleEquiv x) 1).trans circleFundamentalInt)

end EilenbergGanea.CWCollar

namespace EilenbergGanea.CWCollar
open CubicalSingular PathTransport

noncomputable def annulusOppositeInt (x : Annulus 2) : (FundamentalGroup (Annulus 2) x)ᵐᵒᵖ ≃* Multiplicative ℤ :=
  (annulusFundamentalInt x).op.trans (MulEquiv.inv' (Multiplicative ℤ)).symm

noncomputable def annulusAbInt (x : Annulus 2) : AbLoops (Annulus 2) x ≃ₗ[ℤ] ℤ :=
  (((annulusOppositeInt x).abelianizationCongr.trans (Abelianization.equivOfComm (H:=Multiplicative ℤ)).symm).toAdditive).toIntLinearEquiv

noncomputable def annulusHomologyInt (x : Annulus 2) : HomologyOne (Annulus 2) ≃ₗ[ℤ] ℤ :=
  (hurewiczOne (fun y => (PathConnectedSpace.joined x y).somePath)).trans (annulusAbInt x)

def loopCycle {X : Type*} [TopologicalSpace X] {x : X} (p : Path x x) : cyclesOn (Set.univ : Set X) :=
  ⟨gen₁ p.toContinuousMap,by rw [L₁_univ]; trivial,by
    change d₁ (gen₁ p.toContinuousMap) = 0
    simp only [gen₁,d₁_mk,b₁_single,one_smul]
    change Finsupp.single (p 1) (1:ℤ) - Finsupp.single (p 0) (1:ℤ) = 0
    rw [p.target,p.source,sub_self]⟩

def loopHomology {X : Type*} [TopologicalSpace X] {x : X} (p : Path x x) : HomologyOne X :=
  (boundaries Set.univ).mkQ (loopCycle p)

end EilenbergGanea.CWCollar


end

end OAI
end

section
-- module Solutions.OAIEG.CWComplex_CellularPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Metric Topology

namespace EilenbergGanea.CubicalSingular
open Set
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

@[simp] theorem homologyOneMap_const (y : Y) : homologyOneMap (ContinuousMap.const X y) = 0 := by
  apply LinearMap.ext
  intro h
  obtain ⟨z,rfl⟩ := (boundaries (univ : Set X)).mkQ_surjective h
  change (boundaries univ).mkQ (cycleMap (ContinuousMap.const X y) _ z) = 0
  have he : cycleMap (ContinuousMap.const X y) (mapsTo_univ _ _) z = 0 := by
    apply Subtype.ext
    exact pushN₁_const y z.val
  rw [he,map_zero]

variable {J : Type*} (y₀ : Y)

def fiberInclusion (j : J) : C(Y,(Σ _ : J,Y)) := ⟨@Sigma.mk J (fun _ : J => Y) j,by exact @continuous_sigmaMk J (fun _ : J => Y) (fun _ => inferInstance) j⟩

end EilenbergGanea.CubicalSingular

namespace EilenbergGanea.PathTransport
open Set CubicalSingular
variable {X G : Type*} [TopologicalSpace X] [Group G]

variable {U V : Set X} {r : U} (q : ∀ x : U, Path r x) (ρ : (FundamentalGroup U r)ᵐᵒᵖ →* G)

def capInclusion : C((U ∩ V : Set X),U) := ⟨fun z => ⟨z.val,z.property.1⟩,continuous_subtype_val.subtype_mk _⟩

end EilenbergGanea.PathTransport

namespace EilenbergGanea.CubicalSingular
open Set
variable {J : Type*} {Y : J → Type*} [∀ j, TopologicalSpace (Y j)]

noncomputable def sigmaCenter [∀ j, ContractibleSpace (Y j)] (j : J) : Y j :=
  (id_nullhomotopic (Y j)).choose
noncomputable def sigmaContraction [∀ j, ContractibleSpace (Y j)] (j : J) :
    (ContinuousMap.id (Y j)).Homotopy (ContinuousMap.const (Y j) (sigmaCenter (Y:=Y) j)) :=
  (id_nullhomotopic (Y j)).choose_spec.some

noncomputable def sigmaCollapse [∀ j, ContractibleSpace (Y j)] : C((Σ j,Y j),(Σ j,Y j)) :=
  ⟨fun x => ⟨x.1,sigmaCenter (Y:=Y) x.1⟩,continuous_sigma (fun j => by
    change Continuous (fun _ : Y j => (⟨j,sigmaCenter (Y:=Y) j⟩ : Σ j,Y j))
    exact continuous_const)⟩

noncomputable def sigmaHomotopy [∀ j, ContractibleSpace (Y j)] :
    (ContinuousMap.id (Σ j,Y j)).Homotopy (sigmaCollapse (Y:=Y)) where
  toFun p := ⟨p.2.1,sigmaContraction (Y:=Y) p.2.1 (p.1,p.2.2)⟩
  continuous_toFun := by
    have hc : Continuous (fun p : Σ j, Y j × I =>
        (⟨p.1,sigmaContraction (Y:=Y) p.1 (p.2.2,p.2.1)⟩ : Σ j,Y j)) :=
      continuous_sigma (fun j => continuous_sigmaMk.comp ((sigmaContraction (Y:=Y) j).continuous.comp continuous_swap))
    exact hc.comp ((Homeomorph.sigmaProdDistrib (X:=Y) (Y:=I)).continuous.comp continuous_swap)
  map_zero_left x := by congr 1; exact (sigmaContraction (Y:=Y) x.1).apply_zero x.2
  map_one_left x := by
    change (⟨x.1,sigmaContraction (Y:=Y) x.1 (1,x.2)⟩ : Σ j,Y j) = ⟨x.1,sigmaCenter (Y:=Y) x.1⟩
    congr 1
    exact (sigmaContraction (Y:=Y) x.1).apply_one x.2

theorem push_sigmaCollapse_zero [∀ j, ContractibleSpace (Y j)] (c : N₁ (Σ j,Y j)) :
    pushN₁ (sigmaCollapse (Y:=Y)) c = 0 := by
  obtain ⟨c,rfl⟩ := (D₁ (Σ j,Y j)).mkQ_surjective c
  change (D₁ (Σ j,Y j)).mkQ (push₁ sigmaCollapse c) = 0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simpa only [map_add] using (D₁ (Σ j,Y j)).add_mem hc hd
  | single σ m =>
    obtain ⟨j,g,hg,he⟩ := σ.continuous.exists_lift_sigma
    have hcomp : (sigmaCollapse (Y:=Y)).comp σ = constant₁ (⟨j,sigmaCenter (Y:=Y) j⟩ : Σ j,Y j) := by
      apply ContinuousMap.ext
      intro t
      change (⟨(σ t).1,sigmaCenter (Y:=Y) (σ t).1⟩ : Σ j,Y j) = ⟨j,sigmaCenter (Y:=Y) j⟩
      rw [congrFun he t]
      rfl
    rw [push₁_single,hcomp,← Finsupp.smul_single_one]
    exact (D₁ (Σ j,Y j)).smul_mem m (Submodule.subset_span ⟨_,rfl⟩)

/-- Disjoint unions of contractible components have zero integral cubical H1;
no finiteness of the component index is used. -/
theorem exact₁_sigma_contractible [∀ j, ContractibleSpace (Y j)]
    (z : N₁ (Σ j,Y j)) (hz : d₁ z = 0) : ∃ b : N₂ (Σ j,Y j), d₂ b = z := by
  refine ⟨-normalizedPrism (sigmaHomotopy (Y:=Y)) z,?_⟩
  rw [map_neg,normalizedPrism_boundary _ hz,push_sigmaCollapse_zero,pushN₁_id,zero_sub,neg_neg]

end EilenbergGanea.CubicalSingular

namespace EilenbergGanea.CubicalSingular
open Set
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem exact₁_on_of_exact (U : Set X)
    (hU : ∀ z : N₁ U, d₁ z = 0 → ∃ b : N₂ U, d₂ b = z)
    {c : N₁ X} (hc : c ∈ L₁ U) (hz : d₁ c = 0) : ∃ b ∈ L₂ U, d₂ b = c := by
  rw [← range_pushN₁_inc] at hc
  obtain ⟨c,rfl⟩ := hc
  have hz' : d₁ c = 0 := by
    apply push₀_injective (inc U) Subtype.val_injective
    simpa only [d₁_push,map_zero] using hz
  obtain ⟨b,hb⟩ := hU c hz'
  refine ⟨pushN₂ (inc U) b,?_,?_⟩
  · rw [← range_pushN₂_inc]; exact ⟨b,rfl⟩
  · rw [d₂_push,hb]

theorem exact₁_homeomorph (e : X ≃ₜ Y)
    (hX : ∀ z : N₁ X, d₁ z = 0 → ∃ b : N₂ X, d₂ b = z)
    (z : N₁ Y) (hz : d₁ z = 0) : ∃ b : N₂ Y, d₂ b = z := by
  obtain ⟨b,hb⟩ := hX (pushN₁ (⟨e.symm,e.symm.continuous⟩ : C(Y,X)) z) (by rw [d₁_push,hz,map_zero])
  refine ⟨pushN₂ (⟨e,e.continuous⟩ : C(X,Y)) b,?_⟩
  rw [d₂_push,hb,← pushN₁_comp]
  have he : (⟨e,e.continuous⟩ : C(X,Y)).comp (⟨e.symm,e.symm.continuous⟩ : C(Y,X)) = ContinuousMap.id Y :=
    ContinuousMap.ext e.apply_symm_apply
  rw [he,pushN₁_id]

def subspaceHomologyMap (U : Set X) : HomologyOne U →ₗ[ℤ] Homology₁ U :=
  homologyMap (inc U) (by intro x _; exact x.property)

theorem subspaceHomologyMap_injective (U : Set X) : Function.Injective (subspaceHomologyMap U) := by
  apply LinearMap.ker_eq_bot.mp
  refine le_antisymm ?_ bot_le
  intro q hq
  obtain ⟨z,rfl⟩ := (boundaries (univ : Set U)).mkQ_surjective q
  change (boundaries U).mkQ (cycleMap (inc U) _ z) = 0 at hq
  obtain ⟨b,hb,hdb⟩ := (Submodule.Quotient.mk_eq_zero (boundaries U)).mp hq
  rw [← range_pushN₂_inc] at hb
  obtain ⟨c,rfl⟩ := hb
  have hc : d₂ c = z.val := by
    apply pushN₁_injective (inc U) Subtype.val_injective
    rw [← d₂_push]
    exact hdb
  change (boundaries (univ : Set U)).mkQ z = 0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact ⟨c,by rw [L₂_univ]; trivial,hc⟩

theorem subspaceHomologyMap_surjective (U : Set X) : Function.Surjective (subspaceHomologyMap U) := by
  intro q
  obtain ⟨z,rfl⟩ := (boundaries U).mkQ_surjective q
  have hz := z.property.1
  rw [← range_pushN₁_inc] at hz
  obtain ⟨c,hc⟩ := hz
  have hdc : d₁ c = 0 := by
    apply push₀_injective (inc U) Subtype.val_injective
    rw [← d₁_push,hc,map_zero]
    exact z.property.2
  let c' : cyclesOn (univ : Set U) := ⟨c,by rw [L₁_univ]; trivial,hdc⟩
  refine ⟨(boundaries (univ : Set U)).mkQ c',?_⟩
  change (boundaries U).mkQ (cycleMap (inc U) _ c') = (boundaries U).mkQ z
  congr 1
  exact Subtype.ext hc

/-- Supported homology is the actual singular homology of the subspace. -/
def subspaceHomologyEquiv (U : Set X) : HomologyOne U ≃ₗ[ℤ] Homology₁ U :=
  LinearEquiv.ofBijective (subspaceHomologyMap U)
    ⟨subspaceHomologyMap_injective U,subspaceHomologyMap_surjective U⟩

end EilenbergGanea.CubicalSingular

namespace EilenbergGanea.CWCollar
open Set Metric Topology CWCover CubicalSingular
variable {X J : Type*} [TopologicalSpace X] {n : ℕ}

def openDiskHomeomorph (n : ℕ) : OpenDisk n ≃ₜ ball (0 : Fin n → ℝ) 1 where
  toFun z := ⟨z.val.val,by simpa only [mem_ball,dist_zero_right] using z.property⟩
  invFun z := ⟨⟨z.val,ball_subset_closedBall z.property⟩,by simpa only [mem_ball,dist_zero_right] using z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

instance openDiskContractible (n : ℕ) : ContractibleSpace (OpenDisk n) := by
  let : ContractibleSpace (ball (0 : Fin n → ℝ) 1) := contractibleSpace_ball (by norm_num)
  exact (openDiskHomeomorph n).contractibleSpace

namespace Attachment
variable (a : Attachment X J n)

theorem inner_exact (z : N₁ a.inner) (hz : d₁ z = 0) : ∃ b : N₂ a.inner, d₂ b = z :=
  exact₁_homeomorph a.innerHomeomorph exact₁_sigma_contractible z hz

theorem inner_supported_exact {z : N₁ X} (hz : z ∈ L₁ a.inner) (hd : d₁ z = 0) :
    ∃ b ∈ L₂ a.inner, d₂ b = z := exact₁_on_of_exact a.inner a.inner_exact hz hd

end Attachment
end EilenbergGanea.CWCollar

namespace EilenbergGanea.CWCollar
open Set CubicalSingular PathTransport
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

@[simp] theorem homologyOneMap_loop (f : C(X,Y)) {x : X} (p : Path x x) :
    homologyOneMap f (loopHomology p) = loopHomology (p.map f.continuous) := by
  change (boundaries univ).mkQ (cycleMap f _ (loopCycle p)) = (boundaries univ).mkQ (loopCycle _)
  congr 1
  apply Subtype.ext
  change pushN₁ f (gen₁ p.toContinuousMap) = gen₁ (p.map f.continuous).toContinuousMap
  rw [pushN₁_gen]
  rfl

namespace Attachment
variable {J : Type*} (a : Attachment X J 2)

def outerCapHomologyEquiv [ContractibleSpace X] :
    HomologyOne (a.outer ∩ a.inner : Set X) ≃ₗ[ℤ] HomologyOne a.outer :=
  (subspaceHomologyEquiv (a.outer ∩ a.inner)).trans
    ((mayerVietoris_equiv a.outer a.inner a.outer_open a.inner_open a.outer_union_inner
      (fun _ hz hd => a.inner_supported_exact hz hd)).trans (subspaceHomologyEquiv a.outer).symm)

end Attachment
end EilenbergGanea.CWCollar



end

end OAI
end

section
-- module Solutions.OAIEG.Cubical_Chains
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set

open Classical
namespace CubicalChains
variable {G A : Type*} [Group G]
abbrev Chains (G A : Type*) := (G × List A) →₀ ℤ

def front (x : A) : Chains G A →ₗ[ℤ] Chains G A :=
  Finsupp.lmapDomain ℤ ℤ (fun p => (p.1,x :: p.2))

def shift (v : A → G) (x : A) : Chains G A →ₗ[ℤ] Chains G A :=
  Finsupp.lmapDomain ℤ ℤ (fun p => (p.1 * v x,p.2))

omit [Group G] in
@[simp] theorem front_single (x : A) (g : G) (w : List A) (n : ℤ) :
    front x (Finsupp.single (g,w) n) = Finsupp.single (g,x::w) n := by
  simp [front]

@[simp] theorem shift_single (v : A → G) (x : A) (g : G) (w : List A) (n : ℤ) :
    shift v x (Finsupp.single (g,w) n) = Finsupp.single (g*v x,w) n := by
  simp [shift]

def boundaryTerm (v : A → G) (g : G) : List A → Chains G A
  | [] => 0
  | x :: w => Finsupp.single (g*v x,w) 1 - Finsupp.single (g,w) 1 -
      front x (boundaryTerm v g w)

def boundary (v : A → G) : Chains G A →ₗ[ℤ] Chains G A :=
  Finsupp.linearCombination ℤ (fun p => boundaryTerm v p.1 p.2)

@[simp] theorem boundary_single (v : A → G) (g : G) (w : List A) (n : ℤ) :
    boundary v (Finsupp.single (g,w) n) = n • boundaryTerm v g w := by
  simp [boundary]

@[simp] theorem boundaryTerm_nil (v : A → G) (g : G) : boundaryTerm v g [] = 0 := rfl
@[simp] theorem boundaryTerm_cons (v : A → G) (g : G) (x : A) (w : List A) :
    boundaryTerm v g (x :: w) = Finsupp.single (g*v x,w) 1 - Finsupp.single (g,w) 1 -
      front x (boundaryTerm v g w) := rfl

theorem boundary_front (v : A → G) (x : A) (c : Chains G A) :
    boundary v (front x c) = shift v x c - c - front x (boundary v c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add,hc,hd]; abel
  | single p n =>
      rcases p with ⟨g,w⟩
      simp only [front_single,boundary_single,boundaryTerm_cons,shift_single,map_smul]
      simp only [smul_sub, Finsupp.smul_single, smul_eq_mul, mul_one]

theorem shift_front (v : A → G) (x y : A) (c : Chains G A) :
    shift v x (front y c) = front y (shift v x c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add,hc,hd]
  | single p n => rcases p with ⟨g,w⟩; simp

theorem boundaryTerm_shift (v : A → G) (x : A) (g : G) (w : List A)
    (hw : ∀ y ∈ w, Commute (v x) (v y)) :
    boundaryTerm v (g * v x) w = shift v x (boundaryTerm v g w) := by
  induction w with
  | nil => simp
  | cons y w ih =>
      rw [boundaryTerm_cons,boundaryTerm_cons,map_sub,map_sub,shift_single,shift_single,
        shift_front,ih (fun z hz => hw z (by simp [hz]))]
      rw [mul_assoc,(hw y (by simp)).eq,← mul_assoc]

theorem boundary_boundaryTerm (v : A → G) (g : G) (w : List A)
    (hw : w.Pairwise (fun x y => Commute (v x) (v y))) :
    boundary v (boundaryTerm v g w) = 0 := by
  induction w generalizing g with
  | nil => simp
  | cons x w ih =>
      obtain ⟨hx,hw⟩ := List.pairwise_cons.mp hw
      simp only [boundaryTerm_cons,map_sub,boundary_single,one_smul,boundary_front]
      rw [ih _ hw,map_zero,boundaryTerm_shift v x g w hx]
      abel


/-- The part of the boundary incident to the top vertex. -/
def upperTerm (g : G) : List A → Chains G A
  | [] => 0
  | x :: w => -Finsupp.single (g,w) 1 - front x (upperTerm g w)

def upper : Chains G A →ₗ[ℤ] Chains G A :=
  Finsupp.linearCombination ℤ (fun p => upperTerm p.1 p.2)

omit [Group G] in
@[simp] theorem upper_single (g : G) (w : List A) (n : ℤ) :
    upper (Finsupp.single (g,w) n) = n • upperTerm g w := by simp [upper]

omit [Group G] in
@[simp] theorem upperTerm_nil (g : G) : upperTerm g ([] : List A) = 0 := rfl

omit [Group G] in
@[simp] theorem upperTerm_cons (g : G) (x : A) (w : List A) :
    upperTerm g (x::w) = -Finsupp.single (g,w) 1 - front x (upperTerm g w) := rfl

def coneTerm (a : G → A) (g : G) (w : List A) : Chains G A :=
  if a g ∈ w then 0 else -Finsupp.single (g,a g::w) 1

def cone (a : G → A) : Chains G A →ₗ[ℤ] Chains G A :=
  Finsupp.linearCombination ℤ (fun p => coneTerm a p.1 p.2)

omit [Group G] in
@[simp] theorem cone_single (a : G → A) (g : G) (w : List A) (n : ℤ) :
    cone a (Finsupp.single (g,w) n) = n • coneTerm a g w := by simp [cone]

omit [Group G] in
 theorem supported_map {I J : Type*} (f : (I →₀ ℤ) →ₗ[ℤ] (J →₀ ℤ))
    (P : Set I) (Q : Set J)
    (h : ∀ i ∈ P, f (Finsupp.single i 1) ∈ Finsupp.supported ℤ ℤ Q)
    {c : I →₀ ℤ} (hc : c ∈ Finsupp.supported ℤ ℤ P) :
    f c ∈ Finsupp.supported ℤ ℤ Q := by
  rw [Finsupp.supported_eq_span_single] at hc
  apply Submodule.span_induction (p := fun c _ => f c ∈ Finsupp.supported ℤ ℤ Q) _ _ _ _ hc
  · rintro _ ⟨i,hi,rfl⟩; exact h i hi
  · simp
  · intro x y _ _ hx hy; simpa using (Finsupp.supported ℤ ℤ Q).add_mem hx hy
  · intro n x _ hx; simpa using (Finsupp.supported ℤ ℤ Q).smul_mem n hx

omit [Group G] in
 theorem upperTerm_supported (g : G) (w : List A) :
    upperTerm g w ∈ Finsupp.supported ℤ ℤ
      {p : G × List A | p.1 = g ∧ p.2.Sublist w ∧ p.2.length + 1 = w.length} := by
  induction w with
  | nil => simp
  | cons x w ih =>
      rw [upperTerm_cons]
      apply Submodule.sub_mem
      · apply Submodule.neg_mem
        exact Finsupp.single_mem_supported ℤ 1 ⟨rfl, List.sublist_cons_self _ _, rfl⟩
      · apply supported_map (front x) _ _ _ ih
        rintro ⟨g',w'⟩ ⟨rfl,hs,hl⟩
        rw [front_single]
        exact Finsupp.single_mem_supported ℤ 1 ⟨rfl,hs.cons_cons x,by simp; omega⟩


/-- A lower face is obtained by deleting one direction and crossing it. -/
def Removed (x : A) (w u : List A) : Prop :=
  ∃ p q, w = p ++ x :: q ∧ u = p ++ q

omit [Group G] in
 theorem Removed.sublist {x : A} {w u : List A} (h : Removed x w u) : u.Sublist w := by
  obtain ⟨p,q,rfl,rfl⟩ := h
  exact (List.sublist_cons_self x q).append_left p

omit [Group G] in
 theorem Removed.length {x : A} {w u : List A} (h : Removed x w u) : u.length + 1 = w.length := by
  obtain ⟨p,q,rfl,rfl⟩ := h
  simp; omega

omit [Group G] in
 theorem Removed.cons {x y : A} {w u : List A} (h : Removed x w u) : Removed x (y::w) (y::u) := by
  obtain ⟨p,q,rfl,rfl⟩ := h
  exact ⟨y::p,q,rfl,rfl⟩

def lowerTerm (v : A → G) (g : G) (w : List A) := boundaryTerm v g w - upperTerm g w

def lower (v : A → G) : Chains G A →ₗ[ℤ] Chains G A := boundary v - upper

@[simp] theorem lower_single (v : A → G) (g : G) (w : List A) (n : ℤ) :
    lower v (Finsupp.single (g,w) n) = n • lowerTerm v g w := by
  simp [lower,lowerTerm,smul_sub]

@[simp] theorem lowerTerm_nil (v : A → G) (g : G) : lowerTerm v g [] = 0 := by simp [lowerTerm]

@[simp] theorem lowerTerm_cons (v : A → G) (g : G) (x : A) (w : List A) :
    lowerTerm v g (x::w) = Finsupp.single (g*v x,w) 1 - front x (lowerTerm v g w) := by
  simp only [lowerTerm,boundaryTerm_cons,upperTerm_cons,map_sub]
  abel

 theorem lowerTerm_supported (v : A → G) (g : G) (w : List A) :
    lowerTerm v g w ∈ Finsupp.supported ℤ ℤ
      {p : G × List A | ∃ x, Removed x w p.2 ∧ p.1 = g * v x} := by
  induction w with
  | nil => simp
  | cons x w ih =>
      rw [lowerTerm_cons]
      apply Submodule.sub_mem
      · exact Finsupp.single_mem_supported ℤ 1 ⟨x,⟨[],w,rfl,rfl⟩,rfl⟩
      · apply supported_map (front x) _ _ _ ih
        rintro ⟨g',w'⟩ ⟨y,hy,rfl⟩
        rw [front_single]
        exact Finsupp.single_mem_supported ℤ 1 ⟨y,hy.cons,rfl⟩

variable [LinearOrder A]

/-- Local combinatorial descending-cube data. All these fields will be supplied
by the actual trace normal form, not by a geometric exactness assumption. -/
structure DescentSystem (v : A → G) where
  length : G → ℕ
  desc : G → Set A
  step : ∀ g x, x ∈ desc g → length (g*v x)+1 = length g
  preserve : ∀ g x y, x ∈ desc g → y ∈ desc g → x ≠ y → y ∈ desc (g*v x)
  commute : ∀ g x y, x ∈ desc g → y ∈ desc g → x ≠ y → Commute (v x) (v y)
  choose : G → A
  choose_mem : ∀ g, 0 < length g → choose g ∈ desc g
  choose_le : ∀ g x, x ∈ desc g → choose g ≤ x

namespace DescentSystem
variable {v : A → G} (D : DescentSystem v)

def Valid (g : G) (w : List A) : Prop := w.Pairwise (· < ·) ∧ ∀ x ∈ w, x ∈ D.desc g

def admissible (k N : ℕ) : Submodule ℤ (Chains G A) :=
  Finsupp.supported ℤ ℤ {p | D.Valid p.1 p.2 ∧ p.2.length = k ∧ D.length p.1 ≤ N}

def homotopyTerm (g : G) (w : List A) : Chains G A :=
  if D.length g = 0 then 0 else coneTerm D.choose g w

def homotopy : Chains G A →ₗ[ℤ] Chains G A :=
  Finsupp.linearCombination ℤ (fun p => D.homotopyTerm p.1 p.2)

@[simp] theorem homotopy_single (g : G) (w : List A) (n : ℤ) :
    D.homotopy (Finsupp.single (g,w) n) = n • D.homotopyTerm g w := by simp [homotopy]

def remainder : Chains G A →ₗ[ℤ] Chains G A :=
  LinearMap.id - (boundary v).comp D.homotopy - D.homotopy.comp (boundary v)

end DescentSystem
end CubicalChains


end

end OAI
end

section
-- module Solutions.OAIEG.RightAngledArtin_CubeDescents
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set

namespace EilenbergGanea
namespace TraceWords
variable {V : Type*} (L : SimpleGraph V)
/-! Right descents and the cubes in the actual Artin Cayley graph. -/

section CubeDescents
open Classical
variable {L}

theorem Equivalent.extract {x : Letter V} {w w' v : Word V}
    (hs : Equivalent L w w') (he : Extract L x w v) :
    ∃ v', Extract L x w' v' ∧ Equivalent L v v' := by
  have hh : Relation.ReflTransGen (Swap L) w w' := by
    rwa [← Relation.EqvGen.eqvGen_eq_reflTransGen]
  clear hs
  induction hh with
  | refl => exact ⟨_,he,.refl _⟩
  | tail _ hs ih =>
      obtain ⟨v',he',hv'⟩ := ih
      obtain ⟨v'',he'',hv''⟩ := he'.swap hs
      exact ⟨_,he'',hv'.trans hv''⟩

theorem Swap.reverse {w v : Word V} (h : Swap L w v) :
    Equivalent L w.reverse v.reverse := by
  induction h with
  | @head x y w h =>
      simpa only [List.reverse_cons,List.append_assoc,List.cons_append,List.nil_append]
        using Equivalent.append_left (Relation.EqvGen.rel _ _ (Swap.head (w := []) h.symm)) w.reverse
  | cons x _ ih =>
      simpa only [List.reverse_cons] using ih.append_right [x]

theorem Equivalent.reverse {w v : Word V} (h : Equivalent L w v) :
    Equivalent L w.reverse v.reverse := by
  induction h with
  | rel _ _ h => exact h.reverse
  | refl => exact .refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

/-- Distinct accessible occurrences commute. In particular two opposite signs
of the same vertex can never both be accessible. -/
theorem Extract.eq_or_independent {x y : Letter V} {w u v : Word V}
    (hx : Extract L x w u) (hy : Extract L y w v) :
    x = y ∨ Independent L x y := by
  induction hx generalizing v with
  | head w =>
      cases hy with
      | head => exact Or.inl rfl
      | cons h _ => exact Or.inr h.symm
  | @cons a w u ha hx ih =>
      cases hy with
      | head => exact Or.inr ha
      | cons _ hy => exact ih hy

variable (L)
def RightExtract (x : Letter V) (w v : Word V) : Prop :=
  Extract L x w.reverse v.reverse

variable {L}
theorem RightExtract.equivalent {x : Letter V} {w v : Word V}
    (h : RightExtract L x w v) : Equivalent L w (v ++ [x]) := by
  simpa only [List.reverse_reverse,List.reverse_cons] using (Extract.equivalent h).reverse

theorem RightExtract.of_equivalent {x : Letter V} {w v : Word V}
    (h : Equivalent L w (v ++ [x])) : ∃ u, RightExtract L x w u ∧ Equivalent L u v := by
  obtain ⟨u,hu,hue⟩ := h.reverse.symm.extract (by
    simpa only [List.reverse_append,List.reverse_singleton,List.singleton_append]
      using (Extract.head (L := L) (x := x) v.reverse))
  exact ⟨u.reverse,by simpa [RightExtract] using hu,by simpa using hue.symm.reverse⟩

theorem RightExtract.length {x : Letter V} {w v : Word V}
    (h : RightExtract L x w v) : v.length + 1 = w.length := by
  simpa [RightExtract] using Extract.length h

theorem RightExtract.eq_or_independent {x y : Letter V} {w u v : Word V}
    (hx : RightExtract L x w u) (hy : RightExtract L y w v) :
    x = y ∨ Independent L x y := Extract.eq_or_independent hx hy


variable (L)
/-- A maximal occurrence of a trace, retaining its sign. -/
def EndsWith (t : Trace L) (x : Letter V) : Prop :=
  ∃ u, t = appendTrace L u (ofWord L [x])

def artinLength (g : ArtinGroup L) : ℕ := traceLength L (artinNormalTrace L g)

def rightDescents (g : ArtinGroup L) : Set (Letter V) :=
  {x | EndsWith L (artinNormalTrace L g) x}

variable {L}
theorem endsWith_ofWord_iff (w : Word V) (x : Letter V) :
    EndsWith L (ofWord L w) x ↔ ∃ v, RightExtract L x w v := by
  constructor
  · rintro ⟨t,ht⟩
    induction t using Quotient.inductionOn with
    | h v =>
        obtain ⟨u,hu,_⟩ := RightExtract.of_equivalent ((ofWord_eq L).mp ht)
        exact ⟨u,hu⟩
  · rintro ⟨v,hv⟩
    exact ⟨ofWord L v,(ofWord_eq L).mpr hv.equivalent⟩

theorem endsWith_append_independent (t : Trace L) {x y : Letter V}
    (hxy : Independent L x y) :
    EndsWith L (appendTrace L t (ofWord L [x])) y ↔ EndsWith L t y := by
  induction t using Quotient.inductionOn with
  | h w =>
      change EndsWith L (ofWord L (w ++ [x])) y ↔ EndsWith L (ofWord L w) y
      rw [endsWith_ofWord_iff,endsWith_ofWord_iff]
      constructor
      · rintro ⟨v,hv⟩
        have hv' : Extract L y (x :: w.reverse) v.reverse := by
          simpa [RightExtract] using hv
        generalize hvv : v.reverse = u at hv'
        cases hv' with
        | head => exact False.elim (independent_self L x hxy)
        | @cons _ _ u _ hu =>
            exact ⟨u.reverse,by simpa [RightExtract] using hu⟩
      · rintro ⟨v,hv⟩
        refine ⟨v ++ [x],?_⟩
        simpa [RightExtract] using Extract.cons hxy.symm hv

variable (L)
theorem artinLength_word {w : Word V} (h : Reduced L (ofWord L w)) :
    artinLength L (wordEval (artinGenerator L) w) = w.length := by
  simp only [artinLength,artinNormalTrace_word,h.normalTrace_eq,traceLength_ofWord]

theorem rightDescents_word {w : Word V} (h : Reduced L (ofWord L w)) (x : Letter V) :
    x ∈ rightDescents L (wordEval (artinGenerator L) w) ↔ ∃ v, RightExtract L x w v := by
  change EndsWith L (artinNormalTrace L _) x ↔ _
  rw [artinNormalTrace_word,h.normalTrace_eq,endsWith_ofWord_iff]

/-- The whole descending link is a clique, not just its pairwise choices. -/
theorem rightDescents_pairwise (g : ArtinGroup L) :
    (rightDescents L g).Pairwise (Independent L) := by
  obtain ⟨w,hw,rfl⟩ := exists_reduced_word L g
  intro x hx y hy hne
  obtain ⟨u,hu⟩ := (rightDescents_word L hw x).mp hx
  obtain ⟨v,hv⟩ := (rightDescents_word L hw y).mp hy
  exact (hu.eq_or_independent hv).resolve_left hne

theorem rightDescents_length (g : ArtinGroup L) (x : Letter V) :
    x ∈ rightDescents L g ↔
      artinLength L (g * letterValue (artinGenerator L) (invLetter x)) + 1 = artinLength L g := by
  constructor
  · obtain ⟨w,hw,rfl⟩ := exists_reduced_word L g
    intro hx
    obtain ⟨v,hv⟩ := (rightDescents_word L hw x).mp hx
    have he := hv.equivalent
    have hvred := (hw.of_equivalent he).of_append_right
    have heval := he.wordEval (fun _ _ h => adjacent_generators_commute L h)
    rw [wordEval_append,wordEval_singleton] at heval
    rw [heval,letterValue_inverse,mul_inv_cancel_right,artinLength_word L hvred]
    rw [← heval,artinLength_word L hw]
    exact hv.length
  · intro hl
    rcases artinNormalTrace_right_step L g (invLetter x) with ht | ht
    · have := congrArg (traceLength L) ht
      rw [traceLength_append_singleton] at this
      change artinLength L _ = artinLength L _ + 1 at this
      omega
    · exact ⟨_,by simpa only [invLetter_invLetter] using ht⟩

/-- Crossing one cube direction does not change the descent status of any
independent direction. This is the no-local-maximum obstruction needed for the
length filtration of the universal cubical complex. -/
theorem descent_independent_step (g : ArtinGroup L) {x y : Letter V}
    (hxy : Independent L x y) :
    y ∈ rightDescents L (g * letterValue (artinGenerator L) x) ↔ y ∈ rightDescents L g := by
  change EndsWith L (artinNormalTrace L _) y ↔ EndsWith L (artinNormalTrace L g) y
  rcases artinNormalTrace_right_step L g x with ht | ht
  · rw [ht,endsWith_append_independent _ hxy]
  · rw [ht,endsWith_append_independent _ (show Independent L (invLetter x) y from hxy)]

theorem artinLength_eq_zero_iff (g : ArtinGroup L) : artinLength L g = 0 ↔ g = 1 := by
  obtain ⟨w,hw,rfl⟩ := exists_reduced_word L g
  rw [artinLength_word L hw]
  constructor
  · intro h
    have : w = [] := by simpa using h
    simp [this]
  · intro h
    have hh := (artin_word_eq_iff L w []).mp (by simpa using h)
    rw [hw.normalTrace_eq] at hh
    have he : ofWord L w = ofWord L [] := hh.trans (by
      apply Reduced.normalTrace_eq
      intro t ht
      have := ht.length
      simp only [traceLength_ofWord,List.length_nil] at this
      omega)
    exact (congrArg (traceLength L) he)

theorem rightDescents_nonempty {g : ArtinGroup L} (hg : g ≠ 1) :
    (rightDescents L g).Nonempty := by
  obtain ⟨w,hw,rfl⟩ := exists_reduced_word L g
  have hwne : w ≠ [] := by intro h; apply hg; simp [h]
  obtain ⟨v,x,rfl⟩ : ∃ (v : Word V) (x : Letter V), w = v ++ [x] := by
    cases he : w.reverse with
    | nil => exact False.elim (hwne (by simpa using congrArg List.reverse he))
    | cons x v => exact ⟨v.reverse,x,by simpa using congrArg List.reverse he⟩
  refine ⟨x,(rightDescents_word L hw x).mpr ⟨v,?_⟩⟩
  simp only [RightExtract,List.reverse_append,List.reverse_singleton,List.singleton_append]
  exact .head _


/-- The exact length increment of one generator, with no chosen normal word. -/
theorem artinLength_step (g : ArtinGroup L) (x : Letter V) :
    (artinLength L (g * letterValue (artinGenerator L) x) : ℤ) =
      artinLength L g + if invLetter x ∈ rightDescents L g then -1 else 1 := by
  by_cases hx : invLetter x ∈ rightDescents L g
  · have hh := (rightDescents_length L g (invLetter x)).mp hx
    simp only [invLetter_invLetter] at hh
    simp only [ite_eq_left hx]
    omega
  · simp only [ite_eq_right hx]
    rcases artinNormalTrace_right_step L g x with ht | ht
    · have hh := congrArg (traceLength L) ht
      rw [traceLength_append_singleton] at hh
      change artinLength L _ = artinLength L _ + 1 at hh
      omega
    · exact False.elim (hx ⟨_,ht⟩)

end CubeDescents
end TraceWords
end EilenbergGanea

end

end OAI
end

section
-- module Solutions.OAIEG.Cubical_ArtinChains
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set

namespace EilenbergGanea.TraceWords.CubeDescents
open CubicalChains
variable {V : Type*} (L : SimpleGraph V) [Fintype V] [Nonempty V] [LinearOrder (Letter V)]

def descentFinset (g : ArtinGroup L) : Finset (Letter V) :=
  Finset.univ.filter (fun x => x ∈ rightDescents L g)

omit [Nonempty V] [LinearOrder (Letter V)] in
@[simp] theorem mem_descentFinset (g : ArtinGroup L) (x : Letter V) :
    x ∈ descentFinset L g ↔ x ∈ rightDescents L g := by simp [descentFinset]

end EilenbergGanea.TraceWords.CubeDescents

namespace CubicalChains
variable {G A : Type*} [Group G]
namespace Reorientation
variable {V : Type*} (f : V → G)

abbrev Signed (V : Type*) := V × Bool

def step (x : Signed V) : G := if x.2 then (f x.1)⁻¹ else f x.1

def origin (g : G) : List (Signed V) → G
  | [] => g
  | x::w => if x.2 then origin (g * (f x.1)⁻¹) w else origin g w

def sign : List (Signed V) → ℤ
  | [] => 1
  | x::w => (if x.2 then -1 else 1) * sign w

@[simp] theorem origin_nil (g : G) : origin f g [] = g := rfl
@[simp] theorem sign_nil : sign ([] : List (Signed V)) = 1 := rfl

@[simp] theorem sign_sq (w : List (Signed V)) : sign w * sign w = 1 := by
  induction w with
  | nil => rfl
  | cons x w ih => cases hx : x.2 <;> simp [sign,hx,ih]

theorem origin_shift (g k : G) (w : List (Signed V))
    (hw : ∀ x ∈ w, Commute k (f x.1)) :
    origin f (g*k) w = origin f g w * k := by
  induction w generalizing g with
  | nil => rfl
  | cons x w ih =>
      have hx := (hw x (by simp)).inv_right
      have hh : ∀ y ∈ w, Commute k (f y.1) := fun y hy => hw y (by simp [hy])
      simp only [origin]
      split
      · rw [mul_assoc,hx.eq,← mul_assoc,ih _ hh]
      · exact ih _ hh

def normalTerm (g : G) (w : List (Signed V)) : Chains G V :=
  sign w • Finsupp.single (origin f g w,w.map Prod.fst) 1

def normalize : Chains G (Signed V) →ₗ[ℤ] Chains G V :=
  Finsupp.linearCombination ℤ (fun p => normalTerm f p.1 p.2)

@[simp] theorem normalize_single (g : G) (w : List (Signed V)) (n : ℤ) :
    normalize f (Finsupp.single (g,w) n) = n • normalTerm f g w := by simp [normalize]

theorem normalize_front (x : Signed V) (c : Chains G (Signed V)) :
    normalize f (front x c) = if x.2 then
      -front x.1 (normalize f (shift (step f) x c)) else front x.1 (normalize f c) := by
  induction c using Finsupp.induction_linear with
  | zero => cases x.2 <;> simp
  | add c d hc hd =>
      simp only [map_add,hc,hd]
      cases x.2
      all_goals simp only [Bool.false_eq_true,↓reduceIte]
      all_goals abel
  | single p n =>
      rcases p with ⟨g,w⟩
      cases hx : x.2 <;> simp only [front_single,normalize_single,shift_single,normalTerm,
        origin,sign,step,hx,Bool.false_eq_true,↓reduceIte,List.map_cons,map_smul,
        neg_mul,smul_neg,neg_smul,one_mul]

/-- Reversing selected coordinates changes the signs and origin but not the
actual integral cubical boundary. No asphericity input is used here. -/
theorem normalize_boundaryTerm (g : G) (w : List (Signed V))
    (hw : w.Pairwise (fun x y => Commute (f x.1) (f y.1))) :
    normalize f (boundaryTerm (step f) g w) = boundary f (normalTerm f g w) := by
  induction w generalizing g with
  | nil => simp [normalTerm]
  | cons x w ih =>
      obtain ⟨hx,hw⟩ := List.pairwise_cons.mp hw
      have hi : ∀ y ∈ w, Commute (step f x) (step f y) := by
        intro y hy
        have hh := hx y hy
        cases hx' : x.2 <;> cases hy' : y.2 <;> simp only [step,hx',hy',Bool.false_eq_true,↓reduceIte]
        · exact hh
        · exact hh.inv_right
        · exact hh.inv_left
        · exact hh.inv_left.inv_right
      cases hxb : x.2
      · simp only [boundaryTerm_cons,map_sub,normalize_single,one_smul,normalize_front,hxb,
          Bool.false_eq_true,↓reduceIte,ih _ hw,normalTerm,sign,one_mul,origin,List.map_cons,
          map_smul,boundary_single,boundaryTerm_cons]
        have ho := origin_shift f g (f x.1) w hx
        simp only [step,hxb,Bool.false_eq_true,↓reduceIte] at ho ⊢
        rw [ho]
        simp only [smul_sub,Finsupp.smul_single,smul_eq_mul,mul_one]
      · simp only [boundaryTerm_cons,map_sub,normalize_single,one_smul,normalize_front,hxb,
          ↓reduceIte]
        rw [← boundaryTerm_shift (step f) x g w hi,ih _ hw]
        simp only [normalTerm,sign,hxb,↓reduceIte,neg_mul,one_mul,origin,List.map_cons,
          map_smul,boundary_single,boundaryTerm_cons,step]
        have ho : origin f (g * (f x.1)⁻¹) w * f x.1 = origin f g w := by
          rw [origin_shift f g (f x.1)⁻¹ w (fun y hy => (hx y hy).inv_left)]
          group
        rw [ho]
        simp only [smul_sub,neg_smul,Finsupp.smul_single,smul_eq_mul,mul_one]
        abel

end Reorientation
end CubicalChains

namespace EilenbergGanea.TraceWords.CubeDescents
open CubicalChains CubicalChains.Reorientation
variable {V : Type*} (L : SimpleGraph V)

theorem reverse_step_descent (g : ArtinGroup L) (x : Letter V) :
    x ∈ rightDescents L (g * letterValue (artinGenerator L) x) ↔
      invLetter x ∉ rightDescents L g := by
  rw [rightDescents_length]
  simp only [letterValue_inverse,mul_inv_cancel_right]
  have hs := artinLength_step L g x
  by_cases h : invLetter x ∈ rightDescents L g
  · simp only [h,↓reduceIte,not_true_eq_false,iff_false] at hs ⊢
    omega
  · simp only [h,↓reduceIte,not_false_eq_true,iff_true] at hs ⊢
    omega

/-- Orient a positive cube toward its unique word-length maximum. -/
def orient (g : ArtinGroup L) : List V → ArtinGroup L × Word V
  | [] => (g,[])
  | q::w => if (q,false) ∈ rightDescents L g then
      let t := orient g w
      (t.1,(q,false)::t.2)
    else
      let t := orient (g * artinGenerator L q) w
      (t.1,(q,true)::t.2)

@[simp] theorem orient_nil (g : ArtinGroup L) : orient L g [] = (g,[]) := rfl

@[simp] theorem orient_map (g : ArtinGroup L) (w : List V) :
    (orient L g w).2.map Prod.fst = w := by
  induction w generalizing g with
  | nil => rfl
  | cons q w ih => simp only [orient]; split <;> simp [ih]

theorem orient_descent_invariant (g : ArtinGroup L) (w : List V) (x : Letter V)
    (hw : ∀ q ∈ w, L.Adj q x.1) :
    x ∈ rightDescents L (orient L g w).1 ↔ x ∈ rightDescents L g := by
  induction w generalizing g with
  | nil => rfl
  | cons q w ih =>
      have hh : ∀ r ∈ w, L.Adj r x.1 := fun r hr => hw r (by simp [hr])
      simp only [orient]
      split
      · exact ih _ hh
      · rw [ih _ hh]
        exact descent_independent_step L g (x := (q,true)) (hw q (by simp))

theorem orient_descents (g : ArtinGroup L) (w : List V) (hw : w.Pairwise L.Adj) :
    ∀ x ∈ (orient L g w).2, x ∈ rightDescents L (orient L g w).1 := by
  induction w generalizing g with
  | nil => simp
  | cons q w ih =>
      obtain ⟨hq,hw⟩ := List.pairwise_cons.mp hw
      simp only [orient]
      split
      · rename_i hd
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact (orient_descent_invariant L g w (q,false)
            (fun r hr => (hq r hr).symm)).mpr hd
        · exact ih g hw x hx
      · rename_i hd
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · apply (orient_descent_invariant L (g * artinGenerator L q) w (q,true)
            (fun r hr => (hq r hr).symm)).mpr
          exact (reverse_step_descent L g (q,true)).mpr hd
        · exact ih _ hw x hx

theorem origin_orient (g : ArtinGroup L) (w : List V) (hw : w.Pairwise L.Adj) :
    origin (artinGenerator L) (orient L g w).1 (orient L g w).2 = g := by
  induction w generalizing g with
  | nil => rfl
  | cons q w ih =>
      obtain ⟨hq,hw⟩ := List.pairwise_cons.mp hw
      simp only [orient]
      split
      · exact ih g hw
      · simp only [origin,↓reduceIte]
        rw [origin_shift]
        · rw [ih _ hw,mul_inv_cancel_right]
        · intro x hx
          apply Commute.inv_left
          apply adjacent_generators_commute
          have hm : x.1 ∈ w := by
            rw [← orient_map L (g * artinGenerator L q) w]
            exact List.mem_map.mpr ⟨x,hx,rfl⟩
          exact hq x.1 hm

end EilenbergGanea.TraceWords.CubeDescents

namespace EilenbergGanea.TraceWords.CubeDescents
open CubicalChains CubicalChains.Reorientation
variable {V : Type*} (L : SimpleGraph V) [Fintype V] [Nonempty V] [LinearOrder V]

def denormalTerm (g : ArtinGroup L) (w : List V) : Chains (ArtinGroup L) (Letter V) :=
  sign (orient L g w).2 • Finsupp.single (orient L g w) 1

def denormalize : Chains (ArtinGroup L) V →ₗ[ℤ] Chains (ArtinGroup L) (Letter V) :=
  Finsupp.linearCombination ℤ (fun p => denormalTerm L p.1 p.2)

omit [Fintype V] [Nonempty V] [LinearOrder V] in
@[simp] theorem denormalize_single (g : ArtinGroup L) (w : List V) (n : ℤ) :
    denormalize L (Finsupp.single (g,w) n) = n • denormalTerm L g w := by
  simp [denormalize]

end EilenbergGanea.TraceWords.CubeDescents


end

end OAI
end

section
-- module Solutions.OAIEG.Cubical_Descending
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Topology

open Classical Set Topology
namespace EilenbergGanea.DescendingCube
variable {G A : Type*} [Group G]

/-- Finite descending directions with literal word-length decrease. These
combinatorial fields will be supplied by the checked Artin trace normal form. -/
structure Data (f : A → G) where
  length : G → ℕ
  desc : G → Finset A
  decrease : ∀ g a, a ∈ desc g → length (g * f a) + 1 = length g
  preserve : ∀ g a b, a ∈ desc g → b ∈ desc g → a ≠ b → b ∈ desc (g * f a)
  commute : ∀ g a b, a ∈ desc g → b ∈ desc g → a ≠ b → Commute (f a) (f b)
  nonempty : ∀ g, 0 < length g → (desc g).Nonempty
  zero : ∀ g, length g = 0 ↔ g = 1

namespace Data
variable {f : A → G} (D : Data f)
def product (g : G) (s : Finset A) (hs : s ⊆ D.desc g) : G :=
  s.noncommProd f (fun a ha b hb hne => D.commute g a b (hs ha) (hs hb) hne)

@[simp] theorem product_empty (g : G) : D.product g ∅ (by simp) = 1 :=
  Finset.noncommProd_empty _ _

theorem product_insert (g : G) (s : Finset A) (a : A) (ha : a ∉ s)
    (hs : insert a s ⊆ D.desc g) :
    D.product g (insert a s) hs = f a * D.product g s (fun _ hb => hs (Finset.mem_insert_of_mem hb)) := by
  exact Finset.noncommProd_insert_of_notMem _ _ _ _ ha

/-- Simultaneous finite descent and preservation of all untouched directions. -/
theorem product_descent (g : G) (s : Finset A) (hs : s ⊆ D.desc g) :
    D.length (g * D.product g s hs) + s.card = D.length g ∧
    ∀ a ∈ D.desc g, a ∉ s → a ∈ D.desc (g * D.product g s hs) := by
  induction s using Finset.induction_on generalizing g with
  | empty => simp
  | @insert a s ha ih =>
      have hga : a ∈ D.desc g := hs (Finset.mem_insert_self _ _)
      have hs' : s ⊆ D.desc (g * f a) := by
        intro b hb
        exact D.preserve g a b hga (hs (Finset.mem_insert_of_mem hb))
          (fun he => ha (he ▸ hb))
      have hh := ih (g * f a) hs'
      have he : D.product (g * f a) s hs' =
          D.product g s (fun _ hb => hs (Finset.mem_insert_of_mem hb)) := rfl
      rw [he] at hh
      rw [product_insert _ _ _ _ ha,← mul_assoc]
      constructor
      · have hd := D.decrease g a hga
        rw [Finset.card_insert_of_notMem ha]
        omega
      · intro b hb hbs
        exact hh.2 b (D.preserve g a b hga hb (by
          intro he; exact hbs (he ▸ Finset.mem_insert_self a s)))
          (fun hb' => hbs (Finset.mem_insert_of_mem hb'))

structure Cell where
  top : G
  directions : Finset A
  subset : directions ⊆ D.desc top

@[ext] structure Point where
  top : G
  coord : A → ℝ
  nonneg : ∀ a, 0 ≤ coord a
  lt_one : ∀ a, coord a < 1
  support : ∀ a, coord a ≠ 0 → a ∈ D.desc top

abbrev Coordinates (c : D.Cell) := c.directions → Set.Icc (0 : ℝ) 1

def ones (c : D.Cell) (x : D.Coordinates c) : Finset A :=
  c.directions.attach.filter (fun a => (x a : ℝ) = 1) |>.image Subtype.val

@[simp] theorem mem_ones (c : D.Cell) (x : D.Coordinates c) (a : A) :
    a ∈ D.ones c x ↔ ∃ h : a ∈ c.directions, (x ⟨a,h⟩ : ℝ) = 1 := by simp [ones]

theorem ones_subset (c : D.Cell) (x : D.Coordinates c) : D.ones c x ⊆ c.directions := by
  intro a ha
  exact ((D.mem_ones c x a).mp ha).1

def normalizedCoord (c : D.Cell) (x : D.Coordinates c) (a : A) : ℝ :=
  if h : a ∈ c.directions then if (x ⟨a,h⟩ : ℝ) = 1 then 0 else x ⟨a,h⟩ else 0

/-- Crossing a far face removes a descent and strictly lowers the top vertex. -/
def characteristic (c : D.Cell) (x : D.Coordinates c) : D.Point where
  top := c.top * D.product c.top (D.ones c x) ((D.ones_subset c x).trans c.subset)
  coord := D.normalizedCoord c x
  nonneg a := by
    by_cases h : a ∈ c.directions
    · simp only [normalizedCoord,dite_eq_left h]
      split_ifs
      · exact le_rfl
      · exact (x ⟨a,h⟩).property.1
    · simp [normalizedCoord,h]
  lt_one a := by
    by_cases h : a ∈ c.directions
    · simp only [normalizedCoord,dite_eq_left h]
      split_ifs with he
      · norm_num
      · exact lt_of_le_of_ne (x ⟨a,h⟩).property.2 he
    · simp [normalizedCoord,h]
  support a ha := by
    have h : a ∈ c.directions := by
      by_contra hn
      exact ha (by simp [normalizedCoord,hn])
    have hne : (x ⟨a,h⟩ : ℝ) ≠ 1 := by
      intro he
      exact ha (by simp [normalizedCoord,h,he])
    exact (D.product_descent c.top (D.ones c x) _).2 a (c.subset h) (by
      intro hm
      obtain ⟨_,he⟩ := (D.mem_ones c x a).mp hm
      exact hne he)

variable [Fintype A]

def active (p : D.Point) : Finset A := Finset.univ.filter (fun a => p.coord a ≠ 0)

@[simp] theorem mem_active (p : D.Point) (a : A) : a ∈ D.active p ↔ p.coord a ≠ 0 := by
  simp [active]

def pointCell (p : D.Point) : D.Cell :=
  ⟨p.top,D.active p,fun a ha => p.support a ((D.mem_active p a).mp ha)⟩

def pointCoordinates (p : D.Point) : D.Coordinates (D.pointCell p) :=
  fun a => ⟨p.coord a,p.nonneg a,(p.lt_one a).le⟩

@[simp] theorem ones_pointCoordinates (p : D.Point) :
    D.ones (D.pointCell p) (D.pointCoordinates p) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  obtain ⟨h,hh⟩ := (D.mem_ones _ _ _).mp ha
  exact (p.lt_one a).ne hh

@[simp] theorem characteristic_point (p : D.Point) :
    D.characteristic (D.pointCell p) (D.pointCoordinates p) = p := by
  apply Point.ext
  · change p.top * D.product p.top (D.ones (D.pointCell p) (D.pointCoordinates p)) _ = p.top
    simp only [product,ones_pointCoordinates,Finset.noncommProd_empty,mul_one]
  · funext a
    by_cases h : p.coord a = 0
    · simp [characteristic,normalizedCoord,pointCell,h]
    · simp [characteristic,normalizedCoord,pointCell,h,pointCoordinates,(p.lt_one a).ne]

abbrev CubeSum := (c : D.Cell) × D.Coordinates c

def evaluation : D.CubeSum → D.Point := fun z => D.characteristic z.1 z.2

theorem evaluation_surjective : Function.Surjective D.evaluation := by
  intro p
  exact ⟨⟨D.pointCell p,D.pointCoordinates p⟩,D.characteristic_point p⟩

instance pointTopology : TopologicalSpace D.Point :=
  TopologicalSpace.coinduced D.evaluation inferInstance

theorem evaluation_quotient : IsQuotientMap D.evaluation := ⟨⟨rfl⟩,D.evaluation_surjective⟩

theorem characteristic_continuous (c : D.Cell) : Continuous (D.characteristic c) :=
  D.evaluation_quotient.continuous.comp (continuous_sigmaMk (i := c))

omit [Fintype A] in
theorem characteristic_length (c : D.Cell) (x : D.Coordinates c) :
    D.length (D.characteristic c x).top + (D.ones c x).card = D.length c.top :=
  (D.product_descent c.top (D.ones c x) _).1

end Data
end EilenbergGanea.DescendingCube

namespace EilenbergGanea.DescendingCube.Data

section
variable {G A : Type*} [Group G] {f : A → G} (D : Data f)
def fullCell (g : G) : D.Cell := ⟨g,D.desc g,fun _ => id⟩

def fullCoord (c : D.Cell) (x : D.Coordinates c) (a : A) : ℝ :=
  if h : a ∈ c.directions then x ⟨a,h⟩ else 0

@[simp] theorem fullCoord_mem (c : D.Cell) (x : D.Coordinates c) (a : c.directions) :
    D.fullCoord c x a = (x a : ℝ) := by simp [fullCoord,a.property]

theorem fullCoord_nonneg (c : D.Cell) (x : D.Coordinates c) (a : A) :
    0 ≤ D.fullCoord c x a := by
  unfold fullCoord
  split
  · exact (x _).property.1
  · exact le_rfl

theorem fullCoord_le_one (c : D.Cell) (x : D.Coordinates c) (a : A) :
    D.fullCoord c x a ≤ 1 := by
  unfold fullCoord
  split
  · exact (x _).property.2
  · norm_num

def extendCoordinates (c : D.Cell) (x : D.Coordinates c) : D.Coordinates (D.fullCell c.top) :=
  fun a => ⟨D.fullCoord c x a,D.fullCoord_nonneg c x a,D.fullCoord_le_one c x a⟩

@[simp] theorem ones_extend (c : D.Cell) (x : D.Coordinates c) :
    D.ones (D.fullCell c.top) (D.extendCoordinates c x) = D.ones c x := by
  ext a
  simp only [mem_ones,extendCoordinates]
  constructor
  · rintro ⟨ha,he⟩
    by_cases h : a ∈ c.directions
    · exact ⟨h,by simpa only [fullCoord,dite_eq_left h] using he⟩
    · simp [fullCoord,h] at he
  · rintro ⟨ha,he⟩
    exact ⟨c.subset ha,by simpa only [fullCoord,dite_eq_left ha] using he⟩

@[simp] theorem characteristic_extend (c : D.Cell) (x : D.Coordinates c) :
    D.characteristic (D.fullCell c.top) (D.extendCoordinates c x) = D.characteristic c x := by
  apply Point.ext
  · change c.top * D.product c.top (D.ones (D.fullCell c.top) (D.extendCoordinates c x)) _ =
      c.top * D.product c.top (D.ones c x) _
    simp only [product,ones_extend]
  · funext a
    change D.normalizedCoord (D.fullCell c.top) (D.extendCoordinates c x) a = D.normalizedCoord c x a
    by_cases hc : a ∈ c.directions
    · simp [normalizedCoord,fullCell,extendCoordinates,fullCoord,hc,c.subset hc]
    · by_cases ha : a ∈ D.desc c.top <;>
        simp [normalizedCoord,fullCell,extendCoordinates,fullCoord,hc,ha]

variable [Fintype A] [Nonempty A]

def radius (u : A → ℝ) : ℝ := Finset.univ.sup' Finset.univ_nonempty u

theorem le_radius (u : A → ℝ) (a : A) : u a ≤ radius u :=
  Finset.le_sup' u (Finset.mem_univ a)

theorem radius_le {u : A → ℝ} {r : ℝ} (h : ∀ a, u a ≤ r) : radius u ≤ r :=
  Finset.sup'_le _ _ (fun a _ => h a)

open scoped unitInterval

def deformCoordinates (c : D.Cell) (x : D.Coordinates c) (t : unitInterval) :
    D.Coordinates (D.fullCell c.top) := fun a =>
  ⟨D.fullCoord c x a + (t : ℝ) * (1 - radius (D.fullCoord c x)),
    add_nonneg (D.fullCoord_nonneg c x a)
      (mul_nonneg t.property.1 (sub_nonneg.mpr (radius_le (D.fullCoord_le_one c x)))),by
        have ha := le_radius (D.fullCoord c x) a
        have hr := radius_le (D.fullCoord_le_one c x)
        have ht := mul_le_of_le_one_left (sub_nonneg.mpr hr) t.property.2
        linarith⟩

@[simp] theorem deformCoordinates_zero (c : D.Cell) (x : D.Coordinates c) :
    D.deformCoordinates c x 0 = D.extendCoordinates c x := by
  funext a
  apply Subtype.ext
  simp [deformCoordinates,extendCoordinates]

/-- The time-one radial deformation reaches a far face whenever the top is
not the identity. It is fixed on every far face from the outset. -/
theorem deformCoordinates_one_ones (c : D.Cell) (x : D.Coordinates c)
    (hc : 0 < D.length c.top) :
    (D.ones (D.fullCell c.top) (D.deformCoordinates c x 1)).Nonempty := by
  obtain ⟨a,_,ha⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (D.fullCoord c x)
  by_cases hm : a ∈ D.desc c.top
  · refine ⟨a,(D.mem_ones _ _ _).mpr ⟨hm,?_⟩⟩
    change D.fullCoord c x a + (1 : ℝ) * (1 - radius (D.fullCoord c x)) = 1
    change D.fullCoord c x a + 1 * (1 - Finset.univ.sup' _ (D.fullCoord c x)) = 1
    rw [ha]
    ring
  · have hn : a ∉ c.directions := fun h => hm (c.subset h)
    have hr : radius (D.fullCoord c x) = 0 := by
      rw [fullCoord,dite_eq_right hn] at ha
      exact ha
    obtain ⟨b,hb⟩ := D.nonempty c.top hc
    have hb0 : D.fullCoord c x b = 0 :=
      le_antisymm (by simpa only [hr] using le_radius (D.fullCoord c x) b)
        (D.fullCoord_nonneg c x b)
    refine ⟨b,(D.mem_ones _ _ _).mpr ⟨hb,?_⟩⟩
    change D.fullCoord c x b + (1 : ℝ) * (1 - radius (D.fullCoord c x)) = 1
    rw [hb0,hr]
    norm_num

def cellDeform (c : D.Cell) (x : D.Coordinates c) (t : unitInterval) : D.Point :=
  D.characteristic (D.fullCell c.top) (D.deformCoordinates c x t)

@[simp] theorem cellDeform_zero (c : D.Cell) (x : D.Coordinates c) :
    D.cellDeform c x 0 = D.characteristic c x := by
  simp only [cellDeform,deformCoordinates_zero,characteristic_extend]

theorem cellDeform_one_length (c : D.Cell) (x : D.Coordinates c)
    (hc : 0 < D.length c.top) : D.length (D.cellDeform c x 1).top < D.length c.top := by
  have h := D.characteristic_length (D.fullCell c.top) (D.deformCoordinates c x 1)
  have hp := Finset.card_pos.mpr (D.deformCoordinates_one_ones c x hc)
  change D.length (D.cellDeform c x 1).top + _ = D.length c.top at h
  omega

end

section
variable {G A : Type*} [Group G] {f : A → G} (D : Data f)
def farFaceCell (c : D.Cell) (a : c.directions) : D.Cell where
  top := c.top * f a
  directions := c.directions.erase a
  subset := by
    intro b hb
    obtain ⟨hne,hb⟩ := Finset.mem_erase.mp hb
    exact D.preserve c.top a b (c.subset a.property) (c.subset hb) hne.symm

def farFaceCoordinates (c : D.Cell) (a : c.directions) (x : D.Coordinates c) :
    D.Coordinates (D.farFaceCell c a) := fun b => x ⟨b,Finset.mem_of_mem_erase b.property⟩

@[simp] theorem ones_farFace (c : D.Cell) (a : c.directions) (x : D.Coordinates c) :
    D.ones (D.farFaceCell c a) (D.farFaceCoordinates c a x) = (D.ones c x).erase a := by
  ext b
  constructor
  · intro hb
    obtain ⟨hb, he⟩ := (D.mem_ones (D.farFaceCell c a) (D.farFaceCoordinates c a x) b).mp hb
    obtain ⟨hne, hb⟩ := Finset.mem_erase.mp hb
    exact Finset.mem_erase.mpr ⟨hne, (D.mem_ones c x b).mpr ⟨hb, he⟩⟩
  · intro hb
    obtain ⟨hne, hb⟩ := Finset.mem_erase.mp hb
    obtain ⟨hb, he⟩ := (D.mem_ones c x b).mp hb
    exact (D.mem_ones (D.farFaceCell c a) (D.farFaceCoordinates c a x) b).mpr
      ⟨Finset.mem_erase.mpr ⟨hne, hb⟩, he⟩

variable [Fintype A]

variable [Nonempty A]
open scoped unitInterval

def pointDeform (p : D.Point) (t : unitInterval) : D.Point :=
  D.cellDeform (D.pointCell p) (D.pointCoordinates p) t

@[simp] theorem pointDeform_zero (p : D.Point) : D.pointDeform p 0 = p := by
  simp only [pointDeform,cellDeform_zero,characteristic_point]

theorem pointDeform_one_length (p : D.Point) (hp : 0 < D.length p.top) :
    D.length (D.pointDeform p 1).top < D.length p.top :=
  D.cellDeform_one_length (D.pointCell p) (D.pointCoordinates p) hp

end

variable {G A : Type*} [Group G] {f : A → G} (D : Data f)
variable [Fintype A] [Nonempty A]
open scoped unitInterval NNReal
def clip (r : ℝ) : unitInterval := Set.projIcc 0 1 zero_le_one r

/-- Flow to word-length height r, stopping part-way across its unique top shell. -/
def flow (r : ℝ≥0) (p : D.Point) : D.Point :=
  if _h : (D.length p.top : ℝ) ≤ r then p
  else if (D.length p.top : ℝ) - 1 ≤ r then
    D.pointDeform p (clip ((D.length p.top : ℝ) - r))
  else flow r (D.pointDeform p 1)
termination_by D.length p.top
decreasing_by
  apply D.pointDeform_one_length
  have hr := r.property
  by_contra hn
  have hz : D.length p.top = 0 := by omega
  simp only [hz,Nat.cast_zero] at _h
  exact _h hr

def contraction (t : unitInterval) (p : D.Point) : D.Point :=
  if (t : ℝ) = 0 then p else D.flow (Real.toNNReal ((1 - (t : ℝ)) / t)) p

@[simp] theorem contraction_zero (p : D.Point) : D.contraction 0 p = p := by
  simp [contraction]

end EilenbergGanea.DescendingCube.Data

end

end OAI
end

section
-- module Solutions.OAIEG.Cubical_Realization
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Topology

namespace EilenbergGanea
open Classical TraceWords
variable {V : Type*} [Fintype V] (L : SimpleGraph V)

/-- Actual right-angled Artin descending cubes supplied by the proved signed
trace normal form. None of the contractibility hypotheses are postulated. -/
def artinDescendingData : DescendingCube.Data
    (fun x : Letter V => letterValue (artinGenerator L) (invLetter x)) where
  length := artinLength L
  desc g := (rightDescents L g).toFinset
  decrease g a ha := (rightDescents_length L g a).mp (by simpa using ha)
  preserve g a b ha hb hab := by
    have ha' : a ∈ rightDescents L g := by simpa using ha
    have hb' : b ∈ rightDescents L g := by simpa using hb
    have hi := rightDescents_pairwise L g ha' hb' hab
    have hh := (descent_independent_step L g (x := invLetter a) (y := b)
      (show Independent L (invLetter a) b from hi)).mpr hb'
    simpa using hh
  commute g a b ha hb hab := by
    have ha' : a ∈ rightDescents L g := by simpa using ha
    have hb' : b ∈ rightDescents L g := by simpa using hb
    have hi : Independent L a b := rightDescents_pairwise L g ha' hb' hab
    exact letterValue_commute (L := L) (fun _ _ h => adjacent_generators_commute L h)
      (show Independent L (invLetter a) (invLetter b) from hi)
  nonempty g hg := by
    have hne : g ≠ 1 := by
      intro he
      have hz := (artinLength_eq_zero_iff L g).mpr he
      omega
    obtain ⟨a,ha⟩ := rightDescents_nonempty L hne
    exact ⟨a,by simpa using ha⟩
  zero := artinLength_eq_zero_iff L

abbrev ArtinDescendingRealization := (artinDescendingData L).Point

end EilenbergGanea

open Classical Set Topology
namespace EilenbergGanea.CubeRealization
variable {G V : Type*} [Group G] [Fintype V]
variable (L : SimpleGraph V) (f : V → G)
variable (comm : ∀ v w, L.Adj v w → Commute (f v) (f w))

/-- Positive closed cubes of the actual Cayley cubical model. -/
structure Cell where
  base : G
  directions : Finset V
  clique : (directions : Set V).Pairwise L.Adj

/-- Points are represented by the unique open cube containing them. -/
@[ext] structure Point (f : V → G)
    (comm : ∀ v w, L.Adj v w → Commute (f v) (f w)) where
  base : G
  coord : V → ℝ
  nonneg : ∀ v, 0 ≤ coord v
  lt_one : ∀ v, coord v < 1
  clique : {v | coord v ≠ 0}.Pairwise L.Adj

variable {L f comm}

def active (p : Point (G := G) L f comm) : Finset V := Finset.univ.filter (fun v => p.coord v ≠ 0)

@[simp] theorem mem_active (p : Point (G := G) L f comm) (v : V) :
    v ∈ active p ↔ p.coord v ≠ 0 := by simp [active]

def pointCell (p : Point (G := G) L f comm) : Cell (G := G) L :=
  ⟨p.base, active p, fun _ hv _ hw hne => p.clique
    ((mem_active _ _).mp hv) ((mem_active _ _).mp hw) hne⟩

variable (f comm)

def product (s : Finset V) (hs : (s : Set V).Pairwise L.Adj) : G :=
  s.noncommProd f (fun v hv w hw hne => comm v w (hs hv hw hne))

omit [Fintype V] in
@[simp] theorem product_empty : product f comm ∅ (by simp) = 1 := by
  exact Finset.noncommProd_empty _ _

abbrev Coordinates (c : Cell (G := G) L) := c.directions → Set.Icc (0 : ℝ) 1

def ones (c : Cell (G := G) L) (x : Coordinates c) : Finset V :=
  c.directions.attach.filter (fun v => (x v : ℝ) = 1) |>.image Subtype.val

omit [Group G] [Fintype V] in
@[simp] theorem mem_ones (c : Cell (G := G) L) (x : Coordinates c) (v : V) :
    v ∈ ones c x ↔ ∃ h : v ∈ c.directions, (x ⟨v,h⟩ : ℝ) = 1 := by
  simp [ones]

omit [Group G] [Fintype V] in
theorem ones_subset (c : Cell (G := G) L) (x : Coordinates c) :
    ones c x ⊆ c.directions := by
  intro v hv
  exact ((mem_ones c x v).mp hv).1

def normalizedCoord (c : Cell (G := G) L) (x : Coordinates c) (v : V) : ℝ :=
  if h : v ∈ c.directions then if (x ⟨v,h⟩ : ℝ) = 1 then 0 else x ⟨v,h⟩ else 0

omit [Group G] [Fintype V] in
@[simp] theorem normalizedCoord_mem (c : Cell (G := G) L) (x : Coordinates c)
    (v : c.directions) :
    normalizedCoord c x v = if (x v : ℝ) = 1 then (0 : ℝ) else (x v : ℝ) := by
  simp [normalizedCoord,v.property]

omit [Group G] [Fintype V] in
@[simp] theorem normalizedCoord_notMem (c : Cell (G := G) L) (x : Coordinates c)
    {v : V} (hv : v ∉ c.directions) : normalizedCoord c x v = 0 := by
  simp [normalizedCoord,hv]

/-- Boundary coordinates equal to1 translate the initial vertex; coordinates0
or1 are dropped from the unique open face. -/
def characteristic (c : Cell (G := G) L) (x : Coordinates c) : Point (G := G) L f comm where
  base := c.base * product f comm (ones c x) (c.clique.mono (ones_subset c x))
  coord := normalizedCoord c x
  nonneg v := by
    by_cases h : v ∈ c.directions
    · simp only [normalizedCoord,dite_eq_left h]
      split_ifs
      · exact le_rfl
      · exact (x ⟨v,h⟩).property.1
    · simp [normalizedCoord,h]
  lt_one v := by
    by_cases h : v ∈ c.directions
    · simp only [normalizedCoord,dite_eq_left h]
      split_ifs with he
      · norm_num
      · exact lt_of_le_of_ne (x ⟨v,h⟩).property.2 he
    · simp [normalizedCoord,h]
  clique := by
    intro v hv w hw hne
    have hv' : v ∈ c.directions := by
      by_contra h
      exact hv (normalizedCoord_notMem c x h)
    have hw' : w ∈ c.directions := by
      by_contra h
      exact hw (normalizedCoord_notMem c x h)
    exact c.clique hv' hw' hne

omit [Fintype V] in
@[simp] theorem characteristic_coord (c : Cell (G := G) L) (x : Coordinates c) (v : V) :
    (characteristic f comm c x).coord v = normalizedCoord c x v := rfl

variable {f comm}

/-- Canonical coordinates in the unique open cell. -/
def pointCoordinates (p : Point (G := G) L f comm) : Coordinates (pointCell p) :=
  fun v => ⟨p.coord v, p.nonneg v, (p.lt_one v).le⟩

@[simp] theorem pointCoordinates_coe (p : Point (G := G) L f comm) (v : (pointCell p).directions) :
    (pointCoordinates p v : ℝ) = p.coord v := rfl

@[simp] theorem ones_pointCoordinates (p : Point (G := G) L f comm) :
    ones (pointCell p) (pointCoordinates p) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  obtain ⟨h,hh⟩ := (mem_ones _ _ _).mp hv
  exact (p.lt_one v).ne hh

variable (f comm)

@[simp] theorem characteristic_point (p : Point (G := G) L f comm) :
    characteristic f comm (pointCell p) (pointCoordinates p) = p := by
  apply Point.ext
  · change p.base * product f comm (ones (pointCell p) (pointCoordinates p)) _ = p.base
    simp only [product,ones_pointCoordinates,Finset.noncommProd_empty,mul_one]
  · funext v
    by_cases h : p.coord v = 0
    · simp [characteristic,normalizedCoord,pointCell,h]
    · simp [characteristic,normalizedCoord,pointCell,h,pointCoordinates,(p.lt_one v).ne]

abbrev CubeSum := (c : Cell (G := G) L) × Coordinates c

def evaluation : CubeSum (G := G) (L := L) → Point (G := G) L f comm :=
  fun z => characteristic f comm z.1 z.2

 theorem evaluation_surjective : Function.Surjective (evaluation f comm (L := L)) := by
  intro p
  exact ⟨⟨pointCell p,pointCoordinates p⟩, characteristic_point f comm p⟩

/-- The weak topology of the actual closed cubes, without asserting any missing
geometric/homological properties of this construction. -/
instance pointTopology : TopologicalSpace (Point (G := G) L f comm) :=
  TopologicalSpace.coinduced (evaluation f comm) inferInstance

 theorem evaluation_quotient : IsQuotientMap (evaluation f comm (L := L)) :=
  ⟨⟨rfl⟩,evaluation_surjective f comm⟩

 theorem characteristic_continuous (c : Cell (G := G) L) :
    Continuous (characteristic f comm c) :=
  (evaluation_quotient f comm).continuous.comp (continuous_sigmaMk (i := c))

end EilenbergGanea.CubeRealization

open Classical Set Topology
namespace EilenbergGanea.CubeInterpolation
variable {G V : Type*} [Group G]

def translation : G →* Module.End ℝ (G → ℝ) where
  toFun g :=
    { toFun := fun φ a => φ (a*g)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  map_one' := by ext φ a; simp
  map_mul' g h := by ext φ a; simp [mul_assoc]

@[simp] theorem translation_apply (g a : G) (φ : G → ℝ) :
    translation g φ a = φ (a*g) := rfl

def blend (g : G) (x : ℝ) : Module.End ℝ (G → ℝ) :=
  (1-x) • 1 + x • translation g

@[simp] theorem blend_apply (g a : G) (x : ℝ) (φ : G → ℝ) :
    blend g x φ a = (1-x)*φ a + x*φ (a*g) := rfl

@[simp] theorem blend_zero (g : G) : blend g 0 = 1 := by simp [blend]
@[simp] theorem blend_one (g : G) : blend g 1 = translation g := by simp [blend]

theorem blend_commute {g h : G} (hgh : Commute g h) (x y : ℝ) :
    Commute (blend g x) (blend h y) := by
  unfold blend
  exact ((Commute.one_left _).smul_left _).add_left
    (((Commute.one_right _).smul_right _).add_right
      (((hgh.map translation).smul_left _).smul_right _))

variable (f : V → G)

def operator (s : Finset V) (hs : (s : Set V).Pairwise (fun v w => Commute (f v) (f w)))
    (x : V → ℝ) : Module.End ℝ (G → ℝ) :=
  s.noncommProd (fun v => blend (f v) (x v))
    (fun _ hv _ hw hne => blend_commute (hs hv hw hne) _ _)

@[simp] theorem operator_empty (x : V → ℝ) : operator f ∅ (by simp) x = 1 := rfl

@[simp] theorem operator_insert (s : Finset V) (v : V) (hv : v ∉ s)
    (hs : (↑(insert v s) : Set V).Pairwise (fun v w => Commute (f v) (f w))) (x : V → ℝ) :
    operator f (insert v s) hs x = blend (f v) (x v) *
      operator f s (hs.mono (by simp)) x := by
  exact Finset.noncommProd_insert_of_notMem s v _ _ hv

/-- Zero coordinates may be deleted without changing the interpolation. -/
theorem operator_subset (s t : Finset V) (ht : (t : Set V).Pairwise (fun v w => Commute (f v) (f w)))
    (hst : s ⊆ t) (x : V → ℝ) (hx : ∀ v ∈ t, v ∉ s → x v = 0) :
    operator f t ht x = operator f s (ht.mono hst) x := by
  induction t using Finset.induction_on generalizing s with
  | empty => have : s = ∅ := Finset.subset_empty.mp hst; subst s; rfl
  | @insert v t hv ih =>
    have ht' : (t : Set V).Pairwise (fun v w => Commute (f v) (f w)) :=
      ht.mono (by simp)
    by_cases hvs : v ∈ s
    · have hsub : s.erase v ⊆ t := by
        intro w hw
        exact Finset.mem_of_mem_insert_of_ne (hst (Finset.mem_erase.mp hw).2)
          (Finset.mem_erase.mp hw).1
      have hx' : ∀ w ∈ t, w ∉ s.erase v → x w = 0 := by
        intro w hw hn
        apply hx w (by simp [hw])
        intro hws
        exact hn (Finset.mem_erase.mpr ⟨ne_of_mem_of_not_mem hw hv,hws⟩)
      have he := ih (s.erase v) ht' hsub hx'
      have hs' : (↑(insert v (s.erase v)) : Set V).Pairwise
          (fun v w => Commute (f v) (f w)) := by
        simpa only [Finset.insert_erase hvs] using ht.mono hst
      have hr : operator f s (ht.mono hst) x = blend (f v) (x v) *
          operator f (s.erase v) (ht'.mono hsub) x := by
        simpa only [Finset.insert_erase hvs] using
          operator_insert f (s.erase v) v (Finset.notMem_erase _ _) hs' x
      rw [operator_insert f t v hv,hr,he]
    · have hsub : s ⊆ t := by
        intro w hw
        exact Finset.mem_of_mem_insert_of_ne (hst hw)
          (by intro he; exact hvs (he ▸ hw))
      rw [operator_insert f t v hv,hx v (by simp) hvs,blend_zero,one_mul]
      exact ih s ht' hsub (fun w hw hn => hx w (by simp [hw]) hn)

variable {f}
theorem commute_ite_one (g h : G) (hgh : Commute g h) (P Q : Prop) :
    Commute (if P then g else 1) (if Q then h else 1) := by
  split_ifs <;> first | exact hgh | exact Commute.one_left _ | exact Commute.one_right _
theorem noncommProd_ite (s : Finset V) (hs : (s : Set V).Pairwise
    (fun v w => Commute (f v) (f w))) (P : V → Prop) :
    s.noncommProd (fun v => if P v then f v else 1)
      (fun _ hv _ hw he => commute_ite_one _ _ (hs hv hw he) _ _) =
    (s.filter P).noncommProd f (hs.mono (Finset.filter_subset _ _)) := by
  induction s using Finset.induction_on with
  | empty => rfl
  | @insert v s hv ih =>
    erw [Finset.noncommProd_insert_of_notMem _ _ _ _ hv]
    by_cases hp : P v
    · simp only [Finset.filter_insert, ite_eq_left hp]
      erw [Finset.noncommProd_insert_of_notMem _ _ _ _
        (fun h => hv (Finset.mem_of_mem_filter _ h)), ih (hs.mono (by simp))]
    · simp only [Finset.filter_insert, ite_eq_right hp, one_mul]
      exact ih (hs.mono (by simp))

def normalize (x : V → ℝ) (v : V) : ℝ := if x v = 1 then 0 else x v

theorem translation_blend_commute {a b : G} (h : Commute a b) (x : ℝ) :
    Commute (translation a) (blend b x) :=
  ((Commute.one_right _).smul_right _).add_right ((h.map translation).smul_right _)

variable (f)
theorem operator_normalize (s : Finset V) (hs : (s : Set V).Pairwise
    (fun v w => Commute (f v) (f w))) (x : V → ℝ) :
    operator f s hs x =
      translation ((s.filter (fun v => x v = 1)).noncommProd f
        (hs.mono (Finset.filter_subset _ _))) * operator f s hs (normalize x) := by
  let a : V → G := fun v => if x v = 1 then f v else 1
  have ha : (s : Set V).Pairwise (fun v w => Commute (a v) (a w)) :=
    fun _ hv _ hw he => commute_ite_one _ _ (hs hv hw he) _ _
  have ht : (s : Set V).Pairwise (fun v w => Commute (translation (a v)) (translation (a w))) :=
    fun _ hv _ hw he => (ha hv hw he).map translation
  have hb : (s : Set V).Pairwise (fun v w =>
      Commute (blend (f v) (normalize x v)) (blend (f w) (normalize x w))) :=
    fun _ hv _ hw he => blend_commute (hs hv hw he) _ _
  have hbt : (s : Set V).Pairwise (fun v w =>
      Commute (blend (f v) (normalize x v)) (translation (a w))) := by
    intro v hv w hw he
    dsimp [a]
    split_ifs
    · exact (translation_blend_commute (hs hw hv he.symm) _).symm
    · simp only [map_one]; exact Commute.one_right _
  have hfactor : operator f s hs x =
      s.noncommProd ((fun v => translation (a v)) * (fun v => blend (f v) (normalize x v)))
        (Finset.noncommProd_mul_distrib_aux ht hb hbt) := by
    apply Finset.noncommProd_congr rfl
    intro v _
    dsimp [a,normalize]
    split_ifs with hv
    · simp [hv]
    · simp
  rw [hfactor,Finset.noncommProd_mul_distrib _ _ ht hb hbt,
    ← Finset.map_noncommProd s a ha translation]
  congr 1
  congr 1
  exact noncommProd_ite s hs (fun v => x v = 1)

/-- Nonnegative vertex data interpolate nonnegatively throughout every cube. -/
theorem operator_nonneg (s : Finset V) (hs) (x : V → ℝ)
    (hx : ∀ v ∈ s, x v ∈ Set.Icc (0 : ℝ) 1)
    (φ : G → ℝ) (hφ : ∀ a, 0 ≤ φ a) (a : G) : 0 ≤ operator f s hs x φ a := by
  induction s using Finset.induction_on generalizing a with
  | empty => exact hφ a
  | @insert v s hv ih =>
    rw [operator_insert f s v hv,Module.End.mul_apply,blend_apply]
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr (hx v (by simp)).2)
      (ih _ (fun w hw => hx w (by simp [hw])) a))
      (mul_nonneg (hx v (by simp)).1 (ih _ (fun w hw => hx w (by simp [hw])) (a*f v)))

/-- The initial vertex has strictly positive weight in its own open cube. -/
theorem operator_pos (s : Finset V) (hs) (x : V → ℝ)
    (hx : ∀ v ∈ s, x v ∈ Set.Ico (0 : ℝ) 1)
    (φ : G → ℝ) (hφ : ∀ a, 0 ≤ φ a) (a : G) (ha : 0 < φ a) :
    0 < operator f s hs x φ a := by
  induction s using Finset.induction_on generalizing a with
  | empty => exact ha
  | @insert v s hv ih =>
    rw [operator_insert f s v hv,Module.End.mul_apply,blend_apply]
    exact add_pos_of_pos_of_nonneg
      (mul_pos (sub_pos.mpr (hx v (by simp)).2)
        (ih _ (fun w hw => hx w (by simp [hw])) a ha))
      (mul_nonneg (hx v (by simp)).1
        (operator_nonneg f s _ x (fun w hw => ⟨(hx w (by simp [hw])).1,
          (hx w (by simp [hw])).2.le⟩) φ hφ (a*f v)))

/-- No interpolation value detects a vertex below its initial height. At the
initial height it detects only the initial vertex itself. -/
theorem operator_vanish (h : G →* Multiplicative ℤ) (hf : ∀ v, (h (f v)).toAdd = 1)
    (s : Finset V) (hs) (x : V → ℝ) (φ : G → ℝ) (a : G)
    (ha : φ a = 0) (hφ : ∀ b, (h a).toAdd < (h b).toAdd → φ b = 0) :
    operator f s hs x φ a = 0 := by
  induction s using Finset.induction_on generalizing a with
  | empty => exact ha
  | @insert v s hv ih =>
    rw [operator_insert f s v hv,Module.End.mul_apply,blend_apply,ih _ a ha hφ]
    have hstep : (h a).toAdd < (h (a * f v)).toAdd := by
      simp only [map_mul,toAdd_mul,hf]
      omega
    rw [ih _ (a*f v) (hφ _ hstep) (fun b hb => hφ b (hstep.trans hb))]
    ring

/-- Interpolation of a group homomorphism is the ordinary affine coordinate. -/
theorem operator_linear (h : G →* Multiplicative ℝ) (s : Finset V) (hs)
    (x : V → ℝ) (a : G) :
    operator f s hs x (fun a => (h a).toAdd) a =
      (h a).toAdd + ∑ v ∈ s, x v * (h (f v)).toAdd := by
  induction s using Finset.induction_on generalizing a with
  | empty => simp
  | @insert v s hv ih =>
    rw [operator_insert f s v hv,Module.End.mul_apply,blend_apply,
      ih _ a,ih _ (a*f v),Finset.sum_insert hv]
    simp only [map_mul,toAdd_mul]
    ring

end EilenbergGanea.CubeInterpolation

namespace EilenbergGanea.CubeRealization

section
open CubeInterpolation
variable {G V : Type*} [Group G] [Fintype V]
variable (L : SimpleGraph V) (f : V → G)
variable (comm : ∀ v w, L.Adj v w → Commute (f v) (f w))

include comm in
omit [Fintype V] in
theorem cellComm (c : Cell (G := G) L) : (c.directions : Set V).Pairwise
    (fun v w => Commute (f v) (f w)) :=
  fun _ hv _ hw he => comm _ _ (c.clique hv hw he)

variable {L}

def fullCoord (c : Cell (G := G) L) (x : Coordinates c) (v : V) : ℝ :=
  if h : v ∈ c.directions then x ⟨v,h⟩ else 0

omit [Group G] [Fintype V] in
@[simp] theorem fullCoord_mem (c : Cell (G := G) L) (x : Coordinates c) (v : c.directions) :
    fullCoord c x v = (x v : ℝ) := by simp [fullCoord,v.property]

omit [Group G] [Fintype V] in
@[simp] theorem fullCoord_notMem (c : Cell (G := G) L) (x : Coordinates c) {v : V}
    (hv : v ∉ c.directions) : fullCoord c x v = 0 := by simp [fullCoord,hv]

omit [Group G] [Fintype V] in
theorem ones_eq_filter (c : Cell (G := G) L) (x : Coordinates c) :
    ones c x = c.directions.filter (fun v => fullCoord c x v = 1) := by
  ext v
  simp only [mem_ones,Finset.mem_filter]
  constructor
  · rintro ⟨hv,hx⟩
    exact ⟨hv,by simpa only [fullCoord,dite_eq_left hv] using hx⟩
  · rintro ⟨hv,hx⟩
    exact ⟨hv,by simpa only [fullCoord,dite_eq_left hv] using hx⟩

omit [Group G] [Fintype V] in
theorem normalize_fullCoord (c : Cell (G := G) L) (x : Coordinates c) :
    CubeInterpolation.normalize (fullCoord c x) = normalizedCoord c x := by
  funext v
  by_cases hv : v ∈ c.directions
  · simp only [CubeInterpolation.normalize,fullCoord,normalizedCoord,dite_eq_left hv]
  · simp [CubeInterpolation.normalize,fullCoord,normalizedCoord,hv]

variable (L)

def interpolation (p : Point (G := G) L f comm) (φ : G → ℝ) : ℝ :=
  operator f (active p) (cellComm L f comm (pointCell p)) p.coord φ p.base

theorem active_characteristic_subset (c : Cell (G := G) L) (x : Coordinates c) :
    active (characteristic f comm c x) ⊆ c.directions := by
  intro v hv
  by_contra h
  exact ((mem_active _ _).mp hv) (normalizedCoord_notMem c x h)

/-- Literal face compatibility of multilinear vertex interpolation. -/
theorem interpolation_characteristic (c : Cell (G := G) L) (x : Coordinates c) (φ : G → ℝ) :
    interpolation L f comm (characteristic f comm c x) φ =
      operator f c.directions (cellComm L f comm c) (fullCoord c x) φ c.base := by
  have hsub := active_characteristic_subset L f comm c x
  have he := operator_subset f (active (characteristic f comm c x)) c.directions
    (cellComm L f comm c) hsub (normalizedCoord c x) (by
      intro v _ hn
      exact not_not.mp (by simpa only [mem_active,characteristic_coord] using hn))
  have hn := operator_normalize f c.directions (cellComm L f comm c) (fullCoord c x)
  simp only [normalize_fullCoord,← ones_eq_filter] at hn
  have hh := congrArg (fun T : Module.End ℝ (G → ℝ) => T φ c.base) hn
  rw [Module.End.mul_apply,translation_apply,he] at hh
  exact hh.symm

variable (h : G →* Multiplicative ℤ) (hf : ∀ v, (h (f v)).toAdd = 1)

theorem interpolation_vertex_pos (p : Point (G := G) L f comm) :
    0 < interpolation L f comm p (fun a => if a = p.base then 1 else 0) := by
  apply operator_pos
  · intro v _; exact ⟨p.nonneg v,p.lt_one v⟩
  · intro a; split_ifs <;> norm_num
  · simp

include hf in
theorem interpolation_vertex_zero (p : Point (G := G) L f comm) (b : G)
    (hb : (h b).toAdd ≤ (h p.base).toAdd) (hne : b ≠ p.base) :
    interpolation L f comm p (fun a => if a = b then 1 else 0) = 0 := by
  apply operator_vanish f h hf
  · simp [hne.symm]
  · intro a ha
    have hab : a ≠ b := by intro he; subst a; omega
    simp [hab]

include h hf in
theorem interpolation_base_eq (p q : Point (G := G) L f comm)
    (he : ∀ φ, interpolation L f comm p φ = interpolation L f comm q φ) :
    p.base = q.base := by
  have height_le (p q : Point (G := G) L f comm)
      (he : ∀ φ, interpolation L f comm p φ = interpolation L f comm q φ) :
      (h p.base).toAdd ≤ (h q.base).toAdd := by
    by_contra hn
    have hlt : (h q.base).toAdd < (h p.base).toAdd := lt_of_not_ge hn
    have hne : q.base ≠ p.base := by intro eq; rw [eq] at hlt; exact lt_irrefl _ hlt
    have hz := interpolation_vertex_zero L f comm h hf p q.base hlt.le hne
    have hp := interpolation_vertex_pos L f comm q
    rw [← he,hz] at hp
    exact lt_irrefl _ hp
  have h₁ := height_le p q he
  by_contra hne
  have hz := interpolation_vertex_zero L f comm h hf q p.base h₁ hne
  have hp := interpolation_vertex_pos L f comm p
  rw [he,hz] at hp
  exact lt_irrefl _ hp

variable (exponent : V → G →* Multiplicative ℝ)
variable (hexponent : ∀ v w, (exponent v (f w)).toAdd = if v = w then 1 else 0)

include hexponent in
theorem interpolation_exponent (p : Point (G := G) L f comm) (v : V) :
    interpolation L f comm p (fun a => (exponent v a).toAdd) =
      (exponent v p.base).toAdd + p.coord v := by
  unfold interpolation
  erw [operator_linear]
  congr 1
  simp only [hexponent,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq]
  by_cases hv : p.coord v = 0
  · simp [hv]
  · simp [mem_active,hv]

include h hf exponent hexponent in
/-- Interpolation distances separate actual points, not merely vertices. -/
theorem interpolation_injective : Function.Injective
    (fun p : Point (G := G) L f comm => fun φ : G → ℝ => interpolation L f comm p φ) := by
  intro p q he
  have he' : ∀ φ, interpolation L f comm p φ = interpolation L f comm q φ :=
    fun φ => congrFun he φ
  have hb := interpolation_base_eq L f comm h hf p q he'
  apply Point.ext hb
  funext v
  have hv := he' (fun a => (exponent v a).toAdd)
  rw [interpolation_exponent L f comm exponent hexponent,
    interpolation_exponent L f comm exponent hexponent,hb] at hv
  exact add_left_cancel hv

end

section
open Metric
variable {G V : Type*} [Group G] [Fintype V]
variable {L : SimpleGraph V} (f : V → G)
variable (comm : ∀ v w, L.Adj v w → Commute (f v) (f w))

omit [Group G] [Fintype V] in
@[ext] theorem Cell.ext {c d : Cell (G := G) L} (hb : c.base = d.base)
    (hd : c.directions = d.directions) : c = d := by
  cases c; cases d; simp_all

abbrev DimCell (n : ℕ) := {c : Cell (G := G) L // c.directions.card = n}

variable {f comm}
def coordEquiv {n : ℕ} (c : DimCell (G := G) (L := L) n) : c.val.directions ≃ Fin n :=
  Finset.equivFinOfCardEq c.property

def chartCoordinates {n : ℕ} (c : DimCell (G := G) (L := L) n) (t : Fin n → ℝ) :
    Coordinates c.val := fun v => projIcc 0 1 (by norm_num) ((t (coordEquiv c v) + 1) / 2)

def cubeCoordinatesInv {n : ℕ} (c : DimCell (G := G) (L := L) n) (x : Coordinates c.val) :
    Fin n → ℝ := fun i => 2 * (x ((coordEquiv c).symm i) : ℝ) - 1

omit [Group G] [Fintype V] in
theorem cubeCoordinatesInv_mem_disk {n : ℕ} (c : DimCell (G := G) (L := L) n)
    (x : Coordinates c.val) : cubeCoordinatesInv c x ∈ closedBall 0 1 := by
  rw [mem_closedBall_zero_iff,pi_norm_le_iff_of_nonneg (by norm_num)]
  intro i
  rw [Real.norm_eq_abs,abs_le]
  have hx := (x ((coordEquiv c).symm i)).property
  dsimp [cubeCoordinatesInv]
  constructor <;> linarith [hx.1,hx.2]

omit [Group G] [Fintype V] in
theorem chartCoordinates_cubeCoordinatesInv {n : ℕ} (c : DimCell (G := G) (L := L) n)
    (x : Coordinates c.val) : chartCoordinates c (cubeCoordinatesInv c x) = x := by
  funext v
  simp only [chartCoordinates,cubeCoordinatesInv,Equiv.symm_apply_apply]
  have ha : (2 * (x v : ℝ) - 1 + 1) / 2 = (x v : ℝ) := by ring
  rw [ha,projIcc_val]

omit [Group G] [Fintype V] in
theorem chartCoordinates_disk {n : ℕ} (c : DimCell (G := G) (L := L) n)
    {t : Fin n → ℝ} (ht : t ∈ closedBall 0 1) (v : c.val.directions) :
    (chartCoordinates c t v : ℝ) = (t (coordEquiv c v) + 1) / 2 := by
  rw [mem_closedBall_zero_iff,pi_norm_le_iff_of_nonneg (by norm_num)] at ht
  have hv := (abs_le.mp (show |t (coordEquiv c v)| ≤ 1 from ht _))
  unfold chartCoordinates
  rw [projIcc_of_mem (by norm_num) (show (t (coordEquiv c v) + 1) / 2 ∈ Icc (0 : ℝ) 1 by
    constructor <;> linarith [hv.1,hv.2])]

omit [Group G] [Fintype V] in
theorem chartCoordinates_open {n : ℕ} (c : DimCell (G := G) (L := L) n)
    {t : Fin n → ℝ} (ht : t ∈ ball 0 1) (v : c.val.directions) :
    (chartCoordinates c t v : ℝ) ∈ Ioo (0 : ℝ) 1 := by
  rw [chartCoordinates_disk c (ball_subset_closedBall ht)]
  rw [mem_ball_zero_iff,pi_norm_lt_iff (by norm_num)] at ht
  have hv := abs_lt.mp (show |t (coordEquiv c v)| < 1 from ht _)
  constructor <;> linarith [hv.1,hv.2]

omit [Group G] [Fintype V] in
theorem cubeCoordinatesInv_open {n : ℕ} (c : DimCell (G := G) (L := L) n)
    (x : Coordinates c.val) (hx : ∀ v, (x v : ℝ) ∈ Ioo (0 : ℝ) 1) :
    cubeCoordinatesInv c x ∈ ball 0 1 := by
  rw [mem_ball_zero_iff,pi_norm_lt_iff (by norm_num)]
  intro i
  rw [Real.norm_eq_abs,abs_lt]
  dsimp [cubeCoordinatesInv]
  constructor <;> linarith [(hx ((coordEquiv c).symm i)).1,(hx ((coordEquiv c).symm i)).2]

variable (f comm)
theorem characteristic_open_cell (c : Cell (G := G) L) (x : Coordinates c)
    (hx : ∀ v, (x v : ℝ) ∈ Ioo (0 : ℝ) 1) :
    pointCell (characteristic f comm c x) = c := by
  have ho : ones c x = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    obtain ⟨h,hh⟩ := (mem_ones c x v).mp hv
    exact (hx ⟨v,h⟩).2.ne hh
  apply Cell.ext
  · change c.base * product f comm (ones c x) _ = c.base
    simp only [product,ho,Finset.noncommProd_empty,mul_one]
  · ext v
    simp only [pointCell,mem_active,characteristic_coord]
    constructor
    · intro hv
      by_contra hh
      exact hv (normalizedCoord_notMem c x hh)
    · intro hv
      simp only [normalizedCoord,dite_eq_left hv,ite_eq_right (hx ⟨v,hv⟩).2.ne]
      exact (hx ⟨v,hv⟩).1.ne'

/-- Real inverse coordinates of an open cube, without any assumed chart. -/
def chartInverse {n : ℕ} (c : DimCell (G := G) (L := L) n)
    (p : Point (G := G) L f comm) : Fin n → ℝ :=
  fun i => 2 * p.coord ((coordEquiv c).symm i) - 1

omit [Fintype V] in
theorem chart_left_inv {n : ℕ} (c : DimCell (G := G) (L := L) n)
    {t : Fin n → ℝ} (ht : t ∈ ball 0 1) :
    chartInverse f comm c (characteristic f comm c.val (chartCoordinates c t)) = t := by
  funext i
  have he := (chartCoordinates_open c ht ((coordEquiv c).symm i)).2.ne
  simp only [chartInverse, characteristic_coord, normalizedCoord_mem]
  rw [ite_eq_right he,chartCoordinates_disk c (ball_subset_closedBall ht),Equiv.apply_symm_apply]
  ring

theorem chart_right_inv {n : ℕ} (c : DimCell (G := G) (L := L) n)
    (p : Point (G := G) L f comm) (hp : pointCell p = c.val) :
    characteristic f comm c.val (chartCoordinates c (chartInverse f comm c p)) = p := by
  obtain ⟨c,hc⟩ := c
  dsimp at hp
  subst c
  have he : chartInverse f comm ⟨pointCell p,hc⟩ p =
      cubeCoordinatesInv ⟨pointCell p,hc⟩ (pointCoordinates p) := rfl
  rw [he,chartCoordinates_cubeCoordinatesInv,characteristic_point]

theorem chartInverse_mem_source {n : ℕ} (c : DimCell (G := G) (L := L) n)
    (p : Point (G := G) L f comm) (hp : pointCell p = c.val) :
    chartInverse f comm c p ∈ ball 0 1 := by
  obtain ⟨c,hc⟩ := c
  dsimp at hp
  subst c
  apply cubeCoordinatesInv_open ⟨pointCell p,hc⟩ (pointCoordinates p)
  intro v
  exact ⟨lt_of_le_of_ne (p.nonneg v) (by
    exact ((mem_active p v).mp v.property).symm),p.lt_one v⟩

/-- The actual positive-cube open chart. -/
def chart {n : ℕ} (c : DimCell (G := G) (L := L) n) :
    PartialEquiv (Fin n → ℝ) (Point (G := G) L f comm) where
  toFun t := characteristic f comm c.val (chartCoordinates c t)
  invFun := chartInverse f comm c
  source := ball 0 1
  target := {p | pointCell p = c.val}
  map_source' := fun _ ht => characteristic_open_cell f comm _ _ (chartCoordinates_open c ht)
  map_target' := chartInverse_mem_source f comm c
  left_inv' := fun _ ht => chart_left_inv f comm c ht
  right_inv' := chart_right_inv f comm c

end

open Metric
variable {G V : Type*} [Group G] [Fintype V]
variable {L : SimpleGraph V} (f : V → G)
variable (comm : ∀ v w, L.Adj v w → Commute (f v) (f w))

@[simp] theorem chart_image_disk {n : ℕ} (c : DimCell (G := G) (L := L) n) :
    chart f comm c '' closedBall 0 1 = Set.range (characteristic f comm c.val) := by
  ext p
  constructor
  · rintro ⟨t,_,rfl⟩
    exact ⟨chartCoordinates c t,rfl⟩
  · rintro ⟨x,rfl⟩
    exact ⟨cubeCoordinatesInv c x,cubeCoordinatesInv_mem_disk c x,
      congrArg (characteristic f comm c.val) (chartCoordinates_cubeCoordinatesInv c x)⟩

@[simp] theorem chart_image_ball {n : ℕ} (c : DimCell (G := G) (L := L) n) :
    chart f comm c '' ball 0 1 = {p | pointCell p = c.val} :=
  (chart f comm c).image_source_eq_target

end EilenbergGanea.CubeRealization

namespace EilenbergGanea.CubeRealization

variable {G V : Type*} [Group G] [Fintype V]
variable {L : SimpleGraph V} (f : V → G)
variable (comm : ∀ v w, L.Adj v w → Commute (f v) (f w))

/-- Deck translations on the literal positive-cube realization. -/
instance pointMulAction : MulAction G (Point (G := G) L f comm) where
  smul g p := {p with base := g * p.base}
  one_smul p := by apply Point.ext (one_mul p.base); rfl
  mul_smul g h p := by apply Point.ext (mul_assoc g h p.base); rfl

omit [Fintype V] in
@[simp] theorem smul_base (g : G) (p : Point (G := G) L f comm) :
    (g • p).base = g * p.base := rfl

omit [Fintype V] in
@[simp] theorem smul_coord (g : G) (p : Point (G := G) L f comm) :
    (g • p).coord = p.coord := rfl

def translateCell (g : G) (c : Cell (G := G) L) : Cell (G := G) L :=
  {c with base := g * c.base}

omit [Fintype V] in
@[simp] theorem smul_characteristic (g : G) (c : Cell (G := G) L) (x : Coordinates c) :
    g • characteristic f comm c x = characteristic f comm (translateCell g c) x := by
  apply Point.ext (mul_assoc _ _ _).symm
  rfl

end EilenbergGanea.CubeRealization

end

end OAI
end

section
-- module Solutions.OAIEG.CubicalCover
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Topology
open scoped Quaternion

namespace EilenbergGanea.DescendingCube.Data
open CubeInterpolation
variable {G A : Type*} [Group G] {f : A → G} (D : Data f)
variable [Fintype A]

omit [Fintype A] in
theorem cellComm (c : D.Cell) : (c.directions : Set A).Pairwise
    (fun a b => Commute (f a) (f b)) :=
  fun _ ha _ hb he => D.commute c.top _ _ (c.subset ha) (c.subset hb) he

omit [Fintype A] in
theorem ones_eq_filter (c : D.Cell) (x : D.Coordinates c) :
    D.ones c x = c.directions.filter (fun a => D.fullCoord c x a = 1) := by
  ext a
  simp only [mem_ones,Finset.mem_filter]
  constructor
  · rintro ⟨ha,hx⟩
    exact ⟨ha,by simpa only [fullCoord,dite_eq_left ha] using hx⟩
  · rintro ⟨ha,hx⟩
    exact ⟨ha,by simpa only [fullCoord,dite_eq_left ha] using hx⟩

omit [Fintype A] in
theorem normalize_fullCoord (c : D.Cell) (x : D.Coordinates c) :
    CubeInterpolation.normalize (D.fullCoord c x) = D.normalizedCoord c x := by
  funext a
  by_cases ha : a ∈ c.directions
  · simp only [CubeInterpolation.normalize,fullCoord,normalizedCoord,dite_eq_left ha]
  · simp [CubeInterpolation.normalize,fullCoord,normalizedCoord,ha]

def interpolation (p : D.Point) (φ : G → ℝ) : ℝ :=
  operator f (D.active p) (D.cellComm (D.pointCell p)) p.coord φ p.top

theorem active_characteristic_subset (c : D.Cell) (x : D.Coordinates c) :
    D.active (D.characteristic c x) ⊆ c.directions := by
  intro a ha
  by_contra h
  apply ((D.mem_active _ _).mp ha)
  change D.normalizedCoord c x a = 0
  simp [normalizedCoord,h]

theorem interpolation_characteristic (c : D.Cell) (x : D.Coordinates c) (φ : G → ℝ) :
    D.interpolation (D.characteristic c x) φ =
      operator f c.directions (D.cellComm c) (D.fullCoord c x) φ c.top := by
  have hsub := D.active_characteristic_subset c x
  have he := operator_subset f (D.active (D.characteristic c x)) c.directions
    (D.cellComm c) hsub (D.normalizedCoord c x) (by
      intro a _ hn
      exact not_not.mp (by simpa only [mem_active,characteristic] using hn))
  have hn := operator_normalize f c.directions (D.cellComm c) (D.fullCoord c x)
  simp only [normalize_fullCoord,← ones_eq_filter] at hn
  have hh := congrArg (fun T : Module.End ℝ (G → ℝ) => T φ c.top) hn
  rw [Module.End.mul_apply,translation_apply,he] at hh
  exact hh.symm

theorem interpolation_vertex_pos (p : D.Point) :
    0 < D.interpolation p (fun a => if a = p.top then 1 else 0) := by
  apply operator_pos
  · intro a _; exact ⟨p.nonneg a,p.lt_one a⟩
  · intro a; split_ifs <;> norm_num
  · simp

omit [Fintype A] in
theorem descending_operator_delta_zero (s : Finset A) (g : G) (hs : s ⊆ D.desc g)
    (x : A → ℝ) (b : G) (hb : D.length g ≤ D.length b) (hne : b ≠ g) :
    operator f s (fun a ha d hd hne => D.commute g a d (hs ha) (hs hd) hne)
      x (fun a => if a = b then 1 else 0) g = 0 := by
  induction s using Finset.induction_on generalizing g with
  | empty => simp [operator_empty,hne.symm]
  | @insert a s ha ih =>
    have hga := hs (Finset.mem_insert_self a s)
    have hs0 : s ⊆ D.desc g := fun d hd => hs (Finset.mem_insert_of_mem hd)
    have hs1 : s ⊆ D.desc (g * f a) := by
      intro d hd
      exact D.preserve g a d hga (hs0 hd) (by intro he; exact ha (he ▸ hd))
    have hd := D.decrease g a hga
    have hb1 : D.length (g*f a) ≤ D.length b := by omega
    have hne1 : b ≠ g*f a := by intro he; rw [he] at hb; omega
    have hc : (↑(insert a s) : Set A).Pairwise (fun a d => Commute (f a) (f d)) :=
      fun _ ha _ hd hne => D.commute g _ _ (hs ha) (hs hd) hne
    change operator f (insert a s) hc x (fun a => if a = b then 1 else 0) g = 0
    rw [operator_insert f s a ha,Module.End.mul_apply,blend_apply]
    rw [ih g hs0 hb hne,ih (g*f a) hs1 hb1 hne1]
    ring

theorem interpolation_vertex_zero (p : D.Point) (b : G)
    (hb : D.length p.top ≤ D.length b) (hne : b ≠ p.top) :
    D.interpolation p (fun a => if a = b then 1 else 0) = 0 :=
  D.descending_operator_delta_zero (D.active p) p.top (D.pointCell p).subset p.coord b hb hne

theorem interpolation_top_eq (p q : D.Point)
    (he : ∀ φ, D.interpolation p φ = D.interpolation q φ) : p.top = q.top := by
  have length_le (p q : D.Point) (he : ∀ φ, D.interpolation p φ = D.interpolation q φ) :
      D.length q.top ≤ D.length p.top := by
    by_contra hn
    have hlt : D.length p.top < D.length q.top := lt_of_not_ge hn
    have hne : q.top ≠ p.top := by intro eq; rw [eq] at hlt; exact lt_irrefl _ hlt
    have hz := D.interpolation_vertex_zero p q.top hlt.le hne
    have hp := D.interpolation_vertex_pos q
    rw [← he,hz] at hp
    exact lt_irrefl _ hp
  have h₁ := length_le p q he
  by_contra hne
  have hz := D.interpolation_vertex_zero q p.top h₁ hne
  have hp := D.interpolation_vertex_pos p
  rw [he,hz] at hp
  exact lt_irrefl _ hp

variable (exponent : A → G →* Multiplicative ℝ)
variable (hexponent : ∀ g a, a ∈ D.desc g → ∀ b, b ∈ D.desc g →
  (exponent a (f b)).toAdd = if a = b then 1 else 0)

include hexponent in
theorem interpolation_exponent (p : D.Point) (a : A) (ha : a ∈ D.desc p.top) :
    D.interpolation p (fun g => (exponent a g).toAdd) =
      (exponent a p.top).toAdd + p.coord a := by
  refine (operator_linear f (exponent a) (D.active p)
    (D.cellComm (D.pointCell p)) p.coord p.top).trans ?_
  congr 1
  have he : ∀ b ∈ D.active p, (exponent a (f b)).toAdd = if a = b then 1 else 0 :=
    fun b hb => hexponent p.top a ha b ((D.pointCell p).subset hb)
  simp only [Finset.sum_congr rfl (fun b hb => congrArg (fun t : ℝ => p.coord b * t) (he b hb)),
    mul_ite,mul_one,mul_zero,Finset.sum_ite_eq]
  by_cases h : p.coord a = 0
  · simp [h]
  · simp [mem_active,h]

include exponent hexponent in
theorem interpolation_injective : Function.Injective
    (fun p : D.Point => fun φ : G → ℝ => D.interpolation p φ) := by
  intro p q he
  have he' : ∀ φ, D.interpolation p φ = D.interpolation q φ := fun φ => congrFun he φ
  have hb := D.interpolation_top_eq p q he'
  apply Point.ext hb
  funext a
  by_cases ha : a ∈ D.desc p.top
  · have hq : a ∈ D.desc q.top := by simpa only [hb] using ha
    have hh := he' (fun g => (exponent a g).toAdd)
    rw [D.interpolation_exponent exponent hexponent p a ha,
      D.interpolation_exponent exponent hexponent q a hq,hb] at hh
    exact add_left_cancel hh
  · have hp : p.coord a = 0 := by_contra (fun hn => ha (p.support a hn))
    have hq : q.coord a = 0 := by
      by_contra hn
      exact ha (by simpa only [hb] using q.support a hn)
    rw [hp,hq]

end EilenbergGanea.DescendingCube.Data

open Classical Topology
namespace WeakRealization

/-- A homeomorphism is induced by point-separating coordinates and actual
continuous lifts on each characteristic disk, in both directions. -/
def homeomorph {ι κ X Y Z : Type*} {E : ι → Type*} {F : κ → Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    [∀ i, TopologicalSpace (E i)] [∀ j, TopologicalSpace (F j)]
    (e : ((i : ι) × E i) → X) (f : ((j : κ) × F j) → Y)
    (he : IsQuotientMap e) (hf : IsQuotientMap f)
    (J : X → Z) (K : Y → Z) (hJ : Function.Injective J) (hK : Function.Injective K)
    (hxy : ∀ i, ∃ φ : C(E i,Y), ∀ t, K (φ t) = J (e ⟨i,t⟩))
    (hyx : ∀ j, ∃ φ : C(F j,X), ∀ t, J (φ t) = K (f ⟨j,t⟩)) : X ≃ₜ Y := by
  have hx : ∀ x, ∃ y, K y = J x := by
    intro x
    obtain ⟨⟨i,t⟩,rfl⟩ := he.surjective x
    obtain ⟨φ,hφ⟩ := hxy i
    exact ⟨φ t,hφ t⟩
  have hy : ∀ y, ∃ x, J x = K y := by
    intro y
    obtain ⟨⟨j,t⟩,rfl⟩ := hf.surjective y
    obtain ⟨φ,hφ⟩ := hyx j
    exact ⟨φ t,hφ t⟩
  let A : X → Y := fun x => (hx x).choose
  let B : Y → X := fun y => (hy y).choose
  have hA : ∀ x, K (A x) = J x := fun x => (hx x).choose_spec
  have hB : ∀ y, J (B y) = K y := fun y => (hy y).choose_spec
  refine {
    toEquiv := {
      toFun := A
      invFun := B
      left_inv := fun x => hJ ((hB (A x)).trans (hA x))
      right_inv := fun y => hK ((hA (B y)).trans (hB y)) }
    continuous_toFun := ?_
    continuous_invFun := ?_ }
  · apply he.continuous_iff.mpr
    apply continuous_sigma
    intro i
    obtain ⟨φ,hφ⟩ := hxy i
    have hh : (fun t => A (e ⟨i,t⟩)) = φ := by
      funext t
      exact hK ((hA _).trans (hφ t).symm)
    change Continuous (fun t => A (e ⟨i,t⟩))
    rw [hh]
    exact φ.continuous
  · apply hf.continuous_iff.mpr
    apply continuous_sigma
    intro j
    obtain ⟨φ,hφ⟩ := hyx j
    have hh : (fun t => B (f ⟨j,t⟩)) = φ := by
      funext t
      exact hJ ((hB _).trans (hφ t).symm)
    change Continuous (fun t => B (f ⟨j,t⟩))
    rw [hh]
    exact φ.continuous

end WeakRealization

namespace EilenbergGanea.CubeInterpolation
open CubicalChains.Reorientation
variable {G V : Type*} [Group G]

/-- Interpolation in a listed cube, independent of any topological model. -/
def listed (f : V → G) (w : List V) (x : V → ℝ) : Module.End ℝ (G → ℝ) :=
  (w.map (fun v => blend (f v) (x v))).prod

@[simp] theorem listed_nil (f : V → G) (x : V → ℝ) : listed f [] x = 1 := rfl
@[simp] theorem listed_cons (f : V → G) (v : V) (w : List V) (x : V → ℝ) :
    listed f (v::w) x = blend (f v) (x v) * listed f w x := rfl

theorem operator_listed [DecidableEq V] (f : V → G) (w : List V) (hw : w.Nodup)
    (hc : (w.toFinset : Set V).Pairwise (fun v u => Commute (f v) (f u))) (x : V → ℝ) :
    operator f w.toFinset hc x = listed f w x :=
  Finset.noncommProd_toFinset w _ _ hw

/-- Literal multilinear invariance under reversing selected cube directions. -/
theorem listed_reorientation (f : V → G) (w : List (Signed V))
    (hw : w.Pairwise (fun a b => Commute (f a.1) (f b.1)))
    (x : Signed V → ℝ) (z : V → ℝ)
    (hx : ∀ a ∈ w, x a = if a.2 then 1-z a.1 else z a.1) (φ : G → ℝ) (g : G) :
    listed (step f) w x φ g = listed f (w.map Prod.fst) z φ (origin f g w) := by
  induction w generalizing g with
  | nil => rfl
  | cons a w ih =>
    obtain ⟨ha,hw⟩ := List.pairwise_cons.mp hw
    have hxw : ∀ b ∈ w, x b = if b.2 then 1-z b.1 else z b.1 :=
      fun b hb => hx b (by simp [hb])
    simp only [listed_cons,List.map_cons,Module.End.mul_apply,blend_apply,
      ih hw hxw,hx a (by simp),step,origin]
    cases hb : a.2
    · simp only [Bool.false_eq_true,↓reduceIte]
      rw [origin_shift f g (f a.1) w ha]
    · simp only [↓reduceIte]
      rw [origin_shift f g (f a.1)⁻¹ w (fun b hb => (ha b hb).inv_left),
        inv_mul_cancel_right]
      ring

end EilenbergGanea.CubeInterpolation

namespace EilenbergGanea.ArtinCubicalTopology
open TraceWords CubeInterpolation CubicalChains.Reorientation
variable {V : Type*} [Fintype V] (L : SimpleGraph V)

local instance instSymmAdj_solutions : Std.Symm L.Adj := ⟨fun _ _ h => h.symm⟩
local instance instIrreflAdj_solutions : Std.Irrefl L.Adj := ⟨fun _ => L.irrefl⟩

abbrev f := artinGenerator L
abbrev comm := fun v w h => adjacent_generators_commute L (v := v) (w := w) h
abbrev D := artinDescendingData L
abbrev Positive := CubeRealization.Point L (f L) (comm L)
abbrev Descending := (D L).Point

omit [Fintype V] in
@[simp] theorem step_eq (a : Letter V) : step (f L) a = letterValue (f L) (invLetter a) := by
  cases a with | mk v b => cases b <;> rfl

def exponent (v : V) : ArtinGroup L →* Multiplicative ℝ :=
  artinLift L (fun w => Multiplicative.ofAdd (if v = w then (1 : ℝ) else 0))
    (fun _ _ _ => Commute.all _ _)

omit [Fintype V] in
@[simp] theorem exponent_generator (v w : V) :
    (exponent L v (f L w)).toAdd = if v = w then 1 else 0 := by
  simp [exponent,f]

omit [Fintype V] in
@[simp] theorem height_generator (v : V) : (height L (f L v)).toAdd = 1 := by
  exact congrArg Multiplicative.toAdd (PresentedGroup.toGroup.of _)

def signedExponent (a : Letter V) : ArtinGroup L →* Multiplicative ℝ :=
  artinLift L (fun v => Multiplicative.ofAdd
    (if a.1 = v then (if a.2 then (-1 : ℝ) else 1) else 0))
    (fun _ _ _ => Commute.all _ _)

theorem signedExponent_step (g : ArtinGroup L) (a : Letter V) (ha : a ∈ (D L).desc g)
    (b : Letter V) (hb : b ∈ (D L).desc g) :
    (signedExponent L a (letterValue (f L) (invLetter b))).toAdd = if a = b then 1 else 0 := by
  by_cases he : a = b
  · subst b
    rcases a with ⟨v,b⟩
    cases b <;> simp [signedExponent,letterValue,invLetter,f]
  · have hi : Independent L a b := rightDescents_pairwise L g
      (by simpa [D,artinDescendingData] using ha) (by simpa [D,artinDescendingData] using hb) he
    have hv : a.1 ≠ b.1 := hi.ne
    rcases b with ⟨v,b⟩
    cases b <;> simp [signedExponent,letterValue,invLetter,f,hv,he]

theorem positive_interp_inj : Function.Injective
    (fun p : Positive L => fun φ => CubeRealization.interpolation L (f L) (comm L) p φ) :=
  CubeRealization.interpolation_injective L (f L) (comm L) (height L) (height_generator L)
    (exponent L) (exponent_generator L)

theorem descending_interp_inj : Function.Injective
    (fun p : Descending L => fun φ => (D L).interpolation p φ) :=
  (D L).interpolation_injective (signedExponent L) (by
    intro g a ha b hb
    by_cases he : a = b <;> simpa [he] using signedExponent_step L g a ha b hb)

def flip (b : Bool) (t : unitInterval) : unitInterval :=
  if b then unitInterval.symm t else t

@[simp] theorem flip_flip (b : Bool) (t : unitInterval) : flip b (flip b t) = t := by
  cases b <;> simp [flip]

theorem flip_continuous (b : Bool) : Continuous (flip b) := by
  cases b
  · exact continuous_id
  · exact unitInterval.continuous_symm

def vertexEquiv (w : Word V) (hw : (w.map Prod.fst).Nodup) :
    w.toFinset ≃ (w.map Prod.fst).toFinset :=
  Equiv.ofBijective (fun a => ⟨a.val.1,by
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨a.val,List.mem_toFinset.mp a.property,rfl⟩)⟩) (by
    constructor
    · intro a b he
      apply Subtype.ext
      exact (List.nodup_map_iff_inj_on (hw.of_map Prod.fst)).mp hw
        a.val (List.mem_toFinset.mp a.property) b.val (List.mem_toFinset.mp b.property) (congrArg Subtype.val he)
    · intro v
      obtain ⟨a,ha,he⟩ := List.mem_map.mp (List.mem_toFinset.mp v.property)
      exact ⟨⟨a,by simpa using ha⟩,Subtype.ext he⟩)

omit [Fintype V] in
@[simp] theorem vertexEquiv_val (w : Word V) (hw : (w.map Prod.fst).Nodup)
    (a : w.toFinset) : (vertexEquiv w hw a).val = a.val.1 := rfl

def toPositiveCoords (w : Word V) (hw : (w.map Prod.fst).Nodup)
    (x : w.toFinset → unitInterval) : (w.map Prod.fst).toFinset → unitInterval :=
  fun v => flip ((vertexEquiv w hw).symm v).val.2 (x ((vertexEquiv w hw).symm v))

omit [Fintype V] in
@[simp] theorem toPositiveCoords_apply (w : Word V) (hw : (w.map Prod.fst).Nodup)
    (x : w.toFinset → unitInterval) (a : w.toFinset) :
    toPositiveCoords w hw x (vertexEquiv w hw a) = flip a.val.2 (x a) := by
  simp [toPositiveCoords]

omit [Fintype V] in
theorem toPositiveCoords_continuous (w : Word V) (hw : (w.map Prod.fst).Nodup) :
    Continuous (toPositiveCoords w hw) :=
  continuous_pi (fun _ => (flip_continuous _).comp (continuous_apply _))

def toDescendingCoords (w : Word V) (hw : (w.map Prod.fst).Nodup)
    (z : (w.map Prod.fst).toFinset → unitInterval) : w.toFinset → unitInterval :=
  fun a => flip a.val.2 (z (vertexEquiv w hw a))

omit [Fintype V] in
theorem toDescendingCoords_continuous (w : Word V) (hw : (w.map Prod.fst).Nodup) :
    Continuous (toDescendingCoords w hw) :=
  continuous_pi (fun _ => (flip_continuous _).comp (continuous_apply _))

omit [Fintype V] in
@[simp] theorem toPositive_toDescending (w : Word V) (hw : (w.map Prod.fst).Nodup)
    (z : (w.map Prod.fst).toFinset → unitInterval) :
    toPositiveCoords w hw (toDescendingCoords w hw z) = z := by
  funext v
  obtain ⟨a,rfl⟩ := (vertexEquiv w hw).surjective v
  simp [toDescendingCoords]

def positiveCell (g : ArtinGroup L) (w : Word V) (hw : (w.map Prod.fst).Pairwise L.Adj) :
    CubeRealization.Cell (G := ArtinGroup L) L where
  base := origin (f L) g w
  directions := (w.map Prod.fst).toFinset
  clique := fun _ ha _ hb he => hw.forall (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) he

def descendingCell (g : ArtinGroup L) (w : Word V)
    (hd : ∀ a ∈ w, a ∈ rightDescents L g) : (D L).Cell where
  top := g
  directions := w.toFinset
  subset a ha := by simpa [D,artinDescendingData] using hd a (List.mem_toFinset.mp ha)

theorem interpolation_reorientation (g : ArtinGroup L) (w : Word V)
    (hw : (w.map Prod.fst).Pairwise L.Adj) (hd : ∀ a ∈ w, a ∈ rightDescents L g)
    (x : (D L).Coordinates (descendingCell L g w hd)) (φ : ArtinGroup L → ℝ) :
    (D L).interpolation ((D L).characteristic (descendingCell L g w hd) x) φ =
      CubeRealization.interpolation L (f L) (comm L)
        (CubeRealization.characteristic (f L) (comm L) (positiveCell L g w hw)
          (toPositiveCoords w hw.nodup x)) φ := by
  refine ((D L).interpolation_characteristic (descendingCell L g w hd) x φ).trans ?_
  refine Eq.trans ?_ (CubeRealization.interpolation_characteristic L (f L) (comm L)
    (positiveCell L g w hw) (toPositiveCoords w hw.nodup x) φ).symm
  have hf : (fun a : Letter V => letterValue (artinGenerator L) (invLetter a)) = step (f L) :=
    funext (fun a => (step_eq L a).symm)
  erw [operator_listed _ w (hw.nodup.of_map Prod.fst),operator_listed _ _ hw.nodup]
  have hop := congrArg (fun k : Letter V → ArtinGroup L => listed k w) hf
  rw [hop]
  apply listed_reorientation
  · exact (List.pairwise_map.mp hw).imp (fun hh => adjacent_generators_commute L hh)
  · intro a ha
    let aa : w.toFinset := ⟨a,by simpa using ha⟩
    have h₁ : (D L).fullCoord (descendingCell L g w hd) x a = (x aa : ℝ) := by
      exact (D L).fullCoord_mem (descendingCell L g w hd) x aa
    have h₂ : CubeRealization.fullCoord (positiveCell L g w hw)
        (toPositiveCoords w hw.nodup x) a.1 = (flip a.2 (x aa) : ℝ) := by
      have hh := CubeRealization.fullCoord_mem (positiveCell L g w hw)
        (toPositiveCoords w hw.nodup x) (vertexEquiv w hw.nodup aa)
      exact hh.trans (congrArg (fun z : unitInterval => (z : ℝ))
        (toPositiveCoords_apply w hw.nodup x aa))
    rw [h₁,h₂]
    cases h : a.2 <;> simp [flip]

theorem descendingCell_rep (c : (D L).Cell) :
    ∃ (g : ArtinGroup L) (w : Word V) (_hw : (w.map Prod.fst).Pairwise L.Adj)
      (hd : ∀ a ∈ w, a ∈ rightDescents L g), descendingCell L g w hd = c := by
  let w := c.directions.toList
  have hd : ∀ a ∈ w, a ∈ rightDescents L c.top := by
    intro a ha
    have hh := c.subset (Finset.mem_toList.mp ha)
    simpa [D,artinDescendingData] using hh
  have hw : (w.map Prod.fst).Pairwise L.Adj := by
    apply List.pairwise_map.mpr
    apply c.directions.nodup_toList.pairwise_of_forall_ne
    intro a ha b hb he
    exact rightDescents_pairwise L c.top (hd a ha) (hd b hb) he
  refine ⟨c.top,w,hw,hd,?_⟩
  cases c with
  | mk g s hs =>
    dsimp only [descendingCell,w]
    congr
    exact s.toList_toFinset

omit [Fintype V] in
theorem positiveCell_rep (c : CubeRealization.Cell (G := ArtinGroup L) L) :
    ∃ (g : ArtinGroup L) (w : Word V) (hw : (w.map Prod.fst).Pairwise L.Adj)
      (_hd : ∀ a ∈ w, a ∈ rightDescents L g), positiveCell L g w hw = c := by
  let v := c.directions.toList
  have hv : v.Pairwise L.Adj := c.directions.nodup_toList.pairwise_of_forall_ne
    (fun a ha b hb he => c.clique (Finset.mem_toList.mp ha) (Finset.mem_toList.mp hb) he)
  let o := CubeDescents.orient L c.base v
  have hw : (o.2.map Prod.fst).Pairwise L.Adj := by
    simpa only [o,CubeDescents.orient_map] using hv
  have hd : ∀ a ∈ o.2, a ∈ rightDescents L o.1 := CubeDescents.orient_descents L c.base v hv
  refine ⟨o.1,o.2,hw,hd,?_⟩
  have hb : origin (f L) o.1 o.2 = c.base := CubeDescents.origin_orient L c.base v hv
  have hs : (o.2.map Prod.fst).toFinset = c.directions := by
    simp only [o,CubeDescents.orient_map,v,Finset.toList_toFinset]
  cases c with
  | mk g s hc =>
    change CubeRealization.Cell.mk (origin (f L) o.1 o.2) (o.2.map Prod.fst).toFinset _ = _
    congr

theorem descending_local_lift (c : (D L).Cell) :
    ∃ φ : C((D L).Coordinates c,Positive L), ∀ x,
      (fun ψ => CubeRealization.interpolation L (f L) (comm L) (φ x) ψ) =
        (fun ψ => (D L).interpolation ((D L).characteristic c x) ψ) := by
  obtain ⟨g,w,hw,hd,rfl⟩ := descendingCell_rep L c
  refine ⟨⟨fun x => CubeRealization.characteristic (f L) (comm L) (positiveCell L g w hw)
    (toPositiveCoords w hw.nodup x),
    (CubeRealization.characteristic_continuous (f L) (comm L) (positiveCell L g w hw)).comp
      (toPositiveCoords_continuous w hw.nodup)⟩,?_⟩
  intro x
  funext ψ
  exact (interpolation_reorientation L g w hw hd x ψ).symm

theorem positive_local_lift (c : CubeRealization.Cell (G := ArtinGroup L) L) :
    ∃ φ : C(CubeRealization.Coordinates c,Descending L), ∀ x,
      (fun ψ => (D L).interpolation (φ x) ψ) =
        (fun ψ => CubeRealization.interpolation L (f L) (comm L)
          (CubeRealization.characteristic (f L) (comm L) c x) ψ) := by
  obtain ⟨g,w,hw,hd,rfl⟩ := positiveCell_rep L c
  refine ⟨⟨fun x => (D L).characteristic (descendingCell L g w hd) (toDescendingCoords w hw.nodup x),
    ((D L).characteristic_continuous (descendingCell L g w hd)).comp
      (toDescendingCoords_continuous w hw.nodup)⟩,?_⟩
  intro x
  funext ψ
  change (D L).interpolation ((D L).characteristic (descendingCell L g w hd)
    (toDescendingCoords w hw.nodup x)) ψ = _
  change (w.map Prod.fst).toFinset → unitInterval at x
  simpa only [toPositive_toDescending] using interpolation_reorientation L g w hw hd
    (toDescendingCoords w hw.nodup x) ψ

/-- Reorientation preserves the actual weak topologies, not only cellular chains. -/
def reorient : Descending L ≃ₜ Positive L :=
  WeakRealization.homeomorph (D L).evaluation (CubeRealization.evaluation (f L) (comm L))
    (D L).evaluation_quotient (CubeRealization.evaluation_quotient (f L) (comm L))
    (fun p ψ => (D L).interpolation p ψ)
    (fun p ψ => CubeRealization.interpolation L (f L) (comm L) p ψ)
    (descending_interp_inj L) (positive_interp_inj L)
    (descending_local_lift L) (positive_local_lift L)

end EilenbergGanea.ArtinCubicalTopology

open Classical Set Topology
namespace CompactChart

/-- A characteristic map which has singleton fibers over its open cell has a
continuous inverse there. Compactness is used only on the closed disk; no
regularity of the attaching sphere is required. -/
theorem continuousOn_symm {A X : Type*} [TopologicalSpace A] [TopologicalSpace X]
    [T2Space X] (e : PartialEquiv A X) (K : Set A) (hK : IsCompact K)
    (hsub : e.source ⊆ K) (hc : ContinuousOn e K)
    (hboundary : ∀ a ∈ K, e a ∈ e.target → a ∈ e.source) :
    ContinuousOn e.symm e.target := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let f : K → X := fun a => e a
  have hf : Continuous f := continuousOn_iff_continuous_domRestrict.mp hc
  let r := e.target.restrictPreimage f
  have hr : Function.Surjective r := by
    intro x
    refine ⟨⟨⟨e.symm x,hsub (e.map_target x.property)⟩,?_⟩,?_⟩
    · change e (e.symm x) ∈ e.target
      rw [e.right_inv x.property]
      exact x.property
    · exact Subtype.ext (e.right_inv x.property)
  have hq : IsQuotientMap r :=
    (hf.isClosedMap.restrictPreimage e.target).isQuotientMap hf.restrictPreimage hr
  apply continuousOn_iff_continuous_domRestrict.mpr
  apply hq.continuous_iff.mpr
  have he : (fun x : e.target => e.symm x) ∘ r =
      (fun a : f ⁻¹' e.target => (a.val.val : A)) := by
    funext a
    exact e.left_inv (hboundary a.val a.val.property a.property)
  change Continuous ((fun x : e.target => e.symm x) ∘ r)
  rw [he]
  exact continuous_subtype_val.comp continuous_subtype_val

end CompactChart

end

end OAI
end

section
-- module Solutions.OAIEG.Simplicial_Chains
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set

namespace SimplicialChains
variable {V : Type*}
abbrev Chains (V : Type*) := List V →₀ ℤ

def front (v : V) : Chains V →ₗ[ℤ] Chains V := Finsupp.lmapDomain ℤ ℤ (List.cons v)
@[simp] theorem front_single (v : V) (w : List V) (n : ℤ) :
    front v (Finsupp.single w n) = Finsupp.single (v::w) n := by simp [front]

def boundaryTerm : List V → Chains V
  | [] => 0
  | v::w => Finsupp.single w 1 - front v (boundaryTerm w)
def boundary : Chains V →ₗ[ℤ] Chains V := Finsupp.linearCombination ℤ boundaryTerm
@[simp] theorem boundary_single (w : List V) (n : ℤ) :
    boundary (Finsupp.single w n) = n • boundaryTerm w := by simp [boundary]
@[simp] theorem boundaryTerm_nil : boundaryTerm ([] : List V) = 0 := rfl
@[simp] theorem boundaryTerm_cons (v : V) (w : List V) :
    boundaryTerm (v::w) = Finsupp.single w 1 - front v (boundaryTerm w) := rfl

def includeVec {I : Type*} [Fintype I] (f : I → List V) : (I → ℤ) →ₗ[ℤ] Chains V :=
  (Pi.basisFun ℤ I).constr ℤ (fun i => Finsupp.single (f i) 1)
@[simp] theorem includeVec_single {I : Type*} [Fintype I] [DecidableEq I] (f : I → List V) (i : I) :
    includeVec f (Pi.single i 1) = Finsupp.single (f i) 1 := by
  have hb : (Pi.basisFun ℤ I) i = Pi.single i 1 := by
    funext j
    simp [Pi.basisFun_apply,Pi.single_apply]
  rw [← hb]
  exact (Pi.basisFun ℤ I).constr_basis ℤ _ i

variable [LinearOrder V] (L : SimpleGraph V)
def Valid (w : List V) : Prop := w.Pairwise (· < ·) ∧ w.Pairwise L.Adj

def chains (k : ℕ) : Submodule ℤ (Chains V) :=
  Finsupp.supported ℤ ℤ {w | Valid L w ∧ w.length = k}

/-- An augmented chain contraction on the actual ordered cliques. -/
structure Contraction where
  homotopy : Chains V →ₗ[ℤ] Chains V
  degree : ∀ k c, c ∈ chains L k → homotopy c ∈ chains L (k+1)
  identity : ∀ w, Valid L w →
    boundary (homotopy (Finsupp.single w 1)) + homotopy (boundaryTerm w) =
      Finsupp.single w 1

variable {L}

theorem valid_sublist {w u : List V} (hw : Valid L w) (hu : u.Sublist w) : Valid L u :=
  ⟨hw.1.sublist hu,hw.2.sublist hu⟩

/-- Explicit finite index data for vertices, edges and triangles. Every
geometric field is an indexing identity, not an acyclicity assumption. -/
structure TwoDimensionalIndices (E T : Type*) where
  edge : E → V × V
  triangle : T → V × V × V
  face : T → E × E × E
  edgeIndex : V → V → E
  triangleIndex : V → V → V → T
  edge_valid : ∀ e, Valid L [(edge e).1,(edge e).2]
  triangle_valid : ∀ t, Valid L [(triangle t).1,(triangle t).2.1,(triangle t).2.2]
  edge_inverse : ∀ e, edgeIndex (edge e).1 (edge e).2 = e
  edge_complete : ∀ a b, Valid L [a,b] → edge (edgeIndex a b) = (a,b)
  triangle_complete : ∀ a b c, Valid L [a,b,c] → triangle (triangleIndex a b c) = (a,b,c)
  face_edge : ∀ t,
    edge (face t).1 = ((triangle t).2.1,(triangle t).2.2) ∧
    edge (face t).2.1 = ((triangle t).1,(triangle t).2.2) ∧
    edge (face t).2.2 = ((triangle t).1,(triangle t).2.1)
  length_le : ∀ w, Valid L w → w.length ≤ 3

namespace TwoDimensionalIndices
variable {E T : Type*} [Fintype V] [Fintype E] [Fintype T]
variable (D : TwoDimensionalIndices (L := L) E T)
def eList (e : E) : List V := [(D.edge e).1,(D.edge e).2]
def tList (t : T) : List V := [(D.triangle t).1,(D.triangle t).2.1,(D.triangle t).2.2]

variable (root : V) (h₀ : (V → ℤ) →ₗ[ℤ] (E → ℤ))
    (h₁ : (E → ℤ) →ₗ[ℤ] (T → ℤ))

def fillTerm : List V → Chains V
  | [] => Finsupp.single [root] 1
  | [v] => includeVec D.eList (h₀ (Pi.single v 1))
  | [a,b] => includeVec D.tList (h₁ (Pi.single (D.edgeIndex a b) 1))
  | _ => 0

def fill : Chains V →ₗ[ℤ] Chains V := Finsupp.linearCombination ℤ (D.fillTerm root h₀ h₁)
omit [Fintype V] in
@[simp] theorem fill_single (w : List V) (n : ℤ) :
    D.fill root h₀ h₁ (Finsupp.single w n) = n • D.fillTerm root h₀ h₁ w := by simp [fill]

end TwoDimensionalIndices
end SimplicialChains



namespace SimplicialChains
variable {V W : Type*}
def reindex (f : V → W) : Chains V →ₗ[ℤ] Chains W :=
  Finsupp.lmapDomain ℤ ℤ (List.map f)
@[simp] theorem reindex_single (f : V → W) (w : List V) (n : ℤ) :
    reindex f (Finsupp.single w n) = Finsupp.single (w.map f) n := by simp [reindex]
@[simp] theorem reindex_front (f : V → W) (v : V) (c : Chains V) :
    reindex f (front v c) = front (f v) (reindex f c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add,hc,hd]
  | single w n => simp

@[simp] theorem reindex_inverse (e : V ≃ W) (c : Chains V) :
    reindex e.symm (reindex e c) = c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add,hc,hd]
  | single w n => simp

end SimplicialChains



end

end OAI
end

section
-- module Solutions.OAIEG.Cubical_HeightChains
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set

namespace CubicalChains.HeightFiltration
open Classical
variable {G A : Type*} [Group G] [LinearOrder A] (L : SimpleGraph A)
variable (K : SimplicialChains.Contraction L)

def embed (g : G) : SimplicialChains.Chains A →ₗ[ℤ] Chains G A :=
  Finsupp.lmapDomain ℤ ℤ (fun w => (g,w))
omit [Group G] [LinearOrder A] in
@[simp] theorem embed_single (g : G) (w : List A) (n : ℤ) :
    embed g (Finsupp.single w n) = Finsupp.single (g,w) n := by simp [embed]

omit [Group G] [LinearOrder A] in
theorem embed_front (g : G) (a : A) (c : SimplicialChains.Chains A) :
    embed g (SimplicialChains.front a c) = front a (embed g c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add,hc,hd]
  | single w n => simp

omit [Group G] [LinearOrder A] in
theorem upperTerm_embed (g : G) (w : List A) :
    upperTerm g w = -embed g (SimplicialChains.boundaryTerm w) := by
  induction w with
  | nil => simp
  | cons a w ih =>
    simp only [upperTerm_cons,SimplicialChains.boundaryTerm_cons,map_sub,embed_single,
      embed_front,ih,map_neg]
    abel

omit [Group G] [LinearOrder A] in
theorem upper_embed (g : G) (c : SimplicialChains.Chains A) :
    upper (embed g c) = -embed g (SimplicialChains.boundary c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add,hc,hd]; abel
  | single w n => simp [upperTerm_embed,smul_neg]

def homotopyTerm (h : G → ℤ) (g : G) (w : List A) : Chains G A :=
  if h g < 0 then -embed g (K.homotopy (Finsupp.single w 1)) else 0

def homotopy (h : G → ℤ) : Chains G A →ₗ[ℤ] Chains G A :=
  Finsupp.linearCombination ℤ (fun p => homotopyTerm L K h p.1 p.2)
omit [Group G] in
@[simp] theorem homotopy_single (h : G → ℤ) (g : G) (w : List A) (n : ℤ) :
    homotopy L K h (Finsupp.single (g,w) n) = n • homotopyTerm L K h g w := by simp [homotopy]

omit [Group G] in
theorem homotopy_embed (h : G → ℤ) (g : G) (c : SimplicialChains.Chains A) :
    homotopy L K h (embed g c) = if h g < 0 then -embed g (K.homotopy c) else 0 := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
    simp only [map_add,hc,hd]
    split
    · simp_all
      abel
    · simp_all
  | single w n =>
    simp only [embed_single,homotopy_single,homotopyTerm]
    split
    · rw [show Finsupp.single w n = n • Finsupp.single w 1 by simp]
      simp only [map_smul,smul_neg]
    · simp

omit [Group G] in
theorem upper_homotopy (h : G → ℤ) (g : G) (w : List A)
    (hw : SimplicialChains.Valid L w) (hg : h g < 0) :
    upper (homotopyTerm L K h g w) + homotopy L K h (upperTerm g w) =
      Finsupp.single (g,w) 1 := by
  simp only [homotopyTerm,ite_eq_left hg,map_neg,upper_embed,upperTerm_embed,homotopy_embed]
  simp only [neg_neg]
  rw [← map_add,K.identity w hw,embed_single]

def above (h : G → ℤ) (k : ℕ) (m : ℤ) : Submodule ℤ (Chains G A) :=
  Finsupp.supported ℤ ℤ {p | SimplicialChains.Valid L p.2 ∧ p.2.length = k ∧ m ≤ h p.1}

omit [Group G] in
theorem above_mono (h : G → ℤ) {k : ℕ} {m n : ℤ} (hmn : m ≤ n) :
    above L h k n ≤ above L h k m := by
  apply Finsupp.supported_mono
  intro p hp
  exact ⟨hp.1,hp.2.1,hmn.trans hp.2.2⟩

omit [Group G] in
theorem embed_supported (h : G → ℤ) (g : G) {k : ℕ} (c : SimplicialChains.Chains A)
    (hc : c ∈ SimplicialChains.chains L k) : embed g c ∈ above L h k (h g) := by
  apply supported_map (embed g) _ _ _ hc
  intro w hw
  rw [embed_single]
  exact Finsupp.single_mem_supported ℤ 1 ⟨hw.1,hw.2,le_refl _⟩

omit [Group G] in
theorem homotopyTerm_above (h : G → ℤ) (g : G) (w : List A)
    (hw : SimplicialChains.Valid L w) : homotopyTerm L K h g w ∈ above L h (w.length+1) (h g) := by
  unfold homotopyTerm
  split
  · apply Submodule.neg_mem
    apply embed_supported
    exact K.degree _ _ (Finsupp.single_mem_supported ℤ 1 ⟨hw,rfl⟩)
  · exact Submodule.zero_mem _

omit [Group G] in
theorem homotopy_above (h : G → ℤ) {k : ℕ} {m : ℤ} {c : Chains G A}
    (hc : c ∈ above L h k m) : homotopy L K h c ∈ above L h (k+1) m := by
  apply supported_map (homotopy L K h) _ _ _ hc
  rintro ⟨g,w⟩ ⟨hw,hl,hh⟩
  dsimp at hw hl hh ⊢
  rw [homotopy_single,one_smul]
  have ht := homotopyTerm_above L K h g w hw
  rw [hl] at ht
  exact above_mono L h hh ht


variable (v : A → G) (h : G → ℤ)
variable (hv : ∀ g a, h (g * v a) = h g + 1)

include hv in
theorem lowerTerm_above (g : G) (w : List A) (hw : SimplicialChains.Valid L w) :
    lowerTerm v g w ∈ above L h (w.length-1) (h g+1) := by
  apply Finsupp.supported_mono _ (lowerTerm_supported v g w)
  rintro ⟨g',u⟩ ⟨a,ha,rfl⟩
  exact ⟨SimplicialChains.valid_sublist hw ha.sublist,by have := ha.length; omega,
    by dsimp; rw [hv]⟩

include hv in
theorem lower_above {k : ℕ} {m : ℤ} {c : Chains G A}
    (hc : c ∈ above L h k m) : lower v c ∈ above L h (k-1) (m+1) := by
  apply supported_map (lower v) _ _ _ hc
  rintro ⟨g,w⟩ ⟨hw,hl,hh⟩
  dsimp at hw hl hh ⊢
  rw [lower_single,one_smul]
  have ht := lowerTerm_above L v h hv g w hw
  rw [hl] at ht
  exact above_mono L h (by omega) ht

omit [Group G] in
theorem upper_above {k : ℕ} {m : ℤ} {c : Chains G A}
    (hc : c ∈ above L h k m) : upper c ∈ above L h (k-1) m := by
  apply supported_map (upper) _ _ _ hc
  rintro ⟨g,w⟩ ⟨hw,hl,hh⟩
  dsimp at hw hl hh ⊢
  rw [upper_single,one_smul]
  apply Finsupp.supported_mono _ (upperTerm_supported g w)
  rintro ⟨g',u⟩ ⟨rfl,hs,he⟩
  dsimp at hl he hh ⊢
  exact ⟨SimplicialChains.valid_sublist hw hs,by omega,hh⟩

include hv in
theorem boundary_above {k : ℕ} {m : ℤ} {c : Chains G A}
    (hc : c ∈ above L h k m) : boundary v c ∈ above L h (k-1) m := by
  have he : boundary v c = lower v c + upper c := by simp [lower]
  rw [he]
  exact Submodule.add_mem _ (above_mono L h (show m ≤ m+1 by omega) (lower_above L v h hv hc))
    (upper_above L h hc)

omit [Group G] in
theorem homotopy_zero {k : ℕ} {c : Chains G A} (hc : c ∈ above L h k 0) :
    homotopy L K h c = 0 := by
  rw [above,Finsupp.supported_eq_span_single] at hc
  apply Submodule.span_induction (p := fun c _ => homotopy L K h c = 0) _ _ _ _ hc
  · rintro _ ⟨⟨g,w⟩,⟨_,_,hh⟩,rfl⟩
    simp [homotopyTerm,not_lt.mpr hh]
  · simp
  · intro c d _ _ hc hd; simp only [map_add,hc,hd,add_zero]
  · intro n c _ hc; simp only [map_smul,hc,smul_zero]

def push : Chains G A →ₗ[ℤ] Chains G A :=
  LinearMap.id - (boundary v).comp (homotopy L K h) - (homotopy L K h).comp (boundary v)

theorem push_apply (c : Chains G A) : push L K v h c =
    c - boundary v (homotopy L K h c) - homotopy L K h (boundary v c) := rfl

theorem push_single_negative (g : G) (w : List A) (hw : SimplicialChains.Valid L w)
    (hg : h g < 0) : push L K v h (Finsupp.single (g,w) 1) =
      - lower v (homotopyTerm L K h g w) - homotopy L K h (lowerTerm v g w) := by
  have hu := upper_homotopy L K h g w hw hg
  have he : boundary v (homotopyTerm L K h g w) =
      lower v (homotopyTerm L K h g w) + upper (homotopyTerm L K h g w) := by
    simp [lower]
  have he' : boundaryTerm v g w = lowerTerm v g w + upperTerm g w := by simp [lowerTerm]
  simp only [push_apply,homotopy_single,one_smul,boundary_single]
  rw [he,he',map_add,← hu]
  abel

include hv in
theorem push_single_nonnegative (g : G) (w : List A)
    (hw : SimplicialChains.Valid L w) (hg : 0 ≤ h g) :
    push L K v h (Finsupp.single (g,w) 1) = Finsupp.single (g,w) 1 := by
  have hc : Finsupp.single (g,w) (1 : ℤ) ∈ above L h w.length 0 :=
    Finsupp.single_mem_supported ℤ 1 ⟨hw,rfl,hg⟩
  rw [push_apply,homotopy_zero L K h hc,map_zero,
    homotopy_zero L K h (boundary_above L v h hv hc)]
  simp

include hv in
theorem push_above {k N : ℕ} (hk : 0 < k) {c : Chains G A}
    (hc : c ∈ above L h k (-(N+1 : ℕ) : ℤ)) :
    push L K v h c ∈ above L h k (-(N : ℤ)) := by
  apply supported_map (push L K v h) _ _ _ hc
  rintro ⟨g,w⟩ ⟨hw,hl,hh⟩
  dsimp at hw hl hh ⊢
  by_cases hg : h g < 0
  · rw [push_single_negative L K v h g w hw hg]
    apply Submodule.sub_mem
    · apply Submodule.neg_mem
      have ht := lower_above L v h hv (homotopyTerm_above L K h g w hw)
      simp only [Nat.add_sub_cancel] at ht
      rw [hl] at ht
      exact above_mono L h (by norm_num at hh ⊢; omega) ht
    · have ht := homotopy_above L K h (lowerTerm_above L v h hv g w hw)
      have he : w.length-1+1=k := by omega
      rw [he] at ht
      exact above_mono L h (by norm_num at hh ⊢; omega) ht
  · rw [push_single_nonnegative L K v h hv g w hw (not_lt.mp hg)]
    exact Finsupp.single_mem_supported ℤ 1 ⟨hw,hl,by change -(N : ℤ) ≤ h g; omega⟩

variable (comm : ∀ a b, L.Adj a b → Commute (v a) (v b))

include comm in
theorem boundary_squared {k : ℕ} {m : ℤ} {c : Chains G A}
    (hc : c ∈ above L h k m) : boundary v (boundary v c) = 0 := by
  rw [above,Finsupp.supported_eq_span_single] at hc
  apply Submodule.span_induction (p := fun c _ => boundary v (boundary v c) = 0) _ _ _ _ hc
  · rintro _ ⟨⟨g,w⟩,⟨hw,_,_⟩,rfl⟩
    simp only [boundary_single,one_smul]
    exact boundary_boundaryTerm v g w (hw.2.imp (fun {_ _} ha => comm _ _ ha))
  · simp
  · intro c d _ _ hc hd; simp only [map_add,hc,hd,add_zero]
  · intro n c _ hc; simp only [map_smul,hc,smul_zero]

include comm in
theorem push_boundary {k : ℕ} {m : ℤ} {c : Chains G A}
    (hc : c ∈ above L h k m) (hd : boundary v c ∈ above L h (k-1) 0) :
    boundary v (push L K v h c) = boundary v c := by
  rw [push_apply,map_sub,map_sub,homotopy_zero L K h hd,map_zero,
    boundary_squared L v h comm (homotopy_above L K h hc)]
  simp

include K hv comm in
theorem push_into_halfspace {k : ℕ} (hk : 0 < k) (N : ℕ) (c : Chains G A)
    (hc : c ∈ above L h k (-(N : ℤ)))
    (hd : boundary v c ∈ above L h (k-1) 0) :
    ∃ b ∈ above L h k 0, boundary v b = boundary v c := by
  induction N generalizing c with
  | zero => exact ⟨c,by simpa using hc,rfl⟩
  | succ N ih =>
    have hp := push_above L K v h hv hk hc
    have he := push_boundary L K v h comm hc hd
    obtain ⟨b,hb,hdb⟩ := ih (push L K v h c) hp (by rwa [he])
    exact ⟨b,hb,hdb.trans he⟩



/-- All valid cells of degree k, without a height restriction. -/
def total (k : ℕ) : Submodule ℤ (Chains G A) :=
  Finsupp.supported ℤ ℤ {p | SimplicialChains.Valid L p.2 ∧ p.2.length = k}

omit [Group G] in
theorem above_total {k : ℕ} {m : ℤ} {c : Chains G A} (hc : c ∈ above L h k m) :
    c ∈ total (G := G) L k := by
  apply Finsupp.supported_mono _ hc
  intro p hp
  exact ⟨hp.1,hp.2.1⟩

omit [Group G] in
theorem finite_lower_bound {k : ℕ} {c : Chains G A} (hc : c ∈ total (G := G) L k) :
    ∃ N : ℕ, c ∈ above L h k (-(N : ℤ)) := by
  refine ⟨c.support.sup (fun p => (-h p.1).toNat),?_⟩
  apply (Finsupp.mem_supported ℤ c).mpr
  intro p hp
  have ht := (Finsupp.mem_supported ℤ c).mp hc hp
  have hb := Finset.le_sup (f := fun p => (-h p.1).toNat) hp
  have hi := Int.self_le_toNat (-h p.1)
  exact ⟨ht.1,ht.2,by omega⟩

include K hv comm in
theorem halfspace_cycle_bounds
    (exactTotal : ∀ {k : ℕ}, 0 < k → ∀ c, c ∈ total (G := G) L k → boundary v c = 0 →
      ∃ b ∈ total (G := G) L (k+1), boundary v b = c)
    {k : ℕ} (hk : 0 < k) (c : Chains G A) (hc : c ∈ above L h k 0)
    (hz : boundary v c = 0) :
    ∃ b ∈ above L h (k+1) 0, boundary v b = c := by
  obtain ⟨b,hb,hdb⟩ := exactTotal hk c (above_total L h hc) hz
  obtain ⟨N,hN⟩ := finite_lower_bound L h hb
  obtain ⟨b',hb',hdb'⟩ := push_into_halfspace L K v h hv comm (by omega) N b hN
    (by simpa [hdb] using hc)
  exact ⟨b',hb',hdb'.trans hdb⟩

end CubicalChains.HeightFiltration

namespace CubicalChains.Reflection
open Reorientation
variable {G A B : Type*} [Group G]

def relabel (f : A → B) : Chains G A →ₗ[ℤ] Chains G B :=
  Finsupp.lmapDomain ℤ ℤ (fun p => (p.1,p.2.map f))
omit [Group G] in
@[simp] theorem relabel_single (f : A → B) (g : G) (w : List A) (n : ℤ) :
    relabel f (Finsupp.single (g,w) n) = Finsupp.single (g,w.map f) n := by simp [relabel]
omit [Group G] in
theorem relabel_front (f : A → B) (a : A) (c : Chains G A) :
    relabel f (front a c) = front (f a) (relabel f c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add,hc,hd]
  | single p n => rcases p with ⟨g,w⟩; simp

theorem relabel_boundaryTerm (f : A → B) (v : B → G) (g : G) (w : List A) :
    relabel f (boundaryTerm (v ∘ f) g w) = boundaryTerm v g (w.map f) := by
  induction w with
  | nil => simp
  | cons a w ih => simp [relabel_front,ih]

variable (v : A → G)
def letters (w : List A) : List (Signed A) := w.map (fun a => (a,true))
def mirror : Chains G A →ₗ[ℤ] Chains G A :=
  (normalize v).comp (relabel (fun a => (a,true)))

@[simp] theorem mirror_single (g : G) (w : List A) (n : ℤ) :
    mirror v (Finsupp.single (g,w) n) = n • normalTerm v g (letters w) := by
  simp [mirror,letters]

omit [Group G] in
theorem letters_map (w : List A) : (letters w).map Prod.fst = w := by
  simp [letters,List.map_map,Function.comp_def]

omit [Group G] in
theorem letters_sign (w : List A) : sign (letters w) = (-1 : ℤ)^w.length := by
  induction w with
  | nil => rfl
  | cons a w ih => simpa [letters,sign,pow_succ,mul_comm] using congrArg (fun n : ℤ => -n) ih

theorem commute_prod (a : A) (w : List A) (hw : ∀ b ∈ w, Commute (v a) (v b)) :
    Commute (v a) (w.map v).prod := by
  apply Commute.list_prod_right
  intro x hx
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hx
  exact hw b hb

theorem prod_inv (w : List A) (hw : w.Pairwise (fun a b => Commute (v a) (v b))) :
    (w.map (fun a => (v a)⁻¹)).prod = (w.map v).prod⁻¹ := by
  induction w with
  | nil => simp
  | cons a w ih =>
    obtain ⟨ha,hw⟩ := List.pairwise_cons.mp hw
    simp only [List.map_cons,List.prod_cons,ih hw,mul_inv_rev]
    exact (commute_prod v a w ha).inv_left.inv_right.eq

theorem letters_origin (g : G) (w : List A)
    (hw : w.Pairwise (fun a b => Commute (v a) (v b))) :
    origin v g (letters w) = g * (w.map v).prod⁻¹ := by
  induction w generalizing g with
  | nil => simp [letters]
  | cons a w ih =>
    obtain ⟨ha,hw⟩ := List.pairwise_cons.mp hw
    change origin v (g * (v a)⁻¹) (letters w) = g * (v a * (w.map v).prod)⁻¹
    rw [ih _ hw,mul_inv_rev,mul_assoc,(commute_prod v a w ha).inv_left.inv_right.eq]

theorem mirror_single_explicit (g : G) (w : List A) (n : ℤ)
    (hw : w.Pairwise (fun a b => Commute (v a) (v b))) :
    mirror v (Finsupp.single (g,w) n) =
      n • ((-1 : ℤ)^w.length • Finsupp.single (g*(w.map v).prod⁻¹,w) 1) := by
  rw [mirror_single,normalTerm,letters_sign,letters_origin v g w hw,letters_map]

theorem mirror_boundaryTerm (g : G) (w : List A)
    (hw : w.Pairwise (fun a b => Commute (v a) (v b))) :
    mirror v (boundaryTerm (fun a => (v a)⁻¹) g w) =
      boundary v (normalTerm v g (letters w)) := by
  have he : (fun a => (v a)⁻¹) = step v ∘ (fun a => (a,true)) := rfl
  rw [mirror,LinearMap.comp_apply,he,relabel_boundaryTerm]
  apply normalize_boundaryTerm
  simpa only [List.pairwise_map] using hw

theorem mirror_twice_single (g : G) (w : List A)
    (hw : w.Pairwise (fun a b => Commute (v a) (v b))) :
    mirror (fun a => (v a)⁻¹) (mirror v (Finsupp.single (g,w) 1)) = Finsupp.single (g,w) 1 := by
  rw [mirror_single_explicit v g w 1 hw,one_smul,map_smul,
    mirror_single_explicit _ _ w 1 (hw.imp (fun {_ _} hc => hc.inv_left.inv_right)),one_smul,
    prod_inv v w hw,inv_inv,inv_mul_cancel_right,smul_smul,← mul_pow]
  simp

open HeightFiltration
variable [LinearOrder A] (L : SimpleGraph A)
variable (comm : ∀ a b, L.Adj a b → Commute (v a) (v b))

include comm in
theorem mirror_total {k : ℕ} {c : Chains G A} (hc : c ∈ total (G := G) L k) :
    mirror v c ∈ total (G := G) L k := by
  apply supported_map _ _ _ _ hc
  rintro ⟨g,w⟩ ⟨hw,hl⟩
  rw [mirror_single_explicit v g w 1 (hw.2.imp (fun {_ _} ha => comm _ _ ha)),one_smul]
  exact Submodule.smul_mem _ _ (Finsupp.single_mem_supported ℤ 1 ⟨hw,hl⟩)

include comm in
theorem mirror_boundary {k : ℕ} {c : Chains G A} (hc : c ∈ total (G := G) L k) :
    mirror v (boundary (fun a => (v a)⁻¹) c) = boundary v (mirror v c) := by
  rw [total,Finsupp.supported_eq_span_single] at hc
  apply Submodule.span_induction (p := fun c _ =>
    mirror v (boundary (fun a => (v a)⁻¹) c) = boundary v (mirror v c)) _ _ _ _ hc
  · rintro _ ⟨⟨g,w⟩,⟨hw,_⟩,rfl⟩
    simp only [boundary_single,mirror_single,one_smul]
    exact mirror_boundaryTerm v g w (hw.2.imp (fun {_ _} ha => comm _ _ ha))
  · simp
  · intro c d _ _ hc hd; simp only [map_add,hc,hd]
  · intro n c _ hc; simp only [map_smul,hc]

include comm in
theorem mirror_twice {k : ℕ} {c : Chains G A} (hc : c ∈ total (G := G) L k) :
    mirror (fun a => (v a)⁻¹) (mirror v c) = c := by
  rw [total,Finsupp.supported_eq_span_single] at hc
  apply Submodule.span_induction (p := fun c _ =>
    mirror (fun a => (v a)⁻¹) (mirror v c) = c) _ _ _ _ hc
  · rintro _ ⟨⟨g,w⟩,⟨hw,_⟩,rfl⟩
    exact mirror_twice_single v g w (hw.2.imp (fun {_ _} ha => comm _ _ ha))
  · simp
  · intro c d _ _ hc hd; simp only [map_add,hc,hd]
  · intro n c _ hc; simp only [map_smul,hc]

include comm in
theorem inverse_cycle_bounds
    (exactTotal : ∀ {k : ℕ}, 0 < k → ∀ c, c ∈ total (G := G) L k → boundary v c = 0 →
      ∃ b ∈ total (G := G) L (k+1), boundary v b = c)
    {k : ℕ} (hk : 0 < k) (c : Chains G A) (hc : c ∈ total (G := G) L k)
    (hz : boundary (fun a => (v a)⁻¹) c = 0) :
    ∃ b ∈ total (G := G) L (k+1), boundary (fun a => (v a)⁻¹) b = c := by
  have hmi : ∀ a b, L.Adj a b → Commute ((v a)⁻¹) ((v b)⁻¹) :=
    fun a b ha => (comm a b ha).inv_left.inv_right
  have hm := mirror_total v L comm hc
  have hdz : boundary v (mirror v c) = 0 := by rw [← mirror_boundary v L comm hc,hz,map_zero]
  obtain ⟨b,hb,hdb⟩ := exactTotal hk _ hm hdz
  refine ⟨mirror (fun a => (v a)⁻¹) b,mirror_total _ L hmi hb,?_⟩
  have he := mirror_boundary (fun a => (v a)⁻¹) L hmi hb
  simp only [inv_inv] at he
  rw [← he,hdb,mirror_twice v L comm hc]



variable (h : G → ℤ)
variable (hv : ∀ g a, h (g * v a) = h g + 1)

omit [LinearOrder A] in
include hv in
theorem height_inverse_step (g : G) (a : A) : h (g*(v a)⁻¹) = h g-1 := by
  have he := hv (g*(v a)⁻¹) a
  rw [inv_mul_cancel_right] at he
  omega

omit [LinearOrder A] in
include hv in
theorem height_prod (g : G) (w : List A) : h (g*(w.map v).prod) = h g + w.length := by
  induction w generalizing g with
  | nil => simp
  | cons a w ih =>
    simp only [List.map_cons,List.prod_cons,← mul_assoc,ih,hv,List.length_cons,Nat.cast_add,Nat.cast_one]
    omega

omit [LinearOrder A] in
include hv in
theorem height_inv_prod (g : G) (w : List A) : h (g*(w.map v).prod⁻¹) = h g-w.length := by
  have he := height_prod v h hv (g*(w.map v).prod⁻¹) w
  rw [inv_mul_cancel_right] at he
  omega

/-- Cubes lying entirely in the nonpositive halfspace. -/
def below (k : ℕ) : Submodule ℤ (Chains G A) :=
  Finsupp.supported ℤ ℤ {p | SimplicialChains.Valid L p.2 ∧ p.2.length = k ∧ h p.1 + k ≤ 0}

omit [Group G] in
theorem below_total {k : ℕ} {c : Chains G A} (hc : c ∈ below L h k) :
    c ∈ total (G := G) L k := by
  apply Finsupp.supported_mono _ hc
  intro p hp
  exact ⟨hp.1,hp.2.1⟩

include comm hv in
theorem mirror_above_below {k : ℕ} {c : Chains G A}
    (hc : c ∈ above L (fun g => -h g) k 0) : mirror v c ∈ below L h k := by
  apply supported_map _ _ _ _ hc
  rintro ⟨g,w⟩ ⟨hw,hl,hh⟩
  dsimp at hw hl hh
  rw [mirror_single_explicit v g w 1 (hw.2.imp (fun {_ _} ha => comm _ _ ha)),one_smul]
  apply Submodule.smul_mem
  apply Finsupp.single_mem_supported
  refine ⟨hw,hl,?_⟩
  change h (g*(w.map v).prod⁻¹)+(k:ℤ) ≤ 0
  rw [height_inv_prod v h hv,hl]
  omega

include comm hv in
theorem mirror_below_above {k : ℕ} {c : Chains G A} (hc : c ∈ below L h k) :
    mirror (fun a => (v a)⁻¹) c ∈ above L (fun g => -h g) k 0 := by
  apply supported_map _ _ _ _ hc
  rintro ⟨g,w⟩ ⟨hw,hl,hh⟩
  dsimp at hw hl hh
  have hc' := hw.2.imp (fun {_ _} ha => (comm _ _ ha).inv_left.inv_right)
  rw [mirror_single_explicit _ g w 1 hc',one_smul,
    prod_inv v w (hw.2.imp (fun {_ _} ha => comm _ _ ha)),inv_inv]
  apply Submodule.smul_mem
  apply Finsupp.single_mem_supported
  refine ⟨hw,hl,?_⟩
  change 0 ≤ -h (g*(w.map v).prod)
  rw [height_prod v h hv,hl]
  omega

include comm hv in
theorem below_boundary {k : ℕ} {c : Chains G A} (hc : c ∈ below L h k) :
    boundary v c ∈ below L h (k-1) := by
  have hmi : ∀ a b, L.Adj a b → Commute ((v a)⁻¹) ((v b)⁻¹) :=
    fun a b ha => (comm a b ha).inv_left.inv_right
  have hh : ∀ g a, -h (g*(v a)⁻¹) = -h g+1 := by
    intro g a
    rw [height_inverse_step v h hv]
    omega
  have hm := mirror_below_above v L comm h hv hc
  have hd := boundary_above L (fun a => (v a)⁻¹) (fun g => -h g) hh hm
  have he := mirror_above_below v L comm h hv hd
  rw [mirror_boundary v L comm (above_total L (fun g => -h g) hm)] at he
  have hi := mirror_twice (fun a => (v a)⁻¹) L hmi (below_total L h hc)
  simp only [inv_inv] at hi
  rwa [hi] at he

variable (K : SimplicialChains.Contraction L)
include comm hv K in
theorem below_cycle_bounds
    (exactTotal : ∀ {k : ℕ}, 0 < k → ∀ c, c ∈ total (G := G) L k → boundary v c = 0 →
      ∃ b ∈ total (G := G) L (k+1), boundary v b = c)
    {k : ℕ} (hk : 0 < k) (c : Chains G A) (hc : c ∈ below L h k)
    (hz : boundary v c = 0) :
    ∃ b ∈ below L h (k+1), boundary v b = c := by
  have hmi : ∀ a b, L.Adj a b → Commute ((v a)⁻¹) ((v b)⁻¹) :=
    fun a b ha => (comm a b ha).inv_left.inv_right
  have hh : ∀ g a, -h (g*(v a)⁻¹) = -h g+1 := by
    intro g a
    rw [height_inverse_step v h hv]
    omega
  have hm := mirror_below_above v L comm h hv hc
  have hdz : boundary (fun a => (v a)⁻¹) (mirror (fun a => (v a)⁻¹) c) = 0 := by
    have he := mirror_boundary (fun a => (v a)⁻¹) L hmi (below_total L h hc)
    simp only [inv_inv] at he
    rw [← he,hz,map_zero]
  obtain ⟨b,hb,hdb⟩ := halfspace_cycle_bounds L K (fun a => (v a)⁻¹) (fun g => -h g) hh hmi
    (fun hk c hc hz => inverse_cycle_bounds v L comm exactTotal hk c hc hz) hk _ hm hdz
  refine ⟨mirror v b,mirror_above_below v L comm h hv hb,?_⟩
  rw [← mirror_boundary v L comm (above_total L (fun g => -h g) hb),hdb]
  have hi := mirror_twice (fun a => (v a)⁻¹) L hmi (below_total L h hc)
  simpa only [inv_inv] using hi

end CubicalChains.Reflection

namespace CubicalChains.LevelExact
open HeightFiltration Reflection
variable {G A : Type*} [Group G] [LinearOrder A] (L : SimpleGraph A)
variable (v : A → G) (h : G → ℤ)

def select (P : G × List A → Prop) : Chains G A →ₗ[ℤ] Chains G A :=
  Finsupp.linearCombination ℤ (fun p => if P p then Finsupp.single p 1 else 0)
omit [Group G] [LinearOrder A] in
@[simp] theorem select_single (P : G × List A → Prop) (p : G × List A) (n : ℤ) :
    select P (Finsupp.single p n) = if P p then Finsupp.single p n else 0 := by
  simp only [select,Finsupp.linearCombination_single]
  split <;> simp

omit [Group G] [LinearOrder A] in
theorem select_supported (P : G × List A → Prop) {Q : Set (G × List A)}
    {c : Chains G A} (hc : c ∈ Finsupp.supported ℤ ℤ Q) :
    select P c ∈ Finsupp.supported ℤ ℤ {p | p ∈ Q ∧ P p} := by
  apply supported_map _ _ _ _ hc
  intro p hp
  rw [select_single]
  split
  · exact Finsupp.single_mem_supported ℤ 1 ⟨hp,by assumption⟩
  · exact Submodule.zero_mem _

omit [Group G] [LinearOrder A] in
theorem select_eq_self (P : G × List A → Prop) {Q : Set (G × List A)}
    (hQ : ∀ p ∈ Q, P p) {c : Chains G A} (hc : c ∈ Finsupp.supported ℤ ℤ Q) :
    select P c = c := by
  rw [Finsupp.supported_eq_span_single] at hc
  apply Submodule.span_induction (p := fun c _ => select P c = c) _ _ _ _ hc
  · rintro _ ⟨p,hp,rfl⟩; simp [hQ p hp]
  · simp
  · intro c d _ _ hc hd; simp only [map_add,hc,hd]
  · intro n c _ hc; simp only [map_smul,hc]

omit [Group G] [LinearOrder A] in
theorem select_eq_zero (P : G × List A → Prop) {Q : Set (G × List A)}
    (hQ : ∀ p ∈ Q, ¬P p) {c : Chains G A} (hc : c ∈ Finsupp.supported ℤ ℤ Q) :
    select P c = 0 := by
  rw [Finsupp.supported_eq_span_single] at hc
  apply Submodule.span_induction (p := fun c _ => select P c = 0) _ _ _ _ hc
  · rintro _ ⟨p,hp,rfl⟩; simp [hQ p hp]
  · simp
  · intro c d _ _ hc hd; simp only [map_add,hc,hd,add_zero]
  · intro n c _ hc; simp only [map_smul,hc,smul_zero]

def plus : Chains G A →ₗ[ℤ] Chains G A := select (fun p => 0 ≤ h p.1)
def minus : Chains G A →ₗ[ℤ] Chains G A := select (fun p => h p.1+p.2.length ≤ 0)
def crossPart : Chains G A →ₗ[ℤ] Chains G A := select (fun p => h p.1 < 0 ∧ 0 < h p.1+p.2.length)
def crossing (k : ℕ) : Submodule ℤ (Chains G A) :=
  Finsupp.supported ℤ ℤ {p | SimplicialChains.Valid L p.2 ∧ p.2.length = k ∧
    h p.1 < 0 ∧ 0 < h p.1+k}

omit [Group G] in
theorem crossing_total {k : ℕ} {c : Chains G A} (hc : c ∈ crossing L h k) :
    c ∈ total (G := G) L k := by
  apply Finsupp.supported_mono _ hc
  intro p hp
  exact ⟨hp.1,hp.2.1⟩

omit [Group G] in
theorem plus_mem {k : ℕ} {c : Chains G A} (hc : c ∈ total (G := G) L k) :
    plus h c ∈ above L h k 0 := by
  apply Finsupp.supported_mono _ (select_supported (fun p => 0 ≤ h p.1) hc)
  intro p hp
  exact ⟨hp.1.1,hp.1.2,hp.2⟩

omit [Group G] in
theorem minus_mem {k : ℕ} {c : Chains G A} (hc : c ∈ total (G := G) L k) :
    minus h c ∈ below L h k := by
  apply Finsupp.supported_mono _ (select_supported (fun p => h p.1+p.2.length ≤ 0) hc)
  intro p hp
  exact ⟨hp.1.1,hp.1.2,by simpa only [hp.1.2] using hp.2⟩

omit [Group G] in
theorem crossPart_mem {k : ℕ} {c : Chains G A} (hc : c ∈ total (G := G) L k) :
    crossPart h c ∈ crossing L h k := by
  apply Finsupp.supported_mono _
    (select_supported (fun p => h p.1<0 ∧ 0<h p.1+p.2.length) hc)
  intro p hp
  exact ⟨hp.1.1,hp.1.2,hp.2.1,by simpa only [hp.1.2] using hp.2.2⟩

omit [Group G] in
theorem decomposition {k : ℕ} (hk : 0 < k) {c : Chains G A} (hc : c ∈ total (G := G) L k) :
    c = plus h c + minus h c + crossPart h c := by
  rw [total,Finsupp.supported_eq_span_single] at hc
  apply Submodule.span_induction
    (p := fun c _ => c = plus h c + minus h c + crossPart h c) _ _ _ _ hc
  · rintro _ ⟨⟨g,w⟩,⟨_,hl⟩,rfl⟩
    dsimp at hl
    simp only [plus,minus,crossPart,select_single]
    by_cases hg : 0 ≤ h g
    · simp [hg,show ¬h g+(w.length:ℤ) ≤ 0 by omega,not_lt.mpr hg]
    · by_cases hh : h g+(w.length:ℤ) ≤ 0
      · simp [hg,hh,not_lt.mpr hh]
      · simp [hg,hh,not_le.mp hg,not_le.mp hh]
  · simp
  · intro c d _ _ hc hd
    simp only [map_add]
    calc
      c+d = (plus h c + minus h c + crossPart h c) +
          (plus h d + minus h d + crossPart h d) := congrArg₂ (· + ·) hc hd
      _ = _ := by abel
  · intro n c _ hc
    simp only [map_smul]
    simpa only [smul_add] using congrArg (fun z => n • z) hc

omit [Group G] in
theorem plus_self {k : ℕ} {c : Chains G A} (hc : c ∈ above L h k 0) : plus h c = c :=
  select_eq_self _ (fun _ hp => hp.2.2) hc
omit [Group G] in
theorem plus_below_zero {k : ℕ} (hk : 0 < k) {c : Chains G A} (hc : c ∈ below L h k) :
    plus h c = 0 := by
  apply select_eq_zero _ _ hc
  intro p hp
  have hh := hp.2.2
  omega
omit [Group G] in
theorem crossPart_above_zero {k : ℕ} {c : Chains G A} (hc : c ∈ above L h k 0) :
    crossPart h c = 0 := by
  apply select_eq_zero _ _ hc
  intro p hp hh
  exact (not_lt.mpr hp.2.2) hh.1
omit [Group G] in
theorem crossPart_below_zero {k : ℕ} {c : Chains G A} (hc : c ∈ below L h k) :
    crossPart h c = 0 := by
  apply select_eq_zero _ _ hc
  intro p hp hh
  have h₁ := hp.2.1
  have h₂ := hp.2.2
  have h₃ := hh.2
  omega
omit [Group G] in
theorem crossPart_self {k : ℕ} {c : Chains G A} (hc : c ∈ crossing L h k) : crossPart h c = c := by
  apply select_eq_self _ _ hc
  intro p hp
  exact ⟨hp.2.2.1,by simpa only [hp.2.1] using hp.2.2.2⟩

omit [Group G] in
theorem crossing_one_zero {c : Chains G A} (hc : c ∈ crossing L h 1) : c = 0 := by
  apply Finsupp.ext
  intro p
  by_contra hn
  have hp := (Finsupp.mem_supported ℤ c).mp hc (Finsupp.mem_support_iff.mpr hn)
  have h₁ := hp.2.2.1
  have h₂ := hp.2.2.2
  omega

omit [Group G] in
theorem halves_inter_zero {k : ℕ} (hk : 0 < k) {c : Chains G A}
    (hc : c ∈ above L h k 0) (hd : c ∈ below L h k) : c = 0 := by
  apply Finsupp.ext
  intro p
  by_contra hn
  have hp := (Finsupp.mem_supported ℤ c).mp hc (Finsupp.mem_support_iff.mpr hn)
  have hq := (Finsupp.mem_supported ℤ c).mp hd (Finsupp.mem_support_iff.mpr hn)
  have h₁ := hp.2.2
  have h₂ := hq.2.2
  omega



variable (K : SimplicialChains.Contraction L)
variable (hv : ∀ g a, h (g * v a) = h g + 1)
variable (comm : ∀ a b, L.Adj a b → Commute (v a) (v b))
variable (exactTotal : ∀ {k : ℕ}, 0 < k → ∀ c, c ∈ total (G := G) L k → boundary v c = 0 →
      ∃ b ∈ total (G := G) L (k+1), boundary v b = c)

include hv in
theorem boundary_total {k : ℕ} {c : Chains G A} (hc : c ∈ total (G := G) L k) :
    boundary v c ∈ total (G := G) L (k-1) := by
  obtain ⟨N,hN⟩ := finite_lower_bound L h hc
  exact above_total L h (boundary_above L v h hv hN)

include comm in
theorem boundary_squared_total (h : G → ℤ) {k : ℕ} {c : Chains G A} (hc : c ∈ total (G := G) L k) :
    boundary v (boundary v c) = 0 := by
  obtain ⟨N,hN⟩ := finite_lower_bound L h hc
  exact boundary_squared L v h comm hN

/-- The connecting boundary on a crossing square is the difference of its two
height-zero vertices. -/
def levelBoundary : Chains G A →ₗ[ℤ] Chains G A :=
  (boundary v).comp ((plus h).comp (boundary v))
omit [LinearOrder A] in
theorem levelBoundary_apply (c : Chains G A) :
    levelBoundary v h c = boundary v (plus h (boundary v c)) := rfl

include hv comm in
theorem levelBoundary_above {c : Chains G A} (hc : c ∈ above L h 2 0) :
    levelBoundary v h c = 0 := by
  rw [levelBoundary_apply,plus_self L h (boundary_above L v h hv hc)]
  exact boundary_squared L v h comm hc

include hv comm in
theorem levelBoundary_below {c : Chains G A} (hc : c ∈ below L h 2) :
    levelBoundary v h c = 0 := by
  rw [levelBoundary_apply,plus_below_zero L h (by decide) (below_boundary v L comm h hv hc),map_zero]

include hv comm in
theorem levelBoundary_crossPart {c : Chains G A} (hc : c ∈ total (G := G) L 2) :
    levelBoundary v h (crossPart h c) = levelBoundary v h c := by
  have he := congrArg (levelBoundary v h) (decomposition L h (by decide) hc)
  simp only [map_add,levelBoundary_above L v h hv comm (plus_mem L h hc),
    levelBoundary_below L v h hv comm (minus_mem L h hc),zero_add] at he
  exact he.symm

include hv comm in
theorem levelBoundary_cross_boundary {c : Chains G A} (hc : c ∈ crossing L h 3) :
    levelBoundary v h (crossPart h (boundary v c)) = 0 := by
  have ht := crossing_total L h hc
  rw [levelBoundary_crossPart L v h hv comm (boundary_total L v h hv ht),
    levelBoundary_apply,boundary_squared_total L v comm h ht,map_zero,map_zero]

include hv comm K exactTotal in
theorem level_cycle_bounds (c : Chains G A) (hc : c ∈ crossing L h 2)
    (hz : levelBoundary v h c = 0) :
    ∃ t ∈ crossing L h 3, crossPart h (boundary v t) = c := by
  have ht := crossing_total L h hc
  have hd := boundary_total L v h hv ht
  have hp := plus_mem L h hd
  have hm := minus_mem L h hd
  have he : boundary v c = plus h (boundary v c) + minus h (boundary v c) := by
    have hh := decomposition L h (by decide) hd
    rw [crossing_one_zero L h (crossPart_mem L h hd),add_zero] at hh
    exact hh
  have hdp : boundary v (plus h (boundary v c)) = 0 := hz
  have hdm : boundary v (minus h (boundary v c)) = 0 := by
    have hh := congrArg (boundary v) he
    rw [boundary_squared_total L v comm h ht,map_add,hdp,zero_add] at hh
    exact hh.symm
  obtain ⟨a,ha,hda⟩ := halfspace_cycle_bounds L K v h hv comm exactTotal (by decide) _ hp hdp
  obtain ⟨b,hb,hdb⟩ := below_cycle_bounds v L comm h hv K exactTotal (by decide) _ hm hdm
  have hab : c-a-b ∈ total (G := G) L 2 := Submodule.sub_mem _
    (Submodule.sub_mem _ ht (above_total L h ha)) (below_total L h hb)
  have hdz : boundary v (c-a-b) = 0 := by
    simp only [map_sub,hda,hdb]
    exact sub_eq_zero.mpr (sub_eq_iff_eq_add.mpr (he.trans (add_comm _ _)))
  obtain ⟨t,ht',hdt⟩ := exactTotal (by decide) _ hab hdz
  refine ⟨crossPart h t,crossPart_mem L h ht',?_⟩
  have hpdt : crossPart h (boundary v (plus h t)) = 0 :=
    crossPart_above_zero L h (boundary_above L v h hv (plus_mem L h ht'))
  have hmdt : crossPart h (boundary v (minus h t)) = 0 :=
    crossPart_below_zero L h (below_boundary v L comm h hv (minus_mem L h ht'))
  have hh := congrArg (fun z => crossPart h (boundary v z)) (decomposition L h (by decide) ht')
  simp only [map_add,hpdt,hmdt,zero_add] at hh
  rw [← hh,hdt,map_sub,map_sub,crossPart_self L h hc,
    crossPart_above_zero L h ha,crossPart_below_zero L h hb,sub_zero,sub_zero]

variable (dim : ∀ w, SimplicialChains.Valid L w → w.length ≤ 3)
include dim in
omit [Group G] in
theorem total_four_zero {c : Chains G A} (hc : c ∈ total (G := G) L 4) : c = 0 := by
  apply Finsupp.ext
  intro p
  by_contra hn
  have hp := (Finsupp.mem_supported ℤ c).mp hc (Finsupp.mem_support_iff.mpr hn)
  have hh := dim p.2 hp.1
  have hl := hp.2
  omega

include hv comm K exactTotal dim in
theorem level_boundary_injective (t : Chains G A) (ht : t ∈ crossing L h 3)
    (hz : crossPart h (boundary v t) = 0) : t = 0 := by
  have htt := crossing_total L h ht
  have hd := boundary_total L v h hv htt
  have hp := plus_mem L h hd
  have hm := minus_mem L h hd
  have he : boundary v t = plus h (boundary v t) + minus h (boundary v t) := by
    have hh := decomposition L h (by decide) hd
    rwa [hz,add_zero] at hh
  have hh := congrArg (boundary v) he
  rw [boundary_squared_total L v comm h htt,map_add] at hh
  have hdp : boundary v (plus h (boundary v t)) = 0 := by
    apply halves_inter_zero L h (by decide) (boundary_above L v h hv hp)
    have he' : boundary v (plus h (boundary v t)) = -boundary v (minus h (boundary v t)) := by
      exact eq_neg_of_add_eq_zero_left hh.symm
    rw [he']
    exact Submodule.neg_mem _ (below_boundary v L comm h hv hm)
  have hdm : boundary v (minus h (boundary v t)) = 0 := by simpa only [hdp,zero_add] using hh.symm
  obtain ⟨a,ha,hda⟩ := halfspace_cycle_bounds L K v h hv comm exactTotal (by decide) _ hp hdp
  obtain ⟨b,hb,hdb⟩ := below_cycle_bounds v L comm h hv K exactTotal (by decide) _ hm hdm
  have hab : t-a-b ∈ total (G := G) L 3 := Submodule.sub_mem _
    (Submodule.sub_mem _ htt (above_total L h ha)) (below_total L h hb)
  have hdz : boundary v (t-a-b) = 0 := by
    simp only [map_sub,hda,hdb]
    exact sub_eq_zero.mpr (sub_eq_iff_eq_add.mpr (he.trans (add_comm _ _)))
  obtain ⟨q,hq,hdq⟩ := exactTotal (by decide) _ hab hdz
  rw [total_four_zero L dim hq,map_zero] at hdq
  have hc := congrArg (crossPart h) hdq
  simpa only [map_zero,map_sub,crossPart_self L h ht,crossPart_above_zero L h ha,
    crossPart_below_zero L h hb,sub_zero] using hc.symm

end CubicalChains.LevelExact


end

end OAI
end

section
-- module Solutions.OAIEG.PresentationComparison
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe u

open Classical Set Filter Topology MeasureTheory
open scoped Quaternion ContDiff

namespace EilenbergGanea

section QuotientChains
variable {Γ F R S T : Type*} [Group Γ] [Group F]

abbrev BasedChains (Γ S : Type*) := (Γ × S) →₀ ℤ

end QuotientChains
end EilenbergGanea



end

end OAI
end

section
-- module Solutions.OAIEG.LevelBasis
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Filter Topology MeasureTheory
open scoped Quaternion ContDiff

namespace EilenbergGanea.LevelBasis
open CubicalChains CubicalChains.LevelExact CubicalChains.HeightFiltration
variable {G A : Type} [Group G] [LinearOrder A]
variable (L : SimpleGraph A) (φ : G →* Multiplicative ℤ) (v : A → G) (root : A)
def ht (g : G) : ℤ := (φ g).toAdd

end EilenbergGanea.LevelBasis


end

end OAI
end


