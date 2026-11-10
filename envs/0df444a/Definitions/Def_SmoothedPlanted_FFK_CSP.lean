-- Prove2me | Definitions.Def_SmoothedPlanted_FFK_CSP
-- name    : SmoothedPlanted_FFK_CSP
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T22:31:50.510403+00:00
-- url     : https://prove2.me/theorems/af4e87bc-c4d6-4a1f-80f4-fb3635ecaab6
-- title:
--   Pairwise constraint satisfaction instances and symmetric relations
-- statement:
--   A pairwise constraint satisfaction instance assigns one symmetric Boolean relation on an alphabet of size $q$ to each unordered pair of variables. A pair is represented by its increasing ordering. The relation lookup permits either orientation and returns the unrestricted relation on the unused diagonal. Restriction to a set of variables keeps exactly the corresponding labels. This is a general CSP object, before specifying any planted set or probability distribution. Relation-valued labels cover an arbitrary source label space by identifying labels with the same relation; the induced distributions are pushforwards. The relation space has the discrete sigma algebra.
-- source:
--   Kothari, Louis, Paul and Raghavendra, Recovering Planted Subgraphs in Smoothed Models, November 3, 2026, Pairwise constraint satisfaction instances and symmetric relations, printed p. 15 (PDF p. 17), PDF SHA256 0f9dc5d96e197a1868bf10cade60fcb647db289ebc51985e4d167c942c54f82b

import Mathlib

open scoped BigOperators
open MeasureTheory ProbabilityTheory

noncomputable section

namespace SmoothedPlanted.FFK

/-- One representative of each unordered pair. -/
abbrev Pair (V : Type) [LinearOrder V] := {p : V × V // p.1 < p.2}
/-- A symmetric Boolean constraint relation on the alphabet. -/
abbrev Relation (q : ℕ) := {r : Fin q → Fin q → Bool // ∀ a b, r a b = r b a}
instance (q : ℕ) : Fintype (Relation q) := Fintype.ofFinite _
instance (q : ℕ) : MeasurableSpace (Relation q) := ⊤
instance (q : ℕ) : MeasurableSingletonClass (Relation q) := ⟨fun _ => trivial⟩
/-- General pairwise CSP, before introducing a planted model. -/
abbrev CSP (V : Type) [LinearOrder V] (q : ℕ) := Pair V → Relation q
/-- Relation lookup in either orientation; the unused diagonal is unrestricted. -/
def allows {V : Type} [LinearOrder V] {q : ℕ} (Y : CSP V q)
    (i j : V) (a b : Fin q) : Bool :=
  if h : i < j then (Y ⟨(i,j), h⟩).val a b
  else if h : j < i then (Y ⟨(j,i), h⟩).val b a else true
/-- Restrict the instance to a finite set of variables. -/
def restrictCSP {V : Type} [LinearOrder V] {q : ℕ} (Y : CSP V q) (T : Finset V) :
    CSP T q := fun e => Y ⟨(e.val.1.val, e.val.2.val), e.property⟩

end SmoothedPlanted.FFK


