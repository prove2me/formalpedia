-- Prove2me | Definitions.Def_MondererShapley_Solution
-- name    : MondererShapley_Solution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T08:47:27.774869+00:00
-- url     : https://prove2.me/theorems/8802898a-e900-4c06-a4f3-6b55dd7e835e
-- title:
--   Solution
-- statement:
--   Definitions and structural lemmas for Solution, from Arthur Freitas Ramos, David Barros Hulak, and Ruy Jose Guerra Barretto de Queiroz (Arthur742Ramos/monderer-shapley-potential-lean; see pinned Apache-2.0 LICENSE)'s pinned Monderer-Shapley exact potential games characterization development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Arthur742Ramos/monderer-shapley-potential-lean/blob/bce2e989bc8243f938a34ac0f027b57063c71380/Solution.lean

module
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Finset.Max
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Potential
abbrev Profile {I : Type*} (A : I → Type*) := ∀ i, A i
abbrev Payoff {I : Type*} (A : I → Type*) := I → Profile A → ℝ
def ExactPotential {I : Type*} {A : I → Type*} [DecidableEq I]
    (u : Payoff A) (P : Profile A → ℝ) : Prop :=
  ∀ s i a, P (Function.update s i a) - P s =
    u i (Function.update s i a) - u i s
def FourCycle {I : Type*} {A : I → Type*} [DecidableEq I]
    (u : Payoff A) : Prop :=
  ∀ (s : Profile A) (i j : I), i ≠ j → ∀ (a : A i) (b : A j),
    u i (Function.update s i a) - u i s +
    u j (Function.update (Function.update s i a) j b) - u j (Function.update s i a) +
    u i (Function.update s j b) - u i (Function.update (Function.update s i a) j b) +
    u j s - u j (Function.update s j b) = 0
abbrev Move {I : Type*} (A : I → Type*) := Σ i, A i
def endpoint {I : Type*} {A : I → Type*} [DecidableEq I]
    (s : Profile A) (ms : List (Move A)) : Profile A :=
  ms.foldl (fun s m => Function.update s m.1 m.2) s
def pathIntegral {I : Type*} {A : I → Type*} [DecidableEq I]
    (u : Payoff A) (s : Profile A) (ms : List (Move A)) : ℝ :=
  (ms.foldl (fun p m => (p.1 + u m.1 (Function.update p.2 m.1 m.2) - u m.1 p.2,
    Function.update p.2 m.1 m.2)) (0, s)).1
def ClosedPathProperty {I : Type*} {A : I → Type*} [DecidableEq I]
    (u : Payoff A) : Prop :=
  ∀ s ms, endpoint s ms = s → pathIntegral u s ms = 0
def PureNash {I : Type*} {A : I → Type*} [DecidableEq I]
    (u : Payoff A) (s : Profile A) : Prop :=
  ∀ i a, u i (Function.update s i a) ≤ u i s
end Potential
namespace Potential
def maskedProfile {I : Type*} {A : I → Type*} [DecidableEq I]
    (base : Profile A) (S : Finset I) (s : Profile A) : Profile A :=
  fun i => if i ∈ S then s i else base i
end Potential
namespace Potential
variable {I : Type*} {A : I → Type*} [DecidableEq I]
def ActualPath (s : Profile A) : List (Move A) → Prop
  | [] => True
  | m :: ms => m.2 ≠ s m.1 ∧ ActualPath (Function.update s m.1 m.2) ms
def ActualClosedPathProperty (u : Payoff A) : Prop :=
  ∀ s ms, ActualPath s ms → endpoint s ms = s → pathIntegral u s ms = 0
end Potential
namespace Potential
variable {I : Type*} {A : I → Type*} [DecidableEq I]
def vertices (s : Profile A) (ms : List (Move A)) : List (Profile A) :=
  (ms.foldl (fun p m => (Function.update p.1 m.1 m.2, p.2 ++ [Function.update p.1 m.1 m.2])) (s, [s])).2
def SimpleClosedPathProperty (u : Payoff A) : Prop :=
  ∀ s ms, endpoint s ms = s → (vertices s ms).dropLast.Nodup →
    pathIntegral u s ms = 0
def SimpleFourCycleProperty (u : Payoff A) : Prop :=
  ∀ s ms, endpoint s ms = s → (vertices s ms).dropLast.Nodup → ms.length = 4 →
    pathIntegral u s ms = 0
end Potential
namespace Potential
variable {I : Type*} {A : I → Type*} [Fintype I] [DecidableEq I]
  [∀ i, Nonempty (A i)]
end Potential


