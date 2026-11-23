-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_ZelevinskyJacquet_ZelevinskyInterleaving_Interleave
-- name    : Development_WeilBound_CoreStatements_TemperedRepresentationTheory_ZelevinskyJacquet_ZelevinskyInterleaving_Interleave
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:39:23.314639+00:00
-- url     : https://prove2.me/theorems/970f0d37-4916-4a61-88d6-ae817a221c5d
-- title:
--   Interleave
-- statement:
--   Definitions and structural lemmas for Interleave, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/TemperedRepresentationTheory/ZelevinskyJacquet/ZelevinskyInterleaving/Interleave.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Zc.Comb
universe u
structure ASeg (T : Type u) where
  start : T
  len : ℕ
  len_pos : 0 < len
variable {T : Type u}
def ASeg.carrier (s : T → T) (Δ : ASeg T) : Set T := {t | ∃ i < Δ.len, s^[i] Δ.start = t}
def ASeg.dec (s : T → T) (Δ : ASeg T) : List T := (List.range Δ.len).reverse.map fun i => s^[i] Δ.start
def ALinked (s : T → T) (Δ Δ' : ASeg T) : Prop :=
  (∃ Γ : ASeg T, Γ.carrier s = Δ.carrier s ∪ Δ'.carrier s) ∧ ¬ Δ.carrier s ⊆ Δ'.carrier s ∧
    ¬ Δ'.carrier s ⊆ Δ.carrier s
def APrecedes (s : T → T) (Δ Δ' : ASeg T) : Prop :=
  ALinked s Δ Δ' ∧ ∃ j : ℕ, 0 < j ∧ Δ'.start = s^[j] Δ.start
def AOrdered (s : T → T) (L : List (ASeg T)) : Prop := L.Pairwise fun a b => ¬ APrecedes s a b
def wt (s : T → T) (L : List (ASeg T)) : List T := (L.reverse.map (ASeg.dec s)).flatten
inductive Interleave : List T → List T → List T → Prop
  | nil : Interleave [] [] []
  | left {a : T} {u v w : List T} : Interleave u v w → Interleave (a :: u) v (a :: w)
  | right {a : T} {u v w : List T} : Interleave u v w → Interleave u (a :: v) (a :: w)
inductive Shuffle : List (List T) → List T → Prop
  | nil : Shuffle [] []
  | cons {u : List T} {us : List (List T)} {v w : List T} : Shuffle us v → Interleave u v w → Shuffle (u :: us) w
def InSh (s : T → T) (m : Multiset (ASeg T)) (w : List T) : Prop :=
  ∃ L : List (ASeg T), (L : Multiset (ASeg T)) = m ∧ Shuffle (L.map (ASeg.dec s)) w
def sqLen (m : Multiset (ASeg T)) : ℕ := (m.map fun Δ => Δ.len ^ 2).sum
end Zc.Comb


