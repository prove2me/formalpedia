-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemOfMemSupportToFinsupp
-- name    : GroundTheory_AutomorphicForms_HarishChandraCentre_MemOfMemSupportToFinsupp
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:01:53.534883+00:00
-- url     : https://prove2.me/theorems/64848fa8-86c6-482b-852d-cf11f4905dd3
-- title:
--   Mem Of Mem Support To Finsupp
-- statement:
--   Definitions and structural lemmas for Mem Of Mem Support To Finsupp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemOfMemSupportToFinsupp.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Automorphic.HarishChandra
attribute [local instance 100] LieRing.ofAssociativeRing
variable {n : ℕ}
def Closed (P : Fin n × Fin n → Prop) : Prop := ∀ a b, P a → P b → a.2 = b.1 → P (a.1, b.2)
def IsLower (a : Fin n × Fin n) : Prop := a.2 < a.1
def IsDiag (a : Fin n × Fin n) : Prop := a.1 = a.2
def IsUpper (a : Fin n × Fin n) : Prop := a.1 < a.2
def wordSpan (P : Fin n × Fin n → Prop) (k : ℕ) : Submodule ℂ (U n) :=
  Submodule.span ℂ {u | ∃ w : List (Fin n × Fin n), (∀ a ∈ w, P a) ∧ w.length = k ∧ word w = u}
def letters (n : ℕ) : List (Fin n × Fin n) :=
  let all := (List.finRange n).flatMap fun i => (List.finRange n).map fun j => (i, j)
  all.filter (fun a => decide (a.2 < a.1)) ++ all.filter (fun a => decide (a.1 = a.2)) ++
    all.filter (fun a => decide (a.1 < a.2))
def expand (m : Fin n × Fin n →₀ ℕ) : List (Fin n × Fin n) :=
  (letters n).flatMap fun a => List.replicate (m a) a
noncomputable def canon (m : Fin n × Fin n →₀ ℕ) : U n := word (expand m)
def canonSpan (P : Fin n × Fin n → Prop) (lo hi : ℕ) : Submodule ℂ (U n) :=
  Submodule.span ℂ {u | ∃ m : Fin n × Fin n →₀ ℕ, (∀ a ∈ m.support, P a) ∧ lo ≤ m.degree ∧
    m.degree ≤ hi ∧ canon m = u}
def filt (d : ℕ) : Submodule ℂ (U n) :=
  Submodule.span ℂ {u | ∃ w : List (Fin n × Fin n), w.length ≤ d ∧ word w = u}
def rootAt (a : Fin n × Fin n) (k : Fin n) : ℤ :=
  (if k = a.1 then 1 else 0) - (if k = a.2 then 1 else 0)
def wt (m : Fin n × Fin n →₀ ℕ) (k : Fin n) : ℤ := m.sum fun a c => (c : ℤ) * rootAt a k
end GroundTheory.Automorphic.HarishChandra


