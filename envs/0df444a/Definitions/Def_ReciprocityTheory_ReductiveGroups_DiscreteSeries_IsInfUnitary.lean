-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:25:54.958576+00:00
-- url     : https://prove2.me/theorems/42824e41-76d3-4c63-896e-f86f3b6d776b
-- title:
--   Is Inf Unitary
-- statement:
--   Definitions and structural lemmas for Is Inf Unitary, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/IsInfUnitary.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
namespace ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
section Alg
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
def IsGlRep (E : Fin n → Fin n → Module.End ℂ M) : Prop :=
  ∀ a b c d : Fin n, E a b * E c d - E c d * E a b =
    (if b = c then E a d else 0) - (if d = a then E c b else 0)
def casimir (E : Fin n → Fin n → Module.End ℂ M) : Module.End ℂ M :=
  ∑ a, ∑ b, E a b * E b a
def casimirK (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) : Module.End ℂ M :=
  ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a), E a b * E b a
def IsHWVec (E : Fin n → Fin n → Module.End ℂ M) (μ : Fin n → ℝ) (v : M) : Prop :=
  (∀ a, E a a v = (μ a : ℂ) • v) ∧ ∀ a b, a < b → E a b v = 0
def IsKHWVec (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (μ : Fin n → ℝ) (v : M) : Prop :=
  (∀ a, E a a v = (μ a : ℂ) • v) ∧ ∀ a b, a < b → ε a = ε b → E a b v = 0
end Alg
section Unitary
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]
def adjSign (ε : Fin n → Bool) (a b : Fin n) : ℂ := if ε a = ε b then 1 else -1
def IsInfUnitary (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) : Prop :=
  ∀ (a b : Fin n) (x y : M), inner ℂ (E a b x) y = adjSign ε a b * inner ℂ x (E b a y)
end Unitary
section Weights
def dot (u v : Fin n → ℝ) : ℝ := ∑ a, u a * v a
def nsq (u : Fin n → ℝ) : ℝ := dot u u
def root (a b : Fin n) : Fin n → ℝ := Pi.single a 1 - Pi.single b 1
def rho (n : ℕ) : Fin n → ℝ := fun a => ((n : ℝ) - 1) / 2 - (a : ℕ)
def rhoC (ε : Fin n → Bool) : Fin n → ℝ := fun a =>
  (((univ.filter fun b => a < b ∧ ε b = ε a).card : ℝ) -
    ((univ.filter fun b => b < a ∧ ε b = ε a).card : ℝ)) / 2
def rhoN (ε : Fin n → Bool) : Fin n → ℝ := fun a =>
  (((univ.filter fun b => a < b ∧ ε b ≠ ε a).card : ℝ) -
    ((univ.filter fun b => b < a ∧ ε b ≠ ε a).card : ℝ)) / 2
def lowK (ε : Fin n → Bool) (lam : Fin n → ℝ) : Fin n → ℝ := lam + rhoN ε - rhoC ε
def casVal (lam : Fin n → ℝ) : ℝ := nsq lam - nsq (rho n)
end Weights
section KTypes
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
def IsKStableSub (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (S : Submodule ℂ M) : Prop :=
  ∀ a b, ε a = ε b → ∀ v ∈ S, E a b v ∈ S
def IsKIrrHW (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (Λ : Fin n → ℝ)
    (S : Submodule ℂ M) : Prop :=
  FiniteDimensional ℂ S ∧ IsKStableSub ε E S ∧
    (∀ S' : Submodule ℂ M, S' ≤ S → IsKStableSub ε E S' → S' = ⊥ ∨ S' = S) ∧
    ∃ w ∈ S, w ≠ 0 ∧ IsKHWVec ε E Λ w
def genSub (E : Fin n → Fin n → Module.End ℂ M) (S : Submodule ℂ M) : Submodule ℂ M :=
  sInf {T | S ≤ T ∧ ∀ a b, ∀ v ∈ T, E a b v ∈ T}
end KTypes
section Gap
def pOf (ε : Fin n → Bool) : ℕ := (univ.filter fun a => ε a = true).card
def qOf (ε : Fin n → Bool) : ℕ := (univ.filter fun a => ε a = false).card
def GapAtLeast (ε : Fin n → Bool) (lam : Fin n → ℝ) (h : ℝ) : Prop :=
  ∀ a b : Fin n, ε a ≠ ε b → h ≤ |lam a - lam b|
def StdGap (ε : Fin n → Bool) (lam : Fin n → ℝ) : Prop :=
  StrictAnti lam ∧ ∃ h : ℝ, GapAtLeast ε lam h ∧ (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h
end Gap
end ReciprocityTheory.ChartRestriction.DS


