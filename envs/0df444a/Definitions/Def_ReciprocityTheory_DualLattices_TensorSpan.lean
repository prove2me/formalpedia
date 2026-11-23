-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_TensorSpan
-- name    : ReciprocityTheory_DualLattices_TensorSpan
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:37:32.805838+00:00
-- url     : https://prove2.me/theorems/63be005a-5f2f-4aa8-a43e-f23e04d4eaeb
-- title:
--   Tensor Span
-- statement:
--   Definitions and structural lemmas for Tensor Span, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/TensorSpan.lean

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
namespace ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] (R : Type) [CommRing R] [Algebra R C]
def intFun (X : Type) : Submodule R (X → C) where
  carrier := {f | ∀ x, ∃ r : R, algebraMap R C r = f x}
  add_mem' := by
    rintro f g hf hg x
    obtain ⟨r, hr⟩ := hf x
    obtain ⟨s, hs⟩ := hg x
    exact ⟨r + s, by simp [hr, hs]⟩
  zero_mem' := fun _ => ⟨0, by simp⟩
  smul_mem' := by
    rintro c f hf x
    obtain ⟨r, hr⟩ := hf x
    exact ⟨c * r, by simp [hr, Algebra.smul_def]⟩
def tensorSpan {X : Type} (M : Submodule R (X → C)) : Submodule R (X × X → C) :=
  Submodule.span R {F | ∃ g ∈ M, ∃ h ∈ M, F = fun p => g p.1 * h p.2}
def IsLat {X : Type} [Fintype X] [DecidableEq X] (M : Submodule R (X → C)) : Prop :=
  ∃ B : Matrix X X C, IsUnit B.det ∧ M = Submodule.span R (Set.range fun j x => B x j)
def HasColen (v : Valuation C NNReal) {X : Type} [Fintype X] [DecidableEq X]
    (M : Submodule R (X → C)) (c : NNReal) : Prop :=
  ∃ B : Matrix X X C, M = Submodule.span R (Set.range fun j x => B x j) ∧ v B.det = c
def addPull (N : Type) [AddCommGroup N] : (N → C) →ₗ[R] (N × N → C) :=
  LinearMap.funLeft R C (fun p : N × N => p.1 + p.2)
structure HopfOrder (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] where
  carrier : Submodule R (N → C)
  lat : IsLat R carrier
  le_int : carrier ≤ intFun R N
  one_mem : (1 : N → C) ∈ carrier
  mul_mem : ∀ f g, f ∈ carrier → g ∈ carrier → f * g ∈ carrier
  comul : ∀ f ∈ carrier, addPull R N f ∈ tensorSpan R carrier
  antipode : ∀ f ∈ carrier, (fun x => f (-x)) ∈ carrier
variable {R}
def dualLat {X : Type} [Fintype X] (M : Submodule R (X → C)) : Submodule R (X → C) where
  carrier := {u | ∀ f ∈ M, ∃ r : R, algebraMap R C r = ∑ a, u a * f a}
  add_mem' := by
    rintro u w hu hw f hf
    obtain ⟨r, hr⟩ := hu f hf
    obtain ⟨s, hs⟩ := hw f hf
    exact ⟨r + s, by simp [hr, hs, add_mul, Finset.sum_add_distrib]⟩
  zero_mem' := fun _ _ => ⟨0, by simp⟩
  smul_mem' := by
    rintro c u hu f hf
    obtain ⟨r, hr⟩ := hu f hf
    refine ⟨c * r, ?_⟩
    simp only [map_mul, hr, Pi.smul_apply, Algebra.smul_def, Finset.mul_sum, mul_assoc]
def fourier {N H : Type} [Fintype N] (e : H → N → C) :
    (N → C) →ₗ[R] (H → C) where
  toFun u h := ∑ a, u a * e h a
  map_add' u w := by ext h; simp [add_mul, Finset.sum_add_distrib]
  map_smul' c u := by ext h; simp [Algebra.smul_def, Finset.mul_sum, mul_assoc]
def augIdeal {X : Type} [AddCommGroup X] (M : Submodule R (X → C)) : Submodule R (X → C) :=
  M ⊓ LinearMap.ker (LinearMap.proj (R := R) (φ := fun _ : X => C) 0)
def resK {N : Type} [AddCommGroup N] (K : AddSubgroup N) : (N → C) →ₗ[R] (K → C) :=
  LinearMap.funLeft R C (fun k : K => (k : N))
def pullQ {N : Type} [AddCommGroup N] (K : AddSubgroup N) : (N ⧸ K → C) →ₗ[R] (N → C) :=
  LinearMap.funLeft R C (QuotientAddGroup.mk : N → N ⧸ K)
def extK {N : Type} [AddCommGroup N] (K : AddSubgroup N) [DecidablePred (· ∈ K)] :
    (K → C) →ₗ[R] (N → C) where
  toFun u a := if h : a ∈ K then u ⟨a, h⟩ else 0
  map_add' u w := by ext a; by_cases h : a ∈ K <;> simp [h]
  map_smul' c u := by ext a; by_cases h : a ∈ K <;> simp [h]
def pushQ {N : Type} [AddCommGroup N] [Fintype N] (K : AddSubgroup N)
    [DecidableEq (N ⧸ K)] : (N → C) →ₗ[R] (N ⧸ K → C) where
  toFun u c := ∑ a ∈ Finset.univ.filter (fun a : N => (a : N ⧸ K) = c), u a
  map_add' u w := by ext c; simp [Finset.sum_add_distrib]
  map_smul' c u := by ext d; simp [Finset.smul_sum]
end ReciprocityTheory.PGsh.L2


