-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Definitions_CommutativeAlgebra_IsTight
-- name    : Development_AutomorphicSpectrum_Definitions_CommutativeAlgebra_IsTight
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:34:43.411969+00:00
-- url     : https://prove2.me/theorems/fe60c0bf-526c-4dc1-8593-59f2b31772a6
-- title:
--   Is Tight
-- statement:
--   Definitions and structural lemmas for Is Tight, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/CommutativeAlgebra/IsTight.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_CotangentSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.GR
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up
variable {C : Type} [Field C] (R : Type) [CommRing R] [Algebra R C]
def pInt (p : ℕ) : Submodule R C := Submodule.span R {(p : C)}
def pFun (p : ℕ) (N : Type) : Submodule R (N → C) :=
  Submodule.pi Set.univ fun _ => pInt R p
def addFun (p : ℕ) (N : Type) [AddCommGroup N] : Submodule R (N → C) where
  carrier := {f | ∀ x y, f (x + y) - f x - f y ∈ pInt (C := C) R p}
  add_mem' := by
    intro f g hf hg x y
    have h := Submodule.add_mem _ (hf x y) (hg x y)
    convert h using 1
    simp only [Pi.add_apply]; ring
  zero_mem' := by intro x y; simp
  smul_mem' := by
    intro c f hf x y
    have h := Submodule.smul_mem _ c (hf x y)
    convert h using 1
    simp only [Pi.smul_apply, smul_sub]
def linFun (p : ℕ) (N : Type) [AddCommGroup N] : Submodule R (N → C) :=
  intFun R N ⊓ addFun R p N
variable {R}
def afFun (p : ℕ) {N : Type} [AddCommGroup N] (M : Submodule R (N → C)) : Submodule R (N → C) :=
  M ⊓ addFun R p N
abbrev AFQuot (p : ℕ) {N : Type} [AddCommGroup N] (M : Submodule R (N → C)) :=
  linFun (C := C) R p N ⧸ (afFun p M ⊔ pFun R p N).comap (linFun (C := C) R p N).subtype
def invFun {N : Type} [AddCommGroup N] (M : Submodule R (N → C)) (K : AddSubgroup N) :
    Submodule R (N → C) where
  carrier := {g | g ∈ M ∧ ∀ x, ∀ k ∈ K, g (x + k) = g x}
  add_mem' := by
    intro f g hf hg
    exact ⟨M.add_mem hf.1 hg.1, fun x k hk => by simp [hf.2 x k hk, hg.2 x k hk]⟩
  zero_mem' := ⟨M.zero_mem, fun _ _ _ => rfl⟩
  smul_mem' := by
    intro c f hf
    exact ⟨M.smul_mem c hf.1, fun x k hk => by simp [hf.2 x k hk]⟩
def GenAF (p : ℕ) {N : Type} [AddCommGroup N] (M : Submodule R (N → C)) (K : AddSubgroup N) : Prop :=
  invFun M K ≤ Subalgebra.toSubmodule (Algebra.adjoin R ((afFun p (invFun M K) : Submodule R (N → C)) : Set (N → C)))
def afLat (p : ℕ) {ι : Type} [Fintype ι] (M : Submodule R ((ι → ZMod p) → C)) : Submodule R (ι → R) where
  carrier := {l | ∃ g ∈ M, ∀ x, g x - algebraMap R C (∑ i, l i * ((x i).val : R)) ∈ pInt (C := C) R p}
  add_mem' := by
    rintro l l' ⟨g, hg, h⟩ ⟨g', hg', h'⟩
    refine ⟨g + g', M.add_mem hg hg', fun x => ?_⟩
    convert Submodule.add_mem _ (h x) (h' x) using 1
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, map_add]; ring
  zero_mem' := ⟨0, M.zero_mem, fun x => by simp⟩
  smul_mem' := by
    rintro c l ⟨g, hg, h⟩
    refine ⟨c • g, M.smul_mem c hg, fun x => ?_⟩
    convert Submodule.smul_mem _ c (h x) using 1
    simp only [Pi.smul_apply, smul_eq_mul, smul_sub, mul_assoc, ← Finset.mul_sum, map_mul,
      Algebra.smul_def]
    ring
def IsTight (v : Valuation C NNReal) (p : ℕ) {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
    (M : Submodule R (N → C)) : Prop :=
  ∃ cA cN cO : NNReal, HasLen v R (AFQuot p M) cA ∧ HasColen R v M cN ∧ HasLen v R (OmAA M) cO ∧
    cA ^ (Fintype.card N * (p - 1)) = cN ^ 2 ∧ cO ^ Fintype.card N = cN ^ 2
end GlobalTheory.CompanionTheory.Ar.GR


