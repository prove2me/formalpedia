-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_IsSemiChar
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_IsSemiChar
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:58:30.849801+00:00
-- url     : https://prove2.me/theorems/5a217448-6d9e-47c8-b8b6-a423fea1b82f
-- title:
--   Is Semi Char
-- statement:
--   Definitions and structural lemmas for Is Semi Char, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/IsSemiChar.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_SemiChar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
namespace Formalism.L2.Th1.H
abbrev Sesq (V : Type*) [AddCommGroup V] [Module ℂ V] := V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ
section General
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
def IsHerm (H : Sesq V) : Prop := ∀ x y, H y x = conj (H x y)
def IsPosDef (H : Sesq V) : Prop := ∀ x, x ≠ 0 → 0 < (H x x).re
def altE (H : Sesq V) (x y : V) : ℝ := (H x y).im
def opU (H : Sesq V) (x : V) (F : V → ℂ) (z : V) : ℂ :=
  F (z + x) * Complex.exp (-(Real.pi : ℂ) * H z x - (Real.pi : ℂ) * H x x / 2)
def dualLat (H : Sesq V) (Λ : AddSubgroup V) : AddSubgroup V where
  carrier := {x | ∀ y ∈ Λ, ∃ m : ℤ, altE H x y = (m : ℝ)}
  zero_mem' := fun y _ => ⟨0, by simp [altE]⟩
  add_mem' := by
    intro a b ha hb y hy
    obtain ⟨m, hm⟩ := ha y hy
    obtain ⟨k, hk⟩ := hb y hy
    exact ⟨m + k, by simp only [altE] at hm hk ⊢; simp [hm, hk]⟩
  neg_mem' := by
    intro a ha y hy
    obtain ⟨m, hm⟩ := ha y hy
    exact ⟨-m, by simp only [altE] at hm ⊢; simp [hm]⟩
def IsSelfDual (H : Sesq V) (Λ : AddSubgroup V) : Prop := dualLat H Λ = Λ
def IsSemiChar (H : Sesq V) (Λ : AddSubgroup V) (α : V → ℂ) : Prop :=
  (∀ x ∈ Λ, α x = 1 ∨ α x = -1) ∧
  ∀ x ∈ Λ, ∀ y ∈ Λ, α (x + y) = α x * α y * Complex.exp ((Real.pi : ℂ) * Complex.I * (altE H x y : ℂ))
def fixedBy (H : Sesq V) (α : V → ℂ) (Λ : AddSubgroup V) : Submodule ℂ (V → ℂ) where
  carrier := {F | ∀ x ∈ Λ, ∀ z, α x * opU H x F z = F z}
  zero_mem' := by intro x _ z; simp [opU]
  add_mem' := by
    intro F G hF hG x hx z
    have h1 := hF x hx z
    have h2 := hG x hx z
    simp only [opU, Pi.add_apply] at h1 h2 ⊢
    rw [← h1, ← h2]; ring
  smul_mem' := by
    intro c F hF x hx z
    have h1 := hF x hx z
    simp only [opU, Pi.smul_apply, smul_eq_mul] at h1 ⊢
    rw [← h1]; ring
def sumU (H : Sesq V) (α : V → ℂ) (S : Finset V) (F : V → ℂ) (z : V) : ℂ := ∑ x ∈ S, α x * opU H x F z
def IsReps (Λ₁ Λ₂ : AddSubgroup V) (S : Finset V) : Prop :=
  (∀ x ∈ S, x ∈ Λ₂) ∧ (∀ x ∈ S, ∀ y ∈ S, x - y ∈ Λ₁ → x = y) ∧ ∀ y ∈ Λ₂, ∃ x ∈ S, y - x ∈ Λ₁
def relIdx (Λ₁ Λ₂ : AddSubgroup V) : ℕ := Λ₁.relIndex Λ₂
def inter (H : Sesq V) (α : V → ℂ) (Λ₁ Λ₂ : AddSubgroup V) (F : V → ℂ) (z : V) : ℂ :=
  ((Real.sqrt (relIdx Λ₁ Λ₂) : ℝ) : ℂ)⁻¹ *
    ∑ᶠ c : Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂, α ((Quotient.out c : Λ₂) : V) * opU H ((Quotient.out c : Λ₂) : V) F z
def pullInv (δ : V ≃ₗ[ℂ] V) (F : V → ℂ) (z : V) : ℂ := F (δ.symm z)
def IsIsom {W : Type*} [AddCommGroup W] [Module ℂ W] (H : Sesq V) (H' : Sesq W) (g : V →ₗ[ℂ] W) : Prop :=
  ∀ x y, H' (g x) (g y) = H x y
def imgLat {W : Type*} [AddCommGroup W] [Module ℂ W] (g : V →ₗ[ℂ] W) (Λ : AddSubgroup V) : AddSubgroup W :=
  Λ.map g.toAddMonoidHom
end General
section Analytic
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
def Th (H : Sesq V) (α : V → ℂ) (Λ : AddSubgroup V) : Submodule ℂ (V → ℂ) where
  carrier := {F | AnalyticOnNhd ℂ F Set.univ ∧ F ∈ fixedBy H α Λ}
  zero_mem' := ⟨fun _ _ => analyticAt_const, (fixedBy H α Λ).zero_mem⟩
  add_mem' := fun hF hG => ⟨hF.1.add hG.1, (fixedBy H α Λ).add_mem hF.2 hG.2⟩
  smul_mem' := fun c _ hF => ⟨fun z hz => analyticAt_const.smul (hF.1 z hz), (fixedBy H α Λ).smul_mem c hF.2⟩
def IsLat (Λ : AddSubgroup V) : Prop :=
  DiscreteTopology Λ ∧ Submodule.span ℝ (Λ : Set V) = ⊤
end Analytic
section Coordinates
variable {n : Type*} [Fintype n]
def matH (h : Matrix n n ℂ) : Sesq (n → ℂ) :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun z w => ∑ i, ∑ j, z i * h i j * conj (w j))
    (by intro a b c; simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib])
    (by intro c a b; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc])
    (by intro a b c; simp only [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib])
    (by
      intro c a b
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring)
def stdH (L : PeriodPair) (n : Type*) [Fintype n] [DecidableEq n] : Sesq (n → ℂ) :=
  matH (((Formalism.L2.Th1.F.area L : ℝ) : ℂ)⁻¹ • (1 : Matrix n n ℂ))
def stdLat (L : PeriodPair) (n : Type*) : AddSubgroup (n → ℂ) :=
  AddSubgroup.pi Set.univ fun _ => L.lattice.toAddSubgroup
def prodFn (f : n → ℂ → ℂ) (z : n → ℂ) : ℂ := ∏ i, f i (z i)
def slice (a : Fin 4) (z : Fin 4 × n → ℂ) : n → ℂ := fun i => z (a, i)
def tens4 (θ : (n → ℂ) → ℂ) (z : Fin 4 × n → ℂ) : ℂ := ∏ a : Fin 4, θ (slice a z)
def blk4 (h : Matrix n n ℂ) : Matrix (Fin 4 × n) (Fin 4 × n) ℂ :=
  fun w w' => if w.1 = w'.1 then h w.2 w'.2 else 0
def pow4 (Λ : AddSubgroup (n → ℂ)) : AddSubgroup (Fin 4 × n → ℂ) where
  carrier := {z | ∀ a, slice a z ∈ Λ}
  zero_mem' := fun _ => Λ.zero_mem
  add_mem' := fun hx hy a => Λ.add_mem (hx a) (hy a)
  neg_mem' := fun hx a => Λ.neg_mem (hx a)
end Coordinates
end Formalism.L2.Th1.H


