-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitDetRoot
-- name    : Formalism_PeriodIntegrals_UnitDetRoot
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T21:10:21.489875+00:00
-- url     : https://prove2.me/theorems/d55b9113-9aae-4466-ad0e-6642a4321ea4
-- title:
--   Unit Det Root
-- statement:
--   Definitions and structural lemmas for Unit Det Root, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitDetRoot.lean

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
open scoped BigOperators ComplexConjugate
namespace PI
def UnitDetRootDefs.cmTheta (b : ℤ) (d : ℕ) : ℂ := ((b : ℂ) + Complex.I * ((Real.sqrt d : ℝ) : ℂ)) / 2
def UnitDetRootDefs.cmPair (a : ℕ) (b : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) : PeriodPair where
  ω₁ := (a : ℂ)
  ω₂ := UnitDetRootDefs.cmTheta b d
  indep := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
    have him := congrArg Complex.im h
    have hre := congrArg Complex.re h
    simp [UnitDetRootDefs.cmTheta] at him hre
    have ht : t = 0 := by
      rcases him with h1 | h1
      · exact h1
      · exact absurd h1 (by positivity)
    subst ht
    simp at hre
    refine ⟨?_, rfl⟩
    rcases hre with h1 | h1
    · exact h1
    · exact absurd h1 (by positivity)
def UnitDetRootDefs.scalePair (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) : PeriodPair where
  ω₁ := c * L.ω₁
  ω₂ := c * L.ω₂
  indep := by
    have h := L.indep
    rw [LinearIndependent.pair_iff] at h ⊢
    intro s t hst
    apply h s t
    have : c * (s • L.ω₁ + t • L.ω₂) = 0 := by
      rw [← hst]; simp only [Complex.real_smul]; ring
    exact (mul_eq_zero.mp this).resolve_left hc
def UnitDetRootDefs.area (L : PeriodPair) : ℝ := |(conj L.ω₁ * L.ω₂).im|
section General
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
abbrev UnitDetRootDefs.Sesq (V : Type*) [AddCommGroup V] [Module ℂ V] := V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ
def UnitDetRootDefs.altE (H : UnitDetRootDefs.Sesq V) (x y : V) : ℝ := (H x y).im
def UnitDetRootDefs.dualLat (H : UnitDetRootDefs.Sesq V) (Λ : AddSubgroup V) : AddSubgroup V where
  carrier := {x | ∀ y ∈ Λ, ∃ m : ℤ, UnitDetRootDefs.altE H x y = (m : ℝ)}
  zero_mem' := fun y _ => ⟨0, by simp [UnitDetRootDefs.altE]⟩
  add_mem' := by
    intro a b ha hb y hy
    obtain ⟨m, hm⟩ := ha y hy
    obtain ⟨k, hk⟩ := hb y hy
    exact ⟨m + k, by simp only [UnitDetRootDefs.altE] at hm hk ⊢; simp [hm, hk]⟩
  neg_mem' := by
    intro a ha y hy
    obtain ⟨m, hm⟩ := ha y hy
    exact ⟨-m, by simp only [UnitDetRootDefs.altE] at hm ⊢; simp [hm]⟩
def UnitDetRootDefs.IsSelfDual (H : UnitDetRootDefs.Sesq V) (Λ : AddSubgroup V) : Prop := UnitDetRootDefs.dualLat H Λ = Λ
def UnitDetRootDefs.relIdx (Λ₁ Λ₂ : AddSubgroup V) : ℕ := Λ₁.relIndex Λ₂
def UnitDetRootDefs.IsIsom {W : Type*} [AddCommGroup W] [Module ℂ W] (H : UnitDetRootDefs.Sesq V) (H' : UnitDetRootDefs.Sesq W) (g : V →ₗ[ℂ] W) : Prop :=
  ∀ x y, H' (g x) (g y) = H x y
def UnitDetRootDefs.imgLat {W : Type*} [AddCommGroup W] [Module ℂ W] (g : V →ₗ[ℂ] W) (Λ : AddSubgroup V) : AddSubgroup W :=
  Λ.map g.toAddMonoidHom
end General
section Coordinates
variable {n : Type*} [Fintype n]
def UnitDetRootDefs.matH (h : Matrix n n ℂ) : UnitDetRootDefs.Sesq (n → ℂ) :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun z w => ∑ i, ∑ j, z i * h i j * conj (w j))
    (by intro a b c; simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib])
    (by intro c a b; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc])
    (by intro a b c; simp only [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib])
    (by
      intro c a b
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring)
def UnitDetRootDefs.stdH (L : PeriodPair) (n : Type*) [Fintype n] [DecidableEq n] : UnitDetRootDefs.Sesq (n → ℂ) :=
  UnitDetRootDefs.matH (((UnitDetRootDefs.area L : ℝ) : ℂ)⁻¹ • (1 : Matrix n n ℂ))
def UnitDetRootDefs.stdLat (L : PeriodPair) (n : Type*) : AddSubgroup (n → ℂ) :=
  AddSubgroup.pi Set.univ fun _ => L.lattice.toAddSubgroup
end Coordinates
def UnitDetRootDefs.cmL (a : ℕ) (b : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0) : PeriodPair :=
  UnitDetRootDefs.scalePair (UnitDetRootDefs.cmPair a b d ha hd) lam hlam
def UnitDetRootDefs.CmOK (a : ℕ) (b c : ℤ) (d : ℕ) : Prop := 4 * (a : ℤ) * c = b ^ 2 + d ∧ Odd a ∧ d % 8 = 7 ∧ d.Prime
def UnitDetRoot : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0), UnitDetRootDefs.CmOK a b c d →
    ∀ (m : Type) [Fintype m] [DecidableEq m] (Λa : AddSubgroup (m → ℂ)),
      UnitDetRootDefs.IsSelfDual (UnitDetRootDefs.stdH (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) Λa →
      (∀ x ∈ Λa, UnitDetRootDefs.cmTheta b d • x ∈ Λa) →
      UnitDetRootDefs.relIdx (UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) Λa ≠ 0 →
      UnitDetRootDefs.relIdx Λa (UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) ≠ 0 →
      ∃ κ : ℂ, κ ≠ 0 ∧ IsAlgebraic ℚ κ ∧ (∀ σ : ℂ ≃+* ℂ, ‖σ κ‖ = 1) ∧
        ∀ (l : ℕ) [Fact l.Prime] (ι : ℂ ≃+* ℂ_[l]) (δ : (m → ℂ) ≃ₗ[ℂ] (m → ℂ)),
          UnitDetRootDefs.IsIsom (UnitDetRootDefs.stdH (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) (UnitDetRootDefs.stdH (UnitDetRootDefs.cmL a b d ha hd lam hlam) m)
            (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) →
          UnitDetRootDefs.relIdx (UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) (UnitDetRootDefs.imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa) ≠ 0 →
          ¬ l ∣ UnitDetRootDefs.relIdx (UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) (UnitDetRootDefs.imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa) →
          UnitDetRootDefs.relIdx (UnitDetRootDefs.imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa) (UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) ≠ 0 →
          ‖ι κ‖ ^ 2 * ‖ι (LinearMap.det (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)))‖ = 1
end PI


