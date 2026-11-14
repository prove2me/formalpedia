-- Prove2me | Definitions.Def_RPLib_S2_WeilPairingI
-- name    : RPLib_S2_WeilPairingI
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T19:02:15.576722+00:00
-- url     : https://prove2.me/theorems/4567f343-b97c-457c-b27e-ffdd218e3233
-- title:
--   Weil pairing, part I: nondegeneracy
-- statement:
--   Every character of $E[n]$ has the form $e_n(\cdot, T)$, and the Weil pairing is nondegenerate on both sides.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (elliptic-curve layer). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, doi:10.1007/978-0-387-09494-6, Proposition III.8.1

import Mathlib
import Definitions.Def_RPLib_S2_WeilPairingH

/-!
# WPI: nondegeneracy of the Weil pairing (unit S2-WeilPairing, O8 part 2)

* `exists_sum_tau_ne_zero` : Dedekind independence of the translations `τ_S`.
* `exists_eigen` : every character `χ` of `E[n]` has an eigenfunction `g`, `τ_R g = χ(R) g`.
* `char_eq_ePair` : every character of `E[n]` is `e(·, T)` for some `T ∈ E[n]` (descent).
* `ePair_nondeg_right`, `ePair_nondeg_left` : nondegeneracy, using that characters of the finite
  abelian group `E[n]` separate points (`CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity`).
-/

set_option autoImplicit false

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
open IsDedekindDomain
open scoped nonZeroDivisors

namespace RPLib.Weil

section Nondeg

variable {k : Type*} [Field k] {W : WeierstrassCurve k} [W.IsElliptic]
  {L : Type*} [Field L] [Algebra k L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF

/-- Dedekind independence of the translations `τ_S`. -/
lemma exists_sum_tau_ne_zero (s : Finset (Pt W L)) (c : Pt W L → FF W L) {S₀ : Pt W L}
    (hS₀ : S₀ ∈ s) (hc : c S₀ ≠ 0) :
    ∃ a : FF W L, ∑ S ∈ s, c S * tau W L S a ≠ 0 := by
  by_contra h
  push_neg at h
  have hli := (linearIndependent_monoidHom (FF W L) (FF W L)).comp
    (fun S : Pt W L => (tau W L S).toRingEquiv.toMonoidHom)
    (fun S T hST => tau_injective W L (AlgEquiv.ext (fun f => DFunLike.congr_fun hST f)))
  rw [linearIndependent_iff'] at hli
  refine hc (hli s c ?_ S₀ hS₀)
  funext a
  rw [Finset.sum_apply]
  exact h a

/-- **Eigenfunctions**: every character `χ` of `E[n]` has an eigenfunction. -/
theorem exists_eigen {n : ℕ} (hn : (n : L) ≠ 0) (χ : Pt W L → L)
    (hχ0 : ∀ S : Pt W L, n • S = 0 → χ S ≠ 0)
    (hχ : ∀ S₁ S₂ : Pt W L, n • S₁ = 0 → n • S₂ = 0 → χ (S₁ + S₂) = χ S₁ * χ S₂) :
    ∃ g : FF W L, g ≠ 0 ∧ ∀ R : Pt W L, n • R = 0 →
      tau W L R g = algebraMap L (FF W L) (χ R) * g := by
  obtain ⟨a, ha⟩ := exists_sum_tau_ne_zero (W := W) (L := L) (En W L n hn)
    (fun S => algebraMap L (FF W L) (χ S)⁻¹) (S₀ := 0) (mem_En.mpr (smul_zero n))
    ((_root_.map_ne_zero (algebraMap L (FF W L))).mpr (inv_ne_zero (hχ0 0 (smul_zero n))))
  refine ⟨_, ha, fun R hR => ?_⟩
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_equiv (Equiv.addLeft R) (fun S => ?_) (fun S hS => ?_)
  · simp only [mem_En, Equiv.coe_addLeft, nsmul_add, hR, zero_add]
  · have hS' := mem_En.mp hS
    have e1 : (χ S)⁻¹ = χ R * (χ (R + S))⁻¹ := by
      rw [hχ R S hR hS', mul_inv, ← mul_assoc, mul_inv_cancel₀ (hχ0 R hR), one_mul]
    simp only [Equiv.coe_addLeft]
    rw [map_mul, AlgEquiv.commutes, ← tau_add_apply, e1, map_mul, mul_assoc]

/-- Every character of `E[n]` is `e(·, T)` for some `T ∈ E[n]`. -/
theorem char_eq_ePair {n : ℕ} (hn : (n : L) ≠ 0) (χ : Pt W L → L)
    (hχ0 : ∀ S : Pt W L, n • S = 0 → χ S ≠ 0)
    (hχ : ∀ S₁ S₂ : Pt W L, n • S₁ = 0 → n • S₂ = 0 → χ (S₁ + S₂) = χ S₁ * χ S₂) :
    ∃ T : Pt W L, n • T = 0 ∧ ∀ R : Pt W L, n • R = 0 → χ R = ePair W L n R T := by
  obtain ⟨g, hg, hgR⟩ := exists_eigen hn χ hχ0 hχ
  obtain ⟨T, hT, c, _, H, _, hHR, hgc⟩ := descent hn hg (fun R hR P => by
    rw [← ord_tau, hgR R hR,
      ord_mul ((_root_.map_ne_zero (algebraMap L (FF W L))).mpr (hχ0 R hR)) hg,
      ord_alg (hχ0 R hR), zero_add])
  refine ⟨T, hT, fun R hR => alg_cancel hg ?_⟩
  rw [← hgR R hR, hgc, map_mul, map_mul, AlgEquiv.commutes, tau_gT hn hR hT, hHR R hR]
  ring

/-- **Nondegeneracy** in the second variable. -/
theorem ePair_nondeg_right {n : ℕ} (hn : (n : L) ≠ 0) {T : Pt W L} (hT : n • T = 0)
    (h : ∀ S : Pt W L, n • S = 0 → ePair W L n S T = 1) : T = 0 := by
  classical
  by_contra hT0
  haveI : Finite (RPLib.Torsion.tors (W.baseChange L) n) :=
    RPLib.Torsion.finite_tors (W := W.baseChange L) n hn
  haveI : NeZero (n : L) := ⟨hn⟩
  haveI : NeZero n := ⟨ne_zero_of_cast hn⟩
  have hexp : Monoid.exponent (Multiplicative (RPLib.Torsion.tors (W.baseChange L) n)) ∣ n :=
    Monoid.exponent_dvd_of_forall_pow_eq_one (fun g => by
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one]
      exact Subtype.ext (by
        rw [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero]
        exact RPLib.Torsion.mem_tors.mp (Multiplicative.toAdd g).2))
  haveI : HasEnoughRootsOfUnity L
      (Monoid.exponent (Multiplicative (RPLib.Torsion.tors (W.baseChange L) n))) :=
    HasEnoughRootsOfUnity.of_dvd L hexp
  obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity
    (Multiplicative (RPLib.Torsion.tors (W.baseChange L) n)) L
    (a := Multiplicative.ofAdd ⟨T, RPLib.Torsion.mem_tors.mpr hT⟩)
    (fun h1 => hT0 (congrArg Subtype.val (Multiplicative.ofAdd.injective (h1.trans ofAdd_zero.symm))))
  obtain ⟨χ, hχdef⟩ : ∃ χ : Pt W L → L, ∀ (P : Pt W L) (hP : n • P = 0),
      χ P = ((φ (Multiplicative.ofAdd ⟨P, RPLib.Torsion.mem_tors.mpr hP⟩) : Lˣ) : L) :=
    ⟨fun P => if hP : n • P = 0 then
      ((φ (Multiplicative.ofAdd ⟨P, RPLib.Torsion.mem_tors.mpr hP⟩) : Lˣ) : L) else 1,
     fun P hP => dif_pos hP⟩
  have hχ0 : ∀ S : Pt W L, n • S = 0 → χ S ≠ 0 := fun S hS => by
    rw [hχdef S hS]; exact Units.ne_zero _
  have hχ : ∀ S₁ S₂ : Pt W L, n • S₁ = 0 → n • S₂ = 0 → χ (S₁ + S₂) = χ S₁ * χ S₂ := by
    intro S₁ S₂ h₁ h₂
    have h₁₂ : n • (S₁ + S₂) = 0 := by rw [nsmul_add, h₁, h₂, add_zero]
    rw [hχdef _ h₁₂, hχdef _ h₁, hχdef _ h₂, ← Units.val_mul, ← map_mul, ← ofAdd_add]
    rfl
  obtain ⟨T₀, hT₀, hχT⟩ := char_eq_ePair hn χ hχ0 hχ
  apply hφ
  apply Units.ext
  rw [Units.val_one, ← hχdef T hT, hχT T hT]
  have hs := ePair_swap hn hT hT₀
  rw [h T₀ hT₀, mul_one] at hs
  exact hs

/-- **Nondegeneracy** in the first variable. -/
theorem ePair_nondeg_left {n : ℕ} (hn : (n : L) ≠ 0) {S : Pt W L} (hS : n • S = 0)
    (h : ∀ T : Pt W L, n • T = 0 → ePair W L n S T = 1) : S = 0 :=
  ePair_nondeg_right hn hS (fun T hT => by
    have hs := ePair_swap hn hT hS
    rw [h T hT, mul_one] at hs
    exact hs)

end Nondeg

end RPLib.Weil


