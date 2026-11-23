-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:13:57.2845+00:00
-- url     : https://prove2.me/theorems/dd7e0088-6915-45d1-a11a-b6a7a818c359
-- title:
--   Res Alg Split Two
-- statement:
--   Definitions and structural lemmas for Res Alg Split Two, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ResAlgSplitTwo.lean

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc
namespace GlobalTheory.CompanionTheory.UnrDens
def barσ {R : Type} [CommRing R] (σ : R →+* R) (ϖ : R) (h : σ ϖ = ϖ) (k : ℕ) :
    R ⧸ lev ϖ k →+* R ⧸ lev ϖ k :=
  Ideal.Quotient.lift (lev ϖ k) ((Ideal.Quotient.mk (lev ϖ k)).comp σ) (by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    simp only [RingHom.comp_apply, map_mul, map_pow, h]
    apply Ideal.Quotient.eq_zero_iff_mem.2
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))
@[simp] theorem barσ_mk {R : Type} [CommRing R] (σ : R →+* R) (ϖ : R) (h : σ ϖ = ϖ) (k : ℕ) (a : R) :
    barσ σ ϖ h k (Ideal.Quotient.mk (lev ϖ k) a) = Ideal.Quotient.mk (lev ϖ k) (σ a) := rfl
structure ResAlg (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ) : Prop where
  inv : ∀ a, τ (τ a) = a
  fixedUnit : ∀ a, τ a = a → a ≠ 0 → IsUnit a
  basis : ∃ u : E, IsUnit (u - τ u) ∧ ∀ a, ∃ x y, τ x = x ∧ τ y = y ∧ a = x + y * u
  one_lt : 1 < q
  card : Nat.card E = q ^ 2
  eps : (ε = -1 ∧ IsField E) ∨ (ε = 1 ∧ ¬ IsField E)
variable {E : Type} [CommRing E] {τ : E →+* E}
structure HermSp (E : Type) [CommRing E] (τ : E →+* E) (V : Type) [AddCommGroup V] [Module E V] where
  h : V → V → E
  add_left : ∀ u v w, h (u + v) w = h u w + h v w
  smul_left : ∀ (a : E) v w, h (a • v) w = a * h v w
  symm : ∀ v w, h w v = τ (h v w)
  nondeg : ∀ v, (∀ w, h v w = 0) → v = 0
variable {V : Type} [AddCommGroup V] [Module E V]
namespace HermSp
variable (B : HermSp E τ V)
theorem zero_left (w : V) : B.h 0 w = 0 := by
  have h0 := B.smul_left 0 0 w
  rwa [zero_smul, zero_mul] at h0
theorem add_right (v u w : V) : B.h v (u + w) = B.h v u + B.h v w := by
  rw [B.symm (u + w) v, B.add_left, map_add, ← B.symm, ← B.symm]
theorem smul_right (a : E) (v w : V) : B.h v (a • w) = τ a * B.h v w := by
  rw [B.symm (a • w) v, B.smul_left, map_mul, ← B.symm]
def perp (w : V) : Submodule E V where
  carrier := {v | B.h v w = 0}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [B.add_left, ha, hb, add_zero]
  zero_mem' := B.zero_left w
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_setOf_eq] at *
    rw [B.smul_left, hx, mul_zero]
noncomputable def coef {w : V} (hw : IsUnit (B.h w w)) (z : V) : E := B.h z w * (hw.unit⁻¹ : Eˣ)
theorem coef_spec {w : V} (hw : IsUnit (B.h w w)) (z : V) : B.h (z - B.coef hw z • w) w = 0 := by
  have hu : ((hw.unit⁻¹ : Eˣ) : E) * B.h w w = 1 := by
    have h1 := hw.unit.inv_mul
    simpa using h1
  have hc : B.coef hw z * B.h w w = B.h z w := by
    unfold coef
    rw [mul_assoc, hu, mul_one]
  have e : B.h z w = B.h (z - B.coef hw z • w) w + B.h (B.coef hw z • w) w := by
    rw [← B.add_left, sub_add_cancel]
  rw [B.smul_left, hc] at e
  linear_combination -e
noncomputable def perpForm {w : V} (hw : IsUnit (B.h w w)) : HermSp E τ (B.perp w) where
  h a b := B.h a b
  add_left u v x := by simp [B.add_left]
  smul_left a v x := by simp [B.smul_left]
  symm v x := B.symm _ _
  nondeg := by
    intro v hv
    apply Subtype.ext
    apply B.nondeg
    intro z
    have h1 := hv ⟨z - B.coef hw z • w, B.coef_spec hw z⟩
    have hz : z = (z - B.coef hw z • w) + B.coef hw z • w := by abel
    have h0 : B.h (v : V) w = 0 := v.2
    rw [hz, B.add_right, B.smul_right, h0, mul_zero, add_zero]
    exact h1
@[simp] theorem perpForm_h {w : V} (hw : IsUnit (B.h w w)) (a b : B.perp w) :
    (B.perpForm hw).h a b = B.h a b := rfl
noncomputable def perpEquiv {w : V} (hw : IsUnit (B.h w w)) : E × B.perp w ≃ V where
  toFun p := p.1 • w + p.2
  invFun z := (B.coef hw z, ⟨z - B.coef hw z • w, B.coef_spec hw z⟩)
  left_inv := by
    rintro ⟨a, v⟩
    have h0 : B.h (v : V) w = 0 := v.2
    have hc : B.coef hw (a • w + (v : V)) = a := by
      unfold coef
      rw [B.add_left, B.smul_left, h0, add_zero, mul_assoc]
      have : B.h w w * ((hw.unit⁻¹ : Eˣ) : E) = 1 := by
        have := hw.unit.mul_inv
        simpa using this
      rw [this, mul_one]
    ext
    · exact hc
    · simp [hc]
  right_inv := by
    intro z
    simp
end HermSp
def HermSp.self (hτ : ∀ a, τ (τ a) = a) : HermSp E τ E where
  h a b := a * τ b
  add_left u v w := by ring
  smul_left a v w := by simp [mul_assoc]
  symm v w := by simp [hτ, mul_comm]
  nondeg v hv := by simpa using hv 1
def HermSp.ofMatrix (hτ : ∀ a, τ (τ a) = a) {m : ℕ} (S : Matrix (Fin m) (Fin m) E)
    (hS : cT τ S = S) (hd : IsUnit S.det) : HermSp E τ (Fin m → E) where
  h v w := dotProduct (fun i => τ (w i)) (S.mulVec v)
  add_left u v w := by rw [Matrix.mulVec_add, dotProduct_add]
  smul_left a v w := by rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  symm v w := by
    have hij : ∀ i j, τ (S j i) = S i j := fun i j => by
      have := congrFun (congrFun hS i) j
      simpa [cT] using this
    simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, hτ, hij]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  nondeg v hv := by
    have h0 : S.mulVec v = 0 := by
      funext i
      have := hv (Pi.single i 1)
      simpa [dotProduct, Pi.single_apply] using this
    have := congrArg (S⁻¹).mulVec h0
    have hu : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul _ hd
    simpa [Matrix.mulVec_mulVec, hu] using this
end GlobalTheory.CompanionTheory.UnrDens


