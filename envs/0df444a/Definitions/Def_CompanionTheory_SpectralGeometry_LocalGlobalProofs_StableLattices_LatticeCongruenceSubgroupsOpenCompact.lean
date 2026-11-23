-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_LatticeCongruenceSubgroupsOpenCompact
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_LatticeCongruenceSubgroupsOpenCompact
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:53:56.629045+00:00
-- url     : https://prove2.me/theorems/e87e895a-87cb-4ce5-8013-c8f0bda69bfb
-- title:
--   Lattice Congruence Subgroups Open Compact
-- statement:
--   Definitions and structural lemmas for Lattice Congruence Subgroups Open Compact, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/LatticeCongruenceSubgroupsOpenCompact.lean

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsTerLast
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil


set_option autoImplicit false
noncomputable section
open CompanionTheory.Rg.FlB CompanionTheory.Rg.Fl Topology Filter
open scoped Matrix
namespace GlobalTheory.CompanionTheory.BLevel
section Entries
variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {m : ℕ}
def IsInt (A : Matrix (Fin m) (Fin m) L) : Prop := ∀ i j, ‖A i j‖ ≤ 1
def IsNear (r : ℝ) (A : Matrix (Fin m) (Fin m) L) : Prop := ∀ i j, ‖(A - 1) i j‖ ≤ r
theorem norm_one_entry (i j : Fin m) : ‖(1 : Matrix (Fin m) (Fin m) L) i j‖ ≤ 1 := by
  rw [Matrix.one_apply]; split_ifs <;> simp
theorem norm_mul_entry {A B : Matrix (Fin m) (Fin m) L} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : ∀ i j, ‖A i j‖ ≤ a) (hB : ∀ i j, ‖B i j‖ ≤ b) (i j : Fin m) : ‖(A * B) i j‖ ≤ a * b := by
  rw [Matrix.mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg ha hb) fun k _ => ?_
  rw [norm_mul]; exact mul_le_mul (hA _ _) (hB _ _) (norm_nonneg _) ha
theorem IsNear.isInt {r : ℝ} {A : Matrix (Fin m) (Fin m) L} (hr : r ≤ 1) (h : IsNear r A) : IsInt A := fun i j => by
  have e : A i j = (A - 1) i j + (1 : Matrix (Fin m) (Fin m) L) i j := by simp
  rw [e]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ((h i j).trans hr) (norm_one_entry i j))
theorem IsInt.mul {A B : Matrix (Fin m) (Fin m) L} (hA : IsInt A) (hB : IsInt B) : IsInt (A * B) := fun i j => by
  simpa using norm_mul_entry zero_le_one zero_le_one hA hB i j
theorem isInt_one : IsInt (1 : Matrix (Fin m) (Fin m) L) := norm_one_entry
theorem IsNear.mul {r : ℝ} {A B : Matrix (Fin m) (Fin m) L} (h0 : 0 ≤ r) (hr : r ≤ 1) (hA : IsNear r A)
    (hB : IsNear r B) : IsNear r (A * B) := by
  have e : A * B - 1 = (A - 1) * B + (B - 1) := by rw [sub_mul]; simp
  intro i j
  rw [e, Matrix.add_apply]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (hB i j))
  simpa using norm_mul_entry h0 zero_le_one hA (hB.isInt hr) i j
theorem isNear_one {r : ℝ} (h0 : 0 ≤ r) : IsNear r (1 : Matrix (Fin m) (Fin m) L) := fun i j => by simpa using h0
theorem IsNear.inv {r : ℝ} {A B : Matrix (Fin m) (Fin m) L} (h0 : 0 ≤ r) (hr : r < 1) (hA : IsNear r A)
    (hBA : B * A = 1) : IsNear r B := by
  have e : B - 1 = -(B * (A - 1)) := by rw [mul_sub, hBA]; simp
  have key : ∀ c : ℝ, 0 ≤ c → (∀ i j, ‖B i j‖ ≤ c) → ∀ i j, ‖(B - 1) i j‖ ≤ c * r := fun c hc hB i j => by
    rw [e, Matrix.neg_apply, norm_neg]; exact norm_mul_entry hc h0 hB hA i j
  have hint : ∀ i j, ‖B i j‖ ≤ 1 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨i₀, j₀, h1⟩ := hcon
    haveI : Nonempty (Fin m × Fin m) := ⟨(i₀, j₀)⟩
    obtain ⟨p, hp⟩ := Finite.exists_max fun p : Fin m × Fin m => ‖B p.1 p.2‖
    have hc : 1 < ‖B p.1 p.2‖ := h1.trans_le (hp (i₀, j₀))
    have h2 := key _ (norm_nonneg _) (fun i j => hp (i, j)) p.1 p.2
    have h3 : B p.1 p.2 = (B - 1) p.1 p.2 + (1 : Matrix (Fin m) (Fin m) L) p.1 p.2 := by simp
    have h4 := IsUltrametricDist.norm_add_le_max ((B - 1) p.1 p.2) ((1 : Matrix (Fin m) (Fin m) L) p.1 p.2)
    rw [← h3] at h4
    rcases le_max_iff.1 h4 with h | h
    · nlinarith
    · linarith [norm_one_entry (L := L) p.1 p.2]
  intro i j
  simpa using key 1 zero_le_one hint i j
theorem IsNear.conj {r : ℝ} {C D K : Matrix (Fin m) (Fin m) L} (h0 : 0 ≤ r) (hC : IsInt C) (hD : IsInt D)
    (hCD : C * D = 1) (hK : IsNear r K) : IsNear r (C * K * D) := by
  have e : C * K * D - 1 = C * (K - 1) * D := by
    rw [mul_sub, sub_mul, mul_one, hCD]
  intro i j
  rw [e]
  simpa using norm_mul_entry (mul_nonneg zero_le_one h0) zero_le_one (norm_mul_entry zero_le_one h0 hC hK) hD i j
def congS (r : ℝ) (h0 : 0 ≤ r) (h1 : r < 1) : Subgroup (GL (Fin m) L) where
  carrier := {g | IsNear r g.1}
  mul_mem' := fun ha hb => IsNear.mul h0 h1.le ha hb
  one_mem' := isNear_one h0
  inv_mem' := fun {g} hg => IsNear.inv h0 h1 hg g.inv_mul
def intS : Subgroup (GL (Fin m) L) where
  carrier := {g | IsInt g.1 ∧ IsInt (g⁻¹).1}
  mul_mem' := fun {a b} ha hb => ⟨IsInt.mul ha.1 hb.1, by rw [mul_inv_rev]; exact IsInt.mul hb.2 ha.2⟩
  one_mem' := by simpa using isInt_one
  inv_mem' := fun {a} ha => ⟨ha.2, by simpa using ha.1⟩
end Entries
section Top
variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {m : ℕ}
variable [ProperSpace L]
end Top
section Conj
variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {n m : ℕ}
  (b : Module.Basis (Fin m) L (Fin n → L))
def conj : Matrix (Fin n) (Fin n) L ≃ₐ[L] Matrix (Fin m) (Fin m) L :=
  Matrix.toLinAlgEquiv'.trans (LinearMap.toMatrixAlgEquiv b)
variable {b} {Λ : AddSubgroup (Fin n → L)}
variable (b)
def phi : GL (Fin n) L ≃* GL (Fin m) L := Units.mapEquiv (conj b).toMulEquiv
variable [ProperSpace L]
theorem continuous_conj : Continuous (conj b) :=
  LinearMap.continuous_of_finiteDimensional (conj b).toLinearMap
theorem continuous_conj_symm : Continuous (conj b).symm :=
  LinearMap.continuous_of_finiteDimensional (conj b).symm.toLinearMap
def phiHomeo : GL (Fin n) L ≃ₜ GL (Fin m) L where
  toEquiv := (phi b).toEquiv
  continuous_toFun := Continuous.units_map (conj b).toMulEquiv.toMonoidHom (continuous_conj b)
  continuous_invFun := Continuous.units_map (conj b).toMulEquiv.symm.toMonoidHom (continuous_conj_symm b)
end Conj
end GlobalTheory.CompanionTheory.BLevel
end


