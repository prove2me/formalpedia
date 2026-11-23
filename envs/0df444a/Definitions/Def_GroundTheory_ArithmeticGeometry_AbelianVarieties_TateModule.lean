-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_TateModule
-- name    : GroundTheory_ArithmeticGeometry_AbelianVarieties_TateModule
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:42.828314+00:00
-- url     : https://prove2.me/theorems/c12d1cb1-64dd-4002-9b75-6604dc292d3a
-- title:
--   Tate Module
-- statement:
--   Definitions and structural lemmas for Tate Module, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/TateModule.lean

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_TorsionGalois
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_neg
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_some
import Theorems.Thm_GroundTheory_ProfCoh_coe_galRootsOfUnityHom_apply
import Theorems.Thm_GroundTheory_ProfCoh_coe_openNormalSubgroupEquiv_symm_apply
import Theorems.Thm_GroundTheory_ProfCoh_isDiscreteRep_apply
import Theorems.Thm_GroundTheory_ProfCoh_mem_stabilizer
import Theorems.Thm_GroundTheory_ProfCoh_openNormalSubgroupEquiv_apply
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galAddInt___apply_e3c2bd0048b0
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galAddZ___apply_9150def5d083
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galAdd___apply_d57b0a2a1b9a
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galRootsOfUnityZ___apply_40a7d6b8f2a7
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galRootsOfUnity___apply_600492b04171
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galUnitsZ___apply_2d4ee74d5783
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galUnits___apply_5e27268f2c21
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Arith.Abelian.xOf_neg
attribute [local simp] GroundTheory.Arith.Abelian.xOf_some
attribute [local simp] GroundTheory.ProfCoh.coe_galRootsOfUnityHom_apply
attribute [local simp] GroundTheory.ProfCoh.coe_openNormalSubgroupEquiv_symm_apply
attribute [local simp] GroundTheory.ProfCoh.isDiscreteRep_apply
attribute [local simp] GroundTheory.ProfCoh.mem_stabilizer
attribute [local simp] GroundTheory.ProfCoh.openNormalSubgroupEquiv_apply
attribute [local simp] P2M_GroundTheory_ProfCoh_galAddInt___apply_e3c2bd0048b0
attribute [local simp] P2M_GroundTheory_ProfCoh_galAddZ___apply_9150def5d083
attribute [local simp] P2M_GroundTheory_ProfCoh_galAdd___apply_d57b0a2a1b9a
attribute [local simp] P2M_GroundTheory_ProfCoh_galRootsOfUnityZ___apply_40a7d6b8f2a7
attribute [local simp] P2M_GroundTheory_ProfCoh_galRootsOfUnity___apply_600492b04171
attribute [local simp] P2M_GroundTheory_ProfCoh_galUnitsZ___apply_2d4ee74d5783
attribute [local simp] P2M_GroundTheory_ProfCoh_galUnits___apply_5e27268f2c21


set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Arith.Abelian
open AddSubgroup
section Def
variable (ℓ : ℕ) (A : Type*) [AddCommGroup A]
def TateModule : AddSubgroup (ℕ → A) where
  carrier := {t | (∀ k, ℓ ^ k • t k = 0) ∧ ∀ k, ℓ • t (k + 1) = t k}
  add_mem' {s t} hs ht :=
    ⟨fun k => by simp [nsmul_add, hs.1 k, ht.1 k], fun k => by simp [nsmul_add, hs.2 k, ht.2 k]⟩
  zero_mem' := ⟨fun k => by simp, fun k => by simp⟩
  neg_mem' {t} ht := ⟨fun k => by simp [ht.1 k], fun k => by simp [ht.2 k]⟩
variable {ℓ A}
theorem TateModule.pow_nsmul (t : TateModule ℓ A) (k : ℕ) : ℓ ^ k • (t : ℕ → A) k = 0 :=
  t.2.1 k
theorem TateModule.nsmul_succ (t : TateModule ℓ A) (k : ℕ) :
    ℓ • (t : ℕ → A) (k + 1) = (t : ℕ → A) k :=
  t.2.2 k
theorem nsmul_swap (a b : ℕ) (x : A) : a • b • x = b • a • x := by
  rw [← mul_nsmul', mul_comm, mul_nsmul']
end Def
section Module
variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {A : Type*} [AddCommGroup A]
instance neZero_pow_prime (k : ℕ) : NeZero (ℓ ^ k) := ⟨pow_ne_zero k hℓ.out.ne_zero⟩
theorem val_nsmul_eq {k : ℕ} {P : A} (hP : ℓ ^ k • P = 0) {x : ZMod (ℓ ^ k)} {N : ℕ}
    (h : (N : ZMod (ℓ ^ k)) = x) : x.val • P = N • P := by
  rw [← h, ZMod.val_natCast, ← nsmul_eq_mod_nsmul N hP]
noncomputable instance TateModule.instSMul : SMul ℤ_[ℓ] (TateModule ℓ A) where
  smul a t := ⟨fun k => (PadicInt.toZModPow k a).val • (t : ℕ → A) k,
    fun k => by rw [nsmul_swap, (TateModule.pow_nsmul t), nsmul_zero],
    fun k => by
      rw [nsmul_swap, (TateModule.nsmul_succ t)]
      exact (val_nsmul_eq ((TateModule.pow_nsmul t) k)
        (by rw [ZMod.natCast_val, PadicInt.cast_toZModPow _ _ (Nat.le_succ k)])).symm⟩
theorem TateModule.smul_apply (a : ℤ_[ℓ]) (t : TateModule ℓ A) (k : ℕ) :
    ((a • t : TateModule ℓ A) : ℕ → A) k = (PadicInt.toZModPow k a).val • (t : ℕ → A) k :=
  rfl
noncomputable instance TateModule.instModule : Module ℤ_[ℓ] (TateModule ℓ A) where
  one_smul t := Subtype.ext <| funext fun k => by
    rw [TateModule.smul_apply, val_nsmul_eq ((TateModule.pow_nsmul t) k) (N := 1) (by simp), one_nsmul]
  mul_smul a b t := Subtype.ext <| funext fun k => by
    rw [TateModule.smul_apply, TateModule.smul_apply, TateModule.smul_apply, ← mul_nsmul',
      val_nsmul_eq ((TateModule.pow_nsmul t) k)
        (N := (PadicInt.toZModPow k a).val * (PadicInt.toZModPow k b).val) (by simp)]
  smul_zero a := Subtype.ext <| funext fun k => by
    rw [TateModule.smul_apply]
    simp
  smul_add a s t := Subtype.ext <| funext fun k => by
    rw [TateModule.smul_apply]
    simp [nsmul_add, TateModule.smul_apply]
  add_smul a b t := Subtype.ext <| funext fun k => by
    rw [TateModule.smul_apply]
    simp only [AddSubgroup.coe_add, Pi.add_apply, TateModule.smul_apply]
    rw [← add_nsmul, val_nsmul_eq ((TateModule.pow_nsmul t) k)
        (N := (PadicInt.toZModPow k a).val + (PadicInt.toZModPow k b).val) (by simp)]
  zero_smul t := Subtype.ext <| funext fun k => by
    rw [TateModule.smul_apply]
    simp
end Module
section Lift
variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {A : Type*} [AddCommGroup A]
noncomputable def zmodMulHom (m : ℕ) (P : A) (hP : m • P = 0) : ZMod m →+ A :=
  ZMod.lift m ⟨zmultiplesHom A P, by simp [hP]⟩
variable (hcard : ∀ k, Nat.card {P : A // ℓ ^ k • P = 0} = (ℓ ^ k) ^ 2)
include hcard
theorem finite_torsion_of_card (k : ℕ) : Finite {P : A // ℓ ^ k • P = 0} :=
  Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ (NeZero.ne _))
theorem exists_nsmul_eq_of_card (k : ℕ) (P : A) (hP : ℓ ^ k • P = 0) :
    ∃ Q : A, ℓ ^ (k + 1) • Q = 0 ∧ ℓ • Q = P := by
  let D := torsionBy A ((ℓ ^ (k + 1) : ℕ) : ℤ)
  let C := torsionBy A ((ℓ ^ k : ℕ) : ℤ)
  have hD : Nat.card D = (ℓ ^ (k + 1)) ^ 2 := by
    rw [← hcard]; exact Nat.card_congr (Equiv.subtypeEquivRight fun P => torsionBy.nsmul_iff)
  have hC : Nat.card C = (ℓ ^ k) ^ 2 := by
    rw [← hcard]; exact Nat.card_congr (Equiv.subtypeEquivRight fun P => torsionBy.nsmul_iff)
  have : Finite C := Nat.finite_of_card_ne_zero (by rw [hC]; exact pow_ne_zero _ (NeZero.ne _))
  have : Finite D := Nat.finite_of_card_ne_zero (by rw [hD]; exact pow_ne_zero _ (NeZero.ne _))
  have := finite_torsion_of_card hcard 1
  let ψ : D →+ C :=
    { toFun := fun Q => ⟨ℓ • (Q : A), by
        rw [torsionBy.nsmul_iff, ← mul_nsmul', ← pow_succ, torsionBy.nsmul_iff.mp Q.2]⟩
      map_zero' := Subtype.ext (nsmul_zero ℓ)
      map_add' := fun Q R => Subtype.ext (nsmul_add (Q : A) R ℓ) }
  have hker : Nat.card ψ.ker ≤ (ℓ ^ 1) ^ 2 := by
    rw [← hcard 1]
    refine Nat.card_le_card_of_injective (fun Q => ⟨((Q : D) : A), by
        have h := Q.2
        rw [AddMonoidHom.mem_ker] at h
        rw [pow_one]
        exact congrArg Subtype.val h⟩) ?_
    intro Q R h
    exact Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val h))
  have htot : Nat.card D = Nat.card ψ.ker * Nat.card ψ.range := by
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup ψ.ker,
      Nat.card_congr (QuotientAddGroup.quotientKerEquivRange ψ).toEquiv, mul_comm]
  have hrange : ψ.range = ⊤ := by
    apply AddSubgroup.eq_top_of_le_card
    rw [hC]
    have h1 : (ℓ ^ (k + 1)) ^ 2 ≤ (ℓ ^ 1) ^ 2 * Nat.card ψ.range := by
      rw [← hD, htot]; exact Nat.mul_le_mul_right _ hker
    have h2 : (ℓ ^ (k + 1)) ^ 2 = (ℓ ^ 1) ^ 2 * (ℓ ^ k) ^ 2 := by ring
    rw [h2] at h1
    exact Nat.le_of_mul_le_mul_left h1 (pow_pos (pow_pos hℓ.out.pos 1) 2)
  obtain ⟨Q, hQ⟩ := AddMonoidHom.range_eq_top.mp hrange ⟨P, torsionBy.nsmul_iff.mpr hP⟩
  exact ⟨Q, torsionBy.nsmul_iff.mp Q.2, congrArg Subtype.val hQ⟩
noncomputable def rootSeq (k : ℕ) (P : A) (hP : ℓ ^ k • P = 0) :
    (m : ℕ) → {Q : A // ℓ ^ (k + m) • Q = 0}
  | 0 => ⟨P, hP⟩
  | m + 1 =>
    ⟨(exists_nsmul_eq_of_card hcard (k + m) _ (rootSeq k P hP m).2).choose,
      (exists_nsmul_eq_of_card hcard (k + m) _ (rootSeq k P hP m).2).choose_spec.1⟩
end Lift
section Basis
variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {A : Type*} [AddCommGroup A]
end Basis
section Curve
variable {F : Type*} [Field F] [IsSepClosed F] [DecidableEq F] (W : WeierstrassCurve F)
  [W.IsElliptic] (ℓ : ℕ) [hℓ : Fact ℓ.Prime]
end Curve
section Topology
variable {ℓ : ℕ} {A : Type*} [AddCommGroup A]
instance TateModule.instTopologicalSpace : TopologicalSpace (TateModule ℓ A) :=
  TopologicalSpace.induced (fun t => (t : ℕ → A)) (@Pi.topologicalSpace ℕ (fun _ => A) fun _ => ⊥)
end Topology
section Action
variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {A : Type*} [AddCommGroup A]
noncomputable def TateModule.map (f : A →+ A) : TateModule ℓ A →ₗ[ℤ_[ℓ]] TateModule ℓ A where
  toFun t := ⟨fun k => f ((t : ℕ → A) k),
    fun k => by rw [← map_nsmul, TateModule.pow_nsmul t k, map_zero],
    fun k => by rw [← map_nsmul, TateModule.nsmul_succ t k]⟩
  map_add' s t := Subtype.ext (funext fun k => map_add f _ _)
  map_smul' a t := Subtype.ext (funext fun k => map_nsmul f _ _)
noncomputable def tateRep {G : Type*} [Monoid G] (φ : G →* AddMonoid.End A) :
    Representation ℤ_[ℓ] G (TateModule ℓ A) where
  toFun g := TateModule.map (φ g)
  map_one' := LinearMap.ext fun t => Subtype.ext <| funext fun k => by
    show φ 1 ((t : ℕ → A) k) = (t : ℕ → A) k
    rw [map_one]
    rfl
  map_mul' g h := LinearMap.ext fun t => Subtype.ext <| funext fun k => by
    show φ (g * h) ((t : ℕ → A) k) = φ g (φ h ((t : ℕ → A) k))
    rw [map_mul]
    rfl
end Action
section Galois
universe u
variable (K L : Type u) [Field K] [Field L] [Algebra K L] [DecidableEq L] (W : WeierstrassCurve K)
  (ℓ : ℕ) [hℓ : Fact ℓ.Prime]
noncomputable abbrev galTateRep :
    Representation ℤ_[ℓ] Gal(L/K) (TateModule ℓ (W.baseChange L).toAffine.Point) :=
  tateRep (galPointsHom K L W)
end Galois
end GroundTheory.Arith.Abelian


