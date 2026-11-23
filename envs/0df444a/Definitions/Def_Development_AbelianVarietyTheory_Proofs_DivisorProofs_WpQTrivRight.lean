-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WpQTrivRight
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_WpQTrivRight
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:36:37.46415+00:00
-- url     : https://prove2.me/theorems/36f6c0b9-3aac-4c1f-b93d-544fc55a8ac9
-- title:
--   Wp QTriv Right
-- statement:
--   Definitions and structural lemmas for Wp QTriv Right, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WpQTrivRight.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationWeilPairingProperties
import Theorems.Thm_GlobalTheory_Ex_NumD_qEq_iff
import Theorems.Thm_GlobalTheory_Ex_NumD_wp_swap
import Theorems.Thm_GlobalTheory_Ex_WpPairing_wp_mul_right
import Theorems.Thm_GlobalTheory_Ex_WpPairing_wp_qTriv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
namespace GlobalTheory.SympQ
variable {O : Type} [CommRing O] (N : NumD O)
def trivHom (k : ℕ) : Multiplicative N.X →* N.QT k where
  toFun z := N.qTriv k z.toAdd
  map_one' := Subtype.ext (Prod.ext (by simp [NumD.qTriv]) (by simp [NumD.qTriv, N.io_zero]))
  map_mul' a b := Subtype.ext (Prod.ext (by simp [NumD.qTriv, smul_add]) (by simp [NumD.qTriv, N.io_add]))
abbrev Qq (k : ℕ) : Type := N.QT k ⧸ (trivHom N k).range
theorem qEq_iff_mk_eq {k : ℕ} (p p' : N.QT k) : N.QEq p p' ↔ (QuotientGroup.mk p : Qq N k) = QuotientGroup.mk p' := by
  rw [N.qEq_iff, QuotientGroup.eq]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨Multiplicative.ofAdd z, by simp [trivHom]⟩
  · rintro ⟨z, hz⟩
    refine ⟨z.toAdd, ?_⟩
    change N.qTriv k z.toAdd = p⁻¹ * p' at hz
    rw [hz, mul_inv_cancel_left]
def pushRep (M n : ℕ) : N.QT M →* N.QT n :=
  if h : n ∣ M then
    { toFun := fun p => ⟨(p.1.1, p.1.2 ^ (M / n)), by
        rw [NumD.mem_QT, ← pow_mul, Nat.div_mul_cancel h]
        exact p.2⟩
      map_one' := Subtype.ext (Prod.ext rfl (by simp))
      map_mul' := fun p q => Subtype.ext (Prod.ext rfl (by simp [mul_pow])) }
  else 1
theorem pushRep_fst {M n : ℕ} (h : n ∣ M) (p : N.QT M) : (pushRep N M n p).1.1 = p.1.1 := by
  simp [pushRep, h]
theorem pushRep_snd {M n : ℕ} (h : n ∣ M) (p : N.QT M) : (pushRep N M n p).1.2 = p.1.2 ^ (M / n) := by
  simp [pushRep, h]
theorem pushRep_triv (M n : ℕ) : (trivHom N M).range ≤ (trivHom N n).range.comap (pushRep N M n) := by
  rintro _ ⟨z, rfl⟩
  by_cases h : n ∣ M
  · refine ⟨Multiplicative.ofAdd ((M / n) • z.toAdd), Subtype.ext (Prod.ext ?_ ?_)⟩
    · simp only [trivHom, MonoidHom.coe_mk, OneHom.coe_mk, NumD.qTriv, toAdd_ofAdd]
      rw [pushRep_fst N h, smul_smul, Nat.mul_div_cancel' h]
    · simp only [trivHom, MonoidHom.coe_mk, OneHom.coe_mk, NumD.qTriv, toAdd_ofAdd]
      rw [pushRep_snd N h, N.io_nsmul]
  · simp [pushRep, h]
def pushQ (M n : ℕ) : Qq N M →* Qq N n := QuotientGroup.map _ _ (pushRep N M n) (pushRep_triv N M n)
theorem wp_qTriv_right {k : ℕ} (p : N.QT k) (z : N.X) : N.wp p (N.qTriv k z) = 1 := by
  rw [← inv_inj, ← NumD.wp_swap, WpPairing.wp_qTriv, inv_one]
theorem wp_congr {k : ℕ} {p p' q q' : N.QT k} (hp : N.QEq p p') (hq : N.QEq q q') : N.wp p q = N.wp p' q' := by
  obtain ⟨z, rfl⟩ := (N.qEq_iff _ _).1 hp
  obtain ⟨w, rfl⟩ := (N.qEq_iff _ _).1 hq
  rw [WpPairing.wp_mul_left, WpPairing.wp_mul_right, WpPairing.wp_mul_right, WpPairing.wp_qTriv,
    WpPairing.wp_qTriv, wp_qTriv_right]
  simp
def wpQ (k : ℕ) (x y : Qq N k) : Oˣ :=
  Quotient.liftOn₂' x y (fun p q => N.wp p q) fun p q p' q' hp hq =>
    wp_congr N ((qEq_iff_mk_eq N _ _).2 (Quotient.sound' hp)) ((qEq_iff_mk_eq N _ _).2 (Quotient.sound' hq))
end GlobalTheory.SympQ


