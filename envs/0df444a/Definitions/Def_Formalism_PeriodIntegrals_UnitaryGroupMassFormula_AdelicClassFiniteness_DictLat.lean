-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictLat
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictLat
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T13:13:28.412437+00:00
-- url     : https://prove2.me/theorems/61fff927-22a9-46b2-b66f-b9fea8276ec3
-- title:
--   Dict Lat
-- statement:
--   Definitions and structural lemmas for Dict Lat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/DictLat.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictPlan
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


set_option autoImplicit false
noncomputable section
namespace PIW.AdelClassFin
open Formalism.MainNotions.S PI.AdelClassFin NumberField
open scoped TensorProduct Matrix
theorem DictLat.hhat_add_right (I : AutInst) (y z z' : Fin I.n → I.E ⊗[I.F] Af I.F) :
    hhat I y (z + z') = hhat I y z + hhat I y z' := by
  simp only [hhat, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]
theorem DictLat.hhat_smul_right (I : AutInst) (y z : Fin I.n → I.E ⊗[I.F] Af I.F)
    (r : I.E ⊗[I.F] Af I.F) : hhat I y (r • z) = r * hhat I y z := by
  unfold hhat Formalism.UG.hform
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
theorem DictLat.hhat_zero_right (I : AutInst) (y : Fin I.n → I.E ⊗[I.F] Af I.F) : hhat I y 0 = 0 := by
  simp [hhat, Formalism.UG.hform]
theorem DictLat.hhat_add_left (I : AutInst) (y y' z : Fin I.n → I.E ⊗[I.F] Af I.F) :
    hhat I (y + y') z = hhat I y z + hhat I y' z := by
  simp only [hhat, Formalism.UG.hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
theorem DictLat.hhat_smul_left (I : AutInst) (y z : Fin I.n → I.E ⊗[I.F] Af I.F)
    (r : I.E ⊗[I.F] Af I.F) :
    hhat I (r • y) z = Formalism.UG.sigR I.cm.sig (Af I.F) r * hhat I y z := by
  unfold hhat Formalism.UG.hform
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
theorem DictLat.hhat_zero_left (I : AutInst) (z : Fin I.n → I.E ⊗[I.F] Af I.F) : hhat I 0 z = 0 := by
  simp [hhat, Formalism.UG.hform]
theorem DictLat.sigR_inclE (I : AutInst) (e : I.E) :
    Formalism.UG.sigR I.cm.sig (Af I.F) (Formalism.UG.inclE (F := I.F) (Af I.F) e) =
      Formalism.UG.inclE (F := I.F) (Af I.F) (star e) := by
  first
    | rfl
    | simp [Formalism.UG.sigR, Formalism.UG.inclE, Algebra.TensorProduct.map_tmul]; rfl
theorem DictLat.sigR_one_tmul (I : AutInst) (a : Af I.F) :
    Formalism.UG.sigR I.cm.sig (Af I.F) ((1 : I.E) ⊗ₜ[I.F] a) = (1 : I.E) ⊗ₜ[I.F] a := by
  simp [Formalism.UG.sigR, Algebra.TensorProduct.map_tmul]
theorem DictLat.inclE_int (I : AutInst) {e : I.E} (he : e ∈ (algebraMap (𝓞 I.E) I.E).range) :
    Formalism.UG.inclE (F := I.F) (Af I.F) e ∈ IntAf I.F I.E := by
  exact Subring.subset_closure (Or.inl ⟨⟨e, he⟩, rfl⟩)
theorem DictLat.star_int (I : AutInst) (a : 𝓞 I.E) :
    star (algebraMap (𝓞 I.E) I.E a) ∈ (algebraMap (𝓞 I.E) I.E).range := by
  have hint : IsIntegral ℤ (star (algebraMap (𝓞 I.E) I.E a)) :=
    (NumberField.RingOfIntegers.isIntegral_coe a).map (starRingEnd I.E).toIntAlgHom
  exact ⟨⟨_, hint⟩, rfl⟩
theorem DictLat.sigR_int (I : AutInst) {r : I.E ⊗[I.F] Af I.F} (hr : r ∈ IntAf I.F I.E) :
    Formalism.UG.sigR I.cm.sig (Af I.F) r ∈ IntAf I.F I.E := by
  have hle : IntAf I.F I.E ≤ (IntAf I.F I.E).comap (Formalism.UG.sigR I.cm.sig (Af I.F)) := by
    show Subring.closure _ ≤ _
    rw [Subring.closure_le]
    rintro _ (⟨⟨x, hx⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
    · obtain ⟨a, rfl⟩ := hx
      show Formalism.UG.sigR I.cm.sig (Af I.F)
        (Formalism.UG.inclE (F := I.F) (Af I.F) (algebraMap (𝓞 I.E) I.E a)) ∈ IntAf I.F I.E
      rw [DictLat.sigR_inclE]
      exact DictLat.inclE_int I (DictLat.star_int I a)
    · show Formalism.UG.sigR I.cm.sig (Af I.F) ((1 : I.E) ⊗ₜ[I.F] (y : Af I.F)) ∈ IntAf I.F I.E
      rw [DictLat.sigR_one_tmul]
      exact Subring.subset_closure (Or.inr ⟨⟨y, hy⟩, rfl⟩)
  exact hle hr
theorem DictLat.iv_add (I : AutInst) (v w : Fin I.n → I.E) : iv I (v + w) = iv I v + iv I w := by
  funext i
  simp [iv, map_add]
theorem DictLat.iv_zero (I : AutInst) : iv I (0 : Fin I.n → I.E) = 0 := by
  funext i
  simp [iv]
theorem DictLat.iv_smulE (I : AutInst) (c : I.E) (v : Fin I.n → I.E) :
    iv I (c • v) = Formalism.UG.inclE (F := I.F) (Af I.F) c • iv I v := by
  funext i
  simp [iv, map_mul]
theorem DictLat.iv_smulO (I : AutInst) (a : 𝓞 I.E) (v : Fin I.n → I.E) :
    iv I (a • v) = Formalism.UG.inclE (F := I.F) (Af I.F) ((a : 𝓞 I.E) : I.E) • iv I v := by
  funext i
  show Formalism.UG.inclE (F := I.F) (Af I.F) ((a • v) i) =
    Formalism.UG.inclE (F := I.F) (Af I.F) ((a : 𝓞 I.E) : I.E) * Formalism.UG.inclE (F := I.F) (Af I.F) (v i)
  rw [Pi.smul_apply, Algebra.smul_def, map_mul]
theorem DictLat.iv_mem (I : AutInst) {l : Fin I.n → I.E} (hl : l ∈ I.L) : iv I l ∈ I.Lf := by
  exact Submodule.subset_span ⟨⟨l, hl⟩, rfl⟩
theorem DictLat.Lf_smul (I : AutInst) {r : I.E ⊗[I.F] Af I.F} (hr : r ∈ IntAf I.F I.E)
    {y : Fin I.n → I.E ⊗[I.F] Af I.F} (hy : y ∈ I.Lf) : r • y ∈ I.Lf := by
  exact I.Lf.smul_mem ⟨r, hr⟩ hy
def dualR (I : AutInst) (y : Fin I.n → I.E ⊗[I.F] Af I.F) :
    Submodule (IntAf I.F I.E) (Fin I.n → I.E ⊗[I.F] Af I.F) where
  carrier := {z | hhat I y z ∈ IntAf I.F I.E}
  add_mem' := fun {a b} ha hb => by
    show hhat I y (a + b) ∈ IntAf I.F I.E
    rw [DictLat.hhat_add_right]; exact add_mem ha hb
  zero_mem' := by
    show hhat I y 0 ∈ IntAf I.F I.E
    rw [DictLat.hhat_zero_right]; exact zero_mem _
  smul_mem' := fun r z hz => by
    show hhat I y ((r : I.E ⊗[I.F] Af I.F) • z) ∈ IntAf I.F I.E
    rw [DictLat.hhat_smul_right]; exact mul_mem r.2 hz
def dualL (I : AutInst) (z : Fin I.n → I.E ⊗[I.F] Af I.F) :
    Submodule (IntAf I.F I.E) (Fin I.n → I.E ⊗[I.F] Af I.F) where
  carrier := {y | hhat I y z ∈ IntAf I.F I.E}
  add_mem' := fun {a b} ha hb => by
    show hhat I (a + b) z ∈ IntAf I.F I.E
    rw [DictLat.hhat_add_left]; exact add_mem ha hb
  zero_mem' := by
    show hhat I 0 z ∈ IntAf I.F I.E
    rw [DictLat.hhat_zero_left]; exact zero_mem _
  smul_mem' := fun r y hy => by
    show hhat I ((r : I.E ⊗[I.F] Af I.F) • y) z ∈ IntAf I.F I.E
    rw [DictLat.hhat_smul_left]; exact mul_mem (DictLat.sigR_int I r.2) hy
def denomSub (I : AutInst) (h : DDenom) :
    Submodule (I.E ⊗[I.F] Af I.F) (Fin I.n → I.E ⊗[I.F] Af I.F) where
  carrier := {y | ∃ m : ℕ, 0 < m ∧ (m : I.E ⊗[I.F] Af I.F) • y ∈ I.Lf}
  add_mem' := by
    rintro a b ⟨m, hm, ha⟩ ⟨k, hk, hb⟩
    refine ⟨m * k, Nat.mul_pos hm hk, ?_⟩
    have e : ((m * k : ℕ) : I.E ⊗[I.F] Af I.F) • (a + b) =
        (k : I.E ⊗[I.F] Af I.F) • ((m : I.E ⊗[I.F] Af I.F) • a) +
          (m : I.E ⊗[I.F] Af I.F) • ((k : I.E ⊗[I.F] Af I.F) • b) := by
      funext i; simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Nat.cast_mul]; ring
    rw [e]
    exact add_mem (DictLat.Lf_smul I (natCast_mem _ k) ha) (DictLat.Lf_smul I (natCast_mem _ m) hb)
  zero_mem' := ⟨1, one_pos, by rw [smul_zero]; exact I.Lf.zero_mem⟩
  smul_mem' := by
    rintro r y ⟨m, hm, hy⟩
    obtain ⟨d, hd, hdr⟩ := h I.F I.E r
    refine ⟨d * m, Nat.mul_pos hd hm, ?_⟩
    have e : ((d * m : ℕ) : I.E ⊗[I.F] Af I.F) • (r • y) =
        ((d : I.E ⊗[I.F] Af I.F) * r) • ((m : I.E ⊗[I.F] Af I.F) • y) := by
      funext i; simp only [Pi.smul_apply, smul_eq_mul, Nat.cast_mul]; ring
    rw [e]
    exact DictLat.Lf_smul I hdr hy
def ivSub (I : AutInst) (p : Submodule (I.E ⊗[I.F] Af I.F) (Fin I.n → I.E ⊗[I.F] Af I.F)) :
    Submodule I.E (Fin I.n → I.E) where
  carrier := {v | iv I v ∈ p}
  add_mem' := fun {a b} ha hb => by
    show iv I (a + b) ∈ p
    rw [DictLat.iv_add]; exact p.add_mem ha hb
  zero_mem' := by
    show iv I 0 ∈ p
    rw [DictLat.iv_zero]; exact p.zero_mem
  smul_mem' := fun c v hv => by
    show iv I (c • v) ∈ p
    rw [DictLat.iv_smulE]; exact p.smul_mem _ hv
def denseSub (I : AutInst) (N : ℕ) (h : DDense) (hN : 0 < N) :
    Submodule (IntAf I.F I.E) (Fin I.n → I.E ⊗[I.F] Af I.F) where
  carrier := {y | ∃ l ∈ I.L, ∃ y' ∈ I.Lf, y = iv I l + (N : I.E ⊗[I.F] Af I.F) • y'}
  add_mem' := by
    rintro a b ⟨l, hl, a', ha', rfl⟩ ⟨m, hm, b', hb', rfl⟩
    refine ⟨l + m, I.L.add_mem hl hm, a' + b', I.Lf.add_mem ha' hb', ?_⟩
    rw [DictLat.iv_add, smul_add]; abel
  zero_mem' := ⟨0, I.L.zero_mem, 0, I.Lf.zero_mem, by rw [DictLat.iv_zero, smul_zero, add_zero]⟩
  smul_mem' := by
    rintro r _ ⟨l, hl, y', hy', rfl⟩
    obtain ⟨a, r', hr', hr⟩ := h I.F I.E N hN r r.2
    refine ⟨a • l, I.L.smul_mem a hl, r' • iv I l + (r : I.E ⊗[I.F] Af I.F) • y',
      I.Lf.add_mem (DictLat.Lf_smul I hr' (DictLat.iv_mem I hl)) (DictLat.Lf_smul I r.2 hy'), ?_⟩
    show (r : I.E ⊗[I.F] Af I.F) • (iv I l + (N : I.E ⊗[I.F] Af I.F) • y') = _
    rw [DictLat.iv_smulO, hr]
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
end PIW.AdelClassFin


