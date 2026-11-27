-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SplitSubtorusOfIdempotentFamily
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_SplitSubtorusOfIdempotentFamily
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-27T06:27:37.865827+00:00
-- url     : https://prove2.me/theorems/7bd61cda-44e7-5a6f-8e07-52985c2fcbab
-- title:
--   Split Subtorus Of Idempotent Family
-- statement:
--   Definitions and structural lemmas for Split Subtorus Of Idempotent Family, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SplitSubtorusOfIdempotentFamily.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotCompactOfIdempotent
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
open Matrix Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct
namespace GlobalTheory.RegSS.IdemTorus
section Lin
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {ι : Type} [Fintype ι]
  [DecidableEq ι]
def idemLin (p : ι → Matrix n n A) (c : ι → A) : Matrix n n A := 1 + ∑ k, (c k - 1) • p k
theorem idemLin_mul_idem {p : ι → Matrix n n A} (hi : ∀ k, p k * p k = p k)
    (ho : ∀ k l, k ≠ l → p k * p l = 0) (c : ι → A) (k : ι) :
    idemLin p c * p k = c k • p k := by
  unfold idemLin
  rw [add_mul, one_mul, Finset.sum_mul, Finset.sum_eq_single k]
  · rw [smul_mul_assoc, hi, sub_smul, one_smul]; abel
  · intro l _ hl; rw [smul_mul_assoc, ho l k hl, smul_zero]
  · simp
theorem idemLin_mul {p : ι → Matrix n n A} (hi : ∀ k, p k * p k = p k)
    (ho : ∀ k l, k ≠ l → p k * p l = 0) (c c' : ι → A) :
    idemLin p (c * c') = idemLin p c * idemLin p c' := by
  have h : idemLin p c * idemLin p c' = idemLin p c + ∑ k, (c' k - 1) • (idemLin p c * p k) := by
    conv_lhs => rw [show idemLin p c' = 1 + ∑ k, (c' k - 1) • p k from rfl]
    rw [mul_add, mul_one, Finset.mul_sum]
    simp_rw [mul_smul_comm]
  rw [h]
  simp_rw [idemLin_mul_idem hi ho, smul_smul]
  unfold idemLin
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← add_smul]; congr 1; simp only [Pi.mul_apply]; ring
theorem idemLin_one (p : ι → Matrix n n A) : idemLin p 1 = 1 := by
  simp [idemLin]
end Lin
end GlobalTheory.RegSS.IdemTorus
namespace GlobalTheory.RegSS.IdemTorus
section Torus
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {n : Type} [Fintype n] [DecidableEq n]
def idemFam (σ : E →ₐ[F] E) (J : Matrix n n E) {s : ℕ} (ε : Fin s → Matrix n n E) :
    Fin s ⊕ Fin s → Matrix n n E :=
  Sum.elim ε (fun i => adj (σ : E →+* E) J (ε i))
def idemCoef (R : Type) [CommRing R] [Algebra F R] {s : ℕ} (t : Fin s → Rˣ) :
    Fin s ⊕ Fin s → E ⊗[F] R :=
  Sum.elim (fun i => (1 : E) ⊗ₜ[F] (t i : R)) (fun i => (1 : E) ⊗ₜ[F] (((t i)⁻¹ : Rˣ) : R))
theorem idemCoef_one (R : Type) [CommRing R] [Algebra F R] {s : ℕ} :
    idemCoef (F := F) (E := E) R (1 : Fin s → Rˣ) = 1 := by
  funext k; cases k <;> simp [idemCoef, Algebra.TensorProduct.one_def]
theorem idemCoef_mul (R : Type) [CommRing R] [Algebra F R] {s : ℕ} (a b : Fin s → Rˣ) :
    idemCoef (F := F) (E := E) R (a * b) = idemCoef R a * idemCoef R b := by
  funext k; cases k <;> simp [idemCoef, Algebra.TensorProduct.tmul_mul_tmul, mul_comm]
end Torus
end GlobalTheory.RegSS.IdemTorus
namespace GlobalTheory.RegSS.IdemTorus
section Main
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {n : Type} [Fintype n] [DecidableEq n]
def idemFamR (σ : E →ₐ[F] E) (J : Matrix n n E) {s : ℕ} (ε : Fin s → Matrix n n E) (R : Type)
    [CommRing R] [Algebra F R] : Fin s ⊕ Fin s → Matrix n n (E ⊗[F] R) :=
  fun k => (idemFam σ J ε k).map (inclE (F := F) R)
variable {σ : E →ₐ[F] E} {J : Matrix n n E} {s : ℕ} {ε : Fin s → Matrix n n E}
theorem idemFamR_idem (hi : ∀ k, idemFam σ J ε k * idemFam σ J ε k = idemFam σ J ε k)
    (R : Type) [CommRing R] [Algebra F R] (k : Fin s ⊕ Fin s) :
    idemFamR σ J ε R k * idemFamR σ J ε R k = idemFamR σ J ε R k := by
  simp only [idemFamR]; rw [← Matrix.map_mul, hi]
theorem idemFamR_orth (ho : ∀ k l, k ≠ l → idemFam σ J ε k * idemFam σ J ε l = 0)
    (R : Type) [CommRing R] [Algebra F R] (k l : Fin s ⊕ Fin s) (hkl : k ≠ l) :
    idemFamR σ J ε R k * idemFamR σ J ε R l = 0 := by
  simp only [idemFamR]; rw [← Matrix.map_mul, ho k l hkl, Matrix.map_zero _ (map_zero _)]
def idemHom (hi : ∀ k, idemFam σ J ε k * idemFam σ J ε k = idemFam σ J ε k)
    (ho : ∀ k l, k ≠ l → idemFam σ J ε k * idemFam σ J ε l = 0) (R : Type) [CommRing R]
    [Algebra F R] : (Fin s → Rˣ) →* Matrix n n (E ⊗[F] R) where
  toFun t := idemLin (idemFamR σ J ε R) (idemCoef R t)
  map_one' := by simp only [idemCoef_one]; exact idemLin_one _
  map_mul' a b := by
    simp only [idemCoef_mul]
    exact idemLin_mul (idemFamR_idem hi R) (idemFamR_orth ho R) _ _
end Main
end GlobalTheory.RegSS.IdemTorus


