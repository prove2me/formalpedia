-- Prove2me | Definitions.Def_Formalism_ResultantValuation_ResultantAdjugateProofs_Koszul
-- name    : Formalism_ResultantValuation_ResultantAdjugateProofs_Koszul
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:10:31.348814+00:00
-- url     : https://prove2.me/theorems/7d7b7d8c-cf19-4ca1-b2ca-3efdaa25681b
-- title:
--   Koszul
-- statement:
--   Definitions and structural lemmas for Koszul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ResultantValuation/ResultantAdjugateProofs/Koszul.lean

import Definitions.Def_Formalism_ResultantValuation_KoszulSecondDifferential
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
namespace Formalism.ResultantValuation
namespace KoszulProof
variable {k : Type} [Field k] {n : ℕ}
abbrev tT (k : Type) [Field k] (n : ℕ) : truncPoly k n := Ideal.Quotient.mk _ X
lemma tT_pow : (tT k n) ^ n = 0 := by
  rw [tT, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span rfl
lemma tT_pow_pred_mul (hn : 1 ≤ n) (a : truncPoly k n) :
    tT k n * (tT k n ^ (n - 1) * a) = 0 := by
  rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel hn, tT_pow, zero_mul]
abbrev tI (k : Type) [Field k] (n : ℕ) : Submodule (truncPoly k n) (truncPoly k n) :=
  Ideal.span {tT k n}
abbrev tK (k : Type) [Field k] (n : ℕ) : Submodule (truncPoly k n) (truncPoly k n) :=
  LinearMap.ker (tT k n • LinearMap.id : truncPoly k n →ₗ[truncPoly k n] truncPoly k n)
lemma mem_tK (z : truncPoly k n) : z ∈ tK k n ↔ tT k n * z = 0 := by
  simp [tK]
def powMap (hn : 1 ≤ n) : truncPoly k n →ₗ[truncPoly k n] tK k n :=
  LinearMap.codRestrict (tK k n) (tT k n ^ (n - 1) • LinearMap.id) (fun a => by
    rw [mem_tK]; simpa using tT_pow_pred_mul hn a)
end KoszulProof
namespace KoszulProof
variable {k : Type} [Field k] {n : ℕ}
lemma mem_ker_koszul_second_differential (r : ℕ) (x y : truncPoly k n) (v : (Fin r → truncPoly k n) × (Fin r → truncPoly k n)) :
    v ∈ LinearMap.ker (koszulSecondDifferential r x y) ↔ ∀ i, y * v.1 i - x * v.2 i = 0 := by
  rw [LinearMap.mem_ker, funext_iff]
  simp only [koszulSecondDifferential, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.fst_apply,
    LinearMap.snd_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
section Main
variable (hn : 1 ≤ n) (r : ℕ) (u : (truncPoly k n)ˣ) (w : truncPoly k n)
abbrev koszulSecondKernel : Submodule (truncPoly k n) ((Fin r → truncPoly k n) × (Fin r → truncPoly k n)) :=
  LinearMap.ker (koszulSecondDifferential r (tT k n * (u : truncPoly k n)) (tT k n * w))
def fA : koszulSecondKernel r u w →ₗ[truncPoly k n] (Fin r → truncPoly k n ⧸ tI k n) :=
  LinearMap.pi (fun i => (tI k n).mkQ ∘ₗ LinearMap.proj i ∘ₗ
    LinearMap.fst _ _ _ ∘ₗ (koszulSecondKernel r u w).subtype)
def gB : koszulSecondKernel r u w →ₗ[truncPoly k n] (Fin r → truncPoly k n) :=
  (w • LinearMap.fst _ _ _ - (u : truncPoly k n) • LinearMap.snd _ _ _) ∘ₗ (koszulSecondKernel r u w).subtype
lemma gB_apply (v : koszulSecondKernel r u w) (i : Fin r) :
    gB r u w v i = w * v.1.1 i - (u : truncPoly k n) * v.1.2 i := by
  simp [gB]
lemma gB_mem (v : koszulSecondKernel r u w) (i : Fin r) : gB r u w v i ∈ tK k n := by
  rw [mem_tK, gB_apply]
  have h := (mem_ker_koszul_second_differential r _ _ v.1).mp v.2 i
  linear_combination h
def fB : koszulSecondKernel r u w →ₗ[truncPoly k n] (Fin r → tK k n) :=
  LinearMap.pi (fun i => LinearMap.codRestrict (tK k n) (LinearMap.proj i ∘ₗ gB r u w)
    (fun v => by simpa using gB_mem r u w v i))
def fAB : koszulSecondKernel r u w →ₗ[truncPoly k n] (Fin r → truncPoly k n ⧸ tI k n) × (Fin r → tK k n) :=
  (fA r u w).prod (fB r u w)
end Main
end KoszulProof
end Formalism.ResultantValuation


