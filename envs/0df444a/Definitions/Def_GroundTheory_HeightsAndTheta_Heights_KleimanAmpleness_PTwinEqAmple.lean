-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTwinEqAmple
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTwinEqAmple
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:54:13.042007+00:00
-- url     : https://prove2.me/theorems/db107a3d-ae9e-462d-b789-abdfde0b9ecd
-- title:
--   PTwin Eq Ample
-- statement:
--   Definitions and structural lemmas for PTwin Eq Ample, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTwinEqAmple.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ImportsLastLast
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_mul_eq_twist_18fb89964ed5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_pow_zero_sub_b7a88b6ce0bd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
open MvPolynomial
section AmpleProof
variable {S : Type} [CommRing S] {N : ℕ} {Ω : Type} [Field Ω] [Algebra S Ω] {x : Fin (N + 1) → Ω}
theorem pow_mul_pow_le (Q : Kleiman.SubSystem S x Ω) (I : Kleiman.Chart x) (a b : ℕ) :
    ((Q.pow a).sub I).restrictScalars S * ((Q.pow b).sub I).restrictScalars S ≤
      ((Q.pow (a + b)).sub I).restrictScalars S := by
  induction b with
  | zero =>
    rw [Submodule.mul_le]
    intro p hp q hq
    rw [Submodule.restrictScalars_mem, pow_zero_sub] at hq
    rw [Submodule.restrictScalars_mem] at hp ⊢
    rw [Nat.add_zero, mul_comm]
    have := Submodule.smul_mem _ (⟨q, hq⟩ : Kleiman.chartRing S x I) hp
    rwa [Kleiman.chartRing_smul_def] at this
  | succ b ih =>
    have h1 : ((Q.pow (b + 1)).sub I).restrictScalars S =
        ((Q.pow b).sub I).restrictScalars S * (Q.sub I).restrictScalars S :=
      (mul_eq_twist (Q.pow b) Q I).symm
    have h2 : ((Q.pow (a + (b + 1))).sub I).restrictScalars S =
        ((Q.pow (a + b)).sub I).restrictScalars S * (Q.sub I).restrictScalars S :=
      (mul_eq_twist (Q.pow (a + b)) Q I).symm
    rw [h1, h2, ← mul_assoc]
    exact mul_le_mul' ih le_rfl
theorem mul_mem_pow (Q : Kleiman.SubSystem S x Ω) (I : Kleiman.Chart x) {a b : ℕ} {p q : Ω}
    (hp : p ∈ (Q.pow a).sub I) (hq : q ∈ (Q.pow b).sub I) : p * q ∈ (Q.pow (a + b)).sub I :=
  pow_mul_pow_le Q I a b (Submodule.mul_mem_mul (M := ((Q.pow a).sub I).restrictScalars S)
    (N := ((Q.pow b).sub I).restrictScalars S) hp hq)
theorem pow_mem_pow (Q : Kleiman.SubSystem S x Ω) (I : Kleiman.Chart x) {m : ℕ} {h : Ω}
    (hh : h ∈ (Q.pow m).sub I) (n : ℕ) : h ^ n ∈ (Q.pow (m * n)).sub I := by
  induction n with
  | zero =>
    rw [pow_zero, Nat.mul_zero, pow_zero_sub]
    exact one_mem _
  | succ n ih =>
    rw [pow_succ, Nat.mul_succ]
    exact mul_mem_pow Q I ih hh
def ampleSub (Q : Kleiman.SubSystem S x Ω) (m : ℕ) (h : Ω) (hh : ∀ I, h ∈ (Q.pow m).sub I) :
    Subalgebra S Ω where
  carrier := Kleiman.ampleRing Q m h
  mul_mem' := by
    intro a b ha hb
    refine Set.mem_iInter.mpr fun I => ?_
    obtain ⟨n, hn⟩ := Set.mem_iInter.mp ha I
    obtain ⟨n', hn'⟩ := Set.mem_iInter.mp hb I
    refine ⟨n + n', ?_⟩
    have e : a * b * h ^ (n + n') = a * h ^ n * (b * h ^ n') := by ring
    rw [e, Nat.mul_add]
    exact mul_mem_pow Q I hn hn'
  add_mem' := by
    intro a b ha hb
    refine Set.mem_iInter.mpr fun I => ?_
    obtain ⟨n, hn⟩ := Set.mem_iInter.mp ha I
    obtain ⟨n', hn'⟩ := Set.mem_iInter.mp hb I
    refine ⟨n + n', ?_⟩
    have e : (a + b) * h ^ (n + n') = a * h ^ n * h ^ n' + b * h ^ n' * h ^ n := by ring
    rw [e, Nat.mul_add]
    refine add_mem (mul_mem_pow Q I hn (pow_mem_pow Q I (hh I) n')) ?_
    rw [Nat.add_comm (m * n)]
    exact mul_mem_pow Q I hn' (pow_mem_pow Q I (hh I) n)
  algebraMap_mem' s := by
    refine Set.mem_iInter.mpr fun I => ⟨0, ?_⟩
    rw [pow_zero, mul_one, Nat.mul_zero, pow_zero_sub]
    exact Subalgebra.algebraMap_mem _ s
end AmpleProof
end GroundTheory.Heights₂.Heights.Kleiman.TranslateEq


