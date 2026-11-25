-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PDomination
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PDomination
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T06:10:48.117497+00:00
-- url     : https://prove2.me/theorems/c40c30ad-e286-4c74-9641-e3c82486d2f6
-- title:
--   PDomination
-- statement:
--   Definitions and structural lemmas for PDomination, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PDomination.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
namespace Domination
section Charts
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N N' : ℕ}
  {x : Fin (N + 1) → Ω} {x' : Fin (N' + 1) → Ω}
theorem mem_twistMod_zero_iff {R : Type*} [CommRing R] [Algebra R Ω] {y : Fin (N' + 1) → Ω}
    (J : Chart y) (z : Ω) : z ∈ twistMod R y 0 J ↔ z ∈ chartRing R y J := by
  obtain ⟨j, hj⟩ := J.2.1
  rw [twistMod_eq_span 0 J hj, zpow_zero, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    rw [chartRing_smul_def, mul_one]
    exact a.2
  · intro hz
    exact ⟨⟨z, hz⟩, by rw [chartRing_smul_def, mul_one]⟩
abbrev pullPow (x : Fin (N + 1) → Ω) (x' : Fin (N' + 1) → Ω) (n : ℕ) (J : Chart x') :
    Submodule (chartRing S x' J) Ω :=
  ((pullSys (S := S) x x').pow n).sub J
theorem pullPow_succ (n : ℕ) (J : Chart x') :
    pullPow (S := S) x x' (n + 1) J = Submodule.span _ {z | ∃ q ∈ (pullSys (S := S) x x').sub J,
      ∃ y ∈ pullPow (S := S) x x' n J, z = q • y} := rfl
theorem mem_pullPow_zero_iff (J : Chart x') (z : Ω) :
    z ∈ pullPow (S := S) x x' 0 J ↔ z ∈ chartRing S x' J :=
  mem_twistMod_zero_iff J z
theorem coord_mem_pullPow_one (J : Chart x') (l : Fin (N + 1)) : x l ∈ pullPow (S := S) x x' 1 J := by
  rw [pullPow_succ]
  exact Submodule.subset_span ⟨x l, Submodule.subset_span ⟨l, rfl⟩, 1,
    (mem_pullPow_zero_iff J 1).mpr (one_mem _), by rw [smul_eq_mul, mul_one]⟩
theorem mul_mem_pullPow (J : Chart x') {n : ℕ} {z : Ω} (hz : z ∈ pullPow (S := S) x x' n J) :
    ∀ (m : ℕ) {y : Ω}, y ∈ pullPow (S := S) x x' m J → z * y ∈ pullPow (S := S) x x' (n + m) J := by
  intro m
  induction m with
  | zero =>
    intro y hy
    have hy' := (mem_pullPow_zero_iff J y).mp hy
    have h : z * y = (⟨y, hy'⟩ : chartRing S x' J) • z := by
      rw [chartRing_smul_def, mul_comm]
    rw [h]
    exact Submodule.smul_mem _ _ hz
  | succ m ih =>
    intro y hy
    rw [pullPow_succ] at hy
    rw [← Nat.add_assoc, pullPow_succ]
    induction hy using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨q, hq, y', hy', rfl⟩ := hw
      refine Submodule.subset_span ⟨q, hq, z * y', ih hy', ?_⟩
      simp only [smul_eq_mul]
      ring
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [mul_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha =>
      have h : z * (c • a) = c • (z * a) := by simp only [chartRing_smul_def]; ring
      rw [h]
      exact Submodule.smul_mem _ _ ha
theorem pow_mem_pullPow (J : Chart x') (l : Fin (N + 1)) :
    ∀ n : ℕ, x l ^ n ∈ pullPow (S := S) x x' n J
  | 0 => by rw [pow_zero]; exact (mem_pullPow_zero_iff J 1).mpr (one_mem _)
  | n + 1 => by
    rw [pow_succ]
    exact mul_mem_pullPow J (pow_mem_pullPow J l n) 1 (coord_mem_pullPow_one J l)
theorem mem_ampleChart_iff (J : Chart x') (l : Fin (N + 1)) (a : Ω) :
    a ∈ ampleChart (pullSys (S := S) x x') 1 (x l) J ↔ ∃ n : ℕ, a * x l ^ n ∈ pullPow (S := S) x x' n J := by
  simp only [ampleChart, one_mul, Set.mem_ofPred_eq]
def ampleSub (J : Chart x') (l : Fin (N + 1)) : Subalgebra S Ω where
  carrier := ampleChart (pullSys (S := S) x x') 1 (x l) J
  mul_mem' := by
    intro a b ha hb
    rw [mem_ampleChart_iff] at ha hb ⊢
    obtain ⟨n, hn⟩ := ha
    obtain ⟨m, hm⟩ := hb
    refine ⟨n + m, ?_⟩
    have h := mul_mem_pullPow J hn m hm
    rw [show a * x l ^ n * (b * x l ^ m) = a * b * x l ^ (n + m) by ring] at h
    exact h
  add_mem' := by
    intro a b ha hb
    rw [mem_ampleChart_iff] at ha hb ⊢
    obtain ⟨n, hn⟩ := ha
    obtain ⟨m, hm⟩ := hb
    refine ⟨n + m, ?_⟩
    have h1 := mul_mem_pullPow J hn m (pow_mem_pullPow J l m)
    have h2 := mul_mem_pullPow J hm n (pow_mem_pullPow J l n)
    rw [Nat.add_comm m n] at h2
    have h := Submodule.add_mem _ h1 h2
    rw [show a * x l ^ n * x l ^ m + b * x l ^ m * x l ^ n = (a + b) * x l ^ (n + m) by ring] at h
    exact h
  algebraMap_mem' s := by
    show _ ∈ ampleChart _ _ _ _
    rw [mem_ampleChart_iff]
    refine ⟨0, ?_⟩
    rw [pow_zero, mul_one, mem_pullPow_zero_iff]
    exact Subalgebra.algebraMap_mem _ s
variable {i : Fin (N + 1)} (hi : x i ≠ 0) {j : Fin (N' + 1)} (hj : x' j ≠ 0)
variable (x') in

def domSub : Subalgebra (chartRing S x (singleChart hi)) Ω :=
  ⨅ J : Chart x', chartRing (chartRing S x (singleChart hi)) x' J
end Charts
section Clauses
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N N' : ℕ}
  {x : Fin (N + 1) → Ω} {x' : Fin (N' + 1) → Ω}
end Clauses
end Domination
end
end GroundTheory.Heights₂.Heights.Kleiman


