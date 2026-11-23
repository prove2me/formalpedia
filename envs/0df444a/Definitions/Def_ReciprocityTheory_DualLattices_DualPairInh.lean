-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_DualPairInh
-- name    : ReciprocityTheory_DualLattices_DualPairInh
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:16:55.985285+00:00
-- url     : https://prove2.me/theorems/d5763ebb-fd83-4167-9244-5c386cca547c
-- title:
--   Dual Pair Inh
-- statement:
--   Definitions and structural lemmas for Dual Pair Inh, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DualPairInh.lean

import Definitions.Def_ReciprocityTheory_DualLattices_ModuliPointsState
import Definitions.Def_ReciprocityTheory_DualLattices_AinfFacts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
namespace ReciprocityTheory.PGsh
namespace DualNum
variable {R₀ : Type} [CommRing R₀] (R : LAlg R₀)
abbrev DN := (R : Type)[X] ⧸ Ideal.span {(X : (R : Type)[X]) ^ 2}
def ev : DN R →+* (R : Type) :=
  Ideal.Quotient.lift _ (Polynomial.evalRingHom 0) (fun a ha => by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    simp)
lemma ev_mk (f : (R : Type)[X]) : ev R (Ideal.Quotient.mk _ f) = f.eval 0 := rfl
lemma ev_surj : Function.Surjective (ev R) := fun r => ⟨Ideal.Quotient.mk _ (C r), by rw [ev_mk, eval_C]⟩
def eta : DN R := Ideal.Quotient.mk _ X
lemma eta_sq : eta R * eta R = 0 := by
  unfold eta
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, ← pow_two]
  exact Ideal.mem_span_singleton_self _
lemma ker_ev : RingHom.ker (ev R) = Ideal.span {eta R} := by
  apply le_antisymm
  · intro y hy
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [RingHom.mem_ker, ev_mk] at hy
    have hX : (X : (R : Type)[X]) ∣ f := by
      rw [Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero]
      exact hy
    obtain ⟨g, rfl⟩ := hX
    rw [map_mul]
    exact Ideal.mem_span_singleton.2 (dvd_mul_right (eta R) _)
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    show ev R (eta R) = 0
    rw [eta, ev_mk, eval_X]
lemma isLocal : IsLocalRing (DN R) := by
  have hnt : Nontrivial (DN R) := (ev R).domain_nontrivial
  have hunit : ∀ y : DN R, IsUnit (ev R y) → IsUnit y := by
    intro y hy
    obtain ⟨u, hu⟩ : ∃ u : DN R, u = Ideal.Quotient.mk _ (C (ev R y)) := ⟨_, rfl⟩
    have hev : ev R u = ev R y := by rw [hu, ev_mk, eval_C]
    have hk : y - u ∈ RingHom.ker (ev R) := by rw [RingHom.mem_ker, map_sub, hev, sub_self]
    rw [ker_ev, Ideal.mem_span_singleton] at hk
    obtain ⟨c, hc⟩ := hk
    have hn : IsNilpotent (y - u) := ⟨2, by rw [hc, mul_pow, pow_two (eta R), eta_sq, zero_mul]⟩
    have hu' : IsUnit u := by
      have e : u = ((Ideal.Quotient.mk _).comp Polynomial.C) (ev R y) := hu
      rw [e]
      exact hy.map _
    have h := hn.isUnit_add_left_of_commute hu' (Commute.all _ _)
    rwa [add_sub_cancel] at h
  exact IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a =>
    (IsLocalRing.isUnit_or_isUnit_one_sub_self (ev R a)).imp (hunit a)
      fun h => hunit (1 - a) (by rwa [map_sub, map_one])
lemma ev_algebraMap (r : (R : Type)) : ev R (algebraMap (R : Type) (DN R) r) = r := by
  rw [← Ideal.Quotient.mk_algebraMap, ev_mk]
  simp
def evAlg : DN R →ₐ[R₀] (R : Type) :=
  { ev R with
    commutes' := fun r => by
      show ev R (algebraMap R₀ (DN R) r) = _
      rw [← Ideal.Quotient.mk_algebraMap, ev_mk, Polynomial.algebraMap_apply, eval_C] }
def D : LAlg R₀ := { carrier := DN R, loc := isLocal R }
def dualPair : DualPair R where
  D := D R
  π := ⟨evAlg R, TowerExample.isLocalHom_of_surj _ (ev_surj R)⟩
  σ := ⟨IsScalarTower.toAlgHom R₀ (R : Type) (DN R),
    ⟨fun r hr => by
      have h := hr.map (ev R)
      have e : ev R ((IsScalarTower.toAlgHom R₀ (R : Type) (DN R) : (R : Type) →+* DN R) r) = r :=
        ev_algebraMap R r
      convert h using 1
      exact e.symm⟩⟩
  η := eta R
  sect r := ev_algebraMap R r
  η_sq := eta_sq R
  ker_eq := ker_ev R
  free r h := by
    change algebraMap (R : Type) (DN R) r * eta R = 0 at h
    rw [← Ideal.Quotient.mk_algebraMap, eta, ← map_mul, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_span_singleton, X_pow_dvd_iff] at h
    have h1 := h 1 (by norm_num)
    simpa [Polynomial.algebraMap_apply] using h1
end DualNum
end ReciprocityTheory.PGsh


