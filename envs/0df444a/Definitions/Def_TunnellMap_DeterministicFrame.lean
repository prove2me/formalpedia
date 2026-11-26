-- Prove2me | Definitions.Def_TunnellMap_DeterministicFrame
-- name    : TunnellMap_DeterministicFrame
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:59:14.107275+00:00
-- url     : https://prove2.me/theorems/be72f87a-4682-5d07-bc7e-20551f48b5f9
-- title:
--   Deterministic Frame
-- statement:
--   Definitions and structural lemmas for Deterministic Frame, from Aakash Gurung (GrgAakash/tunnell-two-to-one-map; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Two-to-one executable map between Tunnell representation sets development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeterministicFrame.lean

import Definitions.Def_TunnellMap_OrthogonalFrameExistence
import Theorems.Thm_TunnellMap_dot_tau
import Theorems.Thm_TunnellMap_dot_tripleBezout_of_gcd_eq_one
import Theorems.Thm_TunnellMap_evenEquiv_apply
import Theorems.Thm_TunnellMap_evenEquiv_symm_apply
import Theorems.Thm_TunnellMap_qForm_aLift
import Theorems.Thm_TunnellMap_qForm_bLift
import Theorems.Thm_TunnellMap_qForm_tau
attribute [local simp] TunnellMap.dot_tau
attribute [local simp] TunnellMap.evenEquiv_apply
attribute [local simp] TunnellMap.evenEquiv_symm_apply
attribute [local simp] TunnellMap.qForm_aLift
attribute [local simp] TunnellMap.qForm_bLift
attribute [local simp] TunnellMap.qForm_tau


set_option autoImplicit true
namespace TunnellMap
def span2 (a b : ℤ) (u v : Triple) : Triple := vadd (vsmul a u) (vsmul b v)
@[simp] theorem span2_apply (a b : ℤ) (u v : Triple) :
    span2 a b u v = ⟨a * u.x + b * v.x, a * u.y + b * v.y, a * u.z + b * v.z⟩ :=
  rfl
def frameE₁ (p : Triple) : Triple :=
  if (Int.gcd p.x p.y : ℤ) = 0 then
    (if 0 < p.z then ⟨1, 0, 0⟩ else ⟨0, 1, 0⟩)
  else
    ⟨-(p.y / (Int.gcd p.x p.y : ℤ)), p.x / (Int.gcd p.x p.y : ℤ), 0⟩
def frameE₂ (p : Triple) : Triple :=
  if (Int.gcd p.x p.y : ℤ) = 0 then
    (if 0 < p.z then ⟨0, 1, 0⟩ else ⟨1, 0, 0⟩)
  else
    ⟨-(p.x.gcdA p.y) * p.z, -(p.x.gcdB p.y) * p.z, (Int.gcd p.x p.y : ℤ)⟩
theorem gcd_xy_eq_zero_cases {p : Triple} (hp : tripleGCD p = 1)
    (h0 : (Int.gcd p.x p.y : ℤ) = 0) : p.x = 0 ∧ p.y = 0 ∧ (p.z = 1 ∨ p.z = -1) := by
  have h0' : Int.gcd p.x p.y = 0 := by exact_mod_cast h0
  obtain ⟨hx, hy⟩ := Int.gcd_eq_zero_iff.mp h0'
  refine ⟨hx, hy, ?_⟩
  have : Int.gcd (0 : ℤ) p.z = 1 := by
    have := hp
    unfold tripleGCD at this
    rwa [h0'] at this
  simp only [Int.gcd_zero_left] at this
  omega
theorem cross_frameE₁_frameE₂ {p : Triple} (hp : tripleGCD p = 1) :
    cross (frameE₁ p) (frameE₂ p) = p := by
  by_cases h0 : (Int.gcd p.x p.y : ℤ) = 0
  · obtain ⟨hx, hy, hz⟩ := gcd_xy_eq_zero_cases hp h0
    rcases hz with hz | hz
    · have hzpos : 0 < p.z := by omega
      simp only [frameE₁, frameE₂, if_pos h0, if_pos hzpos]
      apply Triple.ext <;> simp [cross, hx, hy, hz]
    · have hzpos : ¬ (0 < p.z) := by omega
      simp only [frameE₁, frameE₂, if_pos h0, if_neg hzpos]
      apply Triple.ext <;> simp [cross, hx, hy, hz]
  · simp only [frameE₁, frameE₂, if_neg h0]
    set G : ℤ := (Int.gcd p.x p.y : ℤ) with hG
    set A : ℤ := p.x.gcdA p.y with hA
    set B : ℤ := p.x.gcdB p.y with hB
    set a : ℤ := p.x / G with ha
    set b : ℤ := p.y / G with hb
    have hxDiv : G * a = p.x := by
      rw [ha, mul_comm]
      exact Int.ediv_mul_cancel (Int.gcd_dvd_left p.x p.y)
    have hyDiv : G * b = p.y := by
      rw [hb, mul_comm]
      exact Int.ediv_mul_cancel (Int.gcd_dvd_right p.x p.y)
    have hBezout : G = p.x * A + p.y * B := Int.gcd_eq_gcd_ab p.x p.y
    have hAB : A * a + B * b = 1 := by
      apply mul_left_cancel₀ h0
      calc
        G * (A * a + B * b) = (G * a) * A + (G * b) * B := by ring
        _ = p.x * A + p.y * B := by rw [hxDiv, hyDiv]
        _ = G := hBezout.symm
        _ = G * 1 := by ring
    apply Triple.ext
    · dsimp only [cross]
      linear_combination hxDiv
    · dsimp only [cross]
      linear_combination hyDiv
    · dsimp only [cross]
      linear_combination p.z * hAB
def orthogonalFrameExec (p : Triple) (hp : tripleGCD p = 1) : OrthogonalFrame p where
  e₁ := frameE₁ p
  e₂ := frameE₂ p
  z := tripleBezout p
  cross_eq := cross_frameE₁_frameE₂ hp
  bezout := dot_tripleBezout_of_gcd_eq_one hp
section Frame
variable {p : Triple} (F : OrthogonalFrame p)
end Frame
section Exec
variable {p : Triple}
end Exec
section Change
variable {p : Triple} (F G : OrthogonalFrame p)
end Change
end TunnellMap


