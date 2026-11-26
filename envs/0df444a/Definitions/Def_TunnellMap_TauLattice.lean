-- Prove2me | Definitions.Def_TunnellMap_TauLattice
-- name    : TunnellMap_TauLattice
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:52:03.626326+00:00
-- url     : https://prove2.me/theorems/b692bc5a-537a-5f93-9bd8-e7c3dee4967a
-- title:
--   Tau Lattice
-- statement:
--   Definitions and structural lemmas for Tau Lattice, from Aakash Gurung (GrgAakash/tunnell-two-to-one-map; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Two-to-one executable map between Tunnell representation sets development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/TauLattice.lean

import Definitions.Def_TunnellMap_AffineLattice
import Theorems.Thm_TunnellMap_dot_tau
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
def InTauLattice (r : Triple) : Prop := (2 : ℤ) ∣ r.x - r.z
instance inTauLatticeDecidable (r : Triple) : Decidable (InTauLattice r) := by
  unfold InTauLattice
  infer_instance
def tauInv (r : Triple) : Triple :=
  ⟨(r.x + r.z) / 2, r.y, (r.x - r.z) / 2⟩
theorem tau_mem (d : Triple) : InTauLattice (tau d) := by
  refine ⟨d.z, ?_⟩
  simp [InTauLattice, tau]
  ring
@[simp] theorem tauInv_tau (d : Triple) : tauInv (tau d) = d := by
  apply Triple.ext
  · simp only [tauInv, tau]
    rw [show (d.x + d.z + (d.x - d.z)) = 2 * d.x by ring]
    exact Int.mul_ediv_cancel_left d.x (by norm_num)
  · rfl
  · simp only [tauInv, tau]
    rw [show (d.x + d.z - (d.x - d.z)) = 2 * d.z by ring]
    exact Int.mul_ediv_cancel_left d.z (by norm_num)
theorem tau_tauInv {r : Triple} (hr : InTauLattice r) : tau (tauInv r) = r := by
  have hdiff : (2 : ℤ) ∣ r.x - r.z := hr
  have hsum : (2 : ℤ) ∣ r.x + r.z := by
    obtain ⟨k, hk⟩ := hdiff
    refine ⟨k + r.z, ?_⟩
    linarith
  have hdiffDiv : 2 * ((r.x - r.z) / 2) = r.x - r.z := by
    rw [mul_comm]
    exact Int.ediv_mul_cancel hdiff
  have hsumDiv : 2 * ((r.x + r.z) / 2) = r.x + r.z := by
    rw [mul_comm]
    exact Int.ediv_mul_cancel hsum
  apply Triple.ext
  · simp only [tau, tauInv]
    omega
  · rfl
  · simp only [tau, tauInv]
    omega
def tauEquiv : Triple ≃ {r : Triple // InTauLattice r} where
  toFun d := ⟨tau d, tau_mem d⟩
  invFun r := tauInv r.1
  left_inv := tauInv_tau
  right_inv := by
    intro r
    apply Subtype.ext
    exact tau_tauInv r.2
end TunnellMap


