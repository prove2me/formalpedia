-- Prove2me | Definitions.Def_RequestProject_TPSSefxConfig
-- name    : RequestProject_TPSSefxConfig
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:18:09.583803+00:00
-- url     : https://prove2.me/theorems/ec4f080d-f3b9-47cc-a21c-53d6f843a9d0
-- title:
--   TPSSefx Config
-- statement:
--   Definitions and structural lemmas for TPSSefx Config, from yotam-gafni/FairAllocationWithOptionalSelling contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Fair allocation with optional selling and maximin-share bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxConfig.lean

import Mathlib
import Definitions.Def_RequestProject_TPSSefxCharge
import Definitions.Def_RequestProject_TPSSefxServe
set_option autoImplicit true
open scoped BigOperators
namespace FairSelling
namespace CfgTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
section Defs
variable (w : Fin n → G → ℝ) (p : G → ℝ) (req : Fin n → ℝ) (k0 : Fin n)
noncomputable def gapMin (S : Finset G) : ℝ :=
  Finset.univ.inf' ⟨k0, Finset.mem_univ k0⟩ (fun m => req m - vbarSum (w m) p S)
noncomputable def Qc (S : Finset G) : ℝ := max 0 (gapMin w p req k0 S)
def Feas (D : ℝ) (S S₀ : Finset G) : Prop := Qc w p req k0 S ≤ D + ∑ g ∈ S₀, p g
def Adm (D : ℝ) (S S₀ : Finset G) : Prop :=
  Feas w p req k0 D S S₀ ∧
  ∀ X ⊆ S, X.Nonempty → ∀ m,
    vbarSum (w m) p (S \ X) + (∑ g ∈ X, p g) + Qc w p req k0 S ≤ req m
end Defs
section Basic
variable (w : Fin n → G → ℝ) (p : G → ℝ) (req : Fin n → ℝ) (k0 : Fin n)
end Basic
section Shrink
variable (w : Fin n → G → ℝ) (p : G → ℝ) (req : Fin n → ℝ) (k0 : Fin n) (D : ℝ)
end Shrink
section Minimal
variable (w : Fin n → G → ℝ) (p : G → ℝ) (req : Fin n → ℝ) (k0 : Fin n) (D : ℝ)
variable {w p req k0 D}
end Minimal
section Cost
variable {w : Fin n → G → ℝ} {p : G → ℝ} {req : Fin n → ℝ} {k0 : Fin n} {D : ℝ}
end Cost
end CfgTPS
end FairSelling


