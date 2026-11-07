-- Prove2me | Definitions.Def_AaronsonAmbainis_Bridge_Transport
-- name    : AaronsonAmbainis_Bridge_Transport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T22:48:20.094952+00:00
-- url     : https://prove2.me/theorems/0bd331e2-b986-49ac-9b33-39f562593942
-- title:
--   Transport
-- statement:
--   Definitions and structural lemmas for Transport, from David Turturean / physical-superintelligence; see upstream NOTICE for AI disclosure and mathematical attributions's pinned Aaronson–Ambainis development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Transport.lean

import Definitions.Def_AaronsonAmbainis_Bridge_Basic
set_option autoImplicit true
namespace AaronsonAmbainis.Bridge
open Finset
def RowBoundFin : Prop :=
  ∀ (n d : ℕ) (f : Cube (Fin n) → ℝ), (∀ x, 0 ≤ f x ∧ f x ≤ 1) → HasDegreeLE f d →
    ∃ c : Cube (Fin n) → Fin n → ℝ,
      (∀ x y, |f x - f y| ≤ ∑ i ∈ diffSet x y, c x i) ∧
      (∀ x, ∑ i, c x i ≤ Real.pi ^ 2 / 4 * (d : ℝ) ^ 2)
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
end AaronsonAmbainis.Bridge


