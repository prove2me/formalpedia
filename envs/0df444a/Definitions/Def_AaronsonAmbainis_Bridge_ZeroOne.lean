-- Prove2me | Definitions.Def_AaronsonAmbainis_Bridge_ZeroOne
-- name    : AaronsonAmbainis_Bridge_ZeroOne
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T22:47:40.580113+00:00
-- url     : https://prove2.me/theorems/00bab22e-7561-43e0-90ef-f3941aa7ff5e
-- title:
--   Zero One
-- statement:
--   Definitions and structural lemmas for Zero One, from David Turturean / physical-superintelligence; see upstream NOTICE for AI disclosure and mathematical attributions's pinned Aaronson–Ambainis development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/ZeroOne.lean

import Definitions.Def_AaronsonAmbainis_Bridge_Basic
set_option autoImplicit true
namespace AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
noncomputable def mon (φ : Bool → ℝ) (S : Finset ι) (x : Cube ι) : ℝ := ∏ i ∈ S, φ (x i)
def HasDegLE (φ : Bool → ℝ) (f : Cube ι → ℝ) (d : ℕ) : Prop :=
  ∃ c : Finset ι → ℝ, (∀ S, d < S.card → c S = 0) ∧ ∀ x, f x = ∑ S, c S * mon φ S x
def HasDegreeLE01 (f : Cube ι → ℝ) (d : ℕ) : Prop :=
  ∃ c : Finset ι → ℝ, (∀ S, d < S.card → c S = 0) ∧
    ∀ x, f x = ∑ S, c S * ∏ i ∈ S, (if x i then (1 : ℝ) else 0)
end AaronsonAmbainis.Bridge


