-- Prove2me | Definitions.Def_SmallRatio_Defs
-- name    : SmallRatio_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T21:12:28.904921+00:00
-- url     : https://prove2.me/theorems/7b65b286-958b-4425-ba8b-dd50be676061
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from J. S. Farland (jkfarland-bot/SmallRatios; see pinned Apache-2.0 LICENSE and README.md)'s pinned SmallRatio: Dedekind sums along Euclid's algorithm and the small-ratio theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Defs.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace SmallRatio
open Finset
noncomputable def sawtooth (x : ℚ) : ℚ := if Int.fract x = 0 then 0 else Int.fract x - 1 / 2
noncomputable def dedekindSum (h k : ℕ) : ℚ :=
  ∑ r ∈ range k, sawtooth ((r : ℚ) / k) * sawtooth ((h * r : ℚ) / k)
def rem (k h : ℕ) : ℕ → ℕ
  | 0 => k
  | 1 => h
  | j + 2 => rem k h j % rem k h (j + 1)
def den (k h : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | j + 2 => rem k h j / rem k h (j + 1) * den k h (j + 1) + den k h j
def steps (k h : ℕ) : ℕ := Nat.find (⟨k + 1, Or.inr rfl⟩ : ∃ j, rem k h j ≤ 1 ∨ j = k + 1)
noncomputable def smallRatioSum (p h : ℕ) : ℚ :=
  ∑ u ∈ Icc 1 p, ∑ v ∈ Icc 1 p,
    if Nat.Coprime u v ∧ 2 * u * v < p then
      ((if ((h * v : ℕ) : ZMod p) = (u : ZMod p) then 1 else 0) -
        (if ((h * v : ℕ) : ZMod p) = -(u : ZMod p) then 1 else 0)) / ((u : ℚ) * v)
    else 0
noncomputable def subgroupSmallRatio (p : ℕ) (H : Finset (ZMod p)) : ℚ :=
  ∑ u ∈ Icc 1 p, ∑ v ∈ Icc 1 p,
    if Nat.Coprime u v ∧ 2 * u * v < p then
      ((if (u : ZMod p) * (v : ZMod p)⁻¹ ∈ H then 1 else 0) -
        (if -((u : ZMod p) * (v : ZMod p)⁻¹) ∈ H then 1 else 0)) / ((u : ℚ) * v)
    else 0
end SmallRatio


