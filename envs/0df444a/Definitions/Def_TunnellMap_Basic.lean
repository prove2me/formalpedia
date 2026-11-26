-- Prove2me | Definitions.Def_TunnellMap_Basic
-- name    : TunnellMap_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:36:00.936666+00:00
-- url     : https://prove2.me/theorems/764ea140-292a-5f6e-b144-c41557a3bbc2
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Aakash Gurung (GrgAakash/tunnell-two-to-one-map; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Two-to-one executable map between Tunnell representation sets development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Basic.lean

import Mathlib
set_option autoImplicit true
namespace TunnellMap
structure Triple where
  x : ℤ
  y : ℤ
  z : ℤ
deriving DecidableEq
@[ext] theorem Triple.ext {p q : Triple} (hx : p.x = q.x) (hy : p.y = q.y)
    (hz : p.z = q.z) : p = q := by
  cases p
  cases q
  simp_all
def bForm (p : Triple) : ℤ :=
  2 * p.x ^ 2 + p.y ^ 2 + 8 * p.z ^ 2
def aForm (p : Triple) : ℤ :=
  2 * p.x ^ 2 + p.y ^ 2 + 32 * p.z ^ 2
def BRep (n : ℤ) := {p : Triple // bForm p = n}
def ARep (n : ℤ) := {p : Triple // aForm p = n}
def BOddRep (n : ℤ) :=
  {p : Triple // bForm p = n ∧ Odd p.z}
structure BEvenParam (n : ℤ) where
  x : ℤ
  y : ℤ
  w : ℤ
  equation : bForm ⟨x, y, 2 * w⟩ = n
def BEvenParam.asBRep {n : ℤ} (p : BEvenParam n) : BRep n :=
  ⟨⟨p.x, p.y, 2 * p.w⟩, p.equation⟩
def evenToA {n : ℤ} (p : BEvenParam n) : ARep n := by
  refine ⟨⟨p.x, p.y, p.w⟩, ?_⟩
  change 2 * p.x ^ 2 + p.y ^ 2 + 32 * p.w ^ 2 = n
  have h := p.equation
  change 2 * p.x ^ 2 + p.y ^ 2 + 8 * (2 * p.w) ^ 2 = n at h
  nlinarith
def aToEven {n : ℤ} (p : ARep n) : BEvenParam n := by
  refine ⟨p.1.x, p.1.y, p.1.z, ?_⟩
  change 2 * p.1.x ^ 2 + p.1.y ^ 2 + 8 * (2 * p.1.z) ^ 2 = n
  have h := p.2
  change 2 * p.1.x ^ 2 + p.1.y ^ 2 + 32 * p.1.z ^ 2 = n at h
  nlinarith
def evenEquiv (n : ℤ) : BEvenParam n ≃ ARep n where
  toFun := evenToA
  invFun := aToEven
  left_inv := by
    intro p
    cases p
    rfl
  right_inv := by
    intro p
    apply Subtype.ext
    rfl
end TunnellMap


