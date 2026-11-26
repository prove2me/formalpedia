-- Prove2me | Definitions.Def_TunnellMap_Finiteness
-- name    : TunnellMap_Finiteness
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:48:26.303808+00:00
-- url     : https://prove2.me/theorems/eb8b205f-7038-4d28-bfff-3ecba32efd20
-- title:
--   Finiteness
-- statement:
--   Definitions and structural lemmas for Finiteness, from Aakash Gurung (GrgAakash/tunnell-two-to-one-map; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Two-to-one executable map between Tunnell representation sets development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Finiteness.lean

import Definitions.Def_TunnellMap_Basic
set_option autoImplicit true
namespace TunnellMap
theorem coordinate_bounds_of_sq_le {x n : ℤ} (hn : 0 ≤ n) (hxn : x ^ 2 ≤ n) :
    -n ≤ x ∧ x ≤ n := by
  constructor
  · by_contra h
    have hx : n + 1 ≤ -x := by omega
    have hleft : 0 ≤ -x - (n + 1) := by omega
    have hright : 0 ≤ -x + (n + 1) := by omega
    have hprod := mul_nonneg hleft hright
    nlinarith
  · by_contra h
    have hx : n + 1 ≤ x := by omega
    have hleft : 0 ≤ x - (n + 1) := by omega
    have hright : 0 ≤ x + (n + 1) := by omega
    have hprod := mul_nonneg hleft hright
    nlinarith
def bRepBounded (n : ℤ) (p : BRep n) :
    Set.Icc (-n) n × Set.Icc (-n) n × Set.Icc (-n) n := by
  have hform := p.2
  change 2 * p.1.x ^ 2 + p.1.y ^ 2 + 8 * p.1.z ^ 2 = n at hform
  have hn : 0 ≤ n := by
    nlinarith [sq_nonneg p.1.x, sq_nonneg p.1.y, sq_nonneg p.1.z]
  have hxsq : p.1.x ^ 2 ≤ n := by
    nlinarith [sq_nonneg p.1.y, sq_nonneg p.1.z]
  have hysq : p.1.y ^ 2 ≤ n := by
    nlinarith [sq_nonneg p.1.x, sq_nonneg p.1.z]
  have hzsq : p.1.z ^ 2 ≤ n := by
    nlinarith [sq_nonneg p.1.x, sq_nonneg p.1.y, sq_nonneg p.1.z]
  exact ⟨⟨p.1.x, coordinate_bounds_of_sq_le hn hxsq⟩,
    ⟨p.1.y, coordinate_bounds_of_sq_le hn hysq⟩,
    ⟨p.1.z, coordinate_bounds_of_sq_le hn hzsq⟩⟩
theorem bRepBounded_injective (n : ℤ) :
    Function.Injective (bRepBounded n) := by
  intro p q h
  apply Subtype.ext
  apply Triple.ext
  · have hx := congrArg (fun r => r.1.1) h
    change p.1.x = q.1.x at hx
    exact hx
  · have hy := congrArg (fun r => r.2.1.1) h
    change p.1.y = q.1.y at hy
    exact hy
  · have hz := congrArg (fun r => r.2.2.1) h
    change p.1.z = q.1.z at hz
    exact hz
instance bRepFinite (n : ℤ) : Finite (BRep n) :=
  Finite.of_injective (bRepBounded n) (bRepBounded_injective n)
noncomputable instance bRepFintype (n : ℤ) : Fintype (BRep n) :=
  Fintype.ofFinite _
def aRepBounded (n : ℤ) (p : ARep n) :
    Set.Icc (-n) n × Set.Icc (-n) n × Set.Icc (-n) n := by
  have hform := p.2
  change 2 * p.1.x ^ 2 + p.1.y ^ 2 + 32 * p.1.z ^ 2 = n at hform
  have hn : 0 ≤ n := by
    nlinarith [sq_nonneg p.1.x, sq_nonneg p.1.y, sq_nonneg p.1.z]
  have hxsq : p.1.x ^ 2 ≤ n := by
    nlinarith [sq_nonneg p.1.y, sq_nonneg p.1.z]
  have hysq : p.1.y ^ 2 ≤ n := by
    nlinarith [sq_nonneg p.1.x, sq_nonneg p.1.z]
  have hzsq : p.1.z ^ 2 ≤ n := by
    nlinarith [sq_nonneg p.1.x, sq_nonneg p.1.y, sq_nonneg p.1.z]
  exact ⟨⟨p.1.x, coordinate_bounds_of_sq_le hn hxsq⟩,
    ⟨p.1.y, coordinate_bounds_of_sq_le hn hysq⟩,
    ⟨p.1.z, coordinate_bounds_of_sq_le hn hzsq⟩⟩
theorem aRepBounded_injective (n : ℤ) :
    Function.Injective (aRepBounded n) := by
  intro p q h
  apply Subtype.ext
  apply Triple.ext
  · have hx := congrArg (fun r => r.1.1) h
    change p.1.x = q.1.x at hx
    exact hx
  · have hy := congrArg (fun r => r.2.1.1) h
    change p.1.y = q.1.y at hy
    exact hy
  · have hz := congrArg (fun r => r.2.2.1) h
    change p.1.z = q.1.z at hz
    exact hz
instance aRepFinite (n : ℤ) : Finite (ARep n) :=
  Finite.of_injective (aRepBounded n) (aRepBounded_injective n)
noncomputable instance aRepFintype (n : ℤ) : Fintype (ARep n) :=
  Fintype.ofFinite _
end TunnellMap


