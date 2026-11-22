-- Prove2me | Definitions.Def_LeanPool_PureNock_NPR
-- name    : LeanPool_PureNock_NPR
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:59:33.497089+00:00
-- url     : https://prove2.me/theorems/f24ff003-064f-4d42-9b2d-f5e0567dacdb
-- title:
--   NPR
-- statement:
--   Definitions and structural lemmas for NPR, from Pure Nock formalization contributors; LeanPool contributors's pinned Pure Nock semantics, trace certificates, and polynomial fingerprints development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean

module
public import Definitions.Def_LeanPool_PureNock_Dyck
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Data.List.GetD
public import Mathlib.Tactic.FieldSimp
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Polynomial
namespace Nock
namespace NPR
section CPoly
variable {K : Type*} [Field K]
noncomputable def cpoly (f : ℕ → K) (n : ℕ) : K[X] := ∑ i ∈ Finset.range n, C (f i) * X ^ i
end CPoly
section ListPoly
variable {K : Type*} [Field K]
noncomputable def listPoly (l : List K) : K[X] :=
  cpoly (fun i => l.getD i 0) l.length
end ListPoly
section FnLayer
variable {K : Type*} [Field K]
def leafF (n : Noun) : List K := n.leafList.map (fun k : ℕ => (k : K))
def dyckBits (n : Noun) : List K := n.dyckWord.map (fun b => if b then (1 : K) else 0)
noncomputable def Φ (n : Noun) : K[X] × K[X] × K[X] :=
  (X ^ n.leaves, listPoly (leafF n), listPoly (dyckBits n))
noncomputable def fn (n : Noun) (r : K) : K × K × K :=
  (r ^ n.leaves, (listPoly (leafF n)).eval r, (listPoly (dyckBits n)).eval r)
end FnLayer
section Decomp
variable {K : Type*} [Field K]
end Decomp
section SchwartzZippel
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
end SchwartzZippel
section Collision
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
def epsCol (Λ : ℕ) : ℚ := ((2 * (2 * Λ - 1) : ℕ) : ℚ) / (Fintype.card K)
end Collision
section Table
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
end Table
end NPR
end Nock


