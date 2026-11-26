-- Prove2me | Definitions.Def_TunnellMap_ComputableDirect
-- name    : TunnellMap_ComputableDirect
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T16:05:30.528033+00:00
-- url     : https://prove2.me/theorems/1f88f449-06ef-49d8-8d64-66dc8771c713
-- title:
--   Computable Direct
-- statement:
--   Definitions and structural lemmas for Computable Direct, from Aakash Gurung (GrgAakash/tunnell-two-to-one-map; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Two-to-one executable map between Tunnell representation sets development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableDirect.lean

import Definitions.Def_TunnellMap_ResidualBalance
import Definitions.Def_TunnellMap_ComputableRoster
set_option autoImplicit true
namespace TunnellMap
def directDomainRep {n : ℤ} : DirectDomain n → BOddRep n
  | Sum.inl d => d.rep
  | Sum.inr (Sum.inl d) => d.rep
  | Sum.inr (Sum.inr d) => d.rep
def directImageRep {n : ℤ} : DirectImage n → ARep n
  | Sum.inl d => d.rep
  | Sum.inr (Sum.inl d) => d.rep
  | Sum.inr (Sum.inr d) => d.rep
def directDomainExec {n : ℤ} (p : BOddRep n) : Option (DirectDomain n) :=
  if h₁ : (8 : ℤ) ∣ (p.1.x + 2 * p.1.z + p.1.y) then
    some (Sum.inl ⟨p, (p.1.x + 2 * p.1.z + p.1.y) / 8,
      (Int.mul_ediv_cancel' h₁).symm⟩)
  else if h₂ : (8 : ℤ) ∣ (p.1.y - p.1.x + 2 * p.1.z) then
    some (Sum.inr (Sum.inl ⟨p, (p.1.y - p.1.x + 2 * p.1.z) / 8,
      (Int.mul_ediv_cancel' h₂).symm⟩))
  else if h₃ : (4 : ℤ) ∣ p.1.x then
    some (Sum.inr (Sum.inr ⟨p, p.1.x / 4, (Int.mul_ediv_cancel' h₃).symm⟩))
  else none
def directMapExec {n : ℤ} (p : BOddRep n) : Option (ARep n) :=
  (directDomainExec p).map fun d => directImageRep (directEquiv n d)
end TunnellMap


