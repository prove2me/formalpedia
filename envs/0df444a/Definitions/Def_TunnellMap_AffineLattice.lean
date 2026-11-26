-- Prove2me | Definitions.Def_TunnellMap_AffineLattice
-- name    : TunnellMap_AffineLattice
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:43:53.036082+00:00
-- url     : https://prove2.me/theorems/45eacf89-58bc-423f-8de7-74de3d762414
-- title:
--   Affine Lattice
-- statement:
--   Definitions and structural lemmas for Affine Lattice, from Aakash Gurung (GrgAakash/tunnell-two-to-one-map; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Two-to-one executable map between Tunnell representation sets development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/AffineLattice.lean

import Definitions.Def_TunnellMap_Midpoint
set_option autoImplicit true
namespace TunnellMap
def dot (p q : Triple) : ℤ := p.x * q.x + p.y * q.y + p.z * q.z
def cross (p q : Triple) : Triple :=
  ⟨p.y * q.z - p.z * q.y,
    p.z * q.x - p.x * q.z,
    p.x * q.y - p.y * q.x⟩
def vadd (p q : Triple) : Triple := ⟨p.x + q.x, p.y + q.y, p.z + q.z⟩
def vsmul (a : ℤ) (p : Triple) : Triple := ⟨a * p.x, a * p.y, a * p.z⟩
def linComb3 (a b c : ℤ) (e₁ e₂ z : Triple) : Triple :=
  vadd (vsmul a e₁) (vadd (vsmul b e₂) (vsmul c z))
def det3 (e₁ e₂ z : Triple) : ℤ := dot (cross e₁ e₂) z
def tau (p : Triple) : Triple := ⟨p.x + p.z, p.y, p.x - p.z⟩
structure OrthogonalFrame (p : Triple) where
  e₁ : Triple
  e₂ : Triple
  z : Triple
  cross_eq : cross e₁ e₂ = p
  bezout : dot p z = 1
namespace OrthogonalFrame
variable {p : Triple} (F : OrthogonalFrame p)
def coeff₁ (r : Triple) : ℤ := dot r (cross F.e₂ F.z)
def coeff₂ (r : Triple) : ℤ := dot r (cross F.z F.e₁)
def coeffZ (r : Triple) : ℤ := dot r p
end OrthogonalFrame
end TunnellMap


