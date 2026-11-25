-- Prove2me | Definitions.Def_DetDLP_PacketKernel
-- name    : DetDLP_PacketKernel
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-23T12:07:34.97254+00:00
-- url     : https://prove2.me/theorems/0c655293-a773-4466-a827-cee23f4c22f4
-- title:
--   Packet kernel and deformed tensor contraction polynomial
-- statement:
--   For an internal edge assigned a packet and a slot, the packet mixing kernel is zero between distinct packets. Within a packet it is the polynomial formed by deleting the slot-difference factor from the node polynomial and normalizing by its derivative at zero. For a given tensor family, the deformation sums over separate left and right edge assignments. Each real port contributes its linear mixed value or its Boolean complement according to the assignment on the other side.
-- source:
--   DetDLP Sections 5.1 and 5.2. Packet deformation in the one-step Cauchy--Hermite identity.

import Definitions.Def_DetDLP_BTN

namespace DetDLP.DeformedContraction
open Polynomial Finset

variable {R : Type*} [CommRing R]

/-- A Boolean assignment on one side of the edge cut. -/
abbrev Assignment (G : BipartiteMultigraph) := Fin G.nE → Bool

noncomputable def bitValue {G : BipartiteMultigraph} (W : Fin G.nE → Fin G.nE → R[X])
    (x : Assignment G) (e : Fin G.nE) : R[X] := ∑ f, if x f then W e f else 0

noncomputable def selector {G : BipartiteMultigraph} (W : Fin G.nE → Fin G.nE → R[X])
    (x y : Assignment G) (e : Fin G.nE) : R[X] :=
  if y e then bitValue W x e else 1-bitValue W x e

def portValue {G : BipartiteMultigraph}
    (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → R) (x : Assignment G) (v : Fin G.nV) :=
  T v fun i => x ((G.ports v).get i)

def weight {G : BipartiteMultigraph}
    (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → R) (x y : Assignment G) :=
  ∏ v, if G.side v then portValue T x v else portValue T y v

/-- Polynomial obtained by splitting the assignments on the two sides of every real edge.
A terminal assignment may be held fixed in the tensors throughout this construction. -/
noncomputable def deformation {G : BipartiteMultigraph}
    (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → R)
    (W : Fin G.nE → Fin G.nE → R[X]) :=
  ∑ x : Assignment G, ∑ y : Assignment G, C (weight T x y) * ∏ e, selector W x y e

/-- The packet interpolation kernel, normalized by the derivative of the node
polynomial at zero. Its first argument is the set of integer shifts embedded in ℚ. -/
noncomputable def shiftKernel (S : Finset ℚ) (d : ℚ) : ℚ[X] :=
  C ((∏ t ∈ S.erase 0, -t)⁻¹) * ∏ t ∈ S.erase d, (X-C t)

noncomputable def packetKernel {e : ℕ} (S : Finset ℚ) (packet : Fin e → ℕ) (slot : Fin e → ℤ)
    (i j : Fin e) : ℚ[X] :=
  if packet i = packet j then shiftKernel S ((slot j-slot i : ℤ):ℚ) else 0


end DetDLP.DeformedContraction


