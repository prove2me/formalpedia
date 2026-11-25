-- Prove2me | Definitions.Def_DetDLP_OrientedPacketInstance
-- name    : DetDLP_OrientedPacketInstance
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-23T15:15:52.476412+00:00
-- url     : https://prove2.me/theorems/91ccbc65-0395-4e82-beb6-117f15d35ae6
-- title:
--   Oriented packet slots and finite-precision selectors
-- statement:
--   A real graph edge occupies one distinct packet slot. Each endpoint is assigned to the group selected by its side and a coordinate bit of the slot. The definition records those ports, their weighted tile modes, the normalized rational dyadic kernel, its finite-precision representatives, and the corresponding selector at any point of a coefficient algebra.
-- source:
--   DetDLP mission, Section 5. Oriented residual networks at a nonzero dyadic sample.

import Definitions.Def_DetDLP_PacketKernel

namespace DetDLP.OrientedPacketInstance
open Polynomial Finset
abbrev Pos (a : ℕ) := Fin (2^a)
abbrev Address {a : ℕ} {P : Type} (active : P→Finset (Pos a)) := (q : P) × ↥(active q)
def group {r a : ℕ} (i : Fin a) (tag : Fin r × Fin r) (right : Bool) (x : ℕ) :=
  let ends := if x.testBit i.val then (max tag.1 tag.2,min tag.1 tag.2) else (min tag.1 tag.2,max tag.1 tag.2)
  if right then ends.2 else ends.1
def endpoint (G : BipartiteMultigraph) (e : Fin G.nE) (right : Bool) :=
  if G.side (G.endpoints e).1=right then (G.endpoints e).1 else (G.endpoints e).2
abbrev Assigned {a r : ℕ} {P : Type} (i : Fin a) (tag : P→Fin r×Fin r) (active : P→Finset (Pos a)) (g : Fin r) :=
  {e : P × Pos a × Bool // e.2.1 ∈ active e.1 ∧ group i (tag e.1) e.2.2 e.2.1.val=g}
abbrev Mode {a r : ℕ} {P : Type} (i : Fin a) (tag : P→Fin r×Fin r) (p : ℕ) (h : Fin r×P) :=
  {k : Fin (2^(i.val+1)) // group i (tag h.2) false k.val=h.1} × Fin (p-1)
noncomputable def kernel {a : ℕ} (t d : ZMod (2^(a+1))) : ℚ[X] :=
  let S := Finset.univ.image (fun w : ZMod (2^(a+1)) => (w.valMinAbs:ℚ))
  (DeformedContraction.shiftKernel S (d.valMinAbs:ℚ)).comp (C (t.valMinAbs:ℚ)+C ((2:ℚ)^(a+1))*X)
def Represents {a p : ℕ} (t : ZMod (2^(a+1))) (U : ZMod (2^(a+1)) → (ZMod (2^p))[X]) :=
  ∀ d n,let c := (kernel t d).coeff n
        IsUnit (c.den:ZMod (2^p)) ∧ (U d).coeff n * (c.den:ZMod (2^p))=(c.num:ZMod (2^p))
noncomputable def selector {a p : ℕ} {P R : Type} [Fintype P] [DecidableEq P] [CommRing R] [Algebra (ZMod (2^p)) R]
    (G : BipartiteMultigraph) (active : P→Finset (Pos a)) (layout : Fin G.nE ≃ Address active)
    (U : ZMod (2^(a+1)) → (ZMod (2^p))[X]) (z : R) (x y : Fin G.nE→Bool) (e : Fin G.nE) : R :=
  let q := (layout e).1
  let u := ∑ f : ↥(active q),
    (U ((f.val.val:ZMod (2^(a+1)))-((layout e).2.val.val:ZMod (2^(a+1))))).eval₂ (algebraMap (ZMod (2^p)) R) z *
      (if x (layout.symm ⟨q,f⟩) then 1 else 0)
  if y e then u else 1-u
end DetDLP.OrientedPacketInstance


