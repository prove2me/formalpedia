-- Prove2me | Definitions.Def_QEC_Coding_FourDimensionalToricCode_Cellulation
-- name    : QEC_Coding_FourDimensionalToricCode_Cellulation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T10:13:30.613375+00:00
-- url     : https://prove2.me/theorems/5d741f34-baac-463a-91a5-2eebd92ede20
-- title:
--   Cellulation
-- statement:
--   Definitions and structural lemmas for Cellulation, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Cellulation.lean

import Definitions.Def_QEC_Coding_Core_Definitions
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


set_option autoImplicit false
noncomputable section
namespace QEC
namespace Coding
namespace PeriodicCubical4
open scoped Classical
inductive Axis
  | x | y | z | w
  deriving DecidableEq
instance : Fintype Axis where
  elems := {.x, .y, .z, .w}
  complete := by intro a; cases a <;> simp
inductive Plane
  | xy | xz | xw | yz | yw | zw
  deriving DecidableEq
instance : Fintype Plane where
  elems := {.xy, .xz, .xw, .yz, .yw, .zw}
  complete := by intro a; cases a <;> simp
inductive Volume
  | xyz | xyw | xzw | yzw
  deriving DecidableEq
instance : Fintype Volume where
  elems := {.xyz, .xyw, .xzw, .yzw}
  complete := by intro a; cases a <;> simp
abbrev Coord (L : Nat) := Axis → ZMod L
abbrev Vertex (L : Nat) := Coord L
abbrev Link (L : Nat) := Coord L × Axis
abbrev Plaquette (L : Nat) := Coord L × Plane
abbrev Cube (L : Nat) := Coord L × Volume
abbrev Hypercube (L : Nat) := Coord L
@[simp]
theorem card_axis : Fintype.card Axis = 4 := by
  decide +kernel
@[simp]
theorem card_plane : Fintype.card Plane = 6 := by
  decide +kernel
@[simp]
theorem card_volume : Fintype.card Volume = 4 := by
  decide +kernel
@[simp]
theorem card_coord (L : Nat) [NeZero L] :
    Fintype.card (Coord L) = L ^ 4 := by
  simp [Coord]
@[simp]
theorem card_vertex (L : Nat) [NeZero L] :
    Fintype.card (Vertex L) = L ^ 4 :=
  card_coord L
@[simp]
theorem card_link (L : Nat) [NeZero L] :
    Fintype.card (Link L) = 4 * L ^ 4 := by
  simp [Link, Nat.mul_comm]
@[simp]
theorem card_plaquette (L : Nat) [NeZero L] :
    Fintype.card (Plaquette L) = 6 * L ^ 4 := by
  simp [Plaquette, Nat.mul_comm]
@[simp]
theorem card_cube (L : Nat) [NeZero L] :
    Fintype.card (Cube L) = 4 * L ^ 4 := by
  simp [Cube, Nat.mul_comm]
@[simp]
theorem card_hypercube (L : Nat) [NeZero L] :
    Fintype.card (Hypercube L) = L ^ 4 :=
  card_coord L
def translateCoord {L : Nat} (v x : Coord L) : Coord L :=
  x + v
def shift {L : Nat} (x : Coord L) (a : Axis) : Coord L :=
  x + Pi.single a 1
def shiftBy {L : Nat} (x : Coord L) (a : Axis) (n : Nat) : Coord L :=
  x + Pi.single a (n : ZMod L)
@[simp]
theorem translateCoord_zero {L : Nat} (x : Coord L) :
    translateCoord 0 x = x := by
  simp [translateCoord]
theorem shift_commute {L : Nat} (x : Coord L) (a b : Axis) :
    shift (shift x a) b = shift (shift x b) a := by
  simp [shift, add_comm, add_left_comm]
@[simp]
theorem shiftBy_zero {L : Nat} (x : Coord L) (a : Axis) :
    shiftBy x a 0 = x := by
  simp [shiftBy]
@[simp]
theorem shiftBy_periodic {L : Nat} [NeZero L] (x : Coord L) (a : Axis) :
    shiftBy x a L = x := by
  ext b
  by_cases h : a = b
  · subst b
    simp [shiftBy]
  · simp [shiftBy]
def translateLink {L : Nat} (v : Coord L) (e : Link L) : Link L :=
  (translateCoord v e.1, e.2)
def translatePlaquette {L : Nat} (v : Coord L) (p : Plaquette L) : Plaquette L :=
  (translateCoord v p.1, p.2)
def translateCube {L : Nat} (v : Coord L) (c : Cube L) : Cube L :=
  (translateCoord v c.1, c.2)
def translateHypercube {L : Nat} (v : Coord L) (c : Hypercube L) : Hypercube L :=
  translateCoord v c
@[simp]
theorem translateLink_zero {L : Nat} (e : Link L) :
    translateLink 0 e = e := by
  rcases e with ⟨x, a⟩
  simp [translateLink]
@[simp]
theorem translatePlaquette_zero {L : Nat} (p : Plaquette L) :
    translatePlaquette 0 p = p := by
  rcases p with ⟨x, a⟩
  simp [translatePlaquette]
@[simp]
theorem translateCube_zero {L : Nat} (c : Cube L) :
    translateCube 0 c = c := by
  rcases c with ⟨x, a⟩
  simp [translateCube]
@[simp]
theorem translateHypercube_zero {L : Nat} (c : Hypercube L) :
    translateHypercube 0 c = c := by
  simp [translateHypercube]
def Axis.dualVolume : Axis → Volume
  | .x => .yzw
  | .y => .xzw
  | .z => .xyw
  | .w => .xyz
def Volume.dualAxis : Volume → Axis
  | .xyz => .w
  | .xyw => .z
  | .xzw => .y
  | .yzw => .x
def Plane.dual : Plane → Plane
  | .xy => .zw
  | .xz => .yw
  | .xw => .yz
  | .yz => .xw
  | .yw => .xz
  | .zw => .xy
@[simp]
theorem Axis.dualVolume_dualAxis (a : Axis) :
    a.dualVolume.dualAxis = a := by
  cases a <;> rfl
@[simp]
theorem Volume.dualAxis_dualVolume (v : Volume) :
    v.dualAxis.dualVolume = v := by
  cases v <;> rfl
@[simp]
theorem Plane.dual_dual (p : Plane) :
    p.dual.dual = p := by
  cases p <;> rfl
def dualVertex {L : Nat} (x : Vertex L) : Hypercube L :=
  x
def dualLink {L : Nat} (e : Link L) : Cube L :=
  (e.1, e.2.dualVolume)
def dualPlaquette {L : Nat} (p : Plaquette L) : Plaquette L :=
  (p.1, p.2.dual)
def dualCube {L : Nat} (c : Cube L) : Link L :=
  (c.1, c.2.dualAxis)
def dualHypercube {L : Nat} (x : Hypercube L) : Vertex L :=
  x
@[simp]
theorem dualCube_dualLink {L : Nat} (e : Link L) :
    dualCube (dualLink e) = e := by
  rcases e with ⟨x, a⟩
  simp [dualCube, dualLink]
@[simp]
theorem dualLink_dualCube {L : Nat} (c : Cube L) :
    dualLink (dualCube c) = c := by
  rcases c with ⟨x, v⟩
  simp [dualCube, dualLink]
@[simp]
theorem dualPlaquette_dualPlaquette {L : Nat} (p : Plaquette L) :
    dualPlaquette (dualPlaquette p) = p := by
  rcases p with ⟨x, q⟩
  simp [dualPlaquette]
section Boundary
variable {L : Nat} [NeZero L]
def cellWord {α : Type*} [DecidableEq α] (a : α) : Word (ZMod 2) α :=
  Pi.single a 1
@[simp]
theorem word_add_self {α : Type*} (x : Word (ZMod 2) α) :
    x + x = 0 :=
  ZModModule.add_self x
@[simp]
theorem two_mul_word {α : Type*} (x : Word (ZMod 2) α) :
    2 * x = 0 := by
  ext a
  change (2 : ZMod 2) * x a = 0
  have htwo : (2 : ZMod 2) = 0 := CharTwo.two_eq_zero
  calc
    (2 : ZMod 2) * x a = 0 * x a := congrArg (fun z : ZMod 2 => z * x a) htwo
    _ = 0 := zero_mul _
def linearize {α β : Type*} [Fintype α] [DecidableEq α]
    (f : α → Word (ZMod 2) β) :
    Word (ZMod 2) α →ₗ[ZMod 2] Word (ZMod 2) β where
  toFun x := ∑ a, x a • f a
  map_add' := by
    intro x y
    simp [add_smul, Finset.sum_add_distrib]
  map_smul' := by
    intro r x
    simp [mul_smul, Finset.smul_sum]
@[simp]
theorem linearize_single {α β : Type*} [Fintype α] [DecidableEq α]
    (f : α → Word (ZMod 2) β) (a : α) (r : ZMod 2) :
    linearize f (Pi.single a r) = r • f a := by
  classical
  simp [linearize]
@[simp]
theorem linearize_cellWord {α β : Type*} [Fintype α] [DecidableEq α]
    [DecidableEq β] (f : α → Word (ZMod 2) β) (a : α) :
    linearize f (cellWord a) = f a := by
  classical
  simp [linearize, cellWord]
def linkBoundary (e : Link L) : Word (ZMod 2) (Vertex L) :=
  cellWord e.1 + cellWord (shift e.1 e.2)
def plaquetteBoundary (p : Plaquette L) : Word (ZMod 2) (Link L) :=
  match p.2 with
  | .xy =>
      cellWord (p.1, .x) + cellWord (shift p.1 .y, .x) +
      cellWord (p.1, .y) + cellWord (shift p.1 .x, .y)
  | .xz =>
      cellWord (p.1, .x) + cellWord (shift p.1 .z, .x) +
      cellWord (p.1, .z) + cellWord (shift p.1 .x, .z)
  | .xw =>
      cellWord (p.1, .x) + cellWord (shift p.1 .w, .x) +
      cellWord (p.1, .w) + cellWord (shift p.1 .x, .w)
  | .yz =>
      cellWord (p.1, .y) + cellWord (shift p.1 .z, .y) +
      cellWord (p.1, .z) + cellWord (shift p.1 .y, .z)
  | .yw =>
      cellWord (p.1, .y) + cellWord (shift p.1 .w, .y) +
      cellWord (p.1, .w) + cellWord (shift p.1 .y, .w)
  | .zw =>
      cellWord (p.1, .z) + cellWord (shift p.1 .w, .z) +
      cellWord (p.1, .w) + cellWord (shift p.1 .z, .w)
def cubeBoundary (c : Cube L) : Word (ZMod 2) (Plaquette L) :=
  match c.2 with
  | .xyz =>
      cellWord (c.1, .xy) + cellWord (shift c.1 .z, .xy) +
      cellWord (c.1, .xz) + cellWord (shift c.1 .y, .xz) +
      cellWord (c.1, .yz) + cellWord (shift c.1 .x, .yz)
  | .xyw =>
      cellWord (c.1, .xy) + cellWord (shift c.1 .w, .xy) +
      cellWord (c.1, .xw) + cellWord (shift c.1 .y, .xw) +
      cellWord (c.1, .yw) + cellWord (shift c.1 .x, .yw)
  | .xzw =>
      cellWord (c.1, .xz) + cellWord (shift c.1 .w, .xz) +
      cellWord (c.1, .xw) + cellWord (shift c.1 .z, .xw) +
      cellWord (c.1, .zw) + cellWord (shift c.1 .x, .zw)
  | .yzw =>
      cellWord (c.1, .yz) + cellWord (shift c.1 .w, .yz) +
      cellWord (c.1, .yw) + cellWord (shift c.1 .z, .yw) +
      cellWord (c.1, .zw) + cellWord (shift c.1 .y, .zw)
def hypercubeBoundary (h : Hypercube L) : Word (ZMod 2) (Cube L) :=
  cellWord (h, .xyz) + cellWord (shift h .w, .xyz) +
  cellWord (h, .xyw) + cellWord (shift h .z, .xyw) +
  cellWord (h, .xzw) + cellWord (shift h .y, .xzw) +
  cellWord (h, .yzw) + cellWord (shift h .x, .yzw)
def boundary1 : Word (ZMod 2) (Link L) →ₗ[ZMod 2] Word (ZMod 2) (Vertex L) :=
  linearize linkBoundary
def boundary2 :
    Word (ZMod 2) (Plaquette L) →ₗ[ZMod 2] Word (ZMod 2) (Link L) :=
  linearize plaquetteBoundary
def boundary3 :
    Word (ZMod 2) (Cube L) →ₗ[ZMod 2] Word (ZMod 2) (Plaquette L) :=
  linearize cubeBoundary
def boundary4 :
    Word (ZMod 2) (Hypercube L) →ₗ[ZMod 2] Word (ZMod 2) (Cube L) :=
  linearize hypercubeBoundary
theorem boundary2_cubeBoundary (c : Cube L) :
    boundary2 (cubeBoundary c) = 0 := by
  rcases c with ⟨x, c⟩
  cases c <;>
    simp only [boundary2, cubeBoundary, map_add, linearize_cellWord,
      plaquetteBoundary] <;>
    simp only [shift_commute] <;>
    abel_nf <;>
    simp
theorem linearize_comp_linearize_eq_zero
    {α β γ : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (f : α → Word (ZMod 2) β) (g : β → Word (ZMod 2) γ)
    (h : ∀ a, linearize g (f a) = 0) :
    (linearize g).comp (linearize f) = 0 := by
  apply LinearMap.ext
  intro x
  rw [← word_eq_sum_single (F := ZMod 2) x]
  simp [h]
theorem boundary2_comp_boundary3 :
    (boundary2 (L := L)).comp boundary3 = 0 :=
  linearize_comp_linearize_eq_zero
    cubeBoundary plaquetteBoundary boundary2_cubeBoundary
def plaquetteChainComplex :
    ChainComplexData (ZMod 2)
      (Word (ZMod 2) (Link L))
      (Word (ZMod 2) (Plaquette L))
      (Word (ZMod 2) (Cube L)) where
  boundary1 := boundary2
  boundary2 := boundary3
  boundary_squared := boundary2_comp_boundary3
def PrimalLinkPlaquetteIncident (e : Link L) (p : Plaquette L) : Prop :=
  plaquetteBoundary p e = 1
def PrimalPlaquetteCubeIncident (p : Plaquette L) (c : Cube L) : Prop :=
  cubeBoundary c p = 1
def DualLinkPlaquetteIncident (e : Link L) (p : Plaquette L) : Prop :=
  PrimalPlaquetteCubeIncident (dualPlaquette p) (dualLink e)
def DualPlaquetteCubeIncident (p : Plaquette L) (c : Cube L) : Prop :=
  PrimalLinkPlaquetteIncident (dualCube c) (dualPlaquette p)
end Boundary
end PeriodicCubical4
end Coding
end QEC


