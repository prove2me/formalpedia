-- Prove2me | Definitions.Def_Nintendo_worlds
-- name    : Nintendo_worlds
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-21T05:51:52.80351+00:00
-- url     : https://prove2.me/theorems/6c4396a0-3647-402c-b7e3-6b09b1337da7
-- title:
--   The five worlds: idealized mechanics for Mario, Donkey Kong Country, Zelda, Metroid, and Pokémon
-- statement:
--   The worlds layer of the Nintendo mission: the five idealized game models of the paper's Sections 3 to 7, each a discrete grid world keeping exactly the mechanics the paper's gadgets use. Super Mario Bros.: the player is small or big and invulnerable under a permanent star, occupying one cell when small and two when big; walking, jumping one to four cells high with at most one cell of horizontal drift from support onto support, falling, and hitting item blocks; bricks are passable only when big, firebars and goombas shrink a big player and kill a small one; the goal is to reach the level's goal alive. Donkey Kong Country: the Kong occupies one cell, walks, jumps, and falls on the same pattern, picks up a barrel from a pile and throws it at the first zinger in the row below within twenty cells, and fires a cannon that carries him to its destination; zingers kill. The Legend of Zelda: walking among walls, floors, chests, blocks, pits, gates, switches, and teleporters; pits kill, switches toggle their gates, single blocks push one cell onto floor, the hookshot - when the level provides it - lands up to seven cells along a direction on the cell before a chest, block, wall, or closed gate, and teleporters carry to their destination. Metroid: Samus occupies two cells unmorphed and one morphed; she walks, jumps unmorphed, falls, toggles the morph ball under support and headroom conditions, and shoots a beam of up to sixteen cells that kills every zoomer it meets until a solid tile; zoomers kill. Pokémon: the player steps among walls and enemy trainers, each with a position, a facing, a sight range, and a strength; a trainer sees along its line of sight - blocked by walls and by other trainers' bodies - or stands adjacent; a seen battle interrupts the step, a line-of-sight trainer being lured to the adjacent cell; a weak trainer is defeated and a strong one kills; there are no wild Pokémon at all. Each model comes with its level and configuration types, step relation, start, goal predicate, and extent-squared size measure; the models are glitch-free by construction.
-- source:
--   G. Aloupis, E. D. Demaine, A. Guo, G. Viglietta, Classic Nintendo games are (computationally) hard, Theoret. Comput. Sci. 586 (2015) 135-160, Sections 3-7.

import Mathlib
import Definitions.Def_Nintendo_sat
import Definitions.Def_Nintendo_game

/-!
# The five worlds

The worlds layer of the Nintendo mission: the five idealized game models of
Sections 3 to 7 of Aloupis, Demaine, Guo, and Viglietta, "Classic Nintendo
games are (computationally) hard" — Super Mario Bros., Donkey Kong Country,
The Legend of Zelda, Metroid, and Pokemon — each with a level type, a
configuration type, a step relation, a start, a goal predicate, and a size
measure. Each model keeps exactly the mechanics that the paper's gadgets
use; the models are glitch-free by construction.
-/

namespace Nintendo

/-! ## Super Mario Bros. -/

/-- The tiles of the Mario world. -/
inductive MarioTile where
  | solid : MarioTile
  | brick : MarioTile
  | itemStarBlock : MarioTile
  | itemMushBlock : MarioTile
  | star : MarioTile
  | mushroom : MarioTile
  | firebar : MarioTile
  | goomba : MarioTile
  | empty : MarioTile
  deriving DecidableEq, Repr

/-- A Mario level: a grid of tiles, a start, a goal, and an extent. -/
structure MarioLevel where
  grid : Pos → MarioTile
  start : Pos
  goal : Pos
  extent : ℕ

/-- A Mario configuration: the mutable grid, the position, and the state of
the player. -/
structure MarioConf where
  grid : Pos → MarioTile
  pos : Pos
  big : Bool
  star : Bool
  alive : Bool

/-- The effect of entering a tile. -/
structure MarioEntry where
  pass : Bool
  big : Bool
  star : Bool
  alive : Bool
  tile : MarioTile

/-- The effect of entering a tile in the current state: bricks are passable
only when big and break; the star item makes the player invulnerable and is
consumed; the mushroom makes the player big and is consumed; firebars and
goombas shrink a big player and kill a small one unless the player is
invulnerable. -/
def marioEntry (t : MarioTile) (big star : Bool) : MarioEntry :=
  match t with
  | MarioTile.solid => { pass := false, big := big, star := star, alive := true, tile := t }
  | MarioTile.brick =>
      { pass := big, big := big, star := star, alive := true, tile := MarioTile.empty }
  | MarioTile.itemStarBlock => { pass := false, big := big, star := star, alive := true, tile := t }
  | MarioTile.itemMushBlock => { pass := false, big := big, star := star, alive := true, tile := t }
  | MarioTile.star =>
      { pass := true, big := big, star := true, alive := true, tile := MarioTile.empty }
  | MarioTile.mushroom =>
      { pass := true, big := true, star := star, alive := true, tile := MarioTile.empty }
  | MarioTile.firebar =>
      { pass := true, big := (if star then big else false), star := star,
        alive := (star || big), tile := t }
  | MarioTile.goomba =>
      { pass := true, big := (if star then big else false), star := star,
        alive := (star || big), tile := t }
  | MarioTile.empty => { pass := true, big := big, star := star, alive := true, tile := t }

/-- The effect of entering the single cell q. -/
def marioEnterOne (g : Pos → MarioTile) (big star : Bool) (q : Pos) :
    MarioEntry × (Pos → MarioTile) :=
  let e := marioEntry (g q) big star
  (e, if e.pass then setTile g q e.tile else g)

/-- The effect of entering the cells occupied at p: two cells when big. -/
def marioEnterCells (g : Pos → MarioTile) (big star : Bool) (p : Pos) :
    MarioEntry × (Pos → MarioTile) :=
  if big then
    let r1 := marioEnterOne g big star p
    let r2 := marioEnterOne r1.2 r1.1.big r1.1.star (p.1, p.2 + 1)
    ({ pass := r1.1.pass && r2.1.pass, big := r2.1.big, star := r2.1.star,
        alive := r1.1.alive && r2.1.alive, tile := MarioTile.empty }, r2.2)
  else marioEnterOne g big star p

/-- Tiles that support the player. -/
def marioSupport : MarioTile → Bool
  | MarioTile.solid => true
  | MarioTile.brick => true
  | MarioTile.itemStarBlock => true
  | MarioTile.itemMushBlock => true
  | _ => false

/-- Walk one cell left or right. -/
def marioWalk (c c' : MarioConf) : Prop :=
  c.alive = true ∧
  ∃ dx : ℤ, (dx = 1 ∨ dx = -1) ∧
    (let p := (c.pos.1 + dx, c.pos.2)
     let r := marioEnterCells c.grid c.big c.star p
     r.1.pass = true ∧ r.1.alive = true ∧
       c' = ⟨r.2, p, r.1.big, r.1.star, r.1.alive⟩)

/-- Jump one to four cells high, with at most one cell of horizontal drift,
from support onto support, with the traversed cells clear. -/
def marioJump (c c' : MarioConf) : Prop :=
  c.alive = true ∧
  ∃ j : ℕ, ∃ dx : ℤ, 1 ≤ j ∧ j ≤ 4 ∧ (dx = 1 ∨ dx = 0 ∨ dx = -1) ∧
    marioSupport (c.grid (c.pos.1, c.pos.2 - 1)) = true ∧
    marioSupport (c.grid (c.pos.1 + dx, c.pos.2 + (j : ℤ) - 1)) = true ∧
    (∀ k ∈ List.range (j - 1),
      (marioEntry (c.grid (c.pos.1, c.pos.2 + ((k : ℤ) + 1))) c.big c.star).pass = true) ∧
    (let p := (c.pos.1 + dx, c.pos.2 + (j : ℤ))
     let r := marioEnterCells c.grid c.big c.star p
     r.1.pass = true ∧ r.1.alive = true ∧
       c' = ⟨r.2, p, r.1.big, r.1.star, r.1.alive⟩)

/-- Fall one cell down. -/
def marioFall (c c' : MarioConf) : Prop :=
  c.alive = true ∧
  (let p := (c.pos.1, c.pos.2 - 1)
   let r := marioEnterCells c.grid c.big c.star p
   r.1.pass = true ∧ r.1.alive = true ∧
     c' = ⟨r.2, p, r.1.big, r.1.star, r.1.alive⟩)

/-- Hit the block tile above the player's head: an item block becomes empty
and its item appears in the cell above it. -/
def marioHit (c c' : MarioConf) : Prop :=
  c.alive = true ∧
  (let above := (c.pos.1, c.pos.2 + (if c.big then (2 : ℤ) else 1))
   let t := c.grid above
   (t = MarioTile.itemStarBlock ∨ t = MarioTile.itemMushBlock) ∧
     c' = ⟨setTile (setTile c.grid above MarioTile.empty)
             (c.pos.1, c.pos.2 + (if c.big then (3 : ℤ) else 2))
             (if t = MarioTile.itemStarBlock then MarioTile.star else MarioTile.mushroom),
           c.pos, c.big, c.star, c.alive⟩)

/-- The step relation of the Mario world. -/
def marioStep (_L : MarioLevel) (c c' : MarioConf) : Prop :=
  marioWalk c c' ∨ marioJump c c' ∨ marioFall c c' ∨ marioHit c c'

/-- The Mario game, start, goal, and level size. -/
def marioGame (L : MarioLevel) : Game MarioConf := { step := marioStep L }

def marioStart (L : MarioLevel) : MarioConf := ⟨L.grid, L.start, false, false, true⟩

def marioGoal (L : MarioLevel) (c : MarioConf) : Prop := c.alive = true ∧ c.pos = L.goal

def marioLevelSize (L : MarioLevel) : ℕ := L.extent ^ 2

/-! ## Donkey Kong Country -/

/-- The tiles of the Donkey Kong Country world. -/
inductive DkcTile where
  | solid : DkcTile
  | empty : DkcTile
  | zinger : DkcTile
  | barrelPile : DkcTile
  | cannonTo (dst : Pos) : DkcTile
  deriving DecidableEq, Repr

/-- A Donkey Kong Country level. -/
structure DkcLevel where
  grid : Pos → DkcTile
  start : Pos
  goal : Pos
  extent : ℕ

/-- A Donkey Kong Country configuration. -/
structure DkcConf where
  grid : Pos → DkcTile
  pos : Pos
  hasBarrel : Bool
  alive : Bool

/-- The effect of entering a tile: zingers kill the Kong. -/
structure DkcEntry where
  pass : Bool
  alive : Bool
  tile : DkcTile

def dkcEntry (t : DkcTile) : DkcEntry :=
  match t with
  | DkcTile.solid => { pass := false, alive := true, tile := t }
  | DkcTile.empty => { pass := true, alive := true, tile := t }
  | DkcTile.zinger => { pass := true, alive := false, tile := t }
  | DkcTile.barrelPile => { pass := true, alive := true, tile := t }
  | DkcTile.cannonTo _ => { pass := true, alive := true, tile := t }

/-- The effect of entering the single cell q (the Kong occupies one cell). -/
def dkcEnterOne (g : Pos → DkcTile) (q : Pos) : DkcEntry × (Pos → DkcTile) :=
  let e := dkcEntry (g q)
  (e, if e.pass then setTile g q e.tile else g)

/-- Tiles that support the Kong. -/
def dkcSupport : DkcTile → Bool
  | DkcTile.solid => true
  | DkcTile.barrelPile => true
  | DkcTile.cannonTo _ => true
  | _ => false

/-- The first zinger in the row below the player, within twenty cells to
either side. -/
def dkcScanZinger (g : Pos → DkcTile) (p : Pos) : Option Pos :=
  (List.range 20).foldl
    (fun acc k =>
      match acc with
      | some q => some q
      | none =>
          if g (p.1 + (k : ℤ) + 1, p.2 - 1) = DkcTile.zinger then
            some (p.1 + (k : ℤ) + 1, p.2 - 1)
          else if g (p.1 - (k : ℤ) - 1, p.2 - 1) = DkcTile.zinger then
            some (p.1 - (k : ℤ) - 1, p.2 - 1)
          else none)
    none

/-- Walk one cell left or right. -/
def dkcWalk (c c' : DkcConf) : Prop :=
  c.alive = true ∧
  ∃ dx : ℤ, (dx = 1 ∨ dx = -1) ∧
    (let p := (c.pos.1 + dx, c.pos.2)
     let r := dkcEnterOne c.grid p
     r.1.pass = true ∧ r.1.alive = true ∧
       c' = ⟨r.2, p, c.hasBarrel, r.1.alive⟩)

/-- Jump one to four cells high, from support onto support, with the
traversed cells clear. -/
def dkcJump (c c' : DkcConf) : Prop :=
  c.alive = true ∧
  ∃ j : ℕ, ∃ dx : ℤ, 1 ≤ j ∧ j ≤ 4 ∧ (dx = 1 ∨ dx = 0 ∨ dx = -1) ∧
    dkcSupport (c.grid (c.pos.1, c.pos.2 - 1)) = true ∧
    dkcSupport (c.grid (c.pos.1 + dx, c.pos.2 + (j : ℤ) - 1)) = true ∧
    (∀ k ∈ List.range (j - 1),
      (dkcEntry (c.grid (c.pos.1, c.pos.2 + ((k : ℤ) + 1)))).pass = true) ∧
    (let p := (c.pos.1 + dx, c.pos.2 + (j : ℤ))
     let r := dkcEnterOne c.grid p
     r.1.pass = true ∧ r.1.alive = true ∧
       c' = ⟨r.2, p, c.hasBarrel, r.1.alive⟩)

/-- Fall one cell down. -/
def dkcFall (c c' : DkcConf) : Prop :=
  c.alive = true ∧
  (let p := (c.pos.1, c.pos.2 - 1)
   let r := dkcEnterOne c.grid p
   r.1.pass = true ∧ r.1.alive = true ∧
     c' = ⟨r.2, p, c.hasBarrel, r.1.alive⟩)

/-- Pick up a barrel from a barrel pile. -/
def dkcPickup (c c' : DkcConf) : Prop :=
  c.alive = true ∧ c.grid c.pos = DkcTile.barrelPile ∧
    c' = ⟨setTile c.grid c.pos DkcTile.empty, c.pos, true, c.alive⟩

/-- Throw the held barrel at the first zinger in the row below. -/
def dkcThrow (c c' : DkcConf) : Prop :=
  c.alive = true ∧ c.hasBarrel = true ∧
    ∃ q, dkcScanZinger c.grid c.pos = some q ∧
      c' = ⟨setTile c.grid q DkcTile.empty, c.pos, false, c.alive⟩

/-- Fire the cannon the Kong stands on. -/
def dkcFire (c c' : DkcConf) : Prop :=
  c.alive = true ∧
  ∃ dst, c.grid c.pos = DkcTile.cannonTo dst ∧
    (let r := dkcEnterOne c.grid dst
     r.1.pass = true ∧ r.1.alive = true ∧
       c' = ⟨r.2, dst, c.hasBarrel, r.1.alive⟩)

/-- The step relation of the Donkey Kong Country world. -/
def dkcStep (_L : DkcLevel) (c c' : DkcConf) : Prop :=
  dkcWalk c c' ∨ dkcJump c c' ∨ dkcFall c c' ∨ dkcPickup c c' ∨
    dkcThrow c c' ∨ dkcFire c c'

/-- The Donkey Kong Country game, start, goal, and level size. -/
def dkcGame (L : DkcLevel) : Game DkcConf := { step := dkcStep L }

def dkcStart (L : DkcLevel) : DkcConf := ⟨L.grid, L.start, false, true⟩

def dkcGoal (L : DkcLevel) (c : DkcConf) : Prop := c.alive = true ∧ c.pos = L.goal

def dkcLevelSize (L : DkcLevel) : ℕ := L.extent ^ 2

/-! ## The Legend of Zelda -/

/-- The tiles of the Zelda world. -/
inductive ZeldaTile where
  | wall : ZeldaTile
  | floor : ZeldaTile
  | chest : ZeldaTile
  | block : ZeldaTile
  | pit : ZeldaTile
  | switchGate (k : ℕ) : ZeldaTile
  | gate (k : ℕ) : ZeldaTile
  | teleport (dst : Pos) : ZeldaTile
  deriving DecidableEq, Repr

/-- A Zelda level, with the hookshot availability and the initial gate
states. -/
structure ZeldaLevel where
  grid : Pos → ZeldaTile
  start : Pos
  goal : Pos
  extent : ℕ
  hasHookshot : Bool
  gatesInit : ℕ → Bool

/-- A Zelda configuration. -/
structure ZeldaConf where
  grid : Pos → ZeldaTile
  pos : Pos
  gates : ℕ → Bool
  alive : Bool

/-- Whether a tile may be walked on, given the current gate states. -/
def zeldaPass (gates : ℕ → Bool) : ZeldaTile → Bool
  | ZeldaTile.wall => false
  | ZeldaTile.chest => false
  | ZeldaTile.block => false
  | ZeldaTile.floor => true
  | ZeldaTile.pit => true
  | ZeldaTile.switchGate _ => true
  | ZeldaTile.gate k => gates k
  | ZeldaTile.teleport _ => true

/-- Walk one cell in one of the four directions; a switch tile toggles its
gate, a pit kills, a gate is passable exactly when open. -/
def zeldaWalk (c c' : ZeldaConf) : Prop :=
  c.alive = true ∧
  ∃ d : Pos, (d = (1, 0) ∨ d = (-1, 0) ∨ d = (0, 1) ∨ d = (0, -1)) ∧
    (let p := (c.pos.1 + d.1, c.pos.2 + d.2)
     let t := c.grid p
     zeldaPass c.gates t = true ∧
       c'.pos = p ∧
       c'.grid = c.grid ∧
       c'.alive = (match t with | ZeldaTile.pit => false | _ => c.alive) ∧
       c'.gates = (match t with
         | ZeldaTile.switchGate k => fun i => if i = k then !(c.gates i) else c.gates i
         | _ => c.gates))

/-- Push a block one cell, when the cell beyond it is floor. -/
def zeldaPush (c c' : ZeldaConf) : Prop :=
  c.alive = true ∧
  ∃ d : Pos, (d = (1, 0) ∨ d = (-1, 0) ∨ d = (0, 1) ∨ d = (0, -1)) ∧
    (let p := (c.pos.1 + d.1, c.pos.2 + d.2)
     let q := (p.1 + d.1, p.2 + d.2)
     c.grid p = ZeldaTile.block ∧ c.grid q = ZeldaTile.floor ∧
       c' = ⟨setTile (setTile c.grid p ZeldaTile.floor) q ZeldaTile.block, p, c.gates, c.alive⟩)

/-- The hookshot scan: the beam travels up to seven cells; it fails at
walls and closed gates, and lands on the cell before a chest or block. -/
def zeldaHookScan (g : Pos → ZeldaTile) (gates : ℕ → Bool) (p : Pos) (d : Pos) : Option Pos :=
  let out :=
    (List.range 7).foldl
      (fun st k =>
        match st with
        | some b => some b
        | none =>
            let q := (p.1 + ((k : ℤ) + 1) * d.1, p.2 + ((k : ℤ) + 1) * d.2)
            let t := g q
            match t with
            | ZeldaTile.chest => some (some (p.1 + (k : ℤ) * d.1, p.2 + (k : ℤ) * d.2))
            | ZeldaTile.block => some (some (p.1 + (k : ℤ) * d.1, p.2 + (k : ℤ) * d.2))
            | ZeldaTile.wall => some none
            | ZeldaTile.gate i => if gates i then none else some none
            | _ => none)
      (none : Option (Option Pos))
  out.getD none

/-- Fire the hookshot in one of the four directions, when the level
provides it. -/
def zeldaHookshot (L : ZeldaLevel) (c c' : ZeldaConf) : Prop :=
  L.hasHookshot = true ∧ c.alive = true ∧
  ∃ d : Pos, (d = (1, 0) ∨ d = (-1, 0) ∨ d = (0, 1) ∨ d = (0, -1)) ∧
    ∃ q, zeldaHookScan c.grid c.gates c.pos d = some q ∧ q ≠ c.pos ∧
      (let t := c.grid q
       zeldaPass c.gates t = true ∧
         c' = ⟨c.grid, q, c.gates, (match t with | ZeldaTile.pit => false | _ => c.alive)⟩)

/-- Take a teleporter to its destination. -/
def zeldaTeleport (c c' : ZeldaConf) : Prop :=
  c.alive = true ∧
  ∃ dst, c.grid c.pos = ZeldaTile.teleport dst ∧
    (let t := c.grid dst
     zeldaPass c.gates t = true ∧
       c' = ⟨c.grid, dst, c.gates, (match t with | ZeldaTile.pit => false | _ => c.alive)⟩)

/-- The step relation of the Zelda world. -/
def zeldaStep (L : ZeldaLevel) (c c' : ZeldaConf) : Prop :=
  zeldaWalk c c' ∨ zeldaPush c c' ∨ zeldaHookshot L c c' ∨ zeldaTeleport c c'

/-- The Zelda game, start, goal, and level size. -/
def zeldaGame (L : ZeldaLevel) : Game ZeldaConf := { step := zeldaStep L }

def zeldaStart (L : ZeldaLevel) : ZeldaConf := ⟨L.grid, L.start, L.gatesInit, true⟩

def zeldaGoal (L : ZeldaLevel) (c : ZeldaConf) : Prop := c.alive = true ∧ c.pos = L.goal

def zeldaLevelSize (L : ZeldaLevel) : ℕ := L.extent ^ 2

/-! ## Metroid -/

/-- The tiles of the Metroid world. -/
inductive MetroidTile where
  | solid : MetroidTile
  | empty : MetroidTile
  | zoomer : MetroidTile
  | tunnel : MetroidTile
  deriving DecidableEq, Repr

/-- A Metroid level. -/
structure MetroidLevel where
  grid : Pos → MetroidTile
  start : Pos
  goal : Pos
  extent : ℕ

/-- A Metroid configuration. -/
structure MetroidConf where
  grid : Pos → MetroidTile
  pos : Pos
  morph : Bool
  alive : Bool

/-- The effect of entering a tile: zoomers kill Samus. -/
structure MetroidEntry where
  pass : Bool
  alive : Bool

def metroidEntryOne (t : MetroidTile) : MetroidEntry :=
  match t with
  | MetroidTile.solid => { pass := false, alive := true }
  | MetroidTile.empty => { pass := true, alive := true }
  | MetroidTile.zoomer => { pass := true, alive := false }
  | MetroidTile.tunnel => { pass := true, alive := true }

/-- The cells Samus occupies: one when morphed, two otherwise. -/
def samusOccupies (morph : Bool) (p : Pos) : List Pos :=
  if morph then [p] else [p, (p.1, p.2 + 1)]

/-- The combined effect of entering the cells occupied at p. -/
def metroidEnter (g : Pos → MetroidTile) (morph : Bool) (p : Pos) : MetroidEntry :=
  (samusOccupies morph p).foldl
    (fun acc q =>
      let e := metroidEntryOne (g q)
      { pass := acc.pass && e.pass, alive := acc.alive && e.alive })
    { pass := true, alive := true }

/-- Tiles that support Samus. -/
def metroidSupport : MetroidTile → Bool
  | MetroidTile.solid => true
  | _ => false

/-- Walk one cell left or right. -/
def metroidWalk (c c' : MetroidConf) : Prop :=
  c.alive = true ∧
  ∃ dx : ℤ, (dx = 1 ∨ dx = -1) ∧
    (let p := (c.pos.1 + dx, c.pos.2)
     let e := metroidEnter c.grid c.morph p
     e.pass = true ∧ e.alive = true ∧ c' = ⟨c.grid, p, c.morph, e.alive⟩)

/-- Jump one to four cells high, only unmorphed, from support onto support. -/
def metroidJump (c c' : MetroidConf) : Prop :=
  c.alive = true ∧ c.morph = false ∧
  ∃ j : ℕ, ∃ dx : ℤ, 1 ≤ j ∧ j ≤ 4 ∧ (dx = 1 ∨ dx = 0 ∨ dx = -1) ∧
    metroidSupport (c.grid (c.pos.1, c.pos.2 - 1)) = true ∧
    metroidSupport (c.grid (c.pos.1 + dx, c.pos.2 + (j : ℤ) - 1)) = true ∧
    (let p := (c.pos.1 + dx, c.pos.2 + (j : ℤ))
     let e := metroidEnter c.grid false p
     e.pass = true ∧ e.alive = true ∧ c' = ⟨c.grid, p, c.morph, e.alive⟩)

/-- Fall one cell down. -/
def metroidFall (c c' : MetroidConf) : Prop :=
  c.alive = true ∧
  (let p := (c.pos.1, c.pos.2 - 1)
   let e := metroidEnter c.grid c.morph p
   e.pass = true ∧ e.alive = true ∧ c' = ⟨c.grid, p, c.morph, e.alive⟩)

/-- Toggle the morph ball: morphing needs support, unmorphing needs the
headroom of both cells. -/
def metroidMorph (c c' : MetroidConf) : Prop :=
  c.alive = true ∧
  ((c.morph = false ∧ metroidSupport (c.grid (c.pos.1, c.pos.2 - 1)) = true ∧
      c' = ⟨c.grid, c.pos, true, c.alive⟩) ∨
   (c.morph = true ∧ (metroidEnter c.grid false c.pos).pass = true ∧
      c' = ⟨c.grid, c.pos, false, c.alive⟩))

/-- The beam: up to sixteen cells along a direction, killing every zoomer
it meets, until it hits a solid tile. -/
def metroidFire (g : Pos → MetroidTile) (p : Pos) (d : Pos) : Pos → MetroidTile :=
  ((List.range 16).foldl
    (fun st k =>
      let firing := st.1
      let gg := st.2
      if firing then
        let q := (p.1 + ((k : ℤ) + 1) * d.1, p.2 + ((k : ℤ) + 1) * d.2)
        if gg q = MetroidTile.solid then (false, gg)
        else if gg q = MetroidTile.zoomer then (true, setTile gg q MetroidTile.empty)
        else st
      else st)
    (true, g)).2

/-- Shoot the beam in one of three directions, only unmorphed. -/
def metroidShoot (c c' : MetroidConf) : Prop :=
  c.alive = true ∧ c.morph = false ∧
  ∃ d : Pos, (d = (1, 0) ∨ d = (-1, 0) ∨ d = (0, 1)) ∧
    c' = ⟨metroidFire c.grid c.pos d, c.pos, c.morph, c.alive⟩

/-- The step relation of the Metroid world. -/
def metroidStep (_L : MetroidLevel) (c c' : MetroidConf) : Prop :=
  metroidWalk c c' ∨ metroidJump c c' ∨ metroidFall c c' ∨
    metroidMorph c c' ∨ metroidShoot c c'

/-- The Metroid game, start, goal, and level size. -/
def metroidGame (L : MetroidLevel) : Game MetroidConf := { step := metroidStep L }

def metroidStart (L : MetroidLevel) : MetroidConf := ⟨L.grid, L.start, false, true⟩

def metroidGoal (L : MetroidLevel) (c : MetroidConf) : Prop := c.alive = true ∧ c.pos = L.goal

def metroidLevelSize (L : MetroidLevel) : ℕ := L.extent ^ 2

/-! ## Pokemon -/

/-- Trainer strength. -/
inductive PokeKind where
  | weak : PokeKind
  | strong : PokeKind
  deriving DecidableEq, Repr

/-- An enemy trainer: a position, a facing direction, a sight range, and a
strength. -/
structure Trainer where
  pos : Pos
  dir : Pos
  range : ℕ
  kind : PokeKind
  deriving DecidableEq, Repr

/-- A Pokemon level: walls, enemy trainers, a start, a goal, and an
extent. -/
structure PokeLevel where
  walls : Pos → Bool
  trainers : List Trainer
  start : Pos
  goal : Pos
  extent : ℕ

/-- A Pokemon configuration. -/
structure PokeConf where
  pos : Pos
  trainerPos : List Pos
  defeated : List Bool
  alive : Bool

/-- The default trainer used beyond the end of the trainer list. -/
def pokeDefaultTrainer : Trainer := ⟨(0, 0), (1, 0), 0, PokeKind.weak⟩

/-- Whether a trainer at tp facing dir with range r sees the cell q, with
walls and other trainer bodies blocking the sight line. -/
def pokeRayHits (walls : Pos → Bool) (bodies : List Pos) (tp dir : Pos) (r : ℕ) (q : Pos) : Bool :=
  let out :=
    (List.range r).foldl
      (fun st k =>
        match st with
        | some b => some b
        | none =>
            let c := (tp.1 + ((k : ℤ) + 1) * dir.1, tp.2 + ((k : ℤ) + 1) * dir.2)
            if c = q then some true
            else if walls c then some false
            else if posIn c bodies then some false
            else none)
      (none : Option Bool)
  out.getD false

/-- Whether two cells are horizontally or vertically adjacent. -/
def pokeAdjacentB (p q : Pos) : Bool :=
  decide (p = (q.1 + 1, q.2) ∨ p = (q.1 - 1, q.2) ∨ p = (q.1, q.2 + 1) ∨ p = (q.1, q.2 - 1))

/-- The current positions of the undefeated trainers other than the i-th. -/
def pokeBodies (L : PokeLevel) (c : PokeConf) (i : ℕ) : List Pos :=
  (List.range L.trainers.length).foldl
    (fun acc j =>
      if getAt c.defeated j then acc
      else if decide (j = i) then acc
      else nthPos c.trainerPos j :: acc)
    []

/-- Whether the i-th undefeated trainer sees or stands adjacent to the
cell q. -/
def pokeSees (L : PokeLevel) (c : PokeConf) (i : ℕ) (q : Pos) : Bool :=
  let tr := L.trainers.getD i pokeDefaultTrainer
  let tp := nthPos c.trainerPos i
  (getAt c.defeated i = false) &&
    (pokeRayHits L.walls (pokeBodies L c i) tp tr.dir tr.range q ||
      pokeAdjacentB tp q)

/-- The first undefeated trainer that sees the target cell, in list order. -/
def pokeFirstEncounter (L : PokeLevel) (c : PokeConf) (q : Pos) : Option ℕ :=
  (List.range L.trainers.length).foldl
    (fun acc i =>
      match acc with
      | some n => some n
      | none => if pokeSees L c i q then some i else none)
    (none : Option ℕ)

/-- The step relation of the Pokemon world. The player attempts to step in
one of the four directions. When no undefeated trainer sees the target
cell, the step is quiet and must land on a free cell. When a trainer sees
the target cell, a battle interrupts the step: a trainer seeing along its
line is lured to the cell adjacent to the player along its facing
direction; a trainer already adjacent is battled in place. A weak trainer
is defeated, a strong one kills the player. -/
def pokeStep (L : PokeLevel) (c c' : PokeConf) : Prop :=
  c.alive = true ∧
  ∃ d : Pos, (d = (1, 0) ∨ d = (-1, 0) ∨ d = (0, 1) ∨ d = (0, -1)) ∧
    (let q := (c.pos.1 + d.1, c.pos.2 + d.2)
     match pokeFirstEncounter L c q with
     | none =>
         (L.walls q) = false ∧
           ((List.range L.trainers.length).any
              (fun i => !(getAt c.defeated i) && decide (nthPos c.trainerPos i = q))) = false ∧
           c' = ⟨q, c.trainerPos, c.defeated, c.alive⟩
     | some i =>
         let tr := L.trainers.getD i pokeDefaultTrainer
         let tp := nthPos c.trainerPos i
         if pokeRayHits L.walls (pokeBodies L c i) tp tr.dir tr.range q then
           (let newTp := (q.1 - tr.dir.1, q.2 - tr.dir.2)
            match tr.kind with
            | PokeKind.weak =>
                c' = ⟨c.pos, updAtPos c.trainerPos i newTp, updAt c.defeated i true, c.alive⟩
            | PokeKind.strong =>
                c' = ⟨c.pos, updAtPos c.trainerPos i newTp, c.defeated, false⟩)
         else
           (match tr.kind with
            | PokeKind.weak =>
                c' = ⟨c.pos, c.trainerPos, updAt c.defeated i true, c.alive⟩
            | PokeKind.strong =>
                c' = ⟨c.pos, c.trainerPos, c.defeated, false⟩))

/-- The Pokemon game, start, goal, and level size. -/
def pokeGame (L : PokeLevel) : Game PokeConf := { step := pokeStep L }

def pokeStart (L : PokeLevel) : PokeConf :=
  ⟨L.start, L.trainers.map (fun t => t.pos), List.replicate L.trainers.length false, true⟩

def pokeGoal (L : PokeLevel) (c : PokeConf) : Prop := c.alive = true ∧ c.pos = L.goal

def pokeLevelSize (L : PokeLevel) : ℕ := L.extent ^ 2

end Nintendo


